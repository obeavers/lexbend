//! Performance telemetry (SPEC.md §22.13): what the verification cost, written
//! to CI evidence and to nowhere else.
//!
//! Wall time, resident set, swap, scheduling order, and the host's memory are
//! facts about one run on one host. A verified artifact is a fact about the
//! project, so nothing here is returned to a stage, hashed, or staged: the
//! sink is a file that is only ever appended to, outside the project and the
//! build root, named by the operator through `LEXLEAN_CI_TELEMETRY`. A write
//! that fails is dropped on purpose, because a result must not depend on
//! whether its measurement could be recorded. Every key the measurements use
//! is in [`VOCABULARY`], and the gate refuses a verified directory that
//! contains one of them, so a measurement planted into an artifact is caught
//! by name rather than by luck.

use std::cell::RefCell;
use std::io::Write;
use std::path::Path;
use std::sync::{Arc, Mutex, PoisonError};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use serde_json::{json, Value};

use crate::verify::operational::Operational;

/// The file the verifier appends to, inside the telemetry directory.
pub const VERIFY_FILE: &str = "verify-telemetry.jsonl";

/// The keys that carry a host-dependent measurement. A JSON key of this
/// vocabulary in a verified artifact is a defect (SPEC.md §22.13).
pub const VOCABULARY: [&str; 11] = [
    "wall_ms",
    "started_unix_ms",
    "peak_rss_kib",
    "peak_swap_kib",
    "mem_total_kib",
    "mem_available_kib",
    "swap_total_kib",
    "swap_used_kib",
    "host_cpus",
    "process_width",
    "completion_seq",
];

/// The keys of an event that name what was measured and carry no
/// measurement. They also appear in artifacts, which is why they are not
/// part of the vocabulary the gate refuses.
pub const LABELS: [&str; 10] = [
    "event",
    "project",
    "stage",
    "module",
    "tool",
    "exit_code",
    "frontier",
    "members",
    "item",
    "ok",
];

/// The record of one event, as written: a JSON object on one line.
fn line(value: &Value) -> String {
    let mut text = value.to_string();
    text.push('\n');
    text
}

/// Append one JSON line to `file` of `directory`, creating the directory.
/// A failure is dropped: telemetry never decides a result.
pub fn append(directory: &Path, file: &str, value: &Value) {
    if std::fs::create_dir_all(directory).is_err() {
        return;
    }
    let opened = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(directory.join(file));
    if let Ok(mut handle) = opened {
        // One `write_all` of one whole line: appends of that size do not
        // interleave, so lines written by the verifier and by `xtask`
        // processes sharing a directory stay whole.
        handle.write_all(line(value).as_bytes()).ok();
    }
}

fn unix_ms() -> u128 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |elapsed| elapsed.as_millis())
}

fn millis(duration: Duration) -> u64 {
    u64::try_from(duration.as_millis()).unwrap_or(u64::MAX)
}

/// Memory of the host, from `/proc/meminfo`, in KiB.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HostMemory {
    /// `MemTotal`.
    pub total: u64,
    /// `MemAvailable`.
    pub available: u64,
    /// `SwapTotal`.
    pub swap_total: u64,
    /// `SwapTotal - SwapFree`.
    pub swap_used: u64,
}

fn kib_field(text: &str, key: &str) -> Option<u64> {
    text.lines()
        .find_map(|row| row.strip_prefix(key))
        .and_then(|rest| rest.trim_start_matches(':').split_whitespace().next())
        .and_then(|number| number.parse().ok())
}

impl HostMemory {
    /// Parse the text of `/proc/meminfo`.
    #[must_use]
    pub fn parse(text: &str) -> Option<Self> {
        let swap_total = kib_field(text, "SwapTotal")?;
        let swap_free = kib_field(text, "SwapFree")?;
        Some(Self {
            total: kib_field(text, "MemTotal")?,
            available: kib_field(text, "MemAvailable")?,
            swap_total,
            swap_used: swap_total.saturating_sub(swap_free),
        })
    }

    /// The host's memory now, where the host has a `/proc/meminfo`.
    #[must_use]
    pub fn now() -> Option<Self> {
        Self::parse(&std::fs::read_to_string("/proc/meminfo").ok()?)
    }

    fn fields(&self, into: &mut serde_json::Map<String, Value>) {
        into.insert("mem_total_kib".to_owned(), json!(self.total));
        into.insert("mem_available_kib".to_owned(), json!(self.available));
        into.insert("swap_total_kib".to_owned(), json!(self.swap_total));
        into.insert("swap_used_kib".to_owned(), json!(self.swap_used));
    }
}

/// The peak resident set of this process so far (`VmHWM`), in KiB.
#[must_use]
pub fn own_peak_rss_kib() -> Option<u64> {
    kib_field(&std::fs::read_to_string("/proc/self/status").ok()?, "VmHWM")
}

/// The file every event of one verification goes to.
pub struct Sink {
    directory: std::path::PathBuf,
    project: String,
    // Whole lines are appended under the lock so that the workers of a
    // batch cannot interleave bytes of two events.
    guard: Mutex<()>,
}

impl Sink {
    fn emit(&self, event: &str, fields: Value) {
        let mut object = serde_json::Map::new();
        object.insert("event".to_owned(), json!(event));
        object.insert("project".to_owned(), json!(self.project));
        if let Value::Object(extra) = fields {
            object.extend(extra);
        }
        let _held = self.guard.lock().unwrap_or_else(PoisonError::into_inner);
        append(&self.directory, VERIFY_FILE, &Value::Object(object));
    }

    fn timed(&self, event: &str, started: Instant, fields: Value) {
        let wall = started.elapsed();
        let mut object = match fields {
            Value::Object(map) => map,
            _ => serde_json::Map::new(),
        };
        object.insert("wall_ms".to_owned(), json!(millis(wall)));
        object.insert(
            "started_unix_ms".to_owned(),
            json!(unix_ms().saturating_sub(wall.as_millis())),
        );
        self.emit(event, Value::Object(object));
    }
}

/// What a worker thread needs to report a process: the sink and the stage
/// that spawned it.
#[derive(Clone)]
pub struct Context {
    sink: Arc<Sink>,
    stage: &'static str,
}

impl Context {
    /// Report one finished child process.
    pub fn process(&self, report: &ProcessReport<'_>) {
        let mut fields = serde_json::Map::new();
        fields.insert("stage".to_owned(), json!(self.stage));
        fields.insert("tool".to_owned(), json!(report.tool));
        if let Some(module) = report.module {
            fields.insert("module".to_owned(), json!(module));
        }
        fields.insert("exit_code".to_owned(), json!(report.exit_code));
        if let Some(peak) = report.peak_rss_kib {
            fields.insert("peak_rss_kib".to_owned(), json!(peak));
        }
        if let Some(peak) = report.peak_swap_kib {
            fields.insert("peak_swap_kib".to_owned(), json!(peak));
        }
        self.sink
            .timed("process", report.started, Value::Object(fields));
    }

    /// Report that the item at `item` of the stage completed as the
    /// `sequence`th to do so. This is the one place completion order is
    /// visible, and it is visible only here.
    fn completion(&self, item: usize, sequence: usize) {
        self.sink.emit(
            "completion",
            json!({ "stage": self.stage, "item": item, "completion_seq": sequence }),
        );
    }
}

/// The facts of one finished child process.
pub struct ProcessReport<'a> {
    /// The tool name.
    pub tool: &'a str,
    /// The module, when the process concerned one.
    pub module: Option<&'a str>,
    /// The exit code.
    pub exit_code: i32,
    /// When it was started.
    pub started: Instant,
    /// The peak resident set of the process and what it started.
    pub peak_rss_kib: Option<u64>,
    /// The peak swap of the process and what it started.
    pub peak_swap_kib: Option<u64>,
}

thread_local! {
    static CURRENT: RefCell<Option<Context>> = const { RefCell::new(None) };
}

/// The context in force on this thread.
#[must_use]
pub fn current() -> Option<Context> {
    CURRENT.with(|cell| cell.borrow().clone())
}

/// Puts a context in force on the thread until dropped.
pub struct Installed {
    previous: Option<Context>,
}

impl Drop for Installed {
    fn drop(&mut self) {
        let previous = self.previous.take();
        CURRENT.with(|cell| *cell.borrow_mut() = previous);
    }
}

/// Put `context` in force on the current thread; the worker threads of a
/// stage call this with the context of the thread that started the stage.
#[must_use]
pub fn install(context: Option<Context>) -> Installed {
    let previous = CURRENT.with(|cell| cell.replace(context));
    Installed { previous }
}

/// One verification's telemetry. Without a telemetry directory every method
/// does nothing.
pub struct Run {
    sink: Option<Arc<Sink>>,
    started: Instant,
    succeeded: std::cell::Cell<bool>,
}

impl Run {
    /// Begin the telemetry of a verification of `project`.
    #[must_use]
    pub fn begin(operational: &Operational, project: &str) -> Self {
        let sink = operational.telemetry().map(|directory| {
            Arc::new(Sink {
                directory: directory.to_path_buf(),
                project: project.to_owned(),
                guard: Mutex::new(()),
            })
        });
        if let Some(sink) = &sink {
            let mut fields = serde_json::Map::new();
            fields.insert("process_width".to_owned(), json!(operational.width()));
            fields.insert(
                "host_cpus".to_owned(),
                json!(std::thread::available_parallelism().map_or(0, std::num::NonZeroUsize::get)),
            );
            fields.insert("started_unix_ms".to_owned(), json!(unix_ms()));
            if let Some(memory) = HostMemory::now() {
                memory.fields(&mut fields);
            }
            sink.emit("verify_begin", Value::Object(fields));
        }
        Self {
            sink,
            started: Instant::now(),
            succeeded: std::cell::Cell::new(false),
        }
    }

    /// Mark the verification as having produced its artifacts.
    pub fn succeeded(&self) {
        self.succeeded.set(true);
    }

    /// The stage clock of this verification.
    #[must_use]
    pub fn stages(&self) -> Stages {
        Stages {
            sink: self.sink.clone(),
            current: None,
            installed: None,
        }
    }

    /// Report one frontier of module elaboration.
    pub fn frontier(&self, stage: &'static str, index: usize, members: usize, started: Instant) {
        if let Some(sink) = &self.sink {
            sink.timed(
                "frontier",
                started,
                json!({ "stage": stage, "frontier": index, "members": members }),
            );
        }
    }
}

impl Drop for Run {
    fn drop(&mut self) {
        if let Some(sink) = &self.sink {
            let mut fields = serde_json::Map::new();
            fields.insert("ok".to_owned(), json!(self.succeeded.get()));
            if let Some(peak) = own_peak_rss_kib() {
                fields.insert("peak_rss_kib".to_owned(), json!(peak));
            }
            if let Some(memory) = HostMemory::now() {
                memory.fields(&mut fields);
            }
            sink.timed("verify_end", self.started, Value::Object(fields));
        }
    }
}

/// The stage clock: entering a stage ends the previous one.
pub struct Stages {
    sink: Option<Arc<Sink>>,
    current: Option<(&'static str, Instant)>,
    installed: Option<Installed>,
}

impl Stages {
    /// End the current stage, if any, and begin `stage`.
    pub fn enter(&mut self, stage: &'static str) {
        self.end();
        if let Some(sink) = &self.sink {
            self.installed = Some(install(Some(Context {
                sink: Arc::clone(sink),
                stage,
            })));
            self.current = Some((stage, Instant::now()));
        }
    }

    fn end(&mut self) {
        // Dropping the guard restores the context the thread had before the
        // first stage, which is none.
        self.installed = None;
        if let (Some(sink), Some((stage, started))) = (&self.sink, self.current.take()) {
            let mut fields = serde_json::Map::new();
            fields.insert("stage".to_owned(), json!(stage));
            if let Some(memory) = HostMemory::now() {
                memory.fields(&mut fields);
            }
            if let Some(peak) = own_peak_rss_kib() {
                fields.insert("peak_rss_kib".to_owned(), json!(peak));
            }
            sink.timed("stage", started, Value::Object(fields));
        }
    }
}

impl Drop for Stages {
    fn drop(&mut self) {
        self.end();
    }
}

/// Record that the item at `item` completed as the `sequence`th of its
/// stage, for the stage in force on this thread.
pub fn completed(item: usize, sequence: usize) {
    if let Some(context) = current() {
        context.completion(item, sequence);
    }
}

/// The peak resident set and swap of a process group, sampled.
///
/// A proof process is started as the leader of a group of its own, so the
/// group is the process and what it started (`lake` starts `lean`). The
/// kernel keeps each process's high-water mark (`VmHWM`), so a spike between
/// two samples is not lost while the process lives. A sample is the sum of the
/// high-water marks of the processes alive in the group at that moment, and
/// the group's peak is the largest sample: the processes of a long run that
/// follow one another are never added together, and the processes that overlap
/// are. Swap is a level, not a mark, so it is the sum of the current swap of
/// the live processes. A process that starts and ends between two samples is
/// not seen, which is why a run's resident peak is a measurement and not a
/// bound. Where the host has no `/proc` the watch reports nothing.
pub struct GroupWatch {
    group: u32,
    rss_peak: u64,
    swap_peak: u64,
    seen: bool,
    sampled: Option<Instant>,
}

/// How often a watch reads the process table at most.
const SAMPLE_EVERY: Duration = Duration::from_millis(100);

impl GroupWatch {
    /// Watch the group led by `group`.
    #[must_use]
    pub fn new(group: u32) -> Self {
        Self {
            group,
            rss_peak: 0,
            swap_peak: 0,
            seen: false,
            sampled: None,
        }
    }

    /// Sample, unless a sample was taken a moment ago.
    pub fn poll(&mut self) {
        if self
            .sampled
            .is_some_and(|last| last.elapsed() < SAMPLE_EVERY)
        {
            return;
        }
        self.sample();
    }

    /// Sample now.
    pub fn sample(&mut self) {
        self.sampled = Some(Instant::now());
        let Ok(entries) = std::fs::read_dir("/proc") else {
            return;
        };
        let (mut rss_now, mut swap_now, mut alive) = (0u64, 0u64, false);
        for entry in entries.flatten() {
            let Some(pid) = entry
                .file_name()
                .to_str()
                .and_then(|name| name.parse::<u32>().ok())
            else {
                continue;
            };
            let Ok(stat) = std::fs::read_to_string(format!("/proc/{pid}/stat")) else {
                continue;
            };
            // `pid (comm) state ppid pgrp ...`: the command may contain
            // spaces and parentheses, so the fields start after the last `)`.
            let group = stat
                .rsplit_once(')')
                .and_then(|(_, rest)| rest.split_whitespace().nth(2))
                .and_then(|field| field.parse::<u32>().ok());
            if group != Some(self.group) {
                continue;
            }
            let Ok(status) = std::fs::read_to_string(format!("/proc/{pid}/status")) else {
                continue;
            };
            if let Some(mark) = kib_field(&status, "VmHWM") {
                alive = true;
                rss_now += mark;
                swap_now += kib_field(&status, "VmSwap").unwrap_or(0);
            }
        }
        if alive {
            self.seen = true;
            self.rss_peak = self.rss_peak.max(rss_now);
            self.swap_peak = self.swap_peak.max(swap_now);
        }
    }

    /// The largest sample of summed high-water marks, in KiB, when any process
    /// was seen.
    #[must_use]
    pub fn peak_rss_kib(&self) -> Option<u64> {
        self.seen.then_some(self.rss_peak)
    }

    /// The largest swap total seen, in KiB, when any process was seen.
    #[must_use]
    pub fn peak_swap_kib(&self) -> Option<u64> {
        self.seen.then_some(self.swap_peak)
    }
}

#[cfg(test)]
mod tests {
    use super::{HostMemory, LABELS, VOCABULARY};

    #[test]
    fn meminfo_is_parsed_and_a_host_without_it_reports_nothing() {
        let text = "MemTotal:       16000000 kB\nMemFree: 1 kB\nMemAvailable:    9000000 kB\nSwapTotal:       4000000 kB\nSwapFree:        3500000 kB\n";
        let memory = HostMemory::parse(text).expect("parses");
        assert_eq!(memory.total, 16_000_000);
        assert_eq!(memory.available, 9_000_000);
        assert_eq!(memory.swap_total, 4_000_000);
        assert_eq!(memory.swap_used, 500_000);
        assert_eq!(HostMemory::parse("nothing here"), None);
    }

    #[test]
    fn a_label_is_never_a_measurement_key() {
        for label in LABELS {
            assert!(!VOCABULARY.contains(&label), "{label}");
        }
    }
}
