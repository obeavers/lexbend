//! The shipped Bend modules a language-2.2 semantic module may import
//! beside the prelude: the semantic support forms, the ported runtime, the
//! linear-arithmetic checker, and the reasoning laws. A build publishes
//! exactly those its modules import, each under `modules/` beside the
//! prelude, with its own imports of the prelude and of earlier support
//! modules renamed to their build paths.

use crate::backend::bend::engine::fail;
use crate::diagnostic::Diagnostic;

/// One shipped support module.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Support {
    /// `Semantic.bend`: the forms the semantic surface lowers through.
    Semantic,
    /// `Runtime.bend`: Lean's runtime library, monomorphized.
    Runtime,
    /// `LinArith.bend`: the reflective linear-arithmetic checker.
    LinArith,
    /// `Reasoning.bend`: the generic laws and lemmas a reasoning
    /// declaration's theorems are proved by. It names `Semantic` and
    /// `Runtime`, which a build therefore publishes with it.
    Reasoning,
}

impl Support {
    /// The embedded source path.
    #[must_use]
    pub const fn source_path(self) -> &'static str {
        match self {
            Self::Semantic => "language/bend-prelude/Semantic.bend",
            Self::Runtime => "language/bend-prelude/Runtime.bend",
            Self::LinArith => "language/bend-prelude/LinArith.bend",
            Self::Reasoning => "language/bend-prelude/Reasoning.bend",
        }
    }

    /// Where a build publishes it.
    #[must_use]
    pub const fn build_path(self) -> &'static str {
        match self {
            Self::Semantic => "modules/LexLeanSemantic.bend",
            Self::Runtime => "modules/LexLeanRuntime.bend",
            Self::LinArith => "modules/LexLeanLinArith.bend",
            Self::Reasoning => "modules/LexLeanReasoning.bend",
        }
    }

    /// The alias generated modules import it under.
    #[must_use]
    pub const fn alias(self) -> &'static str {
        match self {
            Self::Semantic => "S",
            Self::Runtime => "R",
            Self::LinArith => "LA",
            Self::Reasoning => "RS",
        }
    }

    /// The support modules it imports, which a build publishes with it.
    #[must_use]
    pub const fn requires(self) -> &'static [Self] {
        match self {
            Self::Reasoning => &[Self::Semantic, Self::Runtime],
            Self::Semantic | Self::Runtime | Self::LinArith => &[],
        }
    }

    /// Its bytes as published.
    ///
    /// # Errors
    ///
    /// An internal diagnostic when the module is not embedded.
    pub fn artifact(self) -> Result<(&'static str, Vec<u8>), Diagnostic> {
        let path = self.source_path();
        let bytes = crate::embedded::FILES
            .iter()
            .find(|(candidate, _)| *candidate == path)
            .map(|(_, bytes)| *bytes)
            .ok_or_else(|| fail(format!("`{path}` is not embedded")))?;
        let text =
            std::str::from_utf8(bytes).map_err(|_| fail(format!("`{path}` is not UTF-8")))?;
        let mut published = text.replace(
            "import ./LexLean.bend as L\n",
            "import ./LexLeanPrelude.bend as L\n",
        );
        for required in self.requires() {
            let source = required
                .source_path()
                .trim_start_matches("language/bend-prelude/");
            let build = required.build_path().trim_start_matches("modules/");
            published = published.replace(
                &format!("import ./{source} as {}\n", required.alias()),
                &format!("import ./{build} as {}\n", required.alias()),
            );
        }
        Ok((self.build_path(), published.into_bytes()))
    }
}
