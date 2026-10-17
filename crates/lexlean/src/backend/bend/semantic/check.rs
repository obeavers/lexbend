//! The cross-checks a model declaration elaborates to (§17.12).
//!
//! Each obligation a contract or evidence generates is restated against the
//! fixed `LexLeanModels` semantics, which the Bend runtime ports, and proved
//! by exactly the discharging theorem; an artifact's typed value is checked
//! against its embedded bytes by evaluation. Bend, not this lowering, then
//! decides that the generated obligation and the fixed semantics agree, so
//! a model whose elaboration drifted from `LexLeanModels` fails to check.

use crate::backend::bend::engine::fail;
use crate::backend::bend::syntax::{BTerm, Body, Item, Name};
use crate::diagnostic::Diagnostic;
use crate::ir::semantic::model::{element_encoding, CheckProof, CheckStatement, CrossCheck};
use crate::ir::semantic::{SemanticDeclaration, SemanticTerm, SemanticType};
use crate::source::coverage::Origin;

use super::support::Support;
use super::{call, here, var, Lower, Scope};

impl Lower<'_, '_> {
    /// The law a cross-check lowers to.
    ///
    /// # Errors
    ///
    /// `LLB6008` when the restatement names a helper or proof shape the
    /// Bend runtime does not carry.
    pub(super) fn cross_check(&mut self, check: &CrossCheck) -> Result<Item, Diagnostic> {
        let spelled = super::names::global(&check.name)?;
        let params = self.type_params(&check.type_parameters)?;
        let (claim, proof) = match &check.statement {
            CheckStatement::Helper { helper, arguments } => {
                let claim = self.helper_claim(helper, arguments)?;
                let proof = match &check.proof {
                    CheckProof::Theorem {
                        theorem,
                        type_arguments,
                    } => self.theorem_value(theorem, type_arguments)?,
                    // A dataset count unfolds to the length equation and the
                    // count equation, each closed by evaluation.
                    CheckProof::Decide if helper == "Agreement" => {
                        BTerm::Pair(Box::new(BTerm::Refl), Box::new(BTerm::Refl))
                    }
                    CheckProof::Decide => {
                        return Err(fail(format!(
                            "the cross-check `{}` decides `LexLeanModels.{helper}`, which Bend evaluates only for `Agreement`",
                            check.name
                        )))
                    }
                };
                (claim, proof)
            }
            CheckStatement::Tensor {
                artifact,
                element,
                shape,
            } => (self.tensor_claim(artifact, *element, shape)?, BTerm::Refl),
            CheckStatement::Lines { artifact } => {
                let (value, bytes) = self.artifact_parts(artifact)?;
                let lines = self.runtime("LexLeanModels.linesMatch")?;
                (Self::is_true(call(lines, vec![value, bytes])), BTerm::Refl)
            }
            CheckStatement::Bytes { artifact } => {
                let (value, bytes) = self.artifact_parts(artifact)?;
                let ty = self.ty(&SemanticType::Bytes)?;
                (
                    BTerm::Equal(Box::new(value), Box::new(bytes), Box::new(ty)),
                    BTerm::Refl,
                )
            }
        };
        Ok(Item::Law {
            name: Name::new(
                spelled,
                Origin::Synthetic(crate::backend::bend::syntax::SYNTAX_ORIGIN.to_owned()),
            ),
            params,
            claim,
            claim_source: here(),
            proof: Body::term(proof, here()),
            source: here(),
        })
    }

    fn is_true(value: BTerm) -> BTerm {
        BTerm::Equal(
            Box::new(value),
            Box::new(BTerm::Constructor(super::synthetic("True"), Vec::new())),
            Box::new(var("Bool")),
        )
    }

    /// `LexLeanModels.<helper>` at the type arguments its function arguments
    /// determine, applied to those arguments.
    fn helper_claim(
        &mut self,
        helper: &str,
        arguments: &[SemanticTerm],
    ) -> Result<BTerm, Diagnostic> {
        let scope = Scope::default();
        let mut types = Vec::new();
        for argument in arguments {
            let ty = self.infer(argument, &scope)?;
            types.push(self.canonical(&ty));
        }
        let function = |index: usize| -> Result<(Vec<SemanticType>, SemanticType), Diagnostic> {
            match types.get(index) {
                Some(SemanticType::Function { parameters, result }) => {
                    Ok((parameters.clone(), (**result).clone()))
                }
                _ => Err(fail(format!(
                    "`LexLeanModels.{helper}` needs a function in argument {index}"
                ))),
            }
        };
        let last = arguments.len().saturating_sub(1);
        // Each helper's type parameters are the domains, and the result or
        // the result's output half, of the one function its statement
        // quantifies over.
        let (index, arity, result) = match helper {
            "Sound1" | "Complete1" | "Initial" => (0, 1, Typed::Domains),
            "Sound2" | "Complete2" => (0, 2, Typed::Domains),
            "Sound4" | "Complete4" => (0, 4, Typed::Domains),
            "Agreement" => (0, 1, Typed::Whole),
            "Satisfies" | "SatisfiesTotal" | "Equivalent" | "EquivalentTotal" => {
                (last, 1, Typed::Whole)
            }
            "SatisfiesStep"
            | "SatisfiesStepNoInvariant"
            | "SatisfiesStepNoPrecondition"
            | "SatisfiesStepTotal"
            | "Preserves"
            | "PreservesTotal"
            | "EquivalentStep"
            | "EquivalentStepNoInvariant"
            | "EquivalentStepNoPrecondition"
            | "EquivalentStepTotal" => (last, 2, Typed::Output),
            other => {
                return Err(fail(format!(
                    "the Bend runtime carries no `LexLeanModels.{other}`"
                )))
            }
        };
        let (domains, codomain) = function(index)?;
        if domains.len() < arity {
            return Err(fail(format!(
                "`LexLeanModels.{helper}` needs a function of {arity} arguments"
            )));
        }
        let mut type_arguments: Vec<SemanticType> = domains[..arity].to_vec();
        match result {
            Typed::Domains => {}
            Typed::Whole => type_arguments.push(codomain),
            Typed::Output => match codomain {
                SemanticType::Product { right, .. } => type_arguments.push(*right),
                other => {
                    return Err(fail(format!(
                        "`LexLeanModels.{helper}` needs a step returning a pair, not `{other:?}`"
                    )))
                }
            },
        }
        let mut out = Vec::new();
        for ty in &type_arguments {
            out.push(self.ty(ty)?);
        }
        for argument in arguments {
            out.push(self.term(argument, &scope)?);
        }
        let head = self.runtime(&format!("LexLeanModels.{helper}"))?;
        Ok(call(head, out))
    }

    /// The discharging theorem as a function of everything its law binds,
    /// so it inhabits the helper's quantified statement.
    fn theorem_value(
        &mut self,
        theorem: &crate::ir::semantic::MemberRef,
        type_arguments: &[SemanticType],
    ) -> Result<BTerm, Diagnostic> {
        let SemanticDeclaration::Theorem {
            parameters,
            statement,
            ..
        } = self.declaration(theorem)?
        else {
            return Err(fail(format!("`{}` is not a theorem", theorem.name)));
        };
        if self.converts(parameters) {
            return Err(fail(format!(
                "the cross-check's theorem `{}` takes a function, which `LexLeanModels` cannot pass",
                theorem.name
            )));
        }
        let peeled = super::proof::peel(statement);
        let arity = parameters.len() + peeled.binders.len() + peeled.premises.len();
        let names: Vec<String> = (0..arity).map(|_| self.fresh("a")).collect();
        let mut body = self.call_of(theorem, type_arguments, names.iter().map(var).collect())?;
        for name in names.iter().rev() {
            body = BTerm::Lam(super::synthetic(name.clone()), Box::new(body));
        }
        Ok(body)
    }

    /// An artifact's typed value and its embedded bytes.
    fn artifact_parts(&mut self, artifact: &str) -> Result<(BTerm, BTerm), Diagnostic> {
        let value = super::names::global(artifact)?;
        let bytes = super::names::global(&format!("{artifact}.bytes"))?;
        Ok((call(value, Vec::new()), call(bytes, Vec::new())))
    }

    /// The tensor check: the flattened values decode from exactly the
    /// bytes, and every level of nesting has exactly its declared length.
    fn tensor_claim(
        &mut self,
        artifact: &str,
        element: crate::ir::semantic::TensorElement,
        shape: &[u64],
    ) -> Result<BTerm, Diagnostic> {
        let (width, signed) = element_encoding(element);
        let (value, bytes) = self.artifact_parts(artifact)?;
        let depth = shape.len();
        if depth == 0 {
            return Err(fail(format!("the tensor `{artifact}` has no shape")));
        }
        // `nested(k)` is the type of a value nested `k` lists deep over Int.
        let nested = |k: usize| {
            let mut ty = SemanticType::Int;
            for _ in 0..k {
                ty = SemanticType::List {
                    element: Box::new(ty),
                };
            }
            ty
        };
        let nat = |n: u64| super::Lower::nat_literal(&n.to_string());
        let length = self.prelude("Lean.List.length");
        let beq = self.prelude("Lean.Nat.beq");
        let and = self.prelude("Lean.Bool.and");
        let lengths = self.support("lengthsAre");
        let flatten = self.support("flatten");
        let mut checks = Vec::new();
        let element_type = self.ty(&nested(depth - 1))?;
        checks.push(call(
            beq.clone(),
            vec![call(length.clone(), vec![element_type, value.clone()]), nat(shape[0])?],
        ));
        let mut level = value;
        let mut rows: u64 = 1;
        for index in 1..depth {
            rows = rows.saturating_mul(shape[index - 1]);
            // `level` holds `rows` rows, each a list nested `depth - index`
            // deep, whose entries are nested `depth - index - 1` deep.
            let row = self.ty(&nested(depth - index))?;
            let entry = self.ty(&nested(depth - index - 1))?;
            checks.push(call(
                beq.clone(),
                vec![call(length.clone(), vec![row, level.clone()]), nat(rows)?],
            ));
            checks.push(call(
                lengths.clone(),
                vec![entry.clone(), level.clone(), nat(shape[index])?],
            ));
            level = call(flatten.clone(), vec![entry, level]);
        }
        let matches = self.runtime("LexLeanModels.tensorMatches")?;
        let mut claim = call(
            matches,
            vec![
                nat(width as u64)?,
                BTerm::Constructor(
                    super::synthetic(if signed { "True" } else { "False" }),
                    Vec::new(),
                ),
                level,
                bytes,
            ],
        );
        // `tensorMatches && (c1 && (c2 && ..))`: the same conjunction as
        // the Lean check, which Bend evaluates to `true` either way.
        let mut shapes = checks.pop().ok_or_else(|| fail("a tensor check is empty"))?;
        while let Some(check) = checks.pop() {
            shapes = call(and.clone(), vec![check, shapes]);
        }
        claim = call(and, vec![claim, shapes]);
        self.supports.insert(Support::Semantic);
        Ok(Self::is_true(claim))
    }
}

/// Which part of the quantified function's result a helper is typed by.
enum Typed {
    /// The domains alone.
    Domains,
    /// The domains, then the result.
    Whole,
    /// The domains, then the output half of the result pair.
    Output,
}
