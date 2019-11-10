// Copyright 2019 The Starlark in Rust Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! List/dict/set comprenension evaluation.

use crate::eval::eval_expr;
use crate::eval::expr::AstClauseCompiled;
use crate::eval::expr::ClauseCompiled;
use crate::eval::set_expr;
use crate::eval::t;
use crate::eval::EvalException;
use crate::values::context::EvaluationContext;
use crate::values::context::EvaluationContextEnvironment;

pub(crate) fn eval_one_dimensional_comprehension<
    E: EvaluationContextEnvironment,
    F: FnMut(&mut EvaluationContext<E>) -> Result<(), EvalException>,
>(
    expr: &mut F,
    clauses: &[AstClauseCompiled],
    context: &mut EvaluationContext<E>,
) -> Result<(), EvalException> {
    if let Some((first, tl)) = clauses.split_first() {
        match &first.node {
            ClauseCompiled::If(ref cond) => {
                if !eval_expr(cond, context)?.to_bool() {
                    return Ok(());
                }
                eval_one_dimensional_comprehension(expr, tl, context)
            }
            ClauseCompiled::For(ref var, ref iter) => {
                let iterable = eval_expr(iter, context)?;
                for item in &t(iterable.iter(), iter)? {
                    set_expr(var, context, item)?;

                    eval_one_dimensional_comprehension(expr, tl, context)?;
                }

                Ok(())
            }
        }
    } else {
        expr(context)
    }
}
