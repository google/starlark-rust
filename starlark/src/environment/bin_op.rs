use crate::values::cell::ObjectRef;
use crate::values::error::ValueError;
use crate::values::TypedValue;
use crate::values::Value;
use std::any::TypeId;
use std::collections::HashMap;
use std::fmt;

/// Define certain global binary operators.
///
/// Most custom type operations are defined using virtual functions on [`Value`],
/// e. g. unary plus or equals.
///
/// However, for certain type the operation may be defined by RHS, e. g.
/// multiplication `integer * collection` should be defined for collection
/// type, not for collection type, i. e. for RHS, not LHS.
///
/// Python to solve this riddle allows overriding `__mul__` on LHS or `__rmul__` or RHS,
/// and `__rmul__` is used when `__mul__` is not defined.
///
/// Starlark-rust could use the same approach, but instead certain binary operations
/// are stored in [`TypeValues`] object similarly to type-defined methods.
#[derive(Eq, PartialEq, Hash, Clone, Copy)]
pub enum CustomBinOp {
    Addition,
    Multiplication,
}

impl fmt::Display for CustomBinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                CustomBinOp::Addition => "+",
                CustomBinOp::Multiplication => "*",
            }
        )
    }
}

/// Global registry of certain binary operators.
#[derive(Default)]
pub(crate) struct BinOpRegistry {
    bin_ops: HashMap<
        (TypeId, TypeId, CustomBinOp),
        Box<dyn Fn(&Value, &Value) -> Result<Value, ValueError>>,
    >,
}

impl BinOpRegistry {
    /// Register a binary operator for a pair of types.
    pub fn register_bin_op<
        A: TypedValue,
        B: TypedValue,
        R: Into<Value>,
        F: Fn(&A, &B) -> Result<R, ValueError> + 'static,
    >(
        &mut self,
        bin_op: CustomBinOp,
        f: F,
    ) {
        let prev = self.bin_ops.insert(
            (TypeId::of::<A>(), TypeId::of::<B>(), bin_op),
            Box::new(move |l, r| {
                let l: ObjectRef<A> = l.downcast_ref().unwrap();
                let r: ObjectRef<B> = r.downcast_ref().unwrap();
                f(&*l, &*r).map(R::into)
            }),
        );
        assert!(
            prev.is_none(),
            "Cannot register operation {} for {} and {} again",
            bin_op,
            A::TYPE,
            B::TYPE
        );
    }

    /// Eval previously registered bin op
    pub fn eval_bin_op(
        &self,
        bin_op: CustomBinOp,
        l: &Value,
        r: &Value,
    ) -> Result<Value, ValueError> {
        let lt = l.get_type_id();
        let rt = r.get_type_id();
        let f = match self.bin_ops.get(&(lt, rt, bin_op)) {
            Some(f) => f,
            None => {
                return Err(ValueError::OperationNotSupported {
                    op: format!("{}", bin_op),
                    left: l.get_type().to_string(),
                    right: Some(r.get_type().to_string()),
                });
            }
        };
        f(l, r)
    }
}
