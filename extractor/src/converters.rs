// Licensed under the MIT license <LICENSE or
// http://opensource.org/licenses/MIT>. This file may not be copied,
// modified, or distributed except according to those terms.

use corpus_database::types;
use rustc_hir as hir;
use rustc_middle::{mir, ty};

pub trait ConvertInto<T> {
    fn convert_into(&self) -> T;
}

impl ConvertInto<types::TyVisibility> for ty::Visibility<rustc_hir::def_id::DefId> {
    fn convert_into(&self) -> types::TyVisibility {
        match self {
            ty::Visibility::Public => types::TyVisibility::Public,
            ty::Visibility::Restricted(_) => types::TyVisibility::Restricted,
        }
    }
}

// TODO - skius(2): Rename Unsafety to Safety?
impl ConvertInto<types::Unsafety> for hir::Safety {
    fn convert_into(&self) -> types::Unsafety {
        match self {
            hir::Safety::Unsafe => types::Unsafety::Unsafe,
            // TODO - skius(2): Rename Normal to Safe?
            hir::Safety::Safe => types::Unsafety::Normal,
        }
    }
}

impl ConvertInto<types::SpanExpansionKind> for rustc_span::hygiene::ExpnKind {
    fn convert_into(&self) -> types::SpanExpansionKind {
        use rustc_span::hygiene::AstPass;
        use rustc_span::hygiene::DesugaringKind;
        use rustc_span::hygiene::ExpnKind::*;
        use rustc_span::hygiene::MacroKind;
        match self {
            Root => types::SpanExpansionKind::Root,
            Macro(MacroKind::Bang, _) => types::SpanExpansionKind::MacroBang,
            Macro(MacroKind::Attr, _) => types::SpanExpansionKind::MacroAttr,
            Macro(MacroKind::Derive, _) => types::SpanExpansionKind::MacroDerive,
            AstPass(AstPass::StdImports) => types::SpanExpansionKind::AstPassStdImports,
            AstPass(AstPass::TestHarness) => types::SpanExpansionKind::AstPassTestHarness,
            AstPass(AstPass::ProcMacroHarness) => types::SpanExpansionKind::AstPassProcMacroHarness,
            Desugaring(DesugaringKind::CondTemporary) => {
                types::SpanExpansionKind::DesugaringCondTemporary
            }
            Desugaring(DesugaringKind::QuestionMark) => {
                types::SpanExpansionKind::DesugaringQuestionMark
            }
            Desugaring(DesugaringKind::TryBlock) => types::SpanExpansionKind::DesugaringTryBlock,
            Desugaring(DesugaringKind::OpaqueTy) => types::SpanExpansionKind::DesugaringOpaqueTy,
            Desugaring(DesugaringKind::Async) => types::SpanExpansionKind::DesugaringAsync,
            Desugaring(DesugaringKind::Await) => types::SpanExpansionKind::DesugaringAwait,
            Desugaring(DesugaringKind::ForLoop) => types::SpanExpansionKind::DesugaringForLoop,
            Desugaring(DesugaringKind::WhileLoop) => types::SpanExpansionKind::DesugaringWhileLoop,
            Desugaring(DesugaringKind::YeetExpr) => types::SpanExpansionKind::DesugaringYeetExpr,
            // TODO - skius: Remove?
            // Desugaring(DesugaringKind::Replace) => types::SpanExpansionKind::DesugaringReplace,
            Inlined => types::SpanExpansionKind::Inlined,
        }
    }
}

impl ConvertInto<types::BlockCheckMode> for hir::BlockCheckMode {
    fn convert_into(&self) -> types::BlockCheckMode {
        use rustc_hir::BlockCheckMode::*;
        use rustc_hir::UnsafeSource::*;
        match self {
            DefaultBlock => types::BlockCheckMode::DefaultBlock,
            UnsafeBlock(CompilerGenerated) => types::BlockCheckMode::UnsafeBlockCompilerGenerated,
            UnsafeBlock(UserProvided) => types::BlockCheckMode::UnsafeBlockUserProvided,
        }
    }
}

impl ConvertInto<types::Mutability> for hir::Mutability {
    fn convert_into(&self) -> types::Mutability {
        match self {
            hir::Mutability::Mut => types::Mutability::Mutable,
            hir::Mutability::Not => types::Mutability::Immutable,
        }
    }
}

impl ConvertInto<types::Constness> for hir::Constness {
    fn convert_into(&self) -> types::Constness {
        match self {
            hir::Constness::Const => types::Constness::Const,
            hir::Constness::NotConst => types::Constness::NotConst,
        }
    }
}

impl ConvertInto<types::BorrowKind> for mir::BorrowKind {
    fn convert_into(&self) -> types::BorrowKind {
        match self {
            mir::BorrowKind::Shared => types::BorrowKind::Shared,
            mir::BorrowKind::Fake(mir::FakeBorrowKind::Shallow) => types::BorrowKind::Shallow,
            // TODO - skius(2): Add Deep borrowkind downstream
            mir::BorrowKind::Fake(mir::FakeBorrowKind::Deep) => types::BorrowKind::Deep,
            mir::BorrowKind::Mut {
                kind,
            } => {
                match kind {
                    mir::MutBorrowKind::Default => types::BorrowKind::Mut,
                    mir::MutBorrowKind::TwoPhaseBorrow => types::BorrowKind::MutTwoPhase,
                    // TODO - skius: Rename our name?
                    mir::MutBorrowKind::ClosureCapture => types::BorrowKind::Unique,
                }
            }
        }
    }
}

impl ConvertInto<types::CastKind> for mir::CastKind {
    fn convert_into(&self) -> types::CastKind {
        match self {
            // TODO - skius(2): use _source ?
            mir::CastKind::PointerCoercion(coercion, _source) => match coercion {
                ty::adjustment::PointerCoercion::ReifyFnPointer => types::CastKind::ReifyFnPointer,
                ty::adjustment::PointerCoercion::UnsafeFnPointer => types::CastKind::UnsafeFnPointer,
                ty::adjustment::PointerCoercion::ClosureFnPointer(usafety) => match usafety {
                    hir::Safety::Unsafe => types::CastKind::UnsafeClosureFnPointer,
                    // TODO - skius: Rename Normal to Safe?
                    hir::Safety::Safe => types::CastKind::NormalClosureFnPointer,
                },
                ty::adjustment::PointerCoercion::MutToConstPointer => {
                    types::CastKind::MutToConstPointer
                }
                ty::adjustment::PointerCoercion::ArrayToPointer => types::CastKind::ArrayToPointer,
                ty::adjustment::PointerCoercion::Unsize => types::CastKind::UnsizePointer,
                ty::adjustment::PointerCoercion::DynStar => types::CastKind::DynStar,
            },
            // TODO - skius(2): Rename below two downstream?
            mir::CastKind::PointerExposeProvenance => types::CastKind::PointerExposeAddress,
            mir::CastKind::PointerWithExposedProvenance => types::CastKind::PointerFromExposedAddress,
            mir::CastKind::IntToInt => types::CastKind::IntToInt,
            mir::CastKind::FloatToInt => types::CastKind::FloatToInt,
            mir::CastKind::IntToFloat => types::CastKind::IntToFloat,
            mir::CastKind::FloatToFloat => types::CastKind::FloatToFloat,
            mir::CastKind::PtrToPtr => types::CastKind::PtrToPtr,
            mir::CastKind::FnPtrToPtr => types::CastKind::FnPtrToPtr,
            mir::CastKind::Transmute => types::CastKind::Transmute,
        }
    }
}

impl<'tcx> ConvertInto<types::AggregateKind> for mir::AggregateKind<'tcx> {
    fn convert_into(&self) -> types::AggregateKind {
        match self {
            mir::AggregateKind::Array(..) => types::AggregateKind::Array,
            mir::AggregateKind::Tuple => types::AggregateKind::Tuple,
            mir::AggregateKind::Adt(..) => types::AggregateKind::Adt,
            mir::AggregateKind::Closure(..) => types::AggregateKind::Closure,
            // TODO - skius: Remove Generator AggregateKind?
            // mir::AggregateKind::Generator(..) => types::AggregateKind::Generator,
            // TODO - skius: 2nd try: not sure why remove. Coroutine exists => Just rename Generator to Coroutine
            mir::AggregateKind::Coroutine(..) => types::AggregateKind::Generator,
            // TODO - skius(2): Add CoroutineClosure downstream
            mir::AggregateKind::CoroutineClosure(..) => types::AggregateKind::CoroutineClosure,
            // TODO - skius(2): Add RawPtr downstream
            mir::AggregateKind::RawPtr(..) => types::AggregateKind::RawPtr,
        }
    }
}

// TODO - skius(2): is rustc_middle::thir::BlockSafety the right type?
impl ConvertInto<types::ScopeSafety> for Option<rustc_middle::thir::BlockSafety> {
    fn convert_into(&self) -> types::ScopeSafety {
        match self {
            Some(rustc_middle::thir::BlockSafety::Safe) => types::ScopeSafety::Safe,
            Some(rustc_middle::thir::BlockSafety::BuiltinUnsafe) => types::ScopeSafety::BuiltinUnsafe,
            // TODO - skius(2): Remove FnUnsafe downstream
            // Some(rustc_middle::thir::BlockSafety::FnUnsafe) => types::ScopeSafety::FnUnsafe,
            Some(rustc_middle::thir::BlockSafety::ExplicitUnsafe(_)) => types::ScopeSafety::ExplicitUnsafe,
            None => types::ScopeSafety::Unknown,
        }
    }
}

impl ConvertInto<types::ImplPolarity> for hir::ImplPolarity {
    fn convert_into(&self) -> types::ImplPolarity {
        match self {
            hir::ImplPolarity::Positive => types::ImplPolarity::Positive,
            hir::ImplPolarity::Negative(_) => types::ImplPolarity::Negative,
        }
    }
}

impl<'tcx> ConvertInto<types::TyPrimitive> for ty::TyKind<'tcx> {
    fn convert_into(&self) -> types::TyPrimitive {
        use types::TyPrimitive::*;
        match self {
            ty::TyKind::Bool => Bool,
            ty::TyKind::Char => Char,
            ty::TyKind::Int(int_ty) => match int_ty {
                ty::IntTy::Isize => Isize,
                ty::IntTy::I8 => I8,
                ty::IntTy::I16 => I16,
                ty::IntTy::I32 => I32,
                ty::IntTy::I64 => I64,
                ty::IntTy::I128 => I128,
            },
            ty::TyKind::Uint(uint_ty) => match uint_ty {
                ty::UintTy::Usize => Usize,
                ty::UintTy::U8 => U8,
                ty::UintTy::U16 => U16,
                ty::UintTy::U32 => U32,
                ty::UintTy::U64 => U64,
                ty::UintTy::U128 => U128,
            },
            ty::TyKind::Float(float_ty) => match float_ty {
                // TODO - skius(2): Make sure F16 and F128 are used downstream
                ty::FloatTy::F16 => F16,
                ty::FloatTy::F32 => F32,
                ty::FloatTy::F64 => F64,
                ty::FloatTy::F128 => F128,
            },
            ty::TyKind::Str => Str,
            ty::TyKind::Never => Never,
            x => unreachable!("Not primitive type: {:?}", x),
        }
    }
}

impl ConvertInto<bool> for hir::IsAuto {
    fn convert_into(&self) -> bool {
        match self {
            hir::IsAuto::Yes => true,
            hir::IsAuto::No => false,
        }
    }
}

impl ConvertInto<types::Defaultness> for hir::Defaultness {
    fn convert_into(&self) -> types::Defaultness {
        match self {
            hir::Defaultness::Default { has_value } => {
                if *has_value {
                    types::Defaultness::DefaultWithValue
                } else {
                    types::Defaultness::DefaultNoValue
                }
            }
            hir::Defaultness::Final => types::Defaultness::Final,
        }
    }
}

impl ConvertInto<types::AdtKind> for ty::AdtKind {
    fn convert_into(&self) -> types::AdtKind {
        match self {
            ty::AdtKind::Struct => types::AdtKind::Struct,
            ty::AdtKind::Union => types::AdtKind::Union,
            ty::AdtKind::Enum => types::AdtKind::Enum,
        }
    }
}

impl ConvertInto<types::AdtVariantIndex> for rustc_target::abi::VariantIdx {
    fn convert_into(&self) -> types::AdtVariantIndex {
        self.index().into()
    }
}
