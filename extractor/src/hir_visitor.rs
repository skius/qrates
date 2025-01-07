// Licensed under the MIT license <LICENSE or
// http://opensource.org/licenses/MIT>. This file may not be copied,
// modified, or distributed except according to those terms.

use crate::converters::ConvertInto;
use crate::mir_visitor::MirVisitor;
use crate::table_filler::TableFiller;
use crate::thir_storage;
use corpus_database::{tables::Tables, types};
use hir::def_id::LocalDefId;
use rustc_hir::def::DefKind;
use rustc_hir::{
    self as hir,
    intravisit::{self, Visitor},
    HirId,
};
use rustc_middle::hir::map::Map as HirMap;
use rustc_middle::mir::{self, HasLocalDecls};
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;
use rustc_span::Span;
use std::collections::HashMap;
use std::mem;

extern crate rustc_ast_ir;

pub(crate) struct HirVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    hir_map: &'a HirMap<'tcx>,
    filler: TableFiller<'a, 'tcx>,
    current_module: types::Module,
    current_item: Option<types::Item>,
}

impl<'a, 'tcx> HirVisitor<'a, 'tcx> {
    pub fn new(
        mut tables: Tables,
        build: types::Build,
        session: &'a Session,
        hir_map: &'a HirMap<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> Self {
        let (root_module,) = tables.register_root_modules(build);
        let filler = TableFiller::new(tcx, session, tables);
        Self {
            tcx,
            hir_map,
            filler,
            current_module: root_module,
            current_item: None,
        }
    }
    pub fn filler(self) -> TableFiller<'a, 'tcx> {
        self.filler
    }
    fn visit_submodule(
        &mut self,
        def_id: types::DefPath,
        name: &str,
        visibility: types::TyVisibility,
        module: &'tcx hir::Mod,
        id: HirId,
    ) {
        let parent_module = self.current_module;
        let (new_module,) = self.filler.tables.register_submodules(
            def_id,
            parent_module,
            name.to_string(),
            visibility,
            String::from("NONE"),
        );
        self.current_module = new_module;
        intravisit::walk_mod(self, module, id);
        self.current_module = parent_module;
    }
    fn visit_foreign_submodule(
        &mut self,
        def_id: types::DefPath,
        name: &str,
        visibility: types::TyVisibility,
        abi: &'tcx rustc_target::spec::abi::Abi,
        items: &'tcx [rustc_hir::ForeignItemRef],
        id: HirId,
    ) {
        let parent_module = self.current_module;
        let (new_module,) = self.filler.tables.register_submodules(
            def_id,
            parent_module,
            name.to_string(),
            visibility,
            abi.to_string(),
        );
        self.current_module = new_module;
        self.visit_id(id);
        rustc_ast_ir::walk_list!(self, visit_foreign_item_ref, items);
        self.current_module = parent_module;
    }
    fn visit_static(
        &mut self,
        def_id: types::DefPath,
        name: &str,
        visibility: types::TyVisibility,
        mutability: types::Mutability,
        typ: &'tcx hir::Ty,
        id: HirId,
        body_id: hir::BodyId,
    ) {
        let (item,) = self.filler.tables.register_static_definitions(
            def_id,
            self.current_module,
            name.to_string(),
            visibility,
            mutability,
        );
        let old_item = mem::replace(&mut self.current_item, Some(item));
        self.visit_id(id);
        self.visit_ty(typ);
        self.visit_nested_body(body_id);
        self.current_item = old_item;
    }
    /// Extract information from unoptmized MIR.
    fn visit_mir(
        &mut self,
        body_id: rustc_span::def_id::LocalDefId,
        body: &mir::Body<'tcx>,
        safety_map: HashMap<Span, rustc_middle::thir::BlockSafety>,
    ) {
        let error = format!("Mir outside of an item: {:?}", body.span);
        let item = self.current_item.expect(&error);
        let mut mir_visitor =
            MirVisitor::new(self.tcx, item, body_id, body, &mut self.filler, safety_map);
        mir_visitor.visit();
    }
    /// Extract information from THIR.
    // fn visit_thir(&mut self, body_id: rustc_span::def_id::LocalDefId, body: &rustc_middle::thir::Thir<'tcx>) {
    //     let error = format!("THIR outside of an item: {:?}", body_id);
    //     let item = self.current_item.expect(&error);
    //     let mut thir_visitor = ThirVisitor::new(self.tcx, item, body_id, body, &mut self.filler);
    //     thir_visitor.visit();
    // }
    fn visit_type(
        &mut self,
        item: &'tcx hir::Item,
        def_path: types::DefPath,
        def_id: rustc_span::def_id::LocalDefId,
        name: &str,
        visibility: types::TyVisibility,
        kind: types::TyDefKind,
    ) {
        let typ = self
            .filler
            .register_type(self.tcx.type_of(def_id).skip_binder());
        let (item_id,) = self.filler.tables.register_type_defs(
            typ,
            def_path,
            name.to_string(),
            visibility,
            kind,
        );
        let old_item = mem::replace(&mut self.current_item, Some(item_id));
        intravisit::walk_item(self, item);
        self.current_item = old_item;
    }
    /// Retrieves the parameter types and the return type for the function with `def_id`.
    fn get_fn_param_and_return_types(
        &mut self,
        def_id: LocalDefId,
    ) -> (Vec<types::Type>, types::Type) {
        let mir = self.tcx.optimized_mir(def_id);
        let return_type = self.filler.register_type(mir.return_ty());
        let local_decls = mir.local_decls();
        let param_types = mir
            .args_iter()
            .map(|param| self.filler.register_type(local_decls[param].ty))
            .collect();
        (param_types, return_type)
    }
}

impl<'a, 'tcx> Visitor<'tcx> for HirVisitor<'a, 'tcx> {
    type Map = HirMap<'tcx>;
    type NestedFilter = rustc_middle::hir::nested_filter::All;
    fn visit_item(&mut self, item: &'tcx hir::Item) {
        let name: &str = &item.ident.name.as_str();
        let visibility = self.tcx.visibility(item.owner_id.def_id);
        let visibility: types::TyVisibility = visibility.convert_into();
        let def_path = self.filler.resolve_local_def_id(item.owner_id.def_id);
        let def_id = item.owner_id.def_id;
        match &item.kind {
            hir::ItemKind::Mod(ref module) => {
                // This avoids visiting the root module.
                self.visit_submodule(def_path, name, visibility, module, item.hir_id());
            }
            hir::ItemKind::ForeignMod { ref abi, ref items } => {
                self.visit_foreign_submodule(def_path, name, visibility, abi, items, item.hir_id());
            }
            hir::ItemKind::Static(ref typ, ref mutability, body_id) => {
                self.visit_static(
                    def_path,
                    name,
                    visibility,
                    mutability.convert_into(),
                    typ,
                    item.hir_id(),
                    *body_id,
                );
            }
            // TODO - skius: Pass generics along.
            hir::ItemKind::Const(ref typ, _generics, body_id) => {
                self.visit_static(
                    def_path,
                    name,
                    visibility,
                    types::Mutability::Const,
                    typ,
                    item.hir_id(),
                    *body_id,
                );
            }
            hir::ItemKind::Impl(hir::Impl {
                // unsafety,
                polarity,
                defaultness,
                // constness,
                of_trait,
                ..
            }) => {
                let interned_type = self
                    .filler
                    .register_type(self.tcx.type_of(def_id).skip_binder());
                let (item_id,) = self.filler.tables.register_impl_definitions(
                    def_path,
                    self.current_module,
                    name.to_string(),
                    visibility,
                    // TODO - skius(2): DISCUSS: What to do here?
                    types::Unsafety::Unknown,
                    // unsafety.convert_into(),
                    polarity.convert_into(),
                    defaultness.convert_into(),
                    // TODO - skius: DISCUSS: What to do here?
                    // constness.convert_into(),
                    types::Constness::Unknown,
                    interned_type,
                );
                if let Some(trait_ref) = of_trait {
                    if let Some(trait_def_id) = trait_ref.trait_def_id() {
                        let trait_def_path = self.filler.resolve_def_id(trait_def_id);
                        self.filler.tables.register_trait_impls(
                            item_id,
                            interned_type,
                            trait_def_path,
                        );
                    }
                }
                let old_item = mem::replace(&mut self.current_item, Some(item_id));
                intravisit::walk_item(self, item);
                self.current_item = old_item;
            }
            hir::ItemKind::GlobalAsm(_) => {
                self.filler.tables.register_global_asm_blocks(
                    def_path,
                    self.current_module,
                    name.to_string(),
                    visibility,
                );
            }
            hir::ItemKind::TyAlias(..) => self.visit_type(
                item,
                def_path,
                def_id,
                name,
                visibility,
                types::TyDefKind::TyAlias,
            ),
            // TODO - skius(2): Remove OpaqueTy downstream
            // hir::ItemKind::OpaqueTy(..) => self.visit_type(
            //     item,
            //     def_path,
            //     def_id,
            //     name,
            //     visibility,
            //     types::TyDefKind::OpaqueTy,
            // ),
            hir::ItemKind::Enum(..) => self.visit_type(
                item,
                def_path,
                def_id,
                name,
                visibility,
                types::TyDefKind::Enum,
            ),
            hir::ItemKind::Struct(..) => self.visit_type(
                item,
                def_path,
                def_id,
                name,
                visibility,
                types::TyDefKind::Struct,
            ),
            hir::ItemKind::Union(..) => self.visit_type(
                item,
                def_path,
                def_id,
                name,
                visibility,
                types::TyDefKind::Union,
            ),
            hir::ItemKind::Trait(is_auto, unsafety, _, _, trait_items) => {
                let is_marker = self.tcx.trait_def(def_id).is_marker;
                let (item_id,) = self.filler.tables.register_traits(
                    def_path,
                    name.to_string(),
                    visibility,
                    is_auto.convert_into(),
                    is_marker,
                    unsafety.convert_into(),
                );
                for trait_item in *trait_items {
                    let trait_item_def_path = self
                        .filler
                        .resolve_local_def_id(trait_item.id.owner_id.def_id);
                    self.filler.tables.register_trait_items(
                        item_id,
                        trait_item_def_path,
                        // TODO - skius: DISCUSS: What to do here?
                        types::Defaultness::Unknown,
                        // self.tcx
                        //     .impl_defaultness(trait_item.id.owner_id.def_id)
                        //     .convert_into(),
                    )
                }
                let old_item = mem::replace(&mut self.current_item, Some(item_id));
                intravisit::walk_item(self, item);
                self.current_item = old_item;
            }
            hir::ItemKind::ExternCrate(_)
            | hir::ItemKind::Use(_, _)
            | hir::ItemKind::Macro(_, _)
            | hir::ItemKind::Fn(_, _, _)
            | hir::ItemKind::TraitAlias(_, _) => {
                let (item_id,) = self.filler.tables.register_items(
                    def_path,
                    self.current_module,
                    name.to_string(),
                    visibility,
                );
                let old_item = mem::replace(&mut self.current_item, Some(item_id));
                intravisit::walk_item(self, item);
                self.current_item = old_item;
            }
        }
    }
    fn visit_fn(
        &mut self,
        fn_kind: intravisit::FnKind<'tcx>,
        fn_def: &'tcx hir::FnDecl,
        body_id: hir::BodyId,
        _span: Span,
        def_id: LocalDefId,
    ) {
        let visibility = self.tcx.visibility(def_id);
        let def_path = self.filler.resolve_local_def_id(def_id);
        let (param_types, return_type) = self.get_fn_param_and_return_types(def_id);
        let (function,) = match fn_kind {
            intravisit::FnKind::Method(_name, method_sig) => {
                self.filler.tables.register_function_definitions(
                    def_path,
                    self.current_module,
                    visibility.convert_into(),
                    method_sig.header.safety.convert_into(),
                    method_sig.header.abi.name().to_string(),
                    return_type,
                )
            }
            intravisit::FnKind::ItemFn(_name, _generics, header) => {
                self.filler.tables.register_function_definitions(
                    def_path,
                    self.current_module,
                    visibility.convert_into(),
                    header.safety.convert_into(),
                    header.abi.name().to_string(),
                    return_type,
                )
            }
            intravisit::FnKind::Closure => self.filler.tables.register_function_definitions(
                def_path,
                self.current_module,
                types::TyVisibility::Unknown,
                types::Unsafety::Unknown,
                "Closure".to_string(),
                return_type,
            ),
        };
        let old_item = mem::replace(&mut self.current_item, Some(function));
        intravisit::walk_fn(self, fn_kind, fn_def, body_id, def_id);
        self.current_item = old_item;
        for (i, param_type) in param_types.into_iter().enumerate() {
            self.filler
                .tables
                .register_function_parameter_types(function, i.into(), param_type);
        }

        // TODO - skius(3): prettify
        // get thir body
        // let thir_body: &rustc_middle::thir::Thir<'tcx> = &self.tcx.thir_body(def_id).expect("thir body").0.borrow();
        // for block in &thir_body.blocks {
        //     let block: &rustc_middle::thir::Block = block;
        //     let safety_mode = block.safety_mode;
        //     // match safety_mode {
        //     //     rustc_middle::thir::BlockSafety::Safe => {
        //     //         // eprint!("fn: {:?} block: {:?} safety: {:?}\n", def_id, block, safety_mode);
        //     //     }
        //     //     rustc_middle::thir::BlockSafety::BuiltinUnsafe => {
        //     //         // eprint!("fn: {:?} block: {:?} safety: {:?}\n", def_id, block, safety_mode);
        //     //     }
        //     //     rustc_middle::thir::BlockSafety::ExplicitUnsafe(source_info) => {
        //     //         // eprint!("fn: {:?} block: {:?} safety: {:?}\n", def_id, block, safety_mode);
        //     //     }
        //     // }
        // }
        // run check unsafety
        // print to stderr
        // eprint!("fn: {:?}\n", def_id);
        // panic!("test niels");
    }
    fn visit_foreign_item(&mut self, item: &'tcx hir::ForeignItem) {
        let def_path = self.filler.resolve_local_def_id(item.owner_id.def_id);
        let def_id = item.owner_id.def_id;
        let visibility = self.tcx.visibility(def_id);
        let visibility = visibility.convert_into();
        let item_id = match item.kind {
            hir::ForeignItemKind::Fn(..) => {
                let fn_sig = self.tcx.fn_sig(def_id);
                let fn_sig = fn_sig.skip_binder();
                let return_type = self.filler.register_type(fn_sig.skip_binder().output());
                let (function,) = self.filler.tables.register_function_definitions(
                    def_path,
                    self.current_module,
                    visibility,
                    types::Unsafety::Unsafe,
                    "ForeignItem".to_string(),
                    return_type,
                );
                for (i, input) in fn_sig.inputs().iter().enumerate() {
                    let param_type = self.filler.register_type(*input.skip_binder());
                    self.filler.tables.register_function_parameter_types(
                        function,
                        i.into(),
                        param_type,
                    );
                }
                Some(function)
            }
            // TODO - skius(2): Use _safety downstream?
            hir::ForeignItemKind::Static(_, mutability, _safety) => {
                let name: &str = &item.ident.name.as_str();
                let (item,) = self.filler.tables.register_static_definitions(
                    def_path,
                    self.current_module,
                    name.to_string(),
                    visibility,
                    mutability.convert_into(),
                );
                Some(item)
            }
            hir::ForeignItemKind::Type => None,
        };
        if let Some(item_id) = item_id {
            let old_item = mem::replace(&mut self.current_item, Some(item_id));
            intravisit::walk_foreign_item(self, item);
            self.current_item = old_item;
        } else {
            intravisit::walk_foreign_item(self, item);
        }
    }
    fn visit_body(&mut self, body: &hir::Body<'tcx>) {
        intravisit::walk_body(self, body);
        let id = body.id();
        let def_id = self.hir_map.body_owner_def_id(id);
        // let def = WithOptConstParam::unknown(def_id.to_def_id());
        let def_kind = self.tcx.def_kind(def_id);
        let mir_body = match def_kind {
            DefKind::Const
            | DefKind::Static { .. }
            | DefKind::AssocConst
            | DefKind::Ctor(..)
            | DefKind::AnonConst
            | DefKind::InlineConst => self.tcx.mir_for_ctfe(def_id.to_def_id()),
            _ => self.tcx.optimized_mir(def_id),
        };
        // self.tcx.ensure_with_value().mir_built(def_id);
        // self.tcx.ensure_with_value().thir_body(def_id);

        // run the query if for some reason it has not been run yet
        let _ = self.tcx.thir_body(def_id);
        let thir_body = unsafe { thir_storage::retrieve_thir_body(self.tcx, def_id) };
        // let res = self.tcx.thir_body(def_id).expect("thir body").0;
        // // self.tcx.ensure_with_value().mir_built(def_id);
        // // self.tcx.ensure_with_value().thir_body(def_id);

        // let thir_body: &rustc_middle::thir::Thir<'tcx> = &res.borrow();

        // // Because MIR does not have safety associated to its scopes anymore, we need to extract it from THIR.
        // // Safety is stored in blocks in THIR.

        let def_path = self.filler.resolve_local_def_id(def_id);

        let mut block_hir_id_to_safety_map = HashMap::new();
        let mut span_to_safety_map: HashMap<Span, rustc_middle::thir::BlockSafety> = HashMap::new();
        if let Some(thir_body) = thir_body {
            // // Collect safety information from THIR blocks
            for (block_id, block) in thir_body.blocks.iter_enumerated() {
                let block: &rustc_middle::thir::Block = block;
                let block_id: rustc_middle::thir::BlockId = block_id;
                let safety_mode = block.safety_mode;
                let item_local_id = block.region_scope.id;
                // The owner id is the LocalDefId of the directly enclosing item-like.
                let owner_id = rustc_hir::OwnerId { def_id: def_id };
                let block_hir_id = HirId {
                    owner: owner_id,
                    local_id: item_local_id,
                };
                block_hir_id_to_safety_map.insert(block_hir_id, safety_mode);
                span_to_safety_map.insert(block.span, safety_mode);

                self.filler.tables.register_thir_blocks(def_path, Some(safety_mode).convert_into());
            }
        } else {
            eprintln!("No THIR body found for {:?}", def_id);
        }


        self.visit_mir(def_id, mir_body, span_to_safety_map);
    }
    fn nested_visit_map<'this>(&'this mut self) -> Self::Map {
        self.tcx.hir()
    }
}
