use corpus_database::types::Item;
use rustc_middle::{thir::{visit::Visitor, ExprId, Thir}, ty::TyCtxt};

use crate::table_filler::TableFiller;

pub(crate) struct ThirVisitor<'a, 'b, 'thir, 'tcx> {
    tcx: TyCtxt<'tcx>,
    item: Item,
    thir: &'thir Thir<'tcx>,
    body_id: ExprId,
    filler: &'a mut TableFiller<'b, 'tcx>,
}

impl<'a, 'b, 'thir, 'tcx: 'thir> ThirVisitor<'a, 'b, 'thir, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        item: Item,
        thir: &'thir Thir<'tcx>,
        body_id: ExprId,
        filler: &'a mut TableFiller<'b, 'tcx>,
    ) -> Self {
        Self { tcx, item, thir, body_id, filler }
    }

    pub fn visit(&mut self) {
        // need to visit params and body.
        // body is an expr.
        self.visit_expr(&self.thir[self.body_id]);
    }
}

impl<'a, 'b, 'thir, 'tcx: 'thir> Visitor<'thir, 'tcx> for ThirVisitor<'a, 'b, 'thir, 'tcx> {
    fn thir(&self) -> &'thir Thir<'tcx> {
        self.thir
    }

    fn visit_expr(&mut self, expr: &'thir rustc_middle::thir::Expr<'tcx>) {
        // do our thing
        eprintln!("Visiting expr: {:?}", expr);

        // visit sub-expressions
        rustc_middle::thir::visit::walk_expr(self, expr);

    }
}