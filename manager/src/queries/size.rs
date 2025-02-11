//! Report unsafe block sizes by MIR statements.

use super::utils::BuildResolver;
use super::utils::GroupByIterator;
use crate::write_csv;
use corpus_database::tables::Loader;
use corpus_database::types::ThirBlock;
use corpus_database::types::ThirExpr;
use corpus_queries_derive::datapond_query;
use std::collections::{HashMap, HashSet};
use std::path::Path;

pub fn query(loader: &Loader, report_path: &Path) {
    let mut seen_scopes = HashSet::new();
    let build_resolver = BuildResolver::new(loader);
    let unsafe_statements = loader.load_unsafe_statements();
    let unsafe_blocks_by_stmts = unsafe_statements.iter().safe_group_by(
        |(build, _stmt, _block, _index, _kind, unsafe_scope, check_mode)| {
            (build, unsafe_scope, check_mode)
        },
    );
    let unsafe_blocks_sizes_by_stmts: Vec<_> = unsafe_blocks_by_stmts
        .into_iter()
        .map(|((build, unsafe_scope, check_mode), group)| {
            assert!(
                !seen_scopes.contains(unsafe_scope),
                "duplicate scope: {:?} {:?}",
                build,
                unsafe_scope
            );
            seen_scopes.insert(unsafe_scope);
            (*build, unsafe_scope, check_mode, group.count())
        })
        .collect();

    let unsafe_terminators = loader.load_unsafe_terminators();
    let unsafe_blocks_by_terminators = unsafe_terminators.iter().safe_group_by(
        |(build, _block, _kind, unsafe_scope, check_mode)| (build, unsafe_scope, check_mode),
    );
    let unsafe_blocks_sizes_by_terminators: HashMap<_, _> = unsafe_blocks_by_terminators
        .into_iter()
        .map(|((build, unsafe_scope, check_mode), group)| {
            ((*build, unsafe_scope, check_mode), group.count())
        })
        .collect();

    let mut unsafe_block_sizes: Vec<_> = unsafe_blocks_sizes_by_stmts
        .into_iter()
        .map(|(build, unsafe_scope, check_mode, statement_count)| {
            let terminator_count = unsafe_blocks_sizes_by_terminators
                .get(&(build, unsafe_scope, check_mode))
                .cloned()
                .unwrap_or(0);
            (
                build,
                unsafe_scope,
                check_mode,
                statement_count,
                terminator_count,
            )
        })
        .collect();
    for ((build, unsafe_scope, check_mode), terminator_count) in unsafe_blocks_sizes_by_terminators
    {
        if !seen_scopes.contains(unsafe_scope) {
            unsafe_block_sizes.push((build, unsafe_scope, check_mode, 0, terminator_count))
        }
    }

    let unsafe_block_sizes = unsafe_block_sizes.into_iter().map(
        |(build, unsafe_scope, check_mode, statement_count, terminator_count)| {
            (
                build,
                build_resolver.resolve(build),
                unsafe_scope,
                check_mode.to_string(),
                statement_count,
                terminator_count,
            )
        },
    );
    write_csv!(report_path, unsafe_block_sizes);
}


pub fn new_query(loader: &Loader, report_path: &Path) {
    let build_resolver = BuildResolver::new(loader);
    let unsafe_thir_stmts = loader.load_unsafe_thir_stmts();
    let unsafe_thir_blocks_by_stmts = unsafe_thir_stmts.iter().safe_group_by(
        |(build, _stmt, block, _index, check_mode)| {
            (build, block, check_mode)
        },
    );
    let unsafe_thir_blocks_sizes_by_stmts: Vec<_> = unsafe_thir_blocks_by_stmts
        .into_iter()
        .map(|((build, block, check_mode), group)| {
            (*build, block, check_mode, group.count())
        })
        .collect();

    let unsafe_thir_blocks_sizes_by_stmts_map: HashMap<ThirBlock, usize> = unsafe_thir_blocks_sizes_by_stmts.iter().map(|(build, block, check_mode, statement_count)| (**block, *statement_count)).collect();

    // TODO: expressions in thir would be a good metrics too

    // TODO: don't have terminators in thir (yet)

    // TODO (2025-02-08): terminators by counting Call exprs, and also make statement_count + 1 by also counting the
    // block's expression, if it exists.
    // Add call_expr_count as well. count both inside statements and inside the block's expression.

    // actually: let's do
    // - has_trailing_expr: bool
    // - call_expr_count: usize

    let NO_THIR_EXPR = 0u64.into();
    let block_to_has_trailing_expr: HashMap<ThirBlock, bool> = loader.load_thir_block_expr().iter().map(|(block, expr)| (*block, *expr != NO_THIR_EXPR)).collect();

    // let unsafe_thir_block_call_expr_sizes = loader.load_thir_exprs().iter().filter(|(expr, block, ty, span)| {

    // })

    let mut v = vec![];
    for i in 0..10000 {
        v.push([0u8 ;3]);
    }
    Box::leak(Box::new(v));

    let blocks_and_call_exprs;
    datapond_query! {
        load loader {
            relations(thir_exprs, thir_exprs_call),
        }

        output blocks_and_call_exprs(
            block: ThirBlock,
            call_expr: ThirExpr,
        )

        blocks_and_call_exprs(block, expr) :- thir_exprs_call(.expr=expr),
            thir_exprs(.expr=expr, .block=block).

    };

    let unsafe_thir_blocks_to_call_expr_count: HashMap<ThirBlock, usize> = blocks_and_call_exprs.elements.iter().safe_group_by(|(block, _expr)| *block)
        .into_iter()
        .map(|(block, group)| (block, group.count()))
        .collect();



    let unsafe_blocks = loader.load_unsafe_thir_blocks();

    let unsafe_thir_block_sizes = unsafe_blocks.iter().map(
        |(build, _def_path, block, _span_expansion, check_mode, _span)| {
            (
                build,
                build_resolver.resolve(*build),
                block,
                check_mode.to_string(),
                unsafe_thir_blocks_sizes_by_stmts_map.get(&block).copied().unwrap_or(0),
                unsafe_thir_blocks_to_call_expr_count.get(&block).copied().unwrap_or(0),
                block_to_has_trailing_expr.get(&block).copied().unwrap_or(false),
            )
        },
    );

    write_csv!(report_path, unsafe_thir_block_sizes);
}