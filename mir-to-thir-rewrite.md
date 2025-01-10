mir_cfgs( ==> thir_bodies
    item: Item, ==> keep
    body_def_path: DefPath, ==> keep 
    root_scope: auto Scope ==> root_block?
)

scopes( ==> thir_blocks?
    parent: Scope, ==> parent: ThirBlock?
    child: auto Scope, ==> child: ThirBlock?
    safety: ScopeSafety, ==> from THIR
    check_mode: BlockCheckMode, ==> from ExplicitUnsafe(hir_id)
    explicit_unsafe_group: u32, // this may most closely match up with blocks, so redundant unless we need to know some relative position within all _unsafe_ blocks
    span: Span ==> keep
)


// used to track statements, and terminator relationships in schema.dl.
// used to track unsafe_statements, unsafe_terminators, unsafe_block_calls, unsafe_block_calls_known_target in derived.dl
// and to track the caller_crate in the all_calls query.
basic_blocks(
...
)

then all kinds of statements have a relation
some statements have additional data (eg statements_assign_use), while others (eg ConstEvalCounter) are a bare-bones `get_fresh_statement()`.
as well as their operands (operands do not appear in queries yet)
types are registered.


