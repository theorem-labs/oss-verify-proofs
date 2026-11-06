# Hypothesis-position values of wire A's taken knock hunks: all DERIVED (rule: the publication owner via the unit owner's ruling, 22:06Z)

188 values across 15 hypothesis-position sentences (Section Hypothesis / Variable types, `mkAF` atom ranges, `KRange`
facts, register indices, return addresses, frame / stack depths) of the hunks taken from knock. EACH is DERIVED from
fuzz_wire's own definitions; range covers every reachable value; 0 STOP. hyp-values.tsv: one row per value
(unit file:line, sentence, value, what it bounds, derivation evidence, verdict).

Image-dependent, derived on the pinned twin fuzz_wire.asan (symbol + offset): the return address 0x3156c (wire's
__asan::Allocator::Allocate + 0x3ac = the pc after the `jal` to __sanitizer::StackDepotPut; knock's own is 0x3108c,
grant's 0x..); the stack depths sp0 - 2272 / 2128 / 64 (sums of the `addi sp, sp, -N` prologues of __wrap_malloc ->
__interceptor_malloc (0x7f0 + 0x60) -> asan_malloc (16) -> Allocate (0x80), DEP_STK 512 covers the deepest store);
AD1g.v's KRange page bounds (`YImgTop.IMG_TOP / 4096`, 34359733495.. = 2^35 - page counts); AFek 131072 / 4097 and
the Nrange / size-class bounds derived from wire's alloc sites.

What the build already re-checks (build #31/#32, rc 0): the TFIB_RANGES facts in all 50 hand-off states (vm_compute,
AD1g.v:154-155); FACTS_fixed (AFem.v:416); segD / D1W_ok discharge D1w (AFiq.v:274, AFix.v:422 / AFjb.v:420).

Note: the first Section g of AFis / AFj6 (lines <780 / <762: Htp, Hra4096, Hj0-Hj4, Hjb_def, HPB250, SEED 0x522f8) is
BYTE-IDENTICAL to grant's W4-relocated text (0 differing numerals vs the donor), so those are grant's own relocated
values (the identical-to-donor arm + port_core's address gate), not taken from knock. The derived set is the post-Put
station (second Section g) and the other knock-new hunks.
