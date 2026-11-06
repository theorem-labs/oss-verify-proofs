# Print Assumptions: wire image-A tree vs fuzz_grant's release (corrected record)

Trees: wire at f921ad8b3805 (its parents e06a69e09264 and 88b42b3e7e49; the lib/A tops are the same theorems as at
4483a8de6e6f), built by cb (rc 0, 1635 targets); fuzz_grant's release, recipes 4f87de75d677, its own dune build (rc 0,
396/396). pa_probe.py (committed beside this file) runs Print Assumptions on every Theorem / Lemma of the 21
composition files and A/AE37.v in each tree, one compile per file under a 3600 s limit.

CORRECTION. The first record listed AF0w.tfib_amalloc_realizes as `closed` in both trees. That was wrong: its probe
compile hit the then 300 s limit at that theorem (rc 124) and the reader took an empty output as `closed`, the same way
on both sides, so the diff showed no difference. pa_probe.py now reads `closed` only from Rocq's own `Closed under the
global context`; a theorem with no output is NO-OUTPUT, never closed. Re-run: AF0w.tfib_amalloc_realizes has 14 axioms,
all allowed (as amalloc_realizes_sec, which its proof applies). No table row is NO-OUTPUT.

Result (pa-diff.txt): 223 theorems in both trees, axiom lists equal (0 differ). Every axiom is a Rocq primitive
(PrimInt63.*, PrimString.*, PrimArray.array) or FunctionalExtensionality.functional_extensionality_dep or
Classical_Prop.classic; no Section variable, no Admitted, no Parameter. Present in one tree only: grant AD1j.mu0 (removed
by the AD1j patch: fuzz_wire registers 0 globals), grant AD2l.GrantB_ok / GrantB_syms = wire AD2l.WireB_ok / WireB_syms
(the record-name renames), grant AE37.zi8_14ea00 / zi8_14f970 (grant's two shadow-byte lemmas; wire's AE37 writes none,
its image has no such bytes), wire AD1v.top_ok_gle (the grown-layout lemma), wire ACej.TRACES_check_copy_U (the U-side
name). An independent fresh CACHE=none build of 88b42b3e7e49 with its own Print Assumptions run (217 tops) agrees with
pa-wire.tsv on every one of its 217 rows.
