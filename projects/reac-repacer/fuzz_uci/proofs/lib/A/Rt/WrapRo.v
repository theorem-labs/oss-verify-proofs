(* reac-repacer/fuzz_uci, build asan: the read-only premise of the runtime wrappers (lib/A/Rt/StrlenDef.v,
   lib/A/Rt/MemchrDef.v), in the form a program walk can carry across a call.
   A wrapper may read bytes of the image's read-only segments in two ways:
   - bytes the runtime model pins (the GOT cells, the flags pointer, real_<fn>, the shadow offset): these are in
     as_owned_static and their values are AR's const cells (the core's Tfib_const), so AR gives them and no
     premise is needed;
   - the musl constants (strlen/memchr read 0x10350 and 0x10368, 8 bytes each) and the caller's own .rodata
     strings: these are NOT owned, and aro_unowned below states them.
   aro_unowned is the in-segment half of fuzz_identity's arodata_okP (its lib/A/Prog/IdentBase.v:20); this unit has no
   IdentBase, so the donor's bridge lemma aro_unowned_of_arodata is not carried. Unlike YG0d's rom_view, it says nothing about owned
   image bytes, so it survives a call whose post keeps only the bytes that are unowned before and after
   (__asan_stack_malloc_*, YG0d.v:298-299): aro_unowned_keep. *)
(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_identity lib/A/Rt/WrapRo.v (origin/ossv/recipes 70952e1c8c9)
   to reac-repacer/fuzz_uci image A (fuzz_uci.asan, sha256 6ea017c24525) on the fuzz_uci A core (276afc86670b): module
   paths; record class TfibSyms -> UciSyms (code only; the donor's own Modified-by lines are kept as its record).
   Numerals moved by symbol + offset from the fuzz_identity unstripped twin to the fuzz_uci unstripped twin (each
   function is the same code up to pc-relative fields: bytecmp 7daa0e2a03d9 with repin_check 9cbc3553c09e's target pass); a .got slot moves to the slot that
   holds the same symbol. Every changed numeral, old -> new, symbol + offset in fuzz_identity.asan [occurrences]:
     (none: this file has no numeral that changes)
   Also: dropped the Require of lib/A/Prog/IdentBase (fuzz_identity's program base; this unit has none) and the one lemma that used it, aro_unowned_of_arodata (arodata_okP -> aro_unowned); neither contract uses it. aro_unowned and aro_unowned_keep are unchanged.
   Unchanged on purpose: 0x10350, 0x10368, 0x10370 (musl's HIGHS/ONES constants and their end: the same address in
   both images, read by the auipc/ld pairs at strlen+0x3c..0x48 and memchr+0x58..0x64).
   This file only. *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YM05.
Import ListNotations.
Open Scope Z_scope.
Definition aro_unowned (segs : list Segment) (B : asyms) (rd : reader) : Prop :=
forall a, in_rom segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
rd a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
Lemma aro_unowned_keep : forall segs B (rd rd' : reader),
aro_unowned segs B rd ->
(forall a, in_rom segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) -> rd' a = rd a) ->
aro_unowned segs B rd'.
Proof. intros segs B rd rd' HR Hk a Ha Ho He. rewrite (Hk a Ha Ho He). exact (HR a Ha Ho He). Qed.
