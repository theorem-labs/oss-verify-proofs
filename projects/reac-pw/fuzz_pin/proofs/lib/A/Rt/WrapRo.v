(* libreac/fuzz_identity, build asan: the read-only premise of the runtime wrappers (lib/A/Rt/StrlenDef.v,
   lib/A/Rt/MemchrDef.v), in the form a program walk can carry across a call.
   A wrapper may read bytes of the image's read-only segments in two ways:
   - bytes the runtime model pins (the GOT cells, the flags pointer, real_<fn>, the shadow offset): these are in
     as_owned_static and their values are AR's const cells (the core's Tfib_const), so AR gives them and no
     premise is needed;
   - the musl constants (strlen/memchr read 0x10350 and 0x10368, 8 bytes each) and the caller's own .rodata
     strings: these are NOT owned, and aro_unowned below states them.
   aro_unowned is the in-segment half of arodata_okP (lib/A/Prog/IdentBase.v:20), the fact the program walks
   carry; aro_unowned_of_arodata turns one into the other. Unlike YG0d's rom_view, it says nothing about owned
   image bytes, so it survives a call whose post keeps only the bytes that are unowned before and after
   (__asan_stack_malloc_*, YG0d.v:298-299): aro_unowned_keep. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_identity/lib/A/Rt/WrapRo.v at origin/ossv/recipes 6ebe35ba632; module paths changed to reac-pw/fuzz_pin; the Require of the program base A/Prog/IdentBase.v and the lemma aro_unowned_of_arodata that used it are removed. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YM05.
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
