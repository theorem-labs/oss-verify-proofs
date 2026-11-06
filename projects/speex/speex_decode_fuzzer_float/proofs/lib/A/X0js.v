(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1dg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.PA Require Import X1e9 X1e5.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0j2 X02b X00b X0jg X0jw X0ju.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19l X0ta X0ra X19x X1ab X1a9.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ta OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X1ab OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X1a9.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Ltac showpc := match goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.

Definition psglob_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (XS3_LO, XS3_HI)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp) /\ stk bsegs m' XS3_LO XS3_HI.

Lemma psglob_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (lo : Z),
a0 = Z_to_bv 64 0x100ab0 -> a1 = Z_to_bv 64 6464 -> a2 = Z_to_bv 64 0 ->
stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> 0x800c0000 <= lo ->
ro_cells bsegs m 0xfc108 [C8 (Z_to_bv 64 0x1975e8); C8 (Z_to_bv 64 0x1032b8); C8 (Z_to_bv 64 0x105ab8);
C8 (Z_to_bv 64 0x1067a8); C8 (Z_to_bv 64 0x1067b0); C8 (Z_to_bv 64 0x1067a0);
C8 (Z_to_bv 64 0xfe040)] ->
ro_cells bsegs m 0xfe040 [C8 (Z_to_bv 64 0xf1af8)] ->
ro_cells bsegs m 0x105ab8 [C8 (Z_to_bv 64 0x7fff8000)] ->
ro_cells bsegs m 0x197660 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
stk bsegs m XS3_LO XS3_HI ->
mem_inv bsegs m ->
evt bsegs (psglob_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x694e0) fc None m (seg_rom bsegs)).
Proof.
intros until lo. intros -> -> -> ST LO LOLO UG2 RMS SHC THR SC2 MI.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (XS3_LO, XS3_HI)] m) as MU.
pose proof (wmono_refl bsegs m) as WM.
carve_frame 64%nat ST.
xsteps_to 0x6987c%Z.
release_frame FR ST (bv_unsigned sp).
xstep.
lazymatch goal with H : stk bsegs ?mm 2147582294 2147583102 |- _ =>
destruct (stk_window mm 2147582294 2147583102 0x80018156 0x328 H ltac:(lia) ltac:(lia) ltac:(lia)) as (SA & (junk2 & DST) & SB); clear H end.
call memset_callZ; [exact DST| assumption| lia| lia| lia| lia|].
lazymatch goal with P : rw_cells bsegs ?mm 2147582294 [CB _ _] |- _ =>
pose proof (stk_unwindow mm 2147582294 2147583102 _ 0x328 _ SA P ltac:(reflexivity) SB ltac:(lia) ltac:(lia)) as SC2'; clear SA SB P end.
unfold psglob_post. sys_finish.
Qed.

End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Ltac showpc := match goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.

Definition psglob_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (XS3_LO, XS3_HI)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp) /\ stk asegs m' XS3_LO XS3_HI.

Lemma psglob_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (lo : Z),
a0 = Z_to_bv 64 0xf8230 -> a1 = Z_to_bv 64 6528 -> a2 = Z_to_bv 64 0 ->
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> 0x800c0000 <= lo ->
ro_cells asegs m 0xf3888 [C8 (Z_to_bv 64 0x18eda8); C8 (Z_to_bv 64 0xfaa78); C8 (Z_to_bv 64 0xfd278);
C8 (Z_to_bv 64 0xfdf68); C8 (Z_to_bv 64 0xfdf70); C8 (Z_to_bv 64 0xfdf60);
C8 (Z_to_bv 64 0xf57c0)] ->
ro_cells asegs m 0xf57c0 [C8 (Z_to_bv 64 0xe9284)] ->
ro_cells asegs m 0xfd278 [C8 (Z_to_bv 64 0x7fff8000)] ->
ro_cells asegs m 0x18ee20 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
stk asegs m XS3_LO XS3_HI ->
mem_inv asegs m ->
evt asegs (psglob_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x693f4) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros -> -> -> ST LO LOLO UG2 RMS SHC THR SC2 MI.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (XS3_LO, XS3_HI)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 64%nat ST.
xsteps_to 0x69790%Z.
release_frame FR ST (bv_unsigned sp).
xstep.
lazymatch goal with H : stk asegs ?mm 2147577926 2147578742 |- _ =>
destruct (stk_window mm 2147577926 2147578742 0x80017046 0x330 H ltac:(lia) ltac:(lia) ltac:(lia)) as (SA & (junk2 & DST) & SB); clear H end.
call memset_callZ; [exact DST| assumption| lia| lia| lia| lia|].
lazymatch goal with P : rw_cells asegs ?mm 2147577926 [CB _ _] |- _ =>
pose proof (stk_unwindow mm 2147577926 2147578742 _ 0x330 _ SA P ltac:(reflexivity) SB ltac:(lia) ltac:(lia)) as SC2'; clear SA SB P end.
unfold psglob_post. sys_finish.
Qed.

