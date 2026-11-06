(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1dg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.PA Require Import X1e9 X1e5.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0j2 X02b X00b X0jg X0jw X0ju X0jv X0js.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19l X0ta X0ra X19x X1ab X1a9 X1aa X1a7.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ta OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X1ab OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X1a9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X1aa OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X1a7.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Ltac showpc := match goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.

Definition unreg_got (m : mem) : Prop :=
ro_cells bsegs m 0xfc0f8 [C8 (Z_to_bv 64 0x195560)]
/\ ro_cells bsegs m 0xfc108 [C8 (Z_to_bv 64 0x1975e8); C8 (Z_to_bv 64 0x1032b8); C8 (Z_to_bv 64 0x105ab8);
C8 (Z_to_bv 64 0x1067a8); C8 (Z_to_bv 64 0x1067b0); C8 (Z_to_bv 64 0x1067a0);
C8 (Z_to_bv 64 0xfe040)].

Definition unreg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned sp - 240, bv_unsigned sp); (0x103370, 0x103378);
(XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (ODR_LO, ODR_HI)] m m'
/\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp).

Lemma unreg_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (lo : Z),
a0 = Z_to_bv 64 0x100ab0 -> a1 = Z_to_bv 64 GDS_N ->
stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 240 -> 0x800c0000 <= lo ->
unreg_got m ->
ro_cells bsegs m 0x1032d0 [C4 (Z_to_bv 64 1)] ->
rw_cells bsegs m 0x103370 [C8 (Z_to_bv 64 0)] ->
ro_cells bsegs m 0x105ab8 [C8 (Z_to_bv 64 0x7fff8000)] ->
rw_cells bsegs m 0x106798 [C1 (Z_to_bv 8 1)] ->
ro_cells bsegs m 0x10531c [C1 (Z_to_bv 8 1)] ->
ro_cells bsegs m 0x197660 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
ro_cells bsegs m 0xfe040 [C8 (Z_to_bv 64 0xf1af8)] ->
stk bsegs m XS1_LO XS1_HI -> stk bsegs m XS2_LO XS2_HI -> stk bsegs m XS3_LO XS3_HI ->
gds_at m 0x100ab0 asan_gds ->
stk bsegs m ODR_LO ODR_HI ->
mem_inv bsegs m ->
evt bsegs (unreg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x5463c) fc None m (seg_rom bsegs)).
Proof.
intros until lo. intros -> -> ST LO LOLO (G1 & G2) RG MUX SHC AI CP THR RMS SC1 SC2 SC3 GDS ODRS MI.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (0x103370, 0x103378);
(XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (ODR_LO, ODR_HI)] m) as MU.
pose proof (wmono_refl bsegs m) as WM.
carve_frame 176%nat ST.
xsteps_to 0x546e4%Z.
amo_step. showpc. xstep. showpc. amo_step. showpc. xstep. showpc. xstep. showpc.
xsteps_to 0x547f8%Z.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (GDS1 : gds_at mm 0x100ab0 asan_gds)
by (apply (gds_at_agree _ m _ _ GDS); apply (agree_of_munch _ _ _ _ MU); intros xa Hxa;
rewrite asan_gds_length in Hxa; cbn [outside]; lia) end.
clear GDS.
call (unreg_loop asan_gds GDS_N); [exact asan_gds_ok| reflexivity| lia| exact GDS1| exact AI| exact CP| exact RG| exact SHC| exact THR
| exact RMS| exact SC1| exact SC2| exact SC3| exact ODRS| assumption|].
xsteps_to 0x694e0%Z.
assert (EU176 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -176)) = bv_unsigned sp + -176) by (apply unsigned_lit; lia).
lazymatch goal with H : stk bsegs ?mm 2147582294 2147583102 |- _ => rename H into SCX2 end.
call psglob_spec; [reflexivity| reflexivity| reflexivity| rewrite EU176; exact ST| lia| lia| exact G2| exact RMS| exact SHC| exact THR
| exact SCX2| assumption|].
lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -176))) |- _ => rewrite EU176 in H; rename H into ST end.
xsteps_to 0x54a54%Z.
amo_step. xstep. amo_step. xstep. xstep. xstep.
xsteps_to 0x54b08%Z.
release_frame FR ST (bv_unsigned sp).
xstep.
unfold unreg_post. sys_finish.
Qed.

End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Ltac showpc := match goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.

Definition unreg_got (m : mem) : Prop :=
ro_cells asegs m 0xf3878 [C8 (Z_to_bv 64 0x18cd20)]
/\ ro_cells asegs m 0xf3888 [C8 (Z_to_bv 64 0x18eda8); C8 (Z_to_bv 64 0xfaa78); C8 (Z_to_bv 64 0xfd278);
C8 (Z_to_bv 64 0xfdf68); C8 (Z_to_bv 64 0xfdf70); C8 (Z_to_bv 64 0xfdf60);
C8 (Z_to_bv 64 0xf57c0)].

Definition unreg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 240, bv_unsigned sp); (0xfab30, 0xfab38);
(XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (ODR_LO, ODR_HI)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma unreg_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (lo : Z),
a0 = Z_to_bv 64 0xf8230 -> a1 = Z_to_bv 64 GDS_N ->
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 240 -> 0x800c0000 <= lo ->
unreg_got m ->
ro_cells asegs m 0xfaa90 [C4 (Z_to_bv 64 1)] ->
rw_cells asegs m 0xfab30 [C8 (Z_to_bv 64 0)] ->
ro_cells asegs m 0xfd278 [C8 (Z_to_bv 64 0x7fff8000)] ->
rw_cells asegs m 0xfdf58 [C1 (Z_to_bv 8 1)] ->
ro_cells asegs m 0xfcadc [C1 (Z_to_bv 8 1)] ->
ro_cells asegs m 0x18ee20 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
ro_cells asegs m 0xf57c0 [C8 (Z_to_bv 64 0xe9284)] ->
stk asegs m XS1_LO XS1_HI -> stk asegs m XS2_LO XS2_HI -> stk asegs m XS3_LO XS3_HI ->
gds_at m 0xf8230 asan_gds ->
stk asegs m ODR_LO ODR_HI ->
mem_inv asegs m ->
evt asegs (unreg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x54550) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros -> -> ST LO LOLO (G1 & G2) RG MUX SHC AI CP THR RMS SC1 SC2 SC3 GDS ODRS MI.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (0xfab30, 0xfab38);
(XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (ODR_LO, ODR_HI)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 176%nat ST.
xsteps_to 0x545f8%Z.
amo_step. showpc. xstep. showpc. amo_step. showpc. xstep. showpc. xstep. showpc.
xsteps_to 0x5470c%Z.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (GDS1 : gds_at mm 0xf8230 asan_gds)
by (apply (gds_at_agree _ m _ _ GDS); apply (agree_of_munch _ _ _ _ MU); intros xa Hxa;
rewrite asan_gds_length in Hxa; cbn [outside]; lia) end.
clear GDS.
call (unreg_loop asan_gds GDS_N); [exact asan_gds_ok| reflexivity| lia| exact GDS1| exact AI| exact CP| exact RG| exact SHC| exact THR
| exact RMS| exact SC1| exact SC2| exact SC3| exact ODRS| assumption|].
xsteps_to 0x693f4%Z.
assert (EU176 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -176)) = bv_unsigned sp + -176) by (apply unsigned_lit; lia).
lazymatch goal with H : stk asegs ?mm 2147577926 2147578742 |- _ => rename H into SCX2 end.
call psglob_spec; [reflexivity| reflexivity| reflexivity| rewrite EU176; exact ST| lia| lia| exact G2| exact RMS| exact SHC| exact THR
| exact SCX2| assumption|].
lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -176))) |- _ => rewrite EU176 in H; rename H into ST end.
xsteps_to 0x54968%Z.
amo_step. xstep. amo_step. xstep. xstep. xstep.
xsteps_to 0x54a1c%Z.
release_frame FR ST (bv_unsigned sp).
xstep.
unfold unreg_post. sys_finish.
Qed.

