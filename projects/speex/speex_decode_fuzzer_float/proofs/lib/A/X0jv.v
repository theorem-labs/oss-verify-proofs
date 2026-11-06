(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0j2 X00b X0jw X0ju.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19l X0ra X1ab X1a9.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X1ab OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X1a9.
Import ListNotations.
Open Scope Z_scope.

Notation UNREG_W :=
[(XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (ODR_LO, ODR_HI)] (only parsing).

Definition unreg_loop_post (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
fun ms' => exists (ra' s0' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' (Z_to_bv 64 0x1975e8) a0' a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 2) (Z_to_bv 64 0x1ca77) (Z_to_bv 64 0x1023f0) (Z_to_bv 64 (2^61)) (Z_to_bv 64 0x103330)
(Z_to_bv 64 0xfe040) (Z_to_bv 64 0x103370) (Z_to_bv 64 0x1032b8) (Z_to_bv 64 0x105ab8) (Z_to_bv 64 0)
t3' t4' t5' t6')
F (Z_to_bv 64 0x549fc) fc None m' (seg_rom bsegs)
/\ munch UNREG_W m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' XS1_LO XS1_HI /\ stk bsegs m' XS2_LO XS2_HI /\ stk bsegs m' XS3_LO XS3_HI
/\ stk bsegs m' ODR_LO ODR_HI.

Lemma unreg_loop : forall (gs : list gdesc) (K : Z)
(ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (sp : word) F fc (m : mem),
Forall (fun g => gd_okb g = true) gs -> Z.of_nat (length gs) = K -> 1 <= K <= GDS_N ->
gds_at m (0x1023f0 - 64 * K) gs ->
rw_cells bsegs m 0x106798 [C1 (Z_to_bv 8 1)] ->
ro_cells bsegs m 0x10531c [C1 (Z_to_bv 8 1)] ->
ro_cells bsegs m 0x1032d0 [C4 (Z_to_bv 64 1)] ->
ro_cells bsegs m 0x105ab8 [C8 (Z_to_bv 64 0x7fff8000)] ->
ro_cells bsegs m 0x197660 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
ro_cells bsegs m 0xfe040 [C8 (Z_to_bv 64 0xf1af8)] ->
stk bsegs m XS1_LO XS1_HI -> stk bsegs m XS2_LO XS2_HI -> stk bsegs m XS3_LO XS3_HI ->
stk bsegs m ODR_LO ODR_HI ->
mem_inv bsegs m ->
evt bsegs (unreg_loop_post sp gp tp F fc m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0x1975e8) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 2) (Z_to_bv 64 0x1ca77) (Z_to_bv 64 (0x1023f0 - 64 * K)) (Z_to_bv 64 (2^61)) (Z_to_bv 64 0x103330)
(Z_to_bv 64 0xfe040) (Z_to_bv 64 0x103370) (Z_to_bv 64 0x1032b8) (Z_to_bv 64 0x105ab8) (Z_to_bv 64 K)
t3 t4 t5 t6)
F (Z_to_bv 64 0x547f8) fc None m (seg_rom bsegs)).
Proof.
induction gs as [|g gs IH]; intros K ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sp F fc m
OK LEN HK GDS AI CP RG SHC THR RMS SC1 SC2 SC3 ODRS MI.
{ cbn in LEN. lia. }
inversion OK as [|g0 gs0 OKg OKgs]. subst g0 gs0.
destruct GDS as (REC & GDS).
destruct (gd_okb_spec g OKg) as (B0 & B8 & S8 & S8m & BT & ST8 & INS & ODR & Z1 & Z2 & Z3 & Z4 & Z5).
cbn [length] in LEN.
destruct g as [beg size srz name modn dyn loc odr]. cbn [gd_beg gd_size gd_srz gd_name gd_mod gd_dyn gd_loc gd_odr] in *.
unfold gd_cells in REC. cbn [gd_beg gd_size gd_srz gd_name gd_mod gd_dyn gd_loc gd_odr] in REC.
pose proof (munch_refl UNREG_W m) as MU0. pose proof (wmono_refl bsegs m) as WM0.
unfold SHB in INS.
call (unreg_iter_head (0x1023f0 - 64 * K) K beg srz); [exact REC| exact AI| exact CP| exact RG| exact SHC| exact THR| exact RMS
| exact SC1| exact SC2| exact SC3| exact INS| lia| lia| lia| lia| lia| lia| lia| lia| lia| exact MI|].
call (unreg_iter_tail (0x1023f0 - 64 * K) K odr); [exact REC| exact ODRS| exact ODR| lia| lia| lia| assumption|].
destruct (Z.eqb_spec K 1) as [EK|NK].
- assert (GS0 : gs = []) by (destruct gs; [reflexivity| cbn [length] in LEN; lia]). subst gs.
rewrite EK in *.
apply evt_done. unfold unreg_loop_post.
do 18 eexists. split; [reflexivity|].
split; [exact MU0|]. split; [exact WM0|]. split; [assumption|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. eassumption.
- replace (0x1023f0 - 64 * K + 64) with (0x1023f0 - 64 * (K - 1)) by lia.
lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
replace pc with 346104 by (destruct (Z.eqb_spec K 1); [contradiction| reflexivity]) end.
eapply evt_cut.
+ eapply (IH (K - 1)); try eassumption; try lia.
replace (0x1023f0 - 64 * (K - 1)) with (0x1023f0 - 64 * K + 64) by lia.
apply (gds_at_agree gs m _ _ GDS). apply (agree_of_munch _ _ _ _ MU0). intros xa Hxa. cbn [outside]. lia.
+ intros ms' PO. apply evt_done. unfold unreg_loop_post in PO |- *.
destruct PO as (ra' & s0' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
E & MU' & WM' & MI' & R).
exists ra', s0', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
split; [exact E|]. split; [| split; [| split; [exact MI'| exact R]]].
* eapply munch_trans; [exact MU0| exact MU'].
* eapply wmono_trans; [exact WM0| exact WM'].
Qed.

End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Notation UNREG_W :=
[(XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (ODR_LO, ODR_HI)] (only parsing).

Definition unreg_loop_post (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
fun ms' => exists (ra' s0' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' (Z_to_bv 64 0x18eda8) a0' a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 2) (Z_to_bv 64 0x1ca95) (Z_to_bv 64 0xf9bb0) (Z_to_bv 64 (2^61)) (Z_to_bv 64 0xfaaf0)
(Z_to_bv 64 0xf57c0) (Z_to_bv 64 0xfab30) (Z_to_bv 64 0xfaa78) (Z_to_bv 64 0xfd278) (Z_to_bv 64 0)
t3' t4' t5' t6')
F (Z_to_bv 64 0x54910) fc None m' (seg_rom asegs)
/\ munch UNREG_W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' XS1_LO XS1_HI /\ stk asegs m' XS2_LO XS2_HI /\ stk asegs m' XS3_LO XS3_HI
/\ stk asegs m' ODR_LO ODR_HI.

Lemma unreg_loop : forall (gs : list gdesc) (K : Z)
(ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (sp : word) F fc (m : mem),
Forall (fun g => gd_okb g = true) gs -> Z.of_nat (length gs) = K -> 1 <= K <= GDS_N ->
gds_at m (0xf9bb0 - 64 * K) gs ->
rw_cells asegs m 0xfdf58 [C1 (Z_to_bv 8 1)] ->
ro_cells asegs m 0xfcadc [C1 (Z_to_bv 8 1)] ->
ro_cells asegs m 0xfaa90 [C4 (Z_to_bv 64 1)] ->
ro_cells asegs m 0xfd278 [C8 (Z_to_bv 64 0x7fff8000)] ->
ro_cells asegs m 0x18ee20 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
ro_cells asegs m 0xf57c0 [C8 (Z_to_bv 64 0xe9284)] ->
stk asegs m XS1_LO XS1_HI -> stk asegs m XS2_LO XS2_HI -> stk asegs m XS3_LO XS3_HI ->
stk asegs m ODR_LO ODR_HI ->
mem_inv asegs m ->
evt asegs (unreg_loop_post sp gp tp F fc m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0x18eda8) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 2) (Z_to_bv 64 0x1ca95) (Z_to_bv 64 (0xf9bb0 - 64 * K)) (Z_to_bv 64 (2^61)) (Z_to_bv 64 0xfaaf0)
(Z_to_bv 64 0xf57c0) (Z_to_bv 64 0xfab30) (Z_to_bv 64 0xfaa78) (Z_to_bv 64 0xfd278) (Z_to_bv 64 K)
t3 t4 t5 t6)
F (Z_to_bv 64 0x5470c) fc None m (seg_rom asegs)).
Proof.
induction gs as [|g gs IH]; intros K ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sp F fc m
OK LEN HK GDS AI CP RG SHC THR RMS SC1 SC2 SC3 ODRS MI.
{ cbn in LEN. lia. }
inversion OK as [|g0 gs0 OKg OKgs]. subst g0 gs0.
destruct GDS as (REC & GDS).
destruct (gd_okb_spec g OKg) as (B0 & B8 & S8 & S8m & BT & ST8 & INS & ODR & Z1 & Z2 & Z3 & Z4 & Z5).
cbn [length] in LEN.
destruct g as [beg size srz name modn dyn loc odr]. cbn [gd_beg gd_size gd_srz gd_name gd_mod gd_dyn gd_loc gd_odr] in *.
unfold gd_cells in REC. cbn [gd_beg gd_size gd_srz gd_name gd_mod gd_dyn gd_loc gd_odr] in REC.
pose proof (munch_refl UNREG_W m) as MU0. pose proof (wmono_refl asegs m) as WM0.
unfold SHB in INS.
call (unreg_iter_head (0xf9bb0 - 64 * K) K beg srz); [exact REC| exact AI| exact CP| exact RG| exact SHC| exact THR| exact RMS
| exact SC1| exact SC2| exact SC3| exact INS| lia| lia| lia| lia| lia| lia| lia| lia| lia| exact MI|].
call (unreg_iter_tail (0xf9bb0 - 64 * K) K odr); [exact REC| exact ODRS| exact ODR| lia| lia| lia| assumption|].
destruct (Z.eqb_spec K 1) as [EK|NK].
- assert (GS0 : gs = []) by (destruct gs; [reflexivity| cbn [length] in LEN; lia]). subst gs.
rewrite EK in *.
apply evt_done. unfold unreg_loop_post.
do 18 eexists. split; [reflexivity|].
split; [exact MU0|]. split; [exact WM0|]. split; [assumption|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. eassumption.
- replace (0xf9bb0 - 64 * K + 64) with (0xf9bb0 - 64 * (K - 1)) by lia.
lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
replace pc with 345868 by (destruct (Z.eqb_spec K 1); [contradiction| reflexivity]) end.
eapply evt_cut.
+ eapply (IH (K - 1)); try eassumption; try lia.
replace (0xf9bb0 - 64 * (K - 1)) with (0xf9bb0 - 64 * K + 64) by lia.
apply (gds_at_agree gs m _ _ GDS). apply (agree_of_munch _ _ _ _ MU0). intros xa Hxa. cbn [outside]. lia.
+ intros ms' PO. apply evt_done. unfold unreg_loop_post in PO |- *.
destruct PO as (ra' & s0' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
E & MU' & WM' & MI' & R).
exists ra', s0', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
split; [exact E|]. split; [| split; [| split; [exact MI'| exact R]]].
* eapply munch_trans; [exact MU0| exact MU'].
* eapply wmono_trans; [exact WM0| exact WM'].
Qed.

