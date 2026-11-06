(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Import Layout Shadow R_small D_kit X_xdefs X_unregi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation UNREG_W :=
  [(XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (0x6adf80%Z, 0x6adf81%Z); (0x6adf81%Z, 0x6adf8b%Z)] (only parsing).

Definition unreg_loop_post (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (ra' s0' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (o1' o2' o3' o4' o5' o6' o7' o8' o9' o10' o11' : byte),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' (Z_to_bv 64 0x20d1e8) a0' a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 2) (Z_to_bv 64 0x1ce34) (Z_to_bv 64 0x178000) (Z_to_bv 64 (2^61)) (Z_to_bv 64 0x178f30)
                  (Z_to_bv 64 0x1741a8) (Z_to_bv 64 0x178f70) (Z_to_bv 64 0x178eb8) (Z_to_bv 64 0x17b6b8) (Z_to_bv 64 0)
                  t3' t4' t5' t6')
             F (Z_to_bv 64 0x6d974) fc None m' (seg_rom asegs)
    /\ munch UNREG_W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' XS1_LO XS1_HI /\ stk asegs m' XS2_LO XS2_HI /\ stk asegs m' XS3_LO XS3_HI
    /\ rw_cells asegs m' 0x6adf80 [C1 o1'] /\ rw_cells asegs m' 0x6adf81 [C1 o2'] /\ rw_cells asegs m' 0x6adf82 [C1 o3'] /\ rw_cells asegs m' 0x6adf83 [C1 o4'] /\ rw_cells asegs m' 0x6adf84 [C1 o5'] /\ rw_cells asegs m' 0x6adf85 [C1 o6'] /\ rw_cells asegs m' 0x6adf86 [C1 o7'] /\ rw_cells asegs m' 0x6adf87 [C1 o8'] /\ rw_cells asegs m' 0x6adf88 [C1 o9'] /\ rw_cells asegs m' 0x6adf89 [C1 o10'] /\ rw_cells asegs m' 0x6adf8a [C1 o11'].

Lemma unreg_loop : forall (gs : list gdesc) (K : Z)
    (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (sp : word) F fc (m : mem) (o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 : byte),
  Forall (fun g => gd_okb g = true) gs -> Z.of_nat (length gs) = K -> 1 <= K <= 78 ->
  gds_at m (0x178000 - 64 * K) gs ->
  rw_cells asegs m 0x17c398 [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0x17af1c [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0x178ed0 [C4 (Z_to_bv 64 1)] ->
  ro_cells asegs m 0x17b6b8 [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells asegs m 0x20d260 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
  ro_cells asegs m 0x1741a8 [C8 (Z_to_bv 64 0x1644d4)] ->
  stk asegs m XS1_LO XS1_HI -> stk asegs m XS2_LO XS2_HI -> stk asegs m XS3_LO XS3_HI ->
  rw_cells asegs m 0x6adf80 [C1 o1] -> rw_cells asegs m 0x6adf81 [C1 o2] -> rw_cells asegs m 0x6adf82 [C1 o3] -> rw_cells asegs m 0x6adf83 [C1 o4] -> rw_cells asegs m 0x6adf84 [C1 o5] -> rw_cells asegs m 0x6adf85 [C1 o6] -> rw_cells asegs m 0x6adf86 [C1 o7] -> rw_cells asegs m 0x6adf87 [C1 o8] -> rw_cells asegs m 0x6adf88 [C1 o9] -> rw_cells asegs m 0x6adf89 [C1 o10] -> rw_cells asegs m 0x6adf8a [C1 o11] ->
  mem_inv asegs m ->
  evt asegs (unreg_loop_post sp gp tp F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0x20d1e8) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 2) (Z_to_bv 64 0x1ce34) (Z_to_bv 64 (0x178000 - 64 * K)) (Z_to_bv 64 (2^61)) (Z_to_bv 64 0x178f30)
             (Z_to_bv 64 0x1741a8) (Z_to_bv 64 0x178f70) (Z_to_bv 64 0x178eb8) (Z_to_bv 64 0x17b6b8) (Z_to_bv 64 K)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x6d770) fc None m (seg_rom asegs)).
Proof.
  induction gs as [|g gs IH]; intros K ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sp F fc m o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11
    OK LEN HK GDS AI CP RG SHC THR RMS SC1 SC2 SC3 O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 O11 MI.
  { cbn in LEN. lia. }
  inversion OK as [|g0 gs0 OKg OKgs]. subst g0 gs0.
  destruct GDS as (REC & GDS).
  destruct (gd_okb_spec g OKg) as (B0 & B8 & S8 & S8m & BT & ST8 & INS & ODR & Z1 & Z2 & Z3 & Z4 & Z5).
  cbn [length] in LEN.
  destruct g as [beg size srz name modn dyn loc odr]. cbn [gd_beg gd_size gd_srz gd_name gd_mod gd_dyn gd_loc gd_odr] in *.
  unfold gd_cells in REC. cbn [gd_beg gd_size gd_srz gd_name gd_mod gd_dyn gd_loc gd_odr] in REC.
  pose proof (munch_refl UNREG_W m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  unfold SHB in INS.
  call (unreg_iter_head (0x178000 - 64 * K) K beg srz); [exact REC| exact AI| exact CP| exact RG| exact SHC| exact THR| exact RMS
        | exact SC1| exact SC2| exact SC3| exact INS| lia| lia| lia| lia| lia| lia| lia| lia| lia| exact MI|].
  call (unreg_iter_tail (0x178000 - 64 * K) K odr); [exact REC| exact O1| exact O2| exact O3| exact O4| exact O5| exact O6| exact O7| exact O8| exact O9| exact O10| exact O11| exact ODR| lia| lia| lia| assumption|].
  destruct (Z.eqb_spec K 1) as [EK|NK].
  - assert (GS0 : gs = []) by (destruct gs; [reflexivity| cbn [length] in LEN; lia]). subst gs.
    rewrite EK in *.
    apply evt_done. unfold unreg_loop_post.
    do 18 eexists. do 11 eexists. split; [reflexivity|].
    split; [exact MU0|]. split; [exact WM0|]. split; [assumption|].
    repeat (split; [eassumption|]). eassumption.
  - replace (0x178000 - 64 * K + 64) with (0x178000 - 64 * (K - 1)) by lia.
    lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      replace pc with 448368 by (destruct (Z.eqb_spec K 1); [contradiction| reflexivity]) end.
    eapply evt_cut.
    + eapply (IH (K - 1)); try eassumption; try lia.
      replace (0x178000 - 64 * (K - 1)) with (0x178000 - 64 * K + 64) by lia.
      apply (gds_at_agree gs m _ _ GDS). apply (agree_of_munch _ _ _ _ MU0). intros xa Hxa. cbn [outside]. lia.
    + intros ms' PO. apply evt_done. unfold unreg_loop_post in PO |- *.
      destruct PO as (ra' & s0' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                      o1' & o2' & o3' & o4' & o5' & o6' & o7' & o8' & o9' & o10' & o11' & E & MU' & WM' & MI' & R).
      exists ra', s0', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', o1', o2', o3', o4', o5', o6', o7', o8', o9', o10', o11'.
      split; [exact E|]. split; [| split; [| split; [exact MI'| exact R]]].
      * eapply munch_trans; [exact MU0| exact MU'].
      * eapply wmono_trans; [exact WM0| exact WM'].
Qed.
