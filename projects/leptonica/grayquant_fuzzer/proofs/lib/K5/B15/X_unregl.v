(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import SysStep.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import R_small D_kit X_xdefs X_unregi.
Import ListNotations.
Open Scope Z_scope.

Notation UNREG_W :=
  [(XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (0x629cc2%Z, 0x629cc3%Z); (0x629cc0%Z, 0x629cc2%Z)] (only parsing).

Definition unreg_loop_post (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (ra' s0' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (o1' o2' o3' : byte),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' (Z_to_bv 64 0x189168) a0' a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 2) (Z_to_bv 64 0x1cc99) (Z_to_bv 64 0xf3f80) (Z_to_bv 64 (2^61)) (Z_to_bv 64 0xf4eb0)
                  (Z_to_bv 64 0xed8c0) (Z_to_bv 64 0xf4ef0) (Z_to_bv 64 0xf4e38) (Z_to_bv 64 0xf7638) (Z_to_bv 64 0)
                  t3' t4' t5' t6')
             F (Z_to_bv 64 0x4ece8) (RT_iface.frm_clear fc) None m' (seg_rom asegs)
    /\ munch UNREG_W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' XS1_LO XS1_HI /\ stk asegs m' XS2_LO XS2_HI /\ stk asegs m' XS3_LO XS3_HI
    /\ rw_cells asegs m' 0x629cc2 [C1 o1'] /\ rw_cells asegs m' 0x629cc0 [C1 o2'] /\ rw_cells asegs m' 0x629cc1 [C1 o3'].

Lemma unreg_loop : forall (gs : list gdesc) (K : Z)
    (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (sp : word) F fc (m : mem) (o1 o2 o3 : byte),
  Forall (fun g => gd_okb g = true) gs -> Z.of_nat (length gs) = K -> 1 <= K <= 239 ->
  gds_at m (0xf3f80 - 64 * K) gs ->
  rw_cells asegs m 0xf8318 [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0xf6e9c [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0xf4e50 [C4 (Z_to_bv 64 1)] ->
  ro_cells asegs m 0xf7638 [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells asegs m 0x1891e0 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
  ro_cells asegs m 0xed8c0 [C8 (Z_to_bv 64 0xe211c)] ->
  stk asegs m XS1_LO XS1_HI -> stk asegs m XS2_LO XS2_HI -> stk asegs m XS3_LO XS3_HI ->
  rw_cells asegs m 0x629cc2 [C1 o1] -> rw_cells asegs m 0x629cc0 [C1 o2] -> rw_cells asegs m 0x629cc1 [C1 o3] ->
  mem_inv asegs m ->
  evt asegs (unreg_loop_post sp gp tp F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0x189168) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 2) (Z_to_bv 64 0x1cc99) (Z_to_bv 64 (0xf3f80 - 64 * K)) (Z_to_bv 64 (2^61)) (Z_to_bv 64 0xf4eb0)
             (Z_to_bv 64 0xed8c0) (Z_to_bv 64 0xf4ef0) (Z_to_bv 64 0xf4e38) (Z_to_bv 64 0xf7638) (Z_to_bv 64 K)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x4eae4) (RT_iface.frm_clear fc) None m (seg_rom asegs)).
Proof.
  induction gs as [|g gs IH]; intros K ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sp F fc m o1 o2 o3
    OK LEN HK GDS AI CP RG SHC THR RMS SC1 SC2 SC3 O1 O2 O3 MI.
  { cbn in LEN. lia. }
  inversion OK as [|g0 gs0 OKg OKgs]. subst g0 gs0.
  destruct GDS as (REC & GDS).
  destruct (gd_okb_spec g OKg) as (B0 & B8 & S8 & S8m & BT & ST8 & INS & ODR & Z1 & Z2 & Z3 & Z4 & Z5).
  cbn [length] in LEN.
  destruct g as [beg size srz name modn dyn loc odr]. cbn [gd_beg gd_size gd_srz gd_name gd_mod gd_dyn gd_loc gd_odr] in *.
  unfold gd_cells in REC. cbn [gd_beg gd_size gd_srz gd_name gd_mod gd_dyn gd_loc gd_odr] in REC.
  pose proof (munch_refl UNREG_W m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  unfold SHB in INS.
  call (unreg_iter_head (0xf3f80 - 64 * K) K beg srz); [exact REC| exact AI| exact CP| exact RG| exact SHC| exact THR| exact RMS
        | exact SC1| exact SC2| exact SC3| exact INS| lia| lia| lia| lia| lia| lia| lia| lia| lia| exact MI|].
  call (unreg_iter_tail (0xf3f80 - 64 * K) K odr); [exact REC| exact O1| exact O2| exact O3| exact ODR| lia| lia| lia| assumption|].
  destruct (Z.eqb_spec K 1) as [EK|NK].
  - assert (GS0 : gs = []) by (destruct gs; [reflexivity| cbn [length] in LEN; lia]). subst gs.
    rewrite EK in *.
    apply evt_done. unfold unreg_loop_post.
    do 18 eexists. do 3 eexists. split; [reflexivity|].
    split; [exact MU0|]. split; [exact WM0|]. split; [assumption|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. split; eassumption.
  - replace (0xf3f80 - 64 * K + 64) with (0xf3f80 - 64 * (K - 1)) by lia.
    lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      replace pc with 322276 by (destruct (Z.eqb_spec K 1); [contradiction| reflexivity]) end.
    eapply evt_cut.
    + eapply (IH (K - 1)); try eassumption; try lia.
      replace (0xf3f80 - 64 * (K - 1)) with (0xf3f80 - 64 * K + 64) by lia.
      apply (gds_at_agree gs m _ _ GDS). apply (agree_of_munch _ _ _ _ MU0). intros xa Hxa. cbn [outside]. lia.
    + intros ms' PO. apply evt_done. unfold unreg_loop_post in PO |- *.
      destruct PO as (ra' & s0' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                      o1' & o2' & o3' & E & MU' & WM' & MI' & R).
      exists ra', s0', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', o1', o2', o3'.
      split; [exact E|]. split; [| split; [| split; [exact MI'| exact R]]].
      * eapply munch_trans; [exact MU0| exact MU'].
      * eapply wmono_trans; [exact WM0| exact WM'].
Qed.
