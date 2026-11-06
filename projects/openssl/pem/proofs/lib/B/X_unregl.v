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
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.pem.lib.B Require Import Layout R_small D_kit X_gdefs X_unregi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Notation UNREG_W := [(SHW_LO, SHW_HI); (ODR_LO, ODR_HI)] (only parsing).

Definition unreg_loop_post (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (ra' s0' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' (Z_to_bv 64 0x730e68) a0' a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 2) (Z_to_bv 64 0x359d6) (Z_to_bv 64 0x69bc60) (Z_to_bv 64 (2^61)) (Z_to_bv 64 0x69cbb0)
                  (Z_to_bv 64 0x5dfa70) (Z_to_bv 64 0x69cbf0) (Z_to_bv 64 0x69cb38) (Z_to_bv 64 0x69f338) (Z_to_bv 64 0)
                  t3' t4' t5' t6')
             F (Z_to_bv 64 0x1a5250) fc None m' (seg_rom bsegs)
    /\ munch UNREG_W m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' SHW_LO SHW_HI /\ stk bsegs m' ODR_LO ODR_HI.

(* [comment removed for export] *)
Lemma unreg_loop : forall (n : nat) (K : Z)
    (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (sp : word) F fc (m : mem),
  Z.of_nat n = K -> 1 <= K <= GT_N ->
  gtab_at m ->
  rw_cells bsegs m 0x6a0018 [C1 (Z_to_bv 8 1)] ->
  ro_cells bsegs m 0x69eb9c [C1 (Z_to_bv 8 1)] ->
  ro_cells bsegs m 0x69cb50 [C4 (Z_to_bv 64 1)] ->
  ro_cells bsegs m 0x69f338 [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells bsegs m 0x730ee0 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
  ro_cells bsegs m 0x5dfa70 [C8 (Z_to_bv 64 0x55f010)] ->
  stk bsegs m SHW_LO SHW_HI -> stk bsegs m ODR_LO ODR_HI ->
  mem_inv bsegs m ->
  evt bsegs (unreg_loop_post sp gp tp F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0x730e68) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 2) (Z_to_bv 64 0x359d6) (Z_to_bv 64 (0x69bc60 - 64 * K)) (Z_to_bv 64 (2^61)) (Z_to_bv 64 0x69cbb0)
             (Z_to_bv 64 0x5dfa70) (Z_to_bv 64 0x69cbf0) (Z_to_bv 64 0x69cb38) (Z_to_bv 64 0x69f338) (Z_to_bv 64 K)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x1a504c) fc None m (seg_rom bsegs)).
Proof.
  induction n as [|n IH]; intros K ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sp F fc m
    LEN HK GT AI CP RG SHC THR RMS SCW OW MI.
  { cbn in LEN. lia. }
  rewrite Nat2Z.inj_succ in LEN.
  destruct (GT (GT_N - K) ltac:(lia)) as (beg & srz & odr & (REC0 & REC2 & REC7) & OKg).
  destruct (gd_okb_spec beg srz odr OKg) as (B0 & B8 & S8 & S8m & BT & ST8 & INS & ODR).
  assert (EA : GT_LO + 64 * (GT_N - K) = 0x69bc60 - 64 * K) by (unfold GT_LO, GT_N; lia).
  rewrite EA in REC0, REC2, REC7.
  pose proof (munch_refl UNREG_W m) as MU0. pose proof (wmono_refl bsegs m) as WM0.
  assert (HK' : 1 <= K <= 11827) by exact HK.
  unfold XSEGLO, XSEGTOP in *.
  call (unreg_iter_head (0x69bc60 - 64 * K) K beg srz); [exact REC0| exact REC2| exact AI| exact CP| exact RG| exact SHC| exact THR| exact RMS
        | exact SCW| exact INS| lia| lia| lia| lia| lia| lia| lia| lia| exact HK| exact MI|].
  call (unreg_iter_tail (0x69bc60 - 64 * K) K odr); [exact REC7| exact OW| exact ODR| lia| lia| exact HK| assumption|].
  destruct (Z.eqb_spec K 1) as [EK|NK].
  - rewrite EK in *.
    apply evt_done. unfold unreg_loop_post.
    do 18 eexists. split; [reflexivity|].
    split; [exact MU0|]. split; [exact WM0|]. split; [assumption|]. split; eassumption.
  - replace (0x69bc60 - 64 * K + 64) with (0x69bc60 - 64 * (K - 1)) by lia.
    lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      replace pc with 1724492 by (destruct (Z.eqb_spec K 1); [contradiction| reflexivity]) end.
    eapply evt_cut.
    + eapply (IH (K - 1)); try eassumption; try lia.
      apply (gtab_at_munch _ m _ GT MU0). intros xa Hxa. unfold GT_LO, GT_HI in *. cbn [outside]. lia.
    + intros ms' PO. apply evt_done. unfold unreg_loop_post in PO |- *.
      destruct PO as (ra' & s0' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                      E & MU' & WM' & MI' & R).
      exists ra', s0', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
      split; [exact E|]. split; [| split; [| split; [exact MI'| exact R]]].
      * eapply munch_trans; [exact MU0| exact MU'].
      * eapply wmono_trans; [exact WM0| exact WM'].
Qed.
