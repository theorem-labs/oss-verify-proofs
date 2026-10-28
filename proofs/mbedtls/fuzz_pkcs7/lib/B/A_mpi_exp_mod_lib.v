(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_rt_facts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_mpi_exp_mod_lib () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.shadow_of"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.ZArith.BinInt.Z.sub"; "SnapA.snapA"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.add"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.write_to_mem"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.w_client"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "snapA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"].


Section SnapA.
  Variable segs : list Segment.
  Variable AL : asan_layout.

  Definition snapA (m0 m : mem) (a0 a1 : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_lib ()) "Pc,$0.P,(1.(2.O2.R1.)(3.R1.O1.))P,(1.(2.=(4.VAL,R2.))(3.(4.VAL,R2.)(5.+2.+40.)))(1.(6.(7.(8.&8.))A1.O3.(9.(4.VAL,R3.))A1.O4.(9.(4.VAL,R3.)))P,(:.(6.(7.(8.&8.))(;.Vsegs,O4.(9.(4.VAL,R3.)))(<.(8.&8.))))(:.(6.(7.(8.&8.))(;.Vsegs,O3.(9.(4.VAL,R4.)))(<.(8.&8.)))))")
(* [comment removed for export] *).

  #[using="Type"] Lemma snapA_refl : forall m a0 a1, snapA m m a0 a1.
  Proof. intros m a0 a1 c _ _. split; [reflexivity| intros H; exact H]. Qed.

  #[using="Type"] Lemma snapA_sub : forall m0 m a0 a1 b0 b1, snapA m0 m a0 a1 -> a0 <= b0 -> b1 <= a1 -> snapA m0 m b0 b1.
  Proof. intros m0 m a0 a1 b0 b1 H H0 H1 c Hc Hr. apply H; [lia| exact Hr]. Qed.

  #[using="Type"] Lemma snapA_join : forall m0 m a0 a1 a2, snapA m0 m a0 a1 -> snapA m0 m a1 a2 -> snapA m0 m a0 a2.
  Proof. intros m0 m a0 a1 a2 H1 H2 c Hc Hr. destruct (Z_lt_le_dec c a1); [apply H1| apply H2]; first [lia | exact Hr]. Qed.

  
  (* [comment removed for export] *)
  #[using="Type"] Lemma snapA_store_client : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_lib ()) "PCS,P,$0.SpPm0,P,(8.&40.)(7.(8.&8.))Pm,P,(8.&40.)(7.(8.&8.))Pa0,$0.Pa1,$0.Pa,$0.Pbs,(=.(8.&8.))P,(>.VAL,R7.)P,(?.R8.R5.(10.R4.R5.))P,(11.R8.R7.R6.R5.)P,(?.R:.R5.(12.(13.(8.&8.)R4.)))P,(2.=R6.)P,(2.(14.R7.(12.(13.(8.&8.)R6.)))(5.+2.+40.))(11.R<.(15.R;.(9.R8.)R7.)R:.R9.)")
(* [comment removed for export] *).
  Proof.
    intros CS m0 m a0 a1 a bs OK HW H HC Ha Hl c Hc Hr. destruct (H c Hc Hr) as [E1 W1]. split.
    - rewrite <- E1. apply write_outside; [exact Ha| exact Hl| exact Hr|].
      destruct (Z_lt_le_dec (shadow_of AL c) a); [left; lia|]. destruct (Z_lt_le_dec (shadow_of AL c) (a + Z.of_nat (length bs))); [| right; lia].
      exfalso. destruct OK as (C1 & _). assert (CSc : CS c) by (replace c with (a0 + (c - a0)) by lia; apply HW; lia).
      apply (proj2 (proj2 (proj2 (C1 c CSc)))).
      replace (shadow_of AL c) with (a + (shadow_of AL c - a)) by lia. apply HC. lia.
    - intros Hw. apply wview_write_mono. apply W1, Hw.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma snapA_munch : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_lib ()) "PCS,P,$0.SpPW,(=.$16.)Pm0,P,(8.&40.)(7.(8.&8.))Pm,P,(8.&40.)(7.(8.&8.))Pm',P,(8.&40.)(7.(8.&8.))Pa0,$0.Pa1,$0.P,(>.VAL,R7.)P,(17.R8.R7.)P,(?.R9.R4.(10.R3.R4.))P,(18.R9.R7.R6.)P,(19.Vsegs,R8.R7.)P,(11.R:.R9.R7.R6.)(11.R;.R9.R8.R7.)")
(* [comment removed for export] *).
  Proof.
    intros CS W m0 m m' a0 a1 OK HW HR MU WM H c Hc Hr. destruct (H c Hc Hr) as [E1 W1].
    assert (CSc : CS c) by (replace c with (a0 + (c - a0)) by lia; apply HR; lia).
    destruct OK as (C1 & _). pose proof (proj2 (proj2 (proj2 (C1 c CSc)))) as NCS.
    pose proof (outside_of_not_cs CS W (shadow_of AL c) HW NCS) as OUT.
    split.
    - rewrite <- E1. apply MU. rewrite wa_unsigned by lia. exact OUT.
    - intros Hw. apply WM, W1, Hw.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma snapA_store_shadow : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_lib ()) "Pm0,P,(8.&40.)(7.(8.&8.))Pm,P,(8.&40.)(7.(8.&8.))Pa0,$0.Pa1,$0.Pc0,$0.Pa,$0.Pbs,(=.(8.&8.))P,(11.R7.R6.R5.R4.)P,(6.$0.R3.(4.VAL,R4.))P,(6.$0.(1:.R5.+8.)=)P,(1;.(2.(14.R6.(1<.+8.(12.(13.(8.&8.)R4.))))R8.)(2.R7.R6.))P,(2.=R6.)P,(2.(14.R7.(12.(13.(8.&8.)R6.)))(5.+2.+40.))(11.R=.(15.R<.(9.R8.)R7.)R;.R:.)")
(* [comment removed for export] *).
  Proof.
    intros m0 m a0 a1 c0 a bs H -> Hc0 HD Ha Hl c Hc Hr. destruct (H c Hc Hr) as [E1 W1]. split.
    - rewrite <- E1. apply write_outside; [exact Ha| exact Hl| exact Hr|].
      unfold shadow_of in *. clear - Hc Hc0 HD. Z.div_mod_to_equations. lia.
    - intros Hw. apply wview_write_mono. apply W1, Hw.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma snapA_of_sshad : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_lib ()) "Pm0,P,(8.&40.)(7.(8.&8.))Pm,P,(8.&40.)(7.(8.&8.))Pa0,$0.Pa1,$0.P,(1=.Vsegs,VAL,R4.R2.R1.)P,(1=.Vsegs,VAL,R4.R3.R2.)P,Pc,$0.P,(1.(2.R5.R1.)(3.R1.R4.))(:.(6.(7.(8.&8.))A1.R8.(9.(4.VAL,R2.))(<.(8.&8.))))P,Pc,$0.P,(1.(2.R6.R1.)(3.R1.R5.))(:.(6.(7.(8.&8.))A1.R8.(9.(4.VAL,R2.))(<.(8.&8.))))(11.R8.R7.R6.R5.)")
(* [comment removed for export] *).
  Proof.
    (intros m0 m a0 a1 dd_H; ddestruct dd_H as (A0 & A1 & S0); intros dd_H; ddestruct dd_H as (_ & _ & S1); intros M0 M1 c Hc Hr).
    set (g := c - c mod 8).
    assert (G : a0 <= g /\ g + 8 <= a1 /\ g mod 8 = 0 /\ shadow_of AL g = shadow_of AL c).
    { subst g. unfold shadow_of. clear - Hc A0 A1. Z.div_mod_to_equations. lia. }
    ddestruct G as (G0 & G1 & G2 & G3).
    ddestruct (S0 g G0 G1 G2) as [[Hwf0 (B00 & B01 & HB0)] _]. ddestruct (S1 g G0 G1 G2) as [[Hwf1 (B10 & B11 & HB1)] (W0 & W1 & HW)].
    rewrite G3 in *. specialize (HB0 0%nat ltac:(cbn; lia)). specialize (HB1 0%nat ltac:(cbn; lia)). rewrite Z.add_0_r in HB0, HB1. unfold mrd in HB0, HB1.
    specialize (M0 c Hc). specialize (M1 c Hc).
    destruct (m0 (wa (shadow_of AL c))) as [b0|]; [| exfalso; apply M0; reflexivity].
    destruct (m (wa (shadow_of AL c))) as [b1|]; [| exfalso; apply M1; reflexivity].
    split; [congruence|]. intros _. specialize (HW 0 ltac:(cbn; lia)). rewrite Z.add_0_r in HW. exact HW.
  Qed.
End SnapA.

Section SnapR.
  Variable segs : list Segment.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Local Notation AL := (arl_AL R).

  (* [comment removed for export] *)
  #[using="Type"] Lemma snapA_presA : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_lib ()) "PLB,(=.$1>.)PLF,(=.$1>.)PSP,$0.PSSP,$0.PTOP,$0.PW,(=.$16.)Pm0,P,(8.&40.)(7.(8.&8.))Pm,P,(8.&40.)(7.(8.&8.))Pm',P,(8.&40.)(7.(8.&8.))Pa0,$0.Pa1,$0.P,(1?.Vsegs,(20.VR,)R5.R4.R2.R1.)P,(21.Vsegs,VR,R<.R;.R:.R9.R8.R7.R5.R4.)P,(2.R:.R4.)P,(2.R4.R:.)(1?.Vsegs,(20.VR,)R9.R7.R6.R5.)")
(* [comment removed for export] *).
  Proof.
    intros LB LF SP SSP TOP W m0 m m' a0 a1 H [_ S] H0 H1 c Hc Hr. destruct (H c Hc Hr) as [E1 W1].
    destruct (S c ltac:(left; lia) Hr) as [E2 W2]. split; [congruence| intros Hw; apply W2, W1, Hw].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma presA_lower_ssp : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_lib ()) "PLB,(=.$1>.)PLF,(=.$1>.)PSP,$0.PSSP0,$0.PSSP1,$0.PTOP,$0.PW,(=.$16.)Pm,P,(8.&40.)(7.(8.&8.))Pm',P,(8.&40.)(7.(8.&8.))P,(21.Vsegs,VR,R9.R8.R7.R5.R4.R3.R2.R1.)P,(1?.Vsegs,(20.VR,)R3.R2.R7.R6.)(21.Vsegs,VR,R;.R:.R9.R8.R6.R5.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros LB LF SP SSP0 SSP1 TOP W m m' [P S] H. split; [exact P|].
    intros c Hc Hr. destruct (Z_lt_le_dec c SSP1) as [Hlt|Hge].
    - destruct Hc as [Hs|Hc]; [apply H; [lia| exact Hr]| apply S; [right; exact Hc| exact Hr]].
    - apply S; [| exact Hr]. destruct Hc as [Hs|Hc]; [left; lia| right; exact Hc].
  Qed.
End SnapR.

(* [comment removed for export] *)
Ltac transport_chunks segs m a bs ::=
  let Ha := fresh "Ha_st" in let Hl := fresh "Hl_st" in let CR := fresh "CRst" in
  try store_bounds Ha Hl CR a bs;
  (tryif store_is_shadow a then note_chunk_cranges segs m else idtac);
  repeat match goal with
  | H : snapA segs ?L0 ?m0 m ?a0 ?a1, OK : cs_ok ?L0 ?CS |- _ =>
      first [ tryif store_is_shadow a
              then (let c := shadow_client_of a in
                    apply (snapA_store_shadow segs L0 m0 m a0 a1 c a bs) in H;
                    [ | shadow_addr_eq | qlia | simpl_sizes; qlia | sf_a0 | sf_al ])
              else (apply (snapA_store_client segs L0 CS m0 m a0 a1 a bs OK) in H; [ | solve_crange | simpl_sizes; solve_crange | sf_a0 | sf_al ])
            | idtac "note: could not carry snapA across the store (dropping):" H; clear H ]
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_write_other0 segs m a bs A2 bs2) in H;
              [ | sf_a0 | sf_al | simpl_sizes; simpl_arr_sizes; solve_apart0 ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; solve_apart ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; solve_apart ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_frame segs m A2 xs a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; simpl_arr_sizes; solve_apart ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_frame segs m A2 xs a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; simpl_arr_sizes; solve_apart ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_frame segs m A2 xs a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; simpl_arr_sizes; solve_apart ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_frame segs m A2 xs a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; simpl_arr_sizes; solve_apart ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : HEAP _ _ ?HI ?h ?LB m ?mo |- _ =>
      first [ eapply (heap_write segs _ HI h LB m mo _ a bs) in H;
              [ | eassumption | simpl_sizes; solve_client_wrange | qlia | simpl_sizes; qlia ]
            | idtac "note: could not carry HEAP across the store (dropping):" H; clear H ]
  | H : pristine ?lo ?hi ?E m |- _ =>
      first [ apply (pristine_write lo hi E m a bs) in H;
              [ | lia | simpl_sizes; lia | intros; simpl_sizes; lia ]
            | idtac "note: could not carry pristine across the store (dropping):" H; clear H ]
  | H : statics_ok segs ?L m |- _ =>
      first [ apply (statics_ok_write segs L m a bs) in H;
              [ | qlia | simpl_sizes; qlia | simpl_sizes; pqlia ]
            | idtac "note: could not carry statics_ok across the store (dropping):" H; clear H ]
  (* [comment removed for export] *)
  | H : HM segs ?R ?HIA ?h ?LB ?LF m |- _ =>
      first [ tryif store_is_shadow a
              then (let c := shadow_client_of a in
                    apply (hm_write_shadow segs R HIA h LB LF m c a bs) in H;
                    [ | simpl_sizes; solve_hm_shadow_range | shadow_addr_eq | sf_a0 | sf_al ])
              else (apply (hm_write segs R HIA h LB LF m a bs) in H; [ | simpl_sizes; solve_client_wrange | sf_a0 | sf_al ])
            | idtac "note: could not carry HM across the store (dropping):" H; clear H ]
  | H : presW segs ?R ?HIA ?h ?LB ?LF ?SP ?SSP ?W ?m0 m |- _ =>
      first [ tryif store_is_shadow a
              then (let c := shadow_client_of a in
                    first [ match goal with SF : shadow_free _ LB LF SSP _ ?C ?n |- _ =>
                              apply (presW_store_shadow_cov segs R HIA h LB LF SP SSP W m0 m c a bs C n) in H;
                              [ | qlia | shadow_addr_eq | qlia | simpl_sizes; solve_crange | exact SF | qlia | simpl_sizes; qlia ] end
                          | apply (presW_store_shadow_stack segs R HIA h LB LF SP SSP W m0 m c a bs) in H;
                            [ | qlia | shadow_addr_eq | qlia | simpl_sizes; solve_crange | qlia | simpl_sizes; qlia ]
                          | match goal with FR : fresh_apart _ LB LF ?N ?k, AP : forall B j, In (B, j) LF -> _ |- _ =>
                              apply (presW_store_shadow_fresh segs R HIA h LB LF SP SSP W m0 m c a bs N k) in H;
                              [ | qlia | shadow_addr_eq | qlia | simpl_sizes; solve_crange | exact FR | exact AP | qlia | simpl_sizes; qlia | qlia ] end ])
              else first [ match goal with WC : wcover _ LB LF SP W ?A ?n |- _ =>
                             apply (presW_store_cov segs R HIA h LB LF SP SSP W m0 m a bs A n) in H;
                             [ | simpl_sizes; solve_crange | sf_a0 | sf_al | exact WC | qlia | simpl_sizes; qlia ] end
                         | apply (presW_store_out segs R HIA h LB LF SP SSP W m0 m a bs) in H;
                           [ | simpl_sizes; solve_crange | sf_a0 | sf_al | cbn [inside]; simpl_sizes; qlia ]
                         | apply (presW_store_stack segs R HIA h LB LF SP SSP W m0 m a bs) in H;
                           [ | simpl_sizes; solve_crange | sf_a0 | sf_al | qlia | simpl_sizes; qlia ]
                         | match goal with FR : fresh_apart _ LB LF ?N ?k |- _ =>
                             apply (presW_store_fresh segs R HIA h LB LF SP SSP W m0 m a bs N k) in H;
                             [ | simpl_sizes; solve_crange | sf_a0 | sf_al | exact FR | qlia | simpl_sizes; qlia | qlia ] end ]
            | idtac "note: could not carry presW across the store (dropping):" H; clear H ]
  | H : abase segs ?L m, OK : cs_ok ?L ?CS |- _ =>
      first [ tryif store_is_shadow a
              then (let c := shadow_client_of a in
                    apply (abase_shadow_store_at segs L CS m c a bs OK) in H;
                    [ | simpl_sizes; solve_crange | simpl_sizes; clear; lia | shadow_addr_eq ])
              else (apply (abase_frame segs L CS OK m a bs) in H; [ | simpl_sizes; solve_crange | simpl_sizes; clear; lia | sf_a0 | sf_al ])
            | idtac "note: could not carry abase across the store (dropping):" H; clear H ]
  | H : aobj segs ?L ?CS m ?A ?n, OK : cs_ok ?L ?CS |- _ =>
      first [ tryif store_is_shadow a
              then (let c := shadow_client_of a in
                    apply (aobj_shadow_store_at segs L CS m A n c a bs OK) in H;
                    [ | simpl_sizes; solve_crange | qlia | simpl_sizes; clear; lia | simpl_sizes; pqlia | shadow_addr_eq ])
              else (apply (aobj_frame segs L CS OK m A n a bs) in H; [ | simpl_sizes; solve_crange | sf_a0 | sf_al ])
            | idtac "note: could not carry aobj across the store (dropping):" H; clear H ]
  | H : sshad segs ?L m ?lo ?hi, OK : cs_ok ?L ?CS |- _ =>
      first [ tryif store_is_shadow a
              then (let c := shadow_client_of a in
                    apply (sshad_shadow_store_at segs L CS m lo hi c a bs OK) in H;
                    [ | solve_crange | simpl_sizes; solve_crange | qlia | simpl_sizes; clear; lia | simpl_sizes; pqlia | shadow_addr_eq ])
              else (apply (sshad_frame segs L CS m lo hi a bs OK) in H; [ | solve_crange | simpl_sizes; solve_crange | sf_a0 | sf_al ])
            | idtac "note: could not carry sshad across the store (dropping):" H; clear H ]
  end;
  footprint_work segs m a bs;
  try clear Ha; try clear Hl; try clear CR.
