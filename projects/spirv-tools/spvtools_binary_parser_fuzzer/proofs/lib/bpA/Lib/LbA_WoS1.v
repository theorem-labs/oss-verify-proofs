(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HTac HArr HSysStep HExec CellsX TacX HMem HMState HLFrame.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPrelim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsStack0 AsWalk RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_PrsStmt LbA_SR LbA_Conv LbA_WoGen LbA_WoDefs LbA_WoKit LbA_WoSt LbA_WoMs LbA_WoCall LbA_WoCut LbA_WoZ.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_WoR2 LbA_WoR3 LbA_WoR4 LbA_WoR5 LbA_WoE0 LbA_WoE0b LbA_WoP LbA_WoQ.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WoS1.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHb : asan_rt_hyps_bp H.
  Let HB := rt_bp_base H HHb.

  Lemma wpre_budget : forall e, wpre H e ->
       0 <= w_n e < 2 ^ 24
    /\ lb_small (w_LB e) + po_small (w_n e) <= RT_SMALL_MAX /\ Z.of_nat (length (w_LB e)) + po_cnt (w_n e) <= RT_CNT_MAX
    /\ nlarge (w_LB e) + po_large (w_n e) <= RT_LARGE_MAX /\ po_cost (w_n e) <= as_AL H (w_s e).
  Proof.
    intros e HP. unfold wpre in HP.
    destruct HP as (_ & _ & HN & _ & _ & BS & BC & BL & HP). split; [exact HN|]. split; [exact BS|]. split; [exact BC|].
    split; [exact BL|]. repeat (let X := fresh in destruct HP as [X HP]). exact HP.
  Qed.

  Lemma po_budget_facts : forall n, 0 <= n -> 2 ^ 20 <= po_small n /\ 64 <= po_cnt n /\ 0 <= po_large n /\ 2 ^ 30 <= po_cost n.
  Proof. intros n Hn. unfold po_small, po_cnt, po_large, po_cost. Z.div_mod_to_equations. lia. Qed.

  Ltac mpres_chain :=
    repeat match goal with
    | |- as_MPRES H ?a ?a => apply (ah_mpres_refl H HB)
    | K : as_MPRES H ?a ?b |- as_MPRES H ?a ?c => apply (ah_mpres_trans H HB a b c K)
    end.

  Lemma seg_on1 : forall (Q : config -> Prop) (e : went H) msF mo,
    wpre H e -> as_AKREL H (w_s e) (mkCfg msF mo) -> as_MPRES H (w_mo e) mo -> e0_post H e (as_VIS H (w_s e) msF) ->
    (forall ff fp msF' mo' s1 (p1 : bptr) b1, as_AKREL H s1 (mkCfg msF' mo') -> as_MPRES H (w_mo e) mo' ->
       as_AL H s1 >= as_AL H (w_s e) -> ~ In p1 (map blk_id (w_LB e)) ->
       wp1_post H e ff fp s1 ((p1, b1, 500) :: w_LB e) b1 (as_VIS H s1 msF') -> as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q e msF mo HP KR MP P0 K.
    destruct P0 as (ff & fp & x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m0 & VIS & HI & WC & C48 & PZ & PM & PV).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof (wpre_budget e HP) as (HN & BS & BC & BL & AL0).
    pose proof (po_budget_facts (w_n e) ltac:(lia)) as (PB1 & PB2 & PB3 & PB4).
    pose proof (nsmall_bounds 0 ltac:(lia)) as _.
    destruct (z72_split m0 (ff + 344) PV) as (V1 & V2 & V3).
    replace (ff + 344 + 24) with (ff + 368) in V2 by lia. replace (ff + 344 + 48) with (ff + 392) in V3 by lia.
    eapply (won H HB e ff fp [] (w_s e) (w_LB e) m0 msF mo Q); [exact HHb | exact HP | exact HI | intros b Hb; exact Hb | exact VIS | exact KR
      | lia | lia | change (nsmall 500) with 500; lia | lia | lia |].
    intros msF' mo' s' A p m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' junk VIS' KR' MP' HI' AP ABR NI CB AD AL'.
    rewrite (ret_pc_even WO_ON1_RA ltac:(unfold WO_ON1_RA; lia) eq_refl) in VIS'.
    eapply (ahh_evt_then H HB (wp1_post H e ff fp s' ((p, A, 500) :: w_LB e) A) Q s' msF' _ mo'); [exact KR' | exact VIS' | |].
    - refine (wp1 H HHb e ff fp s' _ p A m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HP HI' (or_introl eq_refl) _ _ _ _ AD (proj2 CB)).
      + intros bb Hb. split; [right; exact Hb|]. intros E. apply NI. rewrite <- E. apply in_map. exact Hb.
      + exact (wfc_apres H e ff fp [] (w_s e) (w_LB e) (w_LB e) m0 m' HP HI WC AP).
      + eapply (apres_rw_cells H); [exact AP | exact C48 | left; lia].
      + eapply (wpst_apres H e ff fp [] (w_s e) (w_LB e) (w_LB e) m0 m'); [exact HP | exact HI | | exact AP | reflexivity | reflexivity | reflexivity].
        split; [exact PZ|]. split; [exact PM|]. split; [exact V1|]. split; [exact V2 | exact V3].
    - intros msF2 mo2 KR2 MP2 P2. eapply K; [exact KR2 | | lia | exact NI | exact P2]. mpres_chain.
  Qed.

  Lemma seg_on2 : forall (Q : config -> Prop) (e : went H) ff fp msF mo s1 (p1 : bptr) b1,
    wpre H e -> as_AKREL H s1 (mkCfg msF mo) -> as_MPRES H (w_mo e) mo -> as_AL H s1 >= as_AL H (w_s e) ->
    ~ In p1 (map blk_id (w_LB e)) ->
    wp1_post H e ff fp s1 ((p1, b1, 500) :: w_LB e) b1 (as_VIS H s1 msF) ->
    (forall msF' mo' s2 (p2 : bptr) b2, as_AKREL H s2 (mkCfg msF' mo') -> as_MPRES H (w_mo e) mo' ->
       as_AL H s2 >= as_AL H (w_s e) -> ~ In p2 (map blk_id ((p1, b1, 500) :: w_LB e)) ->
       wp2_post H e ff fp s2 ((p2, b2, 100) :: (p1, b1, 500) :: w_LB e) b1 b2 (as_VIS H s2 msF') -> as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q e ff fp msF mo s1 p1 b1 HP KR MP AL1 NI1 P1 K.
    destruct P1 as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m0 & VIS & HI & WC & C48 & PST & WB).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof (wpre_budget e HP) as (HN & BS & BC & BL & AL0).
    pose proof (po_budget_facts (w_n e) ltac:(lia)) as (PB1 & PB2 & PB3 & PB4).
    set (LB1 := (p1, b1, 500) :: w_LB e) in *.
    eapply (won H HB e ff fp [] s1 LB1 m0 msF mo Q); [exact HHb | exact HP | exact HI | intros b Hb; right; exact Hb | exact VIS | exact KR
      | lia | lia | unfold LB1; rewrite lb_small_cons; change (nsmall (blk_size (p1, b1, 500))) with 500; lia
      | unfold LB1; cbn [length]; lia | unfold LB1; rewrite nlarge_cons; change (nlg (blk_size (p1, b1, 500))) with 0; lia |].
    intros msF' mo' s' A p m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' junk VIS' KR' MP' HI' AP ABR NI CB AD AL'.
    rewrite (ret_pc_even WO_ON2_RA ltac:(unfold WO_ON2_RA; lia) eq_refl) in VIS'.
    assert (NE : p1 <> p) by (intros E; apply NI; left; exact E).
    eapply (ahh_evt_then H HB (wp2_post H e ff fp s' ((p, A, 100) :: LB1) b1 A) Q s' msF' _ mo'); [exact KR' | exact VIS' | |].
    - refine (wp2 H HHb e ff fp s' _ p1 p b1 A m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HP HI'
                  (or_intror (or_introl eq_refl)) (or_introl eq_refl) NE _ _ _ _ _ AD (proj2 CB)).
      + intros bb Hb. split; [right; right; exact Hb|]. intros E. apply NI. rewrite <- E. right. apply in_map. exact Hb.
      + exact (wfc_apres H e ff fp [] s1 LB1 LB1 m0 m' HP HI WC AP).
      + eapply (apres_rw_cells H); [exact AP | exact C48 | left; lia].
      + eapply (wpst_apres H e ff fp [] s1 LB1 LB1 m0 m'); [exact HP | exact HI | exact PST | exact AP | reflexivity | reflexivity | reflexivity].
      + eapply (wblk_apres H LB1 (wS1 e) m0 m' p1 b1 500); [exact WB | exact AP | left; reflexivity | lia].
    - intros msF2 mo2 KR2 MP2 P2. eapply K; [exact KR2 | | lia | exact NI | exact P2]. mpres_chain.
  Qed.

  Lemma seg_on3 : forall (Q : config -> Prop) (e : went H) ff fp msF mo s2 (p1 p2 : bptr) b1 b2,
    wpre H e -> as_AKREL H s2 (mkCfg msF mo) -> as_MPRES H (w_mo e) mo -> as_AL H s2 >= as_AL H (w_s e) ->
    ~ In p1 (map blk_id (w_LB e)) -> ~ In p2 (map blk_id ((p1, b1, 500) :: w_LB e)) ->
    wp2_post H e ff fp s2 ((p2, b2, 100) :: (p1, b1, 500) :: w_LB e) b1 b2 (as_VIS H s2 msF) ->
    (forall msF' mo' s3 (p3 : bptr) b3, as_AKREL H s3 (mkCfg msF' mo') -> as_MPRES H (w_mo e) mo' ->
       as_AL H s3 >= as_AL H (w_s e) -> ~ In p3 (map blk_id ((p2, b2, 100) :: (p1, b1, 500) :: w_LB e)) ->
       wp3_post H e ff fp s3 ((p3, b3, 100) :: (p2, b2, 100) :: (p1, b1, 500) :: w_LB e) b1 b2 b3 (as_VIS H s3 msF') ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q e ff fp msF mo s2 p1 p2 b1 b2 HP KR MP AL2 NI1 NI2 P2 K.
    destruct P2 as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m0 & VIS & HI & WC & C48 & PST & WB & WC2).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof (wpre_budget e HP) as (HN & BS & BC & BL & AL0).
    pose proof (po_budget_facts (w_n e) ltac:(lia)) as (PB1 & PB2 & PB3 & PB4).
    set (LB2 := (p2, b2, 100) :: (p1, b1, 500) :: w_LB e) in *.
    eapply (won H HB e ff fp [] s2 LB2 m0 msF mo Q); [exact HHb | exact HP | exact HI | intros b Hb; right; right; exact Hb | exact VIS | exact KR
      | lia | lia | unfold LB2; rewrite !lb_small_cons; change (nsmall (blk_size (p1, b1, 500))) with 500;
                    change (nsmall (blk_size (p2, b2, 100))) with 100; lia
      | unfold LB2; cbn [length]; lia
      | unfold LB2; rewrite !nlarge_cons; change (nlg (blk_size (p1, b1, 500))) with 0; change (nlg (blk_size (p2, b2, 100))) with 0; lia |].
    intros msF' mo' s' A p m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' junk VIS' KR' MP' HI' AP ABR NI CB AD AL'.
    rewrite (ret_pc_even WO_ON3_RA ltac:(unfold WO_ON3_RA; lia) eq_refl) in VIS'.
    assert (NE1 : p1 <> p) by (intros E; apply NI; right; left; exact E).
    assert (NE2 : p2 <> p) by (intros E; apply NI; left; exact E).
    eapply (ahh_evt_then H HB (wp3_post H e ff fp s' ((p, A, 100) :: LB2) b1 b2 A) Q s' msF' _ mo'); [exact KR' | exact VIS' | |].
    - refine (wp3 H HHb e ff fp s' _ p1 p2 p b1 b2 A m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HP HI'
                  (or_intror (or_intror (or_introl eq_refl))) (or_intror (or_introl eq_refl)) (or_introl eq_refl) NE1 NE2 _ _ _ _ _ _ AD (proj2 CB)).
      + intros bb Hb. split; [right; right; right; exact Hb|]. intros E. apply NI. rewrite <- E. right. right. apply in_map. exact Hb.
      + exact (wfc_apres H e ff fp [] s2 LB2 LB2 m0 m' HP HI WC AP).
      + eapply (apres_rw_cells H); [exact AP | exact C48 | left; lia].
      + eapply (wpst_apres H e ff fp [] s2 LB2 LB2 m0 m'); [exact HP | exact HI | exact PST | exact AP | reflexivity | reflexivity | reflexivity].
      + eapply (wblk_apres H LB2 (wS1 e) m0 m' p1 b1 500); [exact WB | exact AP | right; left; reflexivity | lia].
      + eapply (wblk_apres H LB2 (wS1 e) m0 m' p2 b2 100); [exact WC2 | exact AP | left; reflexivity | lia].
    - intros msF2 mo2 KR2 MP2 P3. eapply K; [exact KR2 | | lia | exact NI | exact P3]. mpres_chain.
  Qed.
End WoS1.
