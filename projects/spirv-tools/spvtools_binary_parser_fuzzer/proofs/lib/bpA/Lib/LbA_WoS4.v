(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HTac HArr HSysStep HExec CellsX TacX HMem HMState HLFrame HCells HStep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPrelim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsStack0 AsWalk RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec LibIface FPSteps.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_SR LbA_Conv.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_MILB LbA_PrsStmt LbA_StateStmt LbA_Own LbA_RtOwn LbA_HKit LbA_HStKit.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_WoGen LbA_WoDefs LbA_WoKit LbA_WoKit2 LbA_WoKit3 LbA_WoSt LbA_WoSt2 LbA_WoMs LbA_WoCall LbA_WoCut LbA_WoZ.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_WoR2 LbA_WoR6 LbA_WoE0 LbA_WoE0b LbA_WoP LbA_WoF LbA_WoS1 LbA_WoS2 LbA_WoT2 LbA_WoPm LbA_WoU LbA_WoG.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WoS4.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHb : asan_rt_hyps_bp H.
  Let HB := rt_bp_base H HHb.

  Ltac mpres_chain :=
    repeat match goal with
    | |- as_MPRES H ?a ?a => apply (ah_mpres_refl H HB)
    | K : as_MPRES H ?a ?b |- as_MPRES H ?a ?c => apply (ah_mpres_trans H HB a b c K)
    end.

  Definition wpf (e : went H) (ff : Z) (LB10 LBs : list block) (c' : parserC) : Prop :=
       state_own LB10 (w_LB e) LBs (pc_state c') /\ pc_cons c' = ff + 48
    /\ st_words (pc_state c') = w_words e /\ st_nwords (pc_state c') = w_n e
    /\ lb_small LBs + 2 ^ 12 <= po_small (w_n e) /\ Z.of_nat (length LBs) + 8 <= po_cnt (w_n e) /\ nlarge LBs + 3 <= po_large (w_n e)
    /\ st_vsteps (pc_state c') /\ (forall q n, In (q, n) (state_blocks (pc_state c')) -> n <= 2 ^ 40).

  Lemma fresh_blk_ne : forall s LB m (p7 : bptr) u nu (q : bptr) p n,
    as_RHEAP H s ((p7, u, nu) :: LB) m -> ~ In p7 (map blk_id LB) -> In (q, p, n) LB -> p <> u.
  Proof.
    intros s LB m p7 u nu q p n RH NI IN E. subst p.
    assert (NE : q <> p7) by (intros E; subst q; apply NI; apply in_map_iff; exists (p7, u, n); split; [reflexivity | exact IN]).
    pose proof (ah_disj H HB _ _ _ (q, u, n) (p7, u, nu) RH (or_intror IN) (or_introl eq_refl) NE) as D. cbn in D.
    pose proof (ah_blocks H HB _ _ _ _ RH (or_intror IN)) as (_ & _ & Bn & _).
    pose proof (ah_blocks H HB _ _ _ _ RH (or_introl eq_refl)) as (_ & _ & Cn & _). cbn in Bn, Cn. lia.
  Qed.

  Lemma wpf_blocks : forall e ff LB10 LBs c' LBk, wpf e ff LB10 LBs c' -> (forall b, In b LB10 -> In b LBk) ->
    forall p n, In (p, n) (state_blocks (pc_state c')) -> exists q, In (q, p, n) LBs /\ In (q, p, n) LBk.
  Proof.
    intros e ff LB10 LBs c' LBk ((O1 & O2) & _) INC p n Hin.
    assert (L : In (p, n) (lbl LBs)) by (eapply Permutation_in; [apply Permutation_sym; exact O2 | exact Hin]).
    destruct (lbl_in_inv _ _ _ L) as (q & Hq). exists q. split; [exact Hq|]. apply INC.
    eapply Permutation_in; [apply Permutation_sym; exact O1|]. apply in_or_app. right. exact Hq.
  Qed.

  Lemma seg_on7 : forall (Q : config -> Prop) (e : went H) ff fp msF mo s10 LB10 LBs XS10 (c' : parserC) k,
    wpre H e -> as_AKREL H s10 (mkCfg msF mo) -> as_MPRES H (w_mo e) mo -> as_AL H s10 >= as_AL H (w_s e) - po_cost (w_n e) ->
    wy1_post H e ff fp XS10 s10 LB10 LBs c' k (as_VIS H s10 msF) ->
    (forall msF' mo' s11 (p7 : bptr) u (F : bvmap 5 word) (fc : bv 32) (r : Z),
       as_AKREL H s11 (mkCfg msF' mo') -> as_MPRES H (w_mo e) mo' -> as_AL H s11 >= as_AL H (w_s e) - po_cost (w_n e) ->
       wpf e ff LB10 LBs c' -> ~ In p7 (map blk_id LB10) -> frm_zero fc ->
       wv1_post H e ff fp XS10 s11 ((p7, u, 500) :: LB10) (pc_state c') k r u F fc (as_VIS H s11 msF') ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q e ff fp msF mo s10 LB10 LBs XS10 c' k HP KR MP AL10 P10 K.
    destruct P10 as (x5 & x6 & x7 & r & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & F & fc & m0
                     & VIS & FZ & HI & WC & C48 & OWN & PR & PSH & EC & EW & EN & B1 & B2 & B3 & VS & CAP & WRT).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CEL).
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wpre_budget H e HP) as (HN & BS & BC & BLg & AL0).
    pose proof (po_budget_facts (w_n e) ltac:(lia)) as (PB1 & PB2 & PB3 & PB4).
    assert (PF : wpf e ff LB10 LBs c') by (repeat (split; [assumption|]); exact CAP).
    destruct OWN as [O1 O2].
    assert (R : state_repA LB10 m0 (ff + 176) (pc_state c')).
    { destruct PR as [Pcons Puser Phdr Pins Phunk Pst Pdef Pal Prange Pconsf Pconsm Pconsd]. unfold ST_OFF in Pst.
      replace (ff + 176) with (ff + 128 + 48) by lia. exact Pst. }
    assert (SHP : state_sh m0 (pc_state c')) by exact (proj2 (proj2 PSH)).
    assert (INC : forall b, In b (w_LB e) -> In b LB10).
    { intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact O1|]. apply in_or_app. left. exact Hb. }
    assert (BL : forall p n, In (p, n) (state_blocks (pc_state c')) -> In (p, n) (lbl LB10)).
    { intros p n Hin. destruct (wpf_blocks e ff LB10 LBs c' LB10 PF (fun b Hb => Hb) p n Hin) as (q & _ & Hq). exact (lbl_in _ _ _ _ Hq). }
    assert (SM : lb_small LB10 = lb_small (w_LB e) + lb_small LBs) by (rewrite (lb_small_permW _ _ O1); apply lb_small_appW).
    assert (SL : nlarge LB10 = nlarge (w_LB e) + nlarge LBs) by (rewrite (nlarge_permW _ _ O1); apply nlarge_appW).
    pose proof (Permutation_length O1) as SC. rewrite length_app in SC.

    eapply (ahh_evt_then H HB (wu_post H e ff fp XS10 s10 LB10 (pc_state c') k r F fc) Q s10 msF _ mo); [exact KR | exact VIS | |].
    { exact (wu H HHb e ff fp XS10 s10 LB10 (pc_state c') k r m0 F fc x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HP HI WC C48 R SHP BL). }
    intros msF1 mo1 KR1 MP1 (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m1 & VIS1 & HI1 & WC1 & C481 & R1 & S1' & TS1).

    eapply (won H HB e ff fp XS10 s10 LB10 m1 msF1 mo1 Q); [exact HHb | exact HP | exact HI1 | exact INC | exact VIS1 | exact KR1
      | lia | lia | rewrite SM; lia | lia | rewrite SL; lia |].
    intros msF' mo' s' A p m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' junk VIS' KR' MP' HI' AP ABR NI CB AD AL'.
    rewrite (ret_pc_even WO_ON7_RA ltac:(unfold WO_ON7_RA; lia) eq_refl) in VIS'.
    pose proof (winv_rh H _ _ _ _ _ _ _ HI') as RH'.
    assert (BLK : forall q n, In (q, n) (state_blocks (pc_state c')) -> In (q, n) (lbl ((p, A, 500) :: LB10)) /\ q <> A).
    { intros q n Hin. destruct (wpf_blocks e ff LB10 LBs c' LB10 PF (fun b Hb => Hb) q n Hin) as (q0 & _ & Hq).
      split; [right; exact (lbl_in _ _ _ _ Hq) | exact (fresh_blk_ne s' LB10 m' p A 500 q0 q n RH' NI Hq)]. }
    destruct (wstate_ap H e ff fp XS10 s10 LB10 ((p, A, 500) :: LB10) m1 m' (pc_state c') HP HI1 AP
                ltac:(intros q n Hin; split; [exact (BL q n Hin) | exact (proj1 (BLK q n Hin))]) R1 S1') as [R2 S2].
    eapply (ahh_evt_then H HB (wv1_post H e ff fp XS10 s' ((p, A, 500) :: LB10) (pc_state c') k r A F fc) Q s' msF' _ mo'); [exact KR' | exact VIS' | |].
    - refine (wv1 H HHb e ff fp XS10 s' ((p, A, 500) :: LB10) p (pc_state c') k r A m' F fc t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
                  HP HI' (or_introl eq_refl) _ BLK _ _ R2 S2 _ AD (proj2 CB)).
      + intros bb Hb. split; [right; exact (INC bb Hb)|]. intros E. apply NI. rewrite <- E. apply in_map. exact (INC bb Hb).
      + exact (wfc2_apres H e ff fp XS10 s10 LB10 LB10 m1 m' HP HI1 WC1 AP).
      + eapply (apres_rw_cells H); [exact AP | exact C481 | left; lia].
      + eapply (wtst0_apres H e LB10 m1 m'); [exact HP | exact TS1 | exact AP | reflexivity | reflexivity | reflexivity].
    - intros msF2 mo2 KR2 MP2 P12. eapply (K msF2 mo2 s' p A F fc r); [exact KR2 | mpres_chain | lia | exact PF | exact NI | exact FZ | exact P12].
  Qed.

  Lemma seg_on8 : forall (Q : config -> Prop) (e : went H) ff fp msF mo s11 LB10 LBs XS10 (c' : parserC) (p7 : bptr) k r u
      (F : bvmap 5 word) (fc : bv 32),
    let LB11 := (p7, u, 500) :: LB10 in
    wpre H e -> as_AKREL H s11 (mkCfg msF mo) -> as_MPRES H (w_mo e) mo -> as_AL H s11 >= as_AL H (w_s e) - po_cost (w_n e) ->
    wpf e ff LB10 LBs c' -> ~ In p7 (map blk_id LB10) ->
    wv1_post H e ff fp XS10 s11 LB11 (pc_state c') k r u F fc (as_VIS H s11 msF) ->
    (forall msF' mo' s12 (p8 : bptr) v,
       as_AKREL H s12 (mkCfg msF' mo') -> as_MPRES H (w_mo e) mo' -> as_AL H s12 >= as_AL H (w_s e) - po_cost (w_n e) ->
       ~ In p8 (map blk_id LB11) ->
       wv2_post H e ff fp XS10 s12 ((p8, v, 100) :: LB11) (pc_state c') r u v F fc (as_VIS H s12 msF') ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q e ff fp msF mo s11 LB10 LBs XS10 c' p7 k r u F fc LB11 HP KR MP AL11 PF NI7 P12 K.
    destruct P12 as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m0 & VIS & HI & WC & C48 & R & SHP & TS & WU).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CEL).
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wpre_budget H e HP) as (HN & BS & BC & BLg & AL0).
    pose proof (po_budget_facts (w_n e) ltac:(lia)) as (PB1 & PB2 & PB3 & PB4).
    pose proof PF as ((O1 & O2) & _ & _ & _ & B1 & B2 & B3 & _).
    assert (INC : forall b, In b (w_LB e) -> In b LB11).
    { intros b Hb. right. eapply Permutation_in; [apply Permutation_sym; exact O1|]. apply in_or_app. left. exact Hb. }
    assert (BL0 : forall p n, In (p, n) (state_blocks (pc_state c')) -> In (p, n) (lbl LB11)).
    { intros p n Hin. destruct (wpf_blocks e ff LB10 LBs c' LB11 PF (fun b Hb => or_intror Hb) p n Hin) as (q & _ & Hq). exact (lbl_in _ _ _ _ Hq). }
    assert (SM : lb_small LB10 = lb_small (w_LB e) + lb_small LBs) by (rewrite (lb_small_permW _ _ O1); apply lb_small_appW).
    assert (SL : nlarge LB10 = nlarge (w_LB e) + nlarge LBs) by (rewrite (nlarge_permW _ _ O1); apply nlarge_appW).
    pose proof (Permutation_length O1) as SC. rewrite length_app in SC.
    eapply (won H HB e ff fp XS10 s11 LB11 m0 msF mo Q); [exact HHb | exact HP | exact HI | exact INC | exact VIS | exact KR
      | lia | lia | unfold LB11; rewrite lb_small_wcons, SM by lia; lia | unfold LB11; cbn [length]; lia
      | unfold LB11; rewrite nlarge_wcons, SL by lia; clear - BLg B3 PB3; lia |].
    intros msF' mo' s' A p m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' junk VIS' KR' MP' HI' AP ABR NI CB AD AL'.
    rewrite (ret_pc_even WO_ON8_RA ltac:(unfold WO_ON8_RA; lia) eq_refl) in VIS'.
    pose proof (winv_rh H _ _ _ _ _ _ _ HI') as RH'.
    assert (NE : p7 <> p) by (intros E; apply NI; unfold LB11; left; exact E).
    assert (BLK : forall q n, In (q, n) (state_blocks (pc_state c')) -> In (q, n) (lbl ((p, A, 100) :: LB11)) /\ q <> A).
    { intros q n Hin. destruct (wpf_blocks e ff LB10 LBs c' LB11 PF (fun b Hb => or_intror Hb) q n Hin) as (q0 & _ & Hq).
      split; [right; exact (lbl_in _ _ _ _ Hq) | exact (fresh_blk_ne s' LB11 m' p A 100 q0 q n RH' NI Hq)]. }
    destruct (wstate_ap H e ff fp XS10 s11 LB11 ((p, A, 100) :: LB11) m0 m' (pc_state c') HP HI AP
                ltac:(intros q n Hin; split; [exact (BL0 q n Hin) | exact (proj1 (BLK q n Hin))]) R SHP) as [R2 S2].
    eapply (ahh_evt_then H HB (wv2_post H e ff fp XS10 s' ((p, A, 100) :: LB11) (pc_state c') r u A F fc) Q s' msF' _ mo'); [exact KR' | exact VIS' | |].
    - refine (wv2 H HHb e ff fp XS10 s' ((p, A, 100) :: LB11) p7 p (pc_state c') k r u A m' F fc t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
                  HP HI' (or_intror (or_introl eq_refl)) (or_introl eq_refl) NE _ BLK _ _ R2 S2 _ _ AD (proj2 CB)).
      + intros bb Hb. split; [right; exact (INC bb Hb)|]. intros E. apply NI. rewrite <- E. apply in_map. exact (INC bb Hb).
      + exact (wfc2_apres H e ff fp XS10 s11 LB11 LB11 m0 m' HP HI WC AP).
      + eapply (apres_rw_cells H); [exact AP | exact C48 | left; lia].
      + eapply (wtst0_apres H e LB11 m0 m'); [exact HP | exact TS | exact AP | reflexivity | reflexivity | reflexivity].
      + eapply (wblk_apres H LB11 (wS1 e) m0 m' p7 u 500); [exact WU | exact AP | left; reflexivity | lia].
    - intros msF2 mo2 KR2 MP2 P13. eapply (K msF2 mo2 s' p A); [exact KR2 | mpres_chain | lia | exact NI | exact P13].
  Qed.

  Lemma seg_on9 : forall (Q : config -> Prop) (e : went H) ff fp msF mo s12 LB10 LBs XS10 (c' : parserC) (p7 p8 : bptr) (r u v : Z)
      (F : bvmap 5 word) (fc : bv 32),
    let LB12 := (p8, v, 100) :: (p7, u, 500) :: LB10 in
    wpre H e -> as_AKREL H s12 (mkCfg msF mo) -> as_MPRES H (w_mo e) mo -> as_AL H s12 >= as_AL H (w_s e) - po_cost (w_n e) ->
    wpf e ff LB10 LBs c' -> ~ In p7 (map blk_id LB10) -> ~ In p8 (map blk_id ((p7, u, 500) :: LB10)) ->
    wv2_post H e ff fp XS10 s12 LB12 (pc_state c') r u v F fc (as_VIS H s12 msF) ->
    (forall msF' mo' s13 (p9 : bptr) w,
       as_AKREL H s13 (mkCfg msF' mo') -> as_MPRES H (w_mo e) mo' -> as_AL H s13 >= as_AL H (w_s e) - po_cost (w_n e) ->
       ~ In p9 (map blk_id LB12) ->
       wv3_post H e ff fp XS10 s13 ((p9, w, 100) :: LB12) (pc_state c') r u v w F fc (as_VIS H s13 msF') ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q e ff fp msF mo s12 LB10 LBs XS10 c' p7 p8 r u v F fc LB12 HP KR MP AL12 PF NI7 NI8 P13 K.
    destruct P13 as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m0 & VIS & HI & WC & C48 & R & SHP & TS & WU & WV).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CEL).
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wpre_budget H e HP) as (HN & BS & BC & BLg & AL0).
    pose proof (po_budget_facts (w_n e) ltac:(lia)) as (PB1 & PB2 & PB3 & PB4).
    pose proof PF as ((O1 & O2) & _ & _ & _ & B1 & B2 & B3 & _).
    assert (INC : forall b, In b (w_LB e) -> In b LB12).
    { intros b Hb. right. right. eapply Permutation_in; [apply Permutation_sym; exact O1|]. apply in_or_app. left. exact Hb. }
    assert (BL0 : forall p n, In (p, n) (state_blocks (pc_state c')) -> In (p, n) (lbl LB12)).
    { intros p n Hin. destruct (wpf_blocks e ff LB10 LBs c' LB12 PF (fun b Hb => or_intror (or_intror Hb)) p n Hin) as (q & _ & Hq). exact (lbl_in _ _ _ _ Hq). }
    assert (SM : lb_small LB10 = lb_small (w_LB e) + lb_small LBs) by (rewrite (lb_small_permW _ _ O1); apply lb_small_appW).
    assert (SL : nlarge LB10 = nlarge (w_LB e) + nlarge LBs) by (rewrite (nlarge_permW _ _ O1); apply nlarge_appW).
    pose proof (Permutation_length O1) as SC. rewrite length_app in SC.
    eapply (won H HB e ff fp XS10 s12 LB12 m0 msF mo Q); [exact HHb | exact HP | exact HI | exact INC | exact VIS | exact KR
      | lia | lia | unfold LB12; rewrite !lb_small_wcons, SM by lia; lia | unfold LB12; cbn [length]; lia
      | unfold LB12; rewrite !nlarge_wcons, SL by lia; clear - BLg B3 PB3; lia |].
    intros msF' mo' s' A p m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' junk VIS' KR' MP' HI' AP ABR NI CB AD AL'.
    rewrite (ret_pc_even WO_ON9_RA ltac:(unfold WO_ON9_RA; lia) eq_refl) in VIS'.
    pose proof (winv_rh H _ _ _ _ _ _ _ HI') as RH'.
    assert (NE7 : p7 <> p) by (intros E; apply NI; unfold LB12; right; left; exact E).
    assert (NE8 : p8 <> p) by (intros E; apply NI; unfold LB12; left; exact E).
    assert (BLK : forall q n, In (q, n) (state_blocks (pc_state c')) -> In (q, n) (lbl ((p, A, 100) :: LB12)) /\ q <> A).
    { intros q n Hin. destruct (wpf_blocks e ff LB10 LBs c' LB12 PF (fun b Hb => or_intror (or_intror Hb)) q n Hin) as (q0 & _ & Hq).
      split; [right; exact (lbl_in _ _ _ _ Hq) | exact (fresh_blk_ne s' LB12 m' p A 100 q0 q n RH' NI Hq)]. }
    destruct (wstate_ap H e ff fp XS10 s12 LB12 ((p, A, 100) :: LB12) m0 m' (pc_state c') HP HI AP
                ltac:(intros q n Hin; split; [exact (BL0 q n Hin) | exact (proj1 (BLK q n Hin))]) R SHP) as [R2 S2].
    eapply (ahh_evt_then H HB (wv3_post H e ff fp XS10 s' ((p, A, 100) :: LB12) (pc_state c') r u v A F fc) Q s' msF' _ mo'); [exact KR' | exact VIS' | |].
    - refine (wv3 H HHb e ff fp XS10 s' ((p, A, 100) :: LB12) p7 p8 p (pc_state c') r u v A m' F fc t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
                  HP HI' (or_intror (or_intror (or_introl eq_refl))) (or_intror (or_introl eq_refl)) (or_introl eq_refl) NE7 NE8 _ BLK _ _ R2 S2 _ _ _ AD (proj2 CB)).
      + intros bb Hb. split; [right; exact (INC bb Hb)|]. intros E. apply NI. rewrite <- E. apply in_map. exact (INC bb Hb).
      + exact (wfc2_apres H e ff fp XS10 s12 LB12 LB12 m0 m' HP HI WC AP).
      + eapply (apres_rw_cells H); [exact AP | exact C48 | left; lia].
      + eapply (wtst0_apres H e LB12 m0 m'); [exact HP | exact TS | exact AP | reflexivity | reflexivity | reflexivity].
      + eapply (wblk_apres H LB12 (wS1 e) m0 m' p7 u 500); [exact WU | exact AP | right; left; reflexivity | lia].
      + eapply (wblk_apres H LB12 (wS1 e) m0 m' p8 v 100); [exact WV | exact AP | left; reflexivity | lia].
    - intros msF2 mo2 KR2 MP2 P14. eapply (K msF2 mo2 s' p A); [exact KR2 | mpres_chain | lia | exact NI | exact P14].
  Qed.
End WoS4.
