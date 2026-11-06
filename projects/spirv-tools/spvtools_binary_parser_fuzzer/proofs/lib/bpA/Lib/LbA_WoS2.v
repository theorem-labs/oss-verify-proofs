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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_WoR2 LbA_WoR3 LbA_WoR4 LbA_WoR5 LbA_WoE0 LbA_WoE0b LbA_WoP LbA_WoQ LbA_WoF LbA_WoS1.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WoS2.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHb : asan_rt_hyps_bp H.
  Let HB := rt_bp_base H HHb.

  Ltac mpres_chain :=
    repeat match goal with
    | |- as_MPRES H ?a ?a => apply (ah_mpres_refl H HB)
    | K : as_MPRES H ?a ?b |- as_MPRES H ?a ?c => apply (ah_mpres_trans H HB a b c K)
    end.

  Lemma wps3_apres : forall LB m m' ff b1 b2 b3 (p1 p2 p3 : bptr) e fp XSc sk LBk, wpre H e -> winv H e ff fp XSc sk LBk m ->
    wps3 ff m b1 b2 b3 -> apres H LB (wS1 e) m m' -> In (p1, b1, 500) LB -> In (p2, b2, 100) LB -> In (p3, b3, 100) LB ->
    wps3 ff m' b1 b2 b3.
  Proof.
    intros LB m m' ff b1 b2 b3 p1 p2 p3 e fp XSc sk LBk HP HI (P & W1 & W2 & W3) AP I1 I2 I3.
    split; [eapply (wpst_apres H e ff fp XSc sk LBk LB m m'); [exact HP | exact HI | exact P | exact AP | reflexivity | reflexivity | reflexivity]|].
    split; [eapply (wblk_apres H LB (wS1 e) m m' p1 b1 500); [exact W1 | exact AP | exact I1 | lia]|].
    split; [eapply (wblk_apres H LB (wS1 e) m m' p2 b2 100); [exact W2 | exact AP | exact I2 | lia]|].
    eapply (wblk_apres H LB (wS1 e) m m' p3 b3 100); [exact W3 | exact AP | exact I3 | lia].
  Qed.

  Lemma lb_small_wcons : forall (p : bptr) A n LB, 0 <= n <= 64512 -> lb_small ((p, A, n) :: LB) = n + lb_small LB.
  Proof. intros p A n LB Hn. rewrite lb_small_cons. cbn [blk_size fst snd]. unfold nsmall. destruct (Z.leb_spec n 64512); lia. Qed.
  Lemma nlarge_wcons : forall (p : bptr) A n LB, 0 <= n <= 64512 -> nlarge ((p, A, n) :: LB) = nlarge LB.
  Proof. intros p A n LB Hn. rewrite nlarge_cons. cbn [blk_size fst snd]. unfold nlg. destruct (Z.ltb_spec 64512 n); lia. Qed.

  Lemma seg_on4 : forall (Q : config -> Prop) (e : went H) ff fp msF mo s3 (p1 p2 p3 : bptr) b1 b2 b3,
    let LB3 := (p3, b3, 100) :: (p2, b2, 100) :: (p1, b1, 500) :: w_LB e in
    wpre H e -> as_AKREL H s3 (mkCfg msF mo) -> as_MPRES H (w_mo e) mo -> as_AL H s3 >= as_AL H (w_s e) ->
    List.NoDup (map blk_id LB3) ->
    wp3_post H e ff fp s3 LB3 b1 b2 b3 (as_VIS H s3 msF) ->
    (forall msF' mo' s4 (p4 : bptr) g, as_AKREL H s4 (mkCfg msF' mo') -> as_MPRES H (w_mo e) mo' ->
       as_AL H s4 >= as_AL H (w_s e) -> List.NoDup (map blk_id ((p4, g, 500) :: LB3)) ->
       wq1_post H e ff fp s4 ((p4, g, 500) :: LB3) b1 b2 b3 b3 g (as_VIS H s4 msF') -> as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q e ff fp msF mo s3 p1 p2 p3 b1 b2 b3 LB3 HP KR MP AL3 ND P3 K.
    destruct P3 as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m0 & VIS & HI & WC & C48 & PST & W1 & W2 & W3 & TS).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof (wpre_budget H e HP) as (HN & BS & BC & BL & AL0).
    pose proof (po_budget_facts (w_n e) ltac:(lia)) as (PB1 & PB2 & PB3 & PB4).
    assert (PS : wps3 ff m0 b1 b2 b3) by (split; [exact PST|]; split; [exact W1|]; split; [exact W2 | exact W3]).
    eapply (won H HB e ff fp [] s3 LB3 m0 msF mo Q); [exact HHb | exact HP | exact HI | intros b Hb; right; right; right; exact Hb | exact VIS | exact KR
      | lia | lia | unfold LB3; rewrite !lb_small_wcons by lia; lia
      | unfold LB3; cbn [length]; lia | unfold LB3; rewrite !nlarge_wcons by lia; lia |].
    intros msF' mo' s' A p m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' junk VIS' KR' MP' HI' AP ABR NI CB AD AL'.
    rewrite (ret_pc_even WO_ON4_RA ltac:(unfold WO_ON4_RA; lia) eq_refl) in VIS'.
    assert (ND' : List.NoDup (map blk_id ((p, A, 500) :: LB3))) by (constructor; [exact NI | exact ND]).
    assert (NE : forall q, In q [p1; p2; p3] -> q <> p).
    { intros q Hq E. subst q. apply NI. unfold LB3. cbn [map]. destruct Hq as [E|[E|[E|[]]]]; subst; cbn; tauto. }
    eapply (ahh_evt_then H HB (wq1_post H e ff fp s' ((p, A, 500) :: LB3) b1 b2 b3 b3 A) Q s' msF' _ mo'); [exact KR' | exact VIS' | |].
    - refine (wq1 H HHb e ff fp s' _ p1 p2 p3 p b1 b2 b3 b3 A m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HP HI'
                  (or_intror (or_intror (or_intror (or_introl eq_refl)))) (or_intror (or_intror (or_introl eq_refl)))
                  (or_intror (or_introl eq_refl)) (or_introl eq_refl)
                  (NE p1 ltac:(cbn; tauto)) (NE p2 ltac:(cbn; tauto)) (NE p3 ltac:(cbn; tauto)) _ _ _ _ _ AD (proj2 CB)).
      + intros bb Hb. split; [right; right; right; right; exact Hb|]. intros E. apply NI. rewrite <- E. unfold LB3. right; right; right. apply in_map. exact Hb.
      + exact (wfc_apres H e ff fp [] s3 LB3 LB3 m0 m' HP HI WC AP).
      + eapply (apres_rw_cells H); [exact AP | exact C48 | left; lia].
      + eapply (wps3_apres LB3 m0 m' ff b1 b2 b3 p1 p2 p3 e fp [] s3 LB3 HP HI PS AP); unfold LB3; cbn; tauto.
      + eapply (wtst_apres H e LB3 m0 m'); [exact HP | exact TS | exact AP | reflexivity | reflexivity | reflexivity].
    - intros msF2 mo2 KR2 MP2 P4. eapply K; [exact KR2 | | lia | exact ND' | exact P4]. mpres_chain.
  Qed.

  Lemma seg_on5 : forall (Q : config -> Prop) (e : went H) ff fp msF mo s4 (p1 p2 p3 p4 : bptr) b1 b2 b3 g,
    let LB4 := (p4, g, 500) :: (p3, b3, 100) :: (p2, b2, 100) :: (p1, b1, 500) :: w_LB e in
    wpre H e -> as_AKREL H s4 (mkCfg msF mo) -> as_MPRES H (w_mo e) mo -> as_AL H s4 >= as_AL H (w_s e) ->
    List.NoDup (map blk_id LB4) ->
    wq1_post H e ff fp s4 LB4 b1 b2 b3 b3 g (as_VIS H s4 msF) ->
    (forall msF' mo' s5 (p5 : bptr) h, as_AKREL H s5 (mkCfg msF' mo') -> as_MPRES H (w_mo e) mo' ->
       as_AL H s5 >= as_AL H (w_s e) -> List.NoDup (map blk_id ((p5, h, 100) :: LB4)) ->
       wq2_post H e ff fp s5 ((p5, h, 100) :: LB4) b1 b2 b3 g h (as_VIS H s5 msF') -> as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q e ff fp msF mo s4 p1 p2 p3 p4 b1 b2 b3 g LB4 HP KR MP AL4 ND P4 K.
    destruct P4 as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m0 & VIS & HI & WC & C48 & PS & TS & WG).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof (wpre_budget H e HP) as (HN & BS & BC & BL & AL0).
    pose proof (po_budget_facts (w_n e) ltac:(lia)) as (PB1 & PB2 & PB3 & PB4).
    eapply (won H HB e ff fp [] s4 LB4 m0 msF mo Q); [exact HHb | exact HP | exact HI | intros b Hb; right; right; right; right; exact Hb | exact VIS | exact KR
      | lia | lia | unfold LB4; rewrite !lb_small_wcons by lia; lia
      | unfold LB4; cbn [length]; lia | unfold LB4; rewrite !nlarge_wcons by lia; lia |].
    intros msF' mo' s' A p m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' junk VIS' KR' MP' HI' AP ABR NI CB AD AL'.
    rewrite (ret_pc_even WO_ON5_RA ltac:(unfold WO_ON5_RA; lia) eq_refl) in VIS'.
    assert (ND' : List.NoDup (map blk_id ((p, A, 100) :: LB4))) by (constructor; [exact NI | exact ND]).
    assert (NE : forall q, In q [p1; p2; p3; p4] -> q <> p).
    { intros q Hq E. subst q. apply NI. unfold LB4. cbn [map]. destruct Hq as [E|[E|[E|[E|[]]]]]; subst; cbn; tauto. }
    eapply (ahh_evt_then H HB (wq2_post H e ff fp s' ((p, A, 100) :: LB4) b1 b2 b3 g A) Q s' msF' _ mo'); [exact KR' | exact VIS' | |].
    - refine (wq2 H HHb e ff fp s' _ p1 p2 p3 p4 p b1 b2 b3 b3 g A m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HP HI'
                  ltac:(unfold LB4; cbn; tauto) ltac:(unfold LB4; cbn; tauto) ltac:(unfold LB4; cbn; tauto) ltac:(unfold LB4; cbn; tauto)
                  (or_introl eq_refl)
                  (NE p1 ltac:(cbn; tauto)) (NE p2 ltac:(cbn; tauto)) (NE p3 ltac:(cbn; tauto)) (NE p4 ltac:(cbn; tauto)) _ _ _ _ _ _ AD (proj2 CB)).
      + intros bb Hb. split; [right; unfold LB4; right; right; right; right; exact Hb|]. intros E. apply NI. rewrite <- E. unfold LB4.
        right; right; right; right. apply in_map. exact Hb.
      + exact (wfc_apres H e ff fp [] s4 LB4 LB4 m0 m' HP HI WC AP).
      + eapply (apres_rw_cells H); [exact AP | exact C48 | left; lia].
      + eapply (wps3_apres LB4 m0 m' ff b1 b2 b3 p1 p2 p3 e fp [] s4 LB4 HP HI PS AP); unfold LB4; cbn; tauto.
      + eapply (wtst_apres H e LB4 m0 m'); [exact HP | exact TS | exact AP | reflexivity | reflexivity | reflexivity].
      + eapply (wblk_apres H LB4 (wS1 e) m0 m' p4 g 500); [exact WG | exact AP | left; reflexivity | lia].
    - intros msF2 mo2 KR2 MP2 P5. eapply K; [exact KR2 | | lia | exact ND' | exact P5]. mpres_chain.
  Qed.

  Lemma seg_on6 : forall (Q : config -> Prop) (e : went H) ff fp msF mo s5 (p1 p2 p3 p4 p5 : bptr) b1 b2 b3 g h,
    let LB5 := (p5, h, 100) :: (p4, g, 500) :: (p3, b3, 100) :: (p2, b2, 100) :: (p1, b1, 500) :: w_LB e in
    wpre H e -> as_AKREL H s5 (mkCfg msF mo) -> as_MPRES H (w_mo e) mo -> as_AL H s5 >= as_AL H (w_s e) ->
    List.NoDup (map blk_id LB5) ->
    wq2_post H e ff fp s5 LB5 b1 b2 b3 g h (as_VIS H s5 msF) ->
    (forall msF' mo' s6 (p6 : bptr) k, as_AKREL H s6 (mkCfg msF' mo') -> as_MPRES H (w_mo e) mo' ->
       as_AL H s6 >= as_AL H (w_s e) -> List.NoDup (map blk_id ((p6, k, 100) :: LB5)) ->
       wq3_post H e ff fp s6 ((p6, k, 100) :: LB5) b1 b2 b3 g h k (as_VIS H s6 msF') -> as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q e ff fp msF mo s5 p1 p2 p3 p4 p5 b1 b2 b3 g h LB5 HP KR MP AL5 ND P5 K.
    destruct P5 as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m0 & VIS & HI & WC & C48 & PS & TS & WG & WH).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof (wpre_budget H e HP) as (HN & BS & BC & BL & AL0).
    pose proof (po_budget_facts (w_n e) ltac:(lia)) as (PB1 & PB2 & PB3 & PB4).
    eapply (won H HB e ff fp [] s5 LB5 m0 msF mo Q); [exact HHb | exact HP | exact HI | intros b Hb; right; right; right; right; right; exact Hb | exact VIS | exact KR
      | lia | lia | unfold LB5; rewrite !lb_small_wcons by lia; lia
      | unfold LB5; cbn [length]; lia | unfold LB5; rewrite !nlarge_wcons by lia; lia |].
    intros msF' mo' s' A p m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' junk VIS' KR' MP' HI' AP ABR NI CB AD AL'.
    rewrite (ret_pc_even WO_ON6_RA ltac:(unfold WO_ON6_RA; lia) eq_refl) in VIS'.
    assert (ND' : List.NoDup (map blk_id ((p, A, 100) :: LB5))) by (constructor; [exact NI | exact ND]).
    assert (NE : forall q, In q [p1; p2; p3; p4; p5] -> q <> p).
    { intros q Hq E. subst q. apply NI. unfold LB5. cbn [map]. destruct Hq as [E|[E|[E|[E|[E|[]]]]]]; subst; cbn; tauto. }
    eapply (ahh_evt_then H HB (wq3_post H e ff fp s' ((p, A, 100) :: LB5) b1 b2 b3 g h A) Q s' msF' _ mo'); [exact KR' | exact VIS' | |].
    - refine (wq3 H HHb e ff fp s' _ p1 p2 p3 p4 p5 p b1 b2 b3 g h A m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HP HI'
                  ltac:(unfold LB5; cbn; tauto) ltac:(unfold LB5; cbn; tauto) ltac:(unfold LB5; cbn; tauto) ltac:(unfold LB5; cbn; tauto)
                  ltac:(unfold LB5; cbn; tauto) (or_introl eq_refl)
                  (NE p1 ltac:(cbn; tauto)) (NE p2 ltac:(cbn; tauto)) (NE p3 ltac:(cbn; tauto)) (NE p4 ltac:(cbn; tauto)) (NE p5 ltac:(cbn; tauto))
                  _ _ _ _ _ _ _ AD (proj2 CB)).
      + intros bb Hb. split; [right; unfold LB5; right; right; right; right; right; exact Hb|]. intros E. apply NI. rewrite <- E. unfold LB5.
        right; right; right; right; right. apply in_map. exact Hb.
      + exact (wfc_apres H e ff fp [] s5 LB5 LB5 m0 m' HP HI WC AP).
      + eapply (apres_rw_cells H); [exact AP | exact C48 | left; lia].
      + eapply (wps3_apres LB5 m0 m' ff b1 b2 b3 p1 p2 p3 e fp [] s5 LB5 HP HI PS AP); unfold LB5; cbn; tauto.
      + eapply (wtst_apres H e LB5 m0 m'); [exact HP | exact TS | exact AP | reflexivity | reflexivity | reflexivity].
      + eapply (wblk_apres H LB5 (wS1 e) m0 m' p4 g 500); [exact WG | exact AP | unfold LB5; cbn; tauto | lia].
      + eapply (wblk_apres H LB5 (wS1 e) m0 m' p5 h 100); [exact WH | exact AP | left; reflexivity | lia].
    - intros msF2 mo2 KR2 MP2 P6. eapply K; [exact KR2 | | lia | exact ND' | exact P6]. mpres_chain.
  Qed.
End WoS2.
