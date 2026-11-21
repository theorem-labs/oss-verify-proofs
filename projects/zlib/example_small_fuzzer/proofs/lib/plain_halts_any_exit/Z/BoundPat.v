(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz DeflateBlk Deflate DeflateSafe DeflateOverlay.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Deflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateSafe OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateOverlay.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateRel RefDeflSafeG RefDeflSafeFB RefDeflSafeLF RefDeflSafeL5.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeI1 RefDeflSafeI2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeLF.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeLF.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeI6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeI3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeI4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require BoundSlow.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require BoundSlow BoundCore.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.BoundSlow.BoundFw OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.BoundSlow OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.BoundCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Record PAT (s : deflate_state) : Prop := {
  pt_level : ds_level s = 6;
  pt_strategy : ds_strategy s = 0;
  pt_wrap : ds_wrap s = 1 \/ (ds_wrap s = -1 /\ ds_status s = FINISH_STATE);
  pt_status : ds_status s = INIT_STATE \/ ds_status s = BUSY_STATE \/ ds_status s = FINISH_STATE;
  pt_gz : ds_gzhead s = 0;
  pt_ins : ds_insert s = 0 \/ ds_status s = FINISH_STATE;
  pt_lbs : ds_lit_bufsize s = 16384;
  pt_ws : ds_w_size s = 32768 }.

Lemma PAT_PF : forall s s', PF s' = PF s -> PAT s -> PAT s'.
Proof.
  intros s s' E [P1 P2 P3 P4 P5 P6 P7 P8].
  pose proof (PF_fields _ _ E) as ((_ & _ & _ & _ & El & Es) & (_ & Ei & _ & _ & _ & _ & _ & Ew) & (Est & Elb & _) & (_ & _ & _ & Eg & _ & _ & _ & _ & EK)).
  pose proof (KV_fields _ _ EK) as (Ews & _).
  constructor; rewrite ?El, ?Es, ?Ew, ?Est, ?Eg, ?Ei, ?Elb, ?Ews; assumption.
Qed.

Lemma PAT_slf : forall s v, PAT s -> PAT (set_last_flush s v).
Proof. intros s v [P1 P2 P3 P4 P5 P6 P7 P8]. constructor; assumption. Qed.
Lemma PAT_set_strm : forall s c, PAT s -> PAT (set_strm s c).
Proof. intros s c [P1 P2 P3 P4 P5 P6 P7 P8]. constructor; assumption. Qed.
Lemma PAT_err : forall s e, PAT s -> PAT (fst (err_return s e)).
Proof. intros s e P. rewrite err_return_fst. apply PAT_set_strm. exact P. Qed.

Lemma PAT_busy : forall s, PAT s -> ds_status s = INIT_STATE -> PAT (set_status s BUSY_STATE).
Proof.
  intros s [P1 P2 P3 P4 P5 P6 P7 P8] E.
  assert (W : ds_wrap s = 1) by (destruct P3 as [W|[_ F]]; [exact W | rewrite E in F; discriminate F]).
  assert (I : ds_insert s = 0) by (destruct P6 as [I|F]; [exact I | rewrite E in F; discriminate F]).
  constructor; try assumption.
  - left. exact W.
  - right. left. reflexivity.
  - left. exact I.
Qed.

Lemma PAT_finish : forall s, PAT s -> ds_status s <> FINISH_STATE -> PAT (set_status s FINISH_STATE).
Proof.
  intros s [P1 P2 P3 P4 P5 P6 P7 P8] N.
  assert (W : ds_wrap s = 1) by (destruct P3 as [W|[_ F]]; [exact W | contradiction]).
  constructor; try assumption.
  - left. exact W.
  - right. right. reflexivity.
  - right. reflexivity.
Qed.

Lemma PAT_wrapneg : forall s, PAT s -> ds_status s = FINISH_STATE -> PAT (set_wrap s (-1)).
Proof.
  intros s [P1 P2 P3 P4 P5 P6 P7 P8] F. constructor; try assumption.
  right. split; [reflexivity | exact F].
Qed.

Lemma PAT_dmode : forall s, PAT s -> dmode s = 4.
Proof. intros s P. exact (dmode4 s (pt_level _ P) (pt_strategy _ P)). Qed.

Lemma PF_zhdr_pre : forall s,
  exists t, zhdr_st s = set_status t BUSY_STATE /\ PF t = PF s.
Proof.
  intros s. unfold zhdr_st. cbv zeta.
  match goal with |- context [putShortMSB s ?hd] => generalize hd end. intros hdr.
  eexists. split; [reflexivity|].
  match goal with |- PF (set_strm ?u _) = _ => assert (E : PF u = PF s) end.
  { destruct (negb (ds_strstart (putShortMSB s hdr) =? 0)); reflexivity. }
  rewrite <- E. reflexivity.
Qed.

Lemma PF_trailer : forall s, PF (trailer_st s) = PF s.
Proof. intros s. unfold trailer_st. cbv zeta. destruct (ds_wrap s =? 2); reflexivity. Qed.

Section CallP.
  Variable c0 : cstrm.
  Variable s0 : deflate_state.
  Hypothesis HC0 : C0OK' c0.
  Hypothesis Hs0 : ds_strm s0 = c0.
  Hypothesis D0 : dwf s0.
  Let HC0w : C0OK c0 := c0'_ok _ HC0.
  Local Abbreviation ST := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeI4.ST c0 s0).

  Definition P2 (s : deflate_state) : Prop := ST s /\ PAT s.

  Lemma P2_slf : forall s v, P2 s -> - 2 <= v <= 5 -> P2 (set_last_flush s v).
  Proof. intros s v [H P] Hv. split; [exact (ST_set_last_flush c0 s0 s v H Hv) | exact (PAT_slf s v P)]. Qed.
  Lemma P2_err : forall s e, P2 s -> P2 (fst (err_return s e)).
  Proof. intros s e [H P]. split; [exact (ST_err_return c0 s0 s e H) | exact (PAT_err s e P)]. Qed.
  Lemma P2_fp : forall s, P2 s -> P2 (flush_pending s) /\ (ds_pending (flush_pending s) = 0 \/ cs_avail_out (ds_strm (flush_pending s)) = 0).
  Proof.
    intros s [H P]. destruct (ST_flush_pending c0 s0 HC0 s H) as (H' & _ & Hor & _).
    split; [split; [exact H' | exact (PAT_PF _ _ (PF_flush_pending s) P)] | exact Hor].
  Qed.

  Lemma P2_blocks : forall s flush, P2 s -> ds_pending s = 0 -> flush = Z_NO_FLUSH \/ flush = Z_FINISH ->
    (ds_status s = FINISH_STATE -> cs_avail_in (ds_strm s) = 0) ->
    let r := deflate_blocks s flush in
    P2 (fst r) /\ (snd r = None -> ds_pending (fst r) = 0 /\ (flush = Z_FINISH -> ds_status (fst r) = FINISH_STATE)).
  Proof.
    intros s flush [HS P] Hp HFL Hfin. pose proof HS as [H K]. pose proof H as [[D X] V].
    assert (Hfl : 0 <= flush <= 5) by (destruct HFL as [-> | ->]; unfold Z_NO_FLUSH, Z_FINISH; lia).
    unfold deflate_blocks.
    match goal with |- context [if ?c then _ else (s, None)] => destruct c eqn:Hcond end.
    2:{ cbn [fst snd]. split; [exact (conj HS P)|]. intros _. split; [exact Hp|]. intros Hf.
        apply orb_false_iff in Hcond as [Hcond C3]. apply andb_false_iff in C3. destruct C3 as [C3|C3].
        - exfalso. rewrite Hf in C3. cbn in C3. discriminate C3.
        - destruct (Z.eqb_spec (ds_status s) FINISH_STATE); [assumption | discriminate C3]. }
    assert (Hst0 : ds_status s <> FINISH_STATE).
    { intros Ef. rewrite (Hfin Ef), (dx_fin _ X Ef), Ef in Hcond. cbn in Hcond. rewrite andb_false_r in Hcond. discriminate Hcond. }
    clear Hcond.
    pose proof (PAT_dmode s P) as Em.
    assert (PRE : BFPRE c0 s flush) by (split; [exact HC0|]; split; [exact H|]; split; [exact Hp|]; split; [exact Hst0 | exact Hfl]).
    destruct (slow_bf_spec FB_CALL_ok c0 s flush PRE Em) as [_ POST].
    pose proof (bslow_frames c0 s flush FB_CALL_ok PRE Em (pt_ws _ P) HFL) as BS. cbv zeta in BS.
    rewrite run_compress_func_dmode, Em. cbv iota.
    unfold BFPOST in POST.
    destruct (deflate_slow s flush) as [s1 bst]. cbn [fst snd] in POST, BS. cbv beta iota zeta.
    destruct POST as (H1 & K1 & O1 & Pbd & Pfin & Pfd). destruct BS as (B3 & B4 & B5 & B6).
    assert (HS1 : ST s1) by (split; [exact H1 | rewrite K1; exact K]).
    destruct (CF_fields _ _ B3) as (El & Es & Ew & Est & _). pose proof (KV_fields _ _ K1) as (Kw & _ & Kl & _).
    assert (P1 : bst = need_more \/ ds_status s1 = FINISH_STATE -> PAT s1).
    { intros Hc. destruct P as [Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8]. constructor; rewrite ?El, ?Es, ?Ew, ?Est, ?Kl, ?Kw; try assumption.
      - unfold GZ in B4. rewrite B4. exact Q5.
      - destruct Hc as [Hc|Hc]; [| rewrite Est in Hc; contradiction].
        left. apply (B5 Hc). destruct Q6 as [I|F]; [exact I | contradiction]. }
    assert (P1f : bst <> need_more -> PAT (set_status s1 FINISH_STATE)).
    { intros _. destruct P as [Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8].
      assert (W : ds_wrap s = 1) by (destruct Q3 as [W|[_ F]]; [exact W | contradiction]).
      constructor.
      - change (ds_level s1 = 6). rewrite El. exact Q1.
      - change (ds_strategy s1 = 0). rewrite Es. exact Q2.
      - left. change (ds_wrap s1 = 1). rewrite Ew. exact W.
      - right. right. reflexivity.
      - change (ds_gzhead s1 = 0). unfold GZ in B4. rewrite B4. exact Q5.
      - right. reflexivity.
      - change (ds_lit_bufsize s1 = 16384). rewrite Kl. exact Q7.
      - change (ds_w_size s1 = 32768). rewrite Kw. exact Q8. }
    destruct bst; cbn [block_state_eqb orb]; cbv iota.
    -
      pose proof (P1 (or_introl eq_refl)) as PP.
      destruct (cs_avail_out (ds_strm s1) =? 0); cbn [fst snd].
      + split; [apply P2_slf; [exact (conj HS1 PP) | lia] | intros E; discriminate E].
      + split; [exact (conj HS1 PP) | intros E; discriminate E].
    -
      exfalso. destruct (B6 ltac:(discriminate)) as (_ & [E|E]); discriminate E.
    -
      destruct (DC_set_status c0 s1 FINISH_STATE H1 ltac:(unfold FINISH_STATE; lia) ltac:(intros; reflexivity)
                  ltac:(intros _; exact (Pfin (or_introl eq_refl)))) as (H2 & K2 & S2).
      pose proof (P1f ltac:(discriminate)) as PP.
      assert (HS2 : ST (set_status s1 FINISH_STATE)) by (split; [exact H2 | rewrite K2, K1; exact K]).
      set (s2 := set_status s1 FINISH_STATE) in *. clearbody s2.
      destruct (cs_avail_out (ds_strm s2) =? 0); cbn [fst snd].
      + split; [apply P2_slf; [exact (conj HS2 PP) | lia] | intros E; discriminate E].
      + split; [exact (conj HS2 PP) | intros E; discriminate E].
    -
      destruct (DC_set_status c0 s1 FINISH_STATE H1 ltac:(unfold FINISH_STATE; lia) ltac:(intros; reflexivity)
                  ltac:(intros _; exact (Pfin (or_intror eq_refl)))) as (H2 & K2 & S2).
      pose proof (P1f ltac:(discriminate)) as PP.
      assert (HS2 : ST (set_status s1 FINISH_STATE)) by (split; [exact H2 | rewrite K2, K1; exact K]).
      assert (Pd2 : ds_pending (set_status s1 FINISH_STATE) = ds_pending s1) by reflexivity.
      assert (St2 : ds_status (set_status s1 FINISH_STATE) = FINISH_STATE) by reflexivity.
      set (s2 := set_status s1 FINISH_STATE) in *. clearbody s2.
      cbn [fst snd]. split; [exact (conj HS2 PP)|]. intros _. split; [rewrite Pd2; exact (Pfd eq_refl) | intros _; exact St2].
  Qed.

  Theorem pat_core : forall flush, P2 s0 -> flush = Z_NO_FLUSH \/ flush = Z_FINISH -> P2 (fst (deflate_core s0 flush)).
  Proof.
    intros flush PP0 HFL. pose proof PP0 as [HS0 P0].
    assert (Hfl : 0 <= flush <= 5) by (destruct HFL as [-> | ->]; unfold Z_NO_FLUSH, Z_FINISH; lia).
    unfold deflate_core.
    destruct (deflateStateCheck s0 || (Z_BLOCK <? flush) || (flush <? 0)); [cbn [fst]; exact PP0|].
    destruct ((ds_status s0 =? FINISH_STATE) && negb (flush =? Z_FINISH)); [apply P2_err; exact PP0|].
    destruct (cs_avail_out (ds_strm s0) =? 0); [apply P2_err; exact PP0|].
    cbv zeta.
    pose proof (P2_slf s0 flush PP0 ltac:(lia)) as PP1.
    assert (Pd1 : ds_pending (set_last_flush s0 flush) = ds_pending s0) by reflexivity.
    set (s1 := set_last_flush s0 flush) in *. clearbody s1.
    match goal with |- P2 (fst (let '(s, r) := ?head in _)) => destruct head as [s2 r2] eqn:Ehead end.
    assert (H2 : P2 s2 /\ (r2 = None -> ds_pending s2 = 0)).
    { destruct (negb (ds_pending s1 =? 0)) eqn:Ep.
      - destruct (P2_fp s1 PP1) as [PPf Hor].
        destruct (Z.eqb_spec (cs_avail_out (ds_strm (flush_pending s1))) 0) as [Ea|Ea]; inversion Ehead; subst s2 r2.
        + split; [apply P2_slf; [exact PPf | lia] | intros HH; discriminate HH].
        + split; [exact PPf | intros _; destruct Hor as [X0|X0]; [exact X0 | contradiction]].
      - destruct ((cs_avail_in (ds_strm s1) =? 0) && (RANK flush <=? RANK (ds_last_flush s0)) && negb (flush =? Z_FINISH)).
        + unfold err_return in Ehead. inversion Ehead; subst s2 r2. split; [exact (P2_err s1 Z_BUF_ERROR PP1) | intros HH; discriminate HH].
        + inversion Ehead; subst s2 r2. split; [exact PP1|]. intros _. destruct (Z.eqb_spec (ds_pending s1) 0); [assumption | discriminate Ep]. }
    clear Ehead. destruct H2 as [PP2 Hp2].
    destruct r2 as [rc|]; [cbn [fst]; exact PP2|]. specialize (Hp2 eq_refl).
    destruct ((ds_status s2 =? FINISH_STATE) && negb (cs_avail_in (ds_strm s2) =? 0)) eqn:Efa; [apply P2_err; exact PP2|].
    pose proof PP2 as [HS2 P2'].
    assert (E4 : ((ds_status s2 =? INIT_STATE) && (ds_wrap s2 =? 0)) = false).
    { destruct (Z.eqb_spec (ds_status s2) INIT_STATE) as [E|E]; [| reflexivity].
      destruct (pt_wrap _ P2') as [W|[_ F]]; [rewrite W; reflexivity | rewrite E in F; discriminate F]. }
    rewrite E4.
    rewrite deflate_zlib_header_eq.
    match goal with |- P2 (fst (let '(s, r) := ?head in _)) => destruct head as [s5 r5] eqn:Ehead end.
    assert (H5 : P2 s5 /\ (r5 = None -> ds_pending s5 = 0 /\ cs_avail_in (ds_strm s5) = cs_avail_in (ds_strm s2)
                                        /\ (ds_status s5 = FINISH_STATE -> ds_status s2 = FINISH_STATE))).
    { destruct (Z.eqb_spec (ds_status s2) INIT_STATE) as [E|E].
      - destruct (hdr_zlib c0 s0 HC0 Hs0 D0 s2 HS2 Hp2 E) as (_ & HSz & Stz & Horz & Aiz & _).
        assert (Pz : PAT (flush_pending (zhdr_st s2))).
        { apply (PAT_PF _ _ (PF_flush_pending (zhdr_st s2))). destruct (PF_zhdr_pre s2) as (t & Et & Pt). rewrite Et.
          apply PAT_busy; [exact (PAT_PF _ _ Pt P2')|].
          pose proof (PF_fields _ _ Pt) as (_ & _ & (Est & _) & _). rewrite Est. exact E. }
        cbv zeta in Ehead. destruct (negb (ds_pending (flush_pending (zhdr_st s2)) =? 0)) eqn:Ep; inversion Ehead; subst s5 r5.
        + split; [apply P2_slf; [exact (conj HSz Pz) | lia] | intros HH; discriminate HH].
        + split; [exact (conj HSz Pz)|]. intros _. rewrite Aiz, Stz.
          split; [destruct (Z.eqb_spec (ds_pending (flush_pending (zhdr_st s2))) 0); [assumption | discriminate Ep]|].
          split; [reflexivity | unfold BUSY_STATE, FINISH_STATE; intros; lia].
      - inversion Ehead; subst s5 r5. split; [exact PP2|]. intros _. split; [exact Hp2|]. split; [reflexivity | intros X; exact X]. }
    clear Ehead. destruct H5 as [PP5 Hr5].
    destruct r5 as [rc|]; [cbn [fst]; exact PP5|]. destruct (Hr5 eq_refl) as (Hp5 & Ai5 & Fin5).
    assert (E6 : (ds_status s5 =? GZIP_STATE) = false).
    { destruct (pt_status _ (proj2 PP5)) as [E|[E|E]]; rewrite E; reflexivity. }
    rewrite E6.
    assert (Hfin5 : ds_status s5 = FINISH_STATE -> cs_avail_in (ds_strm s5) = 0).
    { intros E. rewrite Ai5. pose proof (Fin5 E) as E2. rewrite E2 in Efa. cbn in Efa.
      destruct (Z.eqb_spec (cs_avail_in (ds_strm s2)) 0); [assumption | discriminate Efa]. }
    destruct (P2_blocks s5 flush PP5 Hp5 HFL Hfin5) as [PP7 Hr7]. cbv zeta in PP7, Hr7.
    destruct (deflate_blocks s5 flush) as [s7 r7]. cbn [fst snd] in PP7, Hr7.
    destruct r7 as [rc|]; [cbn [fst]; exact PP7|]. destruct (Hr7 eq_refl) as [Hp7 Hfin7].
    destruct (negb (flush =? Z_FINISH)) eqn:Ef; [cbn [fst]; exact PP7|].
    assert (Hf : flush = Z_FINISH) by (destruct (Z.eqb_spec flush Z_FINISH); [assumption | discriminate Ef]).
    destruct (Z.leb_spec (ds_wrap s7) 0) as [Hw|Hw]; [cbn [fst]; exact PP7|].
    destruct PP7 as [HS7 P7].
    pose proof (proj2 (finish_stage c0 s0 HC0 Hs0 D0 s7 flush HS7 Hp7 Hfl Hfin7) Hf Hw) as HT.
    revert HT. rewrite deflate_trailer_eq. cbv zeta.
    assert (Pt : PAT (flush_pending (trailer_st s7))) by (apply (PAT_PF _ _ (PF_flush_pending (trailer_st s7))); exact (PAT_PF _ _ (PF_trailer s7) P7)).
    assert (St : ds_status (flush_pending (trailer_st s7)) = FINISH_STATE).
    { pose proof (PF_fields _ _ (PF_flush_pending (trailer_st s7))) as (_ & _ & (E1 & _) & _).
      pose proof (PF_fields _ _ (PF_trailer s7)) as (_ & _ & (E2 & _) & _). rewrite E1, E2. exact (Hfin7 Hf). }
    assert (Wt : ds_wrap (flush_pending (trailer_st s7)) = 1).
    { destruct (pt_wrap _ Pt) as [W|[W _]]; [exact W|].
      pose proof (PF_fields _ _ (PF_flush_pending (trailer_st s7))) as (_ & (_ & _ & _ & _ & _ & _ & _ & E1) & _).
      pose proof (PF_fields _ _ (PF_trailer s7)) as (_ & (_ & _ & _ & _ & _ & _ & _ & E2) & _). rewrite E1, E2 in W. lia. }
    set (s8 := flush_pending (trailer_st s7)) in *. clearbody s8.
    rewrite Wt. change (0 <? 1) with true. cbv iota. change (Z.opp 1) with (-1). cbn [fst]. intros HT.
    split; [exact HT | exact (PAT_wrapneg s8 Pt St)].
  Qed.
End CallP.

Theorem PAT_deflate_m : forall s zc flush, DD s -> dcall_wf zc -> flush = Z_NO_FLUSH \/ flush = Z_FINISH ->
  PAT s -> PAT (fst (deflate_m s zc flush)).
Proof.
  intros s zc flush HDD Hzc HFL P. unfold deflate_m.
  set (c0 := cstrm_of_call zc).
  pose proof (C0OK'_of_call zc Hzc) as HC0. fold c0 in HC0.
  assert (H0 : DC c0 (set_strm s c0)) by (split; [apply DD_set_strm; exact HDD | subst c0; apply SV_entry; exact Hzc]).
  assert (E0 : ds_strm (set_strm s c0) = c0) by reflexivity.
  pose proof (PAT_set_strm s c0 P) as P0.
  set (s0 := set_strm s c0) in *. clearbody s0.
  pose proof (pat_core c0 s0 HC0 E0 (proj1 (proj1 H0)) flush (conj (conj H0 eq_refl) P0) HFL) as [_ PP].
  destruct (deflate_core s0 flush) as [s' rc]. cbn [fst] in PP |- *. exact PP.
Qed.

Lemma pow2_inj_small : forall a b, 0 <= a <= 16 -> 0 <= b <= 16 -> 2 ^ a = 2 ^ b -> a = b.
Proof.
  intros a b Ha Hb E. destruct (Z.lt_trichotomy a b) as [L|[L|L]]; [| exact L |].
  - pose proof (Z.pow_lt_mono_r 2 a b ltac:(lia) ltac:(lia) L). lia.
  - pose proof (Z.pow_lt_mono_r 2 b a ltac:(lia) ltac:(lia) L). lia.
Qed.
Lemma PAT_bits : forall s, dwf s -> PAT s -> ds_w_bits s = 15 /\ ds_hash_bits s = 15.
Proof.
  intros s D P. pose proof (df_wsize _ D) as E1. pose proof (df_lbs _ D) as E3.
  pose proof (df_wbits _ D) as Rw. pose proof (df_hbits _ D) as Rh.
  rewrite (pt_ws _ P) in E1. rewrite (pt_lbs _ P) in E3.
  split.
  - symmetry. apply pow2_inj_small; [lia | lia | exact E1].
  - assert (ds_hash_bits s - 1 = 14) by (symmetry; apply pow2_inj_small; [lia | lia | exact E3]). lia.
Qed.
