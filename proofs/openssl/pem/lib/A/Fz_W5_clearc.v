(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS Arr.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_libiface_pem D_defs D_agree D_clx PLayout Fz_kit Fz_ckit Fz_M_malloc Fz_M_free Fz_env Th_mutex Fz_W5_glx Fz_W5_icb Fz_W5_gsi Fz_W5_rep Fz_W5_gsi0 Fz_W5_clear Fz_W2_exdc Fz_W2_bnew Fz_W3_iface Fz_W5_env.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint flat2 (ws : list (word * word)) : list word := match ws with [] => [] | (a, b) :: ws' => a :: b :: flat2 ws' end.
Definition wkeep (w : word) (e : Z * Z) : bool := (bv_unsigned w =? 0) || negb (fst e =? bv_unsigned w).

Lemma filter_true : forall {A} (l : list A), List.filter (fun _ => true) l = l.
Proof. intros A l. induction l as [|x l IH]; cbn; [reflexivity| rewrite IH; reflexivity]. Qed.
Lemma filt_filt : forall {A} (f g : A -> bool) l, List.filter f (List.filter g l) = List.filter (fun e => g e && f e) l.
Proof. intros A f g l. induction l as [|x l IH]; cbn; [reflexivity|]. destruct (g x); cbn; [destruct (f x); cbn; rewrite IH; reflexivity| exact IH]. Qed.
Lemma filter_ext_in : forall {A} (f g : A -> bool) l, (forall e, In e l -> f e = g e) -> List.filter f l = List.filter g l.
Proof.
  intros A f g l H. induction l as [|x l IH]; cbn; [reflexivity|]. rewrite (H x ltac:(left; reflexivity)). rewrite (IH ltac:(intros e He; apply H; right; exact He)). reflexivity.
Qed.
Lemma live_remove_Lfilter : forall p l, live_remove p l = List.filter (fun e => negb (fst e =? p)) l.
Proof.
  intros p l. induction l as [|x l IH]; [reflexivity|]. unfold live_remove in *. cbn. rewrite <- IH. destruct (negb (fst x =? p)); cbn; reflexivity.
Qed.
Lemma rmw_filter : forall w l, rmw w l = List.filter (wkeep w) l.
Proof.
  intros w l. unfold rmw, wkeep. destruct (bv_unsigned w =? 0); [symmetry; apply filter_true| apply live_remove_Lfilter].
Qed.
Lemma clr_rm_filter : forall ws l, clr_rm ws l = List.filter (fun e => forallb (fun w => wkeep w e) (flat2 ws)) l.
Proof.
  induction ws as [|[wf wn] ws IH]; intros l; cbn [clr_rm flat2 forallb].
  - symmetry. apply filter_true.
  - rewrite IH, !rmw_filter, !filt_filt. apply filter_ext_in. intros e _. destruct (wkeep wf e), (wkeep wn e), (forallb (fun w => wkeep w e) (flat2 ws)); reflexivity.
Qed.
Lemma lra_filter : forall ps l, live_remove_all ps l = List.filter (fun e => forallb (fun p => negb (fst e =? p)) ps) l.
Proof.
  induction ps as [|p ps IH]; intros l; cbn [live_remove_all forallb].
  - symmetry. apply filter_true.
  - rewrite IH, live_remove_Lfilter, filt_filt. apply filter_ext_in. intros e _. destruct (negb (fst e =? p)), (forallb (fun p0 => negb (fst e =? p0)) ps); reflexivity.
Qed.
Lemma in_flat2_combine : forall (fs fn : list word) w, length fs = length fn ->
  In w (flat2 (combine fs fn)) <-> exists i, nth_error fs i = Some w \/ nth_error fn i = Some w.
Proof.
  induction fs as [|a fs IH]; intros [|b fn] w HL; cbn in HL; try discriminate; cbn [combine flat2 In].
  - split; [intros []| intros (i & [H|H]); destruct i; discriminate].
  - injection HL as HL. rewrite (IH fn w HL). split.
    + intros [<-|[<-|(i & Hi)]]; [exists 0%nat; left; reflexivity| exists 0%nat; right; reflexivity| exists (S i); cbn; exact Hi].
    + intros (i & Hi). destruct i as [|i]; cbn in Hi; [destruct Hi as [H|H]; injection H as ->; tauto| right; right; exists i; exact Hi].
Qed.

(* [comment removed for export] *)
Lemma clr_rm_strs : forall fs fn ks strs live, slots_ok fs fn ks strs -> length fs = 16%nat -> length fn = 16%nat ->
  (forall pn, In pn strs -> fst pn < 2 ^ 64) -> clr_rm (combine fs fn) live = live_remove_all (map fst strs) live.
Proof.
  intros fs fn ks strs live (ND & LEN & RNG & SL4 & NUL) LF LN BND. rewrite clr_rm_filter, lra_filter. apply filter_ext_in. intros e _.
  (* [comment removed for export] *)
  assert (SW : forall (i : nat) (b : bool) (w : word), (i < 16)%nat -> nth_error (if b then fn else fs) i = Some w -> bv_unsigned w = 0 \/ (bv_unsigned w <> 0 /\ In (bv_unsigned w) (map fst strs))).
  { intros i b w Hi Hw. destruct (in_dec (fun x y : Z * bool => ltac:(decide equality; [apply Bool.bool_dec | apply Z.eq_dec])) (Z.of_nat i, b) ks) as [IN|NI].
    - destruct (In_nth_error _ _ IN) as [j Hj].
      destruct (nth_error strs j) as [pn|] eqn:Hp; [| exfalso; apply nth_error_None in Hp; pose proof (nth_error_lt ks j _ Hj); lia].
      destruct (SL4 j _ pn Hj Hp) as (W1 & P0 & _). unfold slot_word in W1. cbn [fst snd] in W1. rewrite Nat2Z.id in W1. rewrite Hw in W1. injection W1 as ->.
      pose proof (BND pn (nth_error_In _ _ Hp)) as PB. rewrite unsigned_lit by lia. right. split; [lia|]. apply in_map_iff. exists pn. split; [reflexivity| exact (nth_error_In _ _ Hp)].
    - left. rewrite (NUL (Z.of_nat i, b) w ltac:(cbn; lia) ltac:(unfold slot_word; cbn [fst snd]; rewrite Nat2Z.id; exact Hw) NI). reflexivity. }
  (* [comment removed for export] *)
  assert (WS : forall p, In p (map fst strs) -> exists w, In w (flat2 (combine fs fn)) /\ bv_unsigned w = p /\ p <> 0).
  { intros p Hp. apply in_map_iff in Hp. destruct Hp as (pn & <- & Hpn). destruct (In_nth_error _ _ Hpn) as [j Hj].
    destruct (nth_error ks j) as [ik|] eqn:Hk; [| exfalso; apply nth_error_None in Hk; pose proof (nth_error_lt strs j _ Hj); lia].
    destruct (SL4 j ik pn Hk Hj) as (W1 & P0 & _). pose proof (BND pn Hpn) as PB. pose proof (RNG ik (nth_error_In _ _ Hk)) as RI.
    exists (Z_to_bv 64 (fst pn)). rewrite unsigned_lit by lia. split; [| split; [reflexivity| lia]].
    apply (in_flat2_combine fs fn _ ltac:(rewrite LF, LN; reflexivity)). exists (Z.to_nat (fst ik)). unfold slot_word in W1.
    destruct (snd ik); [right| left]; exact W1. }
  match goal with |- ?l = ?r => destruct l eqn:EL; destruct r eqn:ER; [reflexivity| exfalso| exfalso| reflexivity] end.
  - (* [comment removed for export] *)
    assert (HP : exists p, In p (map fst strs) /\ fst e = p).
    { clear - ER. induction (map fst strs) as [|p ps IH]; cbn in ER; [discriminate|].
      destruct (fst e =? p) eqn:E1; cbn in ER; [exists p; split; [left; reflexivity| lia]|].
      destruct (IH ER) as (q & Hq & Eq). exists q. split; [right; exact Hq| exact Eq]. }
    destruct HP as (p & Hp & Ep). destruct (WS p Hp) as (w & Hw & Ew & Pz).
    pose proof (proj1 (forallb_forall _ _) EL w Hw) as K. unfold wkeep in K. rewrite Ew in K. apply Bool.orb_true_iff in K.
    destruct K as [K|K]; [lia|]. apply Bool.negb_true_iff in K. lia.
  - (* [comment removed for export] *)
    assert (HW : exists w, In w (flat2 (combine fs fn)) /\ wkeep w e = false).
    { clear - EL. induction (flat2 (combine fs fn)) as [|w ws IH]; cbn in EL; [discriminate|].
      destruct (wkeep w e) eqn:E1; cbn in EL; [| exists w; split; [left; reflexivity| exact E1]].
      destruct (IH EL) as (q & Hq & Eq). exists q. split; [right; exact Hq| exact Eq]. }
    destruct HW as (w & Hw & Kw). unfold wkeep in Kw. apply Bool.orb_false_iff in Kw. destruct Kw as [K1 K2]. apply Bool.negb_false_iff in K2.
    apply (in_flat2_combine fs fn w ltac:(rewrite LF, LN; reflexivity)) in Hw. destruct Hw as (i & Hi).
    assert (Hi16 : (i < 16)%nat) by (destruct Hi as [H|H]; apply nth_error_lt in H; lia).
    assert (X : bv_unsigned w = 0 \/ (bv_unsigned w <> 0 /\ In (bv_unsigned w) (map fst strs))) by (destruct Hi as [H|H]; [exact (SW i false w Hi16 H)| exact (SW i true w Hi16 H)]).
    destruct X as [X|[_ X]]; [lia|].
    pose proof (proj1 (forallb_forall _ _) ER (bv_unsigned w) X) as K. apply Bool.negb_true_iff in K. lia.
Qed.

Lemma live_remove_all_keep : forall ps (l : list (Z * Z)) e, In e l -> ~ In (fst e) ps -> In e (live_remove_all ps l).
Proof.
  induction ps as [|p ps IH]; intros l e He Hn; cbn [live_remove_all]; [exact He|].
  apply live_remove_keep; [apply IH; [exact He| intros X; apply Hn; right; exact X]| intros X; apply Hn; left; symmetry; exact X].
Qed.

(* [comment removed for export] *)
Lemma slots_ok_pos : forall fs fn ks strs pn, slots_ok fs fn ks strs -> In pn strs -> 0 < fst pn /\ 0 < snd pn.
Proof.
  intros fs fn ks strs pn (ND & LEN & RNG & SL4 & NUL) Hpn. destruct (In_nth_error _ _ Hpn) as [j Hj].
  destruct (nth_error ks j) as [ik|] eqn:Hk; [| exfalso; apply nth_error_None in Hk; pose proof (nth_error_lt strs j _ Hj); lia].
  destruct (SL4 j ik pn Hk Hj) as (_ & P0 & P1). exact (conj P0 P1).
Qed.

(* [comment removed for export] *)
Lemma slots_free_ok : forall fs fn ks strs live bad, slots_ok fs fn ks strs ->
  (forall pn, In pn strs -> fst pn < 2 ^ 64 /\ In pn live /\ ~ In (fst pn) bad) ->
  forall b j w, 0 <= j < 16 -> selw fs fn b j = Some w -> slot_free_ok live bad w.
Proof.
  intros fs fn ks strs live bad (ND & LEN & RNG & SL4 & NUL) BND b j w Hj Hw.
  destruct (in_dec (fun x y : Z * bool => ltac:(decide equality; [apply Bool.bool_dec | apply Z.eq_dec])) (j, b) ks) as [IN|NI].
  - destruct (In_nth_error _ _ IN) as [i Hi].
    destruct (nth_error strs i) as [pn|] eqn:Hp; [| exfalso; apply nth_error_None in Hp; pose proof (nth_error_lt ks i _ Hi); lia].
    destruct (SL4 i _ pn Hi Hp) as (W1 & P0 & _). unfold slot_word in W1. cbn [fst snd] in W1. unfold selw in Hw. rewrite Hw in W1. injection W1 as ->.
    destruct (BND pn (nth_error_In _ _ Hp)) as (PB & INL & NB). unfold slot_free_ok. rewrite unsigned_lit by lia. right. split; [| exact NB]. exists (snd pn). destruct pn; exact INL.
  - left. rewrite (NUL (j, b) w ltac:(cbn; lia) ltac:(unfold slot_word; cbn [fst snd]; unfold selw in Hw; exact Hw) NI). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma slots_distinct : forall fs fn ks strs, slots_ok fs fn ks strs -> List.NoDup (map fst strs) -> (forall pn, In pn strs -> fst pn < 2 ^ 64) ->
  forall b1 j1 w1 b2 j2 w2, 0 <= j1 < 16 -> 0 <= j2 < 16 -> (b1, j1) <> (b2, j2) -> selw fs fn b1 j1 = Some w1 -> selw fs fn b2 j2 = Some w2 ->
  bv_unsigned w1 <> 0 -> bv_unsigned w1 <> bv_unsigned w2.
Proof.
  intros fs fn ks strs (ND & LEN & RNG & SL4 & NUL) NDS BND b1 j1 w1 b2 j2 w2 H1 H2 NE Hw1 Hw2 NZ.
  destruct (in_dec (fun x y : Z * bool => ltac:(decide equality; [apply Bool.bool_dec | apply Z.eq_dec])) (j1, b1) ks) as [IN1|NI1].
  2: { exfalso. apply NZ. rewrite (NUL (j1, b1) w1 ltac:(cbn; lia) ltac:(unfold slot_word; cbn [fst snd]; unfold selw in Hw1; exact Hw1) NI1). reflexivity. }
  destruct (In_nth_error _ _ IN1) as [i1 Hi1].
  destruct (nth_error strs i1) as [pn1|] eqn:Hp1; [| exfalso; apply nth_error_None in Hp1; pose proof (nth_error_lt ks i1 _ Hi1); lia].
  destruct (SL4 i1 _ pn1 Hi1 Hp1) as (W1 & P1 & _). unfold slot_word in W1. cbn [fst snd] in W1. unfold selw in Hw1. rewrite Hw1 in W1. injection W1 as ->.
  pose proof (BND pn1 (nth_error_In _ _ Hp1)) as B1. rewrite unsigned_lit by lia.
  destruct (in_dec (fun x y : Z * bool => ltac:(decide equality; [apply Bool.bool_dec | apply Z.eq_dec])) (j2, b2) ks) as [IN2|NI2].
  2: { rewrite (NUL (j2, b2) w2 ltac:(cbn; lia) ltac:(unfold slot_word; cbn [fst snd]; unfold selw in Hw2; exact Hw2) NI2). change (bv_unsigned (Z_to_bv 64 0)) with 0. lia. }
  destruct (In_nth_error _ _ IN2) as [i2 Hi2].
  destruct (nth_error strs i2) as [pn2|] eqn:Hp2; [| exfalso; apply nth_error_None in Hp2; pose proof (nth_error_lt ks i2 _ Hi2); lia].
  destruct (SL4 i2 _ pn2 Hi2 Hp2) as (W2 & P2 & _). unfold slot_word in W2. cbn [fst snd] in W2. unfold selw in Hw2. rewrite Hw2 in W2. injection W2 as ->.
  pose proof (BND pn2 (nth_error_In _ _ Hp2)) as B2. rewrite unsigned_lit by lia.
  assert (NI : i1 <> i2) by (intros ->; rewrite Hi1 in Hi2; injection Hi2 as E1 E2; apply NE; subst; reflexivity).
  intros EQ. apply NI. rewrite List.NoDup_nth_error in NDS. apply NDS; [rewrite length_map; exact (nth_error_lt strs i1 _ Hp1)|].
  rewrite !nth_error_map, Hp1, Hp2. cbn. rewrite EQ. reflexivity.
Qed.

Section CClrA.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_CLR : Fz_W5_clear.err_clear_error_stmt RT.
Variables FZ_SITES FZ_CALLS : list (Z * Z).
Hypothesis HCG_C : cg_sub CLR_SITES CLR_CALLS FZ_SITES FZ_CALLS.

Theorem err_clear_steady_proof : Fz_W3_iface.err_clear_steady_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer canary LBL E top bot strs
         FDO MST Htp LE INCL INE INS HNL NDS EL ART0 MI0 CALL HSTK CLE CTX UWC CGH HFR HCR.
  intros T c HA Hk.
  destruct LE as (od & e & k & MK & SA & NODES & LV & pad & tw & ne & kd & LK & ELBL & ENV & AL1 & AL2 & AL3 & AL4 & XS & LKC & APT).
  destruct EL as (bot' & fl & mk & buf & fs & ls & fn & ks & ES & SL & HB).
  pose proof ES as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LFS & _ & _ & _ & LFN & _).
  assert (BLK : err_blocks (rt_live RT Σ) MK SA NODES E).
  { split; [apply INCL; rewrite ELBL; cbn; tauto|]. split; [apply INCL; rewrite ELBL; cbn; tauto|]. split; [apply INCL; rewrite ELBL; cbn; tauto|].
    split; [exact INE|]. exact (conj AL1 (conj AL2 (conj AL3 AL4))). }
  pose proof (afp_live_hi RT GOBJ AFP Σ m E 904 ART0 INE ltac:(lia)) as EHI.
  assert (INLK : In (LK, 40) (rt_live RT Σ)) by (apply INCL; rewrite ELBL; cbn; tauto).
  pose proof (live_in_disj RT AF Σ m LK 40 E 904 ART0 INLK INE ltac:(intros X; injection X; lia)) as APLE.
  (* [comment removed for export] *)
  assert (APART : forall pn q nq, In pn strs -> In (q, nq) (rt_live RT Σ) -> 0 < nq -> pn <> (q, nq) -> fst pn <> q).
  { intros pn q nq Hpn Hq NQ NE EQ. destruct pn as (p, n). cbn [fst] in EQ. subst p.
    pose proof (slots_ok_pos fs fn ks strs _ SL Hpn) as [_ N0]. cbn [snd] in N0.
    destruct (live_in_disj RT AF Σ m q n q nq ART0 (INS _ Hpn) Hq NE); lia. }
  assert (BND : forall pn, In pn strs -> fst pn < 2 ^ 64 /\ In pn (rt_live RT Σ) /\ ~ In (fst pn) (ERRBAD MK SA NODES E)).
  { intros pn Hpn. pose proof (INS _ Hpn) as INP. destruct (HNL _ Hpn) as [NL NEE].
    pose proof (af_live_range RT AF Σ m (fst pn) (snd pn) ART0 ltac:(destruct pn; exact INP)) as (_ & R1 & _). pose proof (af_sp0_range RT AF Σ m ART0) as SR.
    pose proof (slots_ok_pos fs fn ks strs _ SL Hpn) as [_ N0].
    split; [unfold USTACK_TOP, STACK_WIN in *; clear - R1 SR N0; lia|]. split; [exact INP|].
    unfold ERRBAD. intros [X|[X|[X|[X|[]]]]]; symmetry in X.
    - exact (APART pn E 904 Hpn INE ltac:(lia) NEE X).
    - refine (APART pn MK 72 Hpn ltac:(apply INCL; rewrite ELBL; cbn; tauto) ltac:(lia) _ X). intros ->. apply NL. rewrite ELBL. cbn. tauto.
    - refine (APART pn SA 32 Hpn ltac:(apply INCL; rewrite ELBL; cbn; tauto) ltac:(lia) _ X). intros ->. apply NL. rewrite ELBL. cbn. tauto.
    - refine (APART pn NODES 128 Hpn ltac:(apply INCL; rewrite ELBL; cbn; tauto) ltac:(lia) _ X). intros ->. apply NL. rewrite ELBL. cbn. tauto. }
  assert (BND1 : forall pn, In pn strs -> fst pn < 2 ^ 64) by (intros pn Hpn; exact (proj1 (BND pn Hpn))).
  apply (C_CLR Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer od e k MK SA NODES E LV pad tw ne top bot'
           fl mk buf fs ls fn (Z_to_bv 8 1) canary FDO MST Htp ART0 MI0 CALL ltac:(clear - HSTK; unfold ERRC_STACK in *; lia) CTX UWC (cg_has_of_sub _ _ _ _ _ CGH HCG_C) HFR HCR
           ENV BLK ES (slots_free_ok fs fn ks strs _ _ SL BND) (slots_distinct fs fn ks strs SL NDS BND1) CLE T c HA).
  intros c' (Σ' & v & fl' & mk' & buf' & ls' & AST & LV' & BLK' & FRS' & SP' & CR' & CG').
  rewrite (clr_rm_strs fs fn ks strs _ SL LFS LFN BND1) in LV'.
  apply Hk. exists Σ'. split; [| split; [exact LV'|]; split; [exact FRS'|]; split; [exact SP'|]; split; [clear - CR'; lia| exact CG']].
  unfold apost. eapply ASTA_conseq; [exact AST|]. cbv beta. intros ms (m' & RS & (ART1 & MI1 & ST1) & PRES & ENV' & ES' & CLE'). exists v, m'.
  split; [exact RS|]. split; [exact (conj ART1 (conj MI1 ST1))|]. rewrite LV' in PRES.
  assert (PR : forall a : word, aclient (live_remove_all (map fst strs) (rt_live RT Σ)) (rt_frames RT Σ) (bv_unsigned sp) (bv_unsigned a) ->
                 outside ((E, E + 904) :: lib_W LBL) (bv_unsigned a) -> m' a = m a).
  { intros a Ha Ho. apply PRES; [exact Ha|]. unfold CLR_W. cbn [outside] in *. clear - Ho. tauto. }
  split; [exact PR|]. split; [exact CLE'|].
  assert (PRS : forall a : word, client_static (bv_unsigned a) -> m' a = m a).
  { intros a Hs. apply PRES; [right; left; exact Hs|]. unfold CLR_W. cbn [outside]. pose proof Hs as [(l & h & Hin & Hx) _].
    unfold CLIENT_STATIC in Hin. cbn [In] in Hin. clear - Hin Hx EHI. repeat (destruct Hin as [EQ|Hin]; [injection EQ as <- <-; lia|]). destruct Hin. }
  assert (INLK' : In (LK, 40) (live_remove_all (map fst strs) (rt_live RT Σ))).
  { apply live_remove_all_keep; [exact INLK|]. cbn [fst]. intros X. apply in_map_iff in X. destruct X as (pn & EQ & Hpn).
    refine (APART pn LK 40 Hpn INLK ltac:(lia) _ EQ). intros ->. destruct (HNL _ Hpn) as [NL _]. apply NL. rewrite ELBL. cbn. tauto. }
  split.
  - exists od, e, k, MK, SA, NODES, LV, pad, tw, ne, kd, LK. split; [exact ELBL|]. split; [exact ENV'|]. split; [exact AL1|]. split; [exact AL2|]. split; [exact AL3|]. split; [exact AL4|].
    pose proof XS as (_ & _ & KD & _).
    split; [apply (exd_stat_agree m m' kd LK XS); intros a Ha; apply PRS; exact (exd_fp_static kd _ KD Ha)|].
    split; [| exact APT].
    apply (rw_cells_agree_nw asegs m m' _ _ LKC). intros a Ha. cbv beta in Ha. unfold mutex_cells in Ha. cbn [cells_size csize Nat.add] in Ha.
    apply PRES; [apply (acl_live _ _ _ LK 40); [exact INLK'| clear - Ha; lia]|]. unfold CLR_W. cbn [outside]. clear - Ha APLE. lia.
  - split; [reflexivity|]. exists fl', mk', buf', ls'. exact ES'.
Qed.
End CClrA.
