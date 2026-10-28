(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun KStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_T_ekit Fz_W1_defs Fz_W1_growc Fz_W3_iface Fz_W2_rep Fz_W3_defs Fz_W3_lems.
     From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_W7_perm. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_W7_defs Fz_W7_f.
Import ListNotations.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation wz := (Z_to_bv 64) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma grow_n_le43 : forall x, 0 <= x -> 0 <= grow_n x /\ 3 * grow_n x <= 4 * x + 12.
Proof. intros x Hx. unfold grow_n. pose proof (Z.div_mod (x + 3) 3 ltac:(lia)). pose proof (Z.mod_pos_bound (x + 3) 3 ltac:(lia)). nia. Qed.

Lemma cnt_mbk_ents : forall K max, 0 <= max ->
  cntA (mbk_ents K max) <= 5 /\ cntB (mbk_ents K max) <= 1 /\ bigsum (mbk_ents K max) <= max + 8192
  /\ 0 <= cntA (mbk_ents K max) /\ 0 <= cntB (mbk_ents K max) /\ 0 <= bigsum (mbk_ents K max).
Proof.
  intros K max H. unfold mbk_ents. rewrite cntA_app, cntB_app, bigsum_app.
  rewrite !cntA_cons, !cntB_cons, !bigsum_cons, cntA_nil, cntB_nil, bigsum_nil. unfold TIER_A_MAX. cbn [snd Z.leb Z.ltb Z.compare Pos.compare Pos.compare_cont].
  destruct (k_d K) as [d|].
  - rewrite !cntA_cons, !cntB_cons, !bigsum_cons, cntA_nil, cntB_nil, bigsum_nil. cbn [snd]. unfold TIER_A_MAX.
    destruct (Z.leb_spec max 236); destruct (Z.ltb_spec 236 max); lia.
  - rewrite cntA_nil, cntB_nil, bigsum_nil. lia.
Qed.

(* [comment removed for export] *)
Lemma cnt_bents : forall bs, cntA (bents bs) + cntB (bents bs) = Z.of_nat (length bs) /\ 0 <= cntA (bents bs) /\ 0 <= cntB (bents bs)
  /\ (Forall (fun b => 0 <= blk_size b) bs -> 0 <= bigsum (bents bs) <= news_sz bs + 8192 * Z.of_nat (length bs)).
Proof.
  induction bs as [|b bs IH]; [cbn [bents map length news_sz fold_right]; rewrite cntA_nil, cntB_nil, bigsum_nil; repeat split; try lia; intros _; lia|]. cbn [bents map length]. fold (bents bs). rewrite cntA_cons, cntB_cons, bigsum_cons. unfold news_sz. cbn [fold_right snd]. fold (news_sz bs).
  rewrite Nat2Z.inj_succ. destruct IH as (I1 & I2 & I3 & I4). unfold TIER_A_MAX.
  destruct (Z.leb_spec (blk_size b) 236); destruct (Z.ltb_spec 236 (blk_size b)); try lia.
  - split; [lia|]. split; [lia|]. split; [lia|]. intros HF. inversion HF; subst. specialize (I4 ltac:(assumption)). lia.
  - split; [lia|]. split; [lia|]. split; [lia|]. intros HF. inversion HF; subst. specialize (I4 ltac:(assumption)). lia.
Qed.
Lemma bents_small : forall bs, Forall (fun b => blk_size b <= 64) bs -> cntB (bents bs) = 0 /\ bigsum (bents bs) = 0.
Proof.
  induction bs as [|b bs IH]; intros HF; [split; reflexivity|]. inversion HF; subst. cbn [bents map]. fold (bents bs). rewrite cntB_cons, bigsum_cons.
  destruct (IH ltac:(assumption)) as [I1 I2]. unfold TIER_A_MAX. cbn [snd]. destruct (Z.ltb_spec 236 (blk_size b)); lia.
Qed.

(* [comment removed for export] *)
Lemma cnt_of_perm : forall (Lc ADD L : @clist bptr), Permutation Lc (ADD ++ L) ->
  cntA Lc = cntA ADD + cntA L /\ cntB Lc = cntB ADD + cntB L /\ bigsum Lc = bigsum ADD + bigsum L.
Proof. intros Lc ADD L P. rewrite (cntA_perm _ _ P), (cntB_perm _ _ P), (bigsum_perm _ _ P), cntA_app, cntB_app, bigsum_app. auto. Qed.

Lemma w_pe_in_gen : forall en q, In q (map blk_id (w_CLB en)) -> In q (map blk_id (w_LBall en)).
Proof. intros en q H. unfold w_LBall. rewrite map_app. apply in_or_app. left. exact H. Qed.
Lemma bptr_eq_dec : forall p q : bptr, p = q \/ p <> q.
Proof.
  intros [a b] [c d]. destruct (aptr_eqb a c) eqn:E1; [apply KStep.aptr_eqb_eq in E1; subst c| right; intros X; inversion X; subst; rewrite (proj2 (KStep.aptr_eqb_eq c c) eq_refl) in E1; discriminate].
  destruct (Z.eq_dec b d) as [->|NE]; [left; reflexivity| right; intros X; inversion X; exact (NE ltac:(assumption))].
Qed.

Section W7. Context {CE__ : Ceiling} {RN__ : RunRnd}.
  Variable libenv : mem -> list block -> Z -> Prop.
  Variable libenv_fp : list block -> Z -> Prop.
  Hypothesis libenv_agree : forall m m' LBL E, libenv m LBL E -> agree_on (libenv_fp LBL) m m' -> libenv m' LBL E.
  Hypothesis libenv_fp_where : forall LBL a, libenv_fp LBL a ->
    (0x2c0000 <= a < 0x353000 /\ ~ ralloc_static a /\ a <> LX_FLAGS) \/ (exists b, In b LBL /\ blk_addr b <= a < blk_addr b + blk_size b).
  Variable errst_at_rest : Z -> list block -> mem -> Prop.
  Variable errst_live : Z -> Z -> Z -> list block -> mem -> Prop.
  Variable errst_fp : Z -> list block -> Z -> Prop.
  Hypothesis errst_rest_agree : forall m m' E strs, errst_at_rest E strs m -> agree_on (errst_fp E strs) m m' -> errst_at_rest E strs m'.
  Hypothesis errst_live_agree : forall m m' E top bot strs, errst_live E top bot strs m -> agree_on (errst_fp E strs) m m' -> errst_live E top bot strs m'.
  Hypothesis errst_fp_where : forall E strs a, errst_fp E strs a -> (E <= a < E + 904) \/ (exists b, In b strs /\ blk_addr b <= a < blk_addr b + blk_size b).
  Hypothesis errst_rest_live : forall m E, errst_at_rest E [] m -> errst_live E 0 0 [] m.
  Local Notation f7_invI := (f7_inv libenv errst_live).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma w7_write_step : forall en st LBc Lc mc K BI len max off top bot strs news st1 LB1 L1 m1 n v,
    f7_invI en st LBc Lc mc K BI len max off top bot strs news ->
    cstate st1 LB1 (w_LB en) L1 m1 (wz (w_SP en + -64)) (w_tp en) (w_lo en) (w_B en) ->
    cframe (mbio_T K) [] (w_SP en + -64) st LBc Lc mc st1 LB1 L1 m1 ->
    bio_puts_res K BI M_MEM (len - off) max n LBc Lc v LB1 L1 m1 ->
    exists pd' max', (max' = max \/ max' = grow_n (len - off + n)) /\ len - off + n <= max'
      /\ f7_invI en st1 LB1 L1 m1 (mbk_data K pd') BI (len - off + n) max' 0 top bot strs news.
  Proof.
    intros en st LBc Lc mc K BI len max off top bot strs news st1 LB1 L1 m1 n v
           (COM & MB & LIVE & LEN2 & SIN & SL & NWS & KFR & KL & KS & NDSN & SFR & SLBL) CST1 FRM1 (pd' & max' & _ & HMAX & HFIT & MB1 & KB & KLc & NB & NL & PLS).
    pose proof COM as (CST & FR0 & LE & INCL0 & INCL & NPL & INE & INL & PERM & SAVED & SLO & SPB & B63 & AL16 & EPE & ROOM & PAY & DLEN & NDE & REL).
    pose proof FRM1 as (CFR1 & KP1 & _).
    pose proof (cstate_nodup _ _ _ _ _ _ _ _ _ CST) as [NDB NDL]. pose proof (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [NDB1 NDL1].
    assert (NKE : ~ mbio_T K (w_pe en)) by (apply KFR; left; exact (w_pe_in _ EPE)).
    assert (KDE : forall q, k_d K = Some q -> mbio_T K q) by (intros q Hq; unfold mbio_T; do 4 right; exact Hq).
    exists pd', max'. split; [exact HMAX|]. split; [exact HFIT|].
    (* [comment removed for export] *)
    assert (KBx : forall b, In b LBc -> ~ mbio_T K (blk_id b) -> In b LB1) by (intros b Hb NT; apply KB; [exact Hb| intros X; exact (NT (KDE _ X))]).
    assert (KLx : forall q nm, In (q, nm) Lc -> ~ mbio_T K q -> In (q, nm) L1) by (intros q nm Hq NT; apply KLc; [exact Hq| intros X; exact (NT (KDE _ X))]).
    (* [comment removed for export] *)
    assert (FRESH : forall q, pd' = Some q -> forall b, In b LBc -> ~ mbio_T K (blk_id b) -> blk_id b <> q).
    { intros q Hq b Hb NT E. destruct b as [[p A] nb]. cbn [blk_id fst] in E, NT. subst p.
      destruct PLS as [(P1 & _ & _ & _)|[(q' & D' & P1 & _ & -> & _)|(q' & D' & d & i & nm & P1 & P2 & -> & _)]].
      - apply NT. apply KDE. rewrite <- P1. exact Hq.
      - rewrite P1 in Hq. inversion Hq; subst q'. exact (cstate_head_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 Hb eq_refl).
      - rewrite P1 in Hq. inversion Hq; subst q'. refine (cstate_head_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 _ eq_refl).
        apply lb_remove_In. split; [exact Hb|]. cbn [blk_id fst]. intros ->. apply NT. apply KDE. exact P2. }
    assert (KDE' : forall q, mbio_T (mbk_data K pd') q <-> (q = k_bi K \/ q = k_bb K \/ q = k_bm K \/ q = k_rp K) \/ pd' = Some q).
    { intros q. unfold mbio_T. cbn [k_bi k_bb k_bm k_rp k_d mbk_data]. tauto. }
    assert (TK4 : forall q, (q = k_bi K \/ q = k_bb K \/ q = k_bm K \/ q = k_rp K) -> mbio_T K q) by (intros q Hq; unfold mbio_T; tauto).
    (* [comment removed for export] *)
    assert (PERM1 : Permutation L1 ((mbk_ents (mbk_data K pd') max' ++ bents strs ++ bents news) ++ w_L en)).
    { unfold mbk_ents in PERM |- *. cbn [k_bi k_bb k_bm k_rp k_d mbk_data].
      destruct PLS as [(P1 & -> & -> & ->)|[(q & D' & -> & P2 & -> & ->)|(q & D' & d & i & nm & -> & P2 & -> & P4 & ->)]].
      - rewrite P1. exact PERM.
      - rewrite P2 in PERM. rewrite app_nil_r in PERM. rewrite <- !app_assoc. cbn [app]. rewrite <- !app_assoc in PERM. cbn [app] in PERM.
        eapply perm_trans; [apply perm_skip; exact PERM|].
        lazymatch goal with |- Permutation ((q, max') :: ?a :: ?b :: ?c :: ?e :: ?r) _ =>
          change (Permutation ((q, max') :: ([a; b; c; e] ++ r)) ([a; b; c; e] ++ (q, max') :: r)) end. apply Permutation_middle.
      - rewrite P2 in PERM. rewrite <- !app_assoc in PERM. cbn [app] in PERM.
        assert (NM : nm = max).
        { apply (nodup_fst_eq Lc d); [exact NDL| apply (nth_error_In _ _ P4)|]. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. cbn [In]. tauto. }
        subst nm. rewrite <- !app_assoc. cbn [app].
        lazymatch type of PERM with Permutation _ (?a :: ?b :: ?c :: ?e :: (d, max) :: ?r) =>
          pose proof (perm_replace_one Lc i (d, max) (q, max') [a; b; c; e] [] r ltac:(cbn [app]; exact PERM) P4) as X end.
        eapply perm_trans; [exact X|]. cbn [app].
        lazymatch goal with |- Permutation ((q, max') :: ?a :: ?b :: ?c :: ?e :: ?r) _ =>
          change (Permutation ((q, max') :: ([a; b; c; e] ++ r)) ([a; b; c; e] ++ (q, max') :: r)) end. apply Permutation_middle. }
    refine (conj _ (conj MB1 (conj _ (conj LEN2 (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj NDSN (conj SFR SLBL)))))))))))).
    - eapply (com7_call libenv); [exact COM| exact CST1| exact FRM1| intros q Hq _; exact (KFR q Hq)| exact KL| | | | | exact PERM1].
      + eapply (libenv_cfr libenv libenv_fp libenv_agree libenv_fp_where); [exact LE| exact CFR1| exact INCL| exact KL].
      + apply KBx; [exact INE| exact NKE].
      + apply KLx; [exact INL| exact NKE].
      + intros b Hb. apply KBx; [exact (INCL _ Hb)| exact (KL _ Hb)].
    - eapply errst_live_agree; [exact LIVE|]. eapply agree_on_mono; [exact CFR1|]. cbv beta. intros a Ha. right; left.
      destruct (errst_fp_where _ _ _ Ha) as [Ra|(b' & Hb' & Rb')].
      + exists (w_pe en, w_E en, 904). split; [exact INE|]. split; [exact NKE| unfold blk_addr, blk_size; cbn [fst snd]; exact Ra].
      + exists b'. split; [exact (proj1 (Forall_forall _ _) SIN b' Hb')|]. split; [exact (KS b' ltac:(apply in_or_app; left; exact Hb'))| exact Rb'].
    - apply Forall_forall. intros b Hb. apply KBx; [exact (proj1 (Forall_forall _ _) SIN b Hb)| exact (KS b ltac:(apply in_or_app; left; exact Hb))].
    - eapply strs_inL_keep; [exact SL| intros q nm Hq NX; exact (KLx q nm Hq NX)| intros b Hb; exact (KS b ltac:(apply in_or_app; left; exact Hb))].
    - apply Forall_forall. intros b Hb. pose proof (proj1 (Forall_forall _ _) NWS b Hb) as [H1 H2]. pose proof (KS b ltac:(apply in_or_app; right; exact Hb)) as NT.
      split; [exact (KBx _ H1 NT)| exact (KLx _ _ H2 NT)].
    - (* [comment removed for export] *)
      intros q Hq X. apply KDE' in X. destruct X as [X|X]; [exact (KFR q Hq (TK4 _ X))|].
      pose proof FR0 as (_ & [KB0 _] & _). change (map blk_ptr (w_CLB en)) with (map blk_id (w_CLB en)) in REL.
      assert (Hq' : In q (map blk_id (w_LBall en))) by (destruct Hq as [Hq|Hq]; [exact Hq| apply w_pe_in_gen; rewrite REL; exact Hq]).
      apply in_map_iff in Hq'. destruct Hq' as (b0 & Eb & Hb0).
      destruct (bptr_eq_dec q (w_pe en)) as [->|NE].
      + exact (FRESH _ X (w_pe en, w_E en, 904) INE NKE eq_refl).
      + refine (FRESH _ X b0 (KB0 _ Hb0 _) _ Eb); [rewrite Eb; intros E; exact (NE (eq_sym E))| rewrite Eb; exact (KFR q Hq)].
    - intros b Hb X. apply KDE' in X. destruct X as [X|X]; [exact (KL b Hb (TK4 _ X))| exact (FRESH _ X b (INCL _ Hb) (KL _ Hb) eq_refl)].
    - intros b Hb X. apply KDE' in X. destruct X as [X|X]; [exact (KS b Hb (TK4 _ X))|].
      assert (HbL : In b LBc).
      { apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [exact (proj1 (Forall_forall _ _) SIN b Hb)| exact (proj1 (proj1 (Forall_forall _ _) NWS b Hb))]. }
      exact (FRESH _ X b HbL (KS _ Hb) eq_refl).
  Qed.
End W7.
