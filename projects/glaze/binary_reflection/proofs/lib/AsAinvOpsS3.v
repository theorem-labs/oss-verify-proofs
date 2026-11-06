(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= am_lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma seps_In : forall x l y, seps x l -> In y l -> snd x <= fst y \/ snd y <= fst x.
Proof. intros x l; induction l as [|z t IH]; intros y Hs Hy; [destruct Hy|]. destruct Hs as [H1 H2]. destruct Hy as [<-|Hy]; [exact H1 | exact (IH y H2 Hy)]. Qed.

Lemma splits_of_PW : forall l : list (Z * Z), PW l ->
  forall l1 l2 lo hi lo' hi', l = l1 ++ (lo, hi) :: l2 -> In (lo', hi') (l1 ++ l2) -> hi <= lo' \/ hi' <= lo.
Proof.
  induction l as [|z t IH]; intros HP l1 l2 lo hi lo' hi' E Hy.
  - destruct l1; discriminate E.
  - destruct HP as [Hz Ht]. destruct l1 as [|w l1'].
    + cbn in E. injection E as -> ->. cbn in Hy. exact (seps_In _ _ _ Hz Hy).
    + cbn in E. injection E as -> E'. destruct Hy as [E2|Hy].
      * subst w. pose proof (seps_In (lo', hi') t (lo, hi) Hz ltac:(rewrite E'; apply in_app_iff; right; left; reflexivity)) as X. cbn in X. lia.
      * exact (IH Ht l1' l2 lo hi lo' hi' E' Hy).
Qed.

Lemma seps_insert : forall y t l2 x, seps y (t ++ l2) -> (snd y <= fst x \/ snd x <= fst y) -> seps y (t ++ x :: l2).
Proof.
  intros y t l2 x Hs Hx. apply seps_of_forall. intros w Hw. apply in_app_iff in Hw. destruct Hw as [Hw | [<- | Hw]].
  - exact (seps_In _ _ _ Hs ltac:(apply in_app_iff; left; exact Hw)).
  - exact Hx.
  - exact (seps_In _ _ _ Hs ltac:(apply in_app_iff; right; exact Hw)).
Qed.

Lemma PW_insert : forall (l1 l2 : list (Z * Z)) x,
  PW (l1 ++ l2) -> (forall y, In y (l1 ++ l2) -> snd x <= fst y \/ snd y <= fst x) -> PW (l1 ++ x :: l2).
Proof.
  induction l1 as [|y t IH]; intros l2 x P AP.
  - cbn in *. split; [apply seps_of_forall; exact AP | exact P].
  - cbn in P |- *. destruct P as [Sy Pt]. split.
    + apply seps_insert; [exact Sy|]. destruct (AP y ltac:(left; reflexivity)); lia.
    + apply IH; [exact Pt|]. intros w Hw. apply AP. right. exact Hw.
Qed.

Lemma splits_insert : forall (l1 l2 : list (Z * Z)) (x : Z * Z),
  (forall m1 m2 lo hi lo' hi', l1 ++ l2 = m1 ++ (lo, hi) :: m2 -> In (lo', hi') (m1 ++ m2) -> hi <= lo' \/ hi' <= lo) ->
  (forall lo' hi', In (lo', hi') (l1 ++ l2) -> snd x <= lo' \/ hi' <= fst x) ->
  forall m1 m2 lo hi lo' hi', l1 ++ x :: l2 = m1 ++ (lo, hi) :: m2 -> In (lo', hi') (m1 ++ m2) -> hi <= lo' \/ hi' <= lo.
Proof.
  intros l1 l2 x DJ AP. apply splits_of_PW. apply PW_insert.
  - apply PW_of_splits. intros m1 [xlo xhi] m2 [ylo yhi] E Hy. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). exact (DJ m1 m2 xlo xhi ylo yhi E Hy).
  - intros [ylo yhi] Hy. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). exact (AP ylo yhi Hy).
Qed.

Lemma perm_insert_mid : forall (A : Type) (x : A) (l0 l1 l2 : list A),
  Permutation (x :: l0 ++ (l1 ++ l2)) (l0 ++ ((l1 ++ [x]) ++ l2)).
Proof.
  intros A x l0 l1 l2. rewrite <- (app_assoc l1 [x] l2). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end).
  rewrite (app_assoc l0 l1 (x :: l2)). rewrite (app_assoc l0 l1 l2). apply Permutation_middle.
Qed.

(* [comment removed for export] *)
Lemma secsum_app2 : forall l x,
  fold_right (fun s acc => sc_mapsz s + sec_hull (sc_map s) (sc_n s) + acc) 0 (l ++ [x])
  = fold_right (fun s acc => sc_mapsz s + sec_hull (sc_map s) (sc_n s) + acc) 0 l + (sc_mapsz x + sec_hull (sc_map x) (sc_n x)).
Proof. induction l as [|y t IH]; intros x; cbn -[sec_hull sc_mapsz]; [lia | rewrite IH; lia]. Qed.

Lemma NoDup_app_single : forall {A} (l : list A) (x : A), List.NoDup l -> ~ In x l -> List.NoDup (l ++ [x]).
Proof.
  intros A l x ND NI. induction l as [|y t IH]; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end).
  - constructor; [intros [] | constructor].
  - inversion ND as [| y' t' Hy Ht]; subst. constructor.
    + intros Hin. apply in_app_iff in Hin. destruct Hin as [Hin | [<- | []]]; [exact (Hy Hin) | exact (NI ltac:(left; reflexivity))].
    + apply IH; [exact Ht | intros Hin; exact (NI ltac:(right; exact Hin))].
Qed.

Section S.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.
  Ltac dsj := repeat match goal with H : _ \/ _ |- _ => destruct H end.
  Ltac Ztac := try ceil; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.
  Ltac Zlia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, T_PC, PC_SZ, T_QC, T_UNW, NMAX in *; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.
  Ltac uilia := unfold IB, DEPOT_TAB, DEPOT_NIDS, DEPOT_MAP1, SSOBJ, IA_FLAG, IA_INST, IASZ in *; ulia.


  (* [comment removed for export] *)
  Lemma fresh_vs_live : forall st Lc FF mp len, WF bt st Lc FF ->
    (forall lo hi, In (lo, hi) (all_ranges bt st) -> mp + len <= lo \/ hi <= mp) -> 0 <= len ->
    forall p n, In (p, n) Lc -> mp + len <= p - rz n \/ p + n <= mp.
  Proof using.
    intros st Lc FF mp len W DJ Hlen p n Hin.
    destruct (live_ext bt st Lc FF W p n Hin) as (lo & hi & EXT & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
    pose proof (up8_rounded n ltac:(lia)) as (U1 & U2 & U3). unfold up8 in *.
    assert (n <= (n + 7) / 8 * 8) by (clear - n; Z.div_mod_to_equations; lia).
    destruct EXT as [(HP & Elo & Ehi & CV & HC & LV & S1 & S2) | (HP & sc & Hs & Eu & En & Elo & Ehi)].
    - pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & PWS & IN6 & R6a & R6b & _) & _).
      destruct (DJ _ _ (all_ranges_fixed bt st _ IN6)). all: clear B11 B12; unfold KSPACE, PG in *; lia.
    - destruct (DJ _ _ (all_ranges_dyn bt st _ (sec_dyn st sc Hs))).
      all: destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8); clear B11 B12; unfold PG in *; lia.
  Qed.

  Lemma fresh_vs_quar : forall st Lc FF mp len, WF bt st Lc FF ->
    (forall lo hi, In (lo, hi) (all_ranges bt st) -> mp + len <= lo \/ hi <= mp) -> 0 <= len ->
    forall m n, In (m, n) (quar st) -> mp + len <= m \/ m + 16 + n <= mp.
  Proof using.
    intros st Lc FF mp len W DJ Hlen m n Hin.
    destruct (quar_item bt st Lc FF W m n Hin) as (N1 & [[HP CV] | [HP (sc & Hs & Eu & En)]]).
    - pose proof (prim_user_in_chunk n ltac:(lia) HP) as (U1 & U2). unfold blk_class in *.
      destruct (carved_range bt st Lc FF W _ _ U2 CV) as (C1 & C2 & C3 & C4 & C5). unfold prim_alloc_beg in *.
      pose proof (rounded_ge n) as (Q1 & _). pose proof (rz_range n).
      pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & PWS & IN6 & R6a & R6b & _) & _).
      destruct (DJ _ _ (all_ranges_fixed bt st _ IN6)); unfold needed, KSPACE, PG in *; lia.
    - destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
      destruct (DJ _ _ (all_ranges_dyn bt st _ (sec_dyn st sc Hs))); rewrite En in *; unfold PG in *; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma all_ranges_sec_alloc : forall st mp n grow,
    all_ranges bt (op_sec_alloc st mp n grow)
    = (bt_fixed bt ++ List.map (fun s => (sc_map s, sc_map s + sc_mapsz s)) (a_sec st))
      ++ (mp, mp + sec_map_size n) :: (List.map (fun b => (b, b + 2 ^ 20)) (dp_nodeblocks (a_dep st)) ++ List.map (fun b => (b, b + 2 ^ 23)) (dp_storeblocks (a_dep st))).
  Proof using.
    intros st mp n grow. (lazymatch goal with |- ?G => let G' := eval unfold all_ranges, dyn_ranges, op_sec_alloc in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_sec a_dep] in G in change_no_check G' end).
    rewrite map_app. (lazymatch goal with |- ?G => let G' := eval cbn [List.map] in G in change_no_check G' end). rewrite <- !app_assoc. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). reflexivity.
  Qed.
  Lemma all_ranges_old : forall st,
    all_ranges bt st = (bt_fixed bt ++ List.map (fun s => (sc_map s, sc_map s + sc_mapsz s)) (a_sec st))
      ++ (List.map (fun b => (b, b + 2 ^ 20)) (dp_nodeblocks (a_dep st)) ++ List.map (fun b => (b, b + 2 ^ 23)) (dp_storeblocks (a_dep st))).
  Proof using. intros st. (lazymatch goal with |- ?G => let G' := eval unfold all_ranges, dyn_ranges in G in change_no_check G' end). rewrite <- !app_assoc. reflexivity. Qed.
  Lemma in_all_ranges_sec_alloc : forall st mp n grow x,
    In x (all_ranges bt (op_sec_alloc st mp n grow)) <-> In x (all_ranges bt st) \/ (mp, mp + sec_map_size n) = x.
  Proof using.
    intros st mp n grow x. rewrite all_ranges_sec_alloc, all_ranges_old. rewrite !in_app_iff. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). rewrite !in_app_iff.
    am_tauto.
  Qed.




  (* [comment removed for export] *)
  Lemma registered_sec_alloc : forall st mp n0 grow p n, registered st p n -> registered (op_sec_alloc st mp n0 grow) p n.
  Proof using. intros st mp n0 grow p n (sc & Hs & E1 & E2). exists sc. split; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); apply in_app_iff; left; exact Hs | split; assumption]. Qed.
  Lemma wf_batch_sec_alloc : forall st mp n0 grow b, wf_batch bt st b -> wf_batch bt (op_sec_alloc st mp n0 grow) b.
  Proof using.
    intros st mp n0 grow b (B1 & B2 & B3). split; [exact B1|]. split; [exact B2|].
    intros m n Hin. destruct (B3 m n Hin) as (N1 & [[HP CV]|[HP RG]]); (split; [exact N1|]).
    - left. split; [exact HP | exact CV].
    - right. split; [exact HP | apply registered_sec_alloc; exact RG].
  Qed.
  Lemma wf_batch_sec_alloc0 : forall st mp n0 grow b, wf_batch0 bt st b -> wf_batch0 bt (op_sec_alloc st mp n0 grow) b.
  Proof using.
    intros st mp n0 grow b (B1 & B2 & B3). split; [exact B1|]. split; [exact B2|].
    intros m n Hin. destruct (B3 m n Hin) as (N1 & [[HP CV]|[HP RG]]); (split; [exact N1|]).
    - left. split; [exact HP | exact CV].
    - right. split; [exact HP | apply registered_sec_alloc; exact RG].
  Qed.

  Lemma mod16_of_pg : forall a b, a mod PG = 0 -> b mod 16 = 0 -> (a + PG + b) mod 16 = 0.
  Proof using. intros a b Ha Hb. unfold PG in *. Z.div_mod_to_equations. lia. Qed.
  Lemma modpg_add : forall a b, a mod PG = 0 -> b mod PG = 0 -> (a + b) mod PG = 0.
  Proof using. intros a b Ha Hb. unfold PG in *. Z.div_mod_to_equations. lia. Qed.

  Theorem OPS_WF_sec_alloc_pf : OPS_WF_sec_alloc bt.
  Proof using.
    (lazymatch goal with |- ?G => let G' := eval unfold OPS_WF_sec_alloc in G in change_no_check G' end). intros st Lc FF mp n grow W Hn Hal Hdyn DJ Hgrow Hroom HCNT HBYT HM0 SR.
    set (p := mp + sec_user_off n).
    set (st' := op_sec_alloc st mp n grow).
    pose proof W as ((WR1 & WR2) & WC & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6) & (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8) & (LV1 & LV2 & LV3) & WK & WD & WM & WMP & G).
    pose proof (sec_map_size_ge n ltac:(lia)) as (MS1 & MS2 & MS3). pose proof (rz_range n) as RZ. pose proof (rz_mod16 n) as RZ16.
    destruct Hdyn as (DY1 & DY2 & DY3 & DY4 & DY5). box DY4. box DY5.
    assert (HPn : is_primary n = false).
    { (lazymatch goal with |- ?G => let G' := eval unfold is_primary, needed in G in change_no_check G' end). pose proof (rounded_ge n) as (R1 & _). rewrite (rz_big n ltac:(lia)). apply Z.leb_gt. lia. }
    assert (P1 : mp + PG + 16 <= p) by (subst p; (lazymatch goal with |- ?G => let G' := eval unfold sec_user_off in G in change_no_check G' end); lia).
    assert (P2 : p + n <= mp + sec_map_size n) by (subst p; (lazymatch goal with |- ?G => let G' := eval unfold sec_user_off in G in change_no_check G' end); lia).
    assert (P3 : p mod 16 = 0) by (subst p; (lazymatch goal with |- ?G => let G' := eval unfold sec_user_off in G in change_no_check G' end); rewrite Z.add_assoc; apply mod16_of_pg; [exact Hal | exact RZ16]).
    assert (Ep : p = mp + sec_user_off n) by reflexivity. clearbody p.
    pose proof (fresh_vs_live st Lc FF mp (sec_map_size n) W DJ ltac:(lia)) as FL.
    pose proof (fresh_vs_quar st Lc FF mp (sec_map_size n) W DJ ltac:(lia)) as FQ.
    assert (FS : forall sc, In sc (a_sec st) -> mp + sec_map_size n <= sc_map sc \/ sc_map sc + sc_mapsz sc <= mp).
    { intros sc Hs. exact (DJ _ _ (all_ranges_dyn bt st _ (sec_dyn st sc Hs))). }
    assert (NEWnotLc : ~ In (p, n) Lc).
    { intros Hin. destruct (FL p n Hin); unfold PG in *; lia. }
    assert (NEWnotQ : ~ In (p - 16, n) (quar st)).
    { intros Hin. destruct (FQ (p - 16) n Hin); unfold PG in *; lia. }
    assert (LIVEc : forall c a, in_live_c ((p, n) :: Lc) c a <-> in_live_c Lc c a).
    { intros c a. rewrite in_live_c_cons. rewrite HPn. split; [intros [(X & _)|X]; [discriminate X | exact X] | intros X; right; exact X]. }
    (* [comment removed for export] *)
    assert (MP4 : PG <= mp) by (clear -DY1 Hal; unfold PG in *; Z.div_mod_to_equations; lia).
    assert (ABLK : ablk_ok IA p n) by ((lazymatch goal with |- ?G => let G' := eval unfold ablk_ok in G in change_no_check G' end); clear -P1 P2 MP4 DY3 DY4 DY5; Zlia).
    (lazymatch goal with |- ?G => let G' := eval unfold WF, WFq in G in change_no_check G' end).
    split. { (* [comment removed for export] *) split; [| exact WR2]. intros c Hc. destruct (WR1 c Hc) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & PART & FHK).
             change (wf_region bt st' ((p, n) :: Lc) c) with (wf_region bt st ((p, n) :: Lc) c). (lazymatch goal with |- ?G => let G' := eval unfold wf_region in G in change_no_check G' end).
             repeat (split; [assumption|]). split; [exact (partition_live_ext bt st Lc ((p, n) :: Lc) c (LIVEc c) PART) | exact FHK]. }
    split. { exact WC. }
    split. { (* [comment removed for export] *) split; [| split; [| split; [exact Q3 | split; [exact Q4 | split; [exact Q5 | exact Q6]]]]].
             - apply Forall_forall. intros b Hb. rewrite Forall_forall in Q1. exact (wf_batch_sec_alloc st mp n grow b (Q1 b Hb)).
             - apply Forall_forall. intros b Hb. rewrite Forall_forall in Q2. exact (wf_batch_sec_alloc0 st mp n grow b (Q2 b Hb)). }
    split. { (* [comment removed for export] *) (lazymatch goal with |- ?G => let G' := eval unfold wf_secondary in G in change_no_check G' end). change (a_sec st') with (a_sec st ++ [(SCH mp n)]). change (quar st') with (quar st).
             change (a_nres st') with (if grow then a_nres st + 2 ^ 14 else a_nres st).
             rewrite length_app. (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). rewrite Nat2Z.inj_add. (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat] in G in change_no_check G' end).
             split. { destruct grow; [pose proof (proj1 Hgrow eq_refl); lia|].
                      assert (Z.of_nat (length (a_sec st)) <> a_nres st) by (intros E; pose proof (proj2 Hgrow E); discriminate). lia. }
             split. { destruct grow; [| exact S2]. rewrite <- Zplus_mod_idemp_l, S2. reflexivity. }
             split. { destruct grow; [pose proof (Hroom eq_refl); lia | lia]. }
             split. { intros s0 Hs0. apply in_app_iff in Hs0. destruct Hs0 as [Hs0 | [<- | []]]; [exact (S4 s0 Hs0)|].
                      (lazymatch goal with |- ?G => let G' := eval cbn [sc_n sc_map] in G in change_no_check G' end). split; [lia | exact Hal]. }
             split. { rewrite map_app. (lazymatch goal with |- ?G => let G' := eval cbn [List.map] in G in change_no_check G' end). apply NoDup_app_single; [exact S5|]. intros Hin. apply in_map_iff in Hin.
                      destruct Hin as (sc & E & Hs). destruct (FS sc Hs) as [D|D]; destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _);
                      change (sc_map (SCH mp n)) with mp in E; pose proof (rz_range (sc_n sc)) as RZs; clear - D E MS1 A5 A6 A7 Hn RZ RZs; unfold PG in *; lia. }
             split. { intros s0 Hs0. apply in_app_iff in Hs0. destruct Hs0 as [Hs0 | [<- | []]].
                      - rewrite <- (S6 s0 Hs0). (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end). split; [intros [E|H]; [|exact H] | intros H; right; exact H].
                        exfalso. destruct (sec_facts bt st Lc FF W s0 Hs0) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). pose proof (rz_range (sc_n s0)).
                        destruct (FS s0 Hs0); injection E as E1 E2; unfold sc_user, sec_user_off, PG in *; cbn [sc_map sc_n] in E1; lia.
                      - (lazymatch goal with |- ?G => let G' := eval unfold sc_user in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [sc_map sc_n] in G in change_no_check G' end). rewrite <- Ep. split; [intros _; exact NEWnotQ | intros _; left; reflexivity]. }
             split. { intros p' n' [E | Hin] HP'.
                      - injection E as <- <-. exists (SCH mp n). split; [apply in_app_iff; right; left; reflexivity | split; [(lazymatch goal with |- ?G => let G' := eval unfold sc_user in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [sc_map sc_n] in G in change_no_check G' end); rewrite <- Ep; reflexivity | reflexivity]].
                      - apply registered_sec_alloc. exact (S7 p' n' Hin HP'). }
             intros m n' Hin HP'. apply registered_sec_alloc. exact (S8 m n' Hin HP'). }
    split. { (* [comment removed for export] *) split; [| split].
             - intros p' n' [E | Hin]; [| exact (LV1 p' n' Hin)]. injection E as <- <-.
               split; [lia|]. split; [exact P3|]. split; [exact ABLK|]. rewrite HPn. intros X; discriminate X.
             - constructor; [exact NEWnotLc | exact LV2].
             - intros p1 n1 p2 n2 [E1 | H1] [E2 | H2] NE.
               + exfalso. apply NE. rewrite <- E1, <- E2. reflexivity.
               + injection E1 as <- <-. destruct (FL p2 n2 H2); pose proof (rz_range n2); unfold PG in *; lia.
               + injection E2 as <- <-. destruct (FL p1 n1 H1); pose proof (rz_range n1); unfold PG in *; lia.
               + exact (LV3 p1 n1 p2 n2 H1 H2 NE). }
    split. { exact WK. } split. { exact WD. }
    split. { (* [comment removed for export] *)
             destruct WM as (M1 & M2 & M3 & M4 & M5). (lazymatch goal with |- ?G => let G' := eval unfold wf_meter in G in change_no_check G' end). change (a_kact st') with (a_kact st). change (a_shsec st') with (a_shsec st).
             change (a_sec st') with (a_sec st ++ [(SCH mp n)]). change (a_reg st') with (a_reg st). change (sum_mu st') with (sum_mu st).
             rewrite length_app. (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). rewrite Nat2Z.inj_add. (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat] in G in change_no_check G' end).
             unfold sec_room in SR. split; [exact M1|]. split; [lia|]. split; [lia|]. split; [exact M4 | exact M5]. }
    split. { (* [comment removed for export] *) destruct WMP as (RNG & PWS & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19 & K20).
             split; [| split; [| do 17 (split; [assumption|]);
               intros b0 n0 lo hi Hb Hin; subst st'; unfold dyn_ranges, op_sec_alloc in Hin; cbn [a_sec a_dep] in Hin; rewrite map_app, <- app_assoc in Hin;
               apply in_app_iff in Hin; destruct Hin as [Hin | Hin]; [apply (K20 b0 n0 lo hi Hb); (lazymatch goal with |- ?G => let G' := eval unfold dyn_ranges in G in change_no_check G' end); apply in_app_iff; left; exact Hin|];
               cbn [map app] in Hin; destruct Hin as [E | Hin]; [injection E as <- <-; (lazymatch goal with |- ?G => let G' := eval cbn [sc_map sc_mapsz sc_n] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold sc_mapsz in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [sc_n] in G in change_no_check G' end); exact (HM0 b0 n0 Hb) | apply (K20 b0 n0 lo hi Hb); (lazymatch goal with |- ?G => let G' := eval unfold dyn_ranges in G in change_no_check G' end); apply in_app_iff; right; exact Hin]]].
             - intros lo hi Hin. apply in_all_ranges_sec_alloc in Hin. destruct Hin as [Hin | E]; [exact (RNG lo hi Hin)|].
               injection E as <- <-. split; [split; [exact DY1 | split; [exact DY2 | split; [exact DY3 | split; [exact DY4 | exact DY5]]]]|].
               split; [lia|]. split; [exact Hal|]. apply modpg_add; [exact Hal | exact MS2].
             - subst st'. intros l1 l2 lo hi lo' hi'. rewrite all_ranges_sec_alloc. revert l1 l2 lo hi lo' hi'. apply splits_insert.
               + rewrite <- all_ranges_old. exact PWS.
               + intros lo' hi' Hin. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). rewrite <- all_ranges_old in Hin. exact (DJ lo' hi' Hin). }
    destruct G as ((GA & GC & GB) & GOK). split; [split; [exact GA | split; [(lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn [PHI snd] in G in change_no_check G' end); lia]] | exact GOK].
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition foot_sec_alloc (st : ast) (mp n : Z) (grow : bool) (a : Z) : Prop :=
    (mp <= a < mp + sec_map_size n) \/ (sh_lo mp <= a < sh_hi mp (sec_map_size n))
    \/ (IB bt + 112 <= a < IB bt + 728)
    \/ (bt_ptrarr bt + 8 * Z.of_nat (length (a_sec st)) <= a < bt_ptrarr bt + 8 * Z.of_nat (length (a_sec st)) + 8)
    \/ (grow = true /\ bt_ptrarr bt + 8 * a_nres st <= a < bt_ptrarr bt + 8 * a_nres st + 2 ^ 17)
    \/ (T + 2768 <= a < T + T_UNW + 1)
    \/ CEIL <= a.

  Definition OPS_REP_sec_alloc : Prop := forall st Lc FF M M' mdl mdl' mp n grow,
    WF bt st Lc FF -> Rep bt st Lc FF M mdl ->
    64513 <= n <= NMAX -> mp mod PG = 0 -> dyn_ok (bt_ia bt) mp (mp + sec_map_size n) ->
    (forall lo hi, In (lo, hi) (all_ranges bt st) -> mp + sec_map_size n <= lo \/ hi <= mp) ->
    (grow = true <-> Z.of_nat (length (a_sec st)) = a_nres st) -> (grow = true -> a_nres st + 2 ^ 14 <= 2 ^ 20) ->
    let p := mp + sec_user_off n in
    let len := Z.of_nat (length (a_sec st)) in
    let nres' := (if grow then a_nres st + 2 ^ 14 else a_nres st) in
    agrees_off (foot_sec_alloc st mp n grow) M M' ->
    (* [comment removed for export] *)
    cellZ SG M' (IB bt + 112) 8 nres' -> cellZ SG M' (IB bt + 120) 8 (len + 1) -> byteZ SG M' (IB bt + 680) 0 ->
    cellZ SG M' (bt_ptrarr bt + 8 * len) 8 mp -> writableZ SG M' (bt_ptrarr bt) (bt_ptrarr bt + 8 * nres') ->
    cellZ SG M' mp 8 mp -> cellZ SG M' (mp + 8) 8 (sec_map_size n) -> cellZ SG M' (mp + 16) 8 (sec_needed n) -> cellZ SG M' (mp + 24) 8 len ->
    writableZ SG M' mp (mp + sec_map_size n) ->
    rep_hdr bt M' p n 2 ->
    (forall g, mp / 8 <= g < (mp + sec_map_size n) / 8 -> ~ user_granule p n g -> byteZ SG M' (SB + g) FA) ->
    byteZ SG M' (T + T_UNW) 0 ->
    (* [comment removed for export] *)
    Permutation (vm_maps (m_vmmaps mdl')) ((Z_to_bv 64 mp, Z_to_bv 64 (sec_map_size n)) :: vm_maps (m_vmmaps mdl)) ->
    (forall a, in_ivz (vm_noaccess (m_vmmaps mdl')) a <->
               in_ivz (vm_noaccess (m_vmmaps mdl)) a /\ ~ (grow = true /\ bt_ptrarr bt + 8 * a_nres st <= a < bt_ptrarr bt + 8 * a_nres st + 2 ^ 17)) ->
    (* [comment removed for export] *)
    Forall (fun e : word * word => 0 < bv_unsigned (snd e)) (vm_noaccess (m_vmmaps mdl')) ->
    (forall a, pg_in_ivz (m_vm_lazy mdl') a <->
               pg_in_ivz (m_vm_lazy mdl) a /\ ~ (grow = true /\ bt_ptrarr bt + 8 * a_nres st <= a < bt_ptrarr bt + 8 * a_nres st + 2 ^ 17)) ->
    Forall (fun iv : word * word => bv_unsigned (fst iv) mod PG = 0 /\ bv_unsigned (snd iv) mod PG = 0
                                   /\ 0 < bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= CEIL
                                   /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= ia_img_lo (bt_ia bt) \/ ia_img_hi (bt_ia bt) <= bv_unsigned (fst iv)))
           (m_vm_lazy mdl') ->
    vm_reserved (m_vmmaps mdl') = vm_reserved (m_vmmaps mdl) -> vm_brk (m_vmmaps mdl') = vm_brk (m_vmmaps mdl) ->
    vm_start_brk (m_vmmaps mdl') = vm_start_brk (m_vmmaps mdl) -> vm_mmap_base (m_vmmaps mdl') = vm_mmap_base (m_vmmaps mdl) ->
    vm_init_sp (m_vmmaps mdl') = vm_init_sp (m_vmmaps mdl) ->
    vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl) ->
    (* [comment removed for export] *)
    MInv (a_aa st ++ sec_naa mp n) mdl' -> eager_used mdl' <= eager_used mdl + sec_map_size n + (if grow then 2 ^ 17 else 0) ->
    Rep bt (op_sec_alloc st mp n grow) ((p, n) :: Lc) FF M' mdl'.

  Lemma range_allowed_sub : forall AA lo hi lo' hi', range_allowed AA lo hi -> lo <= lo' -> hi' <= hi -> range_allowed AA lo' hi'.
  Proof using. intros AA lo hi lo' hi' H A B a Ha. apply H. lia. Qed.

  Lemma byteZ_same : forall M1 M2 a b, byteZ SG M1 a b -> byteZ SG M2 a b ->
    M1 (Z_to_bv 64 a) <> None -> M2 (Z_to_bv 64 a) <> None -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a).
  Proof using.
    intros M1 M2 a b B1 B2 D1 D2. unfold byteZ, cellN in *. cbn [rdn] in B1, B2.
    destruct (M1 (Z_to_bv 64 a)) as [x|]; [| exfalso; exact (D1 eq_refl)].
    destruct (M2 (Z_to_bv 64 a)) as [y|]; [| exfalso; exact (D2 eq_refl)].
    cbn in B1, B2. rewrite <- B2 in B1. injection B1 as ->. reflexivity.
  Qed.

  Lemma ranges_sep : forall st Lc FF, WF bt st Lc FF -> forall lo hi lo' hi',
    In (lo, hi) (all_ranges bt st) -> In (lo', hi') (all_ranges bt st) -> (lo, hi) <> (lo', hi') -> hi <= lo' \/ hi' <= lo.
  Proof using.
    intros st Lc FF W lo hi lo' hi' H1 H2 NE. pose proof (ar_disj_ne bt st Lc FF _ _ W H1 H2 NE) as D. hnf in D. cbn in D. exact D.
  Qed.

  Theorem OPS_REP_sec_alloc_pf : OPS_REP_sec_alloc.
  Proof using.
    intros st Lc FF M M' mdl mdl' mp n grow W R Hn Hal Hdyn DJ Hgrow Hroom. cbn zeta.
    intros AGR CI1 CI2 CI3 CP WP CM1 CM2 CM3 CM4 WM HDR SHN BUNW PM NA NP' LZ FL' E1 E2 E3 E4 E6 E5 MI EAG.
    set (p := mp + sec_user_off n) in *. set (len := Z.of_nat (length (a_sec st))) in *.
    set (st' := op_sec_alloc st mp n grow).
    pose proof W as ((WR1 & WR2) & WC & WQ & (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8) & (LV1 & LV2 & LV3) & WK & WD & WM' & (RNG & PW' & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & G).
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    pose proof (bt_ok_W bt st Lc FF W) as (I1 & I2 & PR & QI1 & QI2 & QI3 & QI4 & QI5 & QI6 & CC & U1 & U2 & U3 & U4 & DC & DT & DR & DJI).
    pose proof (image_facts bt st Lc FF W) as IMF. cbn zeta in IMF.
    destruct IMF as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y16 & YC).
    pose proof (agrees_DEFK _ _ _ AGR) as DEF. pose proof (agrees_at' _ _ _ AGR) as AGF.
    pose proof (sec_map_size_ge n ltac:(lia)) as (MS1 & MS2 & MS3). pose proof (rz_range n) as RZ. pose proof (rz_big n ltac:(lia)) as RZB.
    destruct Hdyn as (DY1 & DY2 & DY3 & DY4 & DY5). box DY4. box DY5.
    destruct (RNG _ _ (all_ranges_fixed bt st _ IN8)) as ((PD1 & PD2 & PD3 & PD4 & PD5) & _). box PD4. box PD5.
    destruct (RNG _ _ (all_ranges_fixed bt st _ INT)) as ((TD1 & TD2 & TD3 & TD4 & TD5) & _). box TD4. box TD5.
    assert (HPn : is_primary n = false).
    { (lazymatch goal with |- ?G => let G' := eval unfold is_primary, needed in G in change_no_check G' end). pose proof (rounded_ge n) as (Q1 & _). rewrite RZB. apply Z.leb_gt. lia. }
    assert (P1 : mp + PG + 16 <= p) by (subst p; (lazymatch goal with |- ?G => let G' := eval unfold sec_user_off in G in change_no_check G' end); lia).
    assert (P2 : p + n <= mp + sec_map_size n) by (subst p; (lazymatch goal with |- ?G => let G' := eval unfold sec_user_off in G in change_no_check G' end); lia).
    assert (Ep : p = mp + sec_user_off n) by reflexivity. clearbody p.
    assert (Elen : len = Z.of_nat (length (a_sec st))) by reflexivity. clearbody len.
    assert (LEN : 0 <= len <= a_nres st) by lia.
    pose proof (fresh_vs_live st Lc FF mp (sec_map_size n) W DJ ltac:(lia)) as FLv.
    pose proof (fresh_vs_quar st Lc FF mp (sec_map_size n) W DJ ltac:(lia)) as FQ.
    assert (FS : forall sc, In sc (a_sec st) -> mp + sec_map_size n <= sc_map sc \/ sc_map sc + sc_mapsz sc <= mp).
    { intros sc Hs. exact (DJ _ _ (all_ranges_dyn bt st _ (sec_dyn st sc Hs))). }
    pose proof (DJ _ _ (all_ranges_fixed bt st _ IN6)) as F6. pose proof (DJ _ _ (all_ranges_fixed bt st _ IN8)) as F8.
    pose proof (DJ _ _ (all_ranges_fixed bt st _ INT)) as Ft. box F6. box F8. box Ft.
    try ceil; unfold AS_HEAPLO, AS_LO, PG, FAKE_SIZE, KSPACE in X1, X2, X3, X4, X5, X6, X8, X9, X10, X11, X12, X13, X14, X15, Y2, Y4, Y6, Y8, Y10, Y12, Y14, Y16.
    unfold IB, DEPOT_TAB, SSOBJ, IA_FLAG, IA_INST in Y1, Y2, Y3, Y4, Y5, Y6, Y7, Y8, Y9, Y10.
    (* [comment removed for export] *)
    assert (IBH : ia_img_lo IA <= ia_instance IA + 112 /\ ia_instance IA + 985 <= ia_img_hi IA).
    { destruct QI1 as (plo & phi & Hin & Hx1 & Hx2). destruct (PR plo phi (or_introl Hin)). lia. }
    (* [comment removed for export] *)
    assert (ROOM : 8 * a_nres st + (if grow then 2 ^ 17 else 0) <= 2 ^ 23) by (clear -Hroom S3; destruct grow; [pose proof (Hroom eq_refl); lia | lia]).
    assert (LENlt : 8 * len + 8 <= 8 * a_nres st + (if grow then 2 ^ 17 else 0)).
    { destruct grow; [lia|]. assert (len <> a_nres st) by (intros E; pose proof (proj2 Hgrow E); discriminate). lia. }
    clear Hgrow Hroom.
    set (GS := if grow then 2 ^ 17 else 0) in *.
    assert (EGS : GS = (if grow then 2 ^ 17 else 0)) by reflexivity.
    assert (GS0 : 0 <= GS <= 2 ^ 17) by (subst GS; destruct grow; lia). clearbody GS.
    assert (AGZ : forall i, 0 <= i < 2 ^ 64 ->
              ~ (mp <= i < mp + sec_map_size n) -> ~ (SB + mp / 8 <= i < SB + (mp + sec_map_size n + 7) / 8) ->
              ~ (ia_instance IA + 112 <= i < ia_instance IA + 728) -> ~ (bt_ptrarr bt + 8 * len <= i < bt_ptrarr bt + 8 * a_nres st + GS) ->
              ~ (T + 2768 <= i < T + T_UNW + 1) -> i < CEIL -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hr N1 N2 N3 N4 N5 N6. apply AGF; [| exact Hr]. intros Hf. unfold foot_sec_alloc, sh_lo, sh_hi, IB in Hf. rewrite <- Elen in Hf.
      destruct Hf as [Hf|[Hf|[Hf|[Hf|[[Gt Hf]|[Hf|Hf]]]]]].
      5: { rewrite Gt in EGS. cbn in EGS. clear -Hf N4 LENlt EGS LEN. lia. }
      all: clear -Hf N1 N2 N3 N4 N5 N6 LEN LENlt GS0; lia. }
    (* [comment removed for export] *)
    assert (SHB : AS_LO <= SB + mp / 8 /\ SB + (mp + sec_map_size n + 7) / 8 <= AS_HEAPLO).
    { clear -DY1 DY3 MS1 Hn RZ. try ceil. unfold AS_LO, AS_HEAPLO, SB, PG in *. Z.div_mod_to_equations. lia. }
    destruct SHB as [SHB1 SHB2].
    (* [comment removed for export] *)
    assert (IMGfree : forall i, ia_img_lo IA <= i < ia_img_hi IA -> ~ (ia_instance IA + 112 <= i < ia_instance IA + 728) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi N3.
      apply AGZ; [clear -Hi I1 I2; ulia | clear -Hi DY4; Ztac | clear -Hi I2 SHB1; ulia | exact N3 | clear -Hi PD4 LEN GS0 ROOM; Ztac | clear -Hi TD4; unfold T_UNW, PG in *; Ztac | clear -Hi I2; ulia]. }
    (* [comment removed for export] *)
    assert (FIXfree : forall lo hi, In (lo, hi) (bt_fixed bt) -> hi <= bt_ptrarr bt \/ bt_ptrarr bt + 2 ^ 23 <= lo ->
                      hi <= T \/ T + PG <= lo ->
                      forall i, lo <= i < hi -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros lo hi Hlohi A8 AT i Hi Hr. destruct (RNG _ _ (all_ranges_fixed bt st _ Hlohi)) as ((A1 & A1' & A3 & A4 & A5) & A2 & _).
      pose proof (DJ _ _ (all_ranges_fixed bt st _ Hlohi)) as Dm.
      apply AGZ; [exact Hr | clear -Hi Dm; Ztac | clear -Hi A5 SHB1 SHB2; Zlia | clear -Hi A4 IBH; Ztac | clear -Hi A8 LEN GS0 ROOM; Ztac | clear -Hi AT; unfold T_UNW, PG in *; Ztac | clear -Hi A3; lia]. }
    assert (DYNfree : forall lo hi, In (lo, hi) (dyn_ranges st) -> forall i, lo <= i < hi -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros lo hi Hlohi i Hi Hr. destruct (RNG _ _ (all_ranges_dyn bt st _ Hlohi)) as ((A1 & A1' & A3 & A4 & A5) & A2 & _).
      pose proof (DJ _ _ (all_ranges_dyn bt st _ Hlohi)) as Dm.
      pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W IN8 Hlohi) as D8. hnf in D8. cbn in D8.
      pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W INT Hlohi) as DT'. hnf in DT'. cbn in DT'.
      apply AGZ; [exact Hr | clear -Hi Dm; Ztac | clear -Hi A5 SHB1 SHB2; Zlia | clear -Hi A4 IBH; Ztac | clear -Hi D8 LEN GS0 ROOM; Ztac | clear -Hi DT'; unfold T_UNW, PG in *; Ztac | clear -Hi A3; lia]. }
    (* [comment removed for export] *)
    destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & SP4 & SP5) & SP6 & SP7 & SP8 & SPH). assert (SBH : AS_HEAPLO <= SBEG) by lia.
    pose proof (ranges_sep st Lc FF W _ _ _ _ (all_ranges_fixed bt st _ IN6) (all_ranges_fixed bt st _ IN8) ltac:(intros E; injection E; clear -SP7 SP8; unfold KSPACE, PG in *; lia)) as R68.
    pose proof (ranges_sep st Lc FF W _ _ _ _ (all_ranges_fixed bt st _ IN6) (all_ranges_fixed bt st _ INT) ltac:(intros E; injection E; clear -SP7 SP8; unfold KSPACE, PG in *; lia)) as R6T.
    box R68. box R6T.
    assert (SPCfree : forall i, SBEG <= i < SBEG + KSPACE + PG -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi. apply (FIXfree _ _ IN6); [exact R68 | exact R6T | clear -Hi SP7 SP8; lia | clear -Hi X14 X15; ulia]. }
    assert (HDRfree : forall p' n' i, In (p', n') Lc \/ In (p' - 16, n') (quar st) -> foot_hdr p' n' i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros p' n' i Hown Hfh Hr.
      destruct (hdr_zone bt st Lc FF W p' n' i Hown Hfh) as [(HP' & Z1 & Z2 & Z3 & CV' & HC' & N1' & Z4) | (HP' & sc' & Hs' & Eu' & En' & Z1 & N1')]; [apply SPCfree; ulia|].
      destruct (sec_facts bt st Lc FF W sc' Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). apply (DYNfree _ _ (sec_dyn st sc' Hs')); ulia. }
    pose proof R as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18 & R19).
    (* [comment removed for export] *)
    assert (SHdef : forall i, SB + mp / 8 <= i < SB + (mp + sec_map_size n + 7) / 8 -> M' (Z_to_bv 64 i) <> None).
    { intros i Hi. apply (def_keep M M' _ DEF). apply (proj1 R19). (lazymatch goal with |- ?G => let G' := eval unfold shmaps in G in change_no_check G' end). clear -Hi DY1 DY3 DY5 MS1 MS2 Hal Hn RZ.
      try ceil. unfold AS_LO, AS_GAPLO, AS_GAPHI, AS_HEAPLO, SB, PG, boxed in *. dsj; Z.div_mod_to_equations; lia. }
    (* [comment removed for export] *)
    pose proof (img_pw bt st Lc FF W) as PWI. unfold img_ranges in PWI. cbn [AsAinvDefs3.PW seps fst snd] in PWI.
    destruct PWI as ((S01 & S02 & S03 & S04 & S05 & S06 & S07 & _) & _).
    assert (IMGR : forall i,
              (ia_depot_tab IA <= i < ia_depot_tab IA + 0x400010 + 8 * 2 ^ 15) \/ (ia_stackstore IA <= i < ia_stackstore IA + 16 + 16 * 2 ^ 12)
              \/ (ia_ialloc_flag IA <= i < ia_ialloc_flag IA + 8) \/ (ia_ialloc_inst IA <= i < ia_ialloc_inst IA + IASZ)
              \/ (bt_tls_fs bt <= i < bt_tls_fs bt + 16) \/ (ia_rtc_sb IA <= i < ia_rtc_sb IA + 8) \/ (ia_rtc_uar IA <= i < ia_rtc_uar IA + 4) ->
              M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hr.
      assert (HI : ia_img_lo IA <= i < ia_img_hi IA).
      { destruct QI2 as (plo2 & phi2 & Hin2 & Hx1 & Hx2). destruct (PR plo2 phi2 (or_introl Hin2)) as [Ga Gb].
        destruct QI3 as (plo3 & phi3 & Hin3 & Hy1 & Hy2). destruct (PR plo3 phi3 (or_introl Hin3)) as [Gc Gd].
        destruct QI4 as (plo4 & phi4 & Hin4 & Hz1 & Hz2). destruct (PR plo4 phi4 (or_introl Hin4)) as [Ge Gf].
        destruct QI5 as (plo5 & phi5 & Hin5 & Hw1 & Hw2). destruct (PR plo5 phi5 (or_introl Hin5)) as [Gg Gh].
        destruct QI6 as (plo6 & phi6 & Hin6 & Hv1 & Hv2). destruct (PR plo6 phi6 (or_introl Hin6)) as [Gi Gj].
        clear -Hr Hx1 Hx2 Hy1 Hy2 Hz1 Hz2 Hw1 Hw2 Hv1 Hv2 Ga Gb Gc Gd Ge Gf Gg Gh Gi Gj U1 U2 U3 U4. unfold IASZ in *. dsj; lia. }
      apply IMGfree; [exact HI|]. intros X.
      destruct Hr as [Hr|[Hr|[Hr|[Hr|[Hr|[Hr|Hr]]]]]]; [clear -Hr X S01 | clear -Hr X S02 | clear -Hr X S03 | clear -Hr X S04 | clear -Hr X S05 | clear -Hr X S06 | clear -Hr X S07]; unfold IASZ in *; lia. }
    clear S01 S02 S03 S04 S05 S06 S07.
    (* [comment removed for export] *)
    assert (CONSTfree : forall c i, In c (bt_consts bt) -> fst (fst c) <= i < fst (fst c) + Z.of_nat (snd (fst c)) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros c i Hc Hi. rewrite Forall_forall in DC. pose proof (DC c Hc i Hi) as ND. unfold img_dyn in ND.
      apply IMGfree; [| intros X; apply ND; left; clear -X; lia].
      exact (proj1 (img_kinds bt st Lc FF W i ltac:(left; exists c; split; [exact Hc | exact Hi]))). }
    assert (NEWnotQ : ~ In (p - 16, n) (quar st)).
    { intros Hin. destruct (FQ (p - 16) n Hin); unfold PG in *; lia. }
    (* [comment removed for export] *)
    pose proof (ranges_sep st Lc FF W _ _ _ _ (all_ranges_fixed bt st _ INN) (all_ranges_fixed bt st _ IN8) ltac:(clear; intros E; injection E; lia)) as N8.
    pose proof (ranges_sep st Lc FF W _ _ _ _ (all_ranges_fixed bt st _ INN) (all_ranges_fixed bt st _ INT) ltac:(clear; intros E; injection E; (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia)) as NT.
    pose proof (ranges_sep st Lc FF W _ _ _ _ (all_ranges_fixed bt st _ INFS) (all_ranges_fixed bt st _ IN8) ltac:(clear; intros E; injection E; (lazymatch goal with |- ?G => let G' := eval unfold FAKE_SIZE in G in change_no_check G' end); lia)) as F8q.
    pose proof (ranges_sep st Lc FF W _ _ _ _ (all_ranges_fixed bt st _ INFS) (all_ranges_fixed bt st _ INT) ltac:(clear; intros E; injection E; (lazymatch goal with |- ?G => let G' := eval unfold FAKE_SIZE, PG in G in change_no_check G' end); lia)) as FTq.
    pose proof (ranges_sep st Lc FF W _ _ _ _ (all_ranges_fixed bt st _ INT) (all_ranges_fixed bt st _ IN8) ltac:(clear; intros E; injection E; (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia)) as T8.
    pose proof (ranges_sep st Lc FF W _ _ _ _ (all_ranges_fixed bt st _ INC) (all_ranges_fixed bt st _ IN8) ltac:(clear; intros E; injection E; lia)) as C8.
    pose proof (ranges_sep st Lc FF W _ _ _ _ (all_ranges_fixed bt st _ INC) (all_ranges_fixed bt st _ INT) ltac:(clear; intros E; injection E; (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia)) as CT.
    box N8. box NT. box F8q. box FTq. box T8. box C8. box CT.
    (lazymatch goal with |- ?G => let G' := eval unfold Rep in G in change_no_check G' end).
    (* [comment removed for export] *)
    split. { eapply cells_hold_frame; [exact R1 | exact YC |]. intros c0 i Hc0 Hi. exact (CONSTfree c0 i Hc0 Hi). }
    (* [comment removed for export] *)
    split. { destruct R2 as (J1 & J2 & J3 & J4 & J5 & J6 & JL & JP & JW). (lazymatch goal with |- ?G => let G' := eval unfold rep_instance in G in change_no_check G' end).
             change (a_nres st') with (if grow then a_nres st + 2 ^ 14 else a_nres st). change (a_sec st') with (a_sec st ++ [SCH mp n]). change (a_gq st') with (a_gq st).
             rewrite length_app. (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). rewrite Nat2Z.inj_add. (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat] in G in change_no_check G' end). rewrite <- Elen.
             unfold IB in *.
             split; [exact CI1|]. split; [exact CI2|]. split; [exact CI3|].
             split. { eapply (byteZ_frame _ _ _ _ _ J4); [uilia | uilia | apply IMGfree; uilia]. }
             split. { eapply (byteZ_frame _ _ _ _ _ J5); [uilia | uilia | apply IMGfree; uilia]. }
             split. { eapply (byteZ_frame _ _ _ _ _ J6); [uilia | uilia | apply IMGfree; uilia]. }
             split. { eapply rep_list_frame; [exact JL | uilia | uilia |]. intros i Hi Hr. apply IMGfree; uilia. }
             split. { intros i s Hs. destruct (lt_dec i (length (a_sec st))) as [LT | GE].
                      - rewrite nth_error_app1 in Hs by exact LT. pose proof (JP i s Hs) as C. pose proof (nth_error_lt _ _ _ Hs).
                        apply Nat2Z.inj_lt in LT. rewrite <- Elen in LT.
                        eapply (cellZ_frame _ _ _ _ _ _ C); [uilia | uilia |]. intros j Hj.
                        apply AGZ; [clear -Hj LT X12 X13 LEN ROOM GS0; Ztac | clear -Hj LT F8 LEN ROOM GS0; Ztac | clear -Hj LT PD5 SHB1 SHB2 LEN ROOM GS0; Zlia | clear -Hj LT PD4 IBH LEN ROOM GS0; Ztac | clear -Hj LT; lia | clear -Hj LT T8 LEN ROOM GS0; Zlia | clear -Hj LT X13 LEN ROOM GS0; lia].
                      - rewrite nth_error_app2 in Hs by lia. destruct (i - length (a_sec st))%nat as [|k] eqn:Ek; cbn in Hs; [| destruct k; discriminate Hs].
                        injection Hs as <-. (lazymatch goal with |- ?G => let G' := eval cbn [sc_map] in G in change_no_check G' end). replace (Z.of_nat i) with len by lia. exact CP. }
             exact WP. }
    (* [comment removed for export] *)
    split. { change (rep_thread bt st' M') with (rep_thread bt st M').
             eapply rep_thread_frame; [exact DEF | exact R3 | uilia | uilia | uilia | uilia | exact (cache_len bt st Lc FF W) |].
             intros i Hi Hr. unfold thread_cells, T_QC, T_PC, PC_SZ, T_UNW in Hi.
             destruct Hi as [Hi|[Hi|[Hi|[Hi|[Hi|[Hi|[Hi|Hi]]]]]]].
             6: { subst i. destruct R3 as (_ & _ & _ & _ & _ & T6 & _ & _ & TW & _). unfold T_UNW in *.
                  assert (D1 : M (Z_to_bv 64 (T + 3168)) <> None) by (apply TW; (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia).
                  exact (byteZ_same M M' _ 0 T6 BUNW D1 (def_keep M M' _ DEF D1)). }
             1-5: apply AGZ; [exact Hr | clear -Hi Ft; unfold PG in *; Ztac | clear -Hi TD5 SHB1 SHB2; Zlia | clear -Hi TD4 IBH; unfold PG in *; Ztac | clear -Hi T8 LEN ROOM GS0; unfold PG in *; Ztac | clear -Hi; lia | clear -Hi X2; lia].
             all: apply (FIXfree _ _ INC); [exact C8 | exact CT | clear -Hi; lia | exact Hr]. }
    (* [comment removed for export] *)
    split. { intros c0 Hc0. destruct (R4 c0 Hc0) as [G0 F0]. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF.
             destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & _).
             change (a_reg st' c0) with (a_reg st c0).
             eapply rep_region_frame; [exact DEF | exact G0 | exact F0 | uilia | uilia | uilia | uilia | uilia |].
             intros i Hi Hr. unfold foot_region in Hi. apply SPCfree. clear -Hi Q1 Q2 Q5 Q6 Q7 Q8 Q9 Q10. uilia. }
    (* [comment removed for export] *)
    assert (BR : forall b0, In b0 (a_tq st ++ a_gq st) -> 0 <= ba_addr b0 /\ ba_addr b0 + BATCHSZ < 2 ^ 64 /\ Z.of_nat (length (ba_items b0)) <= BATCHCAP).
    { intros b0 Hb0. destruct (batch_facts bt st Lc FF W b0 Hb0) as (_ & BL1 & BL2 & BL3). clear -BL1 BL2 BL3 X14 X15. uilia. }
    assert (BA : forall b0 i, In b0 (a_tq st ++ a_gq st) -> foot_batch b0 i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros b0 i Hb0 Hi Hr. unfold foot_batch in Hi. destruct (batch_facts bt st Lc FF W b0 Hb0) as (CVb & BLb & BL2 & BL3). apply SPCfree. clear -Hi BLb BL2 BL3. uilia. }
    split. { change (a_tq st') with (a_tq st). eapply rep_batches_frame; [exact DEF | exact R5 | intros b0 Hb0; apply BR; apply in_app_iff; left; exact Hb0 |].
             intros b0 i Hb0 Hi Hr. apply (BA b0 i); [apply in_app_iff; left; exact Hb0 | exact Hi | exact Hr]. }
    split. { change (a_gq st') with (a_gq st). eapply rep_batches_frame; [exact DEF | exact R6 | intros b0 Hb0; apply BR; apply in_app_iff; right; exact Hb0 |].
             intros b0 i Hb0 Hi Hr. apply (BA b0 i); [apply in_app_iff; right; exact Hb0 | exact Hi | exact Hr]. }
    (* [comment removed for export] *)
    split. { intros i s Hs. change (a_sec st') with (a_sec st ++ [SCH mp n]) in Hs.
             destruct (lt_dec i (length (a_sec st))) as [LT | GE].
             - rewrite nth_error_app1 in Hs by exact LT. pose proof (nth_error_In _ _ Hs) as Hin. destruct (R7 i s Hs) as (Z1 & Z2 & Z3 & Z4 & ZW).
               destruct (sec_facts bt st Lc FF W s Hin) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _).
               assert (AGs : forall j, sc_map s <= j < sc_map s + 32 -> M' (Z_to_bv 64 j) = M (Z_to_bv 64 j)).
               { intros j Hj. apply (DYNfree _ _ (sec_dyn st s Hin)); clear -Hj A1 A2 A5 A6 A7; uilia. }
               split; [eapply (cellZ_frame _ _ _ _ _ _ Z1); [uilia | uilia | intros j Hj; apply AGs; lia]|].
               split; [eapply (cellZ_frame _ _ _ _ _ _ Z2); [uilia | uilia | intros j Hj; apply AGs; lia]|].
               split; [eapply (cellZ_frame _ _ _ _ _ _ Z3); [uilia | uilia | intros j Hj; apply AGs; lia]|].
               split; [eapply (cellZ_frame _ _ _ _ _ _ Z4); [uilia | uilia | intros j Hj; apply AGs; lia]|].
               frW DEF ZW.
             - rewrite nth_error_app2 in Hs by lia. destruct (i - length (a_sec st))%nat as [|k] eqn:Ek; cbn in Hs; [| destruct k; discriminate Hs].
               injection Hs as <-. (lazymatch goal with |- ?G => let G' := eval cbn [sc_map sc_n sc_mapsz] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold sc_mapsz in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [sc_n] in G in change_no_check G' end).
               split; [exact CM1|]. split; [exact CM2|]. split; [exact CM3|]. split; [replace (Z.of_nat i) with len by lia; exact CM4 | exact WM]. }
    (* [comment removed for export] *)
    split. { change (quar st') with (quar st). destruct R8 as [HL HQ]. split.
             - intros p0 n0 [E | Hin].
               + injection E as <- <-. exact HDR.
               + destruct (live_range bt st Lc FF W p0 n0 Hin) as (A1 & A2 & A3 & A4). pose proof (rz_range n0).
                 eapply rep_hdr_frame; [exact DEF | exact (HL p0 n0 Hin) | uilia | uilia |].
                 intros i Hi Hr. apply (HDRfree p0 n0 i); [left; exact Hin | exact Hi | exact Hr].
             - intros m n0 Hin. destruct (HQ m n0 Hin) as [Hh HWq]. destruct (quar_item_range bt st Lc FF W m n0 Hin) as (A1 & A2 & A3). pose proof (rz_range n0).
               split; [| frW DEF HWq].
               eapply rep_hdr_frame; [exact DEF | exact Hh | uilia | uilia |].
               intros i Hi Hr. apply (HDRfree (m + 16) n0 i); [right; replace (m + 16 - 16) with m by lia; exact Hin | exact Hi | exact Hr]. }
    (* [comment removed for export] *)
    split. { change (rep_depot bt st' M') with (rep_depot bt st M'). eapply rep_depot_frame; [exact DEF | exact R9 | uilia | uilia | uilia | uilia | | |].
             - intros id Hid. destruct (node_addr_range bt st Lc FF W id Hid) as (_ & A1 & A2 & _). clear -A1 A2. uilia.
             - intros i Hi Hr. unfold foot_depot_static, DEPOT_NIDS, DEPOT_MAP1, DEPOT_TAB, SSOBJ in Hi. apply IMGR; clear -Hi Y3 Y4 Y5 Y6; uilia.
             - intros id i Hid Hi Hr. unfold foot_node in Hi. destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & A1 & A2 & A3).
               pose proof (node_addr_block bt st id Hid) as Hbk. set (bb := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody bb.
               destruct HIn as [Eb | Hnb].
               + apply (FIXfree _ _ INN); [exact N8 | exact NT | rewrite Eb; lia | exact Hr].
               + apply (DYNfree _ _ (node_dyn st bb Hnb)); [lia | exact Hr]. }
    (* [comment removed for export] *)
    split. { change (rep_fake bt st' FF M') with (rep_fake bt st FF M'). pose proof (dtls_facts bt st Lc FF W) as [DT1 DT2].
             pose proof (ranges_sep st Lc FF W _ _ _ _ (all_ranges_fixed bt st _ (dtls_member bt st Lc FF W)) (all_ranges_fixed bt st _ IN8) ltac:(clear; intros E; injection E; (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia)) as D8q.
             pose proof (dtls_vs_thread bt st Lc FF W) as DTq.
             eapply rep_fake_frame; [exact DEF | exact R10 | uilia | uilia | uilia | uilia | clear -DT1; uilia | clear -DT2; uilia | | |].
             - intros f k0 Hf. destruct (fake_frame_facts bt st Lc FF W f k0 Hf) as (A1 & A2 & A3 & A4 & _). clear -A1 A2 A3 A4 X5 X6. uilia.
             - intros i Hi Hr. unfold foot_fake_static in Hi. destruct Hi as [Hi|[Hi|[Hi|[Hi|Hi]]]].
               1-3: apply (FIXfree _ _ INFS); [exact F8q | exact FTq | uilia | exact Hr].
               + apply IMGR; clear -Hi Y11 Y12; uilia.
               + apply (FIXfree _ _ (dtls_member bt st Lc FF W)); [exact D8q | exact DTq | clear -Hi; (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia | exact Hr].
             - intros f k0 i Hf Hi Hr. unfold foot_fword in Hi. destruct (fake_frame_facts bt st Lc FF W f k0 Hf) as (A1 & A2 & A3 & A4 & _).
               apply (FIXfree _ _ INFS); [exact F8q | exact FTq | clear -Hi A1 A2 A4; uilia | exact Hr]. }
    (* [comment removed for export] *)
    split. { change (rep_ialloc bt st' M') with (rep_ialloc bt st M'). eapply rep_ialloc_frame; [exact R11 | uilia | uilia | uilia | uilia |].
             intros i Hi Hr. unfold ialloc_cells, IA_FLAG, IA_INST in Hi. apply IMGR; clear -Hi Y7 Y8 Y9 Y10; uilia. }
    (* [comment removed for export] *)
    assert (SHspc : forall z, SB + SBEG / 8 <= z < SB + (SBEG + KSPACE + PG) / 8 -> M' (Z_to_bv 64 z) = M (Z_to_bv 64 z)).
    { intros z Hz. apply AGZ; [clear -Hz X14 X15; Zlia | clear -Hz DY5 X14 X15; Zlia | clear -Hz F6 SP7 SP8 Hal SP6 MS2; Zlia | clear -Hz I2 IBH X14; Zlia | clear -Hz PD5 X12 X13 X14 X15 LEN ROOM GS0; Zlia | clear -Hz TD5 X1 X2 X14 X15; Zlia | clear -Hz X14 X15; Zlia]. }
    assert (SHsec : forall sc z, In sc (a_sec st) -> SB + sc_map sc / 8 <= z < SB + (sc_map sc + sc_mapsz sc) / 8 -> M' (Z_to_bv 64 z) = M (Z_to_bv 64 z)).
    { intros sc z Hs Hz. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & _). pose proof (FS sc Hs) as Fs'.
      destruct (RNG _ _ (all_ranges_dyn bt st _ (sec_dyn st sc Hs))) as ((_ & _ & _ & _ & B5) & _).
      apply AGZ; [clear -Hz A1 A2; Zlia | clear -Hz DY5 A1 A2; Zlia | clear -Hz Fs' A3 A4 Hal MS2 A1; Zlia | clear -Hz I2 IBH A1; Zlia | clear -Hz PD5 X12 X13 A1 A2 LEN ROOM GS0; Zlia | clear -Hz TD5 X1 X2 A1 A2; Zlia | clear -Hz A1 A2; Zlia]. }
    assert (R12' : rep_shadow bt st ((p, n) :: Lc) M').
    { eapply (rep_shadow_frame_grow bt st Lc); [exact DEF | exact R12 | | | | |].
      - intros g (p' & n' & Hin & Hg). exists p', n'. split; [right; exact Hin | exact Hg].
      - intros c0 Hc0. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _). ulia.
      - intros sc Hs. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). clear -A1 A2 A3 A4 A5 A6 A7. try ceil; unfold PG, AS_HEAPLO, NMAX in *. Ztac.
      - intros c0 i Hc0 Hi Hr. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _).
        unfold foot_shreg, sh_lo in Hi. apply SHspc. clear -Hi Q1 Q2 Q5 Q6 Q8. Zlia.
      - intros sc i Hs Hi Hr. unfold foot_shsec, sh_lo in Hi. destruct Hi as [Hi _]. apply (SHsec sc); [exact Hs | clear -Hi; lia]. }
    split. { destruct R12' as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6). (lazymatch goal with |- ?G => let G' := eval unfold rep_shadow in G in change_no_check G' end).
             change (a_reg st') with (a_reg st). change (quar st') with (quar st). change (a_sec st') with (a_sec st ++ [SCH mp n]).
             split; [exact SH1|]. split; [exact SH2|].
             split. { intros sc g Hs Hg NU. apply in_app_iff in Hs. destruct Hs as [Hs | [<- | []]]; [exact (SH3 sc g Hs Hg NU)|].
                      unfold sc_mapsz, sc_user in Hg, NU. cbn [sc_n sc_map] in Hg, NU. rewrite <- Ep in NU. exact (SHN g Hg NU). }
             split. { intros sc g Hs HQ HU. apply in_app_iff in Hs. destruct Hs as [Hs | [<- | []]]; [exact (SH4 sc g Hs HQ HU)|].
                      exfalso. apply NEWnotQ. unfold sc_user in HQ. cbn [sc_map sc_n] in HQ. rewrite <- Ep in HQ. exact HQ. }
             split; [exact SH5|].
             intros sc g Hs Hg. apply in_app_iff in Hs. destruct Hs as [Hs | [<- | []]]; [exact (SH6 sc g Hs Hg)|].
             cbn [sc_map sc_mapsz sc_n] in Hg. unfold sc_mapsz in Hg. cbn [sc_n] in Hg. apply SHdef. clear -Hg. Zlia. }
    (* [comment removed for export] *)
    split. { destruct R13 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12). (lazymatch goal with |- ?G => let G' := eval unfold rep_ledger in G in change_no_check G' end).
             change (a_dep st') with (a_dep st).
             assert (HOL : forall a, holes bt st' a <-> holes bt st a) by (intros a; (lazymatch goal with |- ?G => let G' := eval unfold holes in G in change_no_check G' end); change (a_reg st') with (a_reg st); am_tauto).
             split. { destruct L1 as (F6l & PF & FOK & FPW & FH). exists F6l.
                      split. { eapply Permutation_trans; [exact PM|]. eapply Permutation_trans; [apply Permutation_cons; [reflexivity | exact PF] |].
                               (lazymatch goal with |- ?G => let G' := eval unfold dyn_maps in G in change_no_check G' end). change (a_sec st') with (a_sec st ++ [SCH mp n]). change (a_dep st') with (a_dep st). rewrite map_app.
                               change (List.map (fun s : schunk => (Z_to_bv 64 (sc_map s), Z_to_bv 64 (sc_mapsz s))) [SCH mp n]) with [(Z_to_bv 64 mp, Z_to_bv 64 (sec_map_size n))].
                               rewrite !(app_assoc F6l (bt_maps0 bt)). apply perm_insert_mid. }
                      split; [exact FOK|]. split; [exact FPW|]. intros a Ha. rewrite (HOL a). exact (FH a Ha). }
             assert (NF : forall P : Prop, ~ (false = true /\ P)) by (intros P [Hx _]; discriminate Hx).
             split. { intros a. rewrite (NA a), (L2 a), (HOL a). (lazymatch goal with |- ?G => let G' := eval unfold committed in G in change_no_check G' end). change (a_reg st') with (a_reg st). change (a_nres st') with (if grow then a_nres st + 2 ^ 14 else a_nres st).
                      destruct grow.
                      - split.
                        + intros [[A [B HB]] C]. split; [exact A|]. split; [| exact HB]. intros [X|X]; [apply B; left; exact X|].
                          destruct (Z.lt_ge_cases a (bt_ptrarr bt + 8 * a_nres st)); [apply B; right; lia | apply C; split; [reflexivity | lia]].
                        + intros [A [B HB]]. split; [split; [exact A | split; [intros X; apply B; destruct X as [X|X]; [left; exact X | right; lia] | exact HB]] | intros [_ X]; apply B; right; lia].
                      - split; [intros [[A B] _]; split; [exact A | exact B] | intros [A B]; split; [split; [exact A | exact B] | apply NF]]. }
             split. { intros a. rewrite (LZ a), (L3 a), (HOL a). (lazymatch goal with |- ?G => let G' := eval unfold committed in G in change_no_check G' end). change (a_reg st') with (a_reg st). change (a_nres st') with (if grow then a_nres st + 2 ^ 14 else a_nres st).
                      (* [comment removed for export] *)
                      assert (STORE8 : forall b, In b (dp_storeblocks (a_dep st)) -> b + 2 ^ 23 <= bt_ptrarr bt \/ bt_ptrarr bt + 2 ^ 23 <= b).
                      { intros b Hb. pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W IN8 (store_dyn st b Hb)) as Q. hnf in Q. cbn in Q. lia. }
                      destruct grow.
                      - split.
                        + intros [[[A [B HB]]|S] C]; [left | right; exact S]. split; [exact A|]. split; [| exact HB]. intros [X|X]; [apply B; left; exact X|].
                          destruct (Z.lt_ge_cases a (bt_ptrarr bt + 8 * a_nres st)); [apply B; right; lia | apply C; split; [reflexivity | lia]].
                        + intros [[A [B HB]]|S].
                          * split; [left; split; [exact A | split; [intros X; apply B; destruct X as [X|X]; [left; exact X | right; lia] | exact HB]] | intros [_ X]; apply B; right; lia].
                          * split; [right; exact S|]. destruct S as (b & Hb & Rb). intros [_ X]. cbn in EGS. destruct (STORE8 b Hb) as [D|D]; clear -Rb X D LEN S3 ROOM EGS; lia.
                      - split; [intros [[[A B]|S] _]; [left; split; [exact A | exact B] | right; exact S] | intros [[A B]|S]; (split; [| apply NF]); [left; split; [exact A | exact B] | right; exact S]]. }
             split; [exact FL'|]. unfold alloc_top in L10 |- *. rewrite E1, E2, E3, E4, E6, E5. repeat (split; [assumption|]). exact NP'. }
    (* [comment removed for export] *)
    split. { destruct R14 as (Bu1 & Bu2 & Bu3 & Bu4 & Bu5 & Bu6 & Bu7 & Bu8 & Bu9). (lazymatch goal with |- ?G => let G' := eval unfold rep_budget in G in change_no_check G' end).
             change (a_aa st') with (a_aa st ++ sec_naa mp n). change (a_reg st') with (a_reg st). change (a_sec st') with (a_sec st ++ [SCH mp n]).
             change (a_dep st') with (a_dep st). change (a_shsec st') with (a_shsec st). change (a_nres st') with (if grow then a_nres st + 2 ^ 14 else a_nres st).
             assert (RA : range_allowed (a_aa st ++ sec_naa mp n) (sh_lo mp) (sh_hi mp (sec_map_size n))).
             { apply range_allowed_hull; clear -SHB1 SHB2; unfold sh_lo, sh_hi in *; ulia. }
             split. { apply A_wf_sec_naa; [exact Bu1 | lia]. }
             split; [exact MI|].
             split; [intros lo0 hi0 Hsh; apply range_allowed_app; exact (Bu3 lo0 hi0 Hsh)|].
             split. { intros p0 n0 [E | Hin]; [| apply range_allowed_app; exact (Bu4 p0 n0 Hin)]. injection E as <- <-.
                      eapply range_allowed_sub; [exact RA | |]; (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, sh_hi in G in change_no_check G' end); apply Z.add_le_mono_l; apply Z.div_le_mono; clear -P1 P2; ulia. }
             split; [intros c0 Hc0; destruct (Bu5 c0 Hc0) as [Xu5 Yu5]; split; apply range_allowed_app; [exact Xu5 | exact Yu5]|].
             split. { intros sc Hs. apply in_app_iff in Hs. destruct Hs as [Hs | [<- | []]]; [apply range_allowed_app; exact (Bu6 sc Hs)|]. (lazymatch goal with |- ?G => let G' := eval cbn [sc_map] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold sc_mapsz in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [sc_n] in G in change_no_check G' end). exact RA. }
             split; [intros b0 Hb0; apply range_allowed_app; exact (Bu7 b0 Hb0)|].
             change (prim_charge st') with (prim_charge st). change (depot_charge st') with (depot_charge st).
             (lazymatch goal with |- ?G => let G' := eval unfold sec_charge in G in change_no_check G' end). change (a_sec st') with (a_sec st ++ [SCH mp n]). rewrite secsum_app2. unfold sc_mapsz at 2. (lazymatch goal with |- ?G => let G' := eval cbn [sc_n sc_map] in G in change_no_check G' end).
             fold (sec_charge st). unfold sec_charge in Bu8 |- *. rewrite A_bytes_app. (lazymatch goal with |- ?G => let G' := eval cbn [A_bytes sec_naa fst snd] in G in change_no_check G' end).
             split; [destruct grow; cbn in EGS; clear -EAG Bu8 EGS; unfold sec_hull in *; lia|].
             (* [comment removed for export] *)
             intros sc Hs. apply in_app_iff in Hs. apply in_app_iff. destruct Hs as [Hs | [<- | []]]; [left; exact (Bu9 sc Hs) | right; left; reflexivity]. }
    (* [comment removed for export] *)
    split. { intros p0 n0 [E | Hin].
             - injection E as <- <-. split; [eapply writableZ_sub; [exact WM | clear -P1; ulia | clear -P2; ulia] |].
               apply writableZ_of_def. intros i Hi. apply SHdef. unfold sh_lo, sh_hi in Hi. clear -Hi P1 P2. Zlia.
             - destruct (R15 p0 n0 Hin) as [W1 W2]. split; [frW DEF W1 | frW DEF W2]. }
    split. { intros f' k' Hin'. frW DEF (R16 f' k' Hin'). }
    split. { eapply (cellZ_frame _ _ _ _ _ _ R17); [uilia | uilia |]. intros i Hi. apply IMGR; clear -Hi Y13 Y14; uilia. }
    split. { eapply (cellZ_frame _ _ _ _ _ _ R18); [uilia | uilia |]. intros i Hi. apply IMGR; clear -Hi Y15 Y16; uilia. }
    exact (rep_last_keep bt _ _ M M' DEF R19 (fun H => H)).
  Qed.
End S.
