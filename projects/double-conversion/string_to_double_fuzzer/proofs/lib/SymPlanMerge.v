(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import SymExec3 SymExec3Sound SymRun3 SymDrive3 SymPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module SPM.
Import SX2. Import SX2S. Import SP.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition iv_sub (l h : Z) (ivs : list (Z * Z)) : Prop :=
  exists a b, In (a, b) ivs /\ (a <= l)%Z /\ (h <= b)%Z.

Lemma iv_inter_spec : forall lo hi ivs l h,
  In (l, h) (iv_inter lo hi ivs) -> (lo <= l)%Z /\ (h <= hi)%Z /\ (l < h)%Z /\ iv_sub l h ivs.
Proof.
  intros lo hi ivs. induction ivs as [|[a b] r IH]; intros l h Hin; [destruct Hin|].
  cbn [iv_inter] in Hin.
  destruct (Z.ltb (Z.max lo a) (Z.min hi b)) eqn:Hlt.
  - destruct Hin as [Heq|Hin].
    + injection Heq as <- <-. apply Z.ltb_lt in Hlt.
      split; [lia|]. split; [lia|]. split; [lia|]. exists a, b. split; [left; reflexivity|]. lia.
    + destruct (IH l h Hin) as (A & B & C & (a' & b' & Hin' & D & E0)).
      repeat (split; [assumption|]). exists a', b'. split; [right; exact Hin'|]. lia.
  - destruct (IH l h Hin) as (A & B & C & (a' & b' & Hin' & D & E0)).
    repeat (split; [assumption|]). exists a', b'. split; [right; exact Hin'|]. lia.
Qed.

Lemma ivs_inter_spec : forall ps ivs l h,
  In (l, h) (ivs_inter ps ivs) ->
  (exists lo hi, In (lo, hi) ps /\ (lo <= l)%Z /\ (h <= hi)%Z) /\ (l < h)%Z /\ iv_sub l h ivs.
Proof.
  intros ps ivs. induction ps as [|[lo hi] r IH]; intros l h Hin; [destruct Hin|].
  cbn [ivs_inter] in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - destruct (iv_inter_spec lo hi ivs l h Hin) as (A & B & C & D).
    split; [exists lo, hi; split; [left; reflexivity|]; lia|]. split; assumption.
  - destruct (IH l h Hin) as ((lo' & hi' & Hin' & A & B) & C & D).
    split; [exists lo', hi'; split; [right; exact Hin'|]; lia|]. split; assumption.
Qed.

Lemma iv_sub_weaken : forall l h l' h' ivs, iv_sub l h ivs -> (l <= l')%Z -> (h' <= h)%Z -> iv_sub l' h' ivs.
Proof. intros l h l' h' ivs (a & b & Hin & A & B) H1 H2. exists a, b. split; [exact Hin|]. lia. Qed.

(* [comment removed for export] *)
Lemma pieces_spec : forall (others : list (list kentry * list (Z * Z))) acc l h,
  In (l, h) (fold_left (fun ps o => ivs_inter ps (snd o)) others acc) ->
  (exists lo hi, In (lo, hi) acc /\ (lo <= l)%Z /\ (h <= hi)%Z)
  /\ forall o, In o others -> iv_sub l h (snd o).
Proof.
  intros others. induction others as [|o r IH]; intros acc l h Hin.
  - cbn in Hin. split; [exists l, h; split; [exact Hin|]; lia|]. intros o' [].
  - cbn [fold_left] in Hin. destruct (IH _ l h Hin) as ((lo & hi & Hacc & A & B) & Hall).
    destruct (ivs_inter_spec acc (snd o) lo hi Hacc) as ((lo' & hi' & Hin' & A' & B') & C & D).
    split; [exists lo', hi'; split; [exact Hin'|]; lia|].
    intros o' [<-|Ho'].
    + eapply iv_sub_weaken; [exact D| lia | lia].
    + apply Hall. exact Ho'.
Qed.

Lemma iv_covered_spec : forall lo hi ivs, iv_covered lo hi ivs = true -> iv_sub lo hi ivs.
Proof.
  intros lo hi ivs. induction ivs as [|[a b] r IH]; cbn [iv_covered]; intros H; [discriminate|].
  destruct (Z.leb a lo && Z.leb hi b)%bool eqn:E.
  - apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    exists a, b. split; [left; reflexivity|]. lia.
  - destruct (IH H) as (a' & b' & Hin & A & B). exists a', b'. split; [right; exact Hin|]. lia.
Qed.

Lemma kimg_ivs_In : forall k a b, In (a, b) (kimg_ivs k) -> In (KImg a b) k.
Proof.
  intros k a b. induction k as [|K r IH]; cbn [kimg_ivs]; intros H; [destruct H|].
  destruct K; try (right; apply IH; exact H).
  destruct H as [H|H]; [injection H as <- <-; left; reflexivity | right; apply IH; exact H].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma kimg_sub_ok : forall E M a b l h,
  kentry_ok segs E M (KImg a b) -> (a <= l)%Z -> (h <= b)%Z ->
  kentry_ok segs E M (KImg l h).
Proof.
  intros E M a b l h (A & B & C) H1 H2. cbn [kentry_ok]. split; [lia|]. split; [lia|].
  intros i Hi. apply C. lia.
Qed.

(* [comment removed for export] *)
Lemma img_lit_ok : forall E M a b off w iv,
  kentry_ok segs E M (KImg a b) -> (a <= off)%Z -> (off + Z.of_nat w <= b)%Z -> (1 <= w)%nat -> (w <= 8)%nat ->
  img_lit segs off w = Some iv ->
  kentry_ok segs E M (KWord (SA (ELit 0) off) w iv).
Proof.
  intros E M a b off w iv (A & B & C) H1 H2 Hw1 Hw8 Hil.
  unfold img_lit in Hil. destruct (img_bytes segs off w) as [zs|] eqn:Himg; [|discriminate]. injection Hil as <-.
  cbn [kentry_ok]. split; [exact Hw8|].
  assert (Hfl : flat E (SA (ELit 0) off) (Z.of_nat w)).
  { unfold flat. rewrite estart_lit0. lia. }
  split; [exact Hfl|].
  pose proof (flat_u E _ _ Hfl) as Hu. rewrite estart_lit0 in Hu.
  destruct (rdn_img segs M w (adenot E (SA (ELit 0) off)) zs) as (bs & Hbs & Hmap).
  - rewrite Hu. lia.
  - intros j Hj. rewrite Hu. apply C. lia.
  - rewrite Hu. exact Himg.
  - rewrite Hbs. f_equal. cbn [edenot]. unfold lit_of_bytes. rewrite <- Hmap, zbytes_map.
    symmetry. apply word_to_le_bytes_of_lez; [exact (rdn_length _ _ _ _ _ Hbs) | exact Hw8].
Qed.

(* [comment removed for export] *)
Lemma lit_eqb_denot : forall E a b, lit_eqb a b = true -> edenot E a = edenot E b.
Proof.
  intros E a b H. destruct a; try discriminate. destruct b; try discriminate. cbn [lit_eqb] in H.
  apply Z.eqb_eq in H. cbn [edenot]. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with two64. exact H.
Qed.

Lemma kword_val_irrel : forall E M a w v v',
  edenot E v = edenot E v' -> kentry_ok segs E M (KWord a w v) -> kentry_ok segs E M (KWord a w v').
Proof. intros E M a w v v' Heq (A & B & C). cbn [kentry_ok]. rewrite <- Heq. split; [exact A|]. split; assumption. Qed.

(* [comment removed for export] *)
Lemma cell_view_sound : forall E M k b off w v,
  know_ok segs E M k -> (1 <= w)%nat -> (w <= 8)%nat ->
  cell_view segs k (kimg_ivs k) b off w = Some v ->
  kentry_ok segs E M (KWord (SA b off) w v).
Proof.
  intros E M k b off w v HK Hw1 Hw8.
  assert (GEN : forall k', incl k' k ->
            cell_view segs k' (kimg_ivs k) b off w = Some v -> kentry_ok segs E M (KWord (SA b off) w v)).
  { intros k'. induction k' as [|K r IH]; intros Hincl Hcv.
    - cbn [cell_view] in Hcv. destruct b as [z0| | | | | | |]; try discriminate.
      destruct (Z.eqb z0 0 && iv_covered off (off + Z.of_nat w) (kimg_ivs k))%bool eqn:Hc; [|discriminate].
      apply andb_prop in Hc as [Hz Hcov]. apply Z.eqb_eq in Hz. subst z0.
      apply iv_covered_spec in Hcov as (a & b' & Hin & A & B).
      apply kimg_ivs_In in Hin. pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HKi.
      eapply img_lit_ok; try eassumption.
    - cbn [cell_view] in Hcv.
      assert (Hr : incl r k) by (intros x Hx; apply Hincl; right; exact Hx).
      destruct K as [[b' off'] w' v'| | | | | | |]; try (apply IH; assumption).
      destruct (expr_eqb b b' && Z.eqb off off' && Nat.eqb w w')%bool eqn:Heq; [|apply IH; assumption].
      apply andb_prop in Heq as [Heq Hw]. apply andb_prop in Heq as [Hb Ho].
      apply expr_eqb_eq in Hb. apply Z.eqb_eq in Ho. apply Nat.eqb_eq in Hw. subst b' off' w'.
      injection Hcv as <-. apply (proj1 (Forall_forall _ _) HK). apply Hincl. left. reflexivity. }
  apply GEN. intros x Hx; exact Hx.
Qed.

(* [comment removed for export] *)
Lemma val_range_sound : forall E M k v lo hi,
  know_ok segs E M k -> val_range k v = Some (lo, hi) ->
  (lo <= bv_unsigned (edenot E v) <= hi)%Z.
Proof.
  intros E M k v lo hi HK Hv. unfold val_range in Hv.
  destruct v as [z| | | | | | |];
    first [ injection Hv as <- <-; cbn [edenot]; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with two64; lia
          | exact (erange_sound segs E M k _ lo hi HK Hv) ].
Qed.

(* [comment removed for export] *)
Lemma ranges_union_sound : forall ks vs lo hi i k v E M,
  ranges_union ks vs = Some (lo, hi) ->
  nth_error ks i = Some k -> nth_error vs i = Some v ->
  know_ok segs E M k ->
  (lo <= bv_unsigned (edenot E v) <= hi)%Z.
Proof.
  intros ks. induction ks as [|k0 kr IH]; intros vs lo hi i k v E M Hru Hk Hv HK; [destruct i; discriminate|].
  cbn [ranges_union] in Hru.
  destruct kr as [|k1 kr'].
  - destruct vs as [|v0 [|v1 vr']]; [discriminate| | cbn in Hru; destruct (val_range k0 v0) as [[? ?]|]; discriminate].
    destruct i as [|i]; [|destruct i; discriminate]. cbn in Hk, Hv. injection Hk as ->. injection Hv as ->.
    exact (val_range_sound E M k v lo hi HK Hru).
  - destruct vs as [|v0 vr]; [discriminate|].
    destruct (val_range k0 v0) as [[a b]|] eqn:Hvr; [|discriminate].
    destruct (ranges_union (k1 :: kr') vr) as [[c d]|] eqn:Hrr; [|discriminate].
    injection Hru as <- <-.
    destruct i as [|i].
    + cbn in Hk, Hv. injection Hk as ->. injection Hv as ->.
      pose proof (val_range_sound E M k v a b HK Hvr). lia.
    + cbn in Hk, Hv. pose proof (IH vr c d i k v E M Hrr Hk Hv HK). lia.
Qed.

(* [comment removed for export] *)
Lemma cell_views_nth : forall others b off w vs i k ivs,
  cell_views segs others b off w = Some vs -> nth_error others i = Some (k, ivs) ->
  exists v, nth_error vs i = Some v /\ cell_view segs k ivs b off w = Some v.
Proof.
  intros others b off w. induction others as [|[k0 ivs0] r IH]; intros vs i k ivs Hcv Hn; [destruct i; discriminate|].
  cbn [cell_views] in Hcv.
  destruct (cell_view segs k0 ivs0 b off w) as [v0|] eqn:Hv0; [|discriminate].
  destruct (cell_views segs r b off w) as [vr|] eqn:Hvr; [|discriminate]. injection Hcv as <-.
  destruct i as [|i].
  - cbn in Hn. injection Hn as <- <-. exists v0. split; [reflexivity | exact Hv0].
  - cbn in Hn. destruct (IH vr i k ivs eq_refl Hn) as (v & A & B). exists v. split; [exact A | exact B].
Qed.
Lemma cell_views_length : forall others b off w vs,
  cell_views segs others b off w = Some vs -> length vs = length others.
Proof.
  intros others b off w. induction others as [|[k0 ivs0] r IH]; intros vs Hcv.
  - cbn in Hcv. injection Hcv as <-. reflexivity.
  - cbn [cell_views] in Hcv. destruct (cell_view segs k0 ivs0 b off w); [|discriminate].
    destruct (cell_views segs r b off w) as [vr|] eqn:Hvr; [|discriminate]. injection Hcv as <-. cbn. f_equal. apply IH. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma img_cells_from_spec : forall k lo hi others K,
  In K (img_cells_from segs k lo hi others) ->
  exists off w iv, K = KWord (SA (ELit 0) off) w iv /\ (1 <= w)%nat /\ (w <= 8)%nat /\ (lo <= off)%Z /\ (off + Z.of_nat w <= hi)%Z
    /\ img_lit segs off w = Some iv
    /\ forall o, In o others -> exists v, cell_view segs (fst o) (snd o) (ELit 0) off w = Some v /\ lit_eqb v iv = true.
Proof.
  intros k lo hi others K. induction k as [|K0 r IH]; cbn [img_cells_from]; intros Hin; [destruct Hin|].
  destruct K0 as [[[z0| | | | | | |] off] w [z| | | | | | |]| | | | | | |]; try (apply IH; exact Hin).
  destruct (Z.eqb z0 0 && Nat.leb 1 w && Nat.leb w 8 && Z.leb lo off && Z.leb (off + Z.of_nat w) hi)%bool eqn:Hc; [|apply IH; exact Hin].
  destruct (img_lit segs off w) as [iv|] eqn:Hil; [|apply IH; exact Hin].
  destruct (lit_eqb iv (ELit z) && forallb _ others)%bool eqn:Hc2; [|apply IH; exact Hin].
  destruct Hin as [<-|Hin]; [|apply IH; exact Hin].
  apply andb_prop in Hc as [Hc H5]. apply andb_prop in Hc as [Hc H4]. apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
  apply Nat.leb_le in H2. apply Nat.leb_le in H3. apply Z.leb_le in H4. apply Z.leb_le in H5.
  apply andb_prop in Hc2 as [_ Hall].
  exists off, w, iv. repeat (split; [first [reflexivity | assumption]|]).
  intros o Ho. pose proof (proj1 (forallb_forall _ _) Hall o Ho) as X. cbn beta in X.
  destruct (cell_view segs (fst o) (snd o) (ELit 0) off w) as [v|]; [|discriminate]. exists v. split; [reflexivity | exact X].
Qed.

Lemma img_cells_spec : forall lo hi others K,
  In K (img_cells segs lo hi others) ->
  exists off w iv, K = KWord (SA (ELit 0) off) w iv /\ (1 <= w)%nat /\ (w <= 8)%nat /\ (lo <= off)%Z /\ (off + Z.of_nat w <= hi)%Z
    /\ img_lit segs off w = Some iv
    /\ forall o, In o others -> exists v, cell_view segs (fst o) (snd o) (ELit 0) off w = Some v /\ lit_eqb v iv = true.
Proof.
  intros lo hi others K Hin. unfold img_cells in Hin. apply in_flat_map in Hin as (o & _ & Hin).
  exact (img_cells_from_spec _ _ _ _ _ Hin).
Qed.

(* [comment removed for export] *)
Lemma kentry_eqb_eq : forall x y, kentry_eqb x y = true -> x = y.
Proof.
  intros x y H. destruct x, y; cbn [kentry_eqb] in H; try discriminate;
    repeat match goal with
      | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
      end;
    repeat match goal with
      | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
      | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
      | H : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in H
      | H : saddr_eqb _ _ = true |- _ => apply saddr_eqb_eq in H
      end; subst; reflexivity.
Qed.

Lemma kn_vars_lt_In : forall b kn K, kn_vars_lt b kn = true -> In K kn -> kentry_vars_lt b K = true.
Proof.
  intros b kn K. induction kn as [|K0 r IH]; intros Hv Hin; [destruct Hin|].
  cbn [kn_vars_lt] in Hv. apply andb_prop in Hv as [H0 Hr].
  destruct Hin as [->|Hin]; [exact H0 | apply IH; assumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sel_first (p : expr * list expr) : expr := fst p.
Definition sel_other (i : nat) (p : expr * list expr) : expr := nth i (snd p) (ELit 0).

Theorem merge_kn_sound : forall k1 k1all others vbase j kn' j' tr,
  merge_kn segs k1 k1all others vbase j = (kn', j', tr) ->
  (forall o, In o others -> snd o = kimg_ivs (fst o)) ->
  forall (first : bool) (i : nat) kst (nb : nat) E E' M,
  (if first then kst = k1all /\ incl k1 k1all else nth_error others i = Some (kst, kimg_ivs kst)) ->
  know_ok segs E M kst ->
  kn_vars_lt nb kst = true ->
  env_agree nb E E' ->
  (forall t p, nth_error tr t = Some p ->
     ev E' (vbase + j + t)%nat = edenot E (if first then sel_first p else sel_other i p)) ->
  know_ok segs E' M kn'.
Proof.
  intros k1. induction k1 as [|K r IH]; intros k1all others vbase j kn' j' tr Hm Hivs first i kst nb E E' M Hst HK Hvl Hag Htr.
  { cbn in Hm. injection Hm as <- <- <-. constructor. }
  cbn [merge_kn] in Hm.
  (* [comment removed for export] *)
  assert (Hsub : first = true -> In K kst /\ incl r k1all).
  { intros ->. destruct Hst as [-> Hincl]. split; [apply Hincl; left; reflexivity | intros x Hx; apply Hincl; right; exact Hx]. }
  assert (HstR : if first then kst = k1all /\ incl r k1all else nth_error others i = Some (kst, kimg_ivs kst)).
  { destruct first; [destruct Hst as [A B]; split; [exact A | intros x Hx; apply B; right; exact Hx] | exact Hst]. }
  assert (KOK : forall K', In K' kst -> kentry_ok segs E' M K').
  { intros K' HinK. pose proof (know_ok_agree segs nb E E' M kst Hag Hvl HK) as HK'.
    exact (proj1 (Forall_forall _ _) HK' K' HinK). }
  assert (Hoth : first = false -> In (kst, kimg_ivs kst) others).
  { intros ->. eapply nth_error_In. exact Hst. }
  destruct (forallb (fun o => existsb (kentry_eqb K) (fst o)) others) eqn:Hallb.
  { (* [comment removed for export] *)
    destruct (merge_kn segs r k1all others vbase j) as [[kr jr] trr] eqn:Hrec. injection Hm as <- <- <-.
    constructor; [|eapply IH; eassumption].
    apply KOK. destruct first.
    - apply (proj1 (Hsub eq_refl)).
    - pose proof (proj1 (forallb_forall _ _) Hallb _ (Hoth eq_refl)) as X. cbn [fst] in X.
      apply existsb_exists in X as (K' & HinK' & Heq). apply kentry_eqb_eq in Heq. subst K'. exact HinK'. }
  destruct K as [[b off] w v|a n|a n kb|lo hi|ae am|re rlo rhi|wa wn|da1 dn1 da2 dn2];
    try (eapply IH; eassumption).
  - (* [comment removed for export] *)
    destruct (Nat.leb 1 w && Nat.leb w 8)%bool eqn:Hw; [|eapply IH; eassumption].
    apply andb_prop in Hw as [Hw1 Hw8]. apply Nat.leb_le in Hw1. apply Nat.leb_le in Hw8.
    destruct (cell_views segs others b off w) as [vs|] eqn:Hcv; [|eapply IH; eassumption].
    (* [comment removed for export] *)
    assert (VIEW : exists sv, (if first then sv = v else nth_error vs i = Some sv /\ cell_view segs kst (kimg_ivs kst) b off w = Some sv)
                              /\ kentry_ok segs E M (KWord (SA b off) w sv)).
    { destruct first.
      - exists v. split; [reflexivity|]. exact (proj1 (Forall_forall _ _) HK _ (proj1 (Hsub eq_refl))).
      - destruct (cell_views_nth others b off w vs i kst (kimg_ivs kst) Hcv Hst) as (sv & A & B).
        exists sv. split; [split; [exact A | exact B]|]. eapply cell_view_sound; eassumption. }
    destruct VIEW as (sv & Hsv & SVOK).
    assert (SVOK' : kentry_ok segs E' M (KWord (SA b off) w sv)).
    { (* [comment removed for export] *)
      destruct first.
      - subst sv. apply KOK. apply (proj1 (Hsub eq_refl)).
      - destruct Hsv as [_ Hcell].
        (* [comment removed for export] *)
        clear - Hcell HK Hvl Hag SVOK Hw1 Hw8.
        assert (GEN : forall k', incl k' kst -> cell_view segs k' (kimg_ivs kst) b off w = Some sv ->
                      kentry_ok segs E' M (KWord (SA b off) w sv)).
        { intros k'. induction k' as [|K rr IHk]; intros Hincl Hc.
          - cbn [cell_view] in Hc. destruct b as [z0| | | | | | |]; try discriminate.
            destruct (Z.eqb z0 0 && iv_covered off (off + Z.of_nat w) (kimg_ivs kst))%bool eqn:Hc'; [|discriminate].
            apply andb_prop in Hc' as [Hz Hcov]. apply Z.eqb_eq in Hz. subst z0.
            apply iv_covered_spec in Hcov as (a & b' & Hin & A & B). apply kimg_ivs_In in Hin.
            pose proof (know_ok_agree segs nb E E' M kst Hag Hvl HK) as HK'.
            eapply img_lit_ok; try eassumption. exact (proj1 (Forall_forall _ _) HK' _ Hin).
          - cbn [cell_view] in Hc. assert (Hr : incl rr kst) by (intros x Hx; apply Hincl; right; exact Hx).
            destruct K as [[b' off'] w' v'| | | | | | |]; try (apply IHk; assumption).
            destruct (expr_eqb b b' && Z.eqb off off' && Nat.eqb w w')%bool eqn:Heq; [|apply IHk; assumption].
            apply andb_prop in Heq as [Heq Hw]. apply andb_prop in Heq as [Hb Ho].
            apply expr_eqb_eq in Hb. apply Z.eqb_eq in Ho. apply Nat.eqb_eq in Hw. subst b' off' w'.
            injection Hc as <-.
            pose proof (know_ok_agree segs nb E E' M kst Hag Hvl HK) as HK'.
            apply (proj1 (Forall_forall _ _) HK'). apply Hincl. left. reflexivity. }
        apply (GEN kst); [intros x Hx; exact Hx | exact Hcell]. }
    destruct (forallb (expr_eqb v) vs) eqn:Hsame.
    + (* [comment removed for export] *)
      destruct (merge_kn segs r k1all others vbase j) as [[kr jr] trr] eqn:Hrec. injection Hm as <- <- <-.
      constructor; [|eapply IH; eassumption].
      assert (Hv : sv = v).
      { destruct first; [exact Hsv|]. destruct Hsv as [Hn _].
        apply nth_error_In in Hn. pose proof (proj1 (forallb_forall _ _) Hsame sv Hn) as X. apply expr_eqb_eq in X. symmetry. exact X. }
      rewrite <- Hv. exact SVOK'.
    + (* [comment removed for export] *)
      destruct (merge_kn segs r k1all others vbase (S j)) as [[kr jr] trr] eqn:Hrec.
      assert (HX : ev E' (vbase + j)%nat = edenot E sv).
      { assert (T0 : nth_error tr 0 = Some (v, vs)).
        { destruct (ranges_union (k1all :: map fst others) (v :: vs)) as [[lo hi]|]; injection Hm as <- <- <-; reflexivity. }
        pose proof (Htr 0%nat (v, vs) T0) as X. rewrite Nat.add_0_r in X. rewrite X.
        destruct first; [rewrite Hsv; reflexivity|]. destruct Hsv as [Hn _]. unfold sel_other. cbn [snd].
        rewrite (nth_error_nth _ _ _ Hn). reflexivity. }
      assert (KW : kentry_ok segs E' M (KWord (SA b off) w (EVar (vbase + j)))).
      { eapply kword_val_irrel; [|exact SVOK']. cbn [edenot]. rewrite HX. symmetry.
        apply (edenot_agree nb); [exact Hag|].
        (* [comment removed for export] *)
        destruct first.
        + pose proof (Hsub eq_refl) as [HinK _]. subst sv.
          pose proof (kn_vars_lt_In _ _ _ Hvl HinK) as X. cbn [kentry_vars_lt] in X. apply andb_prop in X as [_ X]. exact X.
        + destruct Hsv as [_ Hcell].
          assert (GEN : forall k', incl k' kst -> cell_view segs k' (kimg_ivs kst) b off w = Some sv -> expr_vars_lt nb sv = true).
          { intros k'. induction k' as [|K0 rr IHk]; intros Hincl Hc.
            - cbn [cell_view] in Hc. destruct b as [z0| | | | | | |]; try discriminate.
              destruct (Z.eqb z0 0 && iv_covered off (off + Z.of_nat w) (kimg_ivs kst))%bool; [|discriminate].
              unfold img_lit in Hc. destruct (img_bytes segs off w); [|discriminate]. injection Hc as <-. reflexivity.
            - cbn [cell_view] in Hc. assert (Hr : incl rr kst) by (intros x Hx; apply Hincl; right; exact Hx).
              destruct K0 as [[b' off'] w' v'| | | | | | |]; try (apply IHk; assumption).
              destruct (expr_eqb b b' && Z.eqb off off' && Nat.eqb w w')%bool eqn:Heq; [|apply IHk; assumption].
              injection Hc as ->.
              assert (HinK : In (KWord (SA b' off') w' sv) kst) by (apply Hincl; left; reflexivity).
              pose proof (kn_vars_lt_In _ _ _ Hvl HinK) as X. cbn [kentry_vars_lt] in X. apply andb_prop in X as [_ X]. exact X. }
          apply (GEN kst); [intros x Hx; exact Hx | exact Hcell]. }
      assert (REST : know_ok segs E' M kr).
      { eapply (IH k1all others vbase (S j) kr jr trr Hrec Hivs first i kst nb E E' M HstR HK Hvl Hag).
        intros t p Hp.
        assert (T : nth_error tr (S t) = Some p).
        { destruct (ranges_union (k1all :: map fst others) (v :: vs)) as [[lo hi]|]; injection Hm as <- <- <-; exact Hp. }
        rewrite <- (Htr (S t) p T). f_equal. lia. }
      destruct (ranges_union (k1all :: map fst others) (v :: vs)) as [[lo hi]|] eqn:Hru; injection Hm as <- <- <-.
      * constructor; [exact KW|]. constructor; [|exact REST].
        (* [comment removed for export] *)
        cbn [kentry_ok edenot]. rewrite HX.
        destruct first.
        -- subst sv. destruct Hst as [Hk1 _]. rewrite Hk1 in HK.
           exact (ranges_union_sound (k1all :: map fst others) (v :: vs) lo hi 0 k1all v E M Hru eq_refl eq_refl HK).
        -- destruct Hsv as [Hn _].
           eapply (ranges_union_sound (k1all :: map fst others) (v :: vs) lo hi (S i) kst sv E M Hru); [| exact Hn | exact HK].
           cbn [nth_error]. rewrite nth_error_map, Hst. reflexivity.
      * constructor; [exact KW | exact REST].
  - (* [comment removed for export] *)
    destruct (merge_kn segs r k1all others vbase j) as [[kr jr] trr] eqn:Hrec. injection Hm as <- <- <-.
    apply Forall_app. split; [|apply Forall_app; split; [|eapply IH; eassumption]].
    + (* [comment removed for export] *)
      apply Forall_forall. intros K HinK. apply in_map_iff in HinK as ([l h] & <- & Hin). cbn [fst snd].
      destruct (pieces_spec others [(lo, hi)] l h Hin) as ((lo' & hi' & Hacc & A & B) & Hall).
      destruct Hacc as [Hacc|[]]. injection Hacc as <- <-.
      destruct first.
      * eapply kimg_sub_ok; [apply KOK; apply (proj1 (Hsub eq_refl)) | exact A | exact B].
      * destruct (Hall _ (Hoth eq_refl)) as (a & b' & Hin' & A' & B'). cbn [snd] in Hin'.
        apply kimg_ivs_In in Hin'.
        eapply kimg_sub_ok; [apply KOK; exact Hin' | exact A' | exact B'].
    + (* [comment removed for export] *)
      apply Forall_forall. intros K HinK.
      destruct (img_cells_spec lo hi others K HinK) as (off & w & iv & -> & Hw1 & Hw8 & A & B & Hil & Hall).
      destruct first.
      * eapply img_lit_ok; [apply KOK; apply (proj1 (Hsub eq_refl)) | exact A | exact B | exact Hw1 | exact Hw8 | exact Hil].
      * destruct (Hall _ (Hoth eq_refl)) as (v & Hcv & Hle). cbn [fst snd] in Hcv.
        pose proof (know_ok_agree segs nb E E' M kst Hag Hvl HK) as HK'.
        eapply kword_val_irrel; [apply (lit_eqb_denot E'); exact Hle|].
        eapply cell_view_sound; [exact HK' | exact Hw1 | exact Hw8 | exact Hcv].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ext_cells (E : env) (vbase : nat) (ws : list word) : env :=
  Env (fun n => if Nat.leb vbase n then nth (n - vbase) ws (ev E n) else ev E n) (eb E).
Lemma ext_cells_agree : forall E vbase ws, env_agree vbase E (ext_cells E vbase ws).
Proof.
  intros E vbase ws. split; [|reflexivity]. intros n Hn. cbn [ext_cells ev].
  destruct (Nat.leb_spec vbase n); [lia | reflexivity].
Qed.
Lemma ext_cells_at : forall E vbase ws t w,
  nth_error ws t = Some w -> ev (ext_cells E vbase ws) (vbase + t)%nat = w.
Proof.
  intros E vbase ws t w H. cbn [ext_cells ev].
  destruct (Nat.leb_spec vbase (vbase + t)); [|lia].
  replace (vbase + t - vbase)%nat with t by lia. exact (nth_error_nth _ _ _ H).
Qed.

Lemma expr_vars_lt_mono : forall b b' e, (b <= b')%nat -> expr_vars_lt b e = true -> expr_vars_lt b' e = true.
Proof.
  intros b b' e Hle. induction e; cbn [expr_vars_lt]; intros H; try reflexivity; try exact H;
    repeat match goal with
      | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
      end;
    try (rewrite IHe1, IHe2 by assumption; reflexivity);
    try (apply IHe; assumption).
  apply Nat.ltb_lt in H. apply Nat.ltb_lt. lia.
Qed.
Lemma kentry_vars_lt_mono : forall b b' K, (b <= b')%nat -> kentry_vars_lt b K = true -> kentry_vars_lt b' K = true.
Proof.
  intros b b' K Hle H. destruct K as [[ab ao] w v|[ab ao] n|[ab ao] n k|lo hi|ae am|re rlo rhi|[ab ao] wn|[b1 o1] n1 [b2 o2] n2];
    cbn [kentry_vars_lt saddr_vars_lt a_base] in *; try exact H;
    repeat match goal with
      | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
      end;
    repeat (apply andb_true_intro; split); try (eapply expr_vars_lt_mono; eassumption).
Qed.
Lemma kn_vars_lt_mono : forall b b' kn, (b <= b')%nat -> kn_vars_lt b kn = true -> kn_vars_lt b' kn = true.
Proof.
  intros b b' kn Hle. induction kn as [|K r IH]; cbn [kn_vars_lt]; intros H; [reflexivity|].
  apply andb_prop in H as [H1 H2]. rewrite (kentry_vars_lt_mono b b' K Hle H1), (IH H2). reflexivity.
Qed.

End WithSegs.
End SPM.
