(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from part of proofs/libreac/fuzz_grant/lib/A/Prog/GrantClose.v (itself made from part of proofs/cgif/cgif_file_fuzzer/lib/A/ACfi.v) for libreac/fuzz_disco: is_shc, is_shv, zfind, vscan, glob_chk, in_zr_b and their lemmas, and the shadow of the image and of its registered globals, stated at TfibB (lib/A/AD2l.v) and at disco_segs, the segment list of PB_disco; glob_chk accepts a global with no full granule; the byte check of the read-only ranges (byte_free_b, ro_range_b, ro_unowned_of_b) and its registered-globals part (disco_globs_unowned, disco_glob_readable) are added; module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK04 YA0i YA0n YP09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import AB1v AF0l AF0m AD2l.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym DiscoSyms DiscoPa DiscoImg DiscoBase DiscoRo.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Lemma disco_segs_tfib : disco_segs = tfibsegs.
Proof. reflexivity. Qed.

Definition in_zr_b (a : Z) (r : Z * Z) : bool := ((fst r <=? a) && (a <? fst r + snd r))%bool.

Definition is_shc (s : Z) (c : acell) : bool :=
  match c with ACell (ANum s') (S O) (AV (ANum _)) => Z.eqb s' s | _ => false end.
Definition is_shv (s v : Z) (c : acell) : bool :=
  match c with ACell (ANum s') (S O) (AV (ANum v')) => (Z.eqb s' s && Z.eqb v' v)%bool | _ => false end.

Fixpoint zfind (k : Z) (zs : list (Z * Z)) : option Z :=
  match zs with
  | [] => None
  | (q, m) :: r => if ((q / 8 <=? k) && (k <? (q + m) / 8))%bool then Some ((q + m) / 8) else zfind k r
  end.

Fixpoint vscan (fuel : nat) (k hi : Z) : bool :=
  match fuel with
  | O => false
  | S f =>
      if hi <=? k then true else
      match zfind k Tfib_zero_shadow with
      | Some e => vscan f e hi
      | None => (existsb (is_shc (SHADOW_OFF + k)) Tfib_const_shadow && vscan f (k + 1) hi)%bool
      end
  end.

Definition glob_chk (g : Z * Z) : bool :=
  ((fst g mod 8 =? 0) && (0 <=? snd g) &&
   ((snd g / 8 =? 0) ||
    existsb (fun r => (fst r <=? fst g) && (fst g + snd g / 8 * 8 <=? fst r + snd r)) Tfib_zero_shadow) &&
   ((snd g mod 8 =? 0) || existsb (is_shv (SHADOW_OFF + fst g / 8 + snd g / 8) (snd g mod 8)) Tfib_const_shadow))%bool.

Definition byte_free_b (B : asyms) (a : Z) : bool :=
  (negb (existsb (in_zr_b a) (as_owned_static B)) && negb ((as_errno B <=? a) && (a <? as_errno B + 4)))%bool.

Definition ro_range_b (B : asyms) (r : Z * Z) : bool :=
  forallb (fun j => byte_free_b B (fst r + Z.of_nat j)) (seq 0 (Z.to_nat (snd r))).

Lemma not_Exists_in_zr : forall a l, existsb (in_zr_b a) l = false -> ~ Exists (in_zr a) l.
Proof.
intros a l H HE. apply Exists_exists in HE as (r & Hr & Hz). unfold in_zr in Hz.
assert (E : existsb (in_zr_b a) l = true).
{ apply existsb_exists. exists r. split; [exact Hr|]. unfold in_zr_b. apply andb_true_intro.
  split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
congruence.
Qed.

Lemma le_byte1 : forall v, 0 <= v < 256 -> YG0f.le_byte v 1 0 = v.
Proof.
intros v Hv. unfold YG0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small v 256 Hv). exact (Z.mod_small v 256 Hv).
Qed.

Lemma is_shc_eq : forall s c, is_shc s c = true -> exists v, c = z1 (ANum s) v.
Proof.
intros s [ca cw cv] H. destruct ca; try (cbn in H; discriminate H).
destruct cw as [|[|cw]]; try (cbn in H; discriminate H).
destruct cv as [e|m0 v0]; try (cbn in H; discriminate H).
destruct e; try (cbn in H; discriminate H).
cbn in H. apply Z.eqb_eq in H. subst. eexists. reflexivity.
Qed.

Lemma is_shv_eq : forall s v c, is_shv s v c = true -> c = z1 (ANum s) v.
Proof.
intros s v [ca cw cv] H. destruct ca; try (cbn in H; discriminate H).
destruct cw as [|[|cw]]; try (cbn in H; discriminate H).
destruct cv as [e|m0 v0]; try (cbn in H; discriminate H).
destruct e; try (cbn in H; discriminate H).
cbn in H. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.

Lemma zfind_some : forall k zs e, zfind k zs = Some e ->
  exists q m, In (q, m) zs /\ q / 8 <= k < (q + m) / 8 /\ e = (q + m) / 8.
Proof.
intros k zs. induction zs as [|[q m] r IH]; intros e H; cbn [zfind] in H; [discriminate|].
destruct ((q / 8 <=? k) && (k <? (q + m) / 8))%bool eqn:Hb.
- injection H as <-. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  exists q, m. split; [left; reflexivity|]. split; [split; assumption | reflexivity].
- destruct (IH e H) as (q' & m' & Hin & Hk & He). exists q', m'. split; [right; exact Hin|]. split; [exact Hk | exact He].
Qed.

Lemma vscan_ok : forall fuel k hi, vscan fuel k hi = true -> forall j, k <= j < hi ->
  (exists q m, In (q, m) Tfib_zero_shadow /\ q / 8 <= j < (q + m) / 8) \/
  existsb (is_shc (SHADOW_OFF + j)) Tfib_const_shadow = true.
Proof.
induction fuel as [|f IH]; intros k hi H j Hj; cbn [vscan] in H; [discriminate|].
destruct (hi <=? k) eqn:E; [apply Z.leb_le in E; exfalso; lia|].
destruct (zfind k Tfib_zero_shadow) as [e|] eqn:Ez.
- destruct (zfind_some _ _ _ Ez) as (q & m & Hin & Hk & ->).
  destruct (Z_lt_le_dec j ((q + m) / 8)) as [Hlt|Hge].
  + left. exists q, m. split; [exact Hin|]. split; [|exact Hlt].
    apply (Z.le_trans _ k); [exact (proj1 Hk) | exact (proj1 Hj)].
  + exact (IH _ _ H j (conj Hge (proj2 Hj))).
- apply andb_prop in H as [Hc H]. destruct (Z.eq_dec j k) as [->|Hne]; [right; exact Hc|].
  apply (IH _ _ H). lia.
Qed.

Lemma disco_vscan : vscan (Pos.to_nat 65536) (IMG_LO / 8) (IMG_TOP / 8) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma disco_globs_chk : forallb glob_chk disco_globs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zs_align_chk : forallb (fun r => (fst r mod 8 =? 0) && (snd r mod 8 =? 0) && (0 <=? snd r))%bool Tfib_zero_shadow = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zs_align : forall q m, In (q, m) Tfib_zero_shadow -> q mod 8 = 0 /\ m mod 8 = 0 /\ 0 <= m.
Proof.
intros q m Hin. pose proof (proj1 (forallb_forall _ _) zs_align_chk (q, m) Hin) as Hb. cbn [fst snd] in Hb.
apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.leb_le in H3. auto.
Qed.

Lemma zs_gran_end : forall q m, q mod 8 = 0 -> m mod 8 = 0 -> (q + m) / 8 = q / 8 + m / 8.
Proof. intros q m Hq Hm. lia. Qed.

Lemma img_gran : forall a, IMG_LO <= a < IMG_TOP -> IMG_LO / 8 <= a / 8 < IMG_TOP / 8.
Proof. intros a Ha. unfold IMG_LO, IMG_TOP in *. lia. Qed.

Lemma glob_gran : forall q sz r0 m0 i, q mod 8 = 0 -> r0 mod 8 = 0 -> m0 mod 8 = 0 ->
  r0 <= q -> q + sz / 8 * 8 <= r0 + m0 -> 0 <= i < sz / 8 ->
  r0 / 8 <= q / 8 + i < (r0 + m0) / 8.
Proof. intros q sz r0 m0 i Hq Hr Hm H1 H2 Hi. lia. Qed.

Lemma last_gran : forall sz i, 0 <= sz -> 0 <= i < (sz + 7) / 8 -> sz / 8 <= i ->
  i = sz / 8 /\ sz mod 8 <> 0 /\ 0 <= sz mod 8 < 256.
Proof. intros sz i Hsz Hi Hge. lia. Qed.

Lemma ro_unowned_of_b : forall B l, forallb (ro_range_b B) l = true ->
  Forall (fun r => ro_unowned B (fst r) (snd r)) l.
Proof.
intros B l H. apply Forall_forall. intros [lo n] Hin a Ha. cbn [fst snd] in Ha.
pose proof (proj1 (forallb_forall _ _) H (lo, n) Hin) as Hr. unfold ro_range_b in Hr. cbn [fst snd] in Hr.
assert (Hj : In (Z.to_nat (a - lo)) (seq 0 (Z.to_nat n))) by (apply in_seq; lia).
pose proof (proj1 (forallb_forall _ _) Hr _ Hj) as Hb. cbv beta in Hb.
rewrite Z2Nat.id in Hb by lia. replace (lo + (a - lo)) with a in Hb by lia.
unfold byte_free_b in Hb. apply andb_prop in Hb as [Ho He]. apply negb_true_iff in Ho. apply negb_true_iff in He.
split; [exact (not_Exists_in_zr _ _ Ho)|].
intros [E1 E2].
assert (X : ((as_errno B <=? a) && (a <? as_errno B + 4))%bool = true)
  by (apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
congruence.
Qed.

Lemma disco_ro_unowned_of_b : forall B, forallb (ro_range_b B) disco_ro_ranges = true -> disco_ro_unowned B.
Proof. intros B H. exact (ro_unowned_of_b B disco_ro_ranges H). Qed.

Lemma disco_globs_unowned : Forall (fun r => ro_unowned TfibB (fst r) (snd r)) disco_globs.
Proof. apply ro_unowned_of_b. vm_compute. reflexivity. Qed.

Lemma disco_glob_in_ranges : forall r, In r disco_globs -> In r disco_ro_ranges.
Proof. intros r H. unfold disco_ro_ranges. apply in_or_app. left. exact H. Qed.

Lemma disco_ro_unowned_tfib : disco_ro_unowned TfibB.
Proof. apply disco_ro_unowned_of_b. vm_compute. reflexivity. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma disco_shadow_cell : forall ly S (W : world disco_segs) mem md s v,
  AR disco_segs TfibB ly S W mem md -> In (z1 (ANum s) v) Tfib_const_shadow ->
  aview disco_segs (w_H W) mem s = Some (YG0f.le_byte v 1 0).
Proof.
intros ly S W mem md s v HAR Hin.
pose proof (am_const _ _ _ _ (proj1 HAR)) as HC. rewrite Forall_forall in HC.
assert (Hin' : In (z1 (ANum s) v) (as_const TfibB ly)).
{ cbn [as_const TfibB]. unfold Tfib_const. apply in_or_app. right. apply in_or_app. right. exact Hin. }
specialize (HC _ Hin'). unfold cell_holds, z1, c1 in HC. cbn [c_at c_val c_w aeval] in HC.
specialize (HC 0%nat ltac:(lia)). cbn [Z.of_nat] in HC. rewrite Z.add_0_r in HC. exact HC.
Qed.

Lemma disco_zs_rd : forall ly S (W : world disco_segs) mem md q m j,
  AR disco_segs TfibB ly S W mem md -> In (q, m) Tfib_zero_shadow -> q / 8 <= j < (q + m) / 8 ->
  aview disco_segs (w_H W) mem (SHADOW_OFF + j) = Some 0.
Proof.
intros ly S W mem md q m j HAR Hin Hj.
pose proof (al_zshadow _ _ (AR_laws_ok disco_segs TfibB) ly S W mem md (q, m) HAR (or_intror Hin)) as Hz.
cbn [fst snd] in Hz.
destruct (zs_align q m Hin) as (Hq & Hm & Hm0).
rewrite (zs_gran_end q m Hq Hm) in Hj.
replace (SHADOW_OFF + j) with (shadow_of_addr SHADOW_OFF q + (j - q / 8)) by (unfold shadow_of_addr; lia).
apply Hz. lia.
Qed.

Lemma disco_img_shadow_vis : img_shadow_vis disco_segs TfibB.
Proof.
intros ly S W mem md a HAR Ha. unfold shadow_addr.
destruct (vscan_ok _ _ _ disco_vscan (a / 8) (img_gran a Ha)) as [(q & m & Hin & Hq) | Hc].
- rewrite (disco_zs_rd ly S W mem md q m (a / 8) HAR Hin Hq). discriminate.
- apply existsb_exists in Hc as (c & Hin & Hb). destruct (is_shc_eq _ _ Hb) as [v ->].
  rewrite (disco_shadow_cell ly S W mem md _ v HAR Hin). discriminate.
Qed.

Lemma disco_globs_marked : globs_marked disco_segs TfibB disco_globs.
Proof.
intros ly S W mem md q sz Hin HAR.
pose proof (proj1 (forallb_forall _ _) disco_globs_chk (q, sz) Hin) as Hb. unfold glob_chk in Hb. cbn [fst snd] in Hb.
apply andb_prop in Hb as [Hb Hlast]. apply andb_prop in Hb as [Hb Hfull]. apply andb_prop in Hb as [Hq Hsz].
apply Z.eqb_eq in Hq. apply Z.leb_le in Hsz.
split; [exact Hq|]. split; [exact Hsz|]. intros i Hi.
destruct (i <? sz / 8) eqn:Hlt.
- apply Z.ltb_lt in Hlt.
  apply orb_true_iff in Hfull as [H0|H0]; [apply Z.eqb_eq in H0; rewrite H0 in Hlt; exfalso; lia|].
  apply existsb_exists in H0 as ([r0 m0] & Hr & Hf). cbn [fst snd] in Hf.
  apply andb_prop in Hf as [Hf1 Hf2]. apply Z.leb_le in Hf1. apply Z.leb_le in Hf2.
  destruct (zs_align r0 m0 Hr) as (Hr8 & Hm8 & Hm0).
  pose proof (glob_gran q sz r0 m0 i Hq Hr8 Hm8 Hf1 Hf2 (conj (proj1 Hi) Hlt)) as Hg.
  unfold shadow_of_addr.
  replace (SHADOW_OFF + q / 8 + i) with (SHADOW_OFF + (q / 8 + i)) by lia.
  exact (disco_zs_rd ly S W mem md r0 m0 (q / 8 + i) HAR Hr Hg).
- apply Z.ltb_ge in Hlt.
  destruct (last_gran sz i Hsz Hi Hlt) as (Hi' & Hnz & Hrng).
  apply orb_true_iff in Hlast as [H0|H0]; [apply Z.eqb_eq in H0; exfalso; exact (Hnz H0)|].
  apply existsb_exists in H0 as (c & Hc & Hcb). apply is_shv_eq in Hcb. subst c. subst i.
  unfold shadow_of_addr.
  rewrite (disco_shadow_cell ly S W mem md _ _ HAR Hc). rewrite (le_byte1 _ Hrng). reflexivity.
Qed.

Lemma disco_glob_readable : forall (rd : reader) q sz x,
  arodata_okP (pa_segs (PAImg := PB_disco)) (pa_relro_lo (PAImg := PB_disco)) (pa_relro_hi (PAImg := PB_disco)) TfibB rd ->
  In (q, sz) disco_globs -> q <= x < q + sz -> rd x <> None.
Proof.
intros rd q sz x HA Hin Hx.
exact (disco_ro_readable (PI := PB_disco) TfibB rd q sz x HA disco_ro_unowned_tfib (disco_glob_in_ranges (q, sz) Hin) Hx).
Qed.

End b.
