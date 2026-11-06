(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1d7 X1cx X1cy X1cj X1cp.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition SH_LO : Z := 2147450880.
Definition SH_HI : Z := 17594333495296.
Definition APP_TOP : Z := 140737488355328.

Fixpoint offsh (W : list ivl) : Prop :=
match W with
| [] => True
| (lo, hi) :: W' => (hi <= SH_LO \/ SH_HI <= lo) /\ offsh W'
end.

Lemma offsh_outside : forall W x, offsh W -> SH_LO <= x < SH_HI -> outside W x.
Proof.
induction W as [|[lo hi] W IH]; cbn; intros x H Hx; [exact I|].
destruct H as [H1 H2]. split; [lia| exact (IH x H2 Hx)].
Qed.

Lemma shad_window : forall a, 0 <= a < APP_TOP -> SH_LO <= shad a < SH_HI.
Proof. intros a Ha. unfold shad, SHB, SH_LO, SH_HI, APP_TOP in *. Z.div_mod_to_equations. lia. Qed.

Lemma shad_range_al : forall f n, 0 <= f -> f mod 8 = 0 -> n mod 8 = 0 -> 0 <= n -> f + n <= APP_TOP ->
SH_LO <= shad f /\ shad f + n / 8 <= SH_HI.
Proof. intros f n H0 F8 N8 Hn HT. unfold shad, SHB, SH_LO, SH_HI, APP_TOP in *. Z.div_mod_to_equations. lia. Qed.

Lemma shad_shiftr : forall a, Z.shiftr a 3 + SHB = shad a.
Proof. intros a. unfold shad. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Definition shfree (W : list ivl) (o n : Z) : Prop := forall x, o <= x < o + n -> outside W (shad x).

Lemma shfree_of_offsh : forall W o n, offsh W -> 0 <= o -> o + n <= APP_TOP -> shfree W o n.
Proof. intros W o n OF H0 H1 x Hx. apply (offsh_outside W _ OF). apply shad_window. lia. Qed.
Lemma shfree_nil : forall o n, shfree [] o n.
Proof. intros o n x _. exact I. Qed.
Lemma shfree_cons_off : forall lo hi W o n, (hi <= SH_LO \/ SH_HI <= lo) -> 0 <= o -> o + n <= APP_TOP -> shfree W o n ->
shfree ((lo, hi) :: W) o n.
Proof.
intros lo hi W o n H H0 H1 SF x Hx. cbn. split; [| exact (SF x Hx)].
pose proof (shad_window x ltac:(lia)). lia.
Qed.

Lemma shfree_cons_sh : forall lo hi W o n f fsz, f mod 8 = 0 -> shad f <= lo -> hi <= shad (f + fsz) ->
(o + n <= f \/ f + fsz <= o) -> shfree W o n -> shfree ((lo, hi) :: W) o n.
Proof.
intros lo hi W o n f fsz F8 Hlo Hhi SEP SF x Hx. cbn. split; [| exact (SF x Hx)].
unfold shad in *. destruct SEP as [S|S].
- assert (x / 8 < f / 8) by (Z.div_mod_to_equations; lia). lia.
- assert ((f + fsz) / 8 <= x / 8) by (apply Z.div_le_mono; lia). lia.
Qed.
Lemma shfree_sub : forall W o n o' n', shfree W o n -> o <= o' -> o' + n' <= o + n -> shfree W o' n'.
Proof. intros W o n o' n' SF H1 H2 x Hx. apply SF. lia. Qed.

Section Chk.
Variable segs : list Segment.
Notation mem := (word -> option byte).

Definition shb (m : mem) (a : Z) : byte :=
match mrd segs m (wa (shad a)) with Some b => b | None => Z_to_bv 8 255 end.

Definition shz (m : mem) (a : Z) : Z := bv_signed (shb m a).

Lemma sxb_shb : forall m a, sxb (shb m a) = Z_to_bv 64 (shz m a).
Proof. reflexivity. Qed.

Definition aobj (mb : mem) (o n : Z) : Prop := 0 <= o /\ o + n <= APP_TOP /\ acc segs mb o n.

Lemma aobj_sub : forall mb o n o' n', aobj mb o n -> o <= o' -> o' + n' <= o + n -> aobj mb o' n'.
Proof.
intros mb o n o' n' (H0 & H1 & H) Ho Hn. split; [lia|]. split; [lia|]. exact (acc_sub segs mb o n o' n' H Ho Hn).
Qed.

Lemma shfree_of_aobj : forall W mb o n, offsh W -> aobj mb o n -> shfree W o n.
Proof. intros W mb o n OF (H0 & H1 & _). exact (shfree_of_offsh W o n OF H0 H1). Qed.

Lemma bytes_at1_mrd : forall (m : mem) x b, bytes_at segs m x [b] -> mrd segs m (wa x) = Some b.
Proof.
intros m x b (_ & _ & H). specialize (H 0%nat ltac:(cbn; lia)). cbn in H. rewrite Z.add_0_r in H. exact H.
Qed.

Lemma acc_shb : forall mb o n a, acc segs mb o n -> o <= a < o + n ->
bytes_at segs mb (shad a) [shb mb a] /\ sh_ok (shb mb a) a.
Proof.
intros mb o n a H Ha. destruct (H (a - o) ltac:(lia)) as (b & Hb & Hok).
replace (o + (a - o)) with a in * by lia.
unfold shb. rewrite (bytes_at1_mrd mb _ b Hb). split; assumption.
Qed.

Lemma sh_ok_small : forall b a, sh_ok b a -> bv_signed b = bv_unsigned b /\ 0 <= bv_unsigned b < 8.
Proof.
intros b a H.
assert (R : 0 <= bv_unsigned b < 8) by (pose proof (bv_unsigned_in_range 8 b); destruct H as [H|H]; lia).
split; [| exact R].
unfold bv_signed. apply bv_swrap_small. change (bv_half_modulus 8) with 128. lia.
Qed.

Lemma shb_same_granule : forall m a a', a / 8 = a' / 8 -> shb m a = shb m a'.
Proof. intros m a a' H. unfold shb, shad. rewrite H. reflexivity. Qed.

Lemma sh_fact : forall mb o n a N, aobj mb o n -> o <= a -> a + N <= o + n -> 1 <= N -> a mod 8 + N <= 8 ->
(0 < shz mb a < 8 /\ a mod 8 + (N - 1) < shz mb a) \/ shz mb a = 0.
Proof.
intros mb o n a N (_ & _ & H) Ho Hn HN Hg.
destruct (acc_shb mb o n (a + (N - 1)) H ltac:(lia)) as (_ & Hok).
assert (G : (a + (N - 1)) / 8 = a / 8) by (Z.div_mod_to_equations; lia).
rewrite (shb_same_granule mb _ _ G) in Hok.
pose proof (sh_ok_small _ _ Hok) as (ES & R). unfold shz. rewrite ES.
assert (M : (a + (N - 1)) mod 8 = a mod 8 + (N - 1)) by (Z.div_mod_to_equations; lia).
destruct Hok as [Hz|(Hp & Hm)]; [right; exact Hz| left]. rewrite M in Hm. lia.
Qed.

Lemma shb_zero : forall mb o n a, acc segs mb o n -> o <= a -> a / 8 * 8 + 8 <= o + n -> shb mb a = z8.
Proof.
intros mb o n a H Ho Hn.
destruct (acc_shb mb o n (a / 8 * 8 + 7) H ltac:(Z.div_mod_to_equations; lia)) as (_ & Hok).
assert (G : (a / 8 * 8 + 7) / 8 = a / 8) by (Z.div_mod_to_equations; lia).
rewrite (shb_same_granule mb _ _ G) in Hok.
assert (M : (a / 8 * 8 + 7) mod 8 = 7) by (Z.div_mod_to_equations; lia).
apply bv_eq. change (bv_unsigned z8) with 0. destruct Hok as [Hz|(Hp & Hm)]; [exact Hz| lia].
Qed.

Lemma shb_munch : forall W (mb m : mem) a, munch W mb m -> offsh W -> 0 <= a < APP_TOP -> shb m a = shb mb a.
Proof.
intros W mb m a MU OF Ha. unfold shb, mrd. pose proof (shad_window a Ha) as SW.
rewrite (MU (wa (shad a))); [reflexivity|].
rewrite wa_unsigned by (unfold SH_LO, SH_HI in SW; lia). exact (offsh_outside W _ OF SW).
Qed.

Lemma aobj_munch : forall W (mb m : mem) o n, aobj mb o n -> munch W mb m -> shfree W o n -> aobj m o n.
Proof.
intros W mb m o n (H0 & H1 & H) MU SF. split; [exact H0|]. split; [exact H1|].
intros i Hi. destruct (acc_shb mb o n (o + i) H ltac:(lia)) as (Hb & Hok).
exists (shb mb (o + i)). split; [| exact Hok].
apply (bytes_at_transport segs W mb m _ _ Hb MU). cbn [length].
pose proof (SF (o + i) ltac:(lia)) as OUT. pose proof (shad_window (o + i) ltac:(lia)) as SW. clear - OUT SW.
induction W as [|[lo hi] W IH]; cbn in *; [exact I|]. destruct OUT as [O1 O2]. split; [lia| exact (IH O2)].
Qed.

Lemma sh_rd_shad : forall W (mb m : mem) o n a,
munch W mb m -> shfree W o n -> aobj mb o n -> o <= a < o + n ->
ov_read_bytes segs m (Z_to_bv 64 (shad a)) 1 = Some [shb mb a].
Proof.
intros W mb m o n a MU SF (H0 & H1 & H) Ha.
destruct (acc_shb mb o n a H Ha) as (Hb & _).
assert (Hb' : bytes_at segs m (shad a) [shb mb a]).
{ apply (bytes_at_transport segs W mb m _ _ Hb MU). cbn [length].
pose proof (SF a Ha) as OUT. pose proof (shad_window a ltac:(lia)) as SW. clear - OUT SW.
induction W as [|[lo hi] W IH]; cbn in *; [exact I|]. destruct OUT as [O1 O2]. split; [lia| exact (IH O2)]. }
pose proof (bytes_at_read segs m (shad a) [shb mb a] 0 1 Hb' ltac:(lia) ltac:(cbn; lia)) as R.
rewrite Z.add_0_r in R. exact R.
Qed.

Lemma sh_rd : forall W (mb m : mem) o n a,
munch W mb m -> shfree W o n -> aobj mb o n -> o <= a < o + n ->
ov_read_bytes segs m (Z_to_bv 64 (Z.shiftr a 3 + SHB)) 1 = Some [shb mb a].
Proof. intros. rewrite shad_shiftr. eapply sh_rd_shad; eassumption. Qed.

Lemma sh_rd0 : forall W (mb m : mem) o n a,
munch W mb m -> shfree W o n -> aobj mb o n -> o <= a -> a / 8 * 8 + 8 <= o + n ->
ov_read_bytes segs m (Z_to_bv 64 (Z.shiftr a 3 + SHB)) 1 = Some [z8].
Proof.
intros W mb m o n a MU SF OB Ho Hn.
rewrite <- (shb_zero mb o n a (proj2 (proj2 OB)) Ho Hn).
apply (sh_rd W mb m o n a MU SF OB). Z.div_mod_to_equations. lia.
Qed.

Definition fld_full (d n : Z) : bool := (0 <=? d) && (d / 8 * 8 + 8 <=? n).

Lemma sh_rd0_fld : forall W (mb m : mem) o n d,
munch W mb m -> shfree W o n -> aobj mb o n -> o mod 8 = 0 -> fld_full d n = true ->
ov_read_bytes segs m (Z_to_bv 64 (Z.shiftr (o + d) 3 + SHB)) 1 = Some [z8].
Proof.
intros W mb m o n d MU SF OB AL FF. unfold fld_full in FF. apply andb_prop in FF. destruct FF as [F1 F2].
apply Z.leb_le in F1, F2.
apply (sh_rd0 W mb m o n (o + d) MU SF OB); [lia|]. Z.div_mod_to_equations. lia.
Qed.

Lemma sh_rd0_fld0 : forall W (mb m : mem) o n,
munch W mb m -> shfree W o n -> aobj mb o n -> o mod 8 = 0 -> fld_full 0 n = true ->
ov_read_bytes segs m (Z_to_bv 64 (Z.shiftr o 3 + SHB)) 1 = Some [z8].
Proof.
intros W mb m o n MU SF OB AL FF. pose proof (sh_rd0_fld W mb m o n 0 MU SF OB AL FF) as H.
rewrite Z.add_0_r in H. exact H.
Qed.

End Chk.

Lemma sxb_z8 : sxb z8 = Z_to_bv 64 0.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma zxb_z8 : zxb z8 = Z_to_bv 64 0.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma al1_gran : forall a, a mod 8 + 1 <= 8.
Proof. intros a. pose proof (Z.mod_pos_bound a 8 ltac:(lia)). lia. Qed.
Lemma al2_gran : forall a, a mod 2 = 0 -> a mod 8 + 2 <= 8.
Proof. intros a H. Z.div_mod_to_equations. lia. Qed.
Lemma al4_gran : forall a, a mod 4 = 0 -> a mod 8 + 4 <= 8.
Proof. intros a H. Z.div_mod_to_equations. lia. Qed.
Lemma al8_gran : forall a, a mod 8 = 0 -> a mod 8 + 8 <= 8.
Proof. intros a H. lia. Qed.

Lemma shiftr3_add : forall a k, Z.shiftr (a + 8 * k) 3 = Z.shiftr a 3 + k.
Proof.
intros a k. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
replace (a + 8 * k) with (a + k * 8) by lia. apply Z.div_add. lia.
Qed.

Lemma shad_step16 : forall p off, Z.shiftr (p + off) 3 + SHB + 2 = Z.shiftr (p + (off + 16)) 3 + SHB.
Proof. intros p off. replace (p + (off + 16)) with (p + off + 8 * 2) by lia. rewrite shiftr3_add. lia. Qed.

Lemma signed_small64 : forall z, -9223372036854775808 <= z < 9223372036854775808 -> bv_signed (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_signed. apply bv_swrap_small. change (bv_half_modulus 64) with 9223372036854775808. lia. Qed.
Lemma unsigned_small64 : forall z, 0 <= z < 18446744073709551616 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply Z_to_bv_small. change (bv_modulus 64) with 18446744073709551616. lia. Qed.
Lemma sh_land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma land_m32_al : forall x, 0 <= x < 2^64 -> x mod 32 = 0 -> Z.land x 18446744073709551584 = x.
Proof.
intros x Hx H. change 18446744073709551584 with (Z.ldiff (Z.ones 64) (Z.ones 5)).
rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
change (2^5) with 32. Z.div_mod_to_equations. lia.
Qed.

Definition hid (P : Prop) : Prop := P.
Ltac hide_disj := repeat match goal with H : ?A \/ ?B |- _ => change (hid (A \/ B)) in H end.
Ltac unhide_disj := repeat match goal with H : hid ?P |- _ => change P in H end.
