(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzArrD. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM BzCPermM.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gtu_pre_ne : forall n a2 i1 i2, rd8 a2 i1 <> rd8 a2 i2 ->
  gtu_pre (S n) a2 i1 i2 = (Some (rd8 a2 i2 <? rd8 a2 i1), i1, i2).
Proof. intros n a2 i1 i2 H. cbn [gtu_pre]. destruct (Z.eqb_spec (rd8 a2 i1) (rd8 a2 i2)); [lia| reflexivity]. Qed.
Lemma gtu_pre_eq : forall n a2 i1 i2, rd8 a2 i1 = rd8 a2 i2 ->
  gtu_pre (S n) a2 i1 i2 = gtu_pre n a2 (i1 + 1) (i2 + 1).
Proof. intros n a2 i1 i2 H. cbn [gtu_pre]. rewrite H, Z.eqb_refl. reflexivity. Qed.
(* [comment removed for export] *)
Lemma gtu_pre_ne_t : forall n a2 i1 i2 t, rd8 a2 (i1 + t) <> rd8 a2 (i2 + t) ->
  gtu_pre (S n) a2 (i1 + t) (i2 + t) = (Some (rd8 a2 (i2 + t) <? rd8 a2 (i1 + t)), i1 + t, i2 + t).
Proof. intros. apply gtu_pre_ne. assumption. Qed.
Lemma gtu_pre_eq_t : forall n a2 i1 i2 t, rd8 a2 (i1 + t) = rd8 a2 (i2 + t) ->
  gtu_pre (S n) a2 (i1 + t) (i2 + t) = gtu_pre n a2 (i1 + (t + 1)) (i2 + (t + 1)).
Proof. intros n a2 i1 i2 t H. rewrite gtu_pre_eq by exact H. f_equal; lia. Qed.

Lemma gtu_oct_bne : forall n a2 qoff i1 i2, rd8 a2 i1 <> rd8 a2 i2 ->
  gtu_oct (S n) a2 qoff i1 i2 = (Some (rd8 a2 i2 <? rd8 a2 i1), i1, i2).
Proof. intros n a2 qoff i1 i2 H. cbn [gtu_oct]. destruct (Z.eqb_spec (rd8 a2 i1) (rd8 a2 i2)); [lia| reflexivity]. Qed.
Lemma gtu_oct_qne : forall n a2 qoff i1 i2, rd8 a2 i1 = rd8 a2 i2 -> qrd a2 qoff i1 <> qrd a2 qoff i2 ->
  gtu_oct (S n) a2 qoff i1 i2 = (Some (qrd a2 qoff i2 <? qrd a2 qoff i1), i1, i2).
Proof.
  intros n a2 qoff i1 i2 H Hq. cbn [gtu_oct]. rewrite H, Z.eqb_refl. cbn [negb].
  destruct (Z.eqb_spec (qrd a2 qoff i1) (qrd a2 qoff i2)); [lia| reflexivity].
Qed.
Lemma gtu_oct_eq : forall n a2 qoff i1 i2, rd8 a2 i1 = rd8 a2 i2 -> qrd a2 qoff i1 = qrd a2 qoff i2 ->
  gtu_oct (S n) a2 qoff i1 i2 = gtu_oct n a2 qoff (i1 + 1) (i2 + 1).
Proof. intros n a2 qoff i1 i2 H Hq. cbn [gtu_oct]. rewrite H, Z.eqb_refl. cbn [negb]. rewrite Hq, Z.eqb_refl. reflexivity. Qed.
Lemma gtu_oct_bne_t : forall n a2 qoff i1 i2 t, rd8 a2 (i1 + t) <> rd8 a2 (i2 + t) ->
  gtu_oct (S n) a2 qoff (i1 + t) (i2 + t) = (Some (rd8 a2 (i2 + t) <? rd8 a2 (i1 + t)), i1 + t, i2 + t).
Proof. intros. apply gtu_oct_bne. assumption. Qed.
Lemma gtu_oct_qne_t : forall n a2 qoff i1 i2 t, rd8 a2 (i1 + t) = rd8 a2 (i2 + t) -> qrd a2 qoff (i1 + t) <> qrd a2 qoff (i2 + t) ->
  gtu_oct (S n) a2 qoff (i1 + t) (i2 + t) = (Some (qrd a2 qoff (i2 + t) <? qrd a2 qoff (i1 + t)), i1 + t, i2 + t).
Proof. intros. apply gtu_oct_qne; assumption. Qed.
Lemma gtu_oct_eq_t : forall n a2 qoff i1 i2 t, rd8 a2 (i1 + t) = rd8 a2 (i2 + t) -> qrd a2 qoff (i1 + t) = qrd a2 qoff (i2 + t) ->
  gtu_oct (S n) a2 qoff (i1 + t) (i2 + t) = gtu_oct n a2 qoff (i1 + (t + 1)) (i2 + (t + 1)).
Proof. intros n a2 qoff i1 i2 t H Hq. rewrite gtu_oct_eq by assumption. f_equal; lia. Qed.

Definition gwrap (n i : Z) : Z := if n <=? i then i - n else i.

Lemma gtu_loop_S : forall f a2 qoff n i1 i2 k b,
  gtu_loop (S f) a2 qoff n i1 i2 k b =
  let '(r, _, _) := gtu_oct 8%nat a2 qoff i1 i2 in
  match r with
  | Some bb => (bb, b)
  | None => if 0 <=? k - 8 then gtu_loop f a2 qoff n (gwrap n (i1 + 8)) (gwrap n (i2 + 8)) (k - 8) (b - 1) else (false, b - 1)
  end.
Proof.
  intros. cbn [gtu_loop]. unfold gwrap.
  assert (G : forall m j1 j2, gtu_oct m a2 qoff j1 j2 = (None, j1 + Z.of_nat m, j2 + Z.of_nat m) \/ exists bb j1' j2', gtu_oct m a2 qoff j1 j2 = (Some bb, j1', j2')).
  { induction m as [|m IH]; intros j1 j2.
    - left. cbn. f_equal; [f_equal|]; lia.
    - cbn [gtu_oct]. destruct (negb (rd8 a2 j1 =? rd8 a2 j2)); [right; do 3 eexists; reflexivity|].
      destruct (negb (qrd a2 qoff j1 =? qrd a2 qoff j2)); [right; do 3 eexists; reflexivity|].
      destruct (IH (j1 + 1) (j2 + 1)) as [E | (bb & j1' & j2' & E)]; rewrite E.
      + left. f_equal; [f_equal|]; lia.
      + right. do 3 eexists; reflexivity. }
  destruct (G 8%nat i1 i2) as [E | (bb & j1' & j2' & E)]; rewrite E; [| reflexivity].
  change (Z.of_nat 8) with 8. reflexivity.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma gtu_loop_budget_le : forall f a2 qoff n i1 i2 k b, snd (gtu_loop f a2 qoff n i1 i2 k b) <= b.
Proof.
  induction f as [|f IH]; intros; [cbn; lia|].
  rewrite gtu_loop_S. destruct (gtu_oct 8 a2 qoff i1 i2) as [[[bb|] j1] j2]; [cbn; lia|].
  destruct (0 <=? k - 8); [| cbn; lia]. eapply Z.le_trans; [apply IH| lia].
Qed.
Lemma mainGtU_budget_le : forall i1 i2 a2 qoff n b, snd (mainGtU i1 i2 a2 qoff n b) <= b.
Proof.
  intros. unfold mainGtU. destruct (gtu_pre 12 a2 i1 i2) as [[[bb|] j1] j2]; [cbn; lia| apply gtu_loop_budget_le].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma gwrap_ge : forall n i, n <= i -> gwrap n i = i - n.
Proof. intros n i H. unfold gwrap. destruct (Z.leb_spec n i); lia. Qed.
Lemma gwrap_lt : forall n i, i < n -> gwrap n i = i.
Proof. intros n i H. unfold gwrap. destruct (Z.leb_spec n i); lia. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rd16_range : forall a o, zbok a -> 0 <= rd16 a o < 65536.
Proof. intros a o H. unfold rd16. pose proof (H o). pose proof (H (o + 1)). lia. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma r1key : forall j b, 0 <= j < 65536 -> 0 <= b < 256 -> Z.lor (Z.shiftr j 8) (Z.shiftl b 8) = j / 256 + 256 * b.
Proof. intros. apply lor_step; assumption. Qed.
Lemma key_div256 : forall h b, 0 <= h < 256 -> (h + 256 * b) / 256 = b.
Proof. intros. Z.div_mod_to_equations. lia. Qed.
(* [comment removed for export] *)

Lemma zget_qwr_lo : forall a qoff i v k, k < qoff -> 0 <= i -> zget (qwr a qoff i v) k = zget a k.
Proof. intros. unfold qwr, wr16. rewrite !zget_zset_other by lia. reflexivity. Qed.
Lemma zbok_qwr : forall a qoff i v, zbok a -> zbok (qwr a qoff i v).
Proof. intros. unfold qwr. apply zbok_wr16. assumption. Qed.

(* [comment removed for export] *)
Lemma ms_radix1_step : forall q a2 ft qoff i j, 0 <= j < 65536 -> 0 <= i < qoff -> zbok a2 ->
  ms_radix1 (S q) a2 ft qoff i j =
  let b := zget a2 i in let j1 := j / 256 + 256 * b in
  ms_radix1 q (qwr a2 qoff i 0) (zincr ft j1) qoff (i - 1) j1.
Proof.
  intros q a2 ft qoff i j Hj Hi Hb. cbn [ms_radix1]. unfold rd8. rewrite zget_qwr_lo by lia.
  rewrite r1key by (try apply Hb; lia). reflexivity.
Qed.
(* [comment removed for export] *)
Lemma ms_radix1_step4 : forall q a2 ft qoff i j, 0 <= j < 65536 -> 3 <= i < qoff -> zbok a2 ->
  ms_radix1 (S (S (S (S q)))) a2 ft qoff i j =
  let b0 := zget a2 i in let b1 := zget a2 (i - 1) in let b2 := zget a2 (i - 2) in let b3 := zget a2 (i - 3) in
  let j1 := j / 256 + 256 * b0 in let j2 := b0 + 256 * b1 in let j3 := b1 + 256 * b2 in let j4 := b2 + 256 * b3 in
  ms_radix1 q (qwr (qwr (qwr (qwr a2 qoff i 0) qoff (i - 1) 0) qoff (i - 2) 0) qoff (i - 3) 0)
              (zincr (zincr (zincr (zincr ft j1) j2) j3) j4) qoff (i - 4) j4.
Proof.
  intros q a2 ft qoff i j Hj Hi Hb.
  pose proof (Hb i) as B0. pose proof (Hb (i - 1)) as B1. pose proof (Hb (i - 2)) as B2. pose proof (Hb (i - 3)) as B3.
  assert (D0 : 0 <= j / 256 < 256) by (Z.div_mod_to_equations; lia).
  set (a2a := qwr a2 qoff i 0). set (a2b := qwr a2a qoff (i - 1) 0). set (a2c := qwr a2b qoff (i - 2) 0).
  assert (Ea : zget a2a (i - 1) = zget a2 (i - 1)) by (subst a2a; apply zget_qwr_lo; lia).
  assert (Eb : zget a2b (i - 2) = zget a2 (i - 2)) by (subst a2b a2a; rewrite !zget_qwr_lo by lia; reflexivity).
  assert (Ec : zget a2c (i - 3) = zget a2 (i - 3)) by (subst a2c a2b a2a; rewrite !zget_qwr_lo by lia; reflexivity).
  assert (Hba : zbok a2a) by (subst a2a; apply zbok_qwr; exact Hb).
  assert (Hbb : zbok a2b) by (subst a2b; apply zbok_qwr; exact Hba).
  assert (Hbc : zbok a2c) by (subst a2c; apply zbok_qwr; exact Hbb).
  rewrite (ms_radix1_step _ a2) by (try assumption; lia). cbv zeta. fold a2a.
  rewrite (ms_radix1_step _ a2a); [| lia | lia | exact Hba]. cbv zeta. fold a2b. rewrite Ea. rewrite key_div256 by lia.
  replace (i - 1 - 1) with (i - 2) by lia.
  rewrite (ms_radix1_step _ a2b); [| lia | lia | exact Hbb]. cbv zeta. fold a2c. rewrite Eb. rewrite key_div256 by lia.
  replace (i - 2 - 1) with (i - 3) by lia.
  rewrite (ms_radix1_step _ a2c); [| lia | lia | exact Hbc]. cbv zeta. rewrite Ec. rewrite key_div256 by lia.
  f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma ms_radix1_ft_bound : forall q a2 ft qoff i j (c : Z),
  (forall v, 0 <= zget ft v <= c) -> forall v, 0 <= zget (snd (fst (ms_radix1 q a2 ft qoff i j))) v <= c + Z.of_nat q.
Proof.
  induction q as [|q IH]; intros a2 ft qoff i j c H v.
  - cbn. pose proof (H v). lia.
  - cbn [ms_radix1]. match goal with |- context [ms_radix1 q ?a ?f ?qo ?i' ?j'] =>
      pose proof (IH a f qo i' j' (c + 1)) as K end.
    rewrite Nat2Z.inj_succ. replace (c + Z.succ (Z.of_nat q)) with (c + 1 + Z.of_nat q) by lia. apply K.
    intros w. rewrite zget_zincr. pose proof (H w). match goal with |- context [zget ft ?x + 1] => pose proof (H x) end. destruct (w =? _); lia.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ms_radix1_low : forall q a2 ft qoff i j k, k < qoff -> 0 <= i + 1 - Z.of_nat q ->
  zget (fst (fst (ms_radix1 q a2 ft qoff i j))) k = zget a2 k.
Proof.
  induction q as [|q IH]; intros a2 ft qoff i j k Hk Hi; cbn [ms_radix1 fst]; [reflexivity|].
  rewrite IH by lia. apply zget_qwr_lo; lia.
Qed.
(* [comment removed for export] *)
Lemma ms_radix1_app : forall a b a2 ft qoff i j,
  ms_radix1 (a + b) a2 ft qoff i j = let '(a2', ft', j') := ms_radix1 a a2 ft qoff i j in ms_radix1 b a2' ft' qoff (i - Z.of_nat a) j'.
Proof.
  induction a as [|a IH]; intros b a2 ft qoff i j.
  - cbn [Nat.add ms_radix1]. rewrite Z.sub_0_r. reflexivity.
  - cbn [Nat.add ms_radix1]. rewrite IH. destruct (ms_radix1 a _ _ _ _ _) as [[a2' ft'] j'].
    rewrite Nat2Z.inj_succ. f_equal. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ms_accum_frame : forall r ft i v, v < i -> zget (ms_accum r ft i) v = zget ft v.
Proof.
  induction r as [|r IH]; intros ft i v Hv; cbn [ms_accum]; [reflexivity|].
  rewrite IH by lia. apply zget_zset_other. lia.
Qed.
Lemma ms_accum_here : forall r ft i, zget (ms_accum (S r) ft i) i = zget ft i + zget ft (i - 1).
Proof. intros. cbn [ms_accum]. rewrite ms_accum_frame by lia. apply zget_zset_same. Qed.
Lemma ms_accum_S : forall r ft i, ms_accum (S r) ft i = ms_accum r (zset ft i (zget ft i + zget ft (i - 1))) (i + 1).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ms_overshoot_S : forall r a2 qoff nb i,
  ms_overshoot (S r) a2 qoff nb i = ms_overshoot r (qwr (wr8 a2 (nb + i) (rd8 a2 i)) qoff (nb + i) 0) qoff nb (i + 1).
Proof. reflexivity. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ms_radix2_step : forall q a1 a2 ft i s, 0 <= s < 65536 -> zbok a2 ->
  ms_radix2 (S q) a1 a2 ft i s =
  let b := zget a2 i in let s1 := s / 256 + 256 * b in let j := zget ft s1 - 1 in
  ms_radix2 q (wr32 a1 j i) a2 (zset ft s1 j) (i - 1) s1.
Proof. intros q a1 a2 ft i s Hs Hb. cbn [ms_radix2]. unfold rd8. rewrite r1key by (try apply Hb; lia). reflexivity. Qed.

Lemma ms_radix2_app : forall a b a1 a2 ft i s,
  ms_radix2 (a + b) a1 a2 ft i s = let '(a1', ft', s') := ms_radix2 a a1 a2 ft i s in ms_radix2 b a1' a2 ft' (i - Z.of_nat a) s'.
Proof.
  induction a as [|a IH]; intros b a1 a2 ft i s.
  - cbn [Nat.add ms_radix2]. rewrite Z.sub_0_r. reflexivity.
  - cbn [Nat.add ms_radix2]. rewrite IH. destruct (ms_radix2 a _ _ _ _ _) as [[a1' ft'] s'].
    rewrite Nat2Z.inj_succ. f_equal. lia.
Qed.
Lemma ms_radix2_s_range : forall q a1 a2 ft i s, 0 <= s < 65536 -> zbok a2 -> 0 <= snd (ms_radix2 q a1 a2 ft i s) < 65536.
Proof.
  induction q as [|q IH]; intros a1 a2 ft i s Hs Hb; [cbn; lia|].
  rewrite ms_radix2_step by assumption. cbv zeta. apply IH; [| exact Hb]. pose proof (Hb i). Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Definition r2ok (nb : Z) (r : nat) (a1 a2 ft : zarr) (i s : Z) : Prop :=
  forall k, (k < r)%nat ->
    let '(a1k, ftk, sk) := ms_radix2 k a1 a2 ft i s in
    1 <= zget ftk (sk / 256 + 256 * zget a2 (i - Z.of_nat k)) <= nb.
Lemma r2ok_here : forall nb r a1 a2 ft i s, r2ok nb (S r) a1 a2 ft i s -> 1 <= zget ft (s / 256 + 256 * zget a2 i) <= nb.
Proof. intros nb r a1 a2 ft i s H. pose proof (H 0%nat ltac:(lia)) as K. cbn in K. rewrite Z.sub_0_r in K. exact K. Qed.
Lemma r2ok_shift : forall nb r a1 a2 ft i s, 0 <= s < 65536 -> zbok a2 -> r2ok nb (S r) a1 a2 ft i s ->
  let b := zget a2 i in let s1 := s / 256 + 256 * b in let j := zget ft s1 - 1 in
  r2ok nb r (wr32 a1 j i) a2 (zset ft s1 j) (i - 1) s1.
Proof.
  intros nb r a1 a2 ft i s Hs Hb H. cbv zeta. intros k Hk.
  pose proof (H (S k) ltac:(lia)) as K. change (S k) with (1 + k)%nat in K. rewrite ms_radix2_app in K.
  change (ms_radix2 1 a1 a2 ft i s) with (ms_radix2 (S O) a1 a2 ft i s) in K. rewrite ms_radix2_step in K by assumption.
  cbv zeta in K. cbn [ms_radix2] in K. replace (i - Z.of_nat 1) with (i - 1) in K by lia.
  destruct (ms_radix2 k _ _ _ _ _) as [[a1k ftk] sk].
  replace (i - 1 - Z.of_nat k) with (i - Z.of_nat (1 + k)) by lia. exact K.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ms_ro_init_S : forall n bd ro i, ms_ro_init (S n) bd ro i = ms_ro_init n (zset bd i 0) (zset ro i i) (i + 1).
Proof. reflexivity. Qed.

Lemma ms_sh_shift_S : forall f ro ft h j vv,
  ms_sh_shift (S f) ro ft h j vv =
  if bigfreq ft vv <? bigfreq ft (zget ro (j - h)) then
    let ro1 := zset ro j (zget ro (j - h)) in let j1 := j - h in
    if j1 <=? h - 1 then (ro1, j1) else ms_sh_shift f ro1 ft h j1 vv
  else (ro, j).
Proof. reflexivity. Qed.
Lemma ms_sh_pass_S : forall n ro ft h i,
  ms_sh_pass (S n) ro ft h i = let vv := zget ro i in let '(ro1, j) := ms_sh_shift 300%nat ro ft h i vv in ms_sh_pass n (zset ro1 j vv) ft h (i + 1).
Proof. reflexivity. Qed.
Lemma ms_shell_S : forall f ro ft h,
  ms_shell (S f) ro ft h = let h1 := h / 3 in let ro1 := ms_sh_pass (Z.to_nat (256 - h1)) ro ft h1 h1 in if h1 =? 1 then ro1 else ms_shell f ro1 ft h1.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition rook (ro : zarr) : Prop := forall k, 0 <= k < 256 -> 0 <= zget ro k < 256.
(* [comment removed for export] *)
(* [comment removed for export] *)
