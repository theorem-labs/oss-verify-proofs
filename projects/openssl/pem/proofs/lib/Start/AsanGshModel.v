(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import AsanRegModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module GSM.
Import RGM.

Definition F9 : Z := 0xf9.

(* [comment removed for export] *)
Definition wr_lo (y : lay) (d : desc) : Z := shad y (d_beg d) + d_size d / 8.
Definition wr_hi (y : lay) (d : desc) : Z := shad y (d_beg d) + d_swr d / 8.

Definition sh1 (y : lay) (d : desc) (x old : Z) : Z :=
  if (wr_lo y d <=? x) && (x <? wr_hi y d)
  then (if (x =? wr_lo y d) && negb (d_size d mod 8 =? 0) then d_size d mod 8 else F9)
  else old.

(* [comment removed for export] *)
Definition sh_upd (y : lay) (ds : list desc) (x old : Z) : Z := fold_left (fun b d => sh1 y d x b) ds old.

(* [comment removed for export] *)
Definition gsh (y : lay) (tab : list desc) (x : Z) : Z := sh_upd y tab x 0.

(* [comment removed for export] *)
Definition gshw (T : ctab) (tab : list desc) (x : Z) : Z :=
  if (shad (c_lay T) (c_tab T) <=? x) && (x <? shad (c_lay T) (c_tabend T)) then F9 else gsh (c_lay T) tab x.

(* [comment removed for export] *)
Definition gsh_list (y : lay) (tab : list desc) (lo hi : Z) : list Z := map (fun i => gsh y tab (lo + Z.of_nat i)) (seq 0 (Z.to_nat (hi - lo))).

(* [comment removed for export] *)
Fixpoint sortedb (prev : Z) (tab : list desc) : bool :=
  match tab with
  | [] => true
  | d :: r => (prev <=? d_beg d) && (d_beg d mod 8 =? 0) && (d_swr d mod 8 =? 0) && (0 <=? d_size d) && (d_size d <=? d_swr d) && sortedb (d_beg d + d_swr d) r
  end.

Lemma sh_upd_app : forall y a b x old, sh_upd y (a ++ b) x old = sh_upd y b x (sh_upd y a x old).
Proof. intros. unfold sh_upd. apply fold_left_app. Qed.

(* [comment removed for export] *)
Lemma sh1_out : forall y d x old, (x < wr_lo y d \/ wr_hi y d <= x) -> sh1 y d x old = old.
Proof.
  intros y d x old H. unfold sh1.
  destruct (Z.leb_spec (wr_lo y d) x), (Z.ltb_spec x (wr_hi y d)); cbn; try reflexivity. lia.
Qed.

Lemma sh_upd_out : forall y ds x old, (forall d, In d ds -> x < wr_lo y d \/ wr_hi y d <= x) -> sh_upd y ds x old = old.
Proof.
  intros y ds. induction ds as [|d r IH]; intros x old H; [reflexivity|].
  unfold sh_upd in *. cbn [fold_left]. rewrite (sh1_out y d x old) by (apply H; left; reflexivity).
  apply IH. intros d' Hd. apply H. right. exact Hd.
Qed.

(* [comment removed for export] *)
Lemma shad_mono : forall y a b, a <= b -> shad y a <= shad y b.
Proof. intros y a b H. unfold shad. apply Zplus_le_compat_l. apply Z.div_le_mono; lia. Qed.

Lemma shad_add8 : forall y a n, n mod 8 = 0 -> shad y (a + n) = shad y a + n / 8.
Proof.
  intros y a n Hn. unfold shad. rewrite (Z.div_mod n 8) at 1 by lia. rewrite Hn, Z.add_0_r.
  rewrite (Z.mul_comm 8), Z.div_add by lia. ring.
Qed.

(* [comment removed for export] *)
Definition tail_end (p : Z) (a : list desc) : Z := fold_left (fun _ d => d_beg d + d_swr d) a p.

Lemma sortedb_cons : forall p d r, sortedb p (d :: r) = true ->
  p <= d_beg d /\ d_swr d mod 8 = 0 /\ 0 <= d_size d <= d_swr d /\ sortedb (d_beg d + d_swr d) r = true.
Proof.
  intros p d r H. cbn [sortedb] in H. repeat (apply andb_prop in H; destruct H as [H ?]).
  apply Z.leb_le in H, H1, H2. apply Z.eqb_eq in H3. repeat split; try assumption; lia.
Qed.

Lemma sortedb_app : forall a p b, sortedb p (a ++ b) = true -> sortedb p a = true /\ sortedb (tail_end p a) b = true.
Proof.
  induction a as [|d r IH]; intros p b H; [split; [reflexivity | exact H]|].
  change ((d :: r) ++ b) with (d :: (r ++ b)) in H. cbn [sortedb] in H |- *. apply andb_prop in H as [Hc Hs].
  destruct (IH _ _ Hs) as [Ha Hb]. split; [rewrite Hc; exact Ha | exact Hb].
Qed.

(* [comment removed for export] *)
Lemma sorted_in : forall a p d, sortedb p a = true -> In d a ->
  p <= d_beg d /\ d_swr d mod 8 = 0 /\ 0 <= d_size d <= d_swr d /\ d_beg d + d_swr d <= tail_end p a.
Proof.
  induction a as [|e r IH]; intros p d H Hin; [destruct Hin|].
  pose proof (sortedb_cons _ _ _ H) as (H1 & H2 & H3 & H4).
  assert (Hmono : forall l q, sortedb q l = true -> q <= tail_end q l).
  { clear. induction l as [|e r IH]; intros q H; [cbn; lia|]. pose proof (sortedb_cons _ _ _ H) as (H1 & H2 & H3 & H4).
    unfold tail_end in *. cbn [fold_left]. specialize (IH _ H4). lia. }
  unfold tail_end in *. cbn [fold_left]. destruct Hin as [<-|Hin].
  - repeat split; try assumption; try lia. exact (Hmono r _ H4).
  - destruct (IH _ _ H4 Hin) as (I1 & I2 & I3 & I4). repeat split; try assumption; lia.
Qed.

Lemma wr_hi_eq : forall y d, d_swr d mod 8 = 0 -> wr_hi y d = shad y (d_beg d + d_swr d).
Proof. intros y d H. unfold wr_hi. symmetry. apply shad_add8. exact H. Qed.

Lemma wr_lo_le_hi : forall y d, 0 <= d_size d <= d_swr d -> shad y (d_beg d) <= wr_lo y d <= wr_hi y d.
Proof.
  intros y d H. unfold wr_lo, wr_hi. pose proof (Z.div_pos (d_size d) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono (d_size d) (d_swr d) 8 ltac:(lia) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma sorted_out_above : forall y a q x, sortedb q a = true -> x < shad y q -> forall d, In d a -> x < wr_lo y d \/ wr_hi y d <= x.
Proof.
  intros y a q x Hs Hx d Hin. destruct (sorted_in _ _ _ Hs Hin) as (H1 & H2 & H3 & _). left.
  pose proof (shad_mono y _ _ H1). pose proof (wr_lo_le_hi y d H3). lia.
Qed.
Lemma sorted_out_below : forall y a p x, sortedb p a = true -> shad y (tail_end p a) <= x -> forall d, In d a -> x < wr_lo y d \/ wr_hi y d <= x.
Proof.
  intros y a p x Hs Hx d Hin. destruct (sorted_in _ _ _ Hs Hin) as (H1 & H2 & H3 & H4). right.
  rewrite (wr_hi_eq y d H2). pose proof (shad_mono y _ _ H4). lia.
Qed.

Theorem gsh_gap : forall y tab x, (forall d, In d tab -> x < wr_lo y d \/ wr_hi y d <= x) -> gsh y tab x = 0.
Proof. intros y tab x H. unfold gsh. apply sh_upd_out. exact H. Qed.

(* [comment removed for export] *)
Lemma gsh_at : forall y tab p d x, sortedb p tab = true -> In d tab -> shad y (d_beg d) <= x < wr_hi y d -> gsh y tab x = sh1 y d x 0.
Proof.
  intros y tab p d x Hs Hin Hx. apply in_split in Hin as (pre & post & ->).
  destruct (sortedb_app _ _ _ Hs) as [Hpre Hrest]. pose proof (sortedb_cons _ _ _ Hrest) as (H1 & H2 & H3 & H4).
  unfold gsh. rewrite sh_upd_app. rewrite (sh_upd_out y pre x 0).
  2:{ apply (sorted_out_below y pre p x Hpre). pose proof (shad_mono y _ _ H1). lia. }
  change (d :: post) with ([d] ++ post). rewrite sh_upd_app. unfold sh_upd at 2. cbn [fold_left].
  apply sh_upd_out. apply (sorted_out_above y post (d_beg d + d_swr d) x H4). rewrite <- (wr_hi_eq y d H2). lia.
Qed.

Theorem gsh_obj : forall y tab p d x, sortedb p tab = true -> In d tab -> shad y (d_beg d) <= x < wr_lo y d -> gsh y tab x = 0.
Proof.
  intros y tab p d x Hs Hin Hx. destruct (sorted_in _ _ _ Hs Hin) as (_ & _ & H3 & _). pose proof (wr_lo_le_hi y d H3).
  rewrite (gsh_at y tab p d x Hs Hin) by lia. apply sh1_out. lia.
Qed.

Theorem gsh_partial : forall y tab p d, sortedb p tab = true -> In d tab -> d_size d mod 8 <> 0 -> wr_lo y d < wr_hi y d ->
  gsh y tab (wr_lo y d) = d_size d mod 8.
Proof.
  intros y tab p d Hs Hin Hm Hlt. destruct (sorted_in _ _ _ Hs Hin) as (_ & _ & H3 & _). pose proof (wr_lo_le_hi y d H3).
  rewrite (gsh_at y tab p d _ Hs Hin) by lia. unfold sh1.
  rewrite (proj2 (Z.leb_le _ _) (Z.le_refl _)), (proj2 (Z.ltb_lt _ _) Hlt), Z.eqb_refl. cbn [andb].
  destruct (Z.eqb_spec (d_size d mod 8) 0); [contradiction | reflexivity].
Qed.

Theorem gsh_redzone : forall y tab p d x, sortedb p tab = true -> In d tab -> wr_lo y d <= x < wr_hi y d ->
  (x <> wr_lo y d \/ d_size d mod 8 = 0) -> gsh y tab x = F9.
Proof.
  intros y tab p d x Hs Hin Hx Hc. destruct (sorted_in _ _ _ Hs Hin) as (_ & _ & H3 & _). pose proof (wr_lo_le_hi y d H3).
  rewrite (gsh_at y tab p d x Hs Hin) by lia. unfold sh1.
  rewrite (proj2 (Z.leb_le _ _) (proj1 Hx)), (proj2 (Z.ltb_lt _ _) (proj2 Hx)). cbn [andb].
  destruct Hc as [Hc|Hc].
  - destruct (Z.eqb_spec x (wr_lo y d)); [contradiction | reflexivity].
  - rewrite Hc. cbn. rewrite Bool.andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma run_lo_le : forall y ds d, In d ds -> run_sh_lo y ds <= sh_lo1 y d.
Proof.
  intros y ds d Hin. unfold run_sh_lo. destruct ds as [|e r]; [destruct Hin|].
  assert (G : forall l acc, sh_lo y l acc <= acc /\ forall d', In d' l -> sh_lo y l acc <= sh_lo1 y d').
  { clear. induction l as [|e r IH]; intros acc; cbn [sh_lo]; [split; [lia | intros d' []]|].
    destruct (IH (Z.min acc (sh_lo1 y e))) as [I1 I2]. split; [lia|]. intros d' [<-|Hd]; [lia | exact (I2 _ Hd)]. }
  destruct (G r (sh_lo1 y e)) as [G1 G2]. destruct Hin as [<-|Hin]; [exact G1 | exact (G2 _ Hin)].
Qed.
Lemma run_hi_ge : forall y ds d, In d ds -> sh_hi1 y d <= run_sh_hi y ds.
Proof.
  intros y ds d Hin. unfold run_sh_hi. destruct ds as [|e r]; [destruct Hin|].
  assert (G : forall l acc, acc <= sh_hi y l acc /\ forall d', In d' l -> sh_hi1 y d' <= sh_hi y l acc).
  { clear. induction l as [|e r IH]; intros acc; cbn [sh_hi]; [split; [lia | intros d' []]|].
    destruct (IH (Z.max acc (sh_hi1 y e))) as [I1 I2]. split; [lia|]. intros d' [<-|Hd]; [lia | exact (I2 _ Hd)]. }
  destruct (G r (sh_hi1 y e)) as [G1 G2]. destruct Hin as [<-|Hin]; [exact G1 | exact (G2 _ Hin)].
Qed.
(* [comment removed for export] *)
Lemma run_lo_in : forall y ds, ds <> [] -> exists d, In d ds /\ run_sh_lo y ds = sh_lo1 y d.
Proof.
  intros y ds Hne. destruct ds as [|e r]; [contradiction|]. unfold run_sh_lo.
  assert (G : forall l acc d0, acc = sh_lo1 y d0 -> exists d, (d = d0 \/ In d l) /\ sh_lo y l acc = sh_lo1 y d).
  { clear. induction l as [|e r IH]; intros acc d0 Ha; cbn [sh_lo]; [exists d0; split; [left; reflexivity | exact Ha]|].
    destruct (Z.min_spec acc (sh_lo1 y e)) as [[_ Hm]|[_ Hm]]; rewrite Hm.
    - destruct (IH acc d0 Ha) as (d & [Hd|Hd] & He); exists d; (split; [|exact He]); [left; exact Hd | right; right; exact Hd].
    - destruct (IH (sh_lo1 y e) e eq_refl) as (d & [Hd|Hd] & He); exists d; (split; [|exact He]); [right; left; symmetry; exact Hd | right; right; exact Hd]. }
  destruct (G r (sh_lo1 y e) e eq_refl) as (d & Hd & He). exists d. split; [|exact He]. destruct Hd as [->|Hd]; [left; reflexivity | right; exact Hd].
Qed.
Lemma run_hi_in : forall y ds, ds <> [] -> exists d, In d ds /\ run_sh_hi y ds = sh_hi1 y d.
Proof.
  intros y ds Hne. destruct ds as [|e r]; [contradiction|]. unfold run_sh_hi.
  assert (G : forall l acc d0, acc = sh_hi1 y d0 -> exists d, (d = d0 \/ In d l) /\ sh_hi y l acc = sh_hi1 y d).
  { clear. induction l as [|e r IH]; intros acc d0 Ha; cbn [sh_hi]; [exists d0; split; [left; reflexivity | exact Ha]|].
    destruct (Z.max_spec acc (sh_hi1 y e)) as [[_ Hm]|[_ Hm]]; rewrite Hm.
    - destruct (IH (sh_hi1 y e) e eq_refl) as (d & [Hd|Hd] & He); exists d; (split; [|exact He]); [right; left; symmetry; exact Hd | right; right; exact Hd].
    - destruct (IH acc d0 Ha) as (d & [Hd|Hd] & He); exists d; (split; [|exact He]); [left; exact Hd | right; right; exact Hd]. }
  destruct (G r (sh_hi1 y e) e eq_refl) as (d & Hd & He). exists d. split; [|exact He]. destruct Hd as [->|Hd]; [left; reflexivity | right; exact Hd].
Qed.

Theorem gsh_slice : forall y pre ds post p x, sortedb p (pre ++ ds ++ post) = true -> run_sh_lo y ds <= x < run_sh_hi y ds ->
  gsh y (pre ++ ds ++ post) x = sh_upd y ds x 0.
Proof.
  intros y pre ds post p x Hs Hx.
  destruct ds as [|e0 r0] eqn:Eds; [unfold run_sh_lo, run_sh_hi in Hx; lia|]. rewrite <- Eds in *. assert (Hne : ds <> []) by (rewrite Eds; discriminate).
  destruct (sortedb_app _ _ _ Hs) as [Hpre Hrest]. destruct (sortedb_app _ _ _ Hrest) as [Hds Hpost].
  unfold gsh. rewrite !sh_upd_app. rewrite (sh_upd_out y pre x 0).
  2:{ apply (sorted_out_below y pre p x Hpre). destruct (run_lo_in y ds Hne) as (d & Hd & El).
      destruct (sorted_in _ _ _ Hds Hd) as (H1 & _). pose proof (shad_mono y _ _ H1). unfold sh_lo1 in El. lia. }
  apply sh_upd_out. apply (sorted_out_above y post (tail_end (tail_end p pre) ds) x Hpost).
  destruct (run_hi_in y ds Hne) as (d & Hd & Eh). destruct (sorted_in _ _ _ Hds Hd) as (_ & _ & _ & H4).
  pose proof (shad_mono y _ _ H4). unfold sh_hi1 in Eh. lia.
Qed.

(* [comment removed for export] *)
Lemma gsh_list_length : forall y tab lo hi, lo <= hi -> Z.of_nat (length (gsh_list y tab lo hi)) = hi - lo.
Proof. intros y tab lo hi H. unfold gsh_list. rewrite length_map, length_seq. lia. Qed.

Lemma gsh_list_nth : forall y tab lo hi q, 0 <= q < hi - lo -> nth (Z.to_nat q) (gsh_list y tab lo hi) 0 = gsh y tab (lo + q).
Proof.
  intros y tab lo hi q Hq. unfold gsh_list.
  set (g := fun i : nat => gsh y tab (lo + Z.of_nat i)).
  rewrite (nth_indep (map g (seq 0 (Z.to_nat (hi - lo)))) 0 (g 0%nat)) by (rewrite length_map, length_seq; lia).
  rewrite (map_nth g). rewrite seq_nth by lia. unfold g. cbn [Nat.add]. rewrite Z2Nat.id by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition olist (o : option (list desc)) : list desc := match o with Some l => l | None => [] end.
Definition gtab_chkf (n : nat) (tb te lo : Z) (o : option (list desc)) : bool :=
  match o with
  | Some l => Nat.eqb (length l) n && Z.eqb (tb + 64 * Z.of_nat n) te && sortedb lo l
  | None => false
  end.
Lemma gtab_chkf_spec : forall n tb te lo o, gtab_chkf n tb te lo o = true ->
  o = Some (olist o) /\ length (olist o) = n /\ tb + 64 * Z.of_nat (length (olist o)) = te /\ sortedb lo (olist o) = true.
Proof.
  intros n tb te lo [l|] H; [|discriminate H]. cbn [gtab_chkf olist] in *.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Nat.eqb_eq in H1. apply Z.eqb_eq in H2.
  rewrite H1. repeat split; assumption.
Qed.

End GSM.
