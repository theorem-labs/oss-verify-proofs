(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import LiaTuning MState Mem Cells Exec Step.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mkR (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) : bvmap 5 word :=
  (* [comment removed for export] *)
  @TNode W64
    (@TNode W64 (@TNode W64 (@TNode W64 (@TNode W64 (@TNode W64 (@TEmpty W64) (@Some (bv 64) x31) (@TEmpty W64)) (@Some (bv 64) x15) (@TEmpty W64)) (@Some (bv 64) x7) (@TNode W64 (@TEmpty W64) (@Some (bv 64) x23) (@TEmpty W64))) (@Some (bv 64) x3) (@TNode W64 (@TNode W64 (@TEmpty W64) (@Some (bv 64) x19) (@TEmpty W64)) (@Some (bv 64) x11) (@TNode W64 (@TEmpty W64) (@Some (bv 64) x27) (@TEmpty W64))))
       (@Some (bv 64) x1) (@TNode W64 (@TNode W64 (@TNode W64 (@TEmpty W64) (@Some (bv 64) x17) (@TEmpty W64)) (@Some (bv 64) x9) (@TNode W64 (@TEmpty W64) (@Some (bv 64) x25) (@TEmpty W64))) (@Some (bv 64) x5) (@TNode W64 (@TNode W64 (@TEmpty W64) (@Some (bv 64) x21) (@TEmpty W64)) (@Some (bv 64) x13) (@TNode W64 (@TEmpty W64) (@Some (bv 64) x29) (@TEmpty W64)))))
    (@None W64)
    (@TNode W64 (@TNode W64 (@TNode W64 (@TNode W64 (@TEmpty W64) (@Some (bv 64) x16) (@TEmpty W64)) (@Some (bv 64) x8) (@TNode W64 (@TEmpty W64) (@Some (bv 64) x24) (@TEmpty W64))) (@Some (bv 64) x4) (@TNode W64 (@TNode W64 (@TEmpty W64) (@Some (bv 64) x20) (@TEmpty W64)) (@Some (bv 64) x12) (@TNode W64 (@TEmpty W64) (@Some (bv 64) x28) (@TEmpty W64)))) (@Some (bv 64) x2)
       (@TNode W64 (@TNode W64 (@TNode W64 (@TEmpty W64) (@Some (bv 64) x18) (@TEmpty W64)) (@Some (bv 64) x10) (@TNode W64 (@TEmpty W64) (@Some (bv 64) x26) (@TEmpty W64))) (@Some (bv 64) x6) (@TNode W64 (@TNode W64 (@TEmpty W64) (@Some (bv 64) x22) (@TEmpty W64)) (@Some (bv 64) x14) (@TNode W64 (@TEmpty W64) (@Some (bv 64) x30) (@TEmpty W64))))).

(* [comment removed for export] *)
Lemma mkR_spec : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
  mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 =
  bvmap_set (Z_to_bv 5 31) x31 (bvmap_set (Z_to_bv 5 30) x30 (bvmap_set (Z_to_bv 5 29) x29 (bvmap_set (Z_to_bv 5 28) x28 (
  bvmap_set (Z_to_bv 5 27) x27 (bvmap_set (Z_to_bv 5 26) x26 (bvmap_set (Z_to_bv 5 25) x25 (bvmap_set (Z_to_bv 5 24) x24 (
  bvmap_set (Z_to_bv 5 23) x23 (bvmap_set (Z_to_bv 5 22) x22 (bvmap_set (Z_to_bv 5 21) x21 (bvmap_set (Z_to_bv 5 20) x20 (
  bvmap_set (Z_to_bv 5 19) x19 (bvmap_set (Z_to_bv 5 18) x18 (bvmap_set (Z_to_bv 5 17) x17 (bvmap_set (Z_to_bv 5 16) x16 (
  bvmap_set (Z_to_bv 5 15) x15 (bvmap_set (Z_to_bv 5 14) x14 (bvmap_set (Z_to_bv 5 13) x13 (bvmap_set (Z_to_bv 5 12) x12 (
  bvmap_set (Z_to_bv 5 11) x11 (bvmap_set (Z_to_bv 5 10) x10 (bvmap_set (Z_to_bv 5 9) x9 (bvmap_set (Z_to_bv 5 8) x8 (
  bvmap_set (Z_to_bv 5 7) x7 (bvmap_set (Z_to_bv 5 6) x6 (bvmap_set (Z_to_bv 5 5) x5 (bvmap_set (Z_to_bv 5 4) x4 (
  bvmap_set (Z_to_bv 5 3) x3 (bvmap_set (Z_to_bv 5 2) x2 (bvmap_set (Z_to_bv 5 1) x1 bvmap_empty)))))))))))))))))))))))))))))).
Proof. intros. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ivl := (Z * Z)%type.   (* [comment removed for export] *)

Fixpoint outside (W : list ivl) (x : Z) : Prop :=
  match W with
  | [] => True
  | (lo, hi) :: W' => ~ (lo <= x < hi)%Z /\ outside W' x
  end.

Fixpoint inside (W : list ivl) (a : Z) (n : Z) : Prop :=
  match W with
  | [] => False
  | (lo, hi) :: W' => (lo <= a /\ a + n <= hi)%Z \/ inside W' a n
  end.

Fixpoint disjoint_from (W : list ivl) (a : Z) (n : Z) : Prop :=
  match W with
  | [] => True
  | (lo, hi) :: W' => (a + n <= lo \/ hi <= a)%Z /\ disjoint_from W' a n
  end.

Lemma inside_not_outside : forall W a n x, inside W a n -> (a <= x < a + n)%Z -> ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros a n x Hin Hx; [tauto|].
  intros [H1 H2]. destruct Hin as [Hin|Hin]; [lia|]. exact (IH _ _ _ Hin Hx H2).
Qed.

Lemma disjoint_outside : forall W a n x, disjoint_from W a n -> (a <= x < a + n)%Z -> outside W x.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros a n x Hd Hx; [exact I|].
  destruct Hd as [H1 H2]. split; [lia|]. eauto.
Qed.

(* [comment removed for export] *)
Definition munch (W : list ivl) (m m' : word -> option byte) : Prop :=
  forall x : word, outside W (bv_unsigned x) -> m' x = m x.
Definition wmono (segs : list Segment) (m m' : word -> option byte) : Prop :=
  forall x : word, m x <> None -> m' x <> None.

Lemma munch_refl : forall W m, munch W m m. Proof. intros W m x _; reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.

#[using="Type"] Lemma wmono_refl : forall m, wmono segs m m. Proof. LiaFast.lf_pins LiaFast.u0. intros m x H; exact H. Qed.
#[using="Type"] Lemma wmono_trans : forall m1 m2 m3, wmono segs m1 m2 -> wmono segs m2 m3 -> wmono segs m1 m3.
Proof. LiaFast.lf_pins LiaFast.u0. intros m1 m2 m3 H1 H2 x Hx. apply H2, H1, Hx. Qed.
#[using="Type"] Lemma wmono_wview : forall m m', wmono segs m m' ->
  forall x, wview segs m x <> None -> wview segs m' x <> None.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m m' H x. unfold wview. specialize (H x).
  destruct (m x) as [b|]; destruct (m' x) as [b'|]; intros Hx; try discriminate.
  - exfalso. apply H; [discriminate| reflexivity].
  - exact Hx.
Qed.
#[using="Type"] Lemma wmono_write_to_mem : forall m a bs, wmono segs m (write_to_mem m a bs).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m a bs. revert m a. induction bs as [|b bs IH]; intros m a x H; cbn; [exact H|].
  apply IH. destruct (bv_eqb x a); [discriminate|]. exact H.
Qed.
#[using="Type"] Lemma munch_trans : forall W m1 m2 m3, munch W m1 m2 -> munch W m2 m3 -> munch W m1 m3.
Proof. LiaFast.lf_pins LiaFast.u0. intros W m1 m2 m3 H1 H2 x Hx. rewrite (H2 x Hx). apply H1, Hx. Qed.

(* [comment removed for export] *)
Definition sub_fp (W W' : list ivl) : Prop := forall x, outside W' x -> outside W x.
#[using="Type"] Lemma munch_weaken : forall W W' m m', sub_fp W W' -> munch W m m' -> munch W' m m'.
Proof. LiaFast.lf_pins LiaFast.u0. intros W W' m m' Hs H x Hx. apply H, Hs, Hx. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma munch_write : forall W m0 m a bs,
  munch W m0 m -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
  inside W a (Z.of_nat (length bs)) ->
  munch W m0 (write_to_mem m (wa a) bs).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros W m0 m a bs H Ha Hl Hin x Hx. rewrite write_to_mem_spec by lia.
  pose proof (bv_unsigned_in_range 64 x).
  destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat (length bs))); cbn [andb];
    try (apply H; exact Hx).
  exfalso. eapply (inside_not_outside W a _ (bv_unsigned x) Hin); [lia| exact Hx].
Qed.

#[using="Type"] Lemma wmono_write : forall m0 m a bs, wmono segs m0 m -> wmono segs m0 (write_to_mem m a bs).
Proof. LiaFast.lf_pins LiaFast.u0. intros m0 m a bs H. eapply wmono_trans; [exact H| apply wmono_write_to_mem]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma bytes_at_transport : forall W m m' A bs,
  bytes_at segs m A bs -> munch W m m' -> disjoint_from W A (Z.of_nat (length bs)) ->
  bytes_at segs m' A bs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros W m m' A bs (Ha & Hl & H) Hm Hd. split; [lia|]. split; [lia|].
  intros i Hi. unfold mrd. rewrite Hm.
  - apply H. exact Hi.
  - eapply disjoint_outside; [exact Hd|]. rewrite wa_unsigned by lia. lia.
Qed.

#[using="Type"] Lemma wr_at_transport : forall m m' A n, wr_at segs m A n -> wmono segs m m' -> wr_at segs m' A n.
Proof. LiaFast.lf_pins LiaFast.u0. intros m m' A n (Ha & Hn & H) Hw. split; [lia|]. split; [lia|]. intros i Hi. apply (wmono_wview m m' Hw), H, Hi. Qed.

#[using="Type"] Lemma rw_cells_transport : forall W m m' A cs,
  rw_cells segs m A cs -> munch W m m' -> wmono segs m m' ->
  disjoint_from W A (Z.of_nat (cells_size cs)) ->
  rw_cells segs m' A cs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros W m m' A cs [[Hwf Hb] Hw] Hm Hmono Hd. split; [split; [exact Hwf|]|].
  - eapply bytes_at_transport; eauto. rewrite cells_bytes_length by assumption. exact Hd.
  - eapply wr_at_transport; eauto.
Qed.

#[using="Type"] Lemma ro_cells_transport : forall W m m' A cs,
  ro_cells segs m A cs -> munch W m m' ->
  disjoint_from W A (Z.of_nat (cells_size cs)) ->
  ro_cells segs m' A cs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros W m m' A cs [Hwf Hb] Hm Hd. split; [exact Hwf|].
  eapply bytes_at_transport; eauto. rewrite cells_bytes_length by assumption. exact Hd.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stk (m : word -> option byte) (lo hi : Z) : Prop :=
  (0 <= lo)%Z /\ (hi <= 2^64)%Z /\
  forall a, (lo <= a < hi)%Z -> wview segs m (wa a) <> None /\ exists b, mrd segs m (wa a) = Some b.

#[using="Type"] Lemma stk_split : forall m lo mid hi, stk m lo hi -> (lo <= mid <= hi)%Z -> stk m lo mid /\ stk m mid hi.
Proof. LiaFast.lf_pins LiaFast.u0. intros m lo mid hi (H1 & H2 & H) Hm. split; (split; [lia|]; split; [lia|]); intros a Ha; apply H; lia. Qed.

#[using="Type"] Lemma stk_merge : forall m lo mid hi, stk m lo mid -> stk m mid hi -> (lo <= mid <= hi)%Z -> stk m lo hi.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m lo mid hi (A1 & A2 & A) (B1 & B2 & B) Hm. split; [lia|]. split; [lia|].
  intros a Ha. destruct (Z.ltb_spec0 a mid); [apply A | apply B]; lia.
Qed.

#[using="Type"] Lemma stk_empty : forall m lo, (0 <= lo <= 2^64)%Z -> stk m lo lo.
Proof. LiaFast.lf_pins LiaFast.u0. intros. split; [lia|]. split; [lia|]. intros a Ha. lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma stk_bytes : forall m lo hi, stk m lo hi -> (lo <= hi)%Z ->
  exists bs, length bs = Z.to_nat (hi - lo) /\ bytes_at segs m lo bs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m lo hi (H1 & H2 & H) Hle.
  set (n := Z.to_nat (hi - lo)).
  assert (G : forall k, (k <= n)%nat -> exists bs, length bs = k /\ forall i, (i < k)%nat -> mrd segs m (wa (lo + Z.of_nat i)) = nth_error bs i).
  { induction k as [|k IH]; intros Hk.
    - exists []. split; [reflexivity|]. intros i Hi; lia.
    - destruct (IH ltac:(lia)) as (bs & Hlen & Hbs).
      destruct (H (lo + Z.of_nat k)%Z ltac:(lia)) as [_ (b & Hb)].
      exists (bs ++ [b]). split. { rewrite app_length; cbn; lia. }
      intros i Hi. destruct (Nat.eqb_spec i k).
      + subst i. rewrite nth_error_app2 by lia. rewrite Hlen, Nat.sub_diag. exact Hb.
      + rewrite nth_error_app1 by lia. apply Hbs. lia. }
  destruct (G n ltac:(lia)) as (bs & Hlen & Hbs). exists bs. split; [exact Hlen|].
  split; [lia|]. split; [lia|]. intros i Hi. apply Hbs. lia.
Qed.

#[using="Type"] Lemma stk_carve : forall m lo hi (n : nat),
  stk m lo hi -> (lo <= hi - Z.of_nat n)%Z ->
  stk m lo (hi - Z.of_nat n) /\ exists junk, rw_cells segs m (hi - Z.of_nat n) [CB n junk].
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m lo hi n Hs Hle. pose proof Hs as (H1 & H2 & H).
  destruct (stk_split m lo (hi - Z.of_nat n) hi Hs ltac:(lia)) as [Hlo Hhi].
  split; [exact Hlo|].
  destruct (stk_bytes m (hi - Z.of_nat n) hi Hhi ltac:(lia)) as (bs & Hlen & Hb).
  exists bs. split.
  - split. { cbn. split; [lia|exact I]. }
    cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
    intros i Hi. apply H. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma stk_of_rw_cells : forall m A cs,
  rw_cells segs m A cs -> stk m A (A + Z.of_nat (cells_size cs)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A cs [[Hwf (Ha & Hl & Hb)] (_ & _ & Hw)].
  rewrite cells_bytes_length in Hl, Hb by assumption.
  split; [lia|]. split; [lia|]. intros a Hr. split.
  - replace a with (A + (a - A))%Z by lia. apply Hw. lia.
  - replace a with (A + Z.of_nat (Z.to_nat (a - A)))%Z by lia. rewrite Hb by lia.
    destruct (nth_error (cells_bytes cs) (Z.to_nat (a - A))) eqn:E; [eexists; reflexivity|].
    apply nth_error_None in E. rewrite cells_bytes_length in E by assumption. lia.
Qed.

#[using="Type"] Lemma stk_release : forall m lo A cs,
  stk m lo A -> rw_cells segs m A cs -> (lo <= A)%Z ->
  stk m lo (A + Z.of_nat (cells_size cs)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m lo A cs Hs Hc Hle. pose proof (rw_cells_bound segs m A cs Hc).
  eapply stk_merge; [exact Hs | apply stk_of_rw_cells; exact Hc | lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma stk_write : forall m lo hi a bs,
  stk m lo hi -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z -> stk (write_to_mem m (wa a) bs) lo hi.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m lo hi a bs (H1 & H2 & H) Ha Hl. split; [lia|]. split; [lia|]. intros x Hx.
  destruct (H x Hx) as [Hw (b & Hb)]. split.
  - apply wview_write_mono. exact Hw.
  - unfold mrd. rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
    destruct (Z.leb_spec0 a x); destruct (Z.ltb_spec0 x (a + Z.of_nat (length bs))); cbn [andb]; try (eexists; exact Hb).
    destruct (nth_error bs (Z.to_nat (x - a))) eqn:E; [eexists; reflexivity|]. apply nth_error_None in E. lia.
Qed.

#[using="Type"] Lemma stk_transport : forall W m m' lo hi,
  stk m lo hi -> munch W m m' -> wmono segs m m' ->
  (forall x, (lo <= x < hi)%Z -> outside W x \/ exists b, m' (wa x) = Some b) ->
  stk m' lo hi.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros W m m' lo hi (H1 & H2 & H) Hm Hw Hcase. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hwa (b & Hb)]. split; [apply (wmono_wview m m' Hw); exact Hwa|].
  destruct (Hcase a Ha) as [Ho | (b' & Hb')].
  - exists b. unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
  - exists b'. unfold mrd. rewrite Hb'. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma stk_transport_disjoint : forall W m m' lo hi,
  stk m lo hi -> munch W m m' -> wmono segs m m' -> disjoint_from W lo (hi - lo) -> stk m' lo hi.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros. eapply stk_transport; eauto. intros x Hx. left. eapply disjoint_outside; eauto. lia.
Qed.

End WithSegs.
