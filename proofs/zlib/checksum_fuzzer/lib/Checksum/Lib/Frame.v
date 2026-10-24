(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import PropExec MState Mem Cells Exec Step.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mkR (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) : bvmap 5 word :=
  TNode
    (TNode (TNode (TNode (TNode (TNode TEmpty (Some x31) TEmpty) (Some x15) TEmpty) (Some x7) (TNode TEmpty (Some x23) TEmpty)) (Some x3) (TNode (TNode TEmpty (Some x19) TEmpty) (Some x11) (TNode TEmpty (Some x27) TEmpty)))
       (Some x1) (TNode (TNode (TNode TEmpty (Some x17) TEmpty) (Some x9) (TNode TEmpty (Some x25) TEmpty)) (Some x5) (TNode (TNode TEmpty (Some x21) TEmpty) (Some x13) (TNode TEmpty (Some x29) TEmpty))))
    None
    (TNode (TNode (TNode (TNode TEmpty (Some x16) TEmpty) (Some x8) (TNode TEmpty (Some x24) TEmpty)) (Some x4) (TNode (TNode TEmpty (Some x20) TEmpty) (Some x12) (TNode TEmpty (Some x28) TEmpty))) (Some x2)
       (TNode (TNode (TNode TEmpty (Some x18) TEmpty) (Some x10) (TNode TEmpty (Some x26) TEmpty)) (Some x6) (TNode (TNode TEmpty (Some x22) TEmpty) (Some x14) (TNode TEmpty (Some x30) TEmpty)))).

(* [comment removed for export] *)
(* [comment removed for export] *)

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

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition munch (W : list ivl) (m m' : word -> option byte) : Prop :=
  forall x : word, outside W (bv_unsigned x) -> m' x = m x.
Definition wmono (m m' : word -> option byte) : Prop :=
  forall x : word, wview segs m x <> None -> wview segs m' x <> None.

Lemma munch_refl : forall W m, munch W m m. Proof. intros W m x _; reflexivity. Qed.
Lemma wmono_refl : forall m, wmono m m. Proof. intros m x H; exact H. Qed.
Lemma wmono_trans : forall m1 m2 m3, wmono m1 m2 -> wmono m2 m3 -> wmono m1 m3.
Proof. intros m1 m2 m3 H1 H2 x Hx. apply H2, H1, Hx. Qed.
Lemma munch_trans : forall W m1 m2 m3, munch W m1 m2 -> munch W m2 m3 -> munch W m1 m3.
Proof. intros W m1 m2 m3 H1 H2 x Hx. rewrite (H2 x Hx). apply H1, Hx. Qed.

(* [comment removed for export] *)
Definition sub_fp (W W' : list ivl) : Prop := forall x, outside W' x -> outside W x.
Lemma munch_weaken : forall W W' m m', sub_fp W W' -> munch W m m' -> munch W' m m'.
Proof. intros W W' m m' Hs H x Hx. apply H, Hs, Hx. Qed.

(* [comment removed for export] *)
Lemma munch_write : forall W m0 m a bs,
  munch W m0 m -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
  inside W a (Z.of_nat (length bs)) ->
  munch W m0 (write_to_mem m (wa a) bs).
Proof.
  intros W m0 m a bs H Ha Hl Hin x Hx. rewrite write_to_mem_spec by lia.
  pose proof (bv_unsigned_in_range 64 x).
  destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat (length bs))); cbn [andb];
    try (apply H; exact Hx).
  exfalso. eapply (inside_not_outside W a _ (bv_unsigned x) Hin); [lia| exact Hx].
Qed.

Lemma wmono_write : forall m0 m a bs, wmono m0 m -> wmono m0 (write_to_mem m a bs).
Proof. intros m0 m a bs H x Hx. apply wview_write_mono. apply H, Hx. Qed.

(* [comment removed for export] *)
Lemma bytes_at_transport : forall W m m' A bs,
  bytes_at segs m A bs -> munch W m m' -> disjoint_from W A (Z.of_nat (length bs)) ->
  bytes_at segs m' A bs.
Proof.
  intros W m m' A bs (Ha & Hl & H) Hm Hd. split; [lia|]. split; [lia|].
  intros i Hi. unfold mrd. rewrite Hm.
  - apply H. exact Hi.
  - eapply disjoint_outside; [exact Hd|]. rewrite wa_unsigned by lia. lia.
Qed.

Lemma wr_at_transport : forall m m' A n, wr_at segs m A n -> wmono m m' -> wr_at segs m' A n.
Proof. intros m m' A n (Ha & Hn & H) Hw. split; [lia|]. split; [lia|]. intros i Hi. apply Hw, H, Hi. Qed.

Lemma rw_cells_transport : forall W m m' A cs,
  rw_cells segs m A cs -> munch W m m' -> wmono m m' ->
  disjoint_from W A (Z.of_nat (cells_size cs)) ->
  rw_cells segs m' A cs.
Proof.
  intros W m m' A cs [[Hwf Hb] Hw] Hm Hmono Hd. split; [split; [exact Hwf|]|].
  - eapply bytes_at_transport; eauto. rewrite cells_bytes_length by assumption. exact Hd.
  - eapply wr_at_transport; eauto.
Qed.

Lemma ro_cells_transport : forall W m m' A cs,
  ro_cells segs m A cs -> munch W m m' ->
  disjoint_from W A (Z.of_nat (cells_size cs)) ->
  ro_cells segs m' A cs.
Proof.
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

Lemma stk_split : forall m lo mid hi, stk m lo hi -> (lo <= mid <= hi)%Z -> stk m lo mid /\ stk m mid hi.
Proof. intros m lo mid hi (H1 & H2 & H) Hm. split; (split; [lia|]; split; [lia|]); intros a Ha; apply H; lia. Qed.

Lemma stk_merge : forall m lo mid hi, stk m lo mid -> stk m mid hi -> (lo <= mid <= hi)%Z -> stk m lo hi.
Proof.
  intros m lo mid hi (A1 & A2 & A) (B1 & B2 & B) Hm. split; [lia|]. split; [lia|].
  intros a Ha. destruct (Z.ltb_spec0 a mid); [apply A | apply B]; lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stk_bytes : forall m lo hi, stk m lo hi -> (lo <= hi)%Z ->
  exists bs, length bs = Z.to_nat (hi - lo) /\ bytes_at segs m lo bs.
Proof.
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

Lemma stk_carve : forall m lo hi (n : nat),
  stk m lo hi -> (lo <= hi - Z.of_nat n)%Z ->
  stk m lo (hi - Z.of_nat n) /\ exists junk, rw_cells segs m (hi - Z.of_nat n) [CB n junk].
Proof.
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
Lemma stk_of_rw_cells : forall m A cs,
  rw_cells segs m A cs -> stk m A (A + Z.of_nat (cells_size cs)).
Proof.
  intros m A cs [[Hwf (Ha & Hl & Hb)] (_ & _ & Hw)].
  rewrite cells_bytes_length in Hl, Hb by assumption.
  split; [lia|]. split; [lia|]. intros a Hr. split.
  - replace a with (A + (a - A))%Z by lia. apply Hw. lia.
  - replace a with (A + Z.of_nat (Z.to_nat (a - A)))%Z by lia. rewrite Hb by lia.
    destruct (nth_error (cells_bytes cs) (Z.to_nat (a - A))) eqn:E; [eexists; reflexivity|].
    apply nth_error_None in E. rewrite cells_bytes_length in E by assumption. lia.
Qed.

Lemma stk_release : forall m lo A cs,
  stk m lo A -> rw_cells segs m A cs -> (lo <= A)%Z ->
  stk m lo (A + Z.of_nat (cells_size cs)).
Proof.
  intros m lo A cs Hs Hc Hle. pose proof (rw_cells_bound segs m A cs Hc).
  eapply stk_merge; [exact Hs | apply stk_of_rw_cells; exact Hc | lia].
Qed.

(* [comment removed for export] *)
Lemma stk_write : forall m lo hi a bs,
  stk m lo hi -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z -> stk (write_to_mem m (wa a) bs) lo hi.
Proof.
  intros m lo hi a bs (H1 & H2 & H) Ha Hl. split; [lia|]. split; [lia|]. intros x Hx.
  destruct (H x Hx) as [Hw (b & Hb)]. split.
  - apply wview_write_mono. exact Hw.
  - unfold mrd. rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
    destruct (Z.leb_spec0 a x); destruct (Z.ltb_spec0 x (a + Z.of_nat (length bs))); cbn [andb]; try (eexists; exact Hb).
    destruct (nth_error bs (Z.to_nat (x - a))) eqn:E; [eexists; reflexivity|]. apply nth_error_None in E. lia.
Qed.

Lemma stk_transport : forall W m m' lo hi,
  stk m lo hi -> munch W m m' -> wmono m m' ->
  (forall x, (lo <= x < hi)%Z -> outside W x \/ exists b, m' (wa x) = Some b) ->
  stk m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) Hm Hw Hcase. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hwa (b & Hb)]. split; [apply Hw; exact Hwa|].
  destruct (Hcase a Ha) as [Ho | (b' & Hb')].
  - exists b. unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
  - exists b'. unfold mrd. rewrite Hb'. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma stk_transport_disjoint : forall W m m' lo hi,
  stk m lo hi -> munch W m m' -> wmono m m' -> disjoint_from W lo (hi - lo) -> stk m' lo hi.
Proof.
  intros. eapply stk_transport; eauto. intros x Hx. left. eapply disjoint_outside; eauto. lia.
Qed.

End WithSegs.
