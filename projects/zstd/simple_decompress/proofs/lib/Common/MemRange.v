(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Frame.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Definition rdbl (m : word -> option byte) (lo hi : Z) : Prop :=
  0 <= lo /\ hi <= 2^64 /\ forall a, lo <= a < hi -> exists b, mrd segs m (wa a) = Some b.

Lemma rdbl_sub : forall m lo hi lo' hi', rdbl m lo hi -> lo <= lo' -> hi' <= hi -> rdbl m lo' hi'.
Proof. intros m lo hi lo' hi' (H1 & H2 & H) A B. split; [lia|]. split; [lia|]. intros a Ha. apply H. lia. Qed.

Lemma rdbl_of_bytes_at : forall m a bs, bytes_at segs m a bs -> rdbl m a (a + Z.of_nat (length bs)).
Proof.
  intros m a bs (H1 & H2 & H). split; [lia|]. split; [lia|]. intros x Hx.
  replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia. rewrite H by lia.
  destruct (nth_error bs (Z.to_nat (x - a))) eqn:E; [eexists; reflexivity|]. apply nth_error_None in E. lia.
Qed.

Lemma rdbl_of_stk : forall m lo hi, stk segs m lo hi -> rdbl m lo hi.
Proof. intros m lo hi (H1 & H2 & H). split; [lia|]. split; [lia|]. intros a Ha. exact (proj2 (H a Ha)). Qed.

(* [comment removed for export] *)
Lemma rdbl_bytes : forall m lo hi, rdbl m lo hi -> lo <= hi ->
  exists bs, length bs = Z.to_nat (hi - lo) /\ bytes_at segs m lo bs.
Proof.
  intros m lo hi (H1 & H2 & H) Hle.
  set (n := Z.to_nat (hi - lo)).
  assert (G : forall k, (k <= n)%nat -> exists bs, length bs = k /\ forall i, (i < k)%nat -> mrd segs m (wa (lo + Z.of_nat i)) = nth_error bs i).
  { induction k as [|k IH]; intros Hk.
    - exists []. split; [reflexivity|]. intros i Hi; lia.
    - destruct (IH ltac:(lia)) as (bs & Hlen & Hbs).
      destruct (H (lo + Z.of_nat k) ltac:(lia)) as (b & Hb).
      exists (bs ++ [b]). split. { rewrite length_app; cbn; lia. }
      intros i Hi. destruct (Nat.eqb_spec i k).
      + subst i. rewrite nth_error_app2 by lia. rewrite Hlen, Nat.sub_diag. exact Hb.
      + rewrite nth_error_app1 by lia. apply Hbs. lia. }
  destruct (G n ltac:(lia)) as (bs & Hlen & Hbs). exists bs. split; [exact Hlen|].
  split; [lia|]. split; [lia|]. intros i Hi. apply Hbs. lia.
Qed.

(* [comment removed for export] *)
Lemma rdbl_read : forall m lo hi a (k : nat), rdbl m lo hi -> lo <= a -> a + Z.of_nat k <= hi ->
  exists bs, length bs = k /\ ov_read_bytes segs m (wa a) k = Some bs.
Proof.
  intros m lo hi a k R Ha Hk.
  destruct (rdbl_bytes m a (a + Z.of_nat k) (rdbl_sub _ _ _ _ _ R Ha Hk) ltac:(lia)) as (bs & Hlen & HB).
  replace (a + Z.of_nat k - a) with (Z.of_nat k) in Hlen by lia. rewrite Nat2Z.id in Hlen.
  exists bs. split; [exact Hlen|].
  pose proof (bytes_at_read segs m a bs 0 k HB ltac:(lia) ltac:(cbn; lia)) as E.
  rewrite Z.add_0_r in E. rewrite E. cbn [Z.to_nat skipn]. rewrite <- Hlen. rewrite firstn_all. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdbl_write : forall m lo hi a bs,
  rdbl m lo hi -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 -> rdbl (write_to_mem m (wa a) bs) lo hi.
Proof.
  intros m lo hi a bs (H1 & H2 & H) Ha Hl. split; [lia|]. split; [lia|]. intros x Hx.
  destruct (H x Hx) as (b & Hb).
  unfold mrd. rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
  destruct (Z.leb_spec0 a x); destruct (Z.ltb_spec0 x (a + Z.of_nat (length bs))); cbn [andb]; try (eexists; exact Hb).
  destruct (nth_error bs (Z.to_nat (x - a))) eqn:E; [eexists; reflexivity|]. apply nth_error_None in E. lia.
Qed.

(* [comment removed for export] *)
Lemma rdbl_transport : forall W m m' lo hi,
  rdbl m lo hi -> munch W m m' ->
  (forall x, lo <= x < hi -> outside W x \/ exists b, m' (wa x) = Some b) ->
  rdbl m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) Hm Hcase. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as (b & Hb).
  destruct (Hcase a Ha) as [Ho | (b' & Hb')].
  - exists b. unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
  - exists b'. unfold mrd. rewrite Hb'. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdbl_after_sub : forall m m' lo hi a b,
  rdbl m lo hi -> munch [(a, b)] m m' -> rdbl m' a b -> rdbl m' lo hi.
Proof.
  intros m m' lo hi a b (H1 & H2 & H) MU (_ & _ & HS). split; [lia|]. split; [lia|]. intros x Hx.
  destruct (Z_lt_le_dec x a) as [L|L]; [| destruct (Z_lt_le_dec x b) as [L2|L2]].
  - destruct (H x Hx) as (b0 & Hb). exists b0. unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. cbn [outside]. split; [lia| exact I].
  - apply HS. lia.
  - destruct (H x Hx) as (b0 & Hb). exists b0. unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. cbn [outside]. split; [lia| exact I].
Qed.

Lemma stk_after_sub : forall m m' lo hi a b,
  stk segs m lo hi -> munch [(a, b)] m m' -> wmono segs m m' -> stk segs m' a b -> stk segs m' lo hi.
Proof.
  intros m m' lo hi a b ST MU WM SS. pose proof ST as (H1 & H2 & H). pose proof SS as (_ & _ & HS).
  split; [lia|]. split; [lia|]. intros x Hx.
  destruct (Z_lt_le_dec x a) as [L|L]; [| destruct (Z_lt_le_dec x b) as [L2|L2]].
  - destruct (H x Hx) as [W (b0 & Hb)]. split; [apply WM; exact W|]. exists b0. unfold mrd in *. rewrite MU; [exact Hb|].
    rewrite wa_unsigned by lia. cbn [outside]. split; [lia| exact I].
  - apply HS. lia.
  - destruct (H x Hx) as [W (b0 & Hb)]. split; [apply WM; exact W|]. exists b0. unfold mrd in *. rewrite MU; [exact Hb|].
    rewrite wa_unsigned by lia. cbn [outside]. split; [lia| exact I].
Qed.

(* [comment removed for export] *)
Lemma stk_store_ok : forall m lo hi a (j : nat), stk segs m lo hi -> lo <= a -> a + Z.of_nat j <= hi ->
  store_ok segs m (wa a) j = true.
Proof.
  intros m lo hi a j (H1 & H2 & H) Ha Hj.
  replace a with (a + 0) by lia. apply (wr_at_store_ok segs m a (Z.of_nat j) 0 j); [| lia | lia].
  split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
Qed.

(* [comment removed for export] *)
Lemma rdbl_read_at : forall m lo hi A (k : nat) a, rdbl m lo hi -> lo <= A -> A + Z.of_nat k <= hi -> a = wa A ->
  exists bs, length bs = k /\ ov_read_bytes segs m a k = Some bs.
Proof. intros m lo hi A k a R H1 H2 ->. eapply rdbl_read; eauto. Qed.
Lemma stk_read_at : forall m lo hi A (k : nat) a, stk segs m lo hi -> lo <= A -> A + Z.of_nat k <= hi -> a = wa A ->
  exists bs, length bs = k /\ ov_read_bytes segs m a k = Some bs.
Proof. intros m lo hi A k a R H1 H2 E. eapply rdbl_read_at; [apply rdbl_of_stk; exact R| exact H1| exact H2| exact E]. Qed.
Lemma stk_store_ok_at : forall m lo hi A (j : nat) a, stk segs m lo hi -> lo <= A -> A + Z.of_nat j <= hi -> a = wa A ->
  store_ok segs m a j = true.
Proof. intros m lo hi A j a R H1 H2 ->. eapply stk_store_ok; eauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mv_inv (S D n : Z) (m0 m1 : word -> option byte) : Prop :=
  stk segs m1 D (D + n) /\ rdbl m1 S (S + n) /\ mem_inv segs m1 /\ munch [(D, D + n)] m0 m1 /\ wmono segs m0 m1.

Lemma mv_inv_init : forall S D n m, stk segs m D (D + n) -> rdbl m S (S + n) -> mem_inv segs m -> mv_inv S D n m m.
Proof. intros. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [apply munch_refl| apply wmono_refl]. Qed.

(* [comment removed for export] *)
Lemma mv_read : forall S D n m0 m1 P (k : nat) a,
  mv_inv S D n m0 m1 -> 0 <= P -> P + Z.of_nat k <= n -> a = wa (S + P) ->
  exists bs, length bs = k /\ ov_read_bytes segs m1 a k = Some bs.
Proof. intros S D n m0 m1 P k a (_ & R & _) HP Hk ->. eapply rdbl_read; [exact R| lia| lia]. Qed.

(* [comment removed for export] *)
Lemma mv_store_ok : forall S D n m0 m1 P (k : nat) a,
  mv_inv S D n m0 m1 -> 0 <= P -> P + Z.of_nat k <= n -> a = wa (D + P) -> store_ok segs m1 a k = true.
Proof. intros S D n m0 m1 P k a (ST & _) HP Hk ->. eapply stk_store_ok; [exact ST| lia| lia]. Qed.

(* [comment removed for export] *)
Lemma mv_store : forall S D n m0 m1 P (k : nat) xs a,
  mv_inv S D n m0 m1 -> 0 <= P -> P + Z.of_nat k <= n -> length xs = k -> a = wa (D + P) ->
  mv_inv S D n m0 (write_to_mem m1 a xs).
Proof.
  intros S D n m0 m1 P k xs a (ST & R & MI & MU & WM) HP Hk HL ->.
  pose proof ST as (D0 & Dn & _).
  split; [apply stk_write; [exact ST| lia| lia]|].
  split; [apply rdbl_write; [exact R| lia| lia]|].
  split. { apply mem_inv_store; [exact MI|]. rewrite HL. eapply stk_store_ok; [exact ST| lia| lia]. }
  split; [| apply wmono_write; exact WM].
  apply munch_write; [exact MU| lia| lia|]. cbn [inside]. left. lia.
Qed.

End WithSegs.
