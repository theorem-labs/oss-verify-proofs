(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BecLazy.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma wr_at_wmono : forall m m' a n, wr_at asegs m a n -> wmono asegs m m' -> wr_at asegs m' a n.
Proof. intros m m' a n (W1 & W2 & W) WM. split; [lia|]. split; [lia|]. intros i Hi. apply WM. apply W. exact Hi. Qed.

Lemma mdef_of_wr_at : forall m a n, wr_at asegs m a n -> 0x6e8000 <= a -> CRep.mdef m a n.
Proof.
  intros m a n (W0 & W1 & W) Ha i Hi. specialize (W i Hi). unfold wview in W.
  unfold wa in W. rewrite HLib.u64_of_Z in W by lia.
  destruct (m (Z_to_bv 64 (a + i))) eqn:E; [discriminate|].
  rewrite BecLazy.asegs_find_segment_none_high in W by lia. congruence.
Qed.

Lemma stk_wmono : forall m m' lo hi, stk asegs m lo hi -> wmono asegs m m' -> 0x6e8000 <= lo -> stk asegs m' lo hi.
Proof.
  intros m m' lo hi (S0 & S1 & S) WM Hlo. split; [lia|]. split; [lia|]. intros a Ha.
  destruct (S a Ha) as [W _]. pose proof (WM _ W) as W'. split; [exact W'|].
  unfold wview in W'. unfold wa in W' |- *. rewrite HLib.u64_of_Z in W' by lia.
  destruct (m' (Z_to_bv 64 a)) as [b|] eqn:E.
  - exists b. unfold mrd. rewrite E. reflexivity.
  - rewrite BecLazy.asegs_find_segment_none_high in W' by lia. congruence.
Qed.

Lemma wr_at_rw_cells : forall m a n, wr_at asegs m a n -> 0x6e8000 <= a -> 0 <= n ->
  exists bs, rw_cells asegs m a [CB (Z.to_nat n) bs].
Proof.
  intros m a n W Ha Hn. pose proof (mdef_of_wr_at m a n W Ha) as MD.
  assert (EX : forall k, (k <= Z.to_nat n)%nat -> exists bs, length bs = k /\ bytes_at asegs m a bs).
  { induction k as [|k IH]; intros Hk.
    - exists []. split; [reflexivity|]. split; [lia|]. split; [cbn; destruct W as (_ & W1 & _); lia|]. intros i Hi. cbn in Hi. lia.
    - destruct (IH ltac:(lia)) as (bs & Lb & Bb).
      specialize (MD (Z.of_nat k) ltac:(lia)). destruct (m (Z_to_bv 64 (a + Z.of_nat k))) as [b|] eqn:E; [|congruence].
      exists (bs ++ [b]). rewrite length_app, Lb. cbn [length]. split; [lia|]. apply bytes_at_app. split; [exact Bb|].
      destruct W as (W0 & W1 & _). split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. destruct i as [|i]; [|lia].
      cbn. unfold mrd, wa. rewrite Lb, Z.add_0_r, E. reflexivity. }
  destruct (EX (Z.to_nat n) ltac:(lia)) as (bs & Lb & Bb). exists bs.
  split; [split; [cbn; split; [exact Lb | exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact Bb]|].
  cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact W.
Qed.

Lemma u8arr_sub : forall m A bs i k, u8arr asegs m A bs -> 0 <= i -> 0 <= k -> i + k <= Z.of_nat (length bs) ->
  u8arr asegs m (A + i) (firstn (Z.to_nat k) (skipn (Z.to_nat i) bs)).
Proof.
  intros m A bs i k [B W] Hi Hk Hik.
  assert (L : length (firstn (Z.to_nat k) (skipn (Z.to_nat i) bs)) = Z.to_nat k)
    by (rewrite firstn_length_le; [reflexivity| rewrite length_skipn; lia]).
  split.
  - rewrite <- (firstn_skipn (Z.to_nat i) bs) in B. apply bytes_at_app in B as [_ B2].
    rewrite firstn_length_le in B2 by lia. rewrite Z2Nat.id in B2 by lia.
    rewrite <- (firstn_skipn (Z.to_nat k) (skipn (Z.to_nat i) bs)) in B2. apply bytes_at_app in B2 as [B3 _]. exact B3.
  - destruct W as (W1 & W2 & W). rewrite L. split; [lia|]. split; [lia|]. intros j Hj.
    replace (A + i + j) with (A + (i + j)) by lia. apply W. lia.
Qed.

Lemma skipn_repeat' : forall (A : Type) (x : A) n k, skipn k (repeat x n) = repeat x (n - k).
Proof. intros A x n. induction n as [|n IH]; intros [|k]; cbn; try reflexivity. apply IH. Qed.

Lemma firstn_repeat' : forall (A : Type) (x : A) n k, firstn k (repeat x n) = repeat x (Nat.min k n).
Proof. intros A x n. induction n as [|n IH]; intros [|k]; cbn; try reflexivity. f_equal. apply IH. Qed.

Lemma rw_cells_CB_sub : forall m A n bs i k, rw_cells asegs m A [CB n bs] -> 0 <= i -> 0 <= k -> i + k <= Z.of_nat n ->
  exists bs', rw_cells asegs m (A + i) [CB (Z.to_nat k) bs'].
Proof.
  intros m A n bs i k C Hi Hk Hik.
  assert (LN : length bs = n) by (destruct C as [[[X _] _] _]; exact X).
  pose proof (u8arr_of_rw_cells asegs m A n bs C) as U.
  pose proof (u8arr_sub m A bs i k U Hi Hk ltac:(lia)) as U2.
  exists (firstn (Z.to_nat k) (skipn (Z.to_nat i) bs)).
  pose proof (rw_cells_of_u8arr asegs m _ _ U2) as C2.
  rewrite firstn_length_le in C2 by (rewrite length_skipn; lia). exact C2.
Qed.

Section Gen.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma fs_scratch_mono : forall f LF iv, fs_scratch H (f :: LF) iv -> fs_scratch H LF iv.
  Proof.
    intros f LF iv [X|(k & ff & fp & (FA & FB & FD) & E)]; [left; exact X|]. right. exists k, ff, fp. split; [| exact E].
    split; [exact FA|]. split; [exact FB|]. intros g IN. apply FD. right. exact IN.
  Qed.

  Lemma rin_ivs_none : forall X a, Forall (fun iv : Z * Z => a < fst iv \/ snd iv <= a) X -> ~ rin_ivs X a.
  Proof.
    induction X as [|iv X IH]; intros a F; cbn; [tauto|]. inversion F as [|? ? F1 F2]; subst.
    intros [K|K]; [lia| exact (IH a F2 K)].
  Qed.

  Lemma lb_remove_keep : forall p LB b, List.NoDup (map blk_id LB) -> In b LB -> blk_id b <> p -> In b (as_lb_remove H p LB).
  Proof.
    intros p LB b ND IN NE. pose proof (ah_lb_remove H HH) as (L1 & L2 & L3).
    induction LB as [|b' LB IH]; [destruct IN|]. cbn [map] in ND. apply NoDup_cons_iff in ND as [ND1 ND2].
    destruct (Z.eq_dec (blk_id b') p) as [E|E].
    - destruct b' as [[p' A'] n']. cbn in E. subst p'. rewrite L1 by exact ND1.
      destruct IN as [<-|IN]; [cbn in NE; congruence | exact IN].
    - rewrite L2 by exact E. destruct IN as [<-|IN]; [left; reflexivity | right; exact (IH ND2 IN)].
  Qed.

  Lemma lb_remove_perm : forall p A n LB, List.NoDup (map blk_id LB) -> In (p, A, n) LB ->
    Permutation LB ((p, A, n) :: as_lb_remove H p LB).
  Proof.
    intros p A n LB ND IN. pose proof (ah_lb_remove H HH) as (L1 & L2 & L3).
    induction LB as [|b LB IH]; [destruct IN|]. cbn [map] in ND. apply NoDup_cons_iff in ND as [ND1 ND2].
    destruct (Z.eq_dec (blk_id b) p) as [E|E].
    - destruct b as [[p' A'] n']. cbn in E. subst p'. rewrite L1 by exact ND1.
      destruct IN as [EQ|IN]; [rewrite EQ; reflexivity|].
      exfalso. apply ND1. apply in_map_iff. exists (p, A, n). split; [reflexivity | exact IN].
    - rewrite L2 by exact E. destruct IN as [EQ|IN]; [subst b; cbn in E; congruence|].
      specialize (IH ND2 IN). eapply perm_trans; [apply perm_skip; exact IH|]. apply perm_swap.
  Qed.

End Gen.
