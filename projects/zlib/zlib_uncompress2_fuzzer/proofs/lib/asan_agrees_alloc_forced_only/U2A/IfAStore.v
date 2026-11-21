(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Bytes Tac StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AArr ItAKit IfAPure.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Definition f8bytes (f : Z -> Z) (n : nat) : list byte := map (fun i => Z_to_bv 8 (f (Z.of_nat i))) (seq 0 n).
Lemma f8bytes_length : forall f n, length (f8bytes f n) = n.
Proof. intros. unfold f8bytes. rewrite length_map, length_seq. reflexivity. Qed.
Lemma f8bytes_nth : forall f n k, (k < n)%nat -> nth_error (f8bytes f n) k = Some (Z_to_bv 8 (f (Z.of_nat k))).
Proof.
  intros f n k Hk. unfold f8bytes. rewrite nth_error_map, nth_error_seq.
  destruct (Nat.ltb_spec k n) as [_|X]; [| lia]. cbn. reflexivity.
Qed.

Definition f8hole (m : word -> option byte) (A : Z) (n : nat) (f : Z -> Z) (i : Z) : Prop :=
  bhole segs m A (f8bytes f n) (Z.to_nat i) 1.

Lemma f8_open : forall m A n f i,
  f8arr segs m A n f -> 0 <= i < Z.of_nat n ->
  f8hole m A n f i /\ rw_cells segs m (A + i) [C1 (Z_to_bv 8 (f i))].
Proof.
  intros m A n f i [HB HW] Hi. fold (f8bytes f n) in HB, HW.
  destruct (bhole_open segs m A (f8bytes f n) (Z.to_nat i) 1 HB HW) as (H1 & H2 & H3).
  { rewrite f8bytes_length. lia. }
  split; [exact H1|].
  replace (A + i) with (A + Z.of_nat (Z.to_nat i)) by lia.
  split; [split; [cbn; split; exact I|] | exact H3].
  cbn [cells_bytes cbytes]. rewrite app_nil_r.
  assert (E : firstn 1 (skipn (Z.to_nat i) (f8bytes f n)) = [Z_to_bv 8 (f i)]).
  { pose proof (f8bytes_nth f n (Z.to_nat i) ltac:(lia)) as NE. rewrite Z2Nat.id in NE by lia.
    destruct (List.nth_error_split (f8bytes f n) (Z.to_nat i) NE) as (l1 & l2 & E1 & E2). rewrite E1.
    rewrite skipn_app, (skipn_all2 l1) by lia. replace (Z.to_nat i - length l1)%nat with 0%nat by lia. reflexivity. }
  rewrite <- E. exact H2.
Qed.

Lemma f8_close : forall m A n f i (b : byte) x,
  f8hole m A n f i -> 0 <= i < Z.of_nat n -> rw_cells segs m (A + i) [C1 b] -> b = Z_to_bv 8 x ->
  f8arr segs m A n (fupd8 f i x).
Proof.
  intros m A n f i b x HH Hi [[_ HC] _] EB. cbn [cells_bytes cbytes] in HC. rewrite app_nil_r in HC.
  replace (A + i) with (A + Z.of_nat (Z.to_nat i)) in HC by lia.
  destruct (bhole_close segs m A _ _ _ [b] HH HC eq_refl) as [HB HW].
  unfold f8arr, u8arr. fold (f8bytes (fupd8 f i x) n).
  assert (E : f8bytes (fupd8 f i x) n = firstn (Z.to_nat i) (f8bytes f n) ++ [b] ++ skipn (Z.to_nat i + 1) (f8bytes f n)).
  { apply nth_error_ext'.
    - rewrite !length_app, length_firstn, length_skipn, !f8bytes_length. cbn [length]. lia.
    - intros k Hk. rewrite f8bytes_length in Hk. rewrite f8bytes_nth by exact Hk.
      destruct (Nat.lt_ge_cases k (Z.to_nat i)) as [L|G].
      + rewrite nth_error_app1 by (rewrite length_firstn, f8bytes_length; lia).
        rewrite nth_error_firstn. destruct (Nat.ltb_spec k (Z.to_nat i)) as [_|X]; [| lia].
        rewrite f8bytes_nth by lia. unfold fupd8. destruct (Z.eqb_spec (Z.of_nat k) i); [lia| reflexivity].
      + rewrite nth_error_app2 by (rewrite length_firstn, f8bytes_length; lia).
        rewrite length_firstn, f8bytes_length. replace (Nat.min (Z.to_nat i) n) with (Z.to_nat i) by lia.
        destruct (Nat.eq_dec k (Z.to_nat i)) as [->|NE].
        * rewrite Nat.sub_diag. cbn. unfold fupd8. rewrite Z2Nat.id by lia. rewrite Z.eqb_refl. rewrite EB. reflexivity.
        * replace (k - Z.to_nat i)%nat with (S (k - Z.to_nat i - 1)) by lia. cbn [app nth_error].
          rewrite nth_error_skipn. replace (Z.to_nat i + 1 + (k - Z.to_nat i - 1))%nat with k by lia.
          rewrite f8bytes_nth by exact Hk. unfold fupd8. destruct (Z.eqb_spec (Z.of_nat k) i); [lia| reflexivity]. }
  rewrite E. split; [exact HB|].
  rewrite !length_app, length_firstn, length_skipn, !f8bytes_length in *. cbn [length].
  replace (Z.of_nat (Nat.min (Z.to_nat i) n + (1 + (n - (Z.to_nat i + 1))))) with (Z.of_nat n) by lia. exact HW.
Qed.

Lemma f8hole_frame : forall m A n f i a xs N,
  f8hole m A n f i -> N = Z.of_nat n -> 0 <= i -> 0 <= a -> a + Z.of_nat (length xs) <= 2^64 ->
  (A + N <= a \/ a + Z.of_nat (length xs) <= A \/ (A + i <= a /\ a + Z.of_nat (length xs) <= A + i + 1)) ->
  f8hole (write_to_mem m (wa a) xs) A n f i.
Proof.
  intros m A n f i a xs N H -> Hi Ha Hl D. unfold f8hole in *. apply bhole_frame; [exact H| exact Ha| exact Hl|].
  rewrite f8bytes_length. lia.
Qed.
End WithSegs.

Ltac transport_chunks segs m a bs ::=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : f8arr segs m ?A2 ?n2 ?f2 |- _ =>
      first [ apply (f8arr_frame segs m A2 n2 f2 a bs) in H; [ | lia | ita_side | ita_side ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : f8hole segs m ?A2 ?n2 ?f2 ?i2 |- _ =>
      first [ apply (f8hole_frame segs m A2 n2 f2 i2 a bs (Z.of_nat n2)) in H; [ | reflexivity | lia | lia | ita_side | ita_side ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

Ltac f8_open_at ARR idx C EC CH CC :=
  lazymatch type of ARR with
  | f8arr ?segs ?m ?A ?n ?f =>
      destruct (f8_open segs m A n f idx ARR ltac:(lia)) as [CH CC]; clear ARR;
      remember (A + idx) as C eqn:EC
  end.
Ltac f8_close_at CH CC EC x NEW :=
  lazymatch type of CH with
  | f8hole ?segs ?m ?A ?n ?f ?i =>
      rewrite EC in CC;
      lazymatch type of CC with
      | rw_cells _ _ _ [C1 ?b] =>
          assert (NEW : f8arr segs m A n (fupd8 f i x));
          [ apply (f8_close segs m A n f i b x CH); [lia | exact CC | ] | clear CH CC ]
      end
  end.

Ltac solve_load_f8 :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m (Z_to_bv 64 ?a) 1] =>
      match goal with
      | ARR : f8arr segs m ?B ?n ?f |- _ =>
          rewrite (f8arr_read segs m B n f (a - B) (Z_to_bv 64 a) ARR ltac:(lia) ltac:(unfold wa; f_equal; lia))
      end
  end;
  load_post.
Ltac u8_norm R :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 8 (?f ?ix))] => rewrite (u8_val (f ix)) by (apply R; lia)
         end.
