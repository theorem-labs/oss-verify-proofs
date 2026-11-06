(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import Malloc.
From Stdlib Require Lia. 
From stdpp Require gmap.
Module TplPack.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List.
Import stdpp.gmap.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc.
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition shadow_l : Type := (list (Z * (Z * N)) * list (Z * list (Z * N)) * list (Z * N))%type.
Definition pack_shadow (s : shadow) : shadow_l :=
  (map_to_list (r_cells s), map_to_list (r_hav s), map_to_list (r_havp s)).
Definition fill_shadow (l : shadow_l) : shadow :=
  mkShadow (list_to_map (fst (fst l))) (list_to_map (snd (fst l))) (list_to_map (snd l)).

Definition strip_ctx (c : mctx) : mctx :=
  mkCtx (c_secret c) (c_init_done c) (c_mmap_counter c) (c_free_meta_head c) (c_avail_meta c) (c_avail_meta_count c)
        (c_avail_meta_area_count c) (c_meta_alloc_shift c) (c_meta_area_head c) (c_meta_area_tail c) (c_avail_meta_areas c)
        ∅ ∅ ∅ ∅ (c_seq c) (c_brk c).
Definition ctx_l : Type := (list (Z * aptr) * list (Z * Z) * list (Z * Z) * list (Z * Z))%type.
Definition pack_ctx (c : mctx) : ctx_l :=
  (map_to_list (c_active c), map_to_list (c_usage c), map_to_list (c_unmap_seq c), map_to_list (c_bounces c)).
Definition fill_ctx (sk : mctx) (l : ctx_l) : mctx :=
  mkCtx (c_secret sk) (c_init_done sk) (c_mmap_counter sk) (c_free_meta_head sk) (c_avail_meta sk) (c_avail_meta_count sk)
        (c_avail_meta_area_count sk) (c_meta_alloc_shift sk) (c_meta_area_head sk) (c_meta_area_tail sk) (c_avail_meta_areas sk)
        (list_to_map (fst (fst (fst l)))) (list_to_map (snd (fst (fst l)))) (list_to_map (snd (fst l))) (list_to_map (snd l))
        (c_seq sk) (c_brk sk).

Definition strip_state (st : mstate) : mstate :=
  mkState (strip_ctx (s_ctx st)) ∅ ∅ (s_next_rid st) ∅ ∅ ∅ ∅ (s_tick st) (s_secret st) (s_reserved st).
Definition state_l : Type :=
  (ctx_l * list (N * region) * list (N * shadow_l) * list (aptr * meta) * list (aptr * area) * list (aptr * ghdr)
   * list (aptr * (aptr * Z)))%type.
Definition pack_state (st : mstate) : state_l :=
  (pack_ctx (s_ctx st), map_to_list (s_regions st),
   map (fun p => (fst p, pack_shadow (snd p))) (map_to_list (s_shadow st)),
   map_to_list (s_metas st), map_to_list (s_areas st), map_to_list (s_groups st), map_to_list (s_slots st)).
Definition fill_state (sk : mstate) (l : state_l) : mstate :=
  match l with
  | (cl, regs, shs, metas, areas, groups, slots) =>
      mkState (fill_ctx (s_ctx sk) cl) (list_to_map regs)
              (list_to_map (map (fun p => (fst p, fill_shadow (snd p))) shs))
              (s_next_rid sk) (list_to_map metas) (list_to_map areas) (list_to_map groups) (list_to_map slots)
              (s_tick sk) (s_secret sk) (s_reserved sk)
  end.

(* [comment removed for export] *)
Ltac packed_state X :=
  let p := eval vm_compute in (strip_state X, pack_state X) in
  lazymatch p with (?sk, ?l) => exact (fill_state sk l) end.
Ltac packed_shadow X :=
  let l := eval vm_compute in (pack_shadow X) in exact (fill_shadow l).
End TplPack.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Section ACeilS1. Context {ACEIL__ : ACeil}.


Lemma size_classes_length : length size_classes = 48%nat.
Proof. reflexivity. Qed.

Lemma size_classes_bounds : Forall (fun x => 1 <= x <= 8191) size_classes.
Proof.
  apply Forall_forall. intros x Hx. unfold size_classes in Hx.
  repeat (destruct Hx as [<-|Hx]; [lia|]). destruct Hx.
Qed.

Lemma size_class_bound sc : 0 <= sc < 48 -> 1 <= size_class sc <= 8191.
Proof.
  intros H. unfold size_class.
  apply (Forall_forall (fun x => 1 <= x <= 8191) size_classes); [apply size_classes_bounds|].
  apply nth_In. rewrite size_classes_length. lia.
Qed.

(* [comment removed for export] *)
Lemma mask_upto_nonneg k : 0 <= k -> 0 <= mask_upto k.
Proof. intros. unfold mask_upto. assert (0 < 2 ^ (k + 1)) by (apply Z.pow_pos_nonneg; lia). lia. Qed.

Lemma testbit_mask_upto k i : 0 <= k -> 0 <= i -> Z.testbit (mask_upto k) i = (i <=? k).
Proof.
  intros Hk Hi. unfold mask_upto. replace (2 ^ (k + 1) - 1) with (Z.pred (2 ^ (k + 1))) by lia.
  rewrite <- Z.ones_equiv. destruct (Z.leb_spec i k).
  - apply Z.ones_spec_low. lia.
  - apply Z.ones_spec_high. lia.
Qed.

Lemma testbit_bit i j : 0 <= i -> 0 <= j -> Z.testbit (bit i) j = (i =? j).
Proof.
  intros Hi Hj. unfold bit. destruct (Z.eqb_spec i j) as [<-|NE].
  - apply Z.pow2_bits_true. exact Hi.
  - apply Z.pow2_bits_false. lia.
Qed.

Lemma bits_below_bound n a : 0 <= a -> 0 <= n -> (forall i, 0 <= i -> Z.testbit a i = true -> i < n) -> a < 2 ^ n.
Proof.
  intros Ha Hn Hb. destruct (Z.lt_ge_cases a (2 ^ n)) as [|Hge]; [assumption|]. exfalso.
  assert (Hl : n <= Z.log2 a) by (apply Z.log2_le_pow2; lia).
  assert (Ht : Z.testbit a (Z.log2 a) = true) by (apply Z.bit_log2; lia).
  specialize (Hb (Z.log2 a) ltac:(apply Z.log2_nonneg) Ht). lia.
Qed.

(* [comment removed for export] *)

End ACeilS1.
