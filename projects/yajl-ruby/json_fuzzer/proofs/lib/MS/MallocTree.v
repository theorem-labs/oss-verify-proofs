(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the auxv as any list of (key, value) pairs, with last_assoc for the last AT_RANDOM). *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import F_syscalls MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl Monad RawAlloc.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Export MallocVocab MallocOracle.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition mmap_val (a : mmap_ans) : Z := match a with MmErr e => neg_errno e | MmOk x => x end.
Definition fixed_val (addr : Z) (a : fixed_ans) : Z :=
  match a with FxKept e => neg_errno e | FxDone => addr | FxLost e => neg_errno e end.
Definition range_val (a : range_ans) : Z := match a with RgErr e => neg_errno e | RgDone _ => 0 end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ptr_rel (p : optr) (r : option bptr) : Prop :=
  match p, r with
  | None, None => True
  | Some pf, Some b => fst pf = fst (fst b) /\ exists off, snd pf = snd (fst b) + UNIT * off
  | _, _ => False
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition AUXV_CELL : Z := LIBC + 8.

(* LPS 08b1429: the auxv as mallocng's [__malloc_init] scan sees it, for ANY layout: a
   list [L] of (key, value) pairs before AT_NULL, flattened into words
   ([flat_pairs L ++ [0; 0]]).  [last_assoc k L] is the value of the LAST pair with key
   [k] (musl's loop has no break, so the last AT_RANDOM wins).  Copied from
   jsoncons/fuzz_json_cursor's CJ/Agent/MallocTree.v. *)
Fixpoint flat_pairs (L : list (Z * Z)) : list Z :=
  match L with [] => [] | (k, v) :: L' => k :: v :: flat_pairs L' end.

Fixpoint last_assoc (k : Z) (L : list (Z * Z)) : option Z :=
  match L with
  | [] => None
  | (k', v) :: L' =>
      match last_assoc k L' with Some r => Some r | None => if Z.eqb k' k then Some v else None end
  end.

Lemma flat_pairs_app : forall A B, flat_pairs (A ++ B) = flat_pairs A ++ flat_pairs B.
Proof. induction A as [|[k v] A IH]; intros B; cbn [flat_pairs app]; [reflexivity| rewrite IH; reflexivity]. Qed.

Lemma length_flat_pairs : forall L, length (flat_pairs L) = (2 * length L)%nat.
Proof. induction L as [|[k v] L IH]; cbn [flat_pairs length]; [reflexivity| rewrite IH; lia]. Qed.

Lemma last_assoc_In : forall k L v, last_assoc k L = Some v -> In (k, v) L.
Proof.
  intros k L. induction L as [|[k' v'] L IH]; intros v H; cbn [last_assoc] in H; [discriminate H|].
  revert H. remember (last_assoc k L) as o eqn:Eo. destruct o as [r|]; intros H.
  - injection H as <-. right. apply IH. reflexivity.
  - revert H. destruct (Z.eqb k' k) eqn:Ek; intros H; [|discriminate H].
    apply Z.eqb_eq in Ek. subst k'. injection H as <-. left. reflexivity.
Qed.

Lemma flat_pairs_nth_key : forall L pre k v post, L = pre ++ (k, v) :: post ->
  nth_error (map wz (flat_pairs L ++ [0; 0])) (Z.to_nat (2 * Z.of_nat (length pre))) = Some (wz k).
Proof.
  intros L pre k v post ->.
  replace (Z.to_nat (2 * Z.of_nat (length pre))) with (length (map wz (flat_pairs pre)))
    by (rewrite length_map, length_flat_pairs; lia).
  rewrite flat_pairs_app, <- app_assoc, map_app, nth_error_app2 by lia.
  rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma flat_pairs_nth_val : forall L pre k v post, L = pre ++ (k, v) :: post ->
  nth_error (map wz (flat_pairs L ++ [0; 0])) (Z.to_nat (2 * Z.of_nat (length pre) + 1)) = Some (wz v).
Proof.
  intros L pre k v post ->.
  replace (Z.to_nat (2 * Z.of_nat (length pre) + 1)) with (length (map wz (flat_pairs pre)) + 1)%nat
    by (rewrite length_map, length_flat_pairs; lia).
  rewrite flat_pairs_app, <- app_assoc, map_app, nth_error_app2 by lia.
  replace (length (map wz (flat_pairs pre)) + 1 - length (map wz (flat_pairs pre)))%nat with 1%nat by lia.
  reflexivity.
Qed.

Lemma flat_pairs_nth_end : forall L,
  nth_error (map wz (flat_pairs L ++ [0; 0])) (Z.to_nat (2 * Z.of_nat (length L))) = Some (wz 0).
Proof.
  intros L.
  replace (Z.to_nat (2 * Z.of_nat (length L))) with (length (map wz (flat_pairs L)))
    by (rewrite length_map, length_flat_pairs; lia).
  rewrite map_app, nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma length_auxv_words : forall L, length (map wz (flat_pairs L ++ [0; 0])) = (2 * length L + 2)%nat.
Proof. intros L. rewrite length_map, length_app, length_flat_pairs. reflexivity. Qed.

Lemma Forall_disjoint_from : forall (P : Z * Z -> Prop) W a n,
  Forall P W -> (forall lo hi, P (lo, hi) -> a + n <= lo \/ hi <= a) -> disjoint_from W a n.
Proof.
  intros P W a n F HP. induction F as [|[lo hi] W Hx F IH]; cbn; [exact I|]. split; [apply (HP _ _ Hx)| exact IH].
Qed.

(* [comment removed for export] *)
Definition alloc_fp (K : rkind -> Prop) (st1 : mstate) (lo sp : Z) (a : Z) : Prop :=
  lo <= a < sp
  \/ errno_addr (Z_to_bv 64 0x1a620) <= a < errno_addr (Z_to_bv 64 0x1a620) + 4
  \/ CTX <= a < CTX + 928
  \/ exists rid r, (s_regions st1) !! rid = Some r /\ K (r_kind r) /\ lr_lo r <= a < r_base r + round_up_pg (r_len r).

(* [comment removed for export] *)
Record am_rel (st st1 : mstate) (mo : optr) : Prop := mkAMR {
  amr_active : forall sc, active st1 sc = active st sc;
  amr_usage : forall sc, usage st1 sc = usage st sc;
  amr_bounces : forall i, bounces st1 i = bounces st i;
  amr_unmap_seq : forall i, unmap_seq st1 i = unmap_seq st i;
  amr_seq : c_seq (ctx st1) = c_seq (ctx st);
  amr_counter : c_mmap_counter (ctx st1) = c_mmap_counter (ctx st);
  amr_groups : s_groups st1 = s_groups st;
  amr_slots : s_slots st1 = s_slots st;
  amr_shadow : s_shadow st1 = s_shadow st;
  amr_tick : s_tick st1 = s_tick st;
  amr_reserved : s_reserved st1 = s_reserved st;
  (* [comment removed for export] *)
  amr_metas : forall g, Some g <> mo ->
      (m_mem (get_meta_rec st g) <> None \/ m_next (get_meta_rec st g) = None) ->
      get_meta_rec st1 g = get_meta_rec st g;
  (* [comment removed for export] *)
  amr_result : forall m, mo = Some m -> get_meta_rec st1 m = meta0 /\ meta_slot st1 m;
  (* [comment removed for export] *)
  amr_regions : forall rid r, (s_regions st) !! rid = Some r ->
      exists r', (s_regions st1) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r
                 /\ r_len r <= r_len r' /\ (r_kind r = RKGroup -> r' = r);
  amr_new : forall rid r', (s_regions st1) !! rid = Some r' -> (s_regions st) !! rid = None -> r_kind r' <> RKGroup;
  amr_next_rid : (s_next_rid st <= s_next_rid st1)%N;
  amr_areas : forall a, is_Some ((s_areas st) !! a) -> is_Some ((s_areas st1) !! a);
  (* [comment removed for export] *)
  amr_ptrs : forall P : N -> Prop,
      (forall rid r, (s_regions st1) !! rid = Some r -> r_kind r <> RKGroup -> P rid) ->
      ptrs_in P st -> ptrs_in P st1;
  (* [comment removed for export] *)
  amr_fresh : forall rid, (s_next_rid st1 <= rid)%N -> (s_regions st1) !! rid = None /\ (s_shadow st1) !! rid = (s_shadow st) !! rid
}.

Definition AM_STACK : Z := 128.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition fresh_addr (st : mstate) (a : Z) : Prop :=
  a < alloc_ceiling /\ ranges_free (live_ranges st) a 1 = true.

Lemma ranges_free_In l a n b k : ranges_free l a n = true -> In (b, k) l -> a + n <= b \/ b + k <= a.
Proof.
  intros H HI. unfold ranges_free in H. apply (proj1 (forallb_forall _ _) H) in HI. cbn [fst snd] in HI.
  unfold iv_disjoint in HI. apply Bool.orb_prop in HI. destruct HI as [X|X]; apply Z.leb_le in X; lia.
Qed.

Lemma ranges_free_intro l a n : (forall b k, In (b, k) l -> a + n <= b \/ b + k <= a) -> ranges_free l a n = true.
Proof.
  intros H. unfold ranges_free. apply (proj2 (forallb_forall _ _)). intros [b k] HI. cbn [fst snd].
  unfold iv_disjoint. destruct (H b k HI) as [X|X]; [rewrite (proj2 (Z.leb_le _ _) X); reflexivity|].
  rewrite (proj2 (Z.leb_le _ _) X). apply Bool.orb_true_r.
Qed.

Lemma ranges_free_sub l a n a' n' : ranges_free l a n = true -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> ranges_free l a' n' = true.
Proof.
  intros H H1 H2 H3. apply ranges_free_intro. intros b k HI. pose proof (ranges_free_In l a n b k H HI). lia.
Qed.

Lemma In_live_ranges st rid r : (s_regions st) !! rid = Some r ->
  In (region_live_range r) (live_ranges st).
Proof.
  intros Hr. unfold live_ranges. apply in_or_app. right. apply in_map_iff. exists (rid, r). split; [reflexivity|].
  apply (proj1 (list_elem_of_In _ _)). apply elem_of_map_to_list. exact Hr.
Qed.

(* [comment removed for export] *)
Lemma fresh_live_region st a rid r : fresh_addr st a -> (s_regions st) !! rid = Some r ->
  a + 1 <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= a.
Proof.
  intros [_ FR] Hr. pose proof (In_live_ranges st rid r Hr) as HI.
  unfold region_live_range in HI. unfold lr_lo. unfold PGSZ in HI.
  destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ FR HI); lia).
Qed.

(* [comment removed for export] *)
Lemma fresh_addr_anti st st' a :
  s_reserved st' = s_reserved st ->
  (forall rid r, (s_regions st) !! rid = Some r ->
     exists r', (s_regions st') !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
  fresh_addr st' a -> fresh_addr st a.
Proof.
  intros RS HR [FC FR]. split; [exact FC|]. apply ranges_free_intro. intros b k HI.
  unfold live_ranges in HI. apply in_app_or in HI. destruct HI as [HI|HI].
  - apply (ranges_free_In (live_ranges st') a 1 b k FR). unfold live_ranges. apply in_or_app. left. rewrite RS. exact HI.
  - apply in_map_iff in HI. destruct HI as ([rid r] & E & HI). cbn [snd] in E.
    apply (proj2 (list_elem_of_In _ _)) in HI. apply elem_of_map_to_list in HI.
    destruct (HR rid r HI) as (r' & Hr' & K' & B' & L').
    pose proof (In_live_ranges st' rid r' Hr') as HI'.
    assert (RU : round_up_pg (r_len r) <= round_up_pg (r_len r')).
    { unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite !Z.land_ones by lia. Z.div_mod_to_equations. lia. }
    unfold region_live_range in HI', E. rewrite K', B' in HI'.
    destruct (r_kind r); inversion E; subst; (pose proof (ranges_free_In _ _ _ _ _ FR HI'); lia).
Qed.
End RC__1.
