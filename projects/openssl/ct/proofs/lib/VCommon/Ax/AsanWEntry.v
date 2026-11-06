(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.BootWitness Require Import BootDefs BootLayout.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rdB (B : list byte) (o k : nat) : list byte := firstn k (skipn o B).

Definition tab (L : list (list byte)) : nat := total_arg_bytes_nat L.
Definition pre (i : nat) (L : list (list byte)) : nat := total_arg_bytes_nat (firstn i L).
Definition SBn (av ev : list (list byte)) : nat := (184 + 8 * length av + 8 * length ev)%nat.
Definition ROn (av ev : list (list byte)) : nat := (SBn av ev + 8 * ((tab av + tab ev + 7) / 8))%nat.

Lemma SBn_struct : forall av ev, SBn av ev = struct_nat av ev.
Proof. intros av ev. unfold SBn, struct_nat, auxv_size. lia. Qed.

Lemma tab_Z : forall L, total_arg_bytes L = Z.of_nat (tab L).
Proof. intros L. apply total_arg_bytes_Z. Qed.

(* [comment removed for export] *)
Lemma ROn_pad : forall av ev, ROn av ev = (struct_nat av ev + length (flatten_strings av)
                                             + length (flatten_strings ev) + pad_nat av ev)%nat.
Proof.
  intros av ev. unfold ROn, pad_nat. rewrite !length_flatten_strings. rewrite <- SBn_struct. unfold SBn, tab.
  set (t := (total_arg_bytes_nat av + total_arg_bytes_nat ev)%nat).
  set (q := (23 + length av + length ev)%nat).
  replace (184 + 8 * length av + 8 * length ev + total_arg_bytes_nat av + total_arg_bytes_nat ev)%nat
    with (8 * q + t)%nat by (unfold q, t; lia).
  pose proof (Nat.div_mod t 8 ltac:(lia)) as Hd. pose proof (Nat.mod_upper_bound t 8 ltac:(lia)) as Hm.
  assert (HL : (Z.of_nat (8 * q + t) mod 8 = Z.of_nat (t mod 8))%Z).
  { symmetry. apply Z.mod_unique with (q := Z.of_nat (q + t / 8)); lia. }
  rewrite HL.
  destruct (Nat.eq_dec (t mod 8) 0) as [E0|E0].
  - rewrite E0. change ((8 - Z.of_nat 0) mod 8)%Z with 0%Z. change (Z.to_nat 0) with 0%nat.
    replace ((t + 7) / 8)%nat with (t / 8)%nat.
    2:{ apply Nat.div_unique with (r := 7%nat); lia. }
    replace ((184 + 8 * length av + 8 * length ev))%nat with (8 * q)%nat by (unfold q; lia). lia.
  - rewrite Z.mod_small by lia.
    replace ((t + 7) / 8)%nat with (S (t / 8))%nat.
    2:{ apply Nat.div_unique with (r := (t mod 8 - 1)%nat); lia. }
    replace ((184 + 8 * length av + 8 * length ev))%nat with (8 * q)%nat by (unfold q; lia).
    assert (Hz : Z.to_nat (8 - Z.of_nat (t mod 8)) = (8 - t mod 8)%nat) by lia.
    rewrite Hz. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdB_app_l : forall (l1 l2 : list byte) o k, (o + k <= length l1)%nat -> rdB (l1 ++ l2) o k = rdB l1 o k.
Proof.
  intros l1 l2 o k H. unfold rdB. rewrite skipn_app. replace (o - length l1)%nat with 0%nat by lia.
  rewrite firstn_app. rewrite length_skipn. replace (k - (length l1 - o))%nat with 0%nat by lia.
  cbn [firstn]. apply app_nil_r.
Qed.

Lemma rdB_app_r : forall (l1 l2 : list byte) o k, (length l1 <= o)%nat -> rdB (l1 ++ l2) o k = rdB l2 (o - length l1) k.
Proof.
  intros l1 l2 o k H. unfold rdB. rewrite skipn_app. rewrite (skipn_all2 l1 H). reflexivity.
Qed.

Lemma rdB_exact : forall (l r : list byte), rdB (l ++ r) 0 (length l) = l.
Proof. intros l r. unfold rdB. cbn [skipn]. apply firstn_app_exact. reflexivity. Qed.

Lemma rdB_exact' : forall (l : list byte), rdB l 0 (length l) = l.
Proof. intros l. unfold rdB. cbn [skipn]. apply firstn_all. Qed.

Lemma rdB_flat_le8 : forall (l : list word) i, (i < length l)%nat ->
  rdB (flat_map word_le8 l) (8 * i) 8 = word_le8 (nth i l (Z_to_bv 64 0)).
Proof.
  intros l i Hi. rewrite (flat_map_le8_decomp l i Hi).
  rewrite rdB_app_r by (rewrite length_flat_map_le8, length_firstn; lia).
  rewrite length_flat_map_le8, length_firstn. replace (8 * i - 8 * Nat.min i (length l))%nat with 0%nat by lia.
  apply (rdB_exact (word_le8 (nth i l (Z_to_bv 64 0)))).
Qed.

Lemma nth_flat_pairs : forall (es : list (word * word)) i, (i < length es)%nat ->
  nth (2 * i) (flat_map (fun e => [fst e; snd e]) es) (Z_to_bv 64 0) = fst (nth i es (Z_to_bv 64 0, Z_to_bv 64 0))
  /\ nth (2 * i + 1) (flat_map (fun e => [fst e; snd e]) es) (Z_to_bv 64 0) = snd (nth i es (Z_to_bv 64 0, Z_to_bv 64 0)).
Proof.
  induction es as [|e es IH]; intros i Hi; [cbn in Hi; lia|].
  destruct i as [|i']; [split; reflexivity|].
  cbn [flat_map nth app]. replace (2 * S i')%nat with (S (S (2 * i')))%nat by lia.
  replace (2 * S i' + 1)%nat with (S (S (2 * i' + 1)))%nat by lia. cbn [nth].
  apply IH. cbn in Hi. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Block.
Variables (ph : PhdrInfo) (sp : word) (av ev : list (list byte)) (uid hw : word) (draw : EntryDraw).

Let B := build_stack_bytes ph sp av ev uid hw draw.

Lemma struct_prefix_split : forall (x : list byte),
  B ++ x = (word_le8 (len_word av)
            ++ flat_map word_le8 (argv_ptrs sp av ev)
            ++ word_le8 (Z_to_bv 64 0)
            ++ flat_map word_le8 (envp_ptrs sp av ev)
            ++ word_le8 (Z_to_bv 64 0)
            ++ auxv_bytes ph (at_random_ptr sp av ev) uid hw)
           ++ flatten_strings av ++ flatten_strings ev
           ++ repeat (Z_to_bv 8 0) (pad_nat av ev) ++ at_random_bytes (ed_random draw) ++ x.
Proof. intros x. unfold B. rewrite bsb_decomp. unfold struct_prefix. rewrite <- !app_assoc. reflexivity. Qed.

(* [comment removed for export] *)
Theorem E0_length : length B = (ROn av ev + 16)%nat.
Proof. unfold B. rewrite length_bsb, ROn_pad. lia. Qed.

(* [comment removed for export] *)
Theorem E1_argc : rdB B 0 8 = word_le8 (Z_to_bv 64 (Z.of_nat (length av))).
Proof.
  unfold B. rewrite bsb_decomp. unfold struct_prefix. rewrite <- !app_assoc.
  apply (rdB_exact (word_le8 (len_word av))).
Qed.

Lemma rd_struct : forall o k, (o + k <= SBn av ev)%nat ->
  rdB B o k = rdB (word_le8 (len_word av) ++ flat_map word_le8 (argv_ptrs sp av ev) ++ word_le8 (Z_to_bv 64 0)
                   ++ flat_map word_le8 (envp_ptrs sp av ev) ++ word_le8 (Z_to_bv 64 0)
                   ++ auxv_bytes ph (at_random_ptr sp av ev) uid hw) o k.
Proof.
  intros o k H. unfold B. rewrite bsb_decomp. rewrite rdB_app_l.
  - unfold struct_prefix. reflexivity.
  - rewrite length_struct_prefix. rewrite <- SBn_struct. exact H.
Qed.

(* [comment removed for export] *)
Theorem E2_argv : forall i, (i < length av)%nat ->
  rdB B (8 + 8 * i) 8 = word_le8 (sp + Z_to_bv 64 (Z.of_nat (SBn av ev + pre i av))).
Proof.
  intros i Hi. rewrite rd_struct by (unfold SBn; lia).
  rewrite rdB_app_r by (rewrite length_n_to_le_8; lia). rewrite length_n_to_le_8.
  replace (8 + 8 * i - 8)%nat with (8 * i)%nat by lia.
  rewrite rdB_app_l by (rewrite length_flat_map_le8, length_argv_ptrs; lia).
  rewrite rdB_flat_le8 by (rewrite length_argv_ptrs; exact Hi).
  rewrite argv_ptr_eq by exact Hi. rewrite SBn_struct. reflexivity.
Qed.

Theorem E2_argv_null : rdB B (8 + 8 * length av) 8 = word_le8 (Z_to_bv 64 0).
Proof.
  rewrite rd_struct by (unfold SBn; lia).
  rewrite rdB_app_r by (rewrite length_n_to_le_8; lia). rewrite length_n_to_le_8.
  rewrite rdB_app_r by (rewrite length_flat_map_le8, length_argv_ptrs; lia).
  rewrite length_flat_map_le8, length_argv_ptrs. replace (8 + 8 * length av - 8 - 8 * length av)%nat with 0%nat by lia.
  apply (rdB_exact (word_le8 (Z_to_bv 64 0))).
Qed.

(* [comment removed for export] *)
Theorem E3_envp : forall j, (j < length ev)%nat ->
  rdB B (16 + 8 * length av + 8 * j) 8 = word_le8 (sp + Z_to_bv 64 (Z.of_nat (SBn av ev + tab av + pre j ev))).
Proof.
  intros j Hj. rewrite rd_struct by (unfold SBn; lia).
  rewrite rdB_app_r by (rewrite length_n_to_le_8; lia). rewrite length_n_to_le_8.
  rewrite rdB_app_r by (rewrite length_flat_map_le8, length_argv_ptrs; lia).
  rewrite length_flat_map_le8, length_argv_ptrs.
  rewrite rdB_app_r by (rewrite length_n_to_le_8; lia). rewrite length_n_to_le_8.
  replace (16 + 8 * length av + 8 * j - 8 - 8 * length av - 8)%nat with (8 * j)%nat by lia.
  rewrite rdB_app_l by (rewrite length_flat_map_le8, length_envp_ptrs; lia).
  rewrite rdB_flat_le8 by (rewrite length_envp_ptrs; exact Hj).
  rewrite envp_ptr_eq by exact Hj. rewrite SBn_struct. reflexivity.
Qed.

Theorem E3_envp_null : rdB B (16 + 8 * length av + 8 * length ev) 8 = word_le8 (Z_to_bv 64 0).
Proof.
  rewrite rd_struct by (unfold SBn; lia).
  rewrite rdB_app_r by (rewrite length_n_to_le_8; lia). rewrite length_n_to_le_8.
  rewrite rdB_app_r by (rewrite length_flat_map_le8, length_argv_ptrs; lia).
  rewrite length_flat_map_le8, length_argv_ptrs.
  rewrite rdB_app_r by (rewrite length_n_to_le_8; lia). rewrite length_n_to_le_8.
  rewrite rdB_app_r by (rewrite length_flat_map_le8, length_envp_ptrs; lia).
  rewrite length_flat_map_le8, length_envp_ptrs.
  replace (16 + 8 * length av + 8 * length ev - 8 - 8 * length av - 8 - 8 * length ev)%nat with 0%nat by lia.
  apply (rdB_exact (word_le8 (Z_to_bv 64 0))).
Qed.

Lemma at_random_ptr_RO : at_random_ptr sp av ev = sp + Z_to_bv 64 (Z.of_nat (ROn av ev)).
Proof. rewrite at_random_ptr_eq, ROn_pad. reflexivity. Qed.

(* [comment removed for export] *)
Theorem E4_auxv : forall i, (i < 10)%nat ->
  rdB B (24 + 8 * length av + 8 * length ev + 16 * i) 8
    = word_le8 (fst (nth i (auxv_entries ph (sp + Z_to_bv 64 (Z.of_nat (ROn av ev))) uid hw) (Z_to_bv 64 0, Z_to_bv 64 0)))
  /\ rdB B (32 + 8 * length av + 8 * length ev + 16 * i) 8
    = word_le8 (snd (nth i (auxv_entries ph (sp + Z_to_bv 64 (Z.of_nat (ROn av ev))) uid hw) (Z_to_bv 64 0, Z_to_bv 64 0))).
Proof.
  intros i Hi.
  assert (Hskip : forall o, (24 + 8 * length av + 8 * length ev <= o)%nat -> (o + 8 <= SBn av ev)%nat ->
            rdB B o 8 = rdB (auxv_bytes ph (at_random_ptr sp av ev) uid hw) (o - (24 + 8 * length av + 8 * length ev)) 8).
  { intros o Ho1 Ho2. rewrite rd_struct by exact Ho2.
    rewrite rdB_app_r by (rewrite length_n_to_le_8; lia). rewrite length_n_to_le_8.
    rewrite rdB_app_r by (rewrite length_flat_map_le8, length_argv_ptrs; lia).
    rewrite length_flat_map_le8, length_argv_ptrs.
    rewrite rdB_app_r by (rewrite length_n_to_le_8; lia). rewrite length_n_to_le_8.
    rewrite rdB_app_r by (rewrite length_flat_map_le8, length_envp_ptrs; lia).
    rewrite length_flat_map_le8, length_envp_ptrs.
    rewrite rdB_app_r by (rewrite length_n_to_le_8; lia). rewrite length_n_to_le_8.
    f_equal. lia. }
  rewrite !Hskip by (unfold SBn; lia).
  rewrite auxv_bytes_words. rewrite at_random_ptr_RO.
  pose proof (nth_flat_pairs (auxv_entries ph (sp + Z_to_bv 64 (Z.of_nat (ROn av ev))) uid hw) i ltac:(cbn; lia)) as [N1 N2].
  split.
  - replace (24 + 8 * length av + 8 * length ev + 16 * i - (24 + 8 * length av + 8 * length ev))%nat with (8 * (2 * i))%nat by lia.
    unfold auxv_words. rewrite rdB_flat_le8 by (cbn; lia). rewrite N1. reflexivity.
  - replace (32 + 8 * length av + 8 * length ev + 16 * i - (24 + 8 * length av + 8 * length ev))%nat with (8 * (2 * i + 1))%nat by lia.
    unfold auxv_words. rewrite rdB_flat_le8 by (cbn; lia). rewrite N2. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma nth_strings : forall x, nth (SBn av ev + x) B (Z_to_bv 8 0)
  = nth x (flatten_strings av ++ flatten_strings ev ++ repeat (Z_to_bv 8 0) (pad_nat av ev)
           ++ at_random_bytes (ed_random draw)) (Z_to_bv 8 0).
Proof.
  intros x. unfold B. rewrite bsb_decomp.
  rewrite app_nth2 by (rewrite length_struct_prefix, <- SBn_struct; lia).
  rewrite length_struct_prefix, <- SBn_struct. f_equal. lia.
Qed.

Lemma nth_string_k : forall (L : list (list byte)) (rest : list byte) k j, (k < length L)%nat ->
  (j <= length (nth k L []))%nat ->
  nth (pre k L + j) (flatten_strings L ++ rest) (Z_to_bv 8 0) = nth j (nth k L [] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0).
Proof.
  intros L rest k j Hk Hj. rewrite (flatten_strings_decomp L k Hk). rewrite <- !app_assoc.
  rewrite app_nth2 by (rewrite length_flatten_strings; unfold pre; lia).
  rewrite length_flatten_strings. replace (pre k L + j - total_arg_bytes_nat (firstn k L))%nat with j by (unfold pre; lia).
  rewrite app_assoc. rewrite app_nth1 by (rewrite length_app; cbn [length]; lia). reflexivity.
Qed.

Theorem E5_argv_str : forall k j, (k < length av)%nat -> (j <= length (nth k av []))%nat ->
  nth (SBn av ev + pre k av + j) B (Z_to_bv 8 0) = nth j (nth k av [] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0).
Proof.
  intros k j Hk Hj. rewrite <- Nat.add_assoc, nth_strings. apply nth_string_k; assumption.
Qed.

Theorem E5_envp_str : forall k j, (k < length ev)%nat -> (j <= length (nth k ev []))%nat ->
  nth (SBn av ev + tab av + pre k ev + j) B (Z_to_bv 8 0) = nth j (nth k ev [] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0).
Proof.
  intros k j Hk Hj. rewrite <- !Nat.add_assoc, nth_strings.
  rewrite app_nth2 by (rewrite length_flatten_strings; unfold tab; lia).
  rewrite length_flatten_strings. replace (tab av + (pre k ev + j) - total_arg_bytes_nat av)%nat with (pre k ev + j)%nat
    by (unfold tab; lia).
  apply nth_string_k; assumption.
Qed.

(* [comment removed for export] *)
Theorem E6_random : rdB B (ROn av ev) 16 = at_random_bytes (ed_random draw).
Proof.
  unfold B. rewrite bsb_decomp. rewrite !app_assoc.
  rewrite rdB_app_r.
  - rewrite !length_app, length_struct_prefix, !length_flatten_strings, repeat_length.
    rewrite ROn_pad, !length_flatten_strings.
    replace (struct_nat av ev + total_arg_bytes_nat av + total_arg_bytes_nat ev + pad_nat av ev
             - (struct_nat av ev + total_arg_bytes_nat av + total_arg_bytes_nat ev + pad_nat av ev))%nat with 0%nat by lia.
    apply (rdB_exact' (at_random_bytes (ed_random draw))).
  - rewrite !length_app, length_struct_prefix, !length_flatten_strings, repeat_length.
    rewrite ROn_pad, !length_flatten_strings. lia.
Qed.

End Block.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Init.
Variables (segs : list Segment) (pc : N) (ph : PhdrInfo) (sp : word) (draw : EntryDraw).
Variables (av ev : list (list byte)) (uid hw : word).

Let B := build_stack_bytes ph sp av ev uid hw draw.
Let ms := init_machine_state segs pc ph sp draw av ev uid hw.

Hypothesis Hsp : (bv_unsigned sp + Z.of_nat (ROn av ev) + 16 < 2 ^ 64)%Z.

(* [comment removed for export] *)
Theorem E7_block : forall z, (bv_unsigned sp <= z < bv_unsigned sp + Z.of_nat (ROn av ev) + 16)%Z ->
  ms_mem ms (Z_to_bv 64 z) = Some (nth (Z.to_nat (z - bv_unsigned sp)) B (Z_to_bv 8 0)).
Proof.
  intros z Hz. pose proof (E0_length ph sp av ev uid hw draw) as HL. fold B in HL.
  unfold ms, init_machine_state. cbn [ms_mem]. cbv zeta.
  assert (Hu : bv_unsigned (Z_to_bv 64 z) = z).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64)%Z. pose proof (u64_range sp). lia. }
  rewrite stack_to_mem_image_in_block.
  2:{ unfold entry_block_top. rewrite Hu. fold B. rewrite HL. lia. }
  unfold stack_to_mem. rewrite Hu. fold B.
  rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite HL.
  rewrite (proj2 (Z.ltb_lt _ _)) by lia.
  rewrite (nth_error_nth' B (Z_to_bv 8 0)) by (rewrite HL; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Theorem E7_window : (stack_max_size <= bv_unsigned sp)%Z ->
  forall z, (bv_unsigned sp - stack_max_size <= z < bv_unsigned sp)%Z -> ms_mem ms (Z_to_bv 64 z) = Some (Z_to_bv 8 0).
Proof.
  intros Hsm z Hz. unfold ms, init_machine_state. cbn [ms_mem]. cbv zeta.
  assert (Hu : bv_unsigned (Z_to_bv 64 z) = z).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64)%Z. pose proof (u64_range sp).
    unfold stack_max_size in *. lia. }
  unfold stack_to_mem. rewrite Hu. rewrite (proj2 (Z.leb_gt _ _)) by lia.
  rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem E7_domain : forall a : word, ms_mem ms a <> None ->
  (bv_unsigned sp - stack_max_size <= bv_unsigned a < entry_page_top sp B)%Z.
Proof.
  intros a Ha. unfold ms, init_machine_state in Ha. cbn [ms_mem] in Ha. cbv zeta in Ha.
  pose proof (entry_stack_image_top ph sp av ev uid hw draw) as Htop. fold B in Htop.
  unfold stack_to_mem in Ha.
  destruct (Z.leb_spec (bv_unsigned sp) (bv_unsigned a)) as [H1|H1].
  - destruct (Z.ltb_spec (bv_unsigned a - bv_unsigned sp) (Z.of_nat (length (entry_stack_image ph sp av ev uid hw draw)))) as [H2|H2].
    + split; [unfold stack_max_size; lia | lia].
    + destruct (Z.leb (bv_unsigned sp - stack_max_size) (bv_unsigned a) && Z.ltb (bv_unsigned a) (bv_unsigned sp))%bool eqn:E;
        [|exfalso; apply Ha; reflexivity].
      apply andb_prop in E as [_ E]. apply Z.ltb_lt in E. lia.
  - destruct (Z.leb (bv_unsigned sp - stack_max_size) (bv_unsigned a) && Z.ltb (bv_unsigned a) (bv_unsigned sp))%bool eqn:E;
      [|exfalso; apply Ha; reflexivity].
    apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. pose proof (entry_page_top_ge sp B).
    unfold entry_block_top in *. lia.
Qed.

End Init.
