(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch input ProcInput, the new auxv layout and the init stack window). *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import PropExec.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.BootWitness Require Import BootDefs BootLayout.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition rdB (B : list byte) (o k : nat) : list byte := firstn k (skipn o B).

Definition tab (L : list (list byte)) : nat := total_arg_bytes_nat L.
Lemma tab_app : forall a b, total_arg_bytes_nat (a ++ b) = (total_arg_bytes_nat a + total_arg_bytes_nat b)%nat.
Proof. induction a as [|x a IH]; intros b; [reflexivity|]. cbn [app]. rewrite !total_arg_bytes_cons, IH. lia. Qed.
Definition pre (i : nat) (L : list (list byte)) : nat := total_arg_bytes_nat (firstn i L).
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

Lemma length_flat_pairs : forall (es : list (word * word)), length (flat_map (fun e => [fst e; snd e]) es) = (2 * length es)%nat.
Proof. induction es as [|e es IH]; [reflexivity|]. cbn [flat_map length app]. rewrite IH. lia. Qed.

Section Block.
Local Set Default Proof Using "All".
Variables (la : LaunchAuxv) (ph : PhdrInfo) (entry sp top : word) (av ev : list (list byte)) (xfn : list byte).
Variables (uid gid hw : word) (draw : EntryDraw).

Let B := build_stack_bytes la ph entry sp top av ev xfn uid gid hw draw.
Let HS := block_head_size (la_rseq la) av ev.
Let PAD := block_pad_len (la_rseq la) sp top av ev xfn.

Theorem E0_length : length B = (HS + PAD + launch_string_bytes av ev xfn + 8)%nat.
Proof. unfold B, HS, PAD. apply length_bsb. Qed.

Lemma B_split : B = struct_prefix top av ev xfn
  ++ (auxv_bytes la ph entry uid gid hw (at_random_ptr sp (la_rseq la) av ev) (at_execfn_ptr top xfn)
  ++ repeat (Z_to_bv 8 0) (gap_nat av ev) ++ at_random_bytes (ed_random draw))
  ++ repeat (Z_to_bv 8 0) PAD ++ strs_bytes av ev xfn ++ repeat (Z_to_bv 8 0) 8.
Proof. unfold B, PAD. rewrite bsb_decomp. rewrite <- !app_assoc. reflexivity. Qed.

Lemma length_mid : length (auxv_bytes la ph entry uid gid hw (at_random_ptr sp (la_rseq la) av ev) (at_execfn_ptr top xfn)
  ++ repeat (Z_to_bv 8 0) (gap_nat av ev) ++ at_random_bytes (ed_random draw)) = (auxv_size (la_rseq la) + gap_nat av ev + 16)%nat.
Proof. rewrite !length_app, length_auxv_bytes, repeat_length, length_at_random_bytes. lia. Qed.

Lemma HS_eq : HS = (struct_nat av ev + auxv_size (la_rseq la) + gap_nat av ev + 16)%nat.
Proof. unfold HS. apply head_nat. Qed.

Theorem E1_argc : rdB B 0 8 = word_le8 (Z_to_bv 64 (Z.of_nat (length av))).
Proof.
  rewrite B_split. unfold struct_prefix. rewrite <- !app_assoc.
  apply (rdB_exact (word_le8 (len_word av))).
Qed.

Lemma rd_struct : forall o k, (o + k <= struct_nat av ev)%nat -> rdB B o k = rdB (struct_prefix top av ev xfn) o k.
Proof. intros o k H. rewrite B_split. apply rdB_app_l. rewrite length_struct_prefix. exact H. Qed.

Theorem E2_argv : forall i, (i < length av)%nat ->
  rdB B (8 + 8 * i) 8 = word_le8 (str_base top av ev xfn + nat_to_word (pre i av)).
Proof.
  intros i Hi. rewrite rd_struct by (unfold struct_nat; lia). unfold struct_prefix.
  rewrite rdB_app_r by (rewrite length_n_to_le_8; lia). rewrite length_n_to_le_8.
  replace (8 + 8 * i - 8)%nat with (8 * i)%nat by lia.
  rewrite rdB_app_l by (rewrite length_flat_map_le8, length_argv_ptrs; lia).
  rewrite rdB_flat_le8 by (rewrite length_argv_ptrs; exact Hi).
  rewrite argv_ptr_eq by exact Hi. reflexivity.
Qed.

Theorem E2_argv_null : rdB B (8 + 8 * length av) 8 = word_le8 (Z_to_bv 64 0).
Proof.
  rewrite rd_struct by (unfold struct_nat; lia). unfold struct_prefix.
  rewrite rdB_app_r by (rewrite length_n_to_le_8; lia). rewrite length_n_to_le_8.
  rewrite rdB_app_r by (rewrite length_flat_map_le8, length_argv_ptrs; lia).
  rewrite length_flat_map_le8, length_argv_ptrs. replace (8 + 8 * length av - 8 - 8 * length av)%nat with 0%nat by lia.
  apply (rdB_exact (word_le8 (Z_to_bv 64 0))).
Qed.

Theorem E3_envp : forall j, (j < length ev)%nat ->
  rdB B (16 + 8 * length av + 8 * j) 8 = word_le8 (str_base top av ev xfn + nat_to_word (tab av + pre j ev)).
Proof.
  intros j Hj. rewrite rd_struct by (unfold struct_nat; lia). unfold struct_prefix.
  rewrite rdB_app_r by (rewrite length_n_to_le_8; lia). rewrite length_n_to_le_8.
  rewrite rdB_app_r by (rewrite length_flat_map_le8, length_argv_ptrs; lia).
  rewrite length_flat_map_le8, length_argv_ptrs.
  rewrite rdB_app_r by (rewrite length_n_to_le_8; lia). rewrite length_n_to_le_8.
  replace (16 + 8 * length av + 8 * j - 8 - 8 * length av - 8)%nat with (8 * j)%nat by lia.
  rewrite rdB_app_l by (rewrite length_flat_map_le8, length_envp_ptrs; lia).
  rewrite rdB_flat_le8 by (rewrite length_envp_ptrs; exact Hj).
  rewrite envp_ptr_eq by exact Hj. reflexivity.
Qed.

Theorem E3_envp_null : rdB B (16 + 8 * length av + 8 * length ev) 8 = word_le8 (Z_to_bv 64 0).
Proof.
  rewrite rd_struct by (unfold struct_nat; lia). unfold struct_prefix.
  rewrite rdB_app_r by (rewrite length_n_to_le_8; lia). rewrite length_n_to_le_8.
  rewrite rdB_app_r by (rewrite length_flat_map_le8, length_argv_ptrs; lia).
  rewrite length_flat_map_le8, length_argv_ptrs.
  rewrite rdB_app_r by (rewrite length_n_to_le_8; lia). rewrite length_n_to_le_8.
  rewrite rdB_app_r by (rewrite length_flat_map_le8, length_envp_ptrs; lia).
  rewrite length_flat_map_le8, length_envp_ptrs.
  replace (16 + 8 * length av + 8 * length ev - 8 - 8 * length av - 8 - 8 * length ev)%nat with 0%nat by lia.
  apply (rdB_exact (word_le8 (Z_to_bv 64 0))).
Qed.

Lemma rd_mid : forall o k, (struct_nat av ev <= o)%nat -> (o + k <= HS)%nat ->
  rdB B o k = rdB (auxv_bytes la ph entry uid gid hw (at_random_ptr sp (la_rseq la) av ev) (at_execfn_ptr top xfn)
                   ++ repeat (Z_to_bv 8 0) (gap_nat av ev) ++ at_random_bytes (ed_random draw)) (o - struct_nat av ev) k.
Proof.
  intros o k H1 H2. rewrite B_split. rewrite rdB_app_r by (rewrite length_struct_prefix; lia).
  rewrite length_struct_prefix. apply rdB_app_l. rewrite length_mid. rewrite HS_eq in H2. lia.
Qed.

Definition aux_ent (i : nat) : word * word :=
  nth i (auxv_entries la ph entry uid gid hw (at_random_ptr sp (la_rseq la) av ev) (at_execfn_ptr top xfn)) (Z_to_bv 64 0, Z_to_bv 64 0).

Theorem E4_auxv : forall i, (i < auxv_count (la_rseq la))%nat ->
  rdB B (struct_nat av ev + 16 * i) 8 = word_le8 (fst (aux_ent i))
  /\ rdB B (struct_nat av ev + 16 * i + 8) 8 = word_le8 (snd (aux_ent i)).
Proof.
  intros i Hi.
  assert (Hc : (auxv_size (la_rseq la) = 16 * auxv_count (la_rseq la))%nat) by reflexivity.
  rewrite !rd_mid by (pose proof HS_eq; unfold auxv_size in *; lia).
  replace (struct_nat av ev + 16 * i - struct_nat av ev)%nat with (8 * (2 * i))%nat by lia.
  replace (struct_nat av ev + 16 * i + 8 - struct_nat av ev)%nat with (8 * (2 * i + 1))%nat by lia.
  assert (Hl16 : (8 * (2 * i + 1) + 8 <= auxv_size (la_rseq la))%nat) by (unfold auxv_size; lia).
  rewrite !rdB_app_l by (rewrite length_auxv_bytes; lia).
  rewrite auxv_bytes_words.
  pose proof (nth_flat_pairs (auxv_entries la ph entry uid gid hw (at_random_ptr sp (la_rseq la) av ev) (at_execfn_ptr top xfn)) i
                ltac:(rewrite length_auxv_entries; exact Hi)) as [N1 N2].
  split.
  - unfold auxv_words. rewrite rdB_flat_le8 by (rewrite length_flat_pairs, length_auxv_entries; lia). rewrite N1. reflexivity.
  - unfold auxv_words. rewrite rdB_flat_le8 by (rewrite length_flat_pairs, length_auxv_entries; lia). rewrite N2. reflexivity.
Qed.

Theorem E4_gap : forall j, (j < gap_nat av ev)%nat ->
  nth (struct_nat av ev + auxv_size (la_rseq la) + j) B (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof.
  intros j Hj. rewrite B_split.
  rewrite app_nth2 by (rewrite length_struct_prefix; lia). rewrite length_struct_prefix.
  rewrite app_nth1 by (rewrite length_mid; lia).
  rewrite app_nth2 by (rewrite length_auxv_bytes; lia). rewrite length_auxv_bytes.
  rewrite app_nth1 by (rewrite repeat_length; lia). apply nth_repeat.
Qed.

Theorem E6_random : rdB B (struct_nat av ev + auxv_size (la_rseq la) + gap_nat av ev) 16 = at_random_bytes (ed_random draw).
Proof.
  rewrite rd_mid by (pose proof HS_eq; unfold auxv_size in *; lia).
  rewrite rdB_app_r by (rewrite length_auxv_bytes; lia). rewrite length_auxv_bytes.
  rewrite rdB_app_r by (rewrite repeat_length; lia). rewrite repeat_length.
  replace (struct_nat av ev + auxv_size (la_rseq la) + gap_nat av ev - struct_nat av ev - auxv_size (la_rseq la) - gap_nat av ev)%nat with 0%nat by lia.
  apply (rdB_exact' (at_random_bytes (ed_random draw))).
Qed.

Lemma nth_above_head : forall x, nth (HS + x) B (Z_to_bv 8 0)
  = nth x (repeat (Z_to_bv 8 0) PAD ++ strs_bytes av ev xfn ++ repeat (Z_to_bv 8 0) 8) (Z_to_bv 8 0).
Proof.
  intros x. rewrite B_split. rewrite app_assoc.
  rewrite app_nth2 by (rewrite length_app, length_struct_prefix, length_mid, HS_eq; lia).
  rewrite length_app, length_struct_prefix, length_mid, HS_eq. f_equal. lia.
Qed.

Theorem E_pad : forall j, (j < PAD)%nat -> nth (HS + j) B (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof.
  intros j Hj. rewrite nth_above_head. rewrite app_nth1 by (rewrite repeat_length; exact Hj).
  apply nth_repeat.
Qed.

Lemma nth_strs : forall x, (x < launch_string_bytes av ev xfn)%nat ->
  nth (HS + PAD + x) B (Z_to_bv 8 0) = nth x (strs_bytes av ev xfn) (Z_to_bv 8 0).
Proof.
  intros x Hx. rewrite <- (Nat.add_assoc HS), nth_above_head.
  rewrite app_nth2 by (rewrite repeat_length; lia). rewrite repeat_length.
  replace (PAD + x - PAD)%nat with x by lia.
  rewrite app_nth1 by (rewrite length_strs_bytes; exact Hx). reflexivity.
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

Lemma pre_le_tab : forall (L : list (list byte)) k j, (k < length L)%nat -> (j <= length (nth k L []))%nat ->
  (pre k L + j < tab L)%nat.
Proof.
  intros L k j Hk Hj. unfold tab, pre.
  rewrite <- (firstn_skipn k L) at 2. rewrite tab_app.
  rewrite (skipn_nth L k [] Hk), total_arg_bytes_cons.
  pose proof (Nat.le_0_l (total_arg_bytes_nat (skipn (S k) L))). lia.
Qed.

Theorem E5_argv_str : forall k j, (k < length av)%nat -> (j <= length (nth k av []))%nat ->
  nth (HS + PAD + pre k av + j) B (Z_to_bv 8 0) = nth j (nth k av [] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0).
Proof.
  intros k j Hk Hj. pose proof (pre_le_tab av k j Hk Hj).
  rewrite <- (Nat.add_assoc (HS + PAD)), nth_strs.
  - unfold strs_bytes. apply nth_string_k; assumption.
  - unfold launch_string_bytes, tab in *. rewrite length_flatten_strings. lia.
Qed.

Theorem E5_execfn : forall j, (j <= length xfn)%nat ->
  nth (HS + PAD + tab av + tab ev + j) B (Z_to_bv 8 0) = nth j (xfn ++ [Z_to_bv 8 0]) (Z_to_bv 8 0).
Proof.
  intros j Hj. unfold tab.
  replace (HS + PAD + total_arg_bytes_nat av + total_arg_bytes_nat ev + j)%nat
    with (HS + PAD + (total_arg_bytes_nat av + total_arg_bytes_nat ev + j))%nat by lia.
  rewrite nth_strs.
  - unfold strs_bytes. rewrite app_nth2 by (rewrite length_flatten_strings; lia).
    rewrite length_flatten_strings.
    rewrite app_nth2 by (rewrite length_flatten_strings; lia).
    rewrite length_flatten_strings. f_equal. lia.
  - unfold launch_string_bytes. rewrite !length_flatten_strings. lia.
Qed.

Theorem E_top8 : forall j, (j < 8)%nat ->
  nth (HS + PAD + launch_string_bytes av ev xfn + j) B (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof.
  intros j Hj.
  replace (HS + PAD + launch_string_bytes av ev xfn + j)%nat with (HS + (PAD + launch_string_bytes av ev xfn + j))%nat by lia.
  rewrite nth_above_head.
  rewrite app_nth2 by (rewrite repeat_length; lia). rewrite repeat_length.
  rewrite app_nth2 by (rewrite length_strs_bytes; lia). rewrite length_strs_bytes.
  replace (PAD + launch_string_bytes av ev xfn + j - PAD - launch_string_bytes av ev xfn)%nat with j by lia.
  apply nth_repeat.
Qed.

End Block.

Section Init.
Local Set Default Proof Using "All".
Variables (segs : list Segment) (pc : N) (ph : PhdrInfo) (sp mbase : word) (draw : EntryDraw) (inp : ProcInput).

Let B := entry_stack_image inp mbase ph (Z_to_bv 64 (Z.of_N pc)) sp draw.
Let ms := init_machine_state segs pc ph sp mbase draw inp.
Let WLO := stack_window_lo (in_kernel inp) mbase draw.

Hypothesis Hsp : (bv_unsigned sp + Z.of_nat (length B) < 2 ^ 64)%Z.

Theorem E7_block : forall z, (bv_unsigned sp <= z < bv_unsigned sp + Z.of_nat (length B))%Z ->
  ms_mem ms (Z_to_bv 64 z) = Some (nth (Z.to_nat (z - bv_unsigned sp)) B (Z_to_bv 8 0)).
Proof.
  intros z Hz. unfold ms, init_machine_state. cbn [ms_mem]. cbv zeta. fold B.
  assert (Hu : bv_unsigned (Z_to_bv 64 z) = z).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64)%Z. pose proof (u64_range sp). lia. }
  unfold stack_to_mem. rewrite Hu.
  rewrite (proj2 (Z.leb_le _ _)) by lia.
  rewrite (proj2 (Z.ltb_lt _ _)) by lia.
  rewrite (nth_error_nth' B (Z_to_bv 8 0)) by lia. reflexivity.
Qed.

Theorem E7_window : forall z, (WLO <= z < bv_unsigned sp)%Z -> (0 <= z)%Z ->
  ms_mem ms (Z_to_bv 64 z) = Some (Z_to_bv 8 0).
Proof.
  intros z Hz Hz0. unfold ms, init_machine_state. cbn [ms_mem]. cbv zeta. fold B. fold WLO.
  assert (Hu : bv_unsigned (Z_to_bv 64 z) = z).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64)%Z. pose proof (u64_range sp). lia. }
  unfold stack_to_mem. rewrite Hu. rewrite (proj2 (Z.leb_gt _ _)) by lia.
  rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Theorem E7_domain : forall a : word, ms_mem ms a <> None ->
  (WLO <= bv_unsigned a < bv_unsigned sp \/ bv_unsigned sp <= bv_unsigned a < bv_unsigned sp + Z.of_nat (length B))%Z.
Proof.
  intros a Ha. unfold ms, init_machine_state in Ha. cbn [ms_mem] in Ha. cbv zeta in Ha. fold B in Ha. fold WLO in Ha.
  unfold stack_to_mem in Ha.
  destruct (Z.leb_spec (bv_unsigned sp) (bv_unsigned a)) as [H1|H1].
  - destruct (Z.ltb_spec (bv_unsigned a - bv_unsigned sp) (Z.of_nat (length B))) as [H2|H2].
    + right. lia.
    + destruct (Z.leb WLO (bv_unsigned a) && Z.ltb (bv_unsigned a) (bv_unsigned sp))%bool eqn:E;
        [|exfalso; apply Ha; reflexivity].
      apply andb_prop in E as [_ E]. apply Z.ltb_lt in E. lia.
  - destruct (Z.leb WLO (bv_unsigned a) && Z.ltb (bv_unsigned a) (bv_unsigned sp))%bool eqn:E;
      [|exfalso; apply Ha; reflexivity].
    apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. left. lia.
Qed.

End Init.
