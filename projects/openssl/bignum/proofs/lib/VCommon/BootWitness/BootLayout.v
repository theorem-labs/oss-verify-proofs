(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch input ProcInput, the CONFIG_RSEQ flag, the new auxv layout and the init stack window). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import PropExec.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.BootWitness Require Import BootDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma flat_map_app' : forall {A B : Type} (f : A -> list B) l1 l2,
  flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof.
  intros A B f l1 l2. induction l1 as [|x xs IH]; cbn; [reflexivity|].
  rewrite IH, app_assoc. reflexivity.
Qed.

Lemma skipn_nth : forall {A : Type} (l : list A) k d, (k < length l)%nat ->
  skipn k l = nth k l d :: skipn (S k) l.
Proof.
  induction l as [|x xs IH]; intros k d Hk; [cbn in Hk; lia|].
  destruct k as [|k']; [reflexivity|].
  cbn [skipn nth]. apply IH. cbn in Hk; lia.
Qed.

Lemma flat_map_split : forall {A B : Type} (f : A -> list B) l k d, (k < length l)%nat ->
  flat_map f l = flat_map f (firstn k l) ++ f (nth k l d) ++ flat_map f (skipn (S k) l).
Proof.
  intros A B f l k d Hk.
  rewrite <- (firstn_skipn k l) at 1.
  rewrite flat_map_app'.
  rewrite (skipn_nth l k d Hk). reflexivity.
Qed.

Lemma flat_map_le8_decomp : forall (l : list word) k, (k < length l)%nat ->
  flat_map word_le8 l =
  flat_map word_le8 (firstn k l) ++ word_le8 (nth k l (Z_to_bv 64 0))
    ++ flat_map word_le8 (skipn (S k) l).
Proof. intros l k Hk. apply (flat_map_split word_le8 l k (Z_to_bv 64 0) Hk). Qed.

Lemma flatten_strings_decomp : forall strs k, (k < length strs)%nat ->
  flatten_strings strs =
  flatten_strings (firstn k strs) ++ (nth k strs [] ++ [Z_to_bv 8 0])
    ++ flatten_strings (skipn (S k) strs).
Proof.
  intros strs k Hk.
  apply (flat_map_split (fun s => s ++ [Z_to_bv 8 0]) strs k [] Hk).
Qed.

Lemma total_arg_bytes_cons : forall s l,
  total_arg_bytes_nat (s :: l) = (length s + 1 + total_arg_bytes_nat l)%nat.
Proof. reflexivity. Qed.

Lemma total_arg_bytes_firstn_le : forall k l,
  (total_arg_bytes_nat (firstn k l) <= total_arg_bytes_nat l)%nat.
Proof.
  induction k as [|k IH]; intros l.
  - change (total_arg_bytes_nat (firstn 0 l)) with 0%nat. lia.
  - destruct l as [|s rest]; [cbn; lia|].
    cbn [firstn]. rewrite !total_arg_bytes_cons. specialize (IH rest). lia.
Qed.

Lemma length_flatten_firstn_le : forall k l,
  (length (flatten_strings (firstn k l)) <= length (flatten_strings l))%nat.
Proof.
  intros k l. rewrite !length_flatten_strings. apply total_arg_bytes_firstn_le.
Qed.

Lemma firstn_app_exact : forall {A} (l1 l2 : list A) n,
  length l1 = n -> firstn n (l1 ++ l2) = l1.
Proof.
  intros A l1 l2 n H. subst n. rewrite firstn_app, firstn_all, Nat.sub_diag.
  cbn. apply app_nil_r.
Qed.

Lemma skipn_app_exact : forall {A} (l1 l2 : list A) n,
  length l1 = n -> skipn n (l1 ++ l2) = l2.
Proof.
  intros A l1 l2 n H. subst n. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

Lemma skipn_repeat' : forall {A} (x : A) off n,
  skipn off (repeat x n) = repeat x (n - off).
Proof.
  intros A x off. induction off as [|off IH]; intros n.
  - cbn. rewrite Nat.sub_0_r. reflexivity.
  - destruct n as [|n]; [reflexivity|]. cbn [repeat skipn]. rewrite IH. f_equal.
Qed.

Lemma firstn_repeat' : forall {A} (x : A) k n, (k <= n)%nat ->
  firstn k (repeat x n) = repeat x k.
Proof.
  intros A x k. induction k as [|k IH]; intros n H; [reflexivity|].
  destruct n as [|n]; [lia|]. cbn [repeat firstn]. rewrite IH by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u_Z2bv : forall z, (0 <= z)%Z -> (z < 2^64)%Z ->
  bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z Hlo Hhi. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. apply Z.mod_small. split; [exact Hlo|].
  exact Hhi.
Qed.

Lemma word_add_nat : forall (a : word) (n : nat),
  a + nat_to_word n = Z_to_bv 64 (bv_unsigned a + Z.of_nat n).
Proof.
  intros a n. apply bv_eq. unfold nat_to_word.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned, bv_wrap_add_idemp_r.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma word_of_unsigned : forall (a : word) (z : Z),
  bv_unsigned a = z -> a = Z_to_bv 64 z.
Proof.
  intros a z H. apply bv_eq. subst z. rewrite Z_to_bv_unsigned.
  symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
Lemma word_at_offset : forall (sp a : word) (off : nat),
  bv_unsigned a = (bv_unsigned sp + Z.of_nat off)%Z ->
  a = sp + nat_to_word off.
Proof.
  intros sp a off H. rewrite word_add_nat. apply word_of_unsigned. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma le_word_unsigned : forall bs z,
  bytes_le_to_Z bs = z -> (0 <= z < 2^64)%Z ->
  bv_unsigned (le_bytes_to_word bs) = z.
Proof.
  intros bs z H Hz. unfold le_bytes_to_word. rewrite H. apply u_Z2bv; lia.
Qed.

Lemma le_word_of_le8 : forall v : word, le_bytes_to_word (word_le8 v) = v.
Proof.
  intro v. apply le_word_v. apply bytes_le_n_to_le_8.
Qed.

Lemma bv_extract_64_id : forall v : word, bv_extract 0 64 v = v.
Proof.
  intro v. apply bv_eq.
  rewrite bv_extract_unsigned, Z.shiftr_0_r.
  apply bv_wrap_bv_unsigned.
Qed.

Lemma bytes_le_repeat0 : forall n, bytes_le_to_Z (repeat (Z_to_bv 8 0) n) = 0%Z.
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [repeat bytes_le_to_Z]. rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma firstn4_word_le8 : forall v : word,
  firstn 4 (word_le8 v) = Z_to_le_bytes 4 (bv_unsigned v).
Proof. intro v. reflexivity. Qed.

Lemma bytes_le_firstn4_le8 : forall v : word,
  bytes_le_to_Z (firstn 4 (word_le8 v)) = (bv_unsigned v mod 2^32)%Z.
Proof.
  intro v. rewrite firstn4_word_le8, bytes_le_Z_to_le by apply u64_range.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lw_small : forall (w : word),
  (bv_unsigned w < 2^31)%Z ->
  bv_unsigned (sext 64 (bv_extract 0 32 w)) = bv_unsigned w.
Proof.
  intros w Hw. pose proof (u64_range w) as Hr.
  unfold sext. rewrite bv_sign_extend_unsigned.
  unfold bv_signed. rewrite bv_extract_unsigned, Z.shiftr_0_r.
  rewrite (bv_wrap_small 32) by (change (bv_modulus 32) with (2^32)%Z; lia).
  unfold bv_swrap. change (bv_half_modulus 32) with (2^31)%Z.
  rewrite (bv_wrap_small 32) by (change (bv_modulus 32) with (2^32)%Z; lia).
  replace (bv_unsigned w + 2 ^ 31 - 2 ^ 31)%Z with (bv_unsigned w) by lia.
  apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. lia.
Qed.

Lemma lwu_small : forall (w : word),
  (bv_unsigned w < 2^32)%Z ->
  bv_unsigned (zext 64 (bv_extract 0 32 w)) = bv_unsigned w.
Proof.
  intros w Hw. pose proof (u64_range w) as Hr.
  unfold zext. rewrite bv_zero_extend_unsigned by lia.
  rewrite bv_extract_unsigned, Z.shiftr_0_r.
  apply bv_wrap_small. change (bv_modulus 32) with (2^32)%Z. lia.
Qed.

Lemma lbu_val : forall b : byte,
  bv_unsigned (zext 64 (bv_extract 0 8 (le_bytes_to_word [b]))) = bv_unsigned b.
Proof.
  intro b. rewrite le_word_1, b_extract8_id.
  unfold zext. rewrite bv_zero_extend_unsigned by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_firstn : forall segs mem n (a : word) bs k,
  rdn segs mem a n = Some bs -> (k <= n)%nat ->
  rdn segs mem a k = Some (firstn k bs).
Proof.
  intros segs mem n. induction n as [|n IH]; intros a bs k H Hk.
  - assert (k = 0)%nat by lia. subst k. cbn in H |- *.
    injection H as <-. reflexivity.
  - cbn [rdn] in H.
    destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
      as [b|] eqn:Eb; [|discriminate].
    destruct (rdn segs mem (a+1) n) as [rest|] eqn:Er; [|discriminate].
    injection H as <-.
    destruct k as [|k]; [reflexivity|].
    cbn [rdn firstn]. rewrite Eb.
    rewrite (IH (a+1) rest k Er) by lia. reflexivity.
Qed.

Lemma rdn_skipn : forall segs mem n (a : word) bs off k,
  rdn segs mem a n = Some bs -> (off + k <= n)%nat ->
  rdn segs mem (a + nat_to_word off) k = Some (firstn k (skipn off bs)).
Proof.
  intros segs mem n. induction n as [|n IH]; intros a bs off k H Hk.
  - assert (off = 0%nat) by lia. assert (k = 0%nat) by lia. subst.
    rewrite word_add_0. cbn in H |- *. injection H as <-. reflexivity.
  - cbn [rdn] in H.
    destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
      as [b|] eqn:Eb; [|discriminate].
    destruct (rdn segs mem (a+1) n) as [rest|] eqn:Er; [|discriminate].
    injection H as <-.
    destruct off as [|off].
    + rewrite word_add_0. cbn [skipn].
      eapply rdn_firstn; [|exact Hk].
      cbn [rdn]. rewrite Eb, Er. reflexivity.
    + cbn [skipn].
      replace (a + nat_to_word (S off)) with (a + 1 + nat_to_word off)
        by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
      apply (IH (a+1) rest off k Er). lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* The 08b1429 entry block (StackLayout.build_stack_bytes), split into the     *)
(* pieces the start-up reads: the pointer vector at [sp], the auxv, the gap,   *)
(* the AT_RANDOM bytes, the arch_align_stack pad and the top-anchored strings. *)
(* ------------------------------------------------------------------------- *)

Definition auxv_words (la : LaunchAuxv) (ph : PhdrInfo) (entry uid gid hw rnd xfn : word) : list word :=
  flat_map (fun e => [fst e; snd e]) (auxv_entries la ph entry uid gid hw rnd xfn).

Lemma build_auxv_words : forall entries,
  build_auxv entries = flat_map word_le8 (flat_map (fun e => [fst e; snd e]) entries).
Proof.
  induction entries as [|[t v] es IH]; [reflexivity|].
  cbn [build_auxv flat_map fst snd app].
  change (build_auxv es) with
    (flat_map (fun e : bv 64 * bv 64 => word_le8 (fst e) ++ word_le8 (snd e)) es) in IH.
  rewrite IH, <- app_assoc. reflexivity.
Qed.

Lemma auxv_bytes_words : forall la ph entry uid gid hw rnd xfn,
  auxv_bytes la ph entry uid gid hw rnd xfn = flat_map word_le8 (auxv_words la ph entry uid gid hw rnd xfn).
Proof. intros. unfold auxv_bytes, auxv_words. apply build_auxv_words. Qed.

Lemma length_auxv_entries : forall la ph entry uid gid hw rnd xfn,
  length (auxv_entries la ph entry uid gid hw rnd xfn) = auxv_count (la_rseq la).
Proof. intros. unfold auxv_entries, auxv_count. destruct (la_rseq la); reflexivity. Qed.

(** the pointer vector's size: argc, the two NULL-terminated pointer arrays *)
Definition struct_nat (av ev : list (list byte)) : nat := (8 + (length av + 1) * 8 + (length ev + 1) * 8)%nat.

(** the gap that keeps the AT_RANDOM bytes 16-aligned *)
Definition gap_nat (av ev : list (list byte)) : nat := (8 * (block_items av ev mod 2))%nat.

Definition str_base (top : word) (av ev : list (list byte)) (xfn : list byte) : word :=
  string_base_addr top av ev xfn.
Definition env_base (top : word) (av ev : list (list byte)) (xfn : list byte) : word :=
  str_base top av ev xfn + nat_to_word (total_arg_bytes_nat av).

Definition argv_ptrs (top : word) (av ev : list (list byte)) (xfn : list byte) : list word :=
  fst (string_addrs (str_base top av ev xfn) av).
Definition envp_ptrs (top : word) (av ev : list (list byte)) (xfn : list byte) : list word :=
  fst (string_addrs (env_base top av ev xfn) ev).

Definition struct_prefix (top : word) (av ev : list (list byte)) (xfn : list byte) : list byte :=
  word_le8 (len_word av)
  ++ flat_map word_le8 (argv_ptrs top av ev xfn)
  ++ word_le8 (Z_to_bv 64 0)
  ++ flat_map word_le8 (envp_ptrs top av ev xfn)
  ++ word_le8 (Z_to_bv 64 0).

Lemma length_argv_ptrs : forall top av ev xfn, length (argv_ptrs top av ev xfn) = length av.
Proof. intros. unfold argv_ptrs. apply length_string_addrs_fst. Qed.

Lemma length_envp_ptrs : forall top av ev xfn, length (envp_ptrs top av ev xfn) = length ev.
Proof. intros. unfold envp_ptrs. apply length_string_addrs_fst. Qed.

Lemma length_struct_prefix : forall top av ev xfn, length (struct_prefix top av ev xfn) = struct_nat av ev.
Proof.
  intros. unfold struct_prefix, struct_nat.
  rewrite !length_app, !length_flat_map_le8, length_argv_ptrs, length_envp_ptrs, !length_n_to_le_8. lia.
Qed.

Definition strs_bytes (av ev : list (list byte)) (xfn : list byte) : list byte :=
  flatten_strings av ++ flatten_strings ev ++ xfn ++ [Z_to_bv 8 0].

Lemma length_strs_bytes : forall av ev xfn,
  length (strs_bytes av ev xfn) = launch_string_bytes av ev xfn.
Proof.
  intros. unfold strs_bytes, launch_string_bytes. rewrite !length_app. cbn [length]. lia.
Qed.

Lemma bsb_decomp : forall la ph entry (sp top : word) av ev xfn uid gid hw draw,
  build_stack_bytes la ph entry sp top av ev xfn uid gid hw draw =
  struct_prefix top av ev xfn
  ++ auxv_bytes la ph entry uid gid hw (at_random_ptr sp (la_rseq la) av ev) (at_execfn_ptr top xfn)
  ++ repeat (Z_to_bv 8 0) (gap_nat av ev)
  ++ at_random_bytes (ed_random draw)
  ++ repeat (Z_to_bv 8 0) (block_pad_len (la_rseq la) sp top av ev xfn)
  ++ strs_bytes av ev xfn
  ++ repeat (Z_to_bv 8 0) 8.
Proof.
  intros. unfold build_stack_bytes. cbv zeta.
  rewrite (string_addrs_pair av). cbv beta iota.
  rewrite (string_addrs_pair ev). cbv beta iota.
  unfold struct_prefix, argv_ptrs, envp_ptrs, env_base, str_base, gap_nat, strs_bytes.
  rewrite <- !app_assoc. reflexivity.
Qed.

Lemma head_nat : forall rseq av ev,
  block_head_size rseq av ev = (struct_nat av ev + auxv_size rseq + gap_nat av ev + 16)%nat.
Proof. intros. unfold block_head_size, struct_nat, gap_nat, block_items. cbv zeta. lia. Qed.

Lemma length_bsb : forall la ph entry (sp top : word) av ev xfn uid gid hw draw,
  length (build_stack_bytes la ph entry sp top av ev xfn uid gid hw draw)
  = (block_head_size (la_rseq la) av ev + block_pad_len (la_rseq la) sp top av ev xfn
     + launch_string_bytes av ev xfn + 8)%nat.
Proof.
  intros. rewrite bsb_decomp, !length_app, length_struct_prefix, length_auxv_bytes, !repeat_length,
    length_at_random_bytes, length_strs_bytes, head_nat. lia.
Qed.

Lemma at_random_ptr_eq : forall (sp : word) rseq av ev,
  at_random_ptr sp rseq av ev = sp + nat_to_word (struct_nat av ev + auxv_size rseq + gap_nat av ev).
Proof.
  intros. unfold at_random_ptr. f_equal. unfold nat_to_word. f_equal. rewrite head_nat. lia.
Qed.

Lemma nth_string_addrs : forall strs (base : word) k, (k < length strs)%nat ->
  nth k (fst (string_addrs base strs)) (Z_to_bv 64 0)
  = base + nat_to_word (total_arg_bytes_nat (firstn k strs)).
Proof.
  induction strs as [|s rest IH]; intros base k Hk; [cbn in Hk; lia|].
  rewrite string_addrs_fst_structure.
  destruct k as [|k'].
  - cbn [nth firstn]. change (total_arg_bytes_nat []) with 0%nat.
    rewrite word_add_0. reflexivity.
  - cbn [nth]. rewrite (IH (base + len_word s + 1) k' ltac:(cbn in Hk; lia)).
    cbn [firstn]. rewrite total_arg_bytes_cons.
    rewrite len_word_nat, word1_nat, !nat_to_word_add_merge.
    f_equal. f_equal. lia.
Qed.

Lemma argv_ptr_eq : forall top av ev xfn i, (i < length av)%nat ->
  nth i (argv_ptrs top av ev xfn) (Z_to_bv 64 0)
  = str_base top av ev xfn + nat_to_word (total_arg_bytes_nat (firstn i av)).
Proof. intros. unfold argv_ptrs. apply nth_string_addrs. assumption. Qed.

Lemma envp_ptr_eq : forall top av ev xfn k, (k < length ev)%nat ->
  nth k (envp_ptrs top av ev xfn) (Z_to_bv 64 0)
  = str_base top av ev xfn + nat_to_word (total_arg_bytes_nat av + total_arg_bytes_nat (firstn k ev)).
Proof.
  intros. unfold envp_ptrs. rewrite nth_string_addrs by assumption.
  unfold env_base. rewrite nat_to_word_add_merge. reflexivity.
Qed.

Definition argv0 (inp : ProcInput) : list byte := nth 0 (in_argv inp) [].
