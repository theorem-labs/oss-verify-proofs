(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import PropExec.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.BootWitness Require Import BootDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

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

Lemma firstn_app_exact : forall {A} (l1 l2 : list A) n,
  length l1 = n -> firstn n (l1 ++ l2) = l1.
Proof.
  intros A l1 l2 n H. subst n. rewrite firstn_app, firstn_all, Nat.sub_diag.
  cbn. apply app_nil_r.
Qed.

Definition auxv_words (ph : PhdrInfo) (rnd : word) (uid hw : word) : list word :=
  flat_map (fun e => [fst e; snd e]) (auxv_entries ph rnd uid hw).

Lemma build_auxv_words : forall entries,
  build_auxv entries = flat_map word_le8 (flat_map (fun e => [fst e; snd e]) entries).
Proof.
  induction entries as [|[t v] es IH]; [reflexivity|].
  cbn [build_auxv flat_map fst snd app].
  change (build_auxv es) with
    (flat_map (fun e : bv 64 * bv 64 => word_le8 (fst e) ++ word_le8 (snd e)) es) in IH.
  rewrite IH, <- app_assoc. reflexivity.
Qed.

Lemma auxv_bytes_words : forall ph rnd uid hw,
  auxv_bytes ph rnd uid hw = flat_map word_le8 (auxv_words ph rnd uid hw).
Proof. intros. unfold auxv_bytes, auxv_words. apply build_auxv_words. Qed.

Definition struct_nat (av ev : list (list byte)) : nat :=
  (8 + (length av + 1) * 8 + (length ev + 1) * 8 + auxv_size)%nat.

Definition pad_nat (av ev : list (list byte)) : nat :=
  Z.to_nat ((8 - Z.of_nat (struct_nat av ev + length (flatten_strings av)
                           + length (flatten_strings ev)) mod 8) mod 8).

Definition str_base (sp : word) (av ev : list (list byte)) : word :=
  sp + nat_to_word (struct_nat av ev).
Definition env_base (sp : word) (av ev : list (list byte)) : word :=
  str_base sp av ev + nat_to_word (total_arg_bytes_nat av).

Definition argv_ptrs (sp : word) (av ev : list (list byte)) : list word :=
  fst (string_addrs (str_base sp av ev) av).
Definition envp_ptrs (sp : word) (av ev : list (list byte)) : list word :=
  fst (string_addrs (env_base sp av ev) ev).

Definition struct_prefix (ph : PhdrInfo) (sp : word) (av ev : list (list byte))
    (uid hw : word) : list byte :=
  word_le8 (len_word av)
  ++ flat_map word_le8 (argv_ptrs sp av ev)
  ++ word_le8 (Z_to_bv 64 0)
  ++ flat_map word_le8 (envp_ptrs sp av ev)
  ++ word_le8 (Z_to_bv 64 0)
  ++ auxv_bytes ph (at_random_ptr sp av ev) uid hw.

Lemma length_argv_ptrs : forall sp av ev, length (argv_ptrs sp av ev) = length av.
Proof. intros. unfold argv_ptrs. apply length_string_addrs_fst. Qed.

Lemma length_envp_ptrs : forall sp av ev, length (envp_ptrs sp av ev) = length ev.
Proof. intros. unfold envp_ptrs. apply length_string_addrs_fst. Qed.

Lemma length_struct_prefix : forall ph sp av ev uid hw,
  length (struct_prefix ph sp av ev uid hw) = struct_nat av ev.
Proof.
  intros. unfold struct_prefix, struct_nat.
  rewrite !length_app, !length_flat_map_le8, length_argv_ptrs, length_envp_ptrs,
    !length_n_to_le_8, length_auxv_bytes.
  lia.
Qed.

Lemma bsb_decomp : forall ph (sp : word) av ev uid hw draw,
  build_stack_bytes ph sp av ev uid hw draw =
  struct_prefix ph sp av ev uid hw
  ++ flatten_strings av ++ flatten_strings ev
  ++ repeat (Z_to_bv 8 0) (pad_nat av ev) ++ at_random_bytes (ed_random draw).
Proof.
  intros ph sp av ev uid hw draw.
  unfold build_stack_bytes. rewrite !length_auxv_bytes.
  rewrite (string_addrs_pair av). cbv beta iota.
  rewrite (string_addrs_pair ev). cbv beta iota.
  match goal with
  | |- context [Z.to_nat ((8 - Z.of_nat (length ?r) mod 8) mod 8)] =>
      replace (length r)
        with (struct_nat av ev + length (flatten_strings av) + length (flatten_strings ev))%nat
        by (unfold struct_nat; rewrite !length_app, !length_flat_map_le8,
              !length_string_addrs_fst, !length_n_to_le_8, length_auxv_bytes; lia)
  end.
  unfold struct_prefix, argv_ptrs, envp_ptrs, env_base, str_base, pad_nat, struct_nat.
  rewrite <- !app_assoc. reflexivity.
Qed.

Lemma length_bsb : forall ph (sp : word) av ev uid hw draw,
  length (build_stack_bytes ph sp av ev uid hw draw)
  = (struct_nat av ev + length (flatten_strings av) + length (flatten_strings ev)
     + pad_nat av ev + 16)%nat.
Proof.
  intros. rewrite bsb_decomp, !length_app, length_struct_prefix, repeat_length, length_at_random_bytes.
  lia.
Qed.

Lemma at_random_ptr_eq : forall (sp : word) av ev,
  at_random_ptr sp av ev =
  sp + nat_to_word (struct_nat av ev + length (flatten_strings av)
                    + length (flatten_strings ev) + pad_nat av ev).
Proof. intros sp av ev. reflexivity. Qed.

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

Lemma argv_ptr_eq : forall sp av ev i, (i < length av)%nat ->
  nth i (argv_ptrs sp av ev) (Z_to_bv 64 0)
  = sp + nat_to_word (struct_nat av ev + total_arg_bytes_nat (firstn i av)).
Proof.
  intros sp av ev i Hi. unfold argv_ptrs. rewrite nth_string_addrs by exact Hi.
  unfold str_base. rewrite nat_to_word_add_merge. reflexivity.
Qed.

Lemma envp_ptr_eq : forall sp av ev k, (k < length ev)%nat ->
  nth k (envp_ptrs sp av ev) (Z_to_bv 64 0)
  = sp + nat_to_word (struct_nat av ev + total_arg_bytes_nat av
                      + total_arg_bytes_nat (firstn k ev)).
Proof.
  intros sp av ev k Hk. unfold envp_ptrs. rewrite nth_string_addrs by exact Hk.
  unfold env_base, str_base. rewrite !nat_to_word_add_merge, Nat.add_assoc. reflexivity.
Qed.

Definition M0 (ph : PhdrInfo) (sp0 : Z) (inp : ProcInput) (draw : EntryDraw) : word -> option byte :=
  wrap_mem ph (Z_to_bv 64 sp0) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) draw.

Definition stack_pristine (ph : PhdrInfo) (sp0 : Z) (inp : ProcInput) (draw : EntryDraw)
    (mem : word -> option byte) : Prop :=
  forall a : word, (sp0 <= bv_unsigned a < rand0Z sp0 inp + 16)%Z ->
    mem a = M0 ph sp0 inp draw a.

Section Layout.
  Variable segs : list Segment.
  Variable ph : PhdrInfo.
  Variable sp0 : Z.
  Variable inp : ProcInput.
  Variable draw : EntryDraw.

  Hypothesis Hsp_lo : (sp_window_lo <= sp0)%Z.
  Hypothesis Hsp_hi : (sp0 + entry_stack_span (in_argv inp) (in_envp inp) <= sp_window_hi)%Z.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).

  Let argv := in_argv inp.
  Let envp := in_envp inp.
  Let uid := in_uid inp.
  Let hw := in_hwcap inp.
  Let SP : word := Z_to_bv 64 sp0.
  Let bsb := build_stack_bytes ph SP argv envp uid hw draw.
  Let stk := stack_to_mem SP bsb.

  Let rnd : word := at_random_ptr SP argv envp.

  Definition auxv_word (w : nat) : word :=
    nth w [AT_PHDR; Z_to_bv 64 (Z.of_N (ph_addr ph)); AT_PHENT; Z_to_bv 64 (Z.of_N (ph_ent ph));
           AT_PHNUM; Z_to_bv 64 (Z.of_N (ph_num ph)); AT_HWCAP; in_hwcap inp; AT_PAGESZ; Z_to_bv 64 4096;
           AT_UID; in_uid inp; AT_EUID; in_uid inp; AT_SECURE; Z_to_bv 64 0;
           AT_RANDOM; Z_to_bv 64 (rand0Z sp0 inp); AT_NULL; Z_to_bv 64 0] (Z_to_bv 64 0).

  Definition argv0 : list byte := nth 0 (in_argv inp) [].

End Layout.
