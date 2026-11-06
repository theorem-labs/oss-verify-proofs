(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.BootWitness Require Import BootDefs.
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma build_stack_bytes_within_span : forall ph (sp : word) a e uid hw draw,
  (Z.of_nat (length (build_stack_bytes ph sp a e uid hw draw))
   <= entry_stack_span a e)%Z.
Proof.
  intros ph sp a e uid hw draw.
  unfold entry_stack_span, build_stack_bytes. cbv zeta.
  rewrite (string_addrs_pair a). cbv beta iota.
  rewrite (string_addrs_pair e). cbv beta iota.
  rewrite !length_app, repeat_length, !length_flat_map_le8,
    !length_string_addrs_fst, !length_n_to_le_8, length_auxv_bytes,
    !length_flatten_strings.
  rewrite length_at_random_bytes.
  rewrite !total_arg_bytes_Z.
  match goal with
  | |- context [Z.to_nat ?pd] =>
      assert (Hpd : (0 <= pd < 8)%Z) by (apply Z.mod_pos_bound; lia)
  end.
  unfold auxv_size. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

Lemma length_auxv_words : forall ph rnd uid hw, length (auxv_words ph rnd uid hw) = 20%nat.
Proof. reflexivity. Qed.

Lemma auxv_words_eq : forall ph rnd uid hw,
  auxv_words ph rnd uid hw =
  [AT_PHDR; Z_to_bv 64 (Z.of_N (ph_addr ph)); AT_PHENT; Z_to_bv 64 (Z.of_N (ph_ent ph));
   AT_PHNUM; Z_to_bv 64 (Z.of_N (ph_num ph)); AT_HWCAP; hw; AT_PAGESZ; Z_to_bv 64 4096;
   AT_UID; uid; AT_EUID; uid; AT_SECURE; Z_to_bv 64 0;
   AT_RANDOM; rnd; AT_NULL; Z_to_bv 64 0].
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma at_random_bytes_draw0 : at_random_bytes (ed_random draw0) = repeat (Z_to_bv 8 0) 16.
Proof.
  cbn [ed_random draw0 at_random_bytes repeat].
  repeat (apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|]). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition struct_nat (av ev : list (list byte)) : nat :=
  (8 + (length av + 1) * 8 + (length ev + 1) * 8 + auxv_size)%nat.

(* [comment removed for export] *)
Definition pad_nat (av ev : list (list byte)) : nat :=
  Z.to_nat ((8 - Z.of_nat (struct_nat av ev + length (flatten_strings av)
                           + length (flatten_strings ev)) mod 8) mod 8).

(* [comment removed for export] *)
Definition str_base (sp : word) (av ev : list (list byte)) : word :=
  sp + nat_to_word (struct_nat av ev).
Definition env_base (sp : word) (av ev : list (list byte)) : word :=
  str_base sp av ev + nat_to_word (total_arg_bytes_nat av).

(* [comment removed for export] *)
Definition argv_ptrs (sp : word) (av ev : list (list byte)) : list word :=
  fst (string_addrs (str_base sp av ev) av).
Definition envp_ptrs (sp : word) (av ev : list (list byte)) : list word :=
  fst (string_addrs (env_base sp av ev) ev).

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma at_random_ptr_eq : forall (sp : word) av ev,
  at_random_ptr sp av ev =
  sp + nat_to_word (struct_nat av ev + length (flatten_strings av)
                    + length (flatten_strings ev) + pad_nat av ev).
Proof. intros sp av ev. reflexivity. Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition M0 (ph : PhdrInfo) (sp0 : Z) (inp : ProcInput) (draw : EntryDraw) : word -> option byte :=
  wrap_mem ph (Z_to_bv 64 sp0) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) draw.

Lemma M0_init : forall segs pc ph sp0 inp draw,
  ms_mem (init_machine_state segs pc ph (Z_to_bv 64 sp0) draw
            (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) = M0 ph sp0 inp draw.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Definition stack_pristine (ph : PhdrInfo) (sp0 : Z) (inp : ProcInput) (draw : EntryDraw)
    (mem : word -> option byte) : Prop :=
  forall a : word, (sp0 <= bv_unsigned a < rand0Z sp0 inp + 16)%Z ->
    mem a = M0 ph sp0 inp draw a.

Lemma stack_pristine_M0 : forall ph sp0 inp draw, stack_pristine ph sp0 inp draw (M0 ph sp0 inp draw).
Proof. intros ph sp0 inp draw a _. reflexivity. Qed.

(* [comment removed for export] *)
Lemma stack_pristine_of_above : forall ph sp0 inp draw mem,
  (forall a : word, (sp0 <= bv_unsigned a)%Z -> mem a = M0 ph sp0 inp draw a) ->
  stack_pristine ph sp0 inp draw mem.
Proof. intros ph sp0 inp draw mem H a Ha. apply H. lia. Qed.

(* [comment removed for export] *)
Lemma stack_pristine_frame : forall ph sp0 inp draw mem mem',
  stack_pristine ph sp0 inp draw mem ->
  (forall a : word, (sp0 <= bv_unsigned a < rand0Z sp0 inp + 16)%Z -> mem' a = mem a) ->
  stack_pristine ph sp0 inp draw mem'.
Proof. intros ph sp0 inp draw mem mem' H Hf a Ha. rewrite Hf by exact Ha. apply H. exact Ha. Qed.

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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma argc_bounds : (1 <= argcZ inp <= 1024)%Z.
  Proof. clear stk bsb. destruct Hva as [H _]. unfold argcZ. exact H. Qed.

  Lemma envc_bounds : (0 <= envcZ inp <= 256)%Z.
  Proof. clear stk bsb. destruct Hve as [H _]. unfold envcZ. lia. Qed.

  Lemma strbytes_eq :
    strbytesZ inp = (total_arg_bytes (in_argv inp) + total_arg_bytes (in_envp inp))%Z.
  Proof.
    clear stk bsb. unfold strbytesZ. rewrite Nat2Z.inj_add, !length_flatten_strings, !total_arg_bytes_Z. lia.
  Qed.

  Lemma strbytes_bounds : (0 <= strbytesZ inp <= 2228224)%Z.
  Proof.
    clear stk bsb. rewrite strbytes_eq.
    destruct Hva as [_ [Ha _]]. destruct Hve as [_ [He _]].
    pose proof (total_arg_bytes_nonneg (in_argv inp)).
    pose proof (total_arg_bytes_nonneg (in_envp inp)). lia.
  Qed.

  Lemma structZ_eq : structZ inp = (184 + 8 * argcZ inp + 8 * envcZ inp)%Z.
  Proof. clear stk bsb. unfold structZ. lia. Qed.

  Lemma struct_bounds : (192 <= structZ inp <= 10424)%Z.
  Proof. clear stk bsb. pose proof argc_bounds. pose proof envc_bounds. unfold structZ. lia. Qed.

  Lemma struct_mod8 : (structZ inp mod 8 = 0)%Z.
  Proof.
    clear stk bsb. rewrite structZ_eq.
    replace (184 + 8 * argcZ inp + 8 * envcZ inp)%Z with ((23 + argcZ inp + envcZ inp) * 8)%Z by lia.
    apply Z_mod_mult.
  Qed.

  Lemma pad_bounds : (0 <= padZ inp < 8)%Z.
  Proof. clear stk bsb. unfold padZ. apply Z.mod_pos_bound. lia. Qed.

  Lemma sb_bounds : (0 <= sbZ inp <= 2228231)%Z.
  Proof. clear stk bsb. pose proof strbytes_bounds. pose proof pad_bounds. unfold sbZ. lia. Qed.

  Lemma sb_mod8 : (sbZ inp mod 8 = 0)%Z.
  Proof.
    clear stk bsb. pose proof struct_mod8 as Hs. pose proof strbytes_bounds.
    unfold sbZ, padZ.
    rewrite (Zplus_mod_idemp_r (8 - (structZ inp + strbytesZ inp) mod 8) (strbytesZ inp) 8).
    rewrite <- (Zplus_mod_idemp_l (structZ inp) (strbytesZ inp) 8). rewrite Hs, Z.add_0_l.
    rewrite <- (Zplus_mod_idemp_l (strbytesZ inp) (8 - strbytesZ inp mod 8) 8).
    replace (strbytesZ inp mod 8 + (8 - strbytesZ inp mod 8))%Z with 8%Z by lia.
    reflexivity.
  Qed.

  Lemma struct_nat_Z : Z.of_nat (struct_nat argv envp) = structZ inp.
  Proof. clear stk bsb. unfold struct_nat, structZ, argcZ, envcZ, argv, envp, auxv_size. lia. Qed.

  Lemma strbytes_nat_Z :
    Z.of_nat (length (flatten_strings argv) + length (flatten_strings envp)) = strbytesZ inp.
  Proof. clear stk bsb. reflexivity. Qed.

  Lemma pad_nat_Z : Z.of_nat (pad_nat argv envp) = padZ inp.
  Proof.
    clear stk bsb. pose proof pad_bounds as Hp. unfold pad_nat.
    rewrite <- Nat.add_assoc, Nat2Z.inj_add, struct_nat_Z, strbytes_nat_Z.
    fold (padZ inp). lia.
  Qed.

  Lemma raw_pad_Z :
    Z.of_nat (struct_nat argv envp + length (flatten_strings argv)
              + length (flatten_strings envp) + pad_nat argv envp)
    = (structZ inp + sbZ inp)%Z.
  Proof.
    clear stk bsb. unfold sbZ. rewrite <- strbytes_nat_Z, <- pad_nat_Z, <- struct_nat_Z. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bsb_lenZ : Z.of_nat (length bsb) = (structZ inp + sbZ inp + 16)%Z.
  Proof.
    clear stk. unfold bsb. rewrite length_bsb, Nat2Z.inj_add, raw_pad_Z. lia.
  Qed.

  Lemma sp_num : (0x7fff80000000 <= sp0 /\ sp0 + (structZ inp + sbZ inp + 16) <= 0x800000000000
                  /\ sp0 <= 0x800000000000 - 208)%Z.
  Proof.
    clear stk bsb.
    pose proof strbytes_eq as HE. pose proof pad_bounds as HP. pose proof structZ_eq as HS.
    pose proof argc_bounds as HA. pose proof envc_bounds as HV. pose proof strbytes_bounds as HB.
    pose proof Hsp_hi as HH. unfold entry_stack_span, auxv_size in HH.
    unfold sp_window_lo, sp_window_hi in Hsp_lo, HH. unfold argcZ, envcZ in *. subst argv envp.
    change (Z.of_nat 160) with 160%Z in HH. unfold sbZ.
    clear - Hsp_lo HH HE HP HS HA HV HB. lia.
  Qed.

  Lemma u_SP : bv_unsigned SP = sp0.
  Proof. clear stk bsb. pose proof sp_num. unfold SP. apply u_Z2bv; lia. Qed.

  Lemma bsb_len_bound : (Z.of_nat (length bsb) <= entry_stack_span_max)%Z.
  Proof.
    clear stk. pose proof (build_stack_bytes_within_span ph SP argv envp uid hw draw).
    pose proof (entry_stack_span_bound argv envp Hva Hve). unfold bsb. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma image_end_bound : (sp0 + (structZ inp + sbZ inp + 16) <= sp_window_hi)%Z.
  Proof. pose proof sp_num as H. clear stk bsb. unfold sp_window_hi. lia. Qed.

  Lemma bsb_nw : (bv_unsigned SP + Z.of_nat (length bsb) < 2^64)%Z.
  Proof.
    rewrite u_SP, bsb_lenZ. pose proof image_end_bound. clear stk bsb.
    unfold sp_window_hi in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma entry_fits : entry_stack_fits (Z_to_bv 64 sp0) (in_argv inp) (in_envp inp).
  Proof.
    pose proof u_SP as Hu. clear stk bsb. unfold entry_stack_fits. unfold SP in Hu. rewrite Hu. exact Hsp_hi.
  Qed.

  Lemma sp_valid : (sp0 mod 16 = 0)%Z -> valid_sp (Z_to_bv 64 sp0).
  Proof.
    intros Hsp16. pose proof u_SP as Hu. pose proof sp_num as Hn. pose proof struct_bounds. pose proof sb_bounds.
    clear stk bsb. unfold valid_sp. unfold SP in Hu. rewrite Hu.
    unfold sp_window_lo, sp_window_hi. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma envp0Z_eq : envp0Z sp0 inp = (sp0 + 16 + 8 * argcZ inp)%Z.
  Proof. reflexivity. Qed.
  Lemma auxv0Z_eq : auxv0Z sp0 inp = (envp0Z sp0 inp + 8 * envcZ inp + 8)%Z.
  Proof. clear stk bsb. unfold auxv0Z, envp0Z. lia. Qed.
  Lemma strs0Z_eq : strs0Z sp0 inp = (sp0 + structZ inp)%Z.
  Proof. clear stk bsb. unfold strs0Z, auxv0Z, structZ. lia. Qed.
  Lemma rand0Z_eq : rand0Z sp0 inp = (sp0 + structZ inp + sbZ inp)%Z.
  Proof. clear stk bsb. unfold rand0Z. rewrite strs0Z_eq. lia. Qed.
  Lemma image_endZ : (rand0Z sp0 inp + 16 = sp0 + Z.of_nat (length bsb))%Z.
  Proof. rewrite bsb_lenZ, rand0Z_eq. clear stk bsb. lia. Qed.

  (* [comment removed for export] *)
  Lemma argcZ_alin : forall tid, argcZ inp = alin_val (Env sp0 inp draw tid) 0 0 1 0 0.
  Proof. clear stk bsb. intros. unfold alin_val. cbn [e_sp e_inp]. lia. Qed.
  Lemma envp0Z_alin : forall tid, envp0Z sp0 inp = alin_val (Env sp0 inp draw tid) 1 16 8 0 0.
  Proof. clear stk bsb. intros. unfold envp0Z, alin_val. cbn [e_sp e_inp]. lia. Qed.
  Lemma auxv0Z_alin : forall tid, auxv0Z sp0 inp = alin_val (Env sp0 inp draw tid) 1 24 8 8 0.
  Proof. clear stk bsb. intros. unfold auxv0Z, alin_val. cbn [e_sp e_inp]. lia. Qed.
  Lemma strs0Z_alin : forall tid, strs0Z sp0 inp = alin_val (Env sp0 inp draw tid) 1 184 8 8 0.
  Proof. clear stk bsb. intros. unfold strs0Z, auxv0Z, alin_val. cbn [e_sp e_inp]. lia. Qed.
  Lemma rand0Z_alin : forall tid, rand0Z sp0 inp = alin_val (Env sp0 inp draw tid) 1 184 8 8 1.
  Proof. clear stk bsb. intros. unfold rand0Z, strs0Z, auxv0Z, alin_val. cbn [e_sp e_inp]. lia. Qed.

  (* [comment removed for export] *)
  Lemma layout_ranges :
    (sp0 + 24 <= envp0Z sp0 inp)%Z /\
    (envp0Z sp0 inp + 8 <= auxv0Z sp0 inp)%Z /\
    (auxv0Z sp0 inp + 160 = strs0Z sp0 inp)%Z /\
    (strs0Z sp0 inp <= rand0Z sp0 inp)%Z /\
    (rand0Z sp0 inp + 16 <= 2^47)%Z.
  Proof.
    pose proof image_end_bound. clear stk bsb.
    pose proof argc_bounds. pose proof envc_bounds. pose proof sb_bounds.
    unfold rand0Z, strs0Z, auxv0Z, envp0Z, structZ, sp_window_hi in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sp0_mod8 : (sp0 mod 16 = 0)%Z -> (sp0 mod 8 = 0)%Z.
  Proof.
    clear. intros Hsp16. rewrite <- (Z.mod_mod_divide _ 16 8) by (exists 2%Z; reflexivity).
    rewrite Hsp16. reflexivity.
  Qed.

  Lemma envp0Z_mod8 : (sp0 mod 16 = 0)%Z -> (envp0Z sp0 inp mod 8 = 0)%Z.
  Proof.
    clear. intros Hsp16. pose proof (sp0_mod8 Hsp16). unfold envp0Z.
    replace (sp0 + 16 + 8 * argcZ inp)%Z with (sp0 + (2 + argcZ inp) * 8)%Z by lia.
    rewrite Z_mod_plus_full. assumption.
  Qed.

  Lemma auxv0Z_mod8 : (sp0 mod 16 = 0)%Z -> (auxv0Z sp0 inp mod 8 = 0)%Z.
  Proof.
    clear. intros Hsp16. pose proof (sp0_mod8 Hsp16). unfold auxv0Z.
    replace (sp0 + 24 + 8 * argcZ inp + 8 * envcZ inp)%Z
      with (sp0 + (3 + argcZ inp + envcZ inp) * 8)%Z by lia.
    rewrite Z_mod_plus_full. assumption.
  Qed.

  Lemma strs0Z_mod8 : (sp0 mod 16 = 0)%Z -> (strs0Z sp0 inp mod 8 = 0)%Z.
  Proof.
    clear. intros Hsp16. pose proof (auxv0Z_mod8 Hsp16). unfold strs0Z.
    replace (auxv0Z sp0 inp + 160)%Z with (auxv0Z sp0 inp + 20 * 8)%Z by lia.
    rewrite Z_mod_plus_full. assumption.
  Qed.

  Lemma rand0Z_mod8 : (sp0 mod 16 = 0)%Z -> (rand0Z sp0 inp mod 8 = 0)%Z.
  Proof.
    clear stk bsb. intros Hsp16. pose proof (strs0Z_mod8 Hsp16) as H1. pose proof sb_mod8 as H2.
    unfold rand0Z. rewrite Z.add_mod, H1, H2 by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma u_at_random_ptr :
    bv_unsigned (at_random_ptr (Z_to_bv 64 sp0) (in_argv inp) (in_envp inp)) = rand0Z sp0 inp.
  Proof.
    pose proof image_end_bound as He. pose proof u_SP as Hu.
    fold SP argv envp. rewrite at_random_ptr_eq, word_add_nat, Hu, raw_pad_Z, rand0Z_eq.
    clear stk bsb. pose proof sb_bounds. pose proof sp_num. pose proof struct_bounds.
    unfold sp_window_hi in *.
    rewrite u_Z2bv; lia.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma bsb_fold : build_stack_bytes ph (Z_to_bv 64 sp0) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) draw = bsb.
  Proof. reflexivity. Qed.

  Lemma read_bridge : forall mem (a : word) (pre mid post : list byte),
    stack_pristine ph sp0 inp draw mem ->
    bsb = pre ++ mid ++ post ->
    bv_unsigned a = (sp0 + Z.of_nat (length pre))%Z ->
    rdn segs mem a (length mid) = Some mid.
  Proof.
    intros mem a pre mid post Hpr Hsplit Ha.
    pose proof bsb_nw as Hnw. pose proof u_SP as Hu. pose proof image_endZ as Hend.
    assert (Hlen : (length pre + length mid <= length bsb)%nat).
    { rewrite Hsplit, !length_app. lia. }
    pose proof (read_at_offset segs SP bsb pre mid post (length mid) Hsplit eq_refl Hnw) as Hrd.
    rewrite <- (word_at_offset SP a (length pre)) in Hrd by (rewrite Hu; exact Ha).
    rewrite <- Hrd. apply rdn_ext.
    - clear stk. rewrite Hu in Hnw. lia.
    - intros x Hx. rewrite (Hpr x) by lia.
      unfold M0. fold SP argv envp uid hw. rewrite wrap_above_sp by (rewrite Hu; lia).
      apply stack_to_mem_image_in_block. unfold entry_block_top. fold bsb. rewrite Hu. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma read_bridge_byte : forall mem (a : word) (pre s post : list byte) j,
    stack_pristine ph sp0 inp draw mem ->
    bsb = pre ++ s ++ post -> (j < length s)%nat ->
    bv_unsigned a = (sp0 + Z.of_nat (length pre) + Z.of_nat j)%Z ->
    rdn segs mem a 1 = Some [nth j s (Z_to_bv 8 0)].
  Proof.
    intros mem a pre s post j Hpr Hsplit Hj Ha.
    rewrite <- (firstn_skipn j s) in Hsplit.
    rewrite (skipn_nth s j (Z_to_bv 8 0) Hj) in Hsplit.
    rewrite <- app_assoc in Hsplit. cbn [app] in Hsplit.
    change (firstn j s ++ nth j s (Z_to_bv 8 0) :: skipn (S j) s ++ post)
      with (firstn j s ++ [nth j s (Z_to_bv 8 0)] ++ (skipn (S j) s ++ post)) in Hsplit.
    rewrite app_assoc in Hsplit.
    apply (read_bridge mem a _ [nth j s (Z_to_bv 8 0)] _ Hpr Hsplit).
    rewrite length_app, firstn_length_le by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma u_len_word_argv : bv_unsigned (len_word (in_argv inp)) = argcZ inp.
  Proof.
    clear stk bsb. pose proof argc_bounds. unfold len_word, argcZ in *. apply u_Z2bv; lia.
  Qed.

  Lemma bsb_split_argc : exists post, bsb = [] ++ word_le8 (len_word argv) ++ post.
  Proof.
    unfold bsb. rewrite bsb_decomp. unfold struct_prefix. eexists.
    cbn [app]. rewrite <- !app_assoc. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma read_argc8 : forall mem (a : word),
    stack_pristine ph sp0 inp draw mem -> bv_unsigned a = sp0 ->
    rdn segs mem a 8 = Some (word_le8 (len_word (in_argv inp)))
    /\ bytes_le_to_Z (word_le8 (len_word (in_argv inp))) = argcZ inp
    /\ le_bytes_to_word (word_le8 (len_word (in_argv inp))) = Z_to_bv 64 (argcZ inp).
  Proof.
    intros mem a Hpr Ha. destruct bsb_split_argc as [post Hs].
    split; [|split].
    - apply (read_bridge mem a [] _ post Hpr Hs). cbn [length]. lia.
    - rewrite bytes_le_n_to_le_8. apply u_len_word_argv.
    - rewrite le_word_of_le8. apply word_of_unsigned. apply u_len_word_argv.
  Qed.

  (* [comment removed for export] *)
  Lemma read_argc4 : forall mem (a : word),
    stack_pristine ph sp0 inp draw mem -> bv_unsigned a = sp0 ->
    rdn segs mem a 4 = Some (firstn 4 (word_le8 (len_word (in_argv inp))))
    /\ bytes_le_to_Z (firstn 4 (word_le8 (len_word (in_argv inp)))) = argcZ inp
    /\ le_bytes_to_word (firstn 4 (word_le8 (len_word (in_argv inp)))) = Z_to_bv 64 (argcZ inp).
  Proof.
    intros mem a Hpr Ha. destruct (read_argc8 mem a Hpr Ha) as [Hr _].
    pose proof argc_bounds.
    assert (Hv : bytes_le_to_Z (firstn 4 (word_le8 (len_word (in_argv inp)))) = argcZ inp).
    { rewrite bytes_le_firstn4_le8, u_len_word_argv. apply Z.mod_small. lia. }
    split; [|split].
    - exact (rdn_firstn segs mem 8 a _ 4 Hr ltac:(lia)).
    - exact Hv.
    - unfold le_bytes_to_word. rewrite Hv. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma argc_load8 :
    bv_unsigned (bv_extract 0 64 (Z_to_bv 64 (argcZ inp))) = argcZ inp.
  Proof. clear stk bsb. pose proof argc_bounds. rewrite bv_extract_64_id. apply u_Z2bv; lia. Qed.

  Lemma argc_load4s :
    bv_unsigned (sext 64 (bv_extract 0 32 (Z_to_bv 64 (argcZ inp)))) = argcZ inp.
  Proof.
    clear stk bsb. pose proof argc_bounds.
    rewrite lw_small by (rewrite u_Z2bv; lia). apply u_Z2bv; lia.
  Qed.

  Lemma argc_load4u :
    bv_unsigned (zext 64 (bv_extract 0 32 (Z_to_bv 64 (argcZ inp)))) = argcZ inp.
  Proof.
    clear stk bsb. pose proof argc_bounds.
    rewrite lwu_small by (rewrite u_Z2bv; lia). apply u_Z2bv; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma total_firstn_argv_bound : forall i,
    (Z.of_nat (total_arg_bytes_nat (firstn i argv)) <= total_arg_bytes (in_argv inp))%Z.
  Proof.
    clear stk bsb. intros i. pose proof (total_arg_bytes_firstn_le i argv).
    unfold argv in *. rewrite total_arg_bytes_Z. lia.
  Qed.

  Lemma total_firstn_envp_bound : forall k,
    (Z.of_nat (total_arg_bytes_nat (firstn k envp)) <= total_arg_bytes (in_envp inp))%Z.
  Proof.
    clear stk bsb. intros k. pose proof (total_arg_bytes_firstn_le k envp).
    unfold envp in *. rewrite total_arg_bytes_Z. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma u_argv_ptr : forall i, (i < length (in_argv inp))%nat ->
    bv_unsigned (nth i (argv_ptrs SP argv envp) (Z_to_bv 64 0))
    = (strs0Z sp0 inp + Z.of_nat (total_arg_bytes_nat (firstn i (in_argv inp))))%Z.
  Proof.
    intros i Hi. pose proof u_SP as Hu. pose proof image_end_bound.
    rewrite argv_ptr_eq by exact Hi. rewrite word_add_nat, Hu, Nat2Z.inj_add, struct_nat_Z, strs0Z_eq.
    clear stk bsb. pose proof (total_firstn_argv_bound i). pose proof strbytes_eq.
    pose proof sb_bounds. pose proof sp_num. pose proof strbytes_bounds. pose proof struct_bounds.
    pose proof (total_arg_bytes_nonneg (in_envp inp)).
    unfold sbZ, sp_window_hi, argv in *. rewrite u_Z2bv by lia. lia.
  Qed.

  Lemma bsb_split_argv_ptr : forall i, (i < length argv)%nat -> exists post,
    bsb = (word_le8 (len_word argv) ++ flat_map word_le8 (firstn i (argv_ptrs SP argv envp)))
          ++ word_le8 (nth i (argv_ptrs SP argv envp) (Z_to_bv 64 0)) ++ post.
  Proof.
    intros i Hi. unfold bsb. rewrite bsb_decomp. unfold struct_prefix.
    rewrite (flat_map_le8_decomp (argv_ptrs SP argv envp) i) by (rewrite length_argv_ptrs; exact Hi).
    eexists. rewrite <- !app_assoc. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma read_argv_ptr : forall mem (a : word) i,
    stack_pristine ph sp0 inp draw mem -> (i < length (in_argv inp))%nat ->
    bv_unsigned a = (sp0 + 8 + 8 * Z.of_nat i)%Z ->
    exists bs, rdn segs mem a 8 = Some bs
    /\ bytes_le_to_Z bs = (strs0Z sp0 inp + Z.of_nat (total_arg_bytes_nat (firstn i (in_argv inp))))%Z
    /\ le_bytes_to_word bs = nth i (argv_ptrs (Z_to_bv 64 sp0) (in_argv inp) (in_envp inp)) (Z_to_bv 64 0).
  Proof.
    intros mem a i Hpr Hi Ha. destruct (bsb_split_argv_ptr i Hi) as [post Hs].
    eexists. split; [|split].
    - apply (read_bridge mem a _ _ post Hpr Hs).
      rewrite length_app, length_n_to_le_8, length_flat_map_le8, firstn_length_le
        by (rewrite length_argv_ptrs; unfold argv; lia). lia.
    - rewrite bytes_le_n_to_le_8. apply u_argv_ptr. exact Hi.
    - apply le_word_of_le8.
  Qed.

  (* [comment removed for export] *)
  Lemma read_argv0_ptr : forall mem (a : word),
    stack_pristine ph sp0 inp draw mem -> bv_unsigned a = (sp0 + 8)%Z ->
    exists bs, rdn segs mem a 8 = Some bs
    /\ bytes_le_to_Z bs = strs0Z sp0 inp
    /\ le_bytes_to_word bs = Z_to_bv 64 (strs0Z sp0 inp).
  Proof.
    intros mem a Hpr Ha. pose proof argc_bounds as Hc.
    destruct (read_argv_ptr mem a 0 Hpr ltac:(unfold argcZ in Hc; lia) ltac:(lia))
      as [bs [Hr [Hv _]]].
    cbn [firstn] in Hv. change (total_arg_bytes_nat []) with 0%nat in Hv. rewrite Z.add_0_r in Hv.
    exists bs. split; [exact Hr|]. split; [exact Hv|].
    unfold le_bytes_to_word. rewrite Hv. reflexivity.
  Qed.

  Lemma strs0_load8 :
    bv_unsigned (bv_extract 0 64 (Z_to_bv 64 (strs0Z sp0 inp))) = strs0Z sp0 inp.
  Proof.
    pose proof layout_ranges. clear stk bsb. pose proof sp_num.
    rewrite bv_extract_64_id. apply u_Z2bv; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bsb_split_argv_null : exists post,
    bsb = (word_le8 (len_word argv) ++ flat_map word_le8 (argv_ptrs SP argv envp))
          ++ word_le8 (Z_to_bv 64 0) ++ post.
  Proof.
    unfold bsb. rewrite bsb_decomp. unfold struct_prefix.
    eexists. rewrite <- !app_assoc. reflexivity.
  Qed.

  Lemma read_argv_null : forall mem (a : word),
    stack_pristine ph sp0 inp draw mem -> bv_unsigned a = (sp0 + 8 + 8 * argcZ inp)%Z ->
    rdn segs mem a 8 = Some (word_le8 (Z_to_bv 64 0)).
  Proof.
    intros mem a Hpr Ha. destruct bsb_split_argv_null as [post Hs].
    apply (read_bridge mem a _ _ post Hpr Hs).
    rewrite length_app, length_n_to_le_8, length_flat_map_le8, length_argv_ptrs.
    unfold argcZ in Ha. unfold argv. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma u_envp_ptr : forall k, (k < length (in_envp inp))%nat ->
    bv_unsigned (nth k (envp_ptrs SP argv envp) (Z_to_bv 64 0))
    = (strs0Z sp0 inp + total_arg_bytes (in_argv inp)
       + Z.of_nat (total_arg_bytes_nat (firstn k (in_envp inp))))%Z.
  Proof.
    intros k Hk. pose proof u_SP as Hu. pose proof image_end_bound.
    rewrite envp_ptr_eq by exact Hk.
    rewrite word_add_nat, Hu, !Nat2Z.inj_add, struct_nat_Z, strs0Z_eq, <- total_arg_bytes_Z.
    clear stk bsb. pose proof (total_firstn_envp_bound k). pose proof strbytes_eq.
    pose proof sb_bounds. pose proof sp_num. pose proof strbytes_bounds. pose proof struct_bounds.
    pose proof (total_arg_bytes_nonneg (in_argv inp)).
    unfold sbZ, sp_window_hi, argv, envp in *. rewrite u_Z2bv by lia. lia.
  Qed.

  Lemma bsb_split_envp_ptr : forall k, (k < length envp)%nat -> exists post,
    bsb = (word_le8 (len_word argv) ++ flat_map word_le8 (argv_ptrs SP argv envp)
           ++ word_le8 (Z_to_bv 64 0) ++ flat_map word_le8 (firstn k (envp_ptrs SP argv envp)))
          ++ word_le8 (nth k (envp_ptrs SP argv envp) (Z_to_bv 64 0)) ++ post.
  Proof.
    intros k Hk. unfold bsb. rewrite bsb_decomp. unfold struct_prefix.
    rewrite (flat_map_le8_decomp (envp_ptrs SP argv envp) k) by (rewrite length_envp_ptrs; exact Hk).
    eexists. rewrite <- !app_assoc. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma read_envp_ptr : forall mem (a : word) k,
    stack_pristine ph sp0 inp draw mem -> (k < length (in_envp inp))%nat ->
    bv_unsigned a = (envp0Z sp0 inp + 8 * Z.of_nat k)%Z ->
    exists bs, rdn segs mem a 8 = Some bs
    /\ bytes_le_to_Z bs = (strs0Z sp0 inp + total_arg_bytes (in_argv inp)
                           + Z.of_nat (total_arg_bytes_nat (firstn k (in_envp inp))))%Z
    /\ (sp0 < bytes_le_to_Z bs < 2^47)%Z
    /\ le_bytes_to_word bs <> Z_to_bv 64 0.
  Proof.
    intros mem a k Hpr Hk Ha. destruct (bsb_split_envp_ptr k Hk) as [post Hs].
    pose proof (u_envp_ptr k Hk) as Hv.
    assert (Hrange : (sp0 < strs0Z sp0 inp + total_arg_bytes (in_argv inp)
                     + Z.of_nat (total_arg_bytes_nat (firstn k (in_envp inp))) < 2^47)%Z).
    { pose proof image_end_bound. clear stk bsb Hs Hv.
      pose proof (total_firstn_envp_bound k). pose proof strbytes_eq.
      pose proof pad_bounds. pose proof strbytes_bounds. pose proof struct_bounds.
      pose proof (total_arg_bytes_nonneg (in_argv inp)). rewrite strs0Z_eq.
      unfold sbZ, sp_window_hi, argv, envp in *. lia. }
    eexists. split; [|split; [|split]].
    - apply (read_bridge mem a _ _ post Hpr Hs).
      rewrite !length_app, !length_n_to_le_8, !length_flat_map_le8, length_argv_ptrs,
        firstn_length_le by (rewrite length_envp_ptrs; unfold envp; lia).
      unfold envp0Z, argcZ in Ha. unfold argv. lia.
    - rewrite bytes_le_n_to_le_8. exact Hv.
    - rewrite bytes_le_n_to_le_8, Hv. exact Hrange.
    - rewrite le_word_of_le8. intros E. rewrite E in Hv.
      rewrite u_Z2bv in Hv by lia. clear stk bsb Hs E. pose proof sp_num. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bsb_split_envp_null : exists post,
    bsb = (word_le8 (len_word argv) ++ flat_map word_le8 (argv_ptrs SP argv envp)
           ++ word_le8 (Z_to_bv 64 0) ++ flat_map word_le8 (envp_ptrs SP argv envp))
          ++ word_le8 (Z_to_bv 64 0) ++ post.
  Proof.
    unfold bsb. rewrite bsb_decomp. unfold struct_prefix.
    eexists. rewrite <- !app_assoc. reflexivity.
  Qed.

  Lemma read_envp_null : forall mem (a : word),
    stack_pristine ph sp0 inp draw mem -> bv_unsigned a = (envp0Z sp0 inp + 8 * envcZ inp)%Z ->
    rdn segs mem a 8 = Some (word_le8 (Z_to_bv 64 0)).
  Proof.
    intros mem a Hpr Ha. destruct bsb_split_envp_null as [post Hs].
    apply (read_bridge mem a _ _ post Hpr Hs).
    rewrite !length_app, !length_n_to_le_8, !length_flat_map_le8, length_argv_ptrs, length_envp_ptrs.
    unfold envp0Z, argcZ, envcZ in Ha. unfold argv, envp. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma le_word_le8_0 : le_bytes_to_word (word_le8 (Z_to_bv 64 0)) = Z_to_bv 64 0.
  Proof. apply le_word_of_le8. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Let rnd : word := at_random_ptr SP argv envp.

  Lemma bsb_split_auxv_word : forall w, (w < 20)%nat -> exists post,
    bsb = (word_le8 (len_word argv) ++ flat_map word_le8 (argv_ptrs SP argv envp)
           ++ word_le8 (Z_to_bv 64 0) ++ flat_map word_le8 (envp_ptrs SP argv envp)
           ++ word_le8 (Z_to_bv 64 0) ++ flat_map word_le8 (firstn w (auxv_words ph rnd uid hw)))
          ++ word_le8 (nth w (auxv_words ph rnd uid hw) (Z_to_bv 64 0)) ++ post.
  Proof.
    intros w Hw. unfold bsb. rewrite bsb_decomp. unfold struct_prefix. fold rnd.
    rewrite (auxv_bytes_words ph rnd uid hw).
    rewrite (flat_map_le8_decomp (auxv_words ph rnd uid hw) w) by (rewrite length_auxv_words; exact Hw).
    eexists. rewrite <- !app_assoc. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma read_auxv_word : forall mem (a : word) w,
    stack_pristine ph sp0 inp draw mem -> (w < 20)%nat ->
    bv_unsigned a = (auxv0Z sp0 inp + 8 * Z.of_nat w)%Z ->
    rdn segs mem a 8
    = Some (word_le8 (nth w (auxv_words ph (at_random_ptr (Z_to_bv 64 sp0) (in_argv inp) (in_envp inp))
                                        (in_uid inp) (in_hwcap inp)) (Z_to_bv 64 0))).
  Proof.
    intros mem a w Hpr Hw Ha. destruct (bsb_split_auxv_word w Hw) as [post Hs].
    apply (read_bridge mem a _ _ post Hpr Hs).
    rewrite !length_app, !length_n_to_le_8, !length_flat_map_le8, length_argv_ptrs,
      length_envp_ptrs, firstn_length_le by (rewrite length_auxv_words; lia).
    unfold auxv0Z, argcZ, envcZ in Ha. unfold argv, envp. lia.
  Qed.

  (* [comment removed for export] *)
  Definition auxv_word (w : nat) : word :=
    nth w [AT_PHDR; Z_to_bv 64 (Z.of_N (ph_addr ph)); AT_PHENT; Z_to_bv 64 (Z.of_N (ph_ent ph));
           AT_PHNUM; Z_to_bv 64 (Z.of_N (ph_num ph)); AT_HWCAP; in_hwcap inp; AT_PAGESZ; Z_to_bv 64 4096;
           AT_UID; in_uid inp; AT_EUID; in_uid inp; AT_SECURE; Z_to_bv 64 0;
           AT_RANDOM; Z_to_bv 64 (rand0Z sp0 inp); AT_NULL; Z_to_bv 64 0] (Z_to_bv 64 0).

  Lemma at_random_ptr_word :
    at_random_ptr (Z_to_bv 64 sp0) (in_argv inp) (in_envp inp) = Z_to_bv 64 (rand0Z sp0 inp).
  Proof. apply word_of_unsigned. apply u_at_random_ptr. Qed.

  Lemma auxv_words_nth : forall w,
    nth w (auxv_words ph (at_random_ptr (Z_to_bv 64 sp0) (in_argv inp) (in_envp inp)) (in_uid inp) (in_hwcap inp))
        (Z_to_bv 64 0)
    = auxv_word w.
  Proof.
    intros w. rewrite auxv_words_eq, at_random_ptr_word. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma read_auxv : forall mem (a : word) w,
    stack_pristine ph sp0 inp draw mem -> (w < 20)%nat ->
    bv_unsigned a = (auxv0Z sp0 inp + 8 * Z.of_nat w)%Z ->
    rdn segs mem a 8 = Some (word_le8 (auxv_word w))
    /\ le_bytes_to_word (word_le8 (auxv_word w)) = auxv_word w
    /\ bv_extract 0 64 (le_bytes_to_word (word_le8 (auxv_word w))) = auxv_word w.
  Proof.
    intros mem a w Hpr Hw Ha. split; [|split].
    - rewrite (read_auxv_word mem a w Hpr Hw Ha), auxv_words_nth. reflexivity.
    - apply le_word_of_le8.
    - rewrite le_word_of_le8. apply bv_extract_64_id.
  Qed.

  Lemma u_rand0_word : bv_unsigned (Z_to_bv 64 (rand0Z sp0 inp)) = rand0Z sp0 inp.
  Proof. rewrite <- at_random_ptr_word. apply u_at_random_ptr. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma bsb_split_random : forall k n, (k + n <= 16)%nat -> exists pre post,
    bsb = pre ++ firstn n (skipn k (at_random_bytes (ed_random draw))) ++ post
    /\ Z.of_nat (length pre) = (rand0Z sp0 inp - sp0 + Z.of_nat k)%Z.
  Proof.
    intros k n Hkn. pose proof (length_at_random_bytes (ed_random draw)) as HL.
    unfold bsb. rewrite bsb_decomp.
    set (rb := at_random_bytes (ed_random draw)) in *.
    exists ((struct_prefix ph SP argv envp uid hw ++ flatten_strings argv ++ flatten_strings envp
             ++ repeat (Z_to_bv 8 0) (pad_nat argv envp)) ++ firstn k rb), (skipn n (skipn k rb)).
    split.
    - rewrite <- !app_assoc. rewrite (firstn_skipn n (skipn k rb)), (firstn_skipn k rb). reflexivity.
    - rewrite !length_app, !repeat_length, length_struct_prefix, firstn_length_le by lia.
      pose proof raw_pad_Z. rewrite rand0Z_eq. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma read_random : forall mem (a : word) (k : Z) (n : nat),
    stack_pristine ph sp0 inp draw mem -> (0 <= k)%Z -> (k + Z.of_nat n <= 16)%Z ->
    bv_unsigned a = (rand0Z sp0 inp + k)%Z ->
    rdn segs mem a n = Some (firstn n (skipn (Z.to_nat k) (at_random_bytes (ed_random draw)))).
  Proof.
    intros mem a k n Hpr Hk Hkn Ha. pose proof (length_at_random_bytes (ed_random draw)) as HL.
    destruct (bsb_split_random (Z.to_nat k) n ltac:(lia)) as [pre [post [Hs Hlen]]].
    assert (Hn : length (firstn n (skipn (Z.to_nat k) (at_random_bytes (ed_random draw)))) = n).
    { rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn. lia. }
    rewrite <- Hn at 1.
    apply (read_bridge mem a pre _ post Hpr Hs). rewrite Hlen. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma read_random_draw0 : forall mem (a : word) (k : Z) (n : nat),
    draw = draw0 ->
    stack_pristine ph sp0 inp draw mem -> (0 <= k)%Z -> (k + Z.of_nat n <= 16)%Z ->
    bv_unsigned a = (rand0Z sp0 inp + k)%Z ->
    rdn segs mem a n = Some (repeat (Z_to_bv 8 0) n).
  Proof.
    intros mem a k n Hd Hpr Hk Hkn Ha. rewrite (read_random mem a k n Hpr Hk Hkn Ha).
    rewrite Hd, at_random_bytes_draw0, skipn_repeat', firstn_repeat' by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma le_word_repeat0 : forall n, le_bytes_to_word (repeat (Z_to_bv 8 0) n) = Z_to_bv 64 0.
  Proof. intros n. unfold le_bytes_to_word. rewrite bytes_le_repeat0. reflexivity. Qed.

  Lemma extract_zero : forall w : N, bv_extract 0 w (Z_to_bv 64 0) = Z_to_bv w 0.
  Proof.
    intros w. apply bv_eq. rewrite bv_extract_unsigned, !Z_to_bv_unsigned. reflexivity.
  Qed.

  Lemma sext_zero : forall w : N, (0 < w)%N -> sext 64 (Z_to_bv w 0) = Z_to_bv 64 0.
  Proof.
    clear. intros w Hw. apply bv_eq. unfold sext. rewrite bv_sign_extend_unsigned, Z_to_bv_unsigned.
    unfold bv_signed. rewrite Z_to_bv_unsigned.
    rewrite (bv_wrap_small w 0) by (pose proof (bv_modulus_pos w); lia).
    rewrite bv_swrap_small; [reflexivity|].
    pose proof (bv_half_modulus_twice w ltac:(lia)). pose proof (bv_modulus_pos w).
    pose proof (bv_half_modulus_nonneg w). lia.
  Qed.

  Lemma zext_zero : forall w : N, (w <= 64)%N -> zext 64 (Z_to_bv w 0) = Z_to_bv 64 0.
  Proof.
    clear. intros w Hw. apply bv_eq. unfold zext. rewrite bv_zero_extend_unsigned by lia.
    rewrite !Z_to_bv_unsigned. rewrite !bv_wrap_small; try reflexivity.
    all: pose proof (bv_modulus_pos w); pose proof (bv_modulus_pos 64); lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition argv0 : list byte := nth 0 (in_argv inp) [].

  Lemma argv0_hd : argv0 = hd [] (in_argv inp).
  Proof. clear. unfold argv0. destruct (in_argv inp); reflexivity. Qed.

  Lemma argv_cons : exists rest, in_argv inp = argv0 :: rest.
  Proof.
    clear stk bsb rnd. pose proof argc_bounds as Hc. unfold argcZ in Hc. unfold argv0.
    destruct (in_argv inp) as [|a0 rest]; [cbn in Hc; lia|]. exists rest. reflexivity.
  Qed.

  Lemma argv0_len : (Z.of_nat (length argv0) <= 131071)%Z.
  Proof.
    clear stk bsb rnd. destruct argv_cons as [rest E]. destruct Hva as [_ [_ [Hl _]]].
    rewrite E in Hl. exact (Forall_inv Hl).
  Qed.

  Lemma argv0_no_nul : ~ In (Z_to_bv 8 0) argv0.
  Proof.
    clear stk bsb rnd. destruct argv_cons as [rest E]. destruct Hva as [_ [_ [_ [Hn _]]]].
    rewrite E in Hn. exact (Forall_inv Hn).
  Qed.

  Lemma argv0_fits : (strs0Z sp0 inp + Z.of_nat (length argv0) + 1 <= rand0Z sp0 inp)%Z.
  Proof.
    destruct argv_cons as [rest E]. clear stk bsb rnd.
    pose proof strbytes_eq as Hs. pose proof pad_bounds.
    pose proof (total_arg_bytes_nonneg rest). pose proof (total_arg_bytes_nonneg (in_envp inp)).
    rewrite E in Hs. unfold total_arg_bytes in Hs. cbn [fold_right] in Hs.
    fold (total_arg_bytes rest) in Hs. fold (total_arg_bytes (in_envp inp)) in Hs.
    unfold rand0Z, sbZ. lia.
  Qed.

  Lemma bsb_split_argv0 : exists post,
    bsb = struct_prefix ph SP argv envp uid hw ++ (argv0 ++ [Z_to_bv 8 0]) ++ post.
  Proof.
    destruct argv_cons as [rest E]. unfold bsb. rewrite bsb_decomp.
    unfold argv at 2. rewrite E. unfold flatten_strings at 1. cbn [flat_map].
    fold (flatten_strings rest). eexists. rewrite <- !app_assoc. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma read_argv0_byte : forall mem (a : word) i,
    stack_pristine ph sp0 inp draw mem -> (i <= length argv0)%nat ->
    bv_unsigned a = (strs0Z sp0 inp + Z.of_nat i)%Z ->
    rdn segs mem a 1 = Some [nth i (argv0 ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)].
  Proof.
    intros mem a i Hpr Hi Ha. destruct bsb_split_argv0 as [post Hs].
    apply (read_bridge_byte mem a _ _ post i Hpr Hs).
    - rewrite length_app. cbn [length]. lia.
    - rewrite length_struct_prefix, struct_nat_Z, strs0Z_eq in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma read_argv0_char : forall mem (a : word) i,
    stack_pristine ph sp0 inp draw mem -> (i < length argv0)%nat ->
    bv_unsigned a = (strs0Z sp0 inp + Z.of_nat i)%Z ->
    rdn segs mem a 1 = Some [nth i argv0 (Z_to_bv 8 0)]
    /\ nth i argv0 (Z_to_bv 8 0) <> Z_to_bv 8 0
    /\ bv_unsigned (nth i argv0 (Z_to_bv 8 0)) <> 0%Z.
  Proof.
    intros mem a i Hpr Hi Ha.
    rewrite (read_argv0_byte mem a i Hpr ltac:(lia) Ha), app_nth1 by exact Hi.
    assert (Hnz : nth i argv0 (Z_to_bv 8 0) <> Z_to_bv 8 0).
    { intros E. apply argv0_no_nul. rewrite <- E. apply nth_In. exact Hi. }
    split; [reflexivity|]. split; [exact Hnz|].
    intros Hu. apply Hnz. apply bv_eq. rewrite Hu. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma read_argv0_nul : forall mem (a : word),
    stack_pristine ph sp0 inp draw mem ->
    bv_unsigned a = (strs0Z sp0 inp + Z.of_nat (length argv0))%Z ->
    rdn segs mem a 1 = Some [Z_to_bv 8 0].
  Proof.
    intros mem a Hpr Ha.
    rewrite (read_argv0_byte mem a (length argv0) Hpr ltac:(lia) Ha).
    rewrite app_nth2, Nat.sub_diag by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma lbu_word : forall b : byte,
    zext 64 (bv_extract 0 8 (le_bytes_to_word [b])) = Z_to_bv 64 (bv_unsigned b).
  Proof. clear. intros b. apply word_of_unsigned. apply lbu_val. Qed.

End Layout.
