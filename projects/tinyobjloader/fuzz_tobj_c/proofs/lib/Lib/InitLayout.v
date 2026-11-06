(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint tab (l : list (list byte)) : nat :=
  match l with
  | [] => 0%nat
  | s :: r => (length s + 1 + tab r)%nat
  end.

Lemma tab_app : forall l1 l2, tab (l1 ++ l2) = (tab l1 + tab l2)%nat.
Proof. induction l1 as [|s l1 IH]; intros l2; cbn; [reflexivity|]. rewrite IH. lia. Qed.

Lemma total_arg_bytes_tab : forall l, total_arg_bytes l = Z.of_nat (tab l).
Proof.
  induction l as [|s l IH]; [reflexivity|].
  unfold total_arg_bytes in *. cbn [fold_right tab]. rewrite IH. lia.
Qed.

Lemma flatten_strings_cons : forall s l, flatten_strings (s :: l) = (s ++ [Z_to_bv 8 0]) ++ flatten_strings l.
Proof. reflexivity. Qed.

Lemma length_flatten_strings : forall l, length (flatten_strings l) = tab l.
Proof.
  induction l as [|s l IH]; [reflexivity|]. rewrite flatten_strings_cons, !length_app, IH. cbn. lia.
Qed.

Lemma length_word_le8 : forall w, length (word_le8 w) = 8%nat.
Proof. reflexivity. Qed.

Lemma length_flat_map_le8 : forall l, length (flat_map word_le8 l) = (8 * length l)%nat.
Proof. induction l as [|w l IH]; [reflexivity|]. cbn [flat_map]. rewrite length_app, IH, length_word_le8. cbn [length]. lia. Qed.

Lemma string_addrs_fst_length : forall base l, length (fst (string_addrs base l)) = length l.
Proof.
  intros base l. revert base. induction l as [|s l IH]; intros base; [reflexivity|].
  cbn. specialize (IH (base + len_word s + 1)%bv).
  destruct (string_addrs (base + len_word s + 1)%bv l) as [ptrs final]. cbn in *. now rewrite IH.
Qed.

Lemma length_build_auxv : forall l, length (build_auxv l) = (16 * length l)%nat.
Proof.
  induction l as [|[t v] l IH]; [reflexivity|]. cbn [build_auxv flat_map fst snd].
  rewrite !length_app, !length_word_le8. cbn [length]. fold (build_auxv l). rewrite IH. lia.
Qed.

Section Layout.
Variable ph : PhdrInfo.
Variable sp : word.
Variable argv envp : list (list byte).
Variable uid : word.
Variable hwcap : word.      (* [comment removed for export] *)
Variable draw : EntryDraw.  (* [comment removed for export] *)

Definition argc : nat := length argv.
Definition envc : nat := length envp.

Definition aux_off : nat := (24 + 8 * argc + 8 * envc)%nat.
Definition str_off : nat := (aux_off + 160)%nat.
Definition env_str_off : nat := (str_off + tab argv)%nat.
Definition raw_len : nat := (env_str_off + tab envp)%nat.
Definition pad_len : nat := Z.to_nat ((8 - Z.of_nat raw_len mod 8) mod 8).
Definition rand_off : nat := (raw_len + pad_len)%nat.
Definition img_len : nat := (rand_off + 16)%nat.

(* [comment removed for export] *)
Definition str_base : word := (sp + nat_to_word str_off)%bv.
Definition argv_ptrs : list word := fst (string_addrs str_base argv).
Definition env_str_base : word := snd (string_addrs str_base argv).
Definition envp_ptrs : list word := fst (string_addrs env_str_base envp).

Definition bsb : list byte := build_stack_bytes ph sp argv envp uid hwcap draw.

Lemma pad_len_lt8 : (pad_len < 8)%nat.
Proof using .
  unfold pad_len. pose proof (Z.mod_pos_bound (8 - Z.of_nat raw_len mod 8) 8 ltac:(lia)). lia.
Qed.

Lemma rand_off_mod8 : Z.of_nat rand_off mod 8 = 0.
Proof using .
  unfold rand_off, pad_len. rewrite Nat2Z.inj_add, Z2Nat.id by (apply Z.mod_pos_bound; lia).
  set (n := Z.of_nat raw_len).
  pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Hr.
  rewrite <- Zplus_mod_idemp_l.
  destruct (Z.eq_dec (n mod 8) 0) as [E|E].
  - rewrite E. reflexivity.
  - rewrite (Z.mod_small (8 - n mod 8) 8) by lia.
    replace (n mod 8 + (8 - n mod 8)) with 8 by lia. reflexivity.
Qed.

Lemma str_off_mod8 : Z.of_nat str_off mod 8 = 0.
Proof using .
  unfold str_off, aux_off.
  replace (Z.of_nat (24 + 8 * argc + 8 * envc + 160)) with (8 * (23 + Z.of_nat argc + Z.of_nat envc)) by lia.
  rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
Lemma at_random_ptr_eq : at_random_ptr sp argv envp = (sp + nat_to_word rand_off)%bv.
Proof using .
  unfold at_random_ptr, rand_off, pad_len, raw_len, env_str_off, str_off, aux_off, argc, envc.
  rewrite !length_flatten_strings. unfold auxv_size.
  f_equal. f_equal. f_equal.
  - lia.
  - f_equal. f_equal. f_equal. f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Definition hdr_bytes : list byte :=
  word_le8 (len_word argv) ++ flat_map word_le8 argv_ptrs ++ word_le8 (Z_to_bv 64 0).
Definition env_bytes : list byte := flat_map word_le8 envp_ptrs ++ word_le8 (Z_to_bv 64 0).
Definition auxv : list byte := auxv_bytes ph (at_random_ptr sp argv envp) uid hwcap.
Definition rand_bytes : list byte := at_random_bytes (ed_random draw).

Lemma bsb_decomp :
  bsb = hdr_bytes ++ env_bytes ++ auxv ++ flatten_strings argv ++ flatten_strings envp
        ++ repeat (Z_to_bv 8 0) pad_len ++ rand_bytes.
Proof using .
  unfold bsb, build_stack_bytes, hdr_bytes, env_bytes, auxv, rand_bytes, argv_ptrs, envp_ptrs, env_str_base, str_base.
  rewrite length_auxv_bytes.
  replace (8 + (length argv + 1) * 8 + (length envp + 1) * 8 + auxv_size)%nat with str_off
    by (unfold str_off, aux_off, argc, envc, auxv_size; lia).
  destruct (string_addrs (sp + nat_to_word str_off)%bv argv) as [aptrs esb] eqn:Ea.
  cbn [fst snd].
  destruct (string_addrs esb envp) as [eptrs fin] eqn:Ee. cbn [fst snd].
  rewrite <- !app_assoc.
  match goal with |- context [Z.to_nat ((8 - Z.of_nat ?L mod 8) mod 8)] => replace (Z.to_nat ((8 - Z.of_nat L mod 8) mod 8)) with pad_len end.
  { reflexivity. }
  unfold pad_len, raw_len, env_str_off, str_off, aux_off, argc, envc.
  rewrite !length_app, !length_flat_map_le8, !length_word_le8, length_auxv_bytes, !length_flatten_strings.
  pose proof (string_addrs_fst_length (sp + nat_to_word str_off)%bv argv) as L1.
  rewrite Ea in L1. cbn [fst] in L1.
  pose proof (string_addrs_fst_length esb envp) as L2. rewrite Ee in L2. cbn [fst] in L2.
  rewrite L1, L2. unfold auxv_size. do 4 f_equal. lia.
Qed.

Lemma length_hdr_bytes : length hdr_bytes = (16 + 8 * argc)%nat.
Proof using .
  unfold hdr_bytes, argv_ptrs, argc. rewrite !length_app, length_flat_map_le8, !length_word_le8, string_addrs_fst_length. lia.
Qed.

Lemma length_env_bytes : length env_bytes = (8 * envc + 8)%nat.
Proof using .
  unfold env_bytes, envp_ptrs, envc. rewrite length_app, length_flat_map_le8, length_word_le8, string_addrs_fst_length. lia.
Qed.

Lemma length_auxv : length auxv = 160%nat.
Proof using . unfold auxv. apply length_auxv_bytes. Qed.

Lemma length_bsb : length bsb = img_len.
Proof using .
  rewrite bsb_decomp, !length_app, length_hdr_bytes, length_env_bytes, length_auxv,
    !length_flatten_strings, repeat_length.
  unfold img_len, rand_off, raw_len, env_str_off, str_off, aux_off, rand_bytes. rewrite length_at_random_bytes. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nth_error_app_off : forall {A} (l1 l2 : list A) j,
  nth_error (l1 ++ l2) (length l1 + j) = nth_error l2 j.
Proof using . intros A l1 l2 j. rewrite nth_error_app2 by lia. f_equal. lia. Qed.

(* [comment removed for export] *)
Definition region (o : nat) (seg : list byte) : Prop :=
  exists pre post, bsb = pre ++ seg ++ post /\ length pre = o.

Lemma region_nth : forall o seg j, region o seg -> (j < length seg)%nat ->
  nth_error bsb (o + j) = nth_error seg j.
Proof using .
  intros o seg j (pre & post & E & L) Hj. rewrite E, <- L, nth_error_app_off.
  apply nth_error_app1. exact Hj.
Qed.

Lemma region_app_l : forall o l1 l2, region o (l1 ++ l2) -> region o l1.
Proof using .
  intros o l1 l2 (pre & post & E & L). exists pre, (l2 ++ post). rewrite E, <- !app_assoc. auto.
Qed.

Lemma region_app_r : forall o l1 l2, region o (l1 ++ l2) -> region (o + length l1) l2.
Proof using .
  intros o l1 l2 (pre & post & E & L). exists (pre ++ l1), post.
  rewrite E, <- !app_assoc, length_app, L. auto.
Qed.

Lemma region_at : forall pre seg post o,
  bsb = pre ++ seg ++ post -> length pre = o -> region o seg.
Proof using . intros pre seg post o E L. exists pre, post. auto. Qed.

Lemma region_hdr : region 0 hdr_bytes.
Proof using .
  eapply (region_at []); [|reflexivity]. rewrite bsb_decomp. reflexivity.
Qed.

Lemma region_env : region (16 + 8 * argc) env_bytes.
Proof using .
  eapply (region_at hdr_bytes); [rewrite bsb_decomp; reflexivity|]. apply length_hdr_bytes.
Qed.

Lemma region_auxv : region aux_off auxv.
Proof using .
  eapply (region_at (hdr_bytes ++ env_bytes)).
  - rewrite bsb_decomp, <- !app_assoc. reflexivity.
  - rewrite length_app, length_hdr_bytes, length_env_bytes. unfold aux_off. lia.
Qed.

Lemma region_strs : region str_off (flatten_strings argv ++ flatten_strings envp).
Proof using .
  eapply (region_at (hdr_bytes ++ env_bytes ++ auxv) _ (repeat (Z_to_bv 8 0) pad_len ++ rand_bytes)).
  - rewrite bsb_decomp, <- !app_assoc. reflexivity.
  - rewrite !length_app, length_hdr_bytes, length_env_bytes, length_auxv. unfold str_off, aux_off. lia.
Qed.

Lemma region_rand : region rand_off rand_bytes.
Proof using .
  eapply (region_at (hdr_bytes ++ env_bytes ++ auxv ++ flatten_strings argv ++ flatten_strings envp ++ repeat (Z_to_bv 8 0) pad_len) _ []).
  - rewrite bsb_decomp, <- !app_assoc, app_nil_r. reflexivity.
  - rewrite !length_app, length_hdr_bytes, length_env_bytes, length_auxv, !length_flatten_strings, repeat_length.
    unfold rand_off, raw_len, env_str_off, str_off, aux_off. lia.
Qed.

(* [comment removed for export] *)
Lemma flatten_strings_split : forall l k, (k < length l)%nat ->
  exists post, flatten_strings l = flatten_strings (firstn k l) ++ (nth k l [] ++ [Z_to_bv 8 0]) ++ post.
Proof using .
  induction l as [|s l IH]; intros k Hk; [cbn in Hk; lia|].
  destruct k as [|k].
  - exists (flatten_strings l). reflexivity.
  - destruct (IH k ltac:(cbn in Hk; lia)) as (post & E).
    exists post. cbn [firstn nth]. rewrite !flatten_strings_cons, E, <- !app_assoc. reflexivity.
Qed.

Lemma region_argv_str : forall k, (k < argc)%nat ->
  region (str_off + tab (firstn k argv)) (nth k argv [] ++ [Z_to_bv 8 0]).
Proof using .
  intros k Hk. destruct (flatten_strings_split argv k Hk) as (post & E).
  destruct region_strs as (pre & post' & E' & L').
  eapply (region_at (pre ++ flatten_strings (firstn k argv)) _ (post ++ flatten_strings envp ++ post')).
  - rewrite E', E, <- !app_assoc. reflexivity.
  - rewrite length_app, L', length_flatten_strings. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mod_add_inner : forall a b c M, M <> 0 -> ((a + b mod M) + c) mod M = (a + b + c) mod M.
Proof using .
  intros a b c M HM. replace (a + b mod M + c) with (b mod M + (a + c)) by lia.
  rewrite Z.add_mod_idemp_l by exact HM. f_equal. lia.
Qed.

Lemma M64_ne : 2 ^ 64 <> 0.
Proof using . cbv. discriminate. Qed.

Lemma mod_add_outer : forall a c M, M <> 0 -> (a mod M + c) mod M = (a + c) mod M.
Proof using . intros. apply Z.add_mod_idemp_l. assumption. Qed.
Lemma string_addrs_nth : forall base l k, (k < length l)%nat ->
  nth k (fst (string_addrs base l)) (Z_to_bv 64 0)
  = Z_to_bv 64 (bv_unsigned base + Z.of_nat (tab (firstn k l))).
Proof using .
  intros base l. revert base. induction l as [|s l IH]; intros base k Hk; [cbn in Hk; lia|].
  cbn [string_addrs]. specialize (IH (base + len_word s + 1)%bv).
  destruct (string_addrs (base + len_word s + 1)%bv l) as [ptrs fin] eqn:E. cbn [fst].
  destruct k as [|k].
  - cbn. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - cbn [nth firstn tab]. rewrite IH by (cbn in Hk; lia). cbn [fst].
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_add_unsigned. unfold len_word. rewrite Z_to_bv_unsigned.
    change (bv_unsigned 1%bv) with 1.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    repeat ((rewrite mod_add_outer by apply M64_ne) || (rewrite mod_add_inner by apply M64_ne) || rewrite <- Z.add_assoc).
    f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma string_addrs_snd : forall base l,
  snd (string_addrs base l) = Z_to_bv 64 (bv_unsigned base + Z.of_nat (tab l)).
Proof using .
  intros base l. revert base. induction l as [|s l IH]; intros base.
  - cbn. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - cbn [string_addrs tab]. specialize (IH (base + len_word s + 1)%bv).
    destruct (string_addrs (base + len_word s + 1)%bv l) as [ptrs fin]. cbn [snd] in *. rewrite IH.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_add_unsigned. unfold len_word. rewrite Z_to_bv_unsigned.
    change (bv_unsigned 1%bv) with 1.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    repeat ((rewrite mod_add_outer by apply M64_ne) || (rewrite mod_add_inner by apply M64_ne) || rewrite <- Z.add_assoc).
    f_equal. lia.
Qed.

End Layout.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition valid_entry48 (img : Image) (en : ExecEntry) (inp : ProcInput) : Prop :=
  match img, en with
  | mkImage segs _ _, mkEntry sp brk0 mbase _ =>
      valid_sp sp /\ valid_brk segs brk0 /\ valid_mmap_base mbase
      /\ entry_stack_fits sp (in_argv inp) (in_envp inp)
  end.

Lemma valid_entry48_of : forall img en inp,
  in_va_size inp = Sv48 -> valid_entry img en inp -> valid_entry48 img en inp.
Proof.
  intros img en inp Hv H. pose proof (proj1 (valid_entry_sv48 img en inp Hv) H) as H'.
  destruct img, en. exact H'.
Qed.

Lemma valid_entry48_to : forall img en inp,
  in_va_size inp = Sv48 -> valid_entry48 img en inp -> valid_entry img en inp.
Proof.
  intros img en inp Hv H. apply (proj2 (valid_entry_sv48 img en inp Hv)).
  destruct img, en. exact H.
Qed.

Lemma valid_entry48_of_input : forall img en inp,
  valid_input inp -> valid_entry img en inp -> valid_entry48 img en inp.
Proof. intros img en inp Hi. apply valid_entry48_of. exact (valid_input_va_size _ Hi). Qed.

Lemma valid_input_abort_va_size' : forall inp, valid_input_abort inp -> in_va_size inp = Sv48.
Proof. intros inp (_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma valid_input_either_va_size' : forall inp, valid_input_either inp -> in_va_size inp = Sv48.
Proof. intros inp (_ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma valid_entry48_of_input_abort : forall img en inp,
  valid_input_abort inp -> valid_entry img en inp -> valid_entry48 img en inp.
Proof. intros img en inp Hi. apply valid_entry48_of. exact (valid_input_abort_va_size' _ Hi). Qed.

Lemma valid_entry48_of_input_either : forall img en inp,
  valid_input_either inp -> valid_entry img en inp -> valid_entry48 img en inp.
Proof. intros img en inp Hi. apply valid_entry48_of. exact (valid_input_either_va_size' _ Hi). Qed.
