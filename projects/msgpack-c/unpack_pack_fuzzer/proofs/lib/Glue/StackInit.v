(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith NArith Bool List Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics StackLayout Fs State Monad Specs Run.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Z_to_bv : simpl never.

Module SI.

Fixpoint total_nat (args : list (list byte)) : nat :=
  match args with [] => 0%nat | a :: args' => (length a + 1 + total_nat args')%nat end.

Lemma total_arg_bytes_nat : forall l, total_arg_bytes l = Z.of_nat (total_nat l).
Proof.
  induction l as [|x l IH]; [reflexivity|].
  cbv [total_arg_bytes] in *. cbn [fold_right total_nat]. rewrite IH. lia.
Qed.

Lemma length_flatten_strings : forall l, length (flatten_strings l) = total_nat l.
Proof.
  induction l as [|x l IH]; [reflexivity|].
  unfold flatten_strings in *. cbn [flat_map total_nat]. rewrite !length_app, IH. cbn [length]. lia.
Qed.

Lemma length_word_le8 : forall w, length (word_le8 w) = 8%nat.
Proof. reflexivity. Qed.

Lemma length_flat_map_le8 : forall l, length (flat_map word_le8 l) = (8 * length l)%nat.
Proof. induction l as [|x l IH]; [reflexivity|]. cbn [flat_map]. rewrite length_app, IH, length_word_le8. cbn [length]. lia. Qed.

Lemma u64_range : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range _ w). unfold bv_modulus in H. exact H. Qed.

Lemma Z_to_bv64_unsigned : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz. Qed.

Lemma nat_to_word_add : forall (a : word) (n : nat),
  bv_unsigned a + Z.of_nat n < 2 ^ 64 -> bv_unsigned (a + nat_to_word n)%bv = bv_unsigned a + Z.of_nat n.
Proof.
  intros a n H. unfold nat_to_word. rewrite bv_add_unsigned, Z_to_bv_unsigned.
  pose proof (u64_range a).
  rewrite (bv_wrap_small 64 (Z.of_nat n)) by (unfold bv_modulus; lia).
  apply bv_wrap_small. unfold bv_modulus. lia.
Qed.

Lemma word_add_0 : forall a : word, (a + nat_to_word 0)%bv = a.
Proof. intros a. apply bv_add_0_r. reflexivity. Qed.

Lemma nat_to_word_merge : forall m k : nat, (nat_to_word m + nat_to_word k)%bv = nat_to_word (m + k).
Proof.
  intros m k. apply bv_eq. unfold nat_to_word.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned, bv_wrap_add_idemp. f_equal. lia.
Qed.

Lemma nat_to_word_add_merge : forall (a : word) (m k : nat),
  (a + nat_to_word m + nat_to_word k)%bv = (a + nat_to_word (m + k))%bv.
Proof.
  intros a m k. rewrite <- nat_to_word_merge. apply bv_eq.
  rewrite !bv_add_unsigned. rewrite bv_wrap_add_idemp_l, bv_wrap_add_idemp_r. f_equal. lia.
Qed.

Lemma len_word_nat : forall (s : list byte), len_word s = nat_to_word (length s).
Proof. reflexivity. Qed.
Lemma word1_nat : (1%bv : word) = nat_to_word 1.
Proof. apply bv_eq. reflexivity. Qed.

Lemma string_addrs_pair : forall strs (base : word),
  string_addrs base strs = (fst (string_addrs base strs), (base + nat_to_word (total_nat strs))%bv).
Proof.
  induction strs as [|s rest IH]; intro base.
  - cbn. rewrite word_add_0. reflexivity.
  - cbn [string_addrs]. rewrite (IH (base + len_word s + 1)%bv). cbn [fst]. f_equal.
    rewrite len_word_nat, word1_nat, !nat_to_word_add_merge. cbn [total_nat]. f_equal. f_equal. lia.
Qed.

Lemma string_addrs_fst : forall strs (base : word),
  fst (string_addrs base strs) =
  match strs with [] => [] | s :: rest => base :: fst (string_addrs (base + len_word s + 1)%bv rest) end.
Proof.
  intros strs base. destruct strs as [|s rest]; [reflexivity|]. cbn [string_addrs].
  destruct (string_addrs (base + len_word s + 1)%bv rest); reflexivity.
Qed.

Lemma length_string_addrs_fst : forall strs (base : word), length (fst (string_addrs base strs)) = length strs.
Proof.
  induction strs as [|s rest IH]; intro base; [reflexivity|].
  rewrite string_addrs_fst. cbn [length]. rewrite IH. reflexivity.
Qed.

Lemma word_le8_nth : forall (w : word) (i : nat) d, (i < 8)%nat ->
  nth i (word_le8 w) d = Z_to_bv 8 (Z.shiftr (bv_unsigned w) (8 * Z.of_nat i)).
Proof.
  intros w i d Hi.
  do 8 (destruct i as [|i]; [reflexivity|]). lia.
Qed.

Lemma flat_map_le8_nth : forall (l : list word) k i d dw, (k < length l)%nat -> (i < 8)%nat ->
  nth (8 * k + i) (flat_map word_le8 l) d = nth i (word_le8 (nth k l dw)) d.
Proof.
  induction l as [|w l IH]; intros k i d dw Hk Hi; cbn [length] in Hk; [lia|].
  cbn [flat_map]. destruct k as [|k].
  - cbn [nth Nat.mul Nat.add]. rewrite app_nth1 by (rewrite length_word_le8; lia). reflexivity.
  - rewrite app_nth2 by (rewrite length_word_le8; lia). rewrite length_word_le8.
    replace (8 * S k + i - 8)%nat with (8 * k + i)%nat by lia. cbn [nth]. apply IH; lia.
Qed.

Section Entry.
Variables (segs : list Segment) (pc : N) (ph : PhdrInfo) (sp : word) (argv envp : list (list byte)) (uid hwcap : word) (draw : EntryDraw).

Definition nargc : nat := length argv.
Definition nenvc : nat := length envp.
Definition sstruct : nat := (8 + (nargc + 1) * 8 + (nenvc + 1) * 8 + 160)%nat.
Definition str_base : word := (sp + nat_to_word sstruct)%bv.
Definition argv_ptrs : list word := fst (string_addrs str_base argv).
Definition env_str_base : word := (str_base + nat_to_word (total_nat argv))%bv.
Definition envp_ptrs : list word := fst (string_addrs env_str_base envp).
Definition ARND : word := at_random_ptr sp argv envp.
Definition AUXV : list byte := auxv_bytes ph ARND uid hwcap.
Definition raw_len : nat := (sstruct + total_nat argv + total_nat envp)%nat.
Definition pad : nat := Z.to_nat ((8 - Z.of_nat raw_len mod 8) mod 8).
Definition BSB : list byte := build_stack_bytes ph sp argv envp uid hwcap draw.
Definition IMG : list byte := entry_stack_image ph sp argv envp uid hwcap draw.
Definition mem0 : word -> option byte := ms_mem (init_machine_state segs pc ph sp draw argv envp uid hwcap).
Definition SP : Z := bv_unsigned sp.

Definition auxws : list word :=
  [ Z_to_bv 64 3; Z_to_bv 64 (Z.of_N (ph_addr ph)); Z_to_bv 64 4; Z_to_bv 64 (Z.of_N (ph_ent ph));
    Z_to_bv 64 5; Z_to_bv 64 (Z.of_N (ph_num ph)); Z_to_bv 64 16; hwcap; Z_to_bv 64 6; Z_to_bv 64 4096;
    Z_to_bv 64 11; uid; Z_to_bv 64 12; uid; Z_to_bv 64 23; Z_to_bv 64 0; Z_to_bv 64 25; ARND;
    Z_to_bv 64 0; Z_to_bv 64 0 ].

Lemma AUXV_eq : AUXV = flat_map word_le8 auxws.
Proof. reflexivity. Qed.

Lemma length_AUXV : length AUXV = 160%nat.
Proof. unfold AUXV. apply length_auxv_bytes. Qed.

Theorem BSB_eq : BSB = word_le8 (len_word argv) ++ flat_map word_le8 argv_ptrs ++ word_le8 (Z_to_bv 64 0)
   ++ flat_map word_le8 envp_ptrs ++ word_le8 (Z_to_bv 64 0) ++ AUXV ++ flatten_strings argv ++ flatten_strings envp
   ++ repeat (Z_to_bv 8 0) pad ++ at_random_bytes (ed_random draw).
Proof.
  unfold BSB, build_stack_bytes. rewrite length_auxv_bytes.
  rewrite (string_addrs_pair argv). cbv beta iota. rewrite (string_addrs_pair envp). cbv beta iota zeta.
  rewrite <- !app_assoc.
  unfold pad, raw_len, AUXV, envp_ptrs, env_str_base, argv_ptrs, str_base, sstruct, nargc, nenvc, auxv_size.
  rewrite !length_app, !length_flat_map_le8, !length_string_addrs_fst, !length_word_le8, length_auxv_bytes, !length_flatten_strings.
  unfold auxv_size.
  repeat (f_equal; try reflexivity; try lia).
Qed.

Lemma length_argv_ptrs : length argv_ptrs = nargc.
Proof. unfold argv_ptrs. apply length_string_addrs_fst. Qed.
Lemma length_envp_ptrs : length envp_ptrs = nenvc.
Proof. unfold envp_ptrs. apply length_string_addrs_fst. Qed.

Lemma length_BSB : length BSB = (raw_len + pad + 16)%nat.
Proof.
  rewrite BSB_eq. rewrite !length_app, !length_flat_map_le8, !length_word_le8, length_AUXV, !length_flatten_strings,
    repeat_length, length_at_random_bytes, length_argv_ptrs, length_envp_ptrs.
  unfold raw_len, sstruct. lia.
Qed.

Lemma pad_lt8 : (pad < 8)%nat.
Proof. unfold pad. pose proof (Z.mod_pos_bound (8 - Z.of_nat raw_len mod 8) 8 ltac:(lia)). lia. Qed.

Lemma ARND_eq : ARND = (sp + nat_to_word (raw_len + pad))%bv.
Proof.
  unfold ARND, at_random_ptr, pad, raw_len, sstruct, nargc, nenvc. rewrite !length_flatten_strings. unfold auxv_size. reflexivity.
Qed.

Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hfit : entry_stack_fits sp argv envp.

Lemma SP_lo : 0x7fff80000000 <= SP.
Proof. unfold SP. destruct Hsp as [H _]. unfold sp_window_lo in H. exact H. Qed.

Lemma BSB_span : Z.of_nat (length BSB) <= entry_stack_span argv envp.
Proof.
  rewrite length_BSB. unfold entry_stack_span, raw_len, sstruct, nargc, nenvc, auxv_size.
  rewrite !total_arg_bytes_nat. pose proof pad_lt8. lia.
Qed.

Lemma BSB_top : SP + Z.of_nat (length BSB) <= 0x800000000000.
Proof. pose proof BSB_span. unfold entry_stack_fits, sp_window_hi in Hfit. unfold SP. lia. Qed.

Lemma IMG_eq : IMG = BSB ++ entry_slack sp BSB (ed_slack draw).
Proof. reflexivity. Qed.

Lemma mem0_unfold : forall addr, mem0 addr =
  match stack_to_mem sp IMG addr with
  | Some b => Some b
  | None => if (Z.leb (SP - stack_max_size) (bv_unsigned addr) && Z.ltb (bv_unsigned addr) SP)%bool then Some (Z_to_bv 8 0) else None
  end.
Proof. reflexivity. Qed.

Lemma mem0_block : forall (k : nat) b, nth_error BSB k = Some b -> mem0 (Z_to_bv 64 (SP + Z.of_nat k)) = Some b.
Proof.
  intros k b Hk.
  assert (Hlt : (k < length BSB)%nat) by (apply nth_error_Some; congruence).
  pose proof BSB_top as Htop. pose proof SP_lo as Hlo.
  rewrite mem0_unfold. unfold stack_to_mem. rewrite Z_to_bv64_unsigned by lia. fold SP.
  replace (SP <=? SP + Z.of_nat k) with true by (symmetry; apply Z.leb_le; lia).
  replace (SP + Z.of_nat k - SP) with (Z.of_nat k) by lia.
  assert (Hlen : (length BSB <= length IMG)%nat) by (rewrite IMG_eq, length_app; lia).
  replace (Z.of_nat k <? Z.of_nat (length IMG)) with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite Nat2Z.id, IMG_eq, nth_error_app1 by exact Hlt. rewrite Hk. reflexivity.
Qed.

Lemma mem0_below : forall a, SP - stack_max_size <= a < SP -> mem0 (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
Proof.
  intros a Ha. pose proof SP_lo as Hlo. pose proof (u64_range sp) as Hu. rewrite mem0_unfold. unfold SP, stack_max_size, stack_to_mem in *.
  rewrite Z_to_bv64_unsigned by lia.
  replace (bv_unsigned sp <=? a) with false by (symmetry; apply Z.leb_gt; lia).
  replace (bv_unsigned sp - 8 * 1024 * 1024 <=? a) with true by (symmetry; apply Z.leb_le; lia).
  replace (a <? bv_unsigned sp) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma mem0_none_low : forall a, 0 <= a < SP - stack_max_size -> mem0 (Z_to_bv 64 a) = None.
Proof.
  intros a Ha. pose proof SP_lo as Hlo. pose proof (u64_range sp) as Hu. rewrite mem0_unfold. unfold SP, stack_max_size, stack_to_mem in *.
  rewrite Z_to_bv64_unsigned by lia.
  replace (bv_unsigned sp <=? a) with false by (symmetry; apply Z.leb_gt; lia).
  replace (bv_unsigned sp - 8 * 1024 * 1024 <=? a) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
Qed.

Lemma mem0_piece : forall pre mid post (i : nat),
  BSB = pre ++ mid ++ post -> (i < length mid)%nat ->
  mem0 (Z_to_bv 64 (SP + Z.of_nat (length pre) + Z.of_nat i)) = Some (nth i mid (Z_to_bv 8 0)).
Proof.
  intros pre mid post i HB Hi.
  replace (SP + Z.of_nat (length pre) + Z.of_nat i) with (SP + Z.of_nat (length pre + i)) by lia.
  apply mem0_block. rewrite HB. rewrite nth_error_app2 by lia.
  replace (length pre + i - length pre)%nat with i by lia.
  rewrite nth_error_app1 by exact Hi. apply nth_error_nth'. exact Hi.
Qed.

Definition argcZ : Z := Z.of_nat nargc.
Definition envcZ : Z := Z.of_nat nenvc.

Lemma argc_range : 1 <= argcZ <= 1024.
Proof. unfold argcZ, nargc. destruct Hva as [H _]. exact H. Qed.
Lemma envc_range : 0 <= envcZ <= 256.
Proof. unfold envcZ, nenvc. destruct Hve as [H _]. lia. Qed.

Definition word_at (A : Z) (w : word) : Prop :=
  forall i : nat, (i < 8)%nat -> mem0 (Z_to_bv 64 (A + Z.of_nat i)) = Some (nth i (word_le8 w) (Z_to_bv 8 0)).

Lemma word_at_piece : forall pre w post,
  BSB = pre ++ word_le8 w ++ post -> word_at (SP + Z.of_nat (length pre)) w.
Proof. intros pre w post HB i Hi. apply (mem0_piece pre (word_le8 w) post i HB). rewrite length_word_le8. exact Hi. Qed.

Lemma words_at_piece : forall pre (l : list word) post k d,
  BSB = pre ++ flat_map word_le8 l ++ post -> (k < length l)%nat ->
  word_at (SP + Z.of_nat (length pre) + 8 * Z.of_nat k) (nth k l d).
Proof.
  intros pre l post k d HB Hk i Hi.
  replace (SP + Z.of_nat (length pre) + 8 * Z.of_nat k + Z.of_nat i) with (SP + Z.of_nat (length pre) + Z.of_nat (8 * k + i)) by lia.
  rewrite (mem0_piece pre (flat_map word_le8 l) post (8 * k + i) HB) by (rewrite length_flat_map_le8; lia).
  f_equal. apply flat_map_le8_nth; assumption.
Qed.

Lemma argc_word : word_at SP (len_word argv).
Proof.
  replace SP with (SP + Z.of_nat (@length byte [])) by (cbn; lia).
  eapply (word_at_piece []). rewrite BSB_eq. reflexivity.
Qed.

Lemma len_word_argv : bv_unsigned (len_word argv) = argcZ.
Proof. unfold len_word, argcZ, nargc. apply Z_to_bv64_unsigned. pose proof argc_range. unfold argcZ, nargc in *. lia. Qed.

Lemma argv_ptr_word : forall k, (k < nargc)%nat -> word_at (SP + 8 + 8 * Z.of_nat k) (nth k argv_ptrs (Z_to_bv 64 0)).
Proof.
  intros k Hk.
  replace (SP + 8) with (SP + Z.of_nat (length (word_le8 (len_word argv)))) by (rewrite length_word_le8; lia).
  eapply words_at_piece; [|rewrite length_argv_ptrs; exact Hk].
  rewrite BSB_eq. reflexivity.
Qed.

Lemma argv_cons : exists a0 rest, argv = a0 :: rest.
Proof.
  pose proof argc_range as H. unfold argcZ, nargc in H. clear -H.
  destruct argv as [|a0 rest]; [cbn in H; lia | exists a0, rest; reflexivity].
Qed.

Lemma argv_ptr0 : forall a0 rest, argv = a0 :: rest -> nth 0 argv_ptrs (Z_to_bv 64 0) = str_base.
Proof.
  intros a0 rest Ha. unfold argv_ptrs. rewrite string_addrs_fst. rewrite Ha. reflexivity.
Qed.

Lemma str_base_val : bv_unsigned str_base = SP + Z.of_nat sstruct.
Proof.
  unfold str_base. apply nat_to_word_add. pose proof BSB_top. rewrite length_BSB in H. unfold raw_len in H. fold SP. lia.
Qed.

Definition envp_off : Z := 16 + 8 * argcZ.

Lemma envp_block : BSB = (word_le8 (len_word argv) ++ flat_map word_le8 argv_ptrs ++ word_le8 (Z_to_bv 64 0))
                         ++ (flat_map word_le8 envp_ptrs ++ word_le8 (Z_to_bv 64 0))
                         ++ (AUXV ++ flatten_strings argv ++ flatten_strings envp ++ repeat (Z_to_bv 8 0) pad ++ at_random_bytes (ed_random draw)).
Proof. rewrite BSB_eq. repeat rewrite app_assoc. reflexivity. Qed.

Lemma envp_off_eq : Z.of_nat (length (word_le8 (len_word argv) ++ flat_map word_le8 argv_ptrs ++ word_le8 (Z_to_bv 64 0))) = envp_off.
Proof. rewrite !length_app, !length_word_le8, length_flat_map_le8, length_argv_ptrs. unfold envp_off, argcZ. lia. Qed.

Definition envp_img : list byte := flat_map word_le8 envp_ptrs ++ word_le8 (Z_to_bv 64 0).

Lemma length_envp_img : length envp_img = Z.to_nat (8 * envcZ + 8).
Proof. unfold envp_img. rewrite length_app, length_flat_map_le8, length_word_le8, length_envp_ptrs. unfold envcZ. lia. Qed.

Lemma envp_img_byte : forall i : nat, (i < length envp_img)%nat ->
  mem0 (Z_to_bv 64 (SP + envp_off + Z.of_nat i)) = Some (nth i envp_img (Z_to_bv 8 0)).
Proof.
  intros i Hi. rewrite <- envp_off_eq. apply (mem0_piece _ envp_img _ i envp_block Hi).
Qed.

Lemma env_str_base_val : bv_unsigned env_str_base = SP + Z.of_nat sstruct + Z.of_nat (total_nat argv).
Proof.
  unfold env_str_base. rewrite nat_to_word_add; rewrite str_base_val; [reflexivity|].
  pose proof BSB_top. rewrite length_BSB in H. unfold raw_len in H. fold SP. lia.
Qed.

Lemma envp_ptr_val : forall k, (k < nenvc)%nat ->
  SP < bv_unsigned (nth k envp_ptrs (Z_to_bv 64 0)) < 2 ^ 64.
Proof.
  assert (G : forall strs (base : word) k, (k < length strs)%nat ->
            bv_unsigned base + Z.of_nat (total_nat strs) < 2 ^ 64 ->
            bv_unsigned base <= bv_unsigned (nth k (fst (string_addrs base strs)) (Z_to_bv 64 0)) < 2 ^ 64).
  { induction strs as [|s rest IH]; intros base k Hk Hnw; cbn [length] in Hk; [lia|].
    rewrite string_addrs_fst. destruct k as [|k].
    - cbn [nth]. pose proof (u64_range base). lia.
    - cbn [nth]. cbn [total_nat] in Hnw.
      assert (Hb : bv_unsigned (base + len_word s + 1)%bv = bv_unsigned base + Z.of_nat (length s) + 1).
      { rewrite len_word_nat, word1_nat, nat_to_word_add_merge. rewrite nat_to_word_add; [lia|]. lia. }
      specialize (IH (base + len_word s + 1)%bv k ltac:(lia)). rewrite Hb in IH. lia. }
  intros k Hk. unfold envp_ptrs.
  pose proof BSB_top as Htop. rewrite length_BSB in Htop. unfold raw_len in Htop.
  pose proof env_str_base_val as Hev.
  specialize (G envp env_str_base k Hk ltac:(rewrite Hev; fold SP; lia)). rewrite Hev in G.
  unfold sstruct in G. lia.
Qed.

Definition auxv_off : Z := 24 + 8 * argcZ + 8 * envcZ.

Lemma auxv_block : BSB = (word_le8 (len_word argv) ++ flat_map word_le8 argv_ptrs ++ word_le8 (Z_to_bv 64 0)
                          ++ flat_map word_le8 envp_ptrs ++ word_le8 (Z_to_bv 64 0))
                         ++ flat_map word_le8 auxws
                         ++ (flatten_strings argv ++ flatten_strings envp ++ repeat (Z_to_bv 8 0) pad ++ at_random_bytes (ed_random draw)).
Proof. rewrite BSB_eq, AUXV_eq. repeat rewrite app_assoc. reflexivity. Qed.

Lemma auxv_word : forall j, (j < 20)%nat -> word_at (SP + auxv_off + 8 * Z.of_nat j) (nth j auxws (Z_to_bv 64 0)).
Proof.
  intros j Hj.
  replace (SP + auxv_off) with (SP + Z.of_nat (length (word_le8 (len_word argv) ++ flat_map word_le8 argv_ptrs ++ word_le8 (Z_to_bv 64 0)
                          ++ flat_map word_le8 envp_ptrs ++ word_le8 (Z_to_bv 64 0)))).
  2:{ rewrite !length_app, !length_word_le8, !length_flat_map_le8, length_argv_ptrs, length_envp_ptrs. unfold auxv_off, argcZ, envcZ. lia. }
  eapply words_at_piece; [exact auxv_block|]. cbn. lia.
Qed.

Lemma ARND_val : bv_unsigned ARND = SP + Z.of_nat (raw_len + pad).
Proof.
  rewrite ARND_eq. apply nat_to_word_add. pose proof BSB_top. rewrite length_BSB in H. fold SP. lia.
Qed.

Lemma argv0_block : forall a0 rest, argv = a0 :: rest ->
  BSB = (word_le8 (len_word argv) ++ flat_map word_le8 argv_ptrs ++ word_le8 (Z_to_bv 64 0)
         ++ flat_map word_le8 envp_ptrs ++ word_le8 (Z_to_bv 64 0) ++ AUXV)
        ++ (a0 ++ [Z_to_bv 8 0])
        ++ (flatten_strings rest ++ flatten_strings envp ++ repeat (Z_to_bv 8 0) pad ++ at_random_bytes (ed_random draw)).
Proof.
  intros a0 rest Ha. rewrite BSB_eq.
  replace (flatten_strings argv) with ((a0 ++ [Z_to_bv 8 0]) ++ flatten_strings rest)
    by (rewrite Ha; unfold flatten_strings; cbn [flat_map]; reflexivity).
  repeat rewrite app_assoc. reflexivity.
Qed.

Lemma argv0_byte : forall a0 rest (i : nat), argv = a0 :: rest -> (i <= length a0)%nat ->
  mem0 (Z_to_bv 64 (SP + Z.of_nat sstruct + Z.of_nat i)) = Some (nth i (a0 ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)).
Proof.
  intros a0 rest i Ha Hi.
  replace (SP + Z.of_nat sstruct) with (SP + Z.of_nat (length (word_le8 (len_word argv) ++ flat_map word_le8 argv_ptrs ++ word_le8 (Z_to_bv 64 0)
         ++ flat_map word_le8 envp_ptrs ++ word_le8 (Z_to_bv 64 0) ++ AUXV))).
  2:{ rewrite !length_app, !length_word_le8, !length_flat_map_le8, length_argv_ptrs, length_envp_ptrs, length_AUXV. unfold sstruct. lia. }
  apply (mem0_piece _ (a0 ++ [Z_to_bv 8 0]) _ i (argv0_block a0 rest Ha)). rewrite length_app. cbn [length]. lia.
Qed.

Lemma argv_null_block : BSB = (word_le8 (len_word argv) ++ flat_map word_le8 argv_ptrs) ++ word_le8 (Z_to_bv 64 0)
        ++ (flat_map word_le8 envp_ptrs ++ word_le8 (Z_to_bv 64 0) ++ AUXV ++ flatten_strings argv ++ flatten_strings envp
            ++ repeat (Z_to_bv 8 0) pad ++ at_random_bytes (ed_random draw)).
Proof. rewrite BSB_eq. repeat rewrite app_assoc. reflexivity. Qed.

Lemma argv_null_word : word_at (SP + 8 + 8 * argcZ) (Z_to_bv 64 0).
Proof.
  replace (SP + 8 + 8 * argcZ) with (SP + Z.of_nat (length (word_le8 (len_word argv) ++ flat_map word_le8 argv_ptrs))).
  2:{ rewrite length_app, length_word_le8, length_flat_map_le8, length_argv_ptrs. unfold argcZ. lia. }
  exact (word_at_piece _ _ _ argv_null_block).
Qed.

Lemma argv_ptr1 : forall a0 a1 rest, argv = a0 :: a1 :: rest ->
  nth 1 argv_ptrs (Z_to_bv 64 0) = (str_base + len_word a0 + 1)%bv.
Proof.
  intros a0 a1 rest Ha. unfold argv_ptrs. rewrite Ha. cbn [string_addrs].
  destruct (string_addrs (str_base + len_word a0 + 1 + len_word a1 + 1)%bv rest). reflexivity.
Qed.

Lemma argv_ptr1_val : forall a0 a1 rest, argv = a0 :: a1 :: rest ->
  bv_unsigned (nth 1 argv_ptrs (Z_to_bv 64 0)) = SP + Z.of_nat sstruct + Z.of_nat (length a0) + 1.
Proof.
  intros a0 a1 rest Ha. rewrite (argv_ptr1 a0 a1 rest Ha). rewrite len_word_nat, word1_nat, nat_to_word_add_merge.
  pose proof BSB_top as HT. rewrite length_BSB in HT. unfold raw_len in HT.
  assert (HA : (length a0 + 1 <= total_nat argv)%nat) by (rewrite Ha; cbn [total_nat]; lia).
  rewrite nat_to_word_add; rewrite str_base_val; [lia|]. fold SP. lia.
Qed.

Lemma argv1_block : forall a0 a1 rest, argv = a0 :: a1 :: rest ->
  BSB = (word_le8 (len_word argv) ++ flat_map word_le8 argv_ptrs ++ word_le8 (Z_to_bv 64 0)
         ++ flat_map word_le8 envp_ptrs ++ word_le8 (Z_to_bv 64 0) ++ AUXV ++ (a0 ++ [Z_to_bv 8 0]))
        ++ (a1 ++ [Z_to_bv 8 0])
        ++ (flatten_strings rest ++ flatten_strings envp ++ repeat (Z_to_bv 8 0) pad ++ at_random_bytes (ed_random draw)).
Proof.
  intros a0 a1 rest Ha. rewrite BSB_eq.
  replace (flatten_strings argv) with ((a0 ++ [Z_to_bv 8 0]) ++ (a1 ++ [Z_to_bv 8 0]) ++ flatten_strings rest)
    by (rewrite Ha; unfold flatten_strings; cbn [flat_map]; repeat rewrite app_assoc; reflexivity).
  repeat rewrite app_assoc. reflexivity.
Qed.

Lemma argv1_byte : forall a0 a1 rest (i : nat), argv = a0 :: a1 :: rest -> (i <= length a1)%nat ->
  mem0 (Z_to_bv 64 (SP + Z.of_nat sstruct + Z.of_nat (length a0) + 1 + Z.of_nat i)) = Some (nth i (a1 ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)).
Proof.
  intros a0 a1 rest i Ha Hi.
  replace (SP + Z.of_nat sstruct + Z.of_nat (length a0) + 1) with (SP + Z.of_nat (length (word_le8 (len_word argv) ++ flat_map word_le8 argv_ptrs ++ word_le8 (Z_to_bv 64 0)
         ++ flat_map word_le8 envp_ptrs ++ word_le8 (Z_to_bv 64 0) ++ AUXV ++ (a0 ++ [Z_to_bv 8 0])))).
  2:{ rewrite !length_app, !length_word_le8, !length_flat_map_le8, length_argv_ptrs, length_envp_ptrs, length_AUXV. cbn [length]. unfold sstruct. lia. }
  apply (mem0_piece _ (a1 ++ [Z_to_bv 8 0]) _ i (argv1_block a0 a1 rest Ha)). rewrite length_app. cbn [length]. lia.
Qed.

Lemma random_block :
  BSB = (word_le8 (len_word argv) ++ flat_map word_le8 argv_ptrs ++ word_le8 (Z_to_bv 64 0)
         ++ flat_map word_le8 envp_ptrs ++ word_le8 (Z_to_bv 64 0) ++ AUXV ++ flatten_strings argv ++ flatten_strings envp ++ repeat (Z_to_bv 8 0) pad)
        ++ at_random_bytes (ed_random draw) ++ [].
Proof. rewrite BSB_eq, app_nil_r. repeat rewrite app_assoc. reflexivity. Qed.

Lemma random_byte : forall i : nat, (i < 16)%nat ->
  mem0 (Z_to_bv 64 (SP + Z.of_nat (raw_len + pad) + Z.of_nat i)) = Some (nth i (at_random_bytes (ed_random draw)) (Z_to_bv 8 0)).
Proof.
  intros i Hi.
  replace (SP + Z.of_nat (raw_len + pad)) with (SP + Z.of_nat (length (word_le8 (len_word argv) ++ flat_map word_le8 argv_ptrs ++ word_le8 (Z_to_bv 64 0)
         ++ flat_map word_le8 envp_ptrs ++ word_le8 (Z_to_bv 64 0) ++ AUXV ++ flatten_strings argv ++ flatten_strings envp ++ repeat (Z_to_bv 8 0) pad))).
  2:{ rewrite !length_app, !length_word_le8, !length_flat_map_le8, length_argv_ptrs, length_envp_ptrs, length_AUXV, !length_flatten_strings, repeat_length.
      unfold raw_len, sstruct. lia. }
  apply (mem0_piece _ (at_random_bytes (ed_random draw)) [] i random_block). rewrite length_at_random_bytes. exact Hi.
Qed.

Lemma ARND_aligned : bv_unsigned ARND mod 8 = 0 <-> SP mod 8 = 0.
Proof.
  rewrite ARND_val. unfold pad. set (r := Z.of_nat raw_len).
  pose proof (Z.mod_pos_bound r 8 ltac:(lia)) as Hr. pose proof (Z.div_mod r 8 ltac:(lia)) as Hd.
  assert (Hq : exists q, Z.of_nat (raw_len + Z.to_nat ((8 - r mod 8) mod 8)) = 8 * q).
  { destruct (Z.eq_dec (r mod 8) 0) as [E|E].
    - exists (r / 8). rewrite E. change ((8 - 0) mod 8) with 0. rewrite Nat.add_0_r. lia.
    - exists (r / 8 + 1). rewrite (Z.mod_small (8 - r mod 8)) by lia. rewrite Nat2Z.inj_add, Z2Nat.id by lia. lia. }
  destruct Hq as [q Hq]. rewrite Hq. replace (SP + 8 * q) with (SP + q * 8) by lia. rewrite Z_mod_plus_full. reflexivity.
Qed.

Definition strarea : list byte := flatten_strings argv ++ flatten_strings envp ++ repeat (Z_to_bv 8 0) pad.
Lemma length_strarea : length strarea = (total_nat argv + total_nat envp + pad)%nat.
Proof. unfold strarea. rewrite !length_app, !length_flatten_strings, repeat_length. lia. Qed.
Lemma strarea_block :
  BSB = (word_le8 (len_word argv) ++ flat_map word_le8 argv_ptrs ++ word_le8 (Z_to_bv 64 0)
         ++ flat_map word_le8 envp_ptrs ++ word_le8 (Z_to_bv 64 0) ++ AUXV)
        ++ strarea ++ at_random_bytes (ed_random draw).
Proof. rewrite BSB_eq. unfold strarea. repeat rewrite app_assoc. reflexivity. Qed.
Lemma strarea_byte : forall i : nat, (i < length strarea)%nat ->
  mem0 (Z_to_bv 64 (SP + Z.of_nat sstruct + Z.of_nat i)) = Some (nth i strarea (Z_to_bv 8 0)).
Proof.
  intros i Hi.
  replace (SP + Z.of_nat sstruct) with (SP + Z.of_nat (length (word_le8 (len_word argv) ++ flat_map word_le8 argv_ptrs ++ word_le8 (Z_to_bv 64 0)
         ++ flat_map word_le8 envp_ptrs ++ word_le8 (Z_to_bv 64 0) ++ AUXV))).
  2:{ rewrite !length_app, !length_word_le8, !length_flat_map_le8, length_argv_ptrs, length_envp_ptrs, length_AUXV. unfold sstruct. lia. }
  apply (mem0_piece _ strarea _ i strarea_block). exact Hi.
Qed.
Lemma strarea_len8 : Z.of_nat (length strarea) mod 8 = 0.
Proof.
  rewrite length_strarea. unfold pad, raw_len, sstruct.
  set (t := (total_nat argv + total_nat envp)%nat).
  set (r := (8 + (nargc + 1) * 8 + (nenvc + 1) * 8 + 160 + total_nat argv + total_nat envp)%nat).
  assert (Er : Z.of_nat r = Z.of_nat t + 8 * (Z.of_nat nargc + Z.of_nat nenvc + 23)) by (subst r t; lia).
  pose proof (Z.mod_pos_bound (Z.of_nat r) 8 ltac:(lia)) as H1.
  pose proof (Z.mod_pos_bound (8 - Z.of_nat r mod 8) 8 ltac:(lia)) as H2.
  rewrite Nat2Z.inj_add, Z2Nat.id by lia.
  assert (M : Z.of_nat r mod 8 = Z.of_nat t mod 8).
  { rewrite Er. replace (Z.of_nat t + 8 * (Z.of_nat nargc + Z.of_nat nenvc + 23)) with (Z.of_nat t + (Z.of_nat nargc + Z.of_nat nenvc + 23) * 8) by lia.
    apply Z.mod_add. lia. }
  rewrite M in *. pose proof (Z.div_mod (Z.of_nat t) 8 ltac:(lia)) as D.
  destruct (Z.eq_dec (Z.of_nat t mod 8) 0) as [Z0|NZ].
  - rewrite Z0. change ((8 - 0) mod 8) with 0. rewrite Z.add_0_r. rewrite Z0 in D. replace (Z.of_nat t) with (8 * (Z.of_nat t / 8)) by lia. rewrite Z.mul_comm. apply Z_mod_mult.
  - rewrite (Z.mod_small (8 - Z.of_nat t mod 8)) by lia.
    replace (Z.of_nat t + (8 - Z.of_nat t mod 8)) with ((Z.of_nat t / 8 + 1) * 8) by lia. apply Z_mod_mult.
Qed.

End Entry.

End SI.
