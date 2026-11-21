(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the entry-stack layout of the new model: the random bytes at the head's end, the pad, then the strings; the launch conjunct in place of the entry-stack fit; the offsets and the image taking the stack pointer, the draw and the mmap base; main's argument tails L3 and L2U ending nine bytes past the exec file name's address, its offset EXo read off the launch; written as plain text). *)

From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import InitLayout InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts Init.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma skipn_app_exact : forall {A} (l1 l2 : list A), skipn (length l1) (l1 ++ l2) = l2.
Proof. intros A l1 l2. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity. Qed.

Lemma nth_firstn_lt : forall {A} (l : list A) n j d, (j < n)%nat -> nth j (firstn n l) d = nth j l d.
Proof.
  intros A l. induction l as [|x l IH]; intros n j d Hj; [destruct n; reflexivity|].
  destruct n as [|n]; [lia|]. destruct j as [|j]; [reflexivity|]. cbn. apply IH. lia.
Qed.

Lemma firstn_app_exact : forall {A} (l1 l2 : list A), firstn (length l1) (l1 ++ l2) = l1.
Proof. intros A l1 l2. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn. apply app_nil_r. Qed.

Lemma nth_error_skipn' : forall {A} (l : list A) n j, nth_error (skipn n l) j = nth_error l (n + j).
Proof. intros A l n j. rewrite nth_error_skipn. reflexivity. Qed.

Lemma flat_map_le8_nth : forall (l : list word) (k j : nat) (d : byte) (d' : word),
  (k < length l)%nat -> (j < 8)%nat ->
  nth (8 * k + j) (flat_map word_le8 l) d = nth j (word_le8 (nth k l d')) d.
Proof.
  induction l as [|w l IH]; intros k j d d' Hk Hj; [cbn in Hk; lia|].
  cbn [flat_map nth]. destruct k as [|k].
  - rewrite app_nth1 by (rewrite length_word_le8; lia). replace (8 * 0 + j)%nat with j by lia. reflexivity.
  - rewrite app_nth2 by (rewrite length_word_le8; lia). rewrite length_word_le8.
    replace (8 * S k + j - 8)%nat with (8 * k + j)%nat by lia. apply IH; [cbn in Hk; lia | exact Hj].
Qed.

(* LPS 727298f3 (Lib/InitLayout.v [bsb_decomp]): the launch image is the head (argc, argv, envp, auxv,
   the parity gap, then AT_RANDOM's 16 bytes at [rand_off]), [arch_align_stack]'s pad, the strings from
   [str_off], the exec file name, and the 8-byte slot below [ed_top].  The strings now lie ABOVE the
   random bytes, and [str_off] / [img_len] read the stack pointer and the draw (the pad does), so the
   offsets and the image take them; [Hent]'s fifth conjunct (the launch) bounds the image. *)
Section ArgBytes.
Variables sp brk mb : word.
Variable draw : EntryDraw.
Variable inp : ProcInput.
Hypothesis Hent : valid_entry48 imgA (mkEntry sp brk mb draw) inp.
Hypothesis Hinp : valid_input_either inp.

Definition argv0 : list byte := nth 0 (in_argv inp) [].
Definition argv1 : list byte := nth 1 (in_argv inp) [].
Definition ARGC : Z := Z.of_nat (length (in_argv inp)).

Definition STRo : Z := Z.of_nat (str_off inp sp draw).
Definition A1o : Z := STRo + (Z.of_nat (length argv0) + 1).
Definition RNDo : Z := Z.of_nat (rand_off inp).
Definition LEN : Z := Z.of_nat (img_len inp sp draw).
Definition BSB : list byte := bsb inp mb phA (Z_to_bv 64 (Z.of_N pcA)) sp draw.
(* LPS 727298f3 (Lib/InitState.v [execfn_nums]): the argv and envp strings end at the exec file
   name's address, [sp + EXo] (AT_EXECFN, launch variable 13); the name, its NUL and the 8-byte
   slot follow up to the image's end, so [END9] (the nine bytes past that address: the name's
   bytes or its NUL, then the slot) still lies in the image.  Main's argument tails end there. *)
Definition EXo : Z := STRo + Z.of_nat (tab (in_argv inp)) + Z.of_nat (tab (in_envp inp)).
Definition END9 : Z := EXo + 9.

Definition RND16 : list byte := word_le8 (rnd0 draw) ++ word_le8 (rnd1 draw).

Definition L3 : list byte := firstn (Z.to_nat (END9 - A1o)) (skipn (Z.to_nat A1o) BSB).
Definition L2U : list byte := firstn (Z.to_nat (END9 - STRo)) (skipn (Z.to_nat STRo) BSB).
Definition ms0A : machine_state := ms0 segsA pcA phA sp mb draw inp.

Lemma Hsp : valid_sp sp. Proof. destruct Hent as (H & _). exact H. Qed.
Lemma Hlaunch : entry_launch_ok_va Sv48 (mkEntry sp brk mb draw) inp.
Proof. destruct Hent as (_ & _ & _ & _ & H). exact H. Qed.
Lemma Hsp_hi : (bv_unsigned sp <= launch_sp_hi (ed_top draw) inp)%Z.
Proof. destruct Hlaunch as (_ & (_ & _ & H) & _). exact H. Qed.
Lemma Hfit : bv_unsigned sp + LEN <= sp_window_hi.
Proof. unfold LEN. exact (LEN_fit pcA phA sp brk mb draw inp Hlaunch). Qed.

(* The numbers of the new layout (Lib/InitState.v [nums]), in the positions of the old ones: the
   fifth is [STRo = RNDo + 16 + pad] (was [184 + 8 ARGC + 8 ENVC]), the sixth the page-aligned image
   end (was [STRo mod 8 = 0], which no longer holds), the ninth [RNDo] from the head (was after the
   strings), the tenth the pad's bound 4110 (was 8), the twelfth [LEN] from the strings (was
   [RNDo + 16]) and the thirteenth [Lib/InitState.v]'s [LEN_bound] (was 2238671). *)
Lemma arg_nums :
  140735340871680 <= bv_unsigned sp
  /\ bv_unsigned sp + LEN <= 2 ^ 47
  /\ bv_unsigned sp mod 16 = 0
  /\ (1 <= ARGC /\ ARGC <= 1024)
  /\ STRo = RNDo + 16 + Z.of_nat (pad_len inp sp draw)
  /\ (bv_unsigned sp + LEN) mod 4096 = 0
  /\ A1o = STRo + Z.of_nat (length argv0) + 1
  /\ A1o <= STRo + Z.of_nat (tab (in_argv inp))
  /\ RNDo = 8 * ARGC + 8 * Z.of_nat (length (in_envp inp)) + 24
            + Z.of_nat (auxv_size (kb_rseq (in_kernel inp)))
            + 8 * Z.of_nat (Nat.modulo (block_items (in_argv inp) (in_envp inp)) 2)
  /\ Z.of_nat (pad_len inp sp draw) <= 4110
  /\ RNDo mod 8 = 0
  /\ LEN = STRo + Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp)) + 8
  /\ LEN <= 4194304 - 16
  /\ Z.of_nat (length argv0) <= 131071
  /\ Z.of_nat (tab (in_argv inp)) <= 2097152
  /\ Z.of_nat (tab (in_envp inp)) <= 131072.
Proof.
  pose proof (nums pcA phA sp brk mb draw inp Hsp Hinp Hlaunch) as N. cbv zeta in N.
  destruct N as (Nsp & N16 & Nargc & Nenvc & Nstr & Nlen0 & Nlen0b & Nrnd & Npad & Ntab1 & Ntab2 & Nlen & Nrm8 & Ntop).
  pose proof (LEN_fit pcA phA sp brk mb draw inp Hlaunch) as LF. cbv zeta in LF. rewrite sp_hi_val in LF.
  pose proof (LEN_bound pcA phA sp brk mb draw inp Hinp Hlaunch) as LB. cbv zeta in LB.
  unfold LEN, RNDo, A1o, STRo, ARGC, argv0. repeat split; lia.
Qed.

(* The strings (argv's first among them) are part of [launch_string_bytes]. *)
Lemma tab_le_lsb : Z.of_nat (tab (in_argv inp)) + 1
  <= Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp)).
Proof. unfold launch_string_bytes. rewrite !length_flatten_strings. lia. Qed.

Lemma length_BSB : Z.of_nat (length BSB) = LEN.
Proof. unfold BSB, LEN. rewrite (length_bsb inp mb phA (Z_to_bv 64 (Z.of_N pcA)) sp draw Hsp_hi). reflexivity. Qed.

Lemma BSB_byte : forall off, 0 <= off < LEN ->
  ms_mem ms0A (Z_to_bv 64 (bv_unsigned sp + off)) = Some (nth (Z.to_nat off) BSB (Z_to_bv 8 0)).
Proof.
  intros off Hoff. unfold ms0A. rewrite (ms0_mem_img segsA pcA phA sp brk mb draw inp Hsp Hinp Hlaunch off Hoff). fold BSB.
  apply nth_error_nth'. pose proof length_BSB. lia.
Qed.

(* LPS 727298f3: the exec file name's address is [sp + EXo], AT_EXECFN's value, and the nine bytes
   past it lie in the image (Lib/InitState.v [execfn_nums], proved at the launch). *)
Lemma EXo_nums : bv_unsigned (at_execfn_ptr (ed_top draw) (in_execfn inp)) = bv_unsigned sp + EXo
  /\ END9 <= LEN.
Proof.
  pose proof (execfn_nums pcA phA sp brk mb draw inp Hsp Hinp Hlaunch) as (EX & EXb). cbv zeta in EX, EXb.
  unfold END9, EXo, STRo, LEN. split; lia.
Qed.

(* argv[0], its NUL and (with two or more arguments) argv[1] and its NUL lie below the name. *)
Lemma argv0_tail : A1o <= EXo.
Proof. pose proof arg_nums as AN. pose proof (Zle_0_nat (tab (in_envp inp))). unfold EXo. lia. Qed.
Lemma argv1_tail : 2 <= ARGC -> A1o + Z.of_nat (length argv1) + 1 <= EXo.
Proof.
  intros H2. pose proof (Zle_0_nat (tab (in_envp inp))).
  unfold ARGC, A1o, EXo, argv0, argv1 in *. destruct (in_argv inp) as [|a0 [|a1 r]]; cbn in H2; try lia.
  cbn [nth tab]. pose proof (Zle_0_nat (tab r)). lia.
Qed.

Lemma length_L3 : Z.of_nat (length L3) = END9 - A1o.
Proof.
  unfold L3. rewrite length_firstn, length_skipn. pose proof length_BSB. pose proof arg_nums. pose proof EXo_nums as [_ E9].
  pose proof argv0_tail. unfold END9 in *. lia.
Qed.
Lemma length_L2U : Z.of_nat (length L2U) = END9 - STRo.
Proof.
  unfold L2U. rewrite length_firstn, length_skipn. pose proof length_BSB. pose proof arg_nums. pose proof EXo_nums as [_ E9].
  pose proof argv0_tail. unfold END9 in *. lia.
Qed.

Lemma L3_byte : forall j : nat, (j < length L3)%nat ->
  ms_mem ms0A (Z_to_bv 64 (bv_unsigned sp + A1o + Z.of_nat j)) = Some (nth j L3 (Z_to_bv 8 0)).
Proof.
  intros j Hj. pose proof length_L3. pose proof arg_nums. pose proof EXo_nums as [_ E9]. pose proof argv0_tail.
  replace (bv_unsigned sp + A1o + Z.of_nat j) with (bv_unsigned sp + (A1o + Z.of_nat j)) by lia.
  rewrite BSB_byte by (unfold END9 in *; lia). f_equal. unfold L3. rewrite nth_firstn_lt by lia. rewrite nth_skipn. f_equal. lia.
Qed.
Lemma L2U_byte : forall j : nat, (j < length L2U)%nat ->
  ms_mem ms0A (Z_to_bv 64 (bv_unsigned sp + STRo + Z.of_nat j)) = Some (nth j L2U (Z_to_bv 8 0)).
Proof.
  intros j Hj. pose proof length_L2U. pose proof arg_nums. pose proof EXo_nums as [_ E9]. pose proof argv0_tail.
  replace (bv_unsigned sp + STRo + Z.of_nat j) with (bv_unsigned sp + (STRo + Z.of_nat j)) by lia.
  rewrite BSB_byte by (unfold END9 in *; lia). f_equal. unfold L2U. rewrite nth_firstn_lt by lia. rewrite nth_skipn. f_equal. lia.
Qed.

Lemma region_skipn : forall (o : nat) (seg : list byte),
  region inp mb phA (Z_to_bv 64 (Z.of_N pcA)) sp draw o seg -> firstn (length seg) (skipn o BSB) = seg.
Proof.
  intros o seg (pre & post & E & L). unfold BSB. rewrite E, <- L, skipn_app_exact. apply firstn_app_exact.
Qed.

Lemma L2U_head : firstn (length argv0 + 1) L2U = argv0 ++ [Z_to_bv 8 0].
Proof.
  pose proof arg_nums as AN. pose proof argv0_tail as T0.
  pose proof (region_argv_str inp mb phA (Z_to_bv 64 (Z.of_N pcA)) sp draw Hsp_hi 0 ltac:(unfold InitLayout.argc; unfold ARGC in AN; lia)) as R.
  cbn [firstn tab] in R. rewrite Nat.add_0_r in R. fold argv0 in R.
  replace (length argv0 + 1)%nat with (length (argv0 ++ [Z_to_bv 8 0])) by (rewrite length_app; cbn; lia).
  unfold L2U. rewrite firstn_firstn.
  replace (Nat.min (length (argv0 ++ [Z_to_bv 8 0])) (Z.to_nat (END9 - STRo))) with (length (argv0 ++ [Z_to_bv 8 0]))
    by (rewrite length_app; cbn [length]; unfold END9, A1o in *; lia).
  unfold STRo. rewrite Nat2Z.id. exact (region_skipn _ _ R).
Qed.

Lemma L3_head : 2 <= ARGC -> firstn (length argv1 + 1) L3 = argv1 ++ [Z_to_bv 8 0].
Proof.
  intros H2. pose proof arg_nums as AN. pose proof (argv1_tail H2) as T1.
  pose proof (region_argv_str inp mb phA (Z_to_bv 64 (Z.of_N pcA)) sp draw Hsp_hi 1 ltac:(unfold InitLayout.argc; unfold ARGC in H2; lia)) as R.
  fold argv1 in R.
  assert (E : (str_off inp sp draw + tab (firstn 1 (in_argv inp)))%nat = Z.to_nat A1o).
  { unfold A1o, STRo, argv0. unfold ARGC in H2. destruct (in_argv inp) as [|a0 l0]; [cbn in H2; lia|]. cbn [firstn tab nth]. rewrite Nat.add_0_r. lia. }
  rewrite E in R.
  replace (length argv1 + 1)%nat with (length (argv1 ++ [Z_to_bv 8 0])) by (rewrite length_app; cbn; lia).
  unfold L3. rewrite firstn_firstn.
  replace (Nat.min (length (argv1 ++ [Z_to_bv 8 0])) (Z.to_nat (END9 - A1o))) with (length (argv1 ++ [Z_to_bv 8 0]))
    by (rewrite length_app; cbn [length]; unfold END9 in *; lia).
  exact (region_skipn _ _ R).
Qed.

Lemma length_RND16 : length RND16 = 16%nat.
Proof. unfold RND16. rewrite length_app, !length_word_le8. reflexivity. Qed.

Lemma BSB_rand : forall j : nat, (j < 16)%nat ->
  nth (Z.to_nat RNDo + j) BSB (Z_to_bv 8 0) = nth j RND16 (Z_to_bv 8 0).
Proof.
  intros j Hj. destruct (region_rand inp mb phA (Z_to_bv 64 (Z.of_N pcA)) sp draw Hsp_hi) as (pre & post & E & L).
  unfold BSB. rewrite E. unfold RNDo. rewrite Nat2Z.id, <- L.
  rewrite app_nth2 by lia. rewrite Nat.add_comm, Nat.add_sub.
  assert (ER : rand_bytes draw = RND16).
  { unfold rand_bytes, RND16, rnd0, rnd1. rewrite at_random_bytes_words. cbn [flat_map]. rewrite app_nil_r. reflexivity. }
  rewrite app_nth1 by (rewrite ER, length_RND16; lia). rewrite ER. reflexivity.
Qed.

Lemma RND16_cell0 : forall j : nat, (j < 8)%nat ->
  nth j RND16 (Z_to_bv 8 0) = nth j (word_le8 (rnd0 draw)) (Z_to_bv 8 0).
Proof. intros j Hj. unfold RND16. rewrite app_nth1 by (rewrite length_word_le8; lia). reflexivity. Qed.
Lemma RND16_cell1 : forall j : nat, (8 <= j /\ j < 16)%nat ->
  nth j RND16 (Z_to_bv 8 0) = nth (j - 8) (word_le8 (rnd1 draw)) (Z_to_bv 8 0).
Proof. intros j Hj. unfold RND16. rewrite app_nth2 by (rewrite length_word_le8; lia). rewrite length_word_le8. reflexivity. Qed.

(* argv[1]'s pointer, the second word after argc: [Lib/InitArg1.v]'s route over the head's region. *)
Lemma region_ptrs : region inp mb phA (Z_to_bv 64 (Z.of_N pcA)) sp draw 8 (flat_map word_le8 (argv_ptrs inp sp draw)).
Proof.
  pose proof (region_hdr inp mb phA (Z_to_bv 64 (Z.of_N pcA)) sp draw Hsp_hi) as R. unfold hdr_bytes in R.
  apply (region_app_r _ _ _ _ _ _ Hsp_hi) in R. apply (region_app_l _ _ _ _ _ _ Hsp_hi) in R.
  rewrite length_word_le8 in R. exact R.
Qed.

Lemma argv_ptr1 : 2 <= ARGC -> nth 1 (argv_ptrs inp sp draw) (Z_to_bv 64 0) = Z_to_bv 64 (bv_unsigned sp + A1o).
Proof.
  intros H2. pose proof arg_nums as AN. pose proof tab_le_lsb. unfold ARGC in H2.
  assert (T1 : Z.of_nat (tab (firstn 1 (in_argv inp))) = Z.of_nat (length argv0) + 1).
  { unfold argv0. destruct (in_argv inp) as [|a0 l0]; [cbn in H2; lia|]. change (tab (firstn 1 (a0 :: l0))) with (length a0 + 1 + 0)%nat. cbn [nth]. lia. }
  unfold argv_ptrs. rewrite string_addrs_nth by lia.
  apply bv_eq. rewrite !Z_to_bv_unsigned. f_equal.
  unfold str_base. rewrite bv_add_unsigned. unfold nat_to_word. rewrite Z_to_bv_unsigned.
  rewrite T1. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  unfold A1o, STRo, LEN in *. pose proof (Zle_0_nat (str_off inp sp draw)).
  rewrite (Z.mod_small (Z.of_nat (str_off inp sp draw))) by lia.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma a1p_word : 2 <= ARGC -> forall j : nat, (j < 8)%nat ->
  ms_mem ms0A (Z_to_bv 64 (bv_unsigned sp + 16 + Z.of_nat j))
  = Some (nth j (word_le8 (Z_to_bv 64 (bv_unsigned sp + A1o))) (Z_to_bv 8 0)).
Proof.
  intros H2 j Hj.
  assert (LP : length (argv_ptrs inp sp draw) = length (in_argv inp)) by (unfold argv_ptrs; apply string_addrs_fst_length).
  replace (bv_unsigned sp + 16 + Z.of_nat j) with (bv_unsigned sp + (Z.of_nat 8 + Z.of_nat (8 * 1 + j))) by lia.
  unfold ms0A. rewrite (ms0_mem_region segsA pcA phA sp brk mb draw inp Hsp Hinp Hlaunch 8 (flat_map word_le8 (argv_ptrs inp sp draw)) (8 * 1 + j) region_ptrs).
  2:{ rewrite length_flat_map_le8, LP. unfold ARGC in H2. lia. }
  f_equal. rewrite (flat_map_le8_nth _ 1 j (Z_to_bv 8 0) (Z_to_bv 64 0)); [| rewrite LP; unfold ARGC in H2; lia | exact Hj].
  rewrite (argv_ptr1 H2). reflexivity.
Qed.

Lemma A1o_eq : forall rho, Jinit segsA pcA phA sp mb draw inp rho ->
  bv_unsigned (rw rho 4) + bv_unsigned (rw rho 5) + 1 = bv_unsigned sp + A1o
  /\ bv_unsigned (rw rho 6) = bv_unsigned sp + RNDo
  /\ bv_unsigned (rw rho 1) = bv_unsigned sp
  /\ bv_unsigned (rw rho 2) = ARGC
  /\ rw rho 9 = rnd0 draw /\ rw rho 10 = rnd1 draw.
Proof.
  intros rho HJ. pose proof arg_nums as AN. pose proof tab_le_lsb.
  rewrite (ji_sp _ _ _ _ _ _ _ _ HJ), (ji_argv0 _ _ _ _ _ _ _ _ HJ), (ji_len0 _ _ _ _ _ _ _ _ HJ), (ji_rand _ _ _ _ _ _ _ _ HJ), (ji_argc _ _ _ _ _ _ _ _ HJ),
          (ji_rnd0 _ _ _ _ _ _ _ _ HJ), (ji_rnd1 _ _ _ _ _ _ _ _ HJ).
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  pose proof (Zle_0_nat (tab (in_argv inp))). pose proof (Zle_0_nat (pad_len inp sp draw)).
  pose proof (Zle_0_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))).
  unfold A1o, STRo, RNDo, LEN, ARGC, argv0 in *.
  rewrite !Z.mod_small by lia. repeat split; try lia; reflexivity.
Qed.
End ArgBytes.
