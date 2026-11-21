(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the initial-valuation invariant Jinit taking the launch's mmap base; the tail after argv[0] over the new entry-stack layout: argv[1], the envp strings, AT_EXECFN's name and the closing zero bytes, its bounds and bytes from the launch conjunct; tail1_rand dropped, as the random bytes no longer lie in the tail; written as plain text). *)


From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import InitLayout InitState InitStrs InitArg1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

(* The bytes after argv[0] in the launch image, from argv[1]'s address [A1] to the image's end.
   LPS 727298f3: the image is Lib/InitLayout.v's [bsb_decomp]; the strings block at [str_off] is
   Lib/InitStrs.v's [strs_tail] (argv's strings, envp's strings, AT_EXECFN's name, a zero byte and a
   zero word), so with two arguments the tail is argv[1], its zero byte, then the envp strings,
   AT_EXECFN's name and the closing zero bytes.  The random bytes lie below [str_off] (in the head),
   not in the tail. *)
Section Tail1.
Variable segs : list Segment.
Variable pc0 : N.
Variable ph : PhdrInfo.
Variables sp brk mb : word.
Variable draw : EntryDraw.
Variable inp : ProcInput.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hinp : valid_input_either inp.
Hypothesis Hlaunch : entry_launch_ok_va Sv48 (mkEntry sp brk mb draw) inp.
Let argv := in_argv inp.
Let envp := in_envp inp.
Let argv0 : list byte := nth 0 argv [].
Let argv1 : list byte := nth 1 argv [].
Hypothesis Hargc : length argv = 2%nat.

Lemma Hargc2 : (2 <= length argv)%nat. Proof using Hargc. unfold argv in *. lia. Qed.
Let JI : valuation -> Prop := Jinit segs pc0 ph sp mb draw inp.
Let STR := Z.of_nat (str_off inp sp draw).
Let RND := Z.of_nat (rand_off inp).
Let LEN := Z.of_nat (img_len inp sp draw).
Let ENVC := Z.of_nat (length envp).
Let A1 : Z := InitArg1.A1 sp draw inp.

Let N : Z := Z.of_nat (length argv1).
Definition L3 : Z := LEN - (STR + Z.of_nat (length argv0) + 1).

Definition tail1 : list byte := skipn (length argv0 + 1) (strs_tail inp).

Lemma A1_eq : A1 = bv_unsigned sp + STR + Z.of_nat (length argv0) + 1.
Proof using . reflexivity. Qed.

(* The numbers the drivers read, in the new layout (Lib/InitArg1.v's [NUMS1], Lib/InitState.v's [nums],
   [execfn_nums] and [LEN_fit]): the strings start above the random bytes, and the image holds the
   argv and envp strings and AT_EXECFN's name with 9 more bytes before its end, which lies below the
   stack window's top. *)
Lemma NU :
  (140735340871680 <= bv_unsigned sp <= 140737488355328)
  /\ RND + 16 <= STR
  /\ (0 <= ENVC <= 256)
  /\ Z.of_nat (length argv0) + 1 + N + 1 <= Z.of_nat (tab argv)
  /\ STR + Z.of_nat (tab argv) + Z.of_nat (tab envp) + 9 <= LEN
  /\ LEN < 2 ^ 22
  /\ N <= 131071
  /\ Z.of_nat (length argv0) <= 131071
  /\ bv_unsigned sp mod 16 = 0
  /\ bv_unsigned sp + LEN <= 140737488355328.
Proof using Hargc Hinp Hlaunch Hsp pc0 ph.
  pose proof (NUMS1 pc0 ph sp brk mb draw inp Hsp Hinp Hlaunch Hargc2) as N1.
  pose proof (nums pc0 ph sp brk mb draw inp Hsp Hinp Hlaunch) as N2.
  pose proof (execfn_nums pc0 ph sp brk mb draw inp Hsp Hinp Hlaunch) as (_ & EX).
  pose proof (LEN_fit pc0 ph sp brk mb draw inp Hlaunch) as LF.
  cbv zeta in N1, N2, EX, LF. rewrite sp_hi_val in LF.
  unfold STR, RND, LEN, ENVC, N, argv0, argv1, argv, envp in *. lia.
Qed.

Lemma length_tail1 : Z.of_nat (length tail1) = L3.
Proof using Hargc Hinp Hlaunch Hsp pc0 ph.
  unfold tail1, L3. rewrite length_skipn.
  pose proof (length_tail pc0 ph sp brk mb draw inp Hsp Hinp Hlaunch) as LT. pose proof NU as NU'.
  cbv zeta in LT.
  unfold LEN, STR, RND, ENVC, N, argv0, argv1, argv, envp in *. lia.
Qed.

(* LPS 727298f3: after argv[1] and its zero byte the tail holds the envp strings, AT_EXECFN's name,
   a zero byte and a zero word: at least 9 bytes (it was the pad and the 16 random bytes). *)
Lemma L3_ge : N + 10 <= L3 /\ L3 < 2 ^ 22.
Proof using Hargc Hinp Hlaunch Hsp pc0 ph. pose proof NU as NU'. unfold L3. lia. Qed.

Lemma tail1_nth : forall j : nat,
  nth j tail1 (Z_to_bv 8 0) = nth (j + (length argv0 + 1)) (strs_tail inp) (Z_to_bv 8 0).
Proof using . intros j. unfold tail1. rewrite nth_skipn. f_equal; apply Nat.add_comm. Qed.

Lemma region_tail1 : region inp mb ph (Z_to_bv 64 (Z.of_N pc0)) sp draw
  (str_off inp sp draw + (length argv0 + 1)) tail1.
Proof using Hargc Hinp Hlaunch Hsp pc0 ph.
  assert (HH : (bv_unsigned sp <= launch_sp_hi (ed_top draw) inp)%Z)
    by (destruct Hlaunch as (_ & (_ & _ & H) & _); exact H).
  pose proof (region_tail pc0 ph sp brk mb draw inp Hlaunch) as R.
  rewrite <- (firstn_skipn (length argv0 + 1) (strs_tail inp)) in R.
  apply (region_app_r _ _ _ _ _ _ HH) in R. rewrite length_firstn in R.
  pose proof (length_tail pc0 ph sp brk mb draw inp Hsp Hinp Hlaunch) as LT. pose proof NU as NU'.
  cbv zeta in LT.
  replace (Nat.min (length argv0 + 1) (length (strs_tail inp))) with (length argv0 + 1)%nat in R.
  2:{ unfold LEN, STR, RND, ENVC, N, argv0, argv1, argv, envp in *. lia. }
  exact R.
Qed.

Lemma tail1_split : exists rest, tail1 = (argv1 ++ [Z_to_bv 8 0]) ++ rest.
Proof using Hargc.
  unfold tail1, strs_tail, argv0, argv1, argv. cbv beta zeta. unfold argv in Hargc. clear - Hargc.
  assert (E : exists a0 a1, in_argv inp = [a0; a1]).
  { destruct (in_argv inp) as [|a0 [|a1 [|z l]]]; cbn in Hargc; try lia. exists a0, a1. reflexivity. }
  destruct E as (a0 & a1 & E). rewrite E. cbn [nth].
  rewrite !flatten_strings_cons. cbn [flatten_strings]. eexists.
  rewrite <- !app_assoc. rewrite skipn_app. rewrite skipn_all2 by lia.
  replace (length a0 + 1 - length a0)%nat with 1%nat by lia. cbn [skipn app]. rewrite ?app_nil_l. reflexivity.
Qed.

Lemma tail1_head : forall j : nat, (j <= length argv1)%nat ->
  nth j tail1 (Z_to_bv 8 0) = nth j (argv1 ++ [Z_to_bv 8 0]) (Z_to_bv 8 0).
Proof using Hargc.
  intros j Hj. destruct tail1_split as [rest ->]. clear - Hj. apply app_nth1. rewrite length_app. cbn [length]. lia.
Qed.

Lemma tail1_firstn : firstn (length argv1) tail1 = argv1.
Proof using Hargc.
  destruct tail1_split as [rest ->]. rewrite <- app_assoc, firstn_app, Nat.sub_diag, firstn_all.
  cbn [firstn]. apply app_nil_r.
Qed.

Lemma tail1_nul : nth (length argv1) tail1 (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof using Hargc.
  rewrite tail1_head by apply Nat.le_refl. rewrite app_nth2 by apply Nat.le_refl.
  rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma argv1_nonul : forall j : nat, (j < length argv1)%nat -> nth j tail1 (Z_to_bv 8 0) <> Z_to_bv 8 0.
Proof using Hargc Hinp.
  intros j Hj. rewrite tail1_head by (clear - Hj; lia). rewrite app_nth1 by (clear - Hj; lia). intros E.
  apply (InitArg1.argv1_nonul inp Hinp Hargc2). fold argv argv1. rewrite <- E. apply nth_In. exact Hj.
Qed.

Lemma tail1_frame : forall rho : valuation, JI rho ->
  forall j : nat, (j < length tail1)%nat ->
  rm rho (Z_to_bv 64 (A1 + Z.of_nat j)) = Some (nth j tail1 (Z_to_bv 8 0)).
Proof using Hargc Hinp Hlaunch Hsp pc0 ph segs.
  intros rho HJ j Hj. rewrite (ji_mem _ _ _ _ _ _ _ _ HJ). rewrite A1_eq.
  pose proof NU as NU'.
  replace (bv_unsigned sp + STR + Z.of_nat (length argv0) + 1 + Z.of_nat j)
    with (bv_unsigned sp + (Z.of_nat (str_off inp sp draw + (length argv0 + 1)) + Z.of_nat j)) by (unfold STR; lia).
  exact (ms0_mem_region segs pc0 ph sp brk mb draw inp Hsp Hinp Hlaunch _ tail1 j region_tail1 Hj).
Qed.

Lemma tail1_ms0 : forall j : nat, (j < length tail1)%nat ->
  ms_mem (InitState.ms0 segs pc0 ph sp mb draw inp) (Z_to_bv 64 (A1 + Z.of_nat j))
  = Some (nth j tail1 (Z_to_bv 8 0)).
Proof using Hargc Hinp Hlaunch Hsp pc0 ph segs.
  intros j Hj. rewrite A1_eq.
  pose proof NU as NU'.
  replace (bv_unsigned sp + STR + Z.of_nat (length argv0) + 1 + Z.of_nat j)
    with (bv_unsigned sp + (Z.of_nat (str_off inp sp draw + (length argv0 + 1)) + Z.of_nat j)) by (unfold STR; lia).
  exact (ms0_mem_region segs pc0 ph sp brk mb draw inp Hsp Hinp Hlaunch _ tail1 j region_tail1 Hj).
Qed.
End Tail1.
