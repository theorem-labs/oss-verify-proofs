(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the entry-stack layout of the new model: the strings after the head, the random bytes and the pad; the launch conjunct in place of the entry-stack fit; written as plain text). *)

From Stdlib Require Import ZArith NArith List Lia Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymObj SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import InitLayout InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

(* argv[1] in the launch image: its pointer (the second word after argc) and its bytes, which start
   right after argv[0]'s in the string block at [str_off].  LPS 727298f3: the image is Lib/InitLayout.v's
   [bsb_decomp] (head, AT_RANDOM's bytes, pad, strings), and the bound that keeps argv[1] below
   [sp_window_hi] comes from the launch conjunct [Hlaunch] (Lib/InitState.v's [LEN_fit]). *)
Section Arg1.
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
Let ARGC := Z.of_nat (length argv).
Let ENVC := Z.of_nat (length envp).
Let STR := Z.of_nat (str_off inp sp draw).
Let RND := Z.of_nat (rand_off inp).
Let PAD := Z.of_nat (pad_len inp sp draw).
Let LEN := Z.of_nat (img_len inp sp draw).
Let argv0 : list byte := nth 0 argv [].
Let argv1 : list byte := nth 1 argv [].
Let ms0 : machine_state := InitState.ms0 segs pc0 ph sp mb draw inp.
Let JI : valuation -> Prop := Jinit segs pc0 ph sp mb draw inp.

Hypothesis Hargc : (2 <= length argv)%nat.

Definition A1 : Z := bv_unsigned sp + STR + Z.of_nat (length argv0) + 1.

Lemma Hsp_hi1 : (bv_unsigned sp <= launch_sp_hi (ed_top draw) inp)%Z.
Proof using Hlaunch. destruct Hlaunch as (_ & (_ & _ & H) & _). exact H. Qed.

Lemma NUMS1 :
  (140735340871680 <= bv_unsigned sp <= 140737488355328)
  /\ STR = RND + 16 + PAD
  /\ (2 <= ARGC <= 1024)
  /\ ENVC <= 256
  /\ Z.of_nat (length argv0) + 1 + Z.of_nat (length argv1) + 1 <= Z.of_nat (tab argv)
  /\ STR + Z.of_nat (tab argv) <= LEN
  /\ LEN < 2 ^ 22
  /\ Z.of_nat (length argv1) <= 131071.
Proof using Hargc Hinp Hlaunch Hsp pc0 ph.
  pose proof (nums pc0 ph sp brk mb draw inp Hsp Hinp Hlaunch) as N.
  pose proof (LEN_bound pc0 ph sp brk mb draw inp Hinp Hlaunch) as HL.
  pose proof (tab_envp_bound inp Hinp) as TE.
  destruct Hinp as ((_ & _ & Hlens & _) & _ & _).
  subst argv0 argv1 ARGC ENVC STR RND PAD LEN argv envp.
  unfold launch_string_bytes in N. rewrite ?length_flatten_strings in N.
  destruct (in_argv inp) as [|a [|b r]] eqn:Ea; [cbn in Hargc; lia | cbn in Hargc; lia |].
  cbn [nth tab length] in *.
  apply Forall_cons_iff in Hlens as [_ Hlens]. apply Forall_cons_iff in Hlens as [Hb _].
  repeat split; try lia.
Qed.

Lemma region_arg1 : region inp mb ph (Z_to_bv 64 (Z.of_N pc0)) sp draw
  (str_off inp sp draw + (length argv0 + 1)) (argv1 ++ [Z_to_bv 8 0]).
Proof using Hargc Hlaunch.
  assert (H1 : (1 < argc inp)%nat) by (unfold argc; unfold argv in Hargc; lia).
  pose proof (region_argv_str inp mb ph (Z_to_bv 64 (Z.of_N pc0)) sp draw Hsp_hi1 1 H1) as R.
  unfold argv0, argv1, argv. destruct (in_argv inp) as [|a r] eqn:Ea; [unfold argc in H1; rewrite Ea in H1; cbn in H1; lia|].
  cbn [firstn tab nth] in R |- *. rewrite Nat.add_0_r in R. exact R.
Qed.

Lemma region_ptrs : region inp mb ph (Z_to_bv 64 (Z.of_N pc0)) sp draw 8
  (flat_map word_le8 (argv_ptrs inp sp draw)).
Proof using Hlaunch.
  pose proof (region_hdr inp mb ph (Z_to_bv 64 (Z.of_N pc0)) sp draw Hsp_hi1) as R. unfold hdr_bytes in R.
  apply (region_app_r _ _ _ _ _ _ Hsp_hi1) in R. apply (region_app_l _ _ _ _ _ _ Hsp_hi1) in R.
  rewrite length_word_le8 in R. exact R.
Qed.

Lemma tab_first1 : Z.of_nat (tab (firstn 1 argv)) = Z.of_nat (length argv0) + 1.
Proof using Hargc.
  unfold argv0. destruct argv as [|a r] eqn:Ea; [exfalso; cbn in Hargc; exact (Nat.nle_succ_0 1 Hargc)|].
  cbn [firstn tab nth]. rewrite Nat.add_0_r, Nat2Z.inj_add. reflexivity.
Qed.

Lemma argv_ptr1 : nth 1 (argv_ptrs inp sp draw) (Z_to_bv 64 0) = Z_to_bv 64 A1.
Proof using Hargc Hinp Hlaunch Hsp pc0 ph LEN PAD RND STR.
  pose proof NUMS1 as N. pose proof tab_first1 as T.
  unfold argv_ptrs. rewrite string_addrs_nth by (unfold argv in Hargc; lia).
  unfold A1. apply bv_eq. rewrite !Z_to_bv_unsigned. f_equal.
  unfold str_base. rewrite bv_add_unsigned. unfold nat_to_word. rewrite Z_to_bv_unsigned.
  unfold argv in T. rewrite T. unfold STR in *.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small (Z.of_nat (str_off inp sp draw))) by lia.
  rewrite Z.mod_small by lia. lia.
Qed.

Variable rho : valuation.
Hypothesis HJ : JI rho.

Lemma arg1_ptr_frame : win_bytes_in_frame rho (bv_unsigned sp) 16 8 (Z_to_bv 64 A1).
Proof using HJ Hargc Hinp Hlaunch Hsp LEN PAD RND STR.
  pose proof NUMS1 as N.
  intros j Hj. rewrite (ji_mem _ _ _ _ _ _ _ _ HJ).
  replace (bv_unsigned sp + 16 + Z.of_nat j) with (bv_unsigned sp + (Z.of_nat 8 + Z.of_nat (8 * 1 + j))) by lia.
  rewrite (ms0_mem_region segs pc0 ph sp brk mb draw inp Hsp Hinp Hlaunch 8 (flat_map word_le8 (argv_ptrs inp sp draw)) (8 * 1 + j) region_ptrs).
  2:{ rewrite length_flat_map_le8. unfold argv_ptrs. rewrite string_addrs_fst_length. unfold argv in Hargc. lia. }
  f_equal. rewrite nth_flat_map_le8; [| unfold argv_ptrs; rewrite string_addrs_fst_length; unfold argv in Hargc; lia | exact Hj].
  rewrite argv_ptr1, word_le8_enc. reflexivity.
Qed.

Lemma arg1_bytes_frame : forall j : nat, (j <= length argv1)%nat ->
  rm rho (Z_to_bv 64 (A1 + Z.of_nat j)) = Some (nth j (argv1 ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)).
Proof using HJ Hargc Hinp Hlaunch Hsp LEN PAD RND STR.
  pose proof NUMS1 as N.
  intros j Hj. rewrite (ji_mem _ _ _ _ _ _ _ _ HJ). unfold A1.
  replace (bv_unsigned sp + STR + Z.of_nat (length argv0) + 1 + Z.of_nat j)
    with (bv_unsigned sp + (Z.of_nat (str_off inp sp draw + (length argv0 + 1)) + Z.of_nat j)) by (unfold STR; lia).
  rewrite (ms0_mem_region segs pc0 ph sp brk mb draw inp Hsp Hinp Hlaunch _ (argv1 ++ [Z_to_bv 8 0]) j region_arg1).
  2:{ rewrite length_app. cbn [length]. lia. }
  reflexivity.
Qed.

Lemma argv1_nonul : ~ In (Z_to_bv 8 0) argv1.
Proof using Hargc Hinp.
  pose proof Hinp as ((_ & _ & _ & Hn & _) & _ & _).
  assert (H2 : (2 <= length (in_argv inp))%nat) by exact Hargc.
  unfold argv1, argv. clear - Hn H2.
  destruct (in_argv inp) as [|a [|b r]]; [cbn in H2; lia | cbn in H2; lia |].
  apply Forall_cons_iff in Hn as [_ Hn]. apply Forall_cons_iff in Hn as [Hb _]. exact Hb.
Qed.

Definition arg1_cstr : cstr_result :=
  if Nat.ltb (length argv1) 4096 then CstrOk argv1 else CstrTooLong.

Lemma arg1_read_cstr_mm : forall (objs : list sobj) (ms : machine_state),
  mem_match segs rho objs ms ->
  Forall (fun o => ranges_disjoint (obj_range rho o) (A1, A1 + Z.of_nat (length argv1) + 1)) objs ->
  read_cstr (ms_read_byte ms) (Z_to_bv 64 A1) = arg1_cstr.
Proof using HJ Hargc Hinp Hlaunch Hsp LEN PAD RND STR.
  pose proof NUMS1 as N.
  intros objs ms Hmm Hdisj. unfold read_cstr, arg1_cstr. change path_max with 4096%nat.
  pose proof (LEN_fit pc0 ph sp brk mb draw inp Hlaunch) as LF. rewrite sp_hi_val in LF.
  apply read_cstr_aux_string; [unfold A1; lia | | | apply argv1_nonul].
  { unfold A1, TASK_SIZE. unfold LEN, STR, argv0, argv1, argv, envp in *. lia. }
  intros j Hj.
  destruct (mem_frame_rd segs rho objs ms (Z_to_bv 64 (A1 + Z.of_nat j)) _ Hmm
             ltac:(eapply ranges_disjoint_outside; [exact Hdisj|]; rewrite Z_to_bv_small; [lia|]; rewrite mod64; unfold A1; lia)
             (arg1_bytes_frame j Hj)) as [_ Hrd].
  exact Hrd.
Qed.

Lemma arg1_read_cstr : forall (S : sstate) (tr : list event) (ms : machine_state) (md : Model),
  smatch segs rho S (tr, mkCfg ms md) ->
  Forall (fun o => ranges_disjoint (obj_range rho o) (A1, A1 + Z.of_nat (length argv1) + 1)) (ss_objs S) ->
  read_cstr (ms_read_byte ms) (Z_to_bv 64 A1) = arg1_cstr.
Proof using HJ Hargc Hinp Hlaunch Hsp LEN PAD RND STR.
  intros S tr ms md Hsm. apply arg1_read_cstr_mm. exact (smatch_mm segs rho S tr ms md Hsm).
Qed.

Lemma arg1_cstr_cases :
  ((4096 <= length argv1)%nat /\ arg1_cstr = CstrTooLong)
  \/ ((length argv1 < 4096)%nat /\ arg1_cstr = CstrOk argv1).
Proof using . unfold arg1_cstr. destruct (Nat.ltb_spec (length argv1) 4096); [right|left]; auto. Qed.

End Arg1.
