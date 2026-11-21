(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase StackLayout State Run.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PropExec CatExec SeqExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma total_arg_bytes_nat_split : forall k (l : list (list byte)), (k < length l)%nat ->
  (total_arg_bytes_nat (firstn k l) + length (nth k l []) + 1 <= total_arg_bytes_nat l)%nat.
Proof.
  induction k as [|k IH]; intros l Hk.
  - destruct l as [|s rest]; [cbn in Hk; lia|]. cbn [firstn nth]. rewrite total_arg_bytes_cons.
    change (total_arg_bytes_nat []) with 0%nat. lia.
  - destruct l as [|s rest]; [cbn in Hk; lia|]. cbn [firstn nth]. rewrite !total_arg_bytes_cons.
    cbn in Hk. specialize (IH rest ltac:(lia)). lia.
Qed.

(* port727 (): the argv strings now sit at the TOP of the entry block, under the launch's stack top
   (ed_top draw), so their bound below TASK_SIZE comes from the launch (entry_launch_ok_va: the top is at most
   va_stack_top Sv48 = TASK_SIZE) and Common/CatExec's launch_string_base_arith, as Common/SeqExec's argv_ptr_bounds
   does. r30q2's cat_struct_size_span / argv_str_within_span (the old layout's span; their one user was this lemma)
   are gone with that layout. *)
Lemma argv_str_below_task_size : forall inp mbase (sp brk : word) draw k,
  entry_launch_ok_va Sv48 (mkEntry sp brk mbase draw) inp ->
  (k < length (in_argv inp))%nat ->
  bv_unsigned (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) k)
  + Z.of_nat (length (nth k (in_argv inp) [])) + 1 <= TASK_SIZE.
Proof.
  intros inp mbase sp brk draw k Hlaunch Hk.
  assert (Htop : bv_unsigned (ed_top draw) <= TASK_SIZE).
  { pose proof Hlaunch as HL. cbn [entry_launch_ok_va] in HL. destruct HL as ((_ & Ht & _) & _).
    exact Ht. }
  pose proof (launch_string_base_arith Sv48 inp mbase sp brk draw Hlaunch) as HA.
  pose proof (u_cat_string_base Sv48 inp mbase sp brk draw Hlaunch) as Hu.
  pose proof (u64_range sp). pose proof (u64_range (ed_top draw)).
  pose proof (Nat2Z.is_nonneg (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))).
  pose proof (Nat2Z.is_nonneg (total_arg_bytes_nat (firstn k (in_argv inp)))).
  assert (Hstr : Z.of_nat (total_arg_bytes_nat (firstn k (in_argv inp)))
                 + Z.of_nat (length (nth k (in_argv inp) [])) + 1
                 <= Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))).
  { pose proof (total_arg_bytes_firstn_within (in_argv inp) k Hk) as Hw.
    unfold launch_string_bytes. rewrite length_flatten_strings.
    pose proof (Nat2Z.is_nonneg (length (flatten_strings (in_envp inp)))).
    pose proof (Nat2Z.is_nonneg (length (in_execfn inp))).
    lia. }
  rewrite (cat_argv_ptr_offset _ _ _ _ k Hk), word_add_nat_Z2bv, Hu.
  rewrite u_Z2bv_lt by lia.
  lia.
Qed.
