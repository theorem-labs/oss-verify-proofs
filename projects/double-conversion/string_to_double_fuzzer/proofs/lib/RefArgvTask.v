(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's validity hypotheses; the new initial stack layout). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec RefLayout.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Lemma total_arg_bytes_firstn_S : forall k (l : list (list byte)), (k < length l)%nat ->
  (total_arg_bytes_nat (firstn (S k) l) = total_arg_bytes_nat (firstn k l) + (length (nth k l []) + 1))%nat.
Proof.
  induction k as [|k IH]; intros l Hk.
  - destruct l as [|s r]; [cbn in Hk; lia|]. change (firstn 1 (s :: r)) with [s]. change (firstn 0 (s :: r)) with (@nil (list byte)).
    change (nth 0 (s :: r) []) with s. rewrite total_arg_bytes_cons. change (total_arg_bytes_nat []) with 0%nat. lia.
  - destruct l as [|s r]; [cbn in Hk; lia|]. cbn in Hk.
    change (firstn (S (S k)) (s :: r)) with (s :: firstn (S k) r). change (firstn (S k) (s :: r)) with (s :: firstn k r).
    change (nth (S k) (s :: r) []) with (nth k r []). rewrite !total_arg_bytes_cons. rewrite (IH r) by lia. lia.
Qed.

(* 08b1429: the argv strings end eight bytes below the stack VMA's top ed_top, which the launch keeps
   at or below Sv48's STACK_TOP (valid_stack_top_va), so every argv string ends below TASK_SIZE. *)
Lemma cat_argv_ptr_task : forall inp mbase (sp brk : word) draw (k : nat),
  entry_launch_ok_va Sv48 (mkEntry sp brk mbase draw) inp ->
  (k < length (in_argv inp))%nat ->
  (bv_unsigned (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) k)
   + Z.of_nat (length (nth k (in_argv inp) [])) + 1 <= 0x800000000000)%Z.
Proof.
  intros inp mbase sp brk draw k Hlau Hk.
  pose proof (u_cat_string_base Sv48 inp mbase sp brk draw Hlau) as Hb.
  pose proof (launch_string_base_arith Sv48 inp mbase sp brk draw Hlau) as HA.
  pose proof Hlau as Hl. cbn [entry_launch_ok_va] in Hl. destruct Hl as ((_ & Htop & _) & _ & _).
  assert (Hvt : va_stack_top Sv48 = 0x800000000000%Z) by reflexivity. rewrite Hvt in Htop.
  pose proof (total_arg_bytes_firstn_le (S k) (in_argv inp)) as Hle.
  rewrite (total_arg_bytes_firstn_S k (in_argv inp) Hk) in Hle.
  assert (HL : (total_arg_bytes_nat (in_argv inp)
                <= launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))%nat)
    by (unfold launch_string_bytes; rewrite length_flatten_strings; lia).
  pose proof (u64_range (ed_top draw)). pose proof (u64_range sp).
  rewrite cat_argv_ptr_offset by exact Hk. rewrite word_add_nat_Z2bv.
  rewrite u_Z2bv_lt by (rewrite Hb; lia).
  rewrite Hb. lia.
Qed.
