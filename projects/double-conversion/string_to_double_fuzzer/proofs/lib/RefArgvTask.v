(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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

Lemma cat_argv_ptr_task : forall (sp : word) (av ev : list (list byte)) (k : nat),
  valid_argv av -> valid_envp ev ->
  (sp_window_lo <= bv_unsigned sp)%Z -> (bv_unsigned sp <= sp_window_hi)%Z ->
  entry_stack_fits sp av ev ->
  (k < length av)%nat ->
  (bv_unsigned (cat_argv_ptr sp av ev k) + Z.of_nat (length (nth k av [])) + 1 <= 0x800000000000)%Z.
Proof.
  intros sp av ev k Hva Hve Hlo Hhi Hfit Hk.
  rewrite (u_cat_argv_ptr sp av ev Hva Hve Hlo Hhi k Hk).
  pose proof (total_arg_bytes_firstn_le (S k) av) as Hle. rewrite (total_arg_bytes_firstn_S k av Hk) in Hle.
  unfold entry_stack_fits, entry_stack_span, sp_window_hi in Hfit. unfold cat_struct_size.
  rewrite (total_arg_bytes_Z av) in Hfit. rewrite (total_arg_bytes_Z ev) in Hfit.
  change auxv_size with 160%nat in *. lia.
Qed.
