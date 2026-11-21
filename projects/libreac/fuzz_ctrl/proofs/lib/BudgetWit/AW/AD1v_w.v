(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1v.v (donor image sha256 7093581aab04), with its module paths changed, names TfibSyms -> CtrlTSyms and its addresses moved to libreac/fuzz_ctrl's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AD1v.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3, with libreac/fuzz_boxreg's port of its copy of this file (changed argv_str_fits', argv_over_read). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK15.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YP0n YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.BudgetWit.AW Require Import YA0n_w YA0e_w.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG00 YG0a YG01 YG0k YG0f YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.BudgetWit.AW Require Import YG0n_w YG0d_w.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AB1v AF0m AD2j.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.BudgetWit.AW Require Import AD2i_w AD1t_w AD20_w.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YD2n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.BudgetWit.AW Require Import AD1u_w.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Definition top_ok (usp : Z) (ly : alayout) : Prop :=
usp - 160 <= ly_top ly <= usp + 3920 /\ ly_stk_lo ly = ASAN_CEIL /\ ly_stk_hi ly = kHighMemEnd
/\ YM05.ceil_of_top (usp - stack_max_size).
Lemma top_ok_ceil : forall usp ly, top_ok usp ly -> YM05.ceil_of_top (usp - stack_max_size).
Proof. intros usp ly (_ & _ & _ & H). exact H. Qed.
Lemma argv_str_fits' : forall (top : word) argv envp efn k, bv_unsigned top <= kHighMemEnd -> (k < length argv)%nat ->
z_argv (bv_unsigned top) argv envp efn k + Z.of_nat (length (nth k argv [])) + 1 < kHighMemEnd.
Proof.
intros top argv envp efn k Htop Hk. pose proof (YP08.tab_firstn_nth_le argv k Hk) as T.
unfold z_argv, z_strs, launch_string_bytes. rewrite !length_flatten_strings. lia.
Qed.
Lemma argv_over_read : forall sp {top : word} argv envp {efn : list byte} (two : bool) (m : word -> option byte) k,
(k < length argv)%nat -> runs_at (bv_unsigned sp) m (runs_main_tfa two sp top argv envp efn) ->
forall a, z_argv (bv_unsigned top) argv envp efn k + Z.of_nat (length (nth k argv [])) < a
< z_argv (bv_unsigned top) argv envp efn k + Z.of_nat (length (nth k argv []))
- (z_argv (bv_unsigned top) argv envp efn k + Z.of_nat (length (nth k argv []))) mod 8 + 8 ->
m (Z_to_bv 64 a) <> None.
Proof.
intros sp top argv envp efn two m k Hk HR a Ha.
assert (HB : YP03.bytes_at m (z_strs (bv_unsigned top) argv envp efn) (stack_tail argv envp efn)).
{ apply (runs_at_nth _ _ _ (if two then 3 else 2)%nat _ _ HR). destruct two; reflexivity. }
set (q := z_argv (bv_unsigned top) argv envp efn k + Z.of_nat (length (nth k argv []))) in *.
assert (Hlen : Z.of_nat (length (stack_tail argv envp efn))
= Z.of_nat (total_arg_bytes_nat argv) + Z.of_nat (total_arg_bytes_nat envp) + Z.of_nat (length efn) + 9).
{ unfold stack_tail. rewrite !length_app, !length_flatten_strings, repeat_length. cbn [length]. lia. }
pose proof (YP08.tab_firstn_nth_le argv k Hk) as T.
assert (Hlo : z_strs (bv_unsigned top) argv envp efn <= q) by (unfold q, z_argv; lia).
assert (Hhi : q + 1 <= z_strs (bv_unsigned top) argv envp efn + Z.of_nat (total_arg_bytes_nat argv))
by (unfold q, z_argv; lia).
pose proof (Z.mod_pos_bound q 8 ltac:(lia)) as D2.
replace a with (z_strs (bv_unsigned top) argv envp efn + Z.of_nat (Z.to_nat (a - z_strs (bv_unsigned top) argv envp efn))) by lia.
rewrite (HB (Z.to_nat (a - z_strs (bv_unsigned top) argv envp efn))) by lia.
destruct (nth_error _ _) eqn:Hn; [discriminate|]. apply nth_error_None in Hn. exfalso. lia.
Qed.
End b.
