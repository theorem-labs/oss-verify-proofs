(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatSim LibIface BnContract.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LxLin LxState LxMem LxStep LxCheck LxGlue LxFinal.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Export LxEnvU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations LXL LXS LXM LXI LXC.
Open Scope Z_scope.

Lemma uenv_okb_U : LXG.uenv_okb UU = true.
Proof. vm_compute. reflexivity. Qed.

Lemma glue_okb_U : LXG.glue_okb UU LIBR_HULL_U LIBR_U SNAP_U = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Theorem lib_U_of_units : forall UnA UnB : unitT,
  un_env UnA = UU -> un_env UnB = UU ->
  un_snap UnA = SNAP_U -> un_snap UnB = SNAP_U ->
  nth_error (un_cuts UnA) 0 = Some (entry_cut ENTRY_U NMAX_U []) ->
  nth_error (un_cuts UnB) 0 = Some (entry_cut ENTRY_U NMAX_U SNAP_U) ->
  check_unit UnA = true -> un_total UnA = true ->
  check_unit UnB = true -> un_total UnB = true ->
  cbd_stmt_U -> lib_stmt_U.
Proof.
  intros UnA UnB EA EB SA SB CA CB CHKA TOTA CHKB TOTB HCBD.
  exact (LXF.lx_lib_stmt UU UnA UnB ENTRY_U NMAX_U LIBR_HULL_U LIBR_U SNAP_U CANARY_U uenv_okb_U glue_okb_U eq_refl
           EA EB SA SB CA CB CHKA TOTA CHKB TOTB HCBD).
Qed.
