(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatSim LibIface BnContract.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LxLin LxState LxMem LxStep LxCheck LxGlue LxFinal.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Export LxEnvP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations LXL LXS LXM LXI LXC.
Open Scope Z_scope.

Lemma uenv_okb_P : LXG.uenv_okb UP = true.
Proof. vm_compute. reflexivity. Qed.

Lemma glue_okb_P : LXG.glue_okb UP LIBR_HULL_P LIBR_P SNAP_P = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Theorem lib_P_of_units : forall UnA UnB : unitT,
  un_env UnA = UP -> un_env UnB = UP ->
  un_snap UnA = SNAP_P -> un_snap UnB = SNAP_P ->
  nth_error (un_cuts UnA) 0 = Some (entry_cut ENTRY_P NMAX_P []) ->
  nth_error (un_cuts UnB) 0 = Some (entry_cut ENTRY_P NMAX_P SNAP_P) ->
  check_unit UnA = true -> un_total UnA = true ->
  check_unit UnB = true -> un_total UnB = true ->
  cbd_stmt_P -> lib_stmt_P.
Proof.
  intros UnA UnB EA EB SA SB CA CB CHKA TOTA CHKB TOTB HCBD.
  exact (LXF.lx_lib_stmt UP UnA UnB ENTRY_P NMAX_P LIBR_HULL_P LIBR_P SNAP_P CANARY_P uenv_okb_P glue_okb_P eq_refl
           EA EB SA SB CA CB CHKA TOTA CHKB TOTB HCBD).
Qed.
