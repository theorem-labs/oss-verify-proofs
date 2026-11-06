(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.

Module R_pc1_c.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.R_snq16 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Storrsf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store_sf.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietml6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietml6.dlia3.
(* [comment removed for export] *)

Lemma pc1_c : pass1_stmt FMT_C 3.
Proof.
  unfold pass1_stmt. intros until canary. intros -> -> -> -> ST FMT [SSP1 SSP2] MI LO SPH APR NAR NTR AG GT.
  unfold GOT_SSP, SSP_GUARD, FMT_C, GLOBALS_TOP, PRINTF_CORE, PC1_DEPTH in *.
  pose proof (ro_cells_bound _ _ _ _ FMT) as AB. cbn [cells_size csize Nat.add] in AB.
  pose proof (munch_refl [(bv_unsigned sp - 544, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  (* [comment removed for export] *) carve_frame 112%nat ST. carve_frame (Z.to_nat 320) ST. carve_frame 112%nat ST.
  do 43 zs. name_junk FR. name_junk FR1.
  (* [comment removed for export] *)
  zto 0x26fc8%Z.
  zs. brf Kc. { exfalso. apply Kc. reflexivity. }
  do 16 zs.
  release_frame FR1 ST (bv_unsigned sp + -432)%Z. release_frame FR0 ST (bv_unsigned sp + -112)%Z. release_frame FR ST (bv_unsigned sp).
  finish.
Qed.
End R_pc1_c.


Module R_pcrlm.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.R_snq16 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Storrsf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store_sf.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietml6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietml6.dlia3.
(* [comment removed for export] *)

Lemma pc1_pfx : pass1_stmt FMT_PFX 6.
Proof.
  unfold pass1_stmt. intros until canary. intros -> -> -> -> ST FMT [SSP1 SSP2] MI LO SPH APR NAR NTR AG GT.
  unfold GOT_SSP, SSP_GUARD, FMT_PFX, GLOBALS_TOP, PRINTF_CORE, PC1_DEPTH in *.
  pose proof (ro_cells_bound _ _ _ _ FMT) as AB. cbn [cells_size csize Nat.add] in AB.
  pose proof (munch_refl [(bv_unsigned sp - 544, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  (* [comment removed for export] *) carve_frame 112%nat ST. carve_frame (Z.to_nat 320) ST. carve_frame 112%nat ST.
  do 43 zs. name_junk FR. name_junk FR1.
  (* [comment removed for export] *)
  zto 0x26fc8%Z.
  zs. brf Kc. { exfalso. apply Kc. reflexivity. }
  do 16 zs.
  release_frame FR1 ST (bv_unsigned sp + -432)%Z. release_frame FR0 ST (bv_unsigned sp + -112)%Z. release_frame FR ST (bv_unsigned sp).
  finish.
Qed.
End R_pcrlm.


Module R_pcbh7.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.R_snq16 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Storrsf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.word_eq_guarded.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store_sf.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietml6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietml6.dlia3.
(* [comment removed for export] *)

Lemma pc1_host : pass1_stmt FMT_HOST 13.
Proof.
  unfold pass1_stmt. intros until canary. intros -> -> -> -> ST FMT [SSP1 SSP2] MI LO SPH APR NAR NTR AG GT.
  unfold GOT_SSP, SSP_GUARD, FMT_HOST, GLOBALS_TOP, PRINTF_CORE, PC1_DEPTH in *.
  pose proof (ro_cells_bound _ _ _ _ FMT) as AB. cbn [cells_size csize Nat.add] in AB.
  pose proof (munch_refl [(bv_unsigned sp - 544, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  (* [comment removed for export] *) carve_frame 112%nat ST. carve_frame (Z.to_nat 320) ST. carve_frame 112%nat ST.
  do 43 zs. name_junk FR. name_junk FR1.
  (* [comment removed for export] *)
  zto 0x26fc8%Z.
  zs. brf Kc. { exfalso. apply Kc. reflexivity. }
  do 16 zs.
  release_frame FR1 ST (bv_unsigned sp + -432)%Z. release_frame FR0 ST (bv_unsigned sp + -112)%Z. release_frame FR ST (bv_unsigned sp).
  finish.
Qed.
End R_pcbh7.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_pc6ck.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_pc6ck.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_pc6ck.

Module R_tos6n.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.R_snq16.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Storrsf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.word_eq_guarded.
(* [comment removed for export] *)

Definition towrite_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp buf bufsize CK : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (mode' : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(Fp, Fp + 232)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' Fp (snfile z64 (buf + bufsize) buf buf buf bufsize mode' CK).

Lemma towrite_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Fp wend wpos wbase buf bufsize CK : Z) (mode : word),
  a0 = Z_to_bv 64 Fp ->
  rw_cells rsegs m Fp (snfile z64 wend wpos wbase buf bufsize mode CK) ->
  (0 <= buf)%Z -> (0 <= bufsize)%Z -> (buf + bufsize < 2^64)%Z ->
  mem_inv rsegs m ->
  evt rsegs (towrite_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp buf bufsize CK m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x25a94) fc None m (seg_rom rsegs)).
Proof.
  intros until mode. intros -> FL B0 S0 BS MI.
  pose proof (munch_refl [(Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (rw_cells_bound _ _ _ _ FL) as FB. rewrite snfile_size in FB.
  unfold snfile, z64, m1w in FL.
  zs. zs. zs. zs. zs. zs. zs. if_lit.
  zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
  apply evt_done. unfold towrite_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  unfold snfile, z64, m1w. exact FL.
Qed.
End R_tos6n.

Module R_vfgox.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.R_snq16 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_tos6n OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.R_fw3vn.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Storrsf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.word_eq_guarded.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor5a9.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= hot_kdrop; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *) From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store_sfd.
(* [comment removed for export] *)
Ltac brf K := if_cases K; zify_cond K.
Ltac br K := brf K; try (exfalso; lia).

Definition VF_DEPTH : Z := 976.   (* [comment removed for export] *)

Definition vfprintf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo Fp D : Z) (n : nat) (VA : Z) (slots : list word) (HS : Z) (hs : list byte) (o : list byte) (canary : word)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mode' : word) (jd' : list byte) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length o))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(Fp - 976, Fp + 248); (D, D + Z.of_nat n)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' Fp (snfile z64 0 0 0 (Fp + 255) 0 mode' (Fp + 232))
    /\ rw_cells rsegs m' (Fp + 232) [C8 (Z_to_bv 64 (D + Z.of_nat (length (dl n o)))); C8 (Z_to_bv 64 ((Z.of_nat n - 1) - Z.of_nat (length (dl n o))))]
    /\ rw_cells rsegs m' D [CB n (dl n o ++ Z_to_bv 8 0 :: jd')]
    /\ va_area m' VA slots /\ bytes_at rsegs m' HS hs
    /\ ssp_cells m' canary.

Section VF.
  Variables (FMT : list cell) (la nargs : Z) (PRE : list word -> Z -> list byte -> Prop) (OUT : list word -> list byte -> list byte).
  Hypothesis HLA : Z.of_nat (cells_size FMT) = la.
  Hypothesis HOUT : forall slots HS hs, PRE slots HS hs -> (Z.of_nat (length (OUT slots hs)) < 2^31)%Z.
  Hypothesis P1 : pass1_stmt FMT la.
  Hypothesis P2 : pass2_stmt FMT la nargs PRE OUT.

  #[using="P2 P1 HOUT HLA nargs"] Lemma vfprintf_sn_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte)
      (lo A Fp D : Z) (n : nat) (VA : Z) (slots : list word) (HS : Z) (hs jd : list byte) (canary : word),
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
    stk rsegs m lo (bv_unsigned sp) -> ro_cells rsegs m A FMT -> ssp_cells m canary ->
    rw_cells rsegs m Fp (snfile z64 0 0 0 (Fp + 255) 0 z64 (Fp + 232)) ->
    rw_cells rsegs m (Fp + 232) [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 (Z.of_nat n - 1))] ->
    rw_cells rsegs m D [CB n (Z_to_bv 8 0 :: jd)] ->
    va_area m VA slots -> bytes_at rsegs m HS hs -> PRE slots HS hs -> mem_inv rsegs m ->
    Fp = bv_unsigned sp ->
    (lo <= bv_unsigned sp - VF_DEPTH)%Z -> (GLOBALS_TOP <= lo)%Z -> (Fp + 304 <= VA)%Z -> (VA + 8 * Z.of_nat (length slots) <= 2^63)%Z ->
    (IMG_LO <= A)%Z -> (A + la <= RO_TOP)%Z -> dst_ok D n -> (D + Z.of_nat n <= lo)%Z ->
    (HS + Z.of_nat (length hs) <= lo)%Z -> (~ (D < HS + Z.of_nat (length hs) /\ HS < D + Z.of_nat n))%Z ->
    evt rsegs (vfprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo Fp D n VA slots HS hs (OUT slots hs) canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x26030) fc None m (seg_rom rsegs)).
  Proof.
    intros until canary. intros -> -> -> ST HF SSP FL CKC DST VAA HSB HPRE MI HFp LO GT VLO VHI ARL ART GD DLO HSL HSD.
    destruct SSP as [SSP1 SSP2]. pose proof GD as GD'.
    unfold GOT_SSP, SSP_GUARD, GLOBALS_TOP, RO_TOP, VF_DEPTH, dst_ok, IMG_LO, IMG_HI in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (ro_cells_bound _ _ _ _ HF) as AB.
    pose proof (munch_refl [(Fp - 976, Fp + 248); (D, D + Z.of_nat n)]%Z m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    unfold va_area in VAA. unfold snfile, z64, m1w in FL.
    carve_frame 368%nat ST.
    zto 0x261e0%Z. name_junk FR.
    (* [comment removed for export] *)
    call_lit P1 by (idtac;
      lazymatch goal with
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
      | |- ssp_cells _ _ => split; eassumption
      | |- ro_cells _ _ _ _ => eassumption
      | |- mem_inv _ _ => eassumption
      | |- @eq _ _ _ => reflexivity
      | |- _ => rewrite ?unsigned_lit by lia; unfold PC1_DEPTH, GLOBALS_TOP, RO_TOP in *; lia
      end || match goal with |- ?G => idtac "P1SIDE-FAIL:" G end).
    rename POST into ST.
    zto 0x260c4%Z. rewrite sx32_zero.
    zto 0x25a94%Z.
    (* [comment removed for export] *)
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FL); call_lit towrite_spec by (idtac; first [ reflexivity | eassumption | lia ]).
    rename POST into FL.
    zto 0x261e0%Z.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB rsegs _ _ [_;_] 248 _ _ [80; 168]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in FR. destruct FR as [APC FR].
    apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in FR. destruct FR as [FR1 FR].
    apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in FR. destruct FR as [BUF FR2].
    cbn [cells_size csize Nat.add] in FR1, BUF, FR2.
    replace (bv_unsigned sp + -368 + Z.of_nat 8)%Z with (bv_unsigned sp + -360)%Z in FR1 by lia.
    replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8)%Z with (bv_unsigned sp + -352)%Z in BUF by lia.
    replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 80)%Z with (bv_unsigned sp + -272)%Z in FR2 by lia.
    name_junk BUF. name_junk FR2.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
    assert (CKC' : rw_cells rsegs mq (Fp + 232) [C8 (Z_to_bv 64 (D + Z.of_nat (length (dl n [])))); C8 (Z_to_bv 64 (Z.of_nat n - 1 - Z.of_nat (length (dl n []))))]);
    [ rewrite dl_nil; cbn [length Z.of_nat]; rewrite Z.add_0_r, Z.sub_0_r; exact CKC |];
    assert (DST' : rw_cells rsegs mq D [CB n (dl n [] ++ Z_to_bv 8 0 :: jd)]);
    [ rewrite dl_nil; cbn [app]; exact DST |];
    lazymatch type of FL with rw_cells _ _ _ (snfile _ _ _ _ _ _ ?md _) =>
    assert (FL' : rw_cells rsegs mq Fp (snfile z64 ((bv_unsigned sp + -352) + 80) ((bv_unsigned sp + -352) + Z.of_nat (@length byte [])) (bv_unsigned sp + -352) (bv_unsigned sp + -352) 80 md (Fp + 232)));
    [ cbn [length Z.of_nat]; rewrite Z.add_0_r; exact FL |] end end.
    pose proof (rw_CB_length _ _ _ _ _ DST) as LD. cbn [length] in LD.
    clear CKC DST FL.
    (* [comment removed for export] *)
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_APC); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_BUF); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_CKC'); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_DST'); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FL'); call_lit P2 by (idtac;
      lazymatch goal with
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
      | |- ssp_cells _ _ => split; eassumption
      | |- ro_cells _ _ _ _ => eassumption
      | |- mem_inv _ _ => eassumption
      | |- sink _ _ _ _ _ _ _ _ => rewrite ?unsigned_lit by lia; eexists _, _; refine (conj _ (conj _ (conj _ (conj _ _))));
           [ eapply rwc_eq; [exact FL' | lia] | exact CKC' | rewrite app_nil_l; exact BUF | exact DST' | lia ]
      | |- rw_cells _ _ _ [C8 _] => rewrite ?unsigned_lit by lia; eapply rwc_eq; [exact APC | lia]
      | |- va_area _ _ _ => exact VAA
      | |- bytes_at _ _ _ _ => eassumption
      | |- PRE _ _ _ => exact HPRE
      | |- dst_ok _ _ => unfold dst_ok, IMG_LO, IMG_HI; exact GD
      | |- @eq _ _ _ => rewrite ?unsigned_lit by lia; first [ reflexivity | f_equal; lia | lia ]
      | |- _ => rewrite ?unsigned_lit by lia; unfold PC2_DEPTH, GLOBALS_TOP, RO_TOP, IMG_LO in *; lia
      end).
    try clear FL'; try clear CKC'; try clear BUF; try clear DST'; try clear VAA; try clear HSB; try clear SSP1; try clear SSP2. rename PC into ST. rename PC3 into VAA. rename PC4 into HSB. destruct POST as [SSP1 SSP2]. unfold GOT_SSP, SSP_GUARD in SSP1, SSP2. unfold va_area in VAA.
    unpack_sink PC0 FL CKC BUF DST. unfold snfile, z64, m1w, SN_WRITE in FL.
    zto 0x26140%Z. zs. br K. clear K.
    zto 0x2aa78%Z.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
    eapply evt_cut; [ eapply (sn_write_sink _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 _ _ _ _ F fc mq Fp (bv_unsigned sp + -352) D n _ _ _ [] 0 0 lo);
                      try reflexivity | ] end.
    { rewrite ?unsigned_lit by lia. exact ST. }
    { eexists _, _; refine (conj _ (conj _ (conj _ (conj _ _)))); [ unfold snfile, z64, m1w, SN_WRITE; exact FL | exact CKC | exact BUF | exact DST | lia ]. }
    { apply bytes_at_nil. lia. }
    { lia. }
    { unfold sn_layout. rewrite ?unsigned_lit by lia. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia. }
    { assumption. }
    cbv beta. intros ms' P. unfold sn_write_sink_post in P.
    (first [ dex15 P as y5 y6 y7 b1 b2 b3 b4 b5 b6 b7 y28 y29 y30 y31 m'; dand7 P as -> MU' WM' MI' ST' SNK' _ | dand22 P as y5 y6 y7 b1 b2 b3 b4 b5 b6 b7 y28 y29 y30 y31 m' -> MU' WM' MI' ST' SNK' _ | destruct P as (y5 & y6 & y7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y28 & y29 & y30 & y31 & m' & -> & MU' & WM' & MI' & ST' & SNK' & _) ]).
    rewrite ?unsigned_lit in MU' by lia. rewrite ?unsigned_lit in ST' by lia.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_CKC); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_DST); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FL); lazymatch type of MU' with munch _ ?mq _ => transport_after_call rsegs mq m' MU' WM'; clear MU' WM' end.
    replace (ret_pc (Z_to_bv 64 155992)) with (Z_to_bv 64 155992) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    try clear FL; try clear CKC; try clear BUF; try clear DST.
    rewrite app_nil_r in SNK'. unpack_sink SNK' FL CKC BUF DST. unfold snfile, z64, m1w in FL.
    zto 0x2616c%Z.
    (* [comment removed for export] *)
    zs. zs.
    replace (Z.b2z (0 <? (bv_unsigned sp + -352 + Z.of_nat (@length byte [])) mod 18446744073709551616)%Z) with 1%Z.
    2:{ cbn [length Z.of_nat]. rewrite Z.add_0_r, Z.mod_small by lia. replace (0 <? bv_unsigned sp + -352)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    zto 0x26180%Z. rewrite sx32_zero.
    zto 0x261b4%Z. zs. brf Kc. { exfalso. apply Kc. reflexivity. } clear Kc.
    (* [comment removed for export] *)
    lazymatch type of APC2 with _ => idtac end || idtac.
    match goal with A1 : rw_cells _ ?mq (bv_unsigned sp + -368) [C8 ?va], B1 : rw_cells _ ?mq (bv_unsigned sp + -352) [CB 80 ?bb] |- _ =>
      lazymatch type of FR1 with rw_cells _ _ _ ?cs1 => lazymatch type of FR2 with rw_cells _ _ _ ?cs2 =>
      assert (FR : rw_cells rsegs mq (bv_unsigned sp + -368) ([C8 va] ++ cs1 ++ [CB 80 bb] ++ cs2));
      [ apply (proj2 (rw_cells_app rsegs _ _ [_] _)); split; [exact A1|]; cbn [cells_size csize Nat.add];
        apply (proj2 (rw_cells_app rsegs _ _ [_] _)); split; [eapply rwc_eq; [exact FR1|lia]|]; cbn [cells_size csize Nat.add];
        apply (proj2 (rw_cells_app rsegs _ _ [_] _)); split; [eapply rwc_eq; [exact B1|lia]|]; cbn [cells_size csize Nat.add];
        eapply rwc_eq; [exact FR2|lia]
      | clear A1 FR1 B1 FR2; cbn [app] in FR ] end end end.
    do 9 zs.
    match goal with H : stk _ _ lo _ |- _ => rename H into ST end.
    release_frame FR ST (bv_unsigned sp).
    pose proof (HOUT _ _ _ HPRE) as OL.
    match goal with |- context [Z_to_bv 64 (Z.lor ?a (Z.lor 0 ?b))] =>
      replace (Z.lor a (Z.lor 0 b)) with (Z.of_nat (length (OUT slots hs)));
      [ | rewrite Z.lor_0_l; replace a with 0%Z by reflexivity; rewrite Z.lor_0_l, Z.mod_small by lia; reflexivity ] end.
    apply evt_done. unfold vfprintf_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
    split. { unfold snfile, z64, m1w. exact FL. }
    rewrite <- PC1.
    split; [exact CKC|]. split; [exact DST|]. split; [exact VAA|]. split; [exact HSB|]. split; assumption.
  Qed.
End VF.
End R_vfgox.


Module R_vsn6b.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Img0 R_memset.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_memset OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.R_snq16 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_vfgox.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Storrsf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac transport_after_call segs m m' MU WM ::= hot_kdrop; transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac lia ::= lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.word_eq_guarded.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store_sf.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
Ltac brf K := if_cases K; zify_cond K.
Ltac br K := brf K; try (exfalso; lia).

Definition VSN_DEPTH : Z := 1280.   (* [comment removed for export] *)

Definition vsnprintf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo D : Z) (n : nat) (VA : Z) (slots : list word) (HS : Z) (hs : list byte) (o : list byte) (canary : word)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (jd' : list byte) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length o))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 1280, bv_unsigned sp); (D, D + Z.of_nat n)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' D [CB n (firstn (n - 1) o ++ Z_to_bv 8 0 :: jd')]
    /\ va_area m' VA slots /\ bytes_at rsegs m' HS hs
    /\ ssp_cells m' canary
    /\ (Z.of_nat (length o) < 2^31)%Z.

Lemma le8_z64 : le8 z64 = repeat (Z_to_bv 8 0) 8.
Proof. unfold le8, z64. cbn. rewrite ?unsigned_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Definition zfile : list cell :=
  [C4 z64; C4 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64;
   C8 z64; C8 z64; C4 z64; C4 z64; C8 z64; C4 z64; C4 z64; C4 z64; C4 z64; C8 z64;
   C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64].
Lemma zfile_bytes : cells_bytes zfile = repeat (Z_to_bv 8 0) 232.
Proof. unfold zfile. cbn [cells_bytes cbytes]. rewrite !le8_z64, !le4_z64. reflexivity. Qed.
Lemma zfile_wf : cells_wf zfile.
Proof. cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit. Qed.
Lemma snfile_wf : forall fl we wp wb bf bs md ck, cells_wf (snfile fl we wp wb bf bs md ck).
Proof. intros. cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit. Qed.

Section VSN.
  Variables (FMT : list cell) (la nargs : Z) (PRE : list word -> Z -> list byte -> Prop) (OUT : list word -> list byte -> list byte).
  Hypothesis HLA : Z.of_nat (cells_size FMT) = la.
  Hypothesis HOUT : forall slots HS hs, PRE slots HS hs -> (Z.of_nat (length (OUT slots hs)) < 2^31)%Z.
  Hypothesis P1 : pass1_stmt FMT la.
  Hypothesis P2 : pass2_stmt FMT la nargs PRE OUT.

  #[using="P2 P1 HOUT HLA nargs"] Lemma vsnprintf_gen_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte)
      (lo A D : Z) (n : nat) (VA : Z) (slots : list word) (HS : Z) (hs jd : list byte) (canary : word),
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 (Z.of_nat n) -> a2 = Z_to_bv 64 A -> a3 = Z_to_bv 64 VA ->
    stk rsegs m lo (bv_unsigned sp) -> ro_cells rsegs m A FMT -> ssp_cells m canary ->
    rw_cells rsegs m D [CB n jd] -> va_area m VA slots -> bytes_at rsegs m HS hs -> PRE slots HS hs ->
    mem_inv rsegs m ->
    (1 <= n)%nat ->
    (lo <= bv_unsigned sp - VSN_DEPTH)%Z -> (GLOBALS_TOP <= lo)%Z -> (bv_unsigned sp <= VA)%Z -> (VA + 8 * Z.of_nat (length slots) <= 2^63)%Z ->
    (IMG_LO <= A)%Z -> (A + la <= RO_TOP)%Z -> dst_ok D n -> (D + Z.of_nat n <= lo)%Z ->
    (HS + Z.of_nat (length hs) <= lo)%Z -> (~ (D < HS + Z.of_nat (length hs) /\ HS < D + Z.of_nat n))%Z ->
    evt rsegs (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo D n VA slots HS hs (OUT slots hs) canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2a9ac) fc None m (seg_rom rsegs)).
  Proof.
    intros until canary. intros -> -> -> -> ST HF SSP DST VAA HSB HPRE MI N1 LO GT VLO VHI ARL ART GD DLO HSL HSD.
    destruct SSP as [SSP1 SSP2].
    unfold GOT_SSP, SSP_GUARD, GLOBALS_TOP, RO_TOP, VSN_DEPTH, dst_ok, IMG_LO, IMG_HI in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (ro_cells_bound _ _ _ _ HF) as AB.
    pose proof (rw_CB_length _ _ _ _ _ DST) as LD.
    pose proof (munch_refl [(bv_unsigned sp - 1280, bv_unsigned sp); (D, D + Z.of_nat n)]%Z m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    unfold va_area in VAA.
    carve_frame 304%nat ST.
    zto 0x2a9e0%Z. zs. br K. clear K.
    zto 0x2a9f8%Z.
    (* [comment removed for export] *)
    replace (Z.of_nat n <? Z.of_nat n + -1)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
    change ((0 + -1) mod 18446744073709551616)%Z with 18446744073709551615%Z.
    replace (Z.land 18446744073709551615 (Z.of_nat n + -1)) with (Z.of_nat n + -1)%Z
      by (rewrite Z.land_comm; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
    zto 0x2b058%Z.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in FR. destruct FR as [FFILE FR]. cbn [cells_size csize Nat.add] in FR.
    replace (bv_unsigned sp + -304 + Z.of_nat 232)%Z with (bv_unsigned sp + -72)%Z in FR by lia.
    name_junk FFILE. name_junk FR.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FFILE); lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      eapply evt_cut; [ eapply memset_callv | post_call_lit rsegs mq ] end.
    { exact FFILE. } { lia. } { lia. } { lia. } { assumption. }
    match goal with H : rw_cells _ _ _ [CB (Z.to_nat 232) _] |- _ =>
      pose proof (rw_cells_recast rsegs _ _ _ zfile H zfile_wf ltac:(rewrite zfile_bytes; reflexivity)) as FL; clear H end.
    unfold zfile, z64 in FL.
    zto 0x2aa38%Z.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      assert (FL' : rw_cells rsegs mq (bv_unsigned sp + -304) (snfile z64 0 0 0 ((bv_unsigned sp + -304) + 255) 0 z64 ((bv_unsigned sp + -304) + 232))) end.
    { eapply rw_cells_recast; [exact FL | apply snfile_wf |].
      unfold snfile, z64, m1w, SN_WRITE. cbn [cells_bytes cbytes].
      replace (bv_unsigned sp + -304 + 255)%Z with (bv_unsigned sp + -49)%Z by lia.
      replace (bv_unsigned sp + -304 + 232)%Z with (bv_unsigned sp + -72)%Z by lia. reflexivity. }
    clear FL.
    (* [comment removed for export] *)
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as DA.
    pose proof (u8arr_store_ok rsegs _ _ _ 0 (Z_to_bv 64 D) DA ltac:(rewrite LD; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    zs. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mq _ _) _) =>
          replace (write_to_mem mq (Z_to_bv 64 D) [Z_to_bv 8 0]) with (write_to_mem mq (wa (D + 0)) [Z_to_bv 8 0]) by (unfold wa; f_equal; f_equal; lia) end.
    pose proof (u8arr_write rsegs _ _ _ 0 (Z_to_bv 8 0) DA ltac:(rewrite LD; lia)) as DA2. clear DA. store_done.
    pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DST. rewrite upd_length, LD in DST. clear DA2.
    rewrite upd_firstn_skipn in DST by (rewrite LD; lia). cbn [Z.to_nat firstn app] in DST.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app rsegs _ _ [_;_] _)) in FR. destruct FR as [CKC FR]. cbn [cells_size csize Nat.add] in FR.
    replace (bv_unsigned sp + -72 + Z.of_nat 16)%Z with (bv_unsigned sp + -56)%Z in FR by lia.
    zto 0x26030%Z.
    (* [comment removed for export] *)
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_CKC); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_DST); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FL'); call_lit (vfprintf_sn_spec FMT la nargs PRE OUT HLA HOUT P1 P2) by (idtac;
      lazymatch goal with
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
      | |- ssp_cells _ _ => split; eassumption
      | |- ro_cells _ _ _ _ => eassumption
      | |- mem_inv _ _ => eassumption
      | |- rw_cells _ _ _ (snfile _ _ _ _ _ _ _ _) => rewrite ?unsigned_lit by lia; exact FL'
      | |- rw_cells _ _ _ [C8 _; C8 _] => rewrite ?unsigned_lit by lia; eapply rwc_eq; [exact CKC | lia]
      | |- rw_cells _ _ _ [CB _ _] => exact DST
      | |- va_area _ _ _ => exact VAA
      | |- bytes_at _ _ _ _ => eassumption
      | |- PRE _ _ _ => exact HPRE
      | |- dst_ok _ _ => unfold dst_ok, IMG_LO, IMG_HI; exact GD
      | |- @eq _ _ _ => rewrite ?unsigned_lit by lia; first [ reflexivity | f_equal; lia | lia ]
      | |- _ => rewrite ?unsigned_lit by lia; unfold VF_DEPTH, GLOBALS_TOP, RO_TOP, IMG_LO in *; lia
      end || match goal with |- ?G => idtac "VFSIDE-FAIL:" G end).
    rename PC into ST. try clear SSP1; try clear SSP2. destruct POST as [SSP1 SSP2]. unfold GOT_SSP, SSP_GUARD in SSP1, SSP2.
    zto 0x2aa54%Z. zs. brf Kc. { exfalso. apply Kc. reflexivity. } clear Kc.
    (* [comment removed for export] *)
    unfold snfile, z64, m1w, SN_WRITE in PC0.
    lazymatch type of PC0 with rw_cells _ ?mq _ ?cs0 => lazymatch type of PC1 with rw_cells _ _ _ ?cs1 => lazymatch type of FR with rw_cells _ _ _ ?cs2 =>
      assert (FR' : rw_cells rsegs mq (bv_unsigned sp + -304) (cs0 ++ cs1 ++ cs2));
      [ apply (proj2 (rw_cells_app rsegs _ _ _ _)); split; [exact PC0|]; cbn [cells_size csize Nat.add];
        apply (proj2 (rw_cells_app rsegs _ _ [_;_] _)); split; [eapply rwc_eq; [exact PC1|lia]|]; cbn [cells_size csize Nat.add];
        eapply rwc_eq; [exact FR|lia]
      | clear PC0 PC1 FR; cbn [app] in FR'; rename FR' into FR ] end end end.
    do 7 zs.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold vsnprintf_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
    split; [exact PC2|]. split; [exact PC3|]. split; [exact PC4|]. split; [split; assumption|]. apply (HOUT _ _ _ HPRE).
  Qed.
End VSN.
End R_vsn6b.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.R_snq16 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_pc1_c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_pcrlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_pcbh7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_pc6ck.R_pcgt7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_pc6ck.R_pc429 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_pc6ck OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_vfgox OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_vsn6b.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Lemma HOUT_C : forall slots HS hs, PRE_C slots HS hs -> (Z.of_nat (length (OUT_C slots hs)) < 2^31)%Z.
Proof. intros slots HS hs [ch H]. unfold OUT_C. rewrite H. cbn. lia. Qed.
Lemma HOUT_PFX : forall slots HS hs, PRE_PFX slots HS hs -> (Z.of_nat (length (OUT_PFX slots hs)) < 2^31)%Z.
Proof.
  (intros slots HS hs; (first [ intro dR_3; dand4 dR_3 as P HP _ OKS | intros (P & HP & _ & OKS) ])). unfold OUT_PFX. rewrite HP.
  pose proof (out_s_length _ _ _ OKS). (first [ dand4 OKS as P0 _ OK LH | destruct OKS as (P0 & _ & OK & LH) ]).
  pose proof (strnlen_res_bound _ _ _ (proj1 P0) OK). rewrite length_app. cbn [length]. lia.
Qed.
Lemma HOUT_HOST : forall slots HS hs, PRE_HOST slots HS hs -> (Z.of_nat (length (OUT_HOST slots hs)) < 2^31)%Z.
Proof.
  (intros slots HS hs; (first [ intro dR_4; dand6 dR_4 as P ch HP _ Hch OKS | intros (P & ch & HP & _ & Hch & OKS) ])). unfold OUT_HOST. rewrite HP, Hch.
  pose proof (out_s_length _ _ _ OKS). (first [ dand4 OKS as P0 _ OK LH | destruct OKS as (P0 & _ & OK & LH) ]).
  pose proof (strnlen_res_bound _ _ _ (proj1 P0) OK). unfold TXT_HOST, out_c. rewrite !length_app. cbn [length Nat.add]. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
