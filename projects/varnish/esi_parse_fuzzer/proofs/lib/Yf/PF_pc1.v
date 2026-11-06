(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA RA_seql RA_sjs3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcp2qs AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp2qs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Storrsf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor5a9.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_after_call segs m m' MU WM.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietml6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietml6.dlia3.
(* [comment removed for export] *)
(* [comment removed for export] *) From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store_sfd.
(* [comment removed for export] *)

Definition c1s (l : list Z) : list cell := map (fun z => C1 (Z_to_bv 8 z)) l.
Definition FMT_D : list cell := Eval cbv [c1s map] in c1s [37; 100; 10; 0]%Z.
Definition FMT_USAGE : list cell := Eval cbv [c1s map] in c1s [117; 115; 97; 103; 101; 58; 32; 37; 115; 32; 73; 78; 80; 85; 84; 10; 0]%Z.
Definition FMT_COPEN : list cell := Eval cbv [c1s map] in c1s [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32; 37; 115; 10; 0]%Z.
Definition FMT_RERR : list cell := Eval cbv [c1s map] in c1s [99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32; 37; 115; 10; 0]%Z.
Definition FMT_REFUSED : list cell := Eval cbv [c1s map] in c1s [99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 62; 61; 32; 37; 117; 32; 98; 121; 116; 101; 115; 44; 32; 114; 101; 102; 117; 115; 101; 100; 10; 0]%Z.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma pc1_d : pass1_stmt FMT_D 4.
Proof.
  unfold pass1_stmt. intros until canary. intros -> -> -> -> ST FMT_DH [SSP1 SSP2] MI LO SPH APR NAR NTR AG GT.
  unfold GOT_SSP, SSP_GUARD, FMT_D, GLOBALS_TOP, PRINTF_CORE, PC1_DEPTH in *.
  pose proof (ro_cells_bound _ _ _ _ FMT_DH) as AB. cbn [cells_size csize Nat.add] in AB.
  pose proof (munch_refl [(bv_unsigned sp - 544, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  (* [comment removed for export] *) carve_frame 112%nat ST. carve_frame (Z.to_nat 320) ST. carve_frame 112%nat ST.
  do 43 zs. name_junk FR. name_junk FR1.
  zto 0x9f998%Z.
  zs. brf Kc. { exfalso. apply Kc. reflexivity. }
  do 16 zs.
  release_frame FR1 ST (bv_unsigned sp + -432)%Z. release_frame FR0 ST (bv_unsigned sp + -112)%Z. release_frame FR ST (bv_unsigned sp).
  finish.
Qed.

Lemma pc1_usage : pass1_stmt FMT_USAGE 17.
Proof.
  unfold pass1_stmt. intros until canary. intros -> -> -> -> ST FMT_USAGEH [SSP1 SSP2] MI LO SPH APR NAR NTR AG GT.
  unfold GOT_SSP, SSP_GUARD, FMT_USAGE, GLOBALS_TOP, PRINTF_CORE, PC1_DEPTH in *.
  pose proof (ro_cells_bound _ _ _ _ FMT_USAGEH) as AB. cbn [cells_size csize Nat.add] in AB.
  pose proof (munch_refl [(bv_unsigned sp - 544, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  (* [comment removed for export] *) carve_frame 112%nat ST. carve_frame (Z.to_nat 320) ST. carve_frame 112%nat ST.
  do 43 zs. name_junk FR. name_junk FR1.
  zto 0x9f998%Z.
  zs. brf Kc. { exfalso. apply Kc. reflexivity. }
  do 16 zs.
  release_frame FR1 ST (bv_unsigned sp + -432)%Z. release_frame FR0 ST (bv_unsigned sp + -112)%Z. release_frame FR ST (bv_unsigned sp).
  finish.
Qed.

Lemma pc1_copen : pass1_stmt FMT_COPEN 21.
Proof.
  unfold pass1_stmt. intros until canary. intros -> -> -> -> ST FMT_COPENH [SSP1 SSP2] MI LO SPH APR NAR NTR AG GT.
  unfold GOT_SSP, SSP_GUARD, FMT_COPEN, GLOBALS_TOP, PRINTF_CORE, PC1_DEPTH in *.
  pose proof (ro_cells_bound _ _ _ _ FMT_COPENH) as AB. cbn [cells_size csize Nat.add] in AB.
  pose proof (munch_refl [(bv_unsigned sp - 544, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  (* [comment removed for export] *) carve_frame 112%nat ST. carve_frame (Z.to_nat 320) ST. carve_frame 112%nat ST.
  do 43 zs. name_junk FR. name_junk FR1.
  zto 0x9f998%Z.
  zs. brf Kc. { exfalso. apply Kc. reflexivity. }
  do 16 zs.
  release_frame FR1 ST (bv_unsigned sp + -432)%Z. release_frame FR0 ST (bv_unsigned sp + -112)%Z. release_frame FR ST (bv_unsigned sp).
  finish.
Qed.

Lemma pc1_rerr : pass1_stmt FMT_RERR 23.
Proof.
  unfold pass1_stmt. intros until canary. intros -> -> -> -> ST FMT_RERRH [SSP1 SSP2] MI LO SPH APR NAR NTR AG GT.
  unfold GOT_SSP, SSP_GUARD, FMT_RERR, GLOBALS_TOP, PRINTF_CORE, PC1_DEPTH in *.
  pose proof (ro_cells_bound _ _ _ _ FMT_RERRH) as AB. cbn [cells_size csize Nat.add] in AB.
  pose proof (munch_refl [(bv_unsigned sp - 544, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  (* [comment removed for export] *) carve_frame 112%nat ST. carve_frame (Z.to_nat 320) ST. carve_frame 112%nat ST.
  do 43 zs. name_junk FR. name_junk FR1.
  zto 0x9f998%Z.
  zs. brf Kc. { exfalso. apply Kc. reflexivity. }
  do 16 zs.
  release_frame FR1 ST (bv_unsigned sp + -432)%Z. release_frame FR0 ST (bv_unsigned sp + -112)%Z. release_frame FR ST (bv_unsigned sp).
  finish.
Qed.

Lemma pc1_refused : pass1_stmt FMT_REFUSED 33.
Proof.
  unfold pass1_stmt. intros until canary. intros -> -> -> -> ST FMT_REFUSEDH [SSP1 SSP2] MI LO SPH APR NAR NTR AG GT.
  unfold GOT_SSP, SSP_GUARD, FMT_REFUSED, GLOBALS_TOP, PRINTF_CORE, PC1_DEPTH in *.
  pose proof (ro_cells_bound _ _ _ _ FMT_REFUSEDH) as AB. cbn [cells_size csize Nat.add] in AB.
  pose proof (munch_refl [(bv_unsigned sp - 544, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  (* [comment removed for export] *) carve_frame 112%nat ST. carve_frame (Z.to_nat 320) ST. carve_frame 112%nat ST.
  do 43 zs. name_junk FR. name_junk FR1.
  zto 0x9f998%Z.
  zs. brf Kc. { exfalso. apply Kc. reflexivity. }
  do 16 zs.
  release_frame FR1 ST (bv_unsigned sp + -432)%Z. release_frame FR0 ST (bv_unsigned sp + -112)%Z. release_frame FR ST (bv_unsigned sp).
  finish.
Qed.

End CEIL.

