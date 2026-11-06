(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf YajlLex YajlParser YajlFactsBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 AImages Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BY_ubkit B_iface BI_shadow BYajlRep BYajl_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Theorem ayset_default_proof : ayset_default_stmt.
Proof. aceil.
  unfold ayset_default_stmt. intros P YAF lo junk. intros until m.
  intros [YP YA8] STA YC OS SH1 SH2 MI ST LOC LO SPH -> PSTK PIMG PY.
  pose proof (land7_of_mod8 _ YA8) as L7.                          (* [comment removed for export] *)
  unfold wz in *. unfold AY_SET_DEFAULT.
  destruct STA as (G1 & G2 & G3 & G4). unfold AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz in G1, G2, G3, G4.
  aceil.
  unfold opol, pol, oshw_lo, oshw_hi, A_SB, amem in PSTK, PIMG, PY, SH1. unfold AY_IMG_LO, AY_IMG_HI in PIMG.
  change (2147450880 + 0 / 8 + (2 ^ 47 + 7) / 8) with 0x10007fff8000 in SH1.
  destruct PY as [PY PYS].
  pose proof (block_shadow_bound bsegs m _ _ _ OS) as BSB. unfold A_SB in BSB.
  unfold oshadow, A_SB in OS. open_shadow OS.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  assert (MU : munch [(lo, bv_unsigned sp); (YAF, YAF + 32)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  carve_frame 16%nat ST.
  stepA. stepA.                                (* [comment removed for export] *)
  zstepA. ubtrap K1. zstepA. zstepA. ubtrap K2. (* [comment removed for export] *)
  do 3 stepA.                                  (* [comment removed for export] *)
  shadow_fast OS YAF 8.                        (* [comment removed for export] *)
  stepA. zstepA. stepA.                        (* [comment removed for export] *)
  zstepA.                                      (* [comment removed for export] *)
  shadow_fast OS (YAF + 16) 8.                 (* [comment removed for export] *)
  stepA. zstepA. stepA.                        (* [comment removed for export] *)
  zstepA.                                      (* [comment removed for export] *)
  shadow_fast OS (YAF + 8) 8.                  (* [comment removed for export] *)
  stepA. stepA.                                (* [comment removed for export] *)
  zstepA.                                      (* [comment removed for export] *)
  zstepA.                                      (* [comment removed for export] *)
  shadow_fast OS (YAF + 24) 8.                 (* [comment removed for export] *)
  zstepA.                                      (* [comment removed for export] *)
  stepA. stepA. stepA.                         (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  unfold ayset_default_rpost. finishA.
  - unfold oshadow, block_shadow, A_SB. split; [assumption|]. split; [assumption|]. rewrite <- OSeq. assumption.
  - unfold ay_statics, AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz. split; [|split; [|split]]; assumption.
Qed.
End RC__1.
