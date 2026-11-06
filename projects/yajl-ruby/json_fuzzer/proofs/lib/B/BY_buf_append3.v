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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep SFW1_lemmas.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlLeaf YajlBuf YajlFactsBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BI_shadow BYajlRep BYajl_iface BY_rz BY_buf_append1 BY_buf_append2.
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
Definition AAPP_ERR : Z := 0x874b8.      (* [comment removed for export] *)
Definition AAPP_ERR2 : Z := 0x874b8.     (* [comment removed for export] *)
Definition AAPP_ERR3 : Z := 0x874b8.     (* [comment removed for export] *)

(* [comment removed for export] *)
End RC__1.
Ltac shadow_at BS E w :=
  let HR := fresh "SHR" in
  lazymatch goal with
  | |- evtA ?segs _ _ (MS _ _ _ _ _ ?m _) =>
      lazymatch type of BS with
      | u8arr _ _ (?SB + ?A / 8) ?shb =>
          lazymatch goal with
          | Eshb : shb = blk_shadow ?n |- _ =>
              assert (HR : ov_read_bytes segs m (Z_to_bv 64 (SB + E / 8)) 1 = Some [Z_to_bv 8 0])
                by (apply (block_shadow_read0_u segs m SB A n E w); [lia| lia| rewrite <- Eshb; exact BS| lia| lia| lia| lia])
          end
      end
  end.
Ltac shadow_ld := let HR := lazymatch goal with H : ov_read_bytes _ _ _ 1 = Some [Z_to_bv 8 0] |- _ => H end in
  zstepA; clear HR; rewrite ?zxb_small, ?sxb_small by lia.
