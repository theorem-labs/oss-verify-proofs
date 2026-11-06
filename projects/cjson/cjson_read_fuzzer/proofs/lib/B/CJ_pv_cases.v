(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs CJ_iface AShadow CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_pbuf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_fuzz_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_fuzz_iface.CJ_print_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_pv_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Definition ASHBASE : Z := 0x7fff8000.

(* [comment removed for export] *)
Definition PVPOST (Q : pvi) : machine_state -> Model -> lghost -> Prop :=
  pvalue_post (q_ai Q) (q_ti Q) (q_ra Q) (q_sp Q) (q_gp Q) (q_tp Q) (q_s0 Q) (q_s1 Q) (q_s2 Q) (q_s3 Q) (q_s4 Q) (q_s5 Q)
              (q_s6 Q) (q_s7 Q) (q_s8 Q) (q_s9 Q) (q_s10 Q) (q_s11 Q) (q_F Q) (q_sp0 Q) (q_SPB Q) (q_LR Q) (q_B Q) (q_LF Q)
              (q_np0 Q) (q_BB Q) (q_CH Q) (q_n Q) (q_p Q) (q_PB Q) (q_len0 Q) (q_dep Q) (q_fw Q) (q_lo Q) (q_m Q) (q_g Q).

(* [comment removed for export] *)
Definition CASE_ST (Q : pvi) (entry : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x27 x28 x29 x30 x31 : word)
    (Fx : bvmap 5 word) (fcx : bv 32) (mm : word -> option byte) : machine_state :=
  MS (mkR x1 (Z_to_bv 64 (q_SA Q)) (q_gp Q) (q_tp Q) x5 x6 x7 (q_sp Q) (Z_to_bv 64 (q_SA Q)) x10 x11 x12 x13 x14 x15 x16 x17
          (Z_to_bv 64 (q_Fr Q)) (Z_to_bv 64 (q_PB Q)) (Z_to_bv 64 ASHBASE) (Z_to_bv 64 (q_p Q)) x22 x23 x24 (SHR (q_Fr Q)) (Z_to_bv 64 (q_Fr Q))
          x27 x28 x29 x30 x31)
     Fx (Z_to_bv 64 entry) fcx None mm (seg_rom bsegs).

Definition pv_case_at (entry : Z) (Q : pvi) : Prop :=
  forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb Fx fcx
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x27 x28 x29 x30 x31 : word),
    PVX Q (q_dep Q) mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb SHP_IDLE Fx fcx ->
    LSCPS bsegs (PVPOST Q) (CASE_ST Q entry x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x27 x28 x29 x30 x31 Fx fcx mm) mo1 g1.


End CeilWrap.
