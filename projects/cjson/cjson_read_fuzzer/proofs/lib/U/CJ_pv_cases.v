(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import UImg CJ_iface CJ_tree CJ_print_iface CJ_pv_common CJ_pv_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Definition pv_case_at (entry : Z) (HI : cj_heap_iface) (n : nat) : Prop :=
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
         (m : word -> option byte) (SPB : Z) (LR B : list cblock) (p PB dep : Z) (fw : word) (lo : Z),
    pb_place (bv_unsigned sp) PB SPB -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - PV_STACK n -> tp = wz PTP ->
    bv_unsigned sp <= 2^64 -> (1 <= n)%nat -> (forall b, In b B -> In b LR) -> bv_unsigned sp mod 16 = 0 ->
    dep + Z.of_nat n <= 2^40 -> 0 <= dep -> p <> 0 -> cj_chain CJ_PRINTABLE m n p B ->
    (forall d, (d < n)%nat -> pvalue_spec_at HI d) ->
    forall mm mo loc Fc fcc errv LB buf len off bs
      (x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word),
    actx HI ra sp s0 s1 s2 s3 s4 s5 s6 s7 F m SPB LR PB fw lo dep mm mo loc Fc fcc errv LB buf len off bs ->
    SCPS usegs (pvalue_post HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F SPB LR B n p PB dep fw lo m)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 (Z_to_bv 64 PB) x9 x10 (Z_to_bv 64 p) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 entry) fcc None mm (seg_rom usegs)) mo.

Definition PV_ARR_ENTRY : Z := 0x14768.
Definition PV_OBJ_ENTRY : Z := 0x1445c.
Definition PV_NUM_ENTRY : Z := 0x14690.


End CeilWrap.
