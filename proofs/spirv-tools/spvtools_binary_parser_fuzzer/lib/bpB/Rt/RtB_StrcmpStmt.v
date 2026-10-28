(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Bs0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BZBridge BacX BSFModel BSysStep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition ASTRCMP_STUB : Z := 0xa3684.

Section StrcmpStmt.
  Context {HCEIL : HeapCeil}.

  Definition astrcmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - AINTRIN_STACK, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ ACONST m'.

  Definition strcmp_icpt_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (e t rest1 rest2 : list Z) (lo : Z),
      bytes_at asegs m (bv_unsigned a0) (map b8 (e ++ 0 :: rest1)) -> Forall (fun c => 0 < c < 256) e ->
      bytes_at asegs m (bv_unsigned a1) (map b8 (t ++ 0 :: rest2)) -> Forall (fun c => 0 < c < 256) t ->
      accessible m (bv_unsigned a0) (Z.of_nat (length e) + 1) ->
      accessible m (bv_unsigned a1) (Z.of_nat (length t) + 1) ->
      shvis m (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (length e) + 1) ->
      shvis m (bv_unsigned a1) (bv_unsigned a1 + Z.of_nat (length t) + 1) ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AINTRIN_STACK ->
      mem_inv asegs m -> ACONST m ->
      Z.of_nat (length e) + 1 <= 2 ^ 40 -> Z.of_nat (length t) + 1 <= 2 ^ 40 ->
      in_app_mem (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (length e) + 1) ->
      in_app_mem (bv_unsigned a1) (bv_unsigned a1 + Z.of_nat (length t) + 1) ->
      (bv_unsigned a0 + Z.of_nat (length (e ++ 0 :: rest1)) <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
      (bv_unsigned a1 + Z.of_nat (length (t ++ 0 :: rest2)) <= lo \/ bv_unsigned sp <= bv_unsigned a1) ->
      evt asegs (astrcmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ASTRCMP_STUB) fc None m (seg_rom asegs)).
End StrcmpStmt.
