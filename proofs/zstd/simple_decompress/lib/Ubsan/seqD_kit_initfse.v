(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface.
Import ListNotations.
Open Scope Z_scope.

Definition PZD_INITFSE : Z := 0x1db98.

Definition zd_initfse_post (ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (BD STP T SEQ n B tl : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 a1 a2 a3 a4 a5 a6 a7 m' cw' bc' jpad' ptr' st,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 STP) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(BD, BD + 40); (STP, STP + 16)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' BD (bitd_cells cw' (Z_to_bv 64 bc') jpad' ptr' SEQ)
    /\ rw_cells usegs m' STP [C8 (Z_to_bv 64 st); C8 (Z_to_bv 64 (T + 8))]
    /\ 0 <= st < 2^tl /\ 0 <= bc' <= B + 9
    /\ (bc' <= 64 -> ptr' = SEQ \/ (8 <= n /\ SEQ <= ptr' <= SEQ + n - 8)).

Definition zd_initfse_stmt_if (CND : Z -> Z -> Z -> Z -> Z -> Prop) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (BD STP T SEQ n B bc ptr : Z) (cw st0 tb0 : word)
         (jpad sqb : list byte) (k : seq_kind) (t : seq_table),
  mem_inv usegs m ->
  rw_cells usegs m BD (bitd_cells cw (Z_to_bv 64 bc) jpad ptr SEQ) -> rw_cells usegs m STP [C8 st0; C8 tb0] ->
  bytes_at usegs m T (map (Z_to_bv 8) (seq_table_bytes t)) -> seq_table_ok k t ->
  bytes_at usegs m SEQ sqb -> Z.of_nat (length sqb) = n -> 1 <= n ->
  4096 <= BD -> BD + 40 < 2^47 -> 4096 <= STP -> STP + 16 < 2^47 -> 4096 <= T -> T < 2^47 ->
  4096 <= SEQ -> SEQ + n < 2^47 ->
  BD mod 8 = 0 -> STP mod 8 = 0 -> T mod 4 = 0 ->
  (BD + 40 <= STP \/ STP + 16 <= BD) -> (BD + 40 <= SEQ \/ SEQ + n <= BD) -> (STP + 16 <= SEQ \/ SEQ + n <= STP) ->
  (BD + 40 <= T \/ T + 8 * (1 + 2^(st_log t)) <= BD) -> (STP + 16 <= T \/ T + 8 * (1 + 2^(st_log t)) <= STP) ->
  0 <= bc <= B -> B <= 82 -> (bc <= 64 -> ptr = SEQ \/ (8 <= n /\ SEQ <= ptr <= SEQ + n - 8)) ->
  CND bc (st_log t) ptr SEQ n ->
  evt usegs (zd_initfse_post ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc BD STP T SEQ n B (st_log t) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 STP) (Z_to_bv 64 BD) (Z_to_bv 64 T) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_INITFSE) fc None m (seg_rom usegs)).

Definition zd_initfse_stmt : Prop := zd_initfse_stmt_if (fun _ _ _ _ _ => True).
