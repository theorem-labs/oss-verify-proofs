(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdHufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM ZdHufWR ZdHufWX ZdHufWY.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_hft_iface RZ_hft_x2_defs.
Import ListNotations.
Open Scope Z_scope.

Definition PHUF_FILLW : Z := 0x255fc.
Definition HUF_FILLW_STACK : Z := 48.

Definition huf_fillw_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SP lo DT : Z) (cw : list Z) (pos n v : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' cw',
    ms' = MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(DT + 4, DT + HUF_DTABLE_BYTES); (SP - HUF_FILLW_STACK, SP)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SP /\ x2_cells m' DT cw' /\ cells_written cw cw' pos n v.

Definition huf_fillw_stmt_at (ENTRY : Z) : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SP lo DT SYM : Z) (cw : list Z) (syb : list byte)
         (pos bg en nb tl lv bs : Z),
  mem_inv usegs m ->
  stk usegs m lo SP -> 4096 <= lo -> lo <= SP - HUF_FILLW_STACK -> SP < 2^47 ->
  x2_cells m DT cw -> 4096 <= DT -> DT + HUF_DTABLE_BYTES < 2^47 -> DT mod 2 = 0 ->
  (DT + HUF_DTABLE_BYTES <= lo \/ SP <= DT) ->
  bytes_at usegs m SYM syb -> 4096 <= SYM -> SYM + zlen syb < 2^47 ->
  (SYM + zlen syb <= lo \/ SP <= SYM) -> (DT + HUF_DTABLE_BYTES <= SYM \/ SYM + zlen syb <= DT) ->
  0 <= bg <= en -> en <= zlen syb ->
  0 <= nb <= tl -> tl <= 12 -> 0 <= pos -> pos + 2^(tl - nb) * (en - bg) <= 4096 ->
  (lv = 1 \/ lv = 2) -> 0 <= bs < 2^16 ->
  evt usegs (huf_fillw_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP lo DT cw pos (2^(tl - nb) * (en - bg)) (nb + 256 * lv) m)
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (DT + 4 + 4 * pos)) (Z_to_bv 64 (SYM + bg)) (Z_to_bv 64 (SYM + en))
               (Z_to_bv 64 nb) (Z_to_bv 64 tl) (Z_to_bv 64 bs) (Z_to_bv 64 lv) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom usegs)).

Definition huf_fillw_stmt : Prop := huf_fillw_stmt_at PHUF_FILLW.
