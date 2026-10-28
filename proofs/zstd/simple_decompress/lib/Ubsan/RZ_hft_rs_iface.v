(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame ZdHufStats.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_hft_iface.
Import ListNotations.
Open Scope Z_scope.

Definition HUF_RSTATS_STACK : Z := 64 + 448.

Definition huf_rstats_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV HW RS NSP n WK wksz lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' r,
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(HW, HW + 256); (RS, RS + 52); (NSP, NSP + 8); (WK, WK + wksz); (SPV - 512, SPV)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SPV /\ stk usegs m' WK (WK + wksz) /\ 0 <= r < 2^64
    /\ ((zd_is_error r = false /\ 1 <= r <= n /\ exists hw rank tl nbs,
           u8arr usegs m' HW (map (Z_to_bv 8) hw) /\ zlen hw = 256 /\ Forall (fun v => 0 <= v < 256) hw /\
           u32arr usegs m' RS (map (Z_to_bv 64) rank) /\
           rw_cells usegs m' NSP [C4 (Z_to_bv 64 nbs); C4 (Z_to_bv 64 tl)] /\
           huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl /\ 2 <= nbs <= 256)
        \/ (zd_is_error r = true /\ stk usegs m' HW (HW + 256) /\ stk usegs m' RS (RS + 52) /\ stk usegs m' NSP (NSP + 8))).

Definition huf_rstats_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV HW RS NSP SRC n WK wksz lo B bsz : Z) (src : list byte),
  mem_inv usegs m ->
  stk usegs m lo SPV -> 4096 <= lo -> lo <= SPV - 512 -> SPV mod 16 = 0 ->
  bytes_at usegs m SPV (le8 (Z_to_bv 64 wksz)) ->
  stk usegs m HW (HW + 256) -> stk usegs m RS (RS + 52) -> stk usegs m NSP (NSP + 8) -> RS mod 4 = 0 -> NSP mod 4 = 0 ->
  bytes_at usegs m SRC src -> zlen src = n -> 4096 <= SRC -> n < 2^32 -> SRC + n < 2^47 ->
  stk usegs m WK (WK + wksz) -> 0 <= wksz < 2^32 -> WK mod 4 = 0 ->
  (* [comment removed for export] *)
  4096 <= B -> B + bsz < 2^47 -> B <= RS -> RS + 52 <= HW -> RS + 52 <= WK -> HW + 256 <= B + bsz -> WK + wksz <= B + bsz ->
  (WK + wksz <= HW \/ HW + 256 <= WK) ->
  (* [comment removed for export] *)
  SPV + 8 <= NSP -> NSP + 8 < 2^47 ->
  (* [comment removed for export] *)
  (B + bsz <= lo \/ SPV + 8 <= B) -> (B + bsz <= NSP \/ NSP + 8 <= B) -> (B + bsz <= SRC \/ SRC + n <= B) ->
  (NSP + 8 <= SRC \/ SRC + n <= NSP) -> (SRC + n <= lo \/ SPV <= SRC) ->
  evt usegs (huf_rstats_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV HW RS NSP n WK wksz lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 HW) (Z_to_bv 64 256) (Z_to_bv 64 RS) (Z_to_bv 64 NSP)
               (Z_to_bv 64 (NSP + 4)) (Z_to_bv 64 SRC) (Z_to_bv 64 n) (Z_to_bv 64 WK) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PHUF_RSTATS) fc None m (seg_rom usegs)).
