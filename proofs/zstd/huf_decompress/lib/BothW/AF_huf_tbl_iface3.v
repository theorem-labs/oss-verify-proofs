(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount HufPure_FseDecomp HufPure_HufStats.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AFake0k_iface
  AF_fse_rd_iface AF_huf_tbl_iface AF_huf_tbl_iface2 AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AHUF_RSTATS : Z := 0x9733c.        (* [comment removed for export] *)
Definition AHUF_RSTATS_STACK : Z := 8832.     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Stmts.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable rng_fs : alayout -> footprint -> Prop.

Definition huf_rstats_postA (L : alayout) (RNG : footprint)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (SPV HW RK NSP TLP W : Z) (src : list Z) (lo : Z) (m : amem)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (r : Z) (m' : amem),
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo SPV
    /\ magree bsegs (fun a => aclient_addr CI LB SPV a /\ ~ (HW <= a < HW + 256) /\ ~ (RK <= a < RK + 52)
                              /\ ~ (NSP <= a < NSP + 4) /\ ~ (TLP <= a < TLP + 4) /\ ~ (W <= a < W + 876)) m m'
    /\ AHEAP AI L RNG st LB m'
    /\ 0 <= r < 2^64
    /\ match read_stats src with
       | Ok h => r = hs_ret h
                 /\ (exists jrest, u8arr bsegs m' HW (map (Z_to_bv 8) (hs_weights h) ++ jrest)
                                   /\ zlen jrest = 256 - hs_nbSymbols h)
                 /\ u32arr bsegs m' RK (map (Z_to_bv 64) (hs_rank h))
                 /\ rw_cells bsegs m' NSP [C4 (Z_to_bv 64 (hs_nbSymbols h))]
                 /\ rw_cells bsegs m' TLP [C4 (Z_to_bv 64 (hs_tableLog h))]
       | Err e => r = 2^64 - e /\ 0 < e < 120
       | Ub | NoFuel => False
       end.

Definition huf_rstats_stmtA (k : nat) : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock)
         (SPV HW RK NSP TLP S W : Z) (src : list Z) (jh jr jw : list byte) (nsv tlv : word) (lo : Z) (rstk : region),
  AHEAP AI L RNG st LB m ->
  fake0_lek k LB ->                                         (* [comment removed for export] *)
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  (* [comment removed for export] *)
  u8arr bsegs m HW jh -> zlen jh = 256 ->
  u8arr bsegs m RK jr -> zlen jr = 52 ->
  rw_cells bsegs m NSP [C4 nsv] -> rw_cells bsegs m TLP [C4 tlv] ->
  bytes_at bsegs m S (map (Z_to_bv 8) src) -> Forall (fun c => 0 <= c < 256) src -> zlen src < 2^26 ->
  u8arr bsegs m W jw -> zlen jw = 876 ->
  rw_cells bsegs m SPV [C8 (Z_to_bv 64 876)] ->
  (* [comment removed for export] *)
  hblk8 LB HW 256 -> hblk8 LB RK 52 -> RK mod 4 = 0 -> hblk8 LB W 876 -> W mod 8 = 0 ->
  fcellA m LB NSP 4 -> NSP mod 4 = 0 -> fcellA m LB TLP 4 -> TLP mod 4 = 0 ->
  (0 < zlen src -> bufH LB S (zlen src)) -> 15 <= S ->
  (HW + 256 <= RK \/ RK + 52 <= HW) -> (HW + 256 <= S \/ S + zlen src <= HW) -> (HW + 256 <= W \/ W + 876 <= HW) ->
  (RK + 52 <= S \/ S + zlen src <= RK) -> (RK + 52 <= W \/ W + 876 <= RK) -> (S + zlen src <= W \/ W + 876 <= S) ->
  (NSP + 4 <= TLP \/ TLP + 4 <= NSP) ->
  (* [comment removed for export] *)
  stk bsegs m lo SPV -> ATOP + 4096 <= lo -> lo <= SPV - AHUF_RSTATS_STACK ->
  SPV + 16 < al_top L -> SPV mod 16 = 0 ->
  rclean m rstk -> r_lo rstk <= lo -> SPV <= r_hi rstk -> ATOP <= r_rlo rstk ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  (* [comment removed for export] *)
  zshadow m ABIT_MASK 128 -> (forall a, ABIT_MASK <= a < ABIT_MASK + 128 -> in_ranges CI a) ->
  (* [comment removed for export] *)
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG -> rrng RNG rstk ->
  rng RNG NSP 4 -> rng RNG (shad NSP) 1 -> rng RNG TLP 4 -> rng RNG (shad TLP) 1 ->
  evtF bsegs RNG (huf_rstats_postA L RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB SPV HW RK NSP TLP W src lo m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 HW) (Z_to_bv 64 256) (Z_to_bv 64 RK) (Z_to_bv 64 NSP)
                (Z_to_bv 64 TLP) (Z_to_bv 64 S) (Z_to_bv 64 (zlen src)) (Z_to_bv 64 W) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 AHUF_RSTATS) fc None m (seg_rom bsegs)).
End Stmts.
End CANSEC1.
