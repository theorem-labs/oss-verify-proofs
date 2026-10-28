(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount HufPure_FseDecomp.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AFake0k_iface
  AF_fse_rd_iface AF_huf_tbl_iface AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_tbl_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AFSE_INIT_DSTATE : Z := 0x9a57c.   (* [comment removed for export] *)
Definition ABIT_INIT_F : Z := 0x99fa8.        (* [comment removed for export] *)
Definition AFSE_DECOMP : Z := 0x98160.        (* [comment removed for export] *)
Definition ABIT_MASK : Z := 0x20ea0.          (* [comment removed for export] *)
Definition AZEROFILLED : Z := 0x20f40.        (* [comment removed for export] *)
Definition AFSE_INIT_STACK : Z := 16.
Definition ABIT_INIT_STACK : Z := 2240.       (* [comment removed for export] *)
(* [comment removed for export] *)
Definition AFSE_DECOMP_STACK : Z := 8704.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bitdz_cellsA (S : Z) (d : bitD) (jp : list byte) : list cell :=
  [C8 (Z_to_bv 64 (bd_cont d)); C4 (Z_to_bv 64 (bd_bits d)); CB 4 jp;
   C8 (Z_to_bv 64 (if bd_zero d then AZEROFILLED else S + bd_ptr d)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fse_init_dstate_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (DS BD DT S : Z) (v : Z) (d2 : bitD) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (jp : list byte) (m' : amem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - AFSE_INIT_STACK, bv_unsigned sp); (DS, DS + 16); (BD, BD + 40)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' DS [C8 (Z_to_bv 64 v); C8 (Z_to_bv 64 (DT + 4))]
    /\ rw_cells bsegs m' BD (bitdz_cellsA S d2 jp).

Definition fse_init_dstate_stmtA : Prop :=
  forall (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (DS BD DT S tl : Z) (bs : list Z) (d : bitD) (jds jp : list byte)
         (fmw : word) (v : Z) (d1 : bitD) (st : dstatus) (d2 : bitD) (lo : Z),
  (* [comment removed for export] *)
  rw_cells bsegs m DS [CB 16 jds] -> rw_cells bsegs m BD (bitdz_cellsA S d jp) ->
  rw_cells bsegs m DT [C2 (Z_to_bv 64 tl); C2 fmw] ->
  bytes_at bsegs m S (map (Z_to_bv 8) bs) -> Forall (fun c => 0 <= c < 256) bs ->
  (* [comment removed for export] *)
  0 <= tl <= 12 -> bitd_ok bs d ->
  read_bits d tl = Ok (v, d1) -> reload_dstream bs d1 = Ok (st, d2) ->
  (* [comment removed for export] *)
  bv_unsigned sp <= DS -> DS mod 8 = 0 -> DS + 16 <= BD -> BD mod 8 = 0 -> BD + 48 <= 2^47 ->
  ablk DT (DT + 4) -> DT mod 4 = 0 -> ablk S (S + zlen bs) -> S + 8 <= 2^47 ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFSE_INIT_STACK ->
  mem_inv bsegs m -> artcells m ->
  (* [comment removed for export] *)
  zshadow m DS 16 -> zshadow m BD 40 -> zshadow m DT 4 -> zshadow m ABIT_MASK 128 ->
  unpoisoned m S (S + zlen bs) ->
  (* [comment removed for export] *)
  rng RNG DS 16 -> rng RNG (shad DS) 2 -> rng RNG BD 40 -> rng RNG (shad BD) 5 -> rng RNG DT 4 -> rng RNG (shad DT) 1 ->
  rng RNG S (zlen bs) -> rng RNG (shad S) (nshad (zlen bs + S mod 8)) ->
  rng RNG (bv_unsigned sp - AFSE_INIT_STACK) AFSE_INIT_STACK -> rng_aimg RNG -> rng_aimg_sh RNG ->
  a0 = Z_to_bv 64 DS -> a1 = Z_to_bv 64 BD -> a2 = Z_to_bv 64 DT ->
  evtF bsegs RNG (fse_init_dstate_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DS BD DT S v d2 lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AFSE_INIT_DSTATE) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bit_init_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (D S : Z) (bs : list Z) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (ret : Z) (m' : amem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ret) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - ABIT_INIT_STACK, bv_unsigned sp); (D, D + 40)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ bytes_at bsegs m' S (map (Z_to_bv 8) bs)
    /\ match init_dstream bs with
       | Ok d => ret = zlen bs /\ bd_zero d = false /\ exists jp, rw_cells bsegs m' D (bitdz_cellsA S d jp)
       | Err e => ret = - e /\ exists j', rw_cells bsegs m' D [CB 40 j']
       | Ub | NoFuel => False
       end.

Definition bit_init_stmtA (E : Z) : Prop :=
  forall (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (D S : Z) (bs : list Z) (j : list byte) (lo RLO RHI : Z),
  rw_cells bsegs m D [CB 40 j] -> D mod 8 = 0 ->
  bytes_at bsegs m S (map (Z_to_bv 8) bs) -> Forall (fun c => 0 <= c < 256) bs ->
  (* [comment removed for export] *)
  bv_unsigned sp <= D -> D + 48 <= 2^47 -> (0 < zlen bs -> ablk S (S + zlen bs) /\ S + 8 <= 2^47) ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - ABIT_INIT_STACK ->
  mem_inv bsegs m -> artcells m ->
  (* [comment removed for export] *)
  shclean m D (D + 40) RLO RHI -> unpoisoned m S (S + zlen bs) ->
  (* [comment removed for export] *)
  rng RNG D 40 -> rng RNG (shad D) 5 -> (0 < zlen bs -> rng RNG S (zlen bs) /\ rng RNG (shad S) (nshad (zlen bs + S mod 8))) ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad RLO) (shad RHI - shad RLO) -> rng_aimg RNG ->
  a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlen bs) ->
  evtF bsegs RNG (bit_init_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D S bs lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 E) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Stmts.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.

Definition fse_decomp_postA (L : alayout) (RNG : footprint)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (SPV DST dcap W wks maxLog : Z) (src : list Z) (lo : Z) (m : amem)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (r : Z) (m' : amem),
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo SPV
    /\ magree bsegs (fun a => aclient_addr CI LB SPV a /\ ~ (DST <= a < DST + dcap) /\ ~ (W <= a < W + wks)) m m'
    /\ AHEAP AI L RNG st LB m'
    /\ 0 <= r < 2^64
    /\ match fse_decompress_wksp (repeat 0 256) dcap src maxLog wks with
       | Ok l => r = zlen l /\ exists jrest, u8arr bsegs m' DST (map (Z_to_bv 8) l ++ jrest) /\ zlen jrest = dcap - zlen l
       | Err e => r = 2^64 - e /\ 0 < e < 120
       | Ub | NoFuel => False
       end.

Definition fse_decomp_stmtA (k : nat) : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock)
         (SPV DST dcap S W wks maxLog : Z) (src : list Z) (jd jw : list byte) (lo : Z) (rstk : region),
  AHEAP AI L RNG st LB m ->
  fake0_lek k LB ->                                         (* [comment removed for export] *)
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  (* [comment removed for export] *)
  u8arr bsegs m DST jd -> zlen jd = dcap ->
  bytes_at bsegs m S (map (Z_to_bv 8) src) -> Forall (fun c => 0 <= c < 256) src ->
  u8arr bsegs m W jw -> zlen jw = wks ->
  0 <= dcap <= 255 -> zlen src <= 65536 -> 0 <= maxLog <= 12 -> wks < 2^32 ->
  (* [comment removed for export] *)
  hblk8 LB DST dcap -> hblk8 LB W wks -> W mod 8 = 0 ->
  bufH LB S (zlen src) -> 16 <= S ->
  (DST + dcap <= S \/ S + zlen src <= DST) -> (DST + dcap <= W \/ W + wks <= DST) -> (S + zlen src <= W \/ W + wks <= S) ->
  (* [comment removed for export] *)
  stk bsegs m lo SPV -> ATOP + 4096 <= lo -> lo <= SPV - AFSE_DECOMP_STACK ->
  SPV + 16 < al_top L -> SPV mod 16 = 0 ->
  rclean m rstk -> r_lo rstk <= lo -> SPV <= r_hi rstk -> ATOP <= r_rlo rstk ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  (* [comment removed for export] *)
  zshadow m ABIT_MASK 128 -> (forall a, ABIT_MASK <= a < ABIT_MASK + 128 -> in_ranges CI a) ->
  (* [comment removed for export] *)
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG -> rrng RNG rstk ->
  evtF bsegs RNG (fse_decomp_postA L RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB SPV DST dcap W wks maxLog src lo m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 S) (Z_to_bv 64 (zlen src))
                (Z_to_bv 64 maxLog) (Z_to_bv 64 W) (Z_to_bv 64 wks) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 AFSE_DECOMP) fc None m (seg_rom bsegs)).
End Stmts.
End CANSEC1.
