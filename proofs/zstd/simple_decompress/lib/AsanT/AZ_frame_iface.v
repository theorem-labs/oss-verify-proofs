(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit ZdFrameW DrvAgree.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AZ_kit AZ_globals AZ_globalsR.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)
Notation GETCBLOCK_STACK_A := 16 (only parsing).   (* [comment removed for export] *)
Notation XXH_RESET_STACK_A := 2240 (only parsing).   (* [comment removed for export] *)     (* [comment removed for export] *)
Notation XXH_UPDATE_STACK_A := 2352 (only parsing).   (* [comment removed for export] *)    (* [comment removed for export] *)
Notation XXH_DIGEST_STACK_A := 64 (only parsing).   (* [comment removed for export] *)
(* [comment removed for export] *)
Notation GETFH_STACK_A := 4320 (only parsing).   (* [comment removed for export] *)     (* [comment removed for export] *)
Notation GETFH_DEPTH := 1 (only parsing).
Notation FINDFSI_STACK_A := 4672 (only parsing).   (* [comment removed for export] *)   (* [comment removed for export] *)
Notation FINDFSI_DEPTH := 2 (only parsing).
Notation FINDDSIZE_STACK_A := 5024 (only parsing).   (* [comment removed for export] *)   (* [comment removed for export] *)
Notation FINDDSIZE_DEPTH := 3 (only parsing).

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition APZD_FUZZ : Z := 0x82a28.          (* [comment removed for export] *)
Definition APZD_CREATEDCTX : Z := 0x82c9c.    (* [comment removed for export] *)
Definition APZD_FREEDCTX : Z := 0x83004.      (* [comment removed for export] *)
Definition APZD_GETFH : Z := 0x8324c.         (* [comment removed for export] *)
Definition APZD_FINDDSIZE : Z := 0x83c6c.     (* [comment removed for export] *)
Definition APZD_FINDFSI : Z := 0x840b4.       (* [comment removed for export] *)
Definition APZD_DMF : Z := 0x84750.           (* [comment removed for export] *)
Definition APZD_DDCTX : Z := 0x857f0.         (* [comment removed for export] *)
Definition APZD_DECODEFH : Z := 0x85980.      (* [comment removed for export] *)
Definition APZD_DBEGIN : Z := 0x86834.        (* [comment removed for export] *)
Definition APZD_FREEDDICT : Z := 0x87288.     (* [comment removed for export] *)
Definition APZD_GETCBLOCK : Z := 0x873b8.     (* [comment removed for export] *)
Definition APZD_DBLOCK : Z := 0x89360.        (* [comment removed for export] *)
Definition APZD_CHECKCONT : Z := 0x94e70.     (* [comment removed for export] *)
Definition APZD_ISERROR : Z := 0xae614.       (* [comment removed for export] *)
Definition APZD_ERRCODE : Z := 0xae620.       (* [comment removed for export] *)
Definition APZD_XXH_RESET : Z := 0xaf218.     (* [comment removed for export] *)
Definition APZD_XXH_UPDATE : Z := 0xaf2fc.    (* [comment removed for export] *)
Definition APZD_XXH_DIGEST : Z := 0xafcc4.    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zd_iserror_postA (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (c : Z) (m : amem) : machine_state -> Prop :=
  fun ms' =>
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.b2z (zd_is_error c))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom bsegs).

Definition zd_iserror_stmtA : Prop :=
  forall (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (c : Z),
  0 <= c < 2^64 -> a0 = Z_to_bv 64 c ->
  evtF bsegs RNG (zd_iserror_postA ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc c m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 APZD_ISERROR) fc None m (seg_rom bsegs)).

Definition zd_errcode_postA (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (c : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists a1',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (zd_error_code c)) a1' a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom bsegs).

Definition zd_errcode_stmtA : Prop :=
  forall (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (c : Z),
  0 <= c < 2^64 -> a0 = Z_to_bv 64 c ->
  evtF bsegs RNG (zd_errcode_postA ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc c m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 APZD_ERRCODE) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition bp_cells (bp : block_props) : list cell :=
  [C4 (Z_to_bv 64 (bp_type bp)); C4 (Z_to_bv 64 (bp_last bp)); C4 (Z_to_bv 64 (bp_orig bp))].

Definition zd_getcblock_postA (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV BP : Z) (src : list Z) (ip size lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' cs,
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (cblock_ret (get_cblock_size src ip size))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(BP, BP + 12); (SPV - GETCBLOCK_STACK_A, SPV)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV
    /\ rw_cells bsegs m' BP cs /\ cells_size cs = 12%nat
    /\ (forall v bp, get_cblock_size src ip size = Some (v, bp) -> cs = bp_cells bp).

Definition zd_getcblock_stmtA : Prop :=
  forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV SRC BP : Z) (src : list Z) (ip size : Z) (cs0 : list cell) (lo : Z),
  bytes_at bsegs m SRC (map (Z_to_bv 8) src) -> all_bytes src -> 0 <= ip -> 0 <= size -> ip + size <= zlen src -> 0 < SRC ->
  rw_cells bsegs m BP cs0 -> cells_size cs0 = 12%nat ->
  0 < BP -> BP mod 4 = 0 ->      (* [comment removed for export] *)
  stk bsegs m lo SPV -> lo <= SPV - GETCBLOCK_STACK_A -> SPV < 2^47 ->
  (BP + 12 <= lo \/ SPV <= BP) -> (SRC + zlen src <= lo \/ SPV <= SRC) ->
  (* [comment removed for export] *)
  areg RNG m SRC (zlen src) -> areg RNG m BP 12 -> art m -> astk RNG lo SPV ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 (SRC + ip) -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 BP ->
  evtF bsegs RNG (zd_getcblock_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV BP src ip size lo m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 APZD_GETCBLOCK) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition xxh_cells (j1 : list byte) (ms : Z) (j2 : list byte) : list cell := [CB 72 j1; C4 (Z_to_bv 64 ms); CB 12 j2].
Definition xxh_state (m : amem) (STA ms : Z) : Prop := exists j1 j2, rw_cells bsegs m STA (xxh_cells j1 ms j2).

Definition zd_xxh_reset_postA (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV STA lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(STA, STA + 88); (SPV - XXH_RESET_STACK_A, SPV)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV
    /\ xxh_state m' STA 0.

Definition zd_xxh_reset_stmtA : Prop :=
  forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV STA : Z) (cs0 : list cell) (lo : Z),
  rw_cells bsegs m STA cs0 -> cells_size cs0 = 88%nat -> 4096 <= STA -> STA mod 8 = 0 -> STA + 88 <= 2^47 ->
  stk bsegs m lo SPV -> lo <= SPV - XXH_RESET_STACK_A -> SPV < 2^47 ->
  (STA + 88 <= lo \/ SPV <= STA) ->
  (* [comment removed for export] *)
  areg RNG m STA 88 -> ahull RNG m STA 88 -> art m -> astk RNG lo SPV ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 STA ->
  evtF bsegs RNG (zd_xxh_reset_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV STA lo m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 APZD_XXH_RESET) fc None m (seg_rom bsegs)).

Definition zd_xxh_update_postA (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV STA lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' msz,
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(STA, STA + 88); (SPV - XXH_UPDATE_STACK_A, SPV)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV
    /\ xxh_state m' STA msz /\ 0 <= msz < 32.

(* [comment removed for export] *)
Definition zd_xxh_update_stmtA : Prop :=
  forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV STA IN : Z) (inb : list byte) (msz lo : Z),
  xxh_state m STA msz -> 0 <= msz < 32 -> 4096 <= STA -> STA mod 8 = 0 -> STA + 88 <= 2^47 ->
  ((IN = 0 /\ a2 = Z_to_bv 64 0)
   \/ (bytes_at bsegs m IN inb /\ a2 = Z_to_bv 64 (zlen inb) /\ 4096 <= IN /\ IN + zlen inb <= 2^47 /\
       (STA + 88 <= IN \/ IN + zlen inb <= STA) /\ (IN + zlen inb <= lo \/ SPV <= IN) /\
       areg RNG m IN (zlen inb) /\ ahull RNG m IN (zlen inb))) ->
  stk bsegs m lo SPV -> 4096 <= lo -> lo <= SPV - XXH_UPDATE_STACK_A -> SPV < 2^47 ->
  (STA + 88 <= lo \/ SPV <= STA) ->
  (* [comment removed for export] *)
  areg RNG m STA 88 -> ahull RNG m STA 88 -> art m -> astk RNG lo SPV ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 STA -> a1 = Z_to_bv 64 IN ->
  evtF bsegs RNG (zd_xxh_update_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV STA lo m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 APZD_XXH_UPDATE) fc None m (seg_rom bsegs)).

Definition zd_xxh_digest_postA (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(SPV - XXH_DIGEST_STACK_A, SPV)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV.

Definition zd_xxh_digest_stmtA : Prop :=
  forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV STA : Z) (st : list byte) (lo : Z),
  bytes_at bsegs m STA st -> zlen st = 88 -> 4096 <= STA -> STA mod 8 = 0 -> STA + 88 <= 2^47 ->
  stk bsegs m lo SPV -> lo <= SPV - XXH_DIGEST_STACK_A -> SPV < 2^47 ->
  (STA + 88 <= lo \/ SPV <= STA) ->
  (* [comment removed for export] *)
  areg RNG m STA 88 -> art m -> astk RNG lo SPV ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 STA ->
  evtF bsegs RNG (zd_xxh_digest_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV lo m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 APZD_XXH_DIGEST) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section StmtsF.
Variable AI : AMallocIface.
Variable fflag : alayout -> Z -> Z -> Z.         (* [comment removed for export] *)
Variable rng_fs : alayout -> footprint -> Prop.   (* [comment removed for export] *)

(* [comment removed for export] *)

Definition zfh_cells (h : frame_header) : list cell :=
  [C8 (Z_to_bv 64 (fh_fcs h)); C8 (Z_to_bv 64 (fh_window h)); C4 (Z_to_bv 64 (fh_bsmax h)); C4 (Z_to_bv 64 (fh_type h));
   C4 (Z_to_bv 64 (fh_hsize h)); C4 (Z_to_bv 64 (fh_dictID h)); C4 (Z_to_bv 64 (fh_checksum h)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Definition zd_getfh_postA (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV ZFH : Z) (src : list Z) (off size lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' cs,
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fh_retval (get_frame_header src off size))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch ([(ZFH, ZFH + 48); (SPV - GETFH_STACK_A, SPV)] ++ fake_area L) m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV
    /\ ffr_pres [(ZFH, ZFH + 48)] LB m m' /\ AHEAP AI L RNG st LB m'
    /\ rw_cells bsegs m' ZFH cs /\ cells_size cs = 48%nat
    /\ (forall h, get_frame_header src off size = FH_ok h -> cs = zfh_cells h).

Definition zd_getfh_stmtA : Prop :=
  forall (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
         (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV ZFH SRC : Z) (src : list Z) (off size : Z) (cs0 : list cell) (lo : Z),
  bytes_at bsegs m SRC (map (Z_to_bv 8) src) -> all_bytes src -> 0 <= off -> 5 <= size -> off + size <= zlen src -> 0 < SRC ->
  rw_cells bsegs m ZFH cs0 -> cells_size cs0 = 48%nat -> ZFH mod 8 = 0 ->      (* [comment removed for export] *)
  stk bsegs m lo SPV -> lo <= SPV - GETFH_STACK_A ->
  (ZFH + 48 <= lo \/ SPV <= ZFH) -> (SRC + zlen src <= lo \/ SPV <= SRC) ->
  (ZFH + 48 <= SRC \/ SRC + zlen src <= ZFH) ->
  (* [comment removed for export] *)
  afpre AI rng_fs L RNG st LB m lo SPV GETFH_DEPTH -> aro_client RNG m ->
  areg RNG m SRC (zlen src) -> (0 < zlen src -> ainimg LB SRC (zlen src)) ->
  ZFH mod 8 = 0 ->      (* [comment removed for export] *)
  areg RNG m ZFH 48 -> ahull RNG m ZFH 48 -> ainblk LB ZFH 48 ->
  mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 ZFH -> a1 = Z_to_bv 64 (SRC + off) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 0 ->
  evtF bsegs RNG (zd_getfh_postA L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV ZFH src off size lo m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 APZD_GETFH) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)

Definition zd_findfsi_postA (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV FSIP : Z) (src : list Z) (off size lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' j0,
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch ([(FSIP, FSIP + 24); (SPV - FINDFSI_STACK_A, SPV)] ++ fake_area L) m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV
    /\ ffr_pres [(FSIP, FSIP + 24)] LB m m' /\ AHEAP AI L RNG st LB m'
    /\ rw_cells bsegs m' FSIP [CB 8 j0; C8 (Z_to_bv 64 (fsi_csize (find_frame_size_info src off size)));
                               C8 (Z_to_bv 64 (fsi_bound (find_frame_size_info src off size)))].

Definition zd_findfsi_stmtA : Prop :=
  forall (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
         (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV FSIP SRC : Z) (src : list Z) (off size : Z) (cs0 : list cell) (lo : Z),
  bytes_at bsegs m SRC (map (Z_to_bv 8) src) -> all_bytes src -> 0 <= off -> 5 <= size -> size < 2^40 -> off + size <= zlen src ->
  0 < SRC -> SRC + zlen src < 2^64 ->
  rw_cells bsegs m FSIP cs0 -> cells_size cs0 = 24%nat ->
  stk bsegs m lo SPV -> lo <= SPV - FINDFSI_STACK_A ->
  (* [comment removed for export] *)
  SPV <= FSIP -> KHIGH <= FSIP -> FSIP + 32 <= 2^47 -> (SRC + zlen src <= lo \/ SPV <= SRC) ->
  (FSIP + 24 <= SRC \/ SRC + zlen src <= FSIP) ->
  (* [comment removed for export] *)
  afpre AI rng_fs L RNG st LB m lo SPV FINDFSI_DEPTH -> aro_client RNG m ->
  areg RNG m SRC (zlen src) -> (0 < zlen src -> ainimg LB SRC (zlen src)) ->
  FSIP mod 8 = 0 ->     (* [comment removed for export] *)
  aro RNG m FSIP 24 ->
  mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 FSIP -> a1 = Z_to_bv 64 (SRC + off) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 0 ->
  evtF bsegs RNG (zd_findfsi_postA L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV FSIP src off size lo m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 APZD_FINDFSI) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)

Definition zd_finddsize_postA (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV : Z) (src : list Z) (size lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (find_decompressed_size src size)) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch ((SPV - FINDDSIZE_STACK_A, SPV) :: fake_area L) m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV
    /\ ffr_pres [] LB m m' /\ AHEAP AI L RNG st LB m'.

Definition zd_finddsize_stmtA : Prop :=
  forall (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
         (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV SRC : Z) (src : list Z) (size lo : Z),
  bytes_at bsegs m SRC (map (Z_to_bv 8) src) -> all_bytes src -> 0 <= size -> size < 2^40 -> size <= zlen src ->
  0 < SRC -> SRC + zlen src < 2^64 ->
  stk bsegs m lo SPV -> lo <= SPV - FINDDSIZE_STACK_A ->
  (SRC + zlen src <= lo \/ SPV <= SRC) ->
  (* [comment removed for export] *)
  afpre AI rng_fs L RNG st LB m lo SPV FINDDSIZE_DEPTH -> aro_client RNG m ->
  azstk RNG m lo SPV ->   (* [comment removed for export] *)
  areg RNG m SRC (zlen src) -> (0 < zlen src -> ainimg LB SRC (zlen src)) ->
  mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 SRC -> a1 = Z_to_bv 64 size ->
  evtF bsegs RNG (zd_finddsize_postA L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV src size lo m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 APZD_FINDDSIZE) fc None m (seg_rom bsegs)).
End StmtsF.
End CANSEC1.
