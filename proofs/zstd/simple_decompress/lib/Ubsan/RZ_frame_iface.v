(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit ZdFrameW.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg.
Import ListNotations.
Open Scope Z_scope.

Notation fmem := (word -> option byte).
Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PZD_FUZZ : Z := 0x14848.          (* [comment removed for export] *)
Definition PZD_CREATEDCTX : Z := 0x149a4.    (* [comment removed for export] *)
Definition PZD_FREEDCTX : Z := 0x14a68.      (* [comment removed for export] *)
Definition PZD_GETFH : Z := 0x14b90.         (* [comment removed for export] *)
Definition PZD_FINDDSIZE : Z := 0x150a8.     (* [comment removed for export] *)
Definition PZD_FINDFSI : Z := 0x1528c.       (* [comment removed for export] *)
Definition PZD_DMF : Z := 0x15488.           (* [comment removed for export] *)
Definition PZD_DDCTX : Z := 0x15b64.         (* [comment removed for export] *)
Definition PZD_DECODEFH : Z := 0x15a30.      (* [comment removed for export] *)
Definition PZD_DBEGIN : Z := 0x15f6c.        (* [comment removed for export] *)
Definition PZD_FREEDDICT : Z := 0x165dc.     (* [comment removed for export] *)
Definition PZD_GETCBLOCK : Z := 0x16690.     (* [comment removed for export] *)
Definition PZD_DBLOCK : Z := 0x1779c.        (* [comment removed for export] *)
Definition PZD_CHECKCONT : Z := 0x1d728.     (* [comment removed for export] *)
Definition PZD_ISERROR : Z := 0x2c39c.       (* [comment removed for export] *)
Definition PZD_ERRCODE : Z := 0x2c3a8.       (* [comment removed for export] *)
Definition PZD_XXH_RESET : Z := 0x2c988.     (* [comment removed for export] *)
Definition PZD_XXH_UPDATE : Z := 0x2ca24.    (* [comment removed for export] *)
Definition PZD_XXH_DIGEST : Z := 0x2d280.    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zd_iserror_post (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (c : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' =>
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.b2z (zd_is_error c))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom usegs).

Definition zd_iserror_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (c : Z),
  0 <= c < 2^64 -> a0 = Z_to_bv 64 c ->
  evt usegs (zd_iserror_post ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc c m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_ISERROR) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zd_errcode_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (c : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists a1',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (zd_error_code c)) a1' a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom usegs).

Definition zd_errcode_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (c : Z),
  0 <= c < 2^64 -> a0 = Z_to_bv 64 c ->
  evt usegs (zd_errcode_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc c m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_ERRCODE) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bp_cells (bp : block_props) : list cell :=
  [C4 (Z_to_bv 64 (bp_type bp)); C4 (Z_to_bv 64 (bp_last bp)); C4 (Z_to_bv 64 (bp_orig bp))].

Definition zd_getcblock_post (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (BP : Z) (src : list Z) (ip size : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 a4 a5 m' cs,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (cblock_ret (get_cblock_size src ip size))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(BP, BP + 12)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' BP cs /\ cells_size cs = 12%nat
    /\ (forall v bp, get_cblock_size src ip size = Some (v, bp) -> cs = bp_cells bp).

Definition zd_getcblock_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SRC BP : Z) (src : list Z) (ip size : Z) (cs0 : list cell),
  bytes_at usegs m SRC (map (Z_to_bv 8) src) -> all_bytes src -> 0 <= ip -> 0 <= size -> ip + size <= zlen src -> 0 < SRC ->
  rw_cells usegs m BP cs0 -> cells_size cs0 = 12%nat -> 0 < BP -> BP mod 4 = 0 ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 (SRC + ip) -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 BP ->
  evt usegs (zd_getcblock_post ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc BP src ip size m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_GETCBLOCK) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Notation GETFH_STACK := 48 (only parsing).

Definition zfh_cells (h : frame_header) : list cell :=
  [C8 (Z_to_bv 64 (fh_fcs h)); C8 (Z_to_bv 64 (fh_window h)); C4 (Z_to_bv 64 (fh_bsmax h)); C4 (Z_to_bv 64 (fh_type h));
   C4 (Z_to_bv 64 (fh_hsize h)); C4 (Z_to_bv 64 (fh_dictID h)); C4 (Z_to_bv 64 (fh_checksum h)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Definition zd_getfh_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV ZFH : Z) (src : list Z) (off size lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 m' cs,
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fh_retval (get_frame_header src off size))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(ZFH, ZFH + 48); (SPV - GETFH_STACK, SPV)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SPV
    /\ rw_cells usegs m' ZFH cs /\ cells_size cs = 48%nat
    /\ (forall h, get_frame_header src off size = FH_ok h -> cs = zfh_cells h).

Definition zd_getfh_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV ZFH SRC : Z) (src : list Z) (off size : Z) (cs0 : list cell) (lo : Z),
  bytes_at usegs m SRC (map (Z_to_bv 8) src) -> all_bytes src -> 0 <= off -> 5 <= size -> off + size <= zlen src -> 0 < SRC ->
  rw_cells usegs m ZFH cs0 -> cells_size cs0 = 48%nat -> ZFH mod 8 = 0 ->
  stk usegs m lo SPV -> lo <= SPV - GETFH_STACK -> 0 <= SPV < 2^64 ->
  (ZFH + 48 <= lo \/ SPV <= ZFH) -> (SRC + zlen src <= lo \/ SPV <= SRC) ->
  (ZFH + 48 <= SRC \/ SRC + zlen src <= ZFH) ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 ZFH -> a1 = Z_to_bv 64 (SRC + off) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 0 ->
  evt usegs (zd_getfh_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc SPV ZFH src off size lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_GETFH) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Notation FINDFSI_STACK := 176 (only parsing).   (* [comment removed for export] *)

Definition zd_findfsi_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV FSIP : Z) (src : list Z) (off size lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 m' j0,
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(FSIP, FSIP + 24); (SPV - FINDFSI_STACK, SPV)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SPV
    /\ rw_cells usegs m' FSIP [CB 8 j0; C8 (Z_to_bv 64 (fsi_csize (find_frame_size_info src off size)));
                               C8 (Z_to_bv 64 (fsi_bound (find_frame_size_info src off size)))].

Definition zd_findfsi_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV FSIP SRC : Z) (src : list Z) (off size : Z) (cs0 : list cell) (lo : Z),
  bytes_at usegs m SRC (map (Z_to_bv 8) src) -> all_bytes src -> 0 <= off -> 5 <= size -> size < 2^40 -> off + size <= zlen src ->
  0 < SRC -> SRC + zlen src < 2^64 ->
  rw_cells usegs m FSIP cs0 -> cells_size cs0 = 24%nat ->
  stk usegs m lo SPV -> lo <= SPV - FINDFSI_STACK -> 0 <= SPV < 2^64 -> SPV mod 16 = 0 ->
  (FSIP + 24 <= lo \/ SPV <= FSIP) -> (SRC + zlen src <= lo \/ SPV <= SRC) ->
  (FSIP + 24 <= SRC \/ SRC + zlen src <= FSIP) ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 FSIP -> a1 = Z_to_bv 64 (SRC + off) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 0 ->
  evt usegs (zd_findfsi_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc SPV FSIP src off size lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_FINDFSI) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Notation FINDDSIZE_STACK := 320 (only parsing).

Definition zd_finddsize_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV : Z) (src : list Z) (size lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (find_decompressed_size src size)) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(SPV - FINDDSIZE_STACK, SPV)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SPV.

Definition zd_finddsize_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV SRC : Z) (src : list Z) (size lo : Z),
  bytes_at usegs m SRC (map (Z_to_bv 8) src) -> all_bytes src -> 0 <= size -> size < 2^40 -> size <= zlen src ->
  0 < SRC -> SRC + zlen src < 2^64 ->
  stk usegs m lo SPV -> lo <= SPV - FINDDSIZE_STACK -> 0 <= SPV < 2^64 -> SPV mod 16 = 0 ->
  (SRC + zlen src <= lo \/ SPV <= SRC) ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 SRC -> a1 = Z_to_bv 64 size ->
  evt usegs (zd_finddsize_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc SPV src size lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_FINDDSIZE) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Notation XXH_DIGEST_STACK := 16 (only parsing).
Definition zd_xxh_digest_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(SPV - XXH_DIGEST_STACK, SPV)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SPV.

Definition zd_xxh_digest_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV STA : Z) (st : list byte) (lo : Z),
  bytes_at usegs m STA st -> zlen st = 88 -> 4096 <= STA -> STA mod 8 = 0 -> STA + 88 <= 2^47 ->
  stk usegs m lo SPV -> 4096 <= lo -> lo <= SPV - XXH_DIGEST_STACK -> SPV <= 2^47 ->
  (STA + 88 <= lo \/ SPV <= STA) ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 STA ->
  evt usegs (zd_xxh_digest_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_XXH_DIGEST) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
Definition xxh_cells (j1 : list byte) (ms : Z) (j2 : list byte) : list cell := [CB 72 j1; C4 (Z_to_bv 64 ms); CB 12 j2].
Definition xxh_state (m : fmem) (STA ms : Z) : Prop := exists j1 j2, rw_cells usegs m STA (xxh_cells j1 ms j2).

(* [comment removed for export] *)
Notation XXH_RESET_STACK := 32 (only parsing).
Definition zd_xxh_reset_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV STA lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(STA, STA + 88); (SPV - XXH_RESET_STACK, SPV)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SPV
    /\ xxh_state m' STA 0.

Definition zd_xxh_reset_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV STA : Z) (cs0 : list cell) (lo : Z),
  rw_cells usegs m STA cs0 -> cells_size cs0 = 88%nat -> 0 < STA -> STA mod 8 = 0 ->
  stk usegs m lo SPV -> lo <= SPV - XXH_RESET_STACK -> 0 <= SPV < 2^64 ->
  (STA + 88 <= lo \/ SPV <= STA) ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 STA ->
  evt usegs (zd_xxh_reset_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV STA lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_XXH_RESET) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
Notation XXH_UPDATE_STACK := 96 (only parsing).
Definition zd_xxh_update_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV STA lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' msz,
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(STA, STA + 88); (SPV - XXH_UPDATE_STACK, SPV)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SPV
    /\ xxh_state m' STA msz /\ 0 <= msz < 32.

Definition zd_xxh_update_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV STA IN : Z) (inb : list byte) (msz lo : Z),
  xxh_state m STA msz -> 0 <= msz < 32 -> 4096 <= STA -> STA mod 8 = 0 -> STA + 88 <= 2^47 ->
  ((IN = 0 /\ a2 = Z_to_bv 64 0) \/ (bytes_at usegs m IN inb /\ a2 = Z_to_bv 64 (zlen inb) /\ 4096 <= IN /\ IN + zlen inb <= 2^47 /\
              (STA + 88 <= IN \/ IN + zlen inb <= STA) /\ (IN + zlen inb <= lo \/ SPV <= IN))) ->
  stk usegs m lo SPV -> 4096 <= lo -> lo <= SPV - XXH_UPDATE_STACK -> SPV <= 2^47 ->
  (STA + 88 <= lo \/ SPV <= STA) ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 STA -> a1 = Z_to_bv 64 IN ->
  evt usegs (zd_xxh_update_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV STA lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_XXH_UPDATE) fc None m (seg_rom usegs)).
