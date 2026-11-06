(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
(* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit ZdFrameW.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg.
Import ListNotations.
Open Scope Z_scope.

Notation fmem := (word -> option byte).
Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PZD_FUZZ : Z := 0x146d4.          (* [comment removed for export] *)
Definition PZD_CREATEDCTX : Z := 0x14874.    (* [comment removed for export] *)
Definition PZD_FREEDCTX : Z := 0x1493c.      (* [comment removed for export] *)
Definition PZD_GETFH : Z := 0x14a50.         (* [comment removed for export] *)
Definition PZD_FINDDSIZE : Z := 0x14e7c.     (* [comment removed for export] *)
Definition PZD_FINDFSI : Z := 0x15020.       (* [comment removed for export] *)
Definition PZD_DMF : Z := 0x151d4.           (* [comment removed for export] *)
Definition PZD_DDCTX : Z := 0x15970.         (* [comment removed for export] *)
Definition PZD_DECODEFH : Z := 0x15a30.      (* [comment removed for export] *)
Definition PZD_DBEGIN : Z := 0x15e54.        (* [comment removed for export] *)
Definition PZD_FREEDDICT : Z := 0x16148.     (* [comment removed for export] *)
Definition PZD_GETCBLOCK : Z := 0x161e4.     (* [comment removed for export] *)
Definition PZD_DBLOCK : Z := 0x16f70.        (* [comment removed for export] *)
Definition PZD_CHECKCONT : Z := 0x1c0ec.     (* [comment removed for export] *)
Definition PZD_ISERROR : Z := 0x26600.       (* [comment removed for export] *)
Definition PZD_ERRCODE : Z := 0x2660c.       (* [comment removed for export] *)
Definition PZD_XXH_RESET : Z := 0x26dd0.     (* [comment removed for export] *)
Definition PZD_XXH_UPDATE : Z := 0x26e40.    (* [comment removed for export] *)
Definition PZD_XXH_DIGEST : Z := 0x2732c.    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zd_iserror_post (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (c : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' =>
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.b2z (zd_is_error c))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom psegs).

Definition zd_iserror_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (c : Z),
  0 <= c < 2^64 -> a0 = Z_to_bv 64 c ->
  evt psegs (zd_iserror_post ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc c m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_ISERROR) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zd_errcode_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (c : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists a1',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (zd_error_code c)) a1' a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom psegs).

Definition zd_errcode_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (c : Z),
  0 <= c < 2^64 -> a0 = Z_to_bv 64 c ->
  evt psegs (zd_errcode_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc c m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_ERRCODE) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bp_cells (bp : block_props) : list cell :=
  [C4 (Z_to_bv 64 (bp_type bp)); C4 (Z_to_bv 64 (bp_last bp)); C4 (Z_to_bv 64 (bp_orig bp))].

Definition zd_getcblock_post (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (BP : Z) (src : list Z) (ip size : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 a4 a5 m' cs,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (cblock_ret (get_cblock_size src ip size))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(BP, BP + 12)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ rw_cells psegs m' BP cs /\ cells_size cs = 12%nat
    /\ (forall v bp, get_cblock_size src ip size = Some (v, bp) -> cs = bp_cells bp).

Definition zd_getcblock_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SRC BP : Z) (src : list Z) (ip size : Z) (cs0 : list cell),
  bytes_at psegs m SRC (map (Z_to_bv 8) src) -> all_bytes src -> 0 <= ip -> 0 <= size -> ip + size <= zlen src -> 0 < SRC ->
  rw_cells psegs m BP cs0 -> cells_size cs0 = 12%nat ->
  mem_inv psegs m ->
  a0 = Z_to_bv 64 (SRC + ip) -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 BP ->
  evt psegs (zd_getcblock_post ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc BP src ip size m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_GETCBLOCK) fc None m (seg_rom psegs)).

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
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(ZFH, ZFH + 48); (SPV - GETFH_STACK, SPV)] m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo SPV
    /\ rw_cells psegs m' ZFH cs /\ cells_size cs = 48%nat
    /\ (forall h, get_frame_header src off size = FH_ok h -> cs = zfh_cells h).

Definition zd_getfh_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV ZFH SRC : Z) (src : list Z) (off size : Z) (cs0 : list cell) (lo : Z),
  bytes_at psegs m SRC (map (Z_to_bv 8) src) -> all_bytes src -> 0 <= off -> 5 <= size -> off + size <= zlen src -> 0 < SRC ->
  rw_cells psegs m ZFH cs0 -> cells_size cs0 = 48%nat ->
  stk psegs m lo SPV -> lo <= SPV - GETFH_STACK -> 0 <= SPV < 2^64 ->
  (ZFH + 48 <= lo \/ SPV <= ZFH) -> (SRC + zlen src <= lo \/ SPV <= SRC) ->
  (ZFH + 48 <= SRC \/ SRC + zlen src <= ZFH) ->
  mem_inv psegs m ->
  a0 = Z_to_bv 64 ZFH -> a1 = Z_to_bv 64 (SRC + off) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 0 ->
  evt psegs (zd_getfh_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc SPV ZFH src off size lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_GETFH) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Notation FINDFSI_STACK := 176 (only parsing).   (* [comment removed for export] *)

Definition zd_findfsi_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV FSIP : Z) (src : list Z) (off size lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 m' j0,
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(FSIP, FSIP + 24); (SPV - FINDFSI_STACK, SPV)] m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo SPV
    /\ rw_cells psegs m' FSIP [CB 8 j0; C8 (Z_to_bv 64 (fsi_csize (find_frame_size_info src off size)));
                               C8 (Z_to_bv 64 (fsi_bound (find_frame_size_info src off size)))].

Definition zd_findfsi_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV FSIP SRC : Z) (src : list Z) (off size : Z) (cs0 : list cell) (lo : Z),
  bytes_at psegs m SRC (map (Z_to_bv 8) src) -> all_bytes src -> 0 <= off -> 5 <= size -> size < 2^40 -> off + size <= zlen src ->
  0 < SRC -> SRC + zlen src < 2^64 ->
  rw_cells psegs m FSIP cs0 -> cells_size cs0 = 24%nat ->
  stk psegs m lo SPV -> lo <= SPV - FINDFSI_STACK -> 0 <= SPV < 2^64 ->
  (FSIP + 24 <= lo \/ SPV <= FSIP) -> (SRC + zlen src <= lo \/ SPV <= SRC) ->
  (FSIP + 24 <= SRC \/ SRC + zlen src <= FSIP) ->
  mem_inv psegs m ->
  a0 = Z_to_bv 64 FSIP -> a1 = Z_to_bv 64 (SRC + off) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 0 ->
  evt psegs (zd_findfsi_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc SPV FSIP src off size lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_FINDFSI) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Notation FINDDSIZE_STACK := 320 (only parsing).

Definition zd_finddsize_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV : Z) (src : list Z) (size lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (find_decompressed_size src size)) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(SPV - FINDDSIZE_STACK, SPV)] m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo SPV.

Definition zd_finddsize_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV SRC : Z) (src : list Z) (size lo : Z),
  bytes_at psegs m SRC (map (Z_to_bv 8) src) -> all_bytes src -> 0 <= size -> size < 2^40 -> size <= zlen src ->
  0 < SRC -> SRC + zlen src < 2^64 ->
  stk psegs m lo SPV -> lo <= SPV - FINDDSIZE_STACK -> 0 <= SPV < 2^64 ->
  (SRC + zlen src <= lo \/ SPV <= SRC) ->
  mem_inv psegs m ->
  a0 = Z_to_bv 64 SRC -> a1 = Z_to_bv 64 size ->
  evt psegs (zd_finddsize_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc SPV src size lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_FINDDSIZE) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zd_xxh_digest_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom psegs).

Definition zd_xxh_digest_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (STA : Z) (st : list byte),
  bytes_at psegs m STA st -> zlen st = 88 -> 4096 <= STA -> STA + 88 <= 2^47 ->
  mem_inv psegs m ->
  a0 = Z_to_bv 64 STA ->
  evt psegs (zd_xxh_digest_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_XXH_DIGEST) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
Definition xxh_cells (j1 : list byte) (ms : Z) (j2 : list byte) : list cell := [CB 72 j1; C4 (Z_to_bv 64 ms); CB 12 j2].
Definition xxh_state (m : fmem) (STA ms : Z) : Prop := exists j1 j2, rw_cells psegs m STA (xxh_cells j1 ms j2).

(* [comment removed for export] *)
Notation XXH_RESET_STACK := 32 (only parsing).
Definition zd_xxh_reset_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV STA lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(STA, STA + 88); (SPV - XXH_RESET_STACK, SPV)] m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo SPV
    /\ xxh_state m' STA 0.

Definition zd_xxh_reset_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV STA : Z) (cs0 : list cell) (lo : Z),
  rw_cells psegs m STA cs0 -> cells_size cs0 = 88%nat ->
  stk psegs m lo SPV -> lo <= SPV - XXH_RESET_STACK -> 0 <= SPV < 2^64 ->
  (STA + 88 <= lo \/ SPV <= STA) ->
  mem_inv psegs m ->
  a0 = Z_to_bv 64 STA ->
  evt psegs (zd_xxh_reset_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV STA lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_XXH_RESET) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
Notation XXH_UPDATE_STACK := 96 (only parsing).
Definition zd_xxh_update_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV STA lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' msz,
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(STA, STA + 88); (SPV - XXH_UPDATE_STACK, SPV)] m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo SPV
    /\ xxh_state m' STA msz /\ 0 <= msz < 32.

Definition zd_xxh_update_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV STA IN : Z) (inb : list byte) (msz lo : Z),
  xxh_state m STA msz -> 0 <= msz < 32 -> 4096 <= STA -> STA + 88 <= 2^47 ->
  (IN = 0 \/ (bytes_at psegs m IN inb /\ a2 = Z_to_bv 64 (zlen inb) /\ 4096 <= IN /\ IN + zlen inb <= 2^47 /\
              (STA + 88 <= IN \/ IN + zlen inb <= STA) /\ (IN + zlen inb <= lo \/ SPV <= IN))) ->
  stk psegs m lo SPV -> 4096 <= lo -> lo <= SPV - XXH_UPDATE_STACK -> SPV <= 2^47 ->
  (STA + 88 <= lo \/ SPV <= STA) ->
  mem_inv psegs m ->
  a0 = Z_to_bv 64 STA -> a1 = Z_to_bv 64 IN ->
  evt psegs (zd_xxh_update_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV STA lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_XXH_UPDATE) fc None m (seg_rom psegs)).
