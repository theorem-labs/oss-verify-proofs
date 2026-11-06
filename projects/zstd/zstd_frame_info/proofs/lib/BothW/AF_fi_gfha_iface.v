(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Image ZBridge Arr Bytes.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AHarness_iface AH_fi_iface.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

Section CANSEC1. Context {rc : runConstT}.
Section Stmts.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.

(* [comment removed for export] *)
Definition gfhaA_post (L : alayout) (RNG : footprint)
    (ra : word) (SPV : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (ZF n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (r : Z) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j1 hb j2 : list byte) (m' : amem),
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo SPV
    /\ magree bsegs (fun a => aclient_addr CI LB SPV a /\ ~ (ZF <= a < ZF + 48)) m m'
    /\ AHEAP AI L RNG st LB m'
    /\ rw_cells bsegs m' ZF [CB 24 j1; CB 4 hb; CB 20 j2]
    /\ (r mod 2^64 = 0 -> exists h, hb = le4 (Z_to_bv 64 h) /\ 6 <= h <= n /\ h <= 18).

Definition gfhaA_stmt_at (pc : Z) (fmt : word -> Prop) : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra : word) (SPV : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock)
         (S : Z) (bl : list Z) (ZF lo : Z) (zj : list byte),
  AHEAP AI L RNG st LB m ->
  fake_lek 0 0 LB ->                                                       (* [comment removed for export] *)
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  buf_atA m S bl -> zlen bl < 2^62 -> hcoverA LB S (zlen bl) ->
  (* [comment removed for export] *)
  rw_cells bsegs m ZF [CB 48 zj] -> fcellA m LB ZF 48 -> ZF mod 8 = 0 -> shullA RNG m LB ZF 48 ->
  (* [comment removed for export] *)
  gshA m ->
  (* [comment removed for export] *)
  stk bsegs m lo SPV -> ATOP + 4096 <= lo -> lo <= SPV - AFI_STACK -> SPV <= al_top L -> SPV mod 16 = 0 ->
  mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  (* [comment removed for export] *)
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG ->
  rng RNG ZF 48 -> rng RNG (shad ZF) 6 ->
  fmt a3 ->
  a0 = Z_to_bv 64 ZF -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlen bl) ->
  evtF bsegs RNG (gfhaA_post L RNG ra SPV gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB ZF (zlen bl) lo m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 pc) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Definition gfhaA_stmt : Prop := gfhaA_stmt_at AFI_GFHA (fun a3 => a3 = Z_to_bv 64 0).
Definition gfhA_stmt : Prop := gfhaA_stmt_at AFI_GFH (fun _ => True).
End Stmts.
End CANSEC1.
