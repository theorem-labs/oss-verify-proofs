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
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface AHarness_iface AH_fi_iface.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition AFI_FFSI_STACK : Z := 192 + AFI_STACK.

Section Stmts.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.

Definition ffsiA_post (L : alayout) (RNG : footprint)
    (ra : word) (SPV : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (R n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (a0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (nb : list byte) (cs db : word) (m' : amem),
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo SPV
    /\ magree asegs (fun a => aclient_addr CI LB SPV a /\ ~ (R <= a < R + 24)) m m'
    /\ AHEAP AI L RNG st LB m'
    /\ rw_cells asegs m' R [CB 8 nb; C8 cs; C8 db]
    /\ (bv_unsigned cs < 2^64 - 119 -> 1 <= bv_unsigned cs <= n).

Definition ffsiA_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra : word) (SPV : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock)
         (S : Z) (bl : list Z) (R lo : Z) (rj : list cell),
  AHEAP AI L RNG st LB m ->
  fake_lek 2 0 LB -> fake_lek 0 0 LB ->                                  (* [comment removed for export] *)
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  (* [comment removed for export] *)
  buf_atA m S bl -> zlen bl < 2^62 -> hcoverA LB S (zlen bl) ->
  (* [comment removed for export] *)
  rw_cells asegs m R rj -> cells_size rj = 24%nat -> unpoisoned m R (R + 24) -> R mod 8 = 0 -> SPV <= R -> R + 24 <= al_top L ->
  (* [comment removed for export] *)
  gshA m ->
  (* [comment removed for export] *)
  stk asegs m lo SPV -> ATOP + 4096 <= lo -> lo <= SPV - AFI_FFSI_STACK -> SPV + 16 < al_top L -> SPV mod 16 = 0 ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  (* [comment removed for export] *)
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG ->
  rng RNG R 24 -> rng RNG (shad R) 3 ->
  a3 = Z_to_bv 64 0 ->
  a0 = Z_to_bv 64 R -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlen bl) ->
  evtF asegs RNG (ffsiA_post L RNG ra SPV gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB R (zlen bl) lo m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 AFI_FFSI) fc None m (seg_rom asegs)).
End Stmts.
End CANSEC1.
