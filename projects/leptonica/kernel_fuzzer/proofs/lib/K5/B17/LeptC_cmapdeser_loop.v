(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import ImageA.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import Layout.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptB_guard.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.




Definition cmap_cells_i (arr depth nalloc n : Z) (pad : list byte) : list cell :=
  [C8 (Z_to_bv 64 arr); C4 (Z_to_bv 64 depth); C4 (Z_to_bv 64 nalloc); C4 (Z_to_bv 64 n); CB 4 pad].

Notation DSL_W cmap arr nalloc := [(cmap, cmap + 24); (arr, arr + 4 * nalloc)]%Z (only parsing).

(* [comment removed for export] *)
Definition deser_loop_post (ra sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (dp cmap arr depth nalloc ncolors : Z) (pad : list byte) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (abs' : list byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' (Z_to_bv 64 ncolors) (Z_to_bv 64 4) a0' a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 dp) (Z_to_bv 64 cmap) (Z_to_bv 64 (cmap + 12)) (Z_to_bv 64 (cmap + 16)) (Z_to_bv 64 SHB)
                  (Z_to_bv 64 ((cmap + 12) / 8 + SHB)) (Z_to_bv 64 (cmap / 8 + SHB)) (Z_to_bv 64 ((cmap + 16) / 8 + SHB))
                  (Z_to_bv 64 ncolors) (Z_to_bv 64 4) t3' t4' t5' t6')
             F (Z_to_bv 64 0x900d0) fc None m' (seg_rom asegs)
    /\ munch (DSL_W cmap arr nalloc) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' cmap (cmap_cells_i arr depth nalloc ncolors pad)
    /\ u8arr asegs m' arr abs' /\ Z.of_nat (length abs') = 4 * nalloc.

Lemma deser_loop : forall (k : nat) (i : Z)
    (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem)
    (dp cmap arr depth nalloc ncolors : Z) (pad dbs abs : list byte),
  Z.of_nat k = ncolors - i -> 0 <= i -> (1 <= k)%nat -> ncolors <= nalloc -> 2 <= nalloc <= 256 ->
  0 < dp -> dp + 4 * ncolors + 8 <= 2^47 -> 0 < cmap -> cmap mod 16 = 0 -> cmap + 24 <= 2^47 -> 0 < arr -> arr mod 16 = 0 -> arr + 4 * nalloc <= 2^47 ->
  (arr + 4 * nalloc <= cmap \/ cmap + 24 <= arr) ->
  (dp + 4 * ncolors <= cmap \/ cmap + 24 <= dp) -> (dp + 4 * ncolors <= arr \/ arr + 4 * nalloc <= dp) ->
  (cmap + 24 <= 0x7fff7000 \/ 0x10007fff8000 <= cmap) -> (arr + 4 * nalloc <= 0x7fff7000 \/ 0x10007fff8000 <= arr) ->
  bytes_at asegs m dp dbs -> Z.of_nat (length dbs) = 4 * ncolors ->
  rw_cells asegs m cmap (cmap_cells_i arr depth nalloc i pad) ->
  u8arr asegs m arr abs -> Z.of_nat (length abs) = 4 * nalloc ->
  acc asegs m dp (4 * ncolors) -> acc asegs m cmap 24 -> acc asegs m arr (4 * nalloc) ->
  mem_inv asegs m ->
  evt asegs (deser_loop_post ra sp gp tp F fc m dp cmap arr depth nalloc ncolors pad)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 ncolors) (Z_to_bv 64 4) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 dp) (Z_to_bv 64 cmap) (Z_to_bv 64 (cmap + 12)) (Z_to_bv 64 (cmap + 16)) (Z_to_bv 64 SHB)
             (Z_to_bv 64 ((cmap + 12) / 8 + SHB)) (Z_to_bv 64 (cmap / 8 + SHB)) (Z_to_bv 64 ((cmap + 16) / 8 + SHB))
             (Z_to_bv 64 i) (Z_to_bv 64 4) t3 t4 t5 t6)
        F (Z_to_bv 64 0x901e8) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m dp cmap arr depth nalloc ncolors pad dbs abs
    HK HI HK1 HNA NAR DP0 DPH CM0 CM16 CMHI AR0 AR16 ARHI DCA DDC DDA CMSH ARSH DB DBL CMC UA UAL ACCD ACCC ACCA MI.
  { lia. }
  unfold cmap_cells_i in CMC.
  pose proof (munch_refl (DSL_W cmap arr nalloc) m) as MU. pose proof (wmono_refl asegs m) as WM.
  gwalk (@nil Z).
  destruct (bytes_at_read1 m dp dbs (4 * i) DB ltac:(lia)) as (b0 & R0).
  replace (4 * i + dp) with (dp + 4 * i) in * by lia. lstep. clear R0.
  gwalk (@nil Z).
  destruct (bytes_at_read1 m dp dbs (4 * i + 1) DB ltac:(lia)) as (b1 & R1).
  try swrap_fix. replace (4 * i + 1 + dp) with (dp + (4 * i + 1)) in * by lia. lstep. clear R1.
  gwalk (@nil Z).
  destruct (bytes_at_read1 m dp dbs (4 * i + 2) DB ltac:(lia)) as (b2 & R2).
  try swrap_fix. replace (4 * i + 2 + dp) with (dp + (4 * i + 2)) in * by lia. lstep. clear R2.
  gwalk (@nil Z).
  destruct (bytes_at_read1 m dp dbs (4 * i + 3) DB ltac:(lia)) as (b3 & R3).
  try swrap_fix. replace (4 * i + 3 + dp) with (dp + (4 * i + 3)) in * by lia. lstep. clear R3.
  gwalk (@nil Z).
  try (sx32_fix; brF).      (* [comment removed for export] *)
  gwalk [0x90338].
  arr_sb arr (4 * i + 2) (arr + i * 4 + 2).
  gwalk [0x90354]. arr_sb arr (4 * i + 1) (arr + i * 4 + 1).
  gwalk [0x90368]. arr_sb arr (4 * i) (arr + i * 4).
  gwalk [0x90380]. arr_sb arr (4 * i + 3) (arr + i * 4 + 3).
  gwalk [0x901e8; 0x900d0].
  swrap_fix.
  destruct k as [|k].
  - (* [comment removed for export] *)
    assert (EI : i + 1 = ncolors) by lia. rewrite EI in *.
    brT. apply evt_done. unfold deser_loop_post, cmap_cells_i.
    do 15 eexists. exists m0, abs. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact CMC|]. split; [exact UA| exact UAL].
  - brF.
    eapply evt_cut.
    + eapply (IH (i + 1)) with (dbs := dbs) (abs := abs) (pad := pad) (depth := depth); try eassumption; try lia.
    + intros ms' PO. apply evt_done. unfold deser_loop_post in PO |- *.
      destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & abs' & E & MU' & WM' & R).
      exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', abs'.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')| exact R].
Qed.
