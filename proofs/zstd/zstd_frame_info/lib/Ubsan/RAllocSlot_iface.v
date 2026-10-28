(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import ProgDeps.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import Malloc_fp.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_fp.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition RAS_STACK (sc : Z) : Z := 288 + 144 * Z.max 0 (27 - sc).

#[using="Type"] Lemma RAS_STACK_ge sc : 288 <= RAS_STACK sc.
Proof. unfold RAS_STACK. Local Ltac2 Set LiaHints.tbl := fun () => "0010=44640850317.2000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma RAS_STACK_le sc : 0 <= sc -> RAS_STACK sc <= 4176.
Proof. unfold RAS_STACK. Local Ltac2 Set LiaHints.tbl := fun () => "0010=10769734807.2000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma RAS_STACK_mono a b : a <= b -> RAS_STACK b <= RAS_STACK a.
Proof. unfold RAS_STACK. Local Ltac2 Set LiaHints.tbl := fun () => "0010<6257380167.3000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma RAS_STACK_nest sc j : sc < j -> j <= 26 -> RAS_STACK j + 144 <= RAS_STACK sc.
Proof. unfold RAS_STACK. Local Ltac2 Set LiaHints.tbl := fun () => "0010=27101283572.3000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ras_post (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (o m : mem) (st0 st : mstate) (s : PState) (lo sc req : Z)
    (st1 : mstate) (idx : Z) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' (bv_unsigned sp)
    /\ rmrep st1 m' /\ ticks_ok st1 /\ unk_agree st1 o m'
    /\ rpres_except (rmalloc_fp st0 st1 lo (bv_unsigned sp)) m m'
    /\ mrel st st1 /\ brk_link_ps st1 s'
    /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ as_inv st0 st st1 sc idx
    /\ 0 <= c_mmap_counter (ctx st1) < 2^32
    /\ (idx = -1
        \/ (0 <= idx /\ exists g b r, active st1 sc = Some g /\ slot_ok st1 g b r idx req
              /\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx - 4 <= a
                           < r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx + get_stride (get_meta_rec st1 g) - 4 ->
                    rmalloc_fp st0 st1 lo (bv_unsigned sp) a)
              (* [comment removed for export] *)
              /\ (s_regions st0 = ∅ -> rdv pans_mem o st1 (fst b, snd b + (16 + get_stride (get_meta_rec st1 g) * idx) + -3) = 0))).

Definition ralloc_slot_stmt (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop)
                           (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop) : Prop :=
  forall (fuel : nat) (R : Type) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem)
         (s : PState) (Q : R -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st0 st : mstate) (lo sc req : Z) (errv : word),
  as_pre st0 st sc req fuel ->
  rmrep st m -> ticks_ok st -> unk_agree st o m -> brk_link_ps st s ->
  rauxv_ok m (bv_unsigned sp) ->
  stk usegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
  rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
  (forall st1 idx s' ms',
     ras_post as_inv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
     rimplT o (k st1 idx) s' Q ms') ->
  rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom usegs)).

End CANSEC1.
