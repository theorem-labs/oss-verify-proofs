(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Tac.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Image.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require ZBridge.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require SysStep.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Walk.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require ITree.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Nodes.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Decode.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require SFModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require PImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM11.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocTree.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocFacts_A.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocKit_A.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Malloc.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Malloc_fp.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require RMallocRep.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require RMallocTree.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require PM22.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require PM01.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM12.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocNat.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocFacts_AS.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require ASlot_W1.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require ASlot_I.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM14.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require RMallocKit_B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module RAllocSlot_iface.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Decode. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require Import PImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM11. Import MM11. Import MM11.F_malloc_enframe. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocFacts_A. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocKit_A.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.Monad.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import Malloc_fp.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require Import RMallocRep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require Import RMallocTree. Import PM22. Import PM22.RMalloc_fp.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Definition RAS_STACK (sc : Z) : Z := 288 + 144 * Z.max 0 (27 - sc).

Lemma RAS_STACK_ge sc : 288 <= RAS_STACK sc.
Proof. unfold RAS_STACK. lia. Qed.
Lemma RAS_STACK_le sc : 0 <= sc -> RAS_STACK sc <= 4176.
Proof. unfold RAS_STACK. lia. Qed.
Lemma RAS_STACK_mono a b : a <= b -> RAS_STACK b <= RAS_STACK a.
Proof. unfold RAS_STACK. lia. Qed.
Lemma RAS_STACK_nest sc j : sc < j -> j <= 26 -> RAS_STACK j + 144 <= RAS_STACK sc.
Proof. unfold RAS_STACK. lia. Qed.

Definition ras_post (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (o m : mem) (st0 st : mstate) (s : PState) (lo sc req : Z)
    (st1 : mstate) (idx : Z) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
    /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m' /\ stk (run_segments psegs rc_inp rc_sp rc_mb) m' lo (bv_unsigned sp)
    /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' (bv_unsigned sp)
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
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (errno_addr tp) [C4 errv] -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
  (forall st1 idx s' ms',
     ras_post as_inv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
     rimplT o (k st1 idx) s' Q ms') ->
  rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).

End CANSEC1.
End RAllocSlot_iface.

Module RASlot_I.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Decode. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require Import PImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM11. Import MM11. Import MM11.F_malloc_enframe. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocFacts_A. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM12. Import MM12. Import MM12.MallocHINV. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocKit_A.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.Monad.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import Malloc_fp. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocNat. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocFacts_AS. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import ASlot_W1. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import ASlot_I.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require Import RMallocRep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require Import RMallocTree. Import PM22. Import PM22.RMalloc_fp. Import RAllocSlot_iface.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope Z_scope.

Notation RAREACH := (AREACH_from ref_reserved).
Notation RISTF := (@ISTF_g _ ref_reserved).
Notation RAMP_AS := (AMP_AS_g ref_reserved).


Section CANSEC1.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Lemma rimplT_steq {R} o (t1 t2 : Malloc.M R) s Q ms :
  steq t1 t2 -> rimplT o t1 s Q ms -> rimplT o t2 s Q ms.
Proof.
  intros Hs H. unfold rimplT, mrun, prun in *. eapply rimplM_membed_steq; [|exact H]. apply eruns_steq. exact Hs.
Qed.

Lemma rimplT_nat2 {X Y R} o (P : forall R', (X -> Y -> Malloc.M R') -> Malloc.M R' -> Malloc.M R')
      (k : X -> Y -> Malloc.M R) bail s (QS : option (X * Y) -> PState -> machine_state -> Prop) Q ms :
  steq (P R k bail) (sbind (P _ kS bS) (KF k bail)) ->
  rimplT o (P _ kS bS) s QS ms ->
  (forall x y s' ms', QS (Some (x, y)) s' ms' -> leaf_of o (P _ kS bS) (Some (x, y)) -> rimplT o (k x y) s' Q ms') ->
  (forall s' ms', QS None s' ms' -> leaf_of o (P _ kS bS) None -> rimplT o bail s' Q ms') ->
  rimplT o (P R k bail) s Q ms.
Proof.
  intros NAT H HK HB. eapply rimplT_steq; [apply steq_sym; exact NAT|].
  eapply rimplT_bind; [eapply rimplT_reach; exact H|].
  intros [[x y]|] s' ms' [HQ HL]; cbn [KF]; eauto.
Qed.

Definition ras_pre2 (st0 st : mstate) (sc req : Z) (fuel : nat) : Prop :=
  (exists LB, RAREACH st0 LB /\ IST st0 st) /\ ENTRY_REL st0 st /\ ALLC st
  /\ 0 <= sc < 48 /\ 0 <= req < 2^32 /\ req + 4 <= 16 * size_class sc.

Definition ras_post2
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (o m : mem) (st0 st : mstate) (s : PState) (lo sc req : Z)
    (st1 : mstate) (idx : Z) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
    /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m' /\ stk (run_segments psegs rc_inp rc_sp rc_mb) m' lo (bv_unsigned sp)
    /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' (bv_unsigned sp)
    /\ rmrep st1 m' /\ ticks_ok st1 /\ unk_agree st1 o m'
    /\ rpres_except (rmalloc_fp st0 st1 lo (bv_unsigned sp)) m m'
    /\ mrel st st1 /\ brk_link_ps st1 s'
    /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ as_inv2 st0 st st1 sc idx
    /\ 0 <= c_mmap_counter (ctx st1) < 2^32
    /\ (idx = -1
        \/ (0 <= idx /\ exists g b r, active st1 sc = Some g /\ slot_ok st1 g b r idx req
              /\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx - 4 <= a
                           < r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx + get_stride (get_meta_rec st1 g) - 4 ->
                    rmalloc_fp st0 st1 lo (bv_unsigned sp) a)
              /\ (s_regions st0 = ∅ -> rdv pans_mem o st1 (fst b, snd b + (16 + get_stride (get_meta_rec st1 g) * idx) + -3) = 0))).

Lemma ras_post2_post : ras_post2 = ras_post as_inv2.
Proof. reflexivity. Qed.

Definition ralloc_slot_stmt2 (fuel : nat) : Prop :=
  forall (R : Type) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem)
         (s : PState) (Q : R -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st0 st : mstate) (lo sc req : Z) (errv : word),
  ras_pre2 st0 st sc req fuel ->
  rmrep st m -> ticks_ok st -> unk_agree st o m -> brk_link_ps st s ->
  rauxv_ok m (bv_unsigned sp) ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (errno_addr tp) [C4 errv] -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
  (forall st1 idx s' ms',
     ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
     rimplT o (k st1 idx) s' Q ms') ->
  rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).

Lemma ralloc_slot_stmt2_all : (forall fuel, ralloc_slot_stmt2 fuel) -> ralloc_slot_stmt ras_pre2 as_inv2.
Proof. intros H. exact H. Qed.

Lemma ralloc_slot_stmtL (fuel : nat) : ralloc_slot_stmt2 fuel ->
  forall (R : Type) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem)
         (s : PState) (Q : R -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st0 st : mstate) (lo sc req : Z) (errv : word),
  ras_pre2 st0 st sc req fuel ->
  rmrep st m -> ticks_ok st -> unk_agree st o m -> brk_link_ps st s ->
  rauxv_ok m (bv_unsigned sp) ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (errno_addr tp) [C4 errv] -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
  (forall st1 idx s' ms',
     ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
     leaf_of o (alloc_slot full_lay fuel st sc req kS bS) (Some (st1, idx)) ->
     rimplT o (k st1 idx) s' Q ms') ->
  rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros AS. intros until errv. intros PRE MR TK UA BL AUX ST CLO LO ER MI TP A0 A1 K.
  eapply (rimplT_nat2 o (fun R' k' b' => @alloc_slot R' full_lay fuel st sc req k' b') k bail s
            (fun r s' ms' => match r with
                             | Some (st1, idx) => ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms'
                             | None => False end)).
  - apply alloc_slot_nat.
  - eapply AS; try eassumption. intros st1 idx s' ms' HP. apply rimplT_ret. apply evt_done. exact HP.
  - intros x y s' ms' HP HL. exact (K x y s' ms' HP HL).
  - intros s' ms' [].
Qed.

Lemma ralloc_meta_stmtL (am_pre : mstate -> Prop) : ralloc_meta_stmt am_pre ->
  forall (R : Type) (k : mstate -> optr -> Malloc.M R) (bail : Malloc.M R) (o : mem)
         (s : PState) (Q : R -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word),
  am_pre st -> rmrep st m -> ticks_ok st -> brk_link_ps st s ->
  rauxv_ok m (bv_unsigned sp) ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RAM_STACK ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (errno_addr tp) [C4 errv] -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m ->
  tp = Z_to_bv 64 0x2fb00 ->
  (forall st1 mo s' ms',
     ram_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' ->
     brk_link_ps st1 s' ->
     leaf_of o (alloc_meta st kS bS) (Some (st1, mo)) ->
     rimplT o (k st1 mo) s' Q ms') ->
  rimplT o (alloc_meta st k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ralloc_meta_entry) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros AM. intros until errv. intros PRE MR TK BL AUX ST CLO LO ER MI TP K.
  eapply (rimplT_nat2 o (fun R' k' b' => @alloc_meta R' st k' b') k bail s
            (fun r s' ms' => match r with
                             | Some (st1, mo) => ram_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' /\ brk_link_ps st1 s'
                             | None => False end)).
  - apply alloc_meta_nat.
  - eapply AM; try eassumption. intros st1 mo s' ms' HP HB. apply rimplT_ret. apply evt_done. split; assumption.
  - intros x y s' ms' [HP HB] HL. exact (K x y s' ms' HP HB HL).
  - intros s' ms' [].
Qed.
End CANSEC1.
End RASlot_I.

Module RMallocKit_B3.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require Import PImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM12. Import MM12. Import MM12.MallocModel_B.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM14. Import MM14. Export MM14.MallocKit_B3.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require Import RMallocRep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require Import RMallocTree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require Import RMallocKit_B.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.


Ltac rctx_same := intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.

Section CANSEC1.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Lemma rmrep_set_usage : forall st m sc v,
  rmrep st m -> 0 <= sc < 48 ->
  rmrep (set_usage sc v st) (write_to_mem m (wa (RCTX + 464 + 8 * sc)) (le8 (wz v))).
Proof.
  intros st m sc v MR Hsc. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
  pose proof (length_le8 (wz v)) as L8.
  pose proof (munch_write [(RCTX + 464 + 8 * sc, RCTX + 464 + 8 * sc + 8)] m m (RCTX + 464 + 8 * sc) (le8 (wz v)) (munch_refl _ m)
                ltac:(unfold RCTX; lia) ltac:(rewrite L8; unfold RCTX; lia) ltac:(rewrite L8; cbn [inside]; lia)) as MU.
  pose proof (wmono_write (run_segments psegs rc_inp rc_sp rc_mb) m m (wa (RCTX + 464 + 8 * sc)) (le8 (wz v)) (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m)) as WM.
  eapply (rmrep_ctx_frameW st (set_usage sc v st) m _ _ MR MU WM); try reflexivity.
  - rctx_same.
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - left. rewrite usages_set_usage by lia. replace (RCTX + 464 + 8 * sc) with ((RCTX + 464) + 8 * sc) by lia.
    apply u64arr_write; [exact X3| rewrite usages_length; lia].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [| rctx_same].
    unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx set_usage upd_ctx c_seq c_brk set_usage_map]. reflexivity.
Qed.

Lemma rmrep_set_seq : forall st m v,
  rmrep st m -> 0 <= v < 256 ->
  rmrep (upd_ctx (set_seq v) st) (write_to_mem m (wa (RCTX + 912)) [b8 v]).
Proof.
  intros st m v MR Hv. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
  pose proof (munch_write [(RCTX + 912, RCTX + 913)] m m (RCTX + 912) [b8 v] (munch_refl _ m)
                ltac:(unfold RCTX; lia) ltac:(cbn; unfold RCTX; lia) ltac:(cbn; lia)) as MU.
  pose proof (wmono_write (run_segments psegs rc_inp rc_sp rc_mb) m m (wa (RCTX + 912)) [b8 v] (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m)) as WM.
  eapply (rmrep_ctx_frameW st (upd_ctx (set_seq v) st) m _ _ MR MU WM); try reflexivity.
  - rctx_same.
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - left.
    pose proof (rw_cells_write (run_segments psegs rc_inp rc_sp rc_mb) m (RCTX + 912) (ctx_tail_cells st) 0 (C1 (b8 (c_seq (ctx st)))) (C1 (b8 v)) X6 eq_refl eq_refl I) as W.
    rewrite Z.add_0_r in W. cbn [cbytes cell_upd ctx_tail_cells Nat.eqb] in W.
    unfold ctx_tail_cells, brk_word, ctx in *. cbn [s_ctx upd_ctx set_seq c_seq c_brk]. exact W.
Qed.

Lemma rmrep_set_unmap_seq : forall st m i v,
  rmrep st m -> 0 <= i < 32 ->
  rmrep (upd_ctx (fun c => set_unmap_seq_map (<[i := v]> (c_unmap_seq c)) c) st) (write_to_mem m (wa (RCTX + 848 + i)) [b8 v]).
Proof.
  intros st m i v MR Hi. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
  pose proof (munch_write [(RCTX + 848 + i, RCTX + 848 + i + 1)] m m (RCTX + 848 + i) [b8 v] (munch_refl _ m)
                ltac:(unfold RCTX; lia) ltac:(cbn; unfold RCTX; lia) ltac:(cbn; lia)) as MU.
  pose proof (wmono_write (run_segments psegs rc_inp rc_sp rc_mb) m m (wa (RCTX + 848 + i)) [b8 v] (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m)) as WM.
  eapply (rmrep_ctx_frameW st _ m _ _ MR MU WM); try reflexivity.
  - rctx_same.
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - left. rewrite unmap_seqs_set by lia. replace (RCTX + 848 + i) with ((RCTX + 848) + i) by lia.
    apply (u8arr_write (run_segments psegs rc_inp rc_sp rc_mb) m (RCTX + 848) (unmap_seqs st) i (b8 v)); [exact X4| rewrite unmap_seqs_length; lia].
  - right. split; [reflexivity| rctx_same].
  - right. split; [| rctx_same].
    unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]. reflexivity.
Qed.

Lemma rmrep_group_hdr_zero : forall st m p gh bs,
  rmrep st m -> (s_groups st) !! p = Some gh ->
  (forall o, 0 <= o < 12 -> exists h, cell_read (get_shadow st (fst p)) (snd p + o) = Unknown h) ->
  length bs = 8%nat ->
  rmrep (del_group p st) (write_to_mem m (wa (conc st p)) bs).
Proof.
  intros st m p gh bs MR Hp UNK L8.
  pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
  destruct (rgroup_conc st p gh WF Hp) as (r & Hr & Cp & Kr & Sp0 & Sp1 & SpA & RB0 & RBC).
  destruct (WR _ r Hr) as (_ & RBAL & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2].
  pose proof (round_up_pg_ge (r_len r)) as RU. atop_facts.
  eapply rmrep_transport_unowned.
  - apply rmrep_del_group. exact MR.
  - apply (munch_write [(conc st p, conc st p + 8)] m m (conc st p) bs (munch_refl _ m)); [lia| rewrite L8; cbn; lia| rewrite L8; cbn [inside]; lia].
  - apply wmono_write. apply wmono_refl.
  - intros lo hi a [E|[]] Ha. inversion E; subst lo hi. clear E.
    intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
    + unfold RCTX in C. lia.
    + unfold RMLOCK in C. lia.
    + unfold RNEED_LOCKS in C. lia.
    + unfold RPAGE_SIZE in C. lia.
    + destruct C as (ak & ar & Hak & Hin). cbn in Hak.
      destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & _).
      assert (NE : fst ak <> fst p) by (intros E; rewrite E, Hr in Hra; inversion Hra; subst; congruence).
      change (conc (del_group p st) ak) with (conc st ak) in Hin.
      pose proof (rarea_lr_lo st ak ar ra WF Hak Hra). pose proof (lr_lo_group r Kr).
      destruct (DJ (fst ak) ra (fst p) r Hra Hr NE); lia.
    + destruct C as (b & gh' & Hb & Hin). cbn in Hb. apply lookup_delete_Some in Hb. destruct Hb as [NEb Hb].
      change (conc (del_group p st) b) with (conc st b) in Hin.
      destruct (rgroup_conc st b gh' WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & _).
      destruct (N.eq_dec (fst b) (fst p)) as [E|NE].
      * rewrite E, Hr in Hrb. inversion Hrb; subst rb.
        assert (snd b <> snd p) by (intros E2; apply NEb; destruct b, p; cbn in *; congruence).
        Z.div_mod_to_equations. lia.
      * pose proof (lr_lo_group rb Krb). pose proof (lr_lo_group r Kr). destruct (DJ (fst b) rb (fst p) r Hrb Hr NE); lia.
    + destruct C as (rid & r' & v & Hr' & Hk' & Hin & HC). cbn in Hr'. change (get_shadow (del_group p st) rid) with (get_shadow st rid) in HC.
      destruct (N.eq_dec rid (fst p)) as [E|NE].
      * subst rid. rewrite Hr in Hr'. inversion Hr'; subst r'.
        destruct (UNK (a - r_base r - snd p) ltac:(lia)) as [h Hh].
        replace (snd p + (a - r_base r - snd p)) with (a - r_base r) in Hh by lia. rewrite Hh in HC. discriminate.
      * pose proof (lr_lo_group r' Hk'). pose proof (lr_lo_group r Kr). destruct (DJ rid r' (fst p) r Hr' Hr NE); lia.
    + unfold RGOT_SSP in C. lia.
    + unfold RSSP_GUARD in C. lia.
Qed.

Lemma rmrep_grp_del_eq : forall st m g p, rmrep (del_group p st) m -> rmrep (grp_del st g p) m.
Proof. intros. unfold grp_del. apply rmrep_del_slots. exact H. Qed.
End CANSEC1.
End RMallocKit_B3.
