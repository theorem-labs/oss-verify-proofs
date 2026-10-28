(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode Arr SFMisc.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_malloc_join.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require AllocSlot_iface Malloc_iface MallocHINV F_malloc_join F_malloc_small F_malloc_entry.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_join.F_malloc_enf OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.AllocSlot_iface OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_iface OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocHINV OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_join OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_small OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_entry.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition coreQ (o m0 : mem) (st : mstate) (s : PState)
    (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z)
    (res : mstate * option (aptr * Z)) (s' : PState) (ms' : machine_state) : Prop :=
  match res with
  | (st2, Some (g, idx)) =>
    exists (b : aptr) (r : region) (m1 : mem) (junk : list byte) (errv : word) (t0 t1 t2 a0 a1 a3 a5 a7 t3 t4 t5 t6 : word),
      ms' = MS (mkR (Z_to_bv 64 0x17008) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz n) s1
                   a0 a1 (wz idx) a3 (wz (sxv (c_mmap_counter (ctx st2)))) a5 (pw st2 (Some g)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x17014) fc None m1 (seg_rom asegs)
      /\ mrep st2 m1 /\ ticks_ok st2 /\ unk_agree st2 o m1 /\ mem_inv asegs m1
      /\ stk asegs m1 lo (bv_unsigned sp + -64)
      /\ rw_cells asegs m1 (bv_unsigned sp + -64)
           [C8 (wz idx); C8 (pw st2 (Some g)); C8 (wz (sxv (c_mmap_counter (ctx st2)))); C8 (wz idx); CB 16 junk; C8 s0v; C8 ra]
      /\ rw_cells asegs m1 (errno_addr tp) [C4 errv] /\ auxv_ok m1 (bv_unsigned sp)
      /\ pres_except (malloc_fp st st2 lo (bv_unsigned sp)) m0 m1
      /\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx - 4 <= a
                   < r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) - 4 ->
            malloc_fp st st2 lo (bv_unsigned sp) a)
      /\ 0 <= c_mmap_counter (ctx st2) < 2^32
      /\ slot_ok st2 g b r idx n
      /\ (expo_cond st n -> rdv pans_mem o st2 (fst b, snd b + (16 + get_stride (get_meta_rec st2 g) * idx) + -3) = 0)
      /\ mrel st st2 /\ brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
  | (st2, None) =>
    exists (m1 : mem) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0v s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m1 (seg_rom asegs)
      /\ mrep st2 m1 /\ ticks_ok st2 /\ mem_inv asegs m1 /\ stk asegs m1 lo (bv_unsigned sp)
      /\ rw_cells asegs m1 (errno_addr tp) [C4 errv] /\ auxv_ok m1 (bv_unsigned sp)
      /\ pres_except (malloc_fp st st2 lo (bv_unsigned sp)) m0 m1
      /\ mrel st st2 /\ brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition big_stmt : Prop :=
  forall (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
         (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N)
         (m1 : mem) (junk : list byte) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a6 a7 t3 t4 t5 t6 ra' : word),
  let st1 := set_tick t st in
  AREACH st LB -> MFACTS st LB -> mrep st m0 -> gp = Z_to_bv 64 AGP -> tp = Z_to_bv 64 0x1a620 ->
  alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 - AM_STACK -> MMAP_THRESHOLD <= n < 2^32 -> brk_link_ps st s ->
  mrep st1 m1 -> ticks_ok st1 -> unk_agree st1 o m1 -> mem_inv asegs m1 ->
  stk asegs m1 lo (bv_unsigned sp + -64) ->
  rw_cells asegs m1 (bv_unsigned sp + -64) [CB 48 junk; C8 s0v; C8 ra] -> length junk = 48%nat ->
  rw_cells asegs m1 (errno_addr tp) [C4 errv] -> auxv_ok m1 (bv_unsigned sp) ->
  pres_except (malloc_fp st st1 lo (bv_unsigned sp)) m0 m1 ->
  implT o (malloc_core full_lay st1 n) s (coreQ o m0 st s ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v F fc n lo)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz n) s1 (Z_to_bv 64 n) a1 a2 a3 a4 (Z_to_bv 64 131051) a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16d60) fc None m1 (seg_rom asegs)).

Section CORE.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis AS : alloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : forall st LB t sc n, AREACH st LB -> MFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
  n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis BIG : big_stmt.

(* [comment removed for export] *)
End CORE.


End ACeilS1.
