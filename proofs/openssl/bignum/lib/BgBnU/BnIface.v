(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnModel BnTree BnInv BnSpecs BnMInv BnBridge.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition refs_stable (ls : lstate bptr) (OW : list block) (ls' : lstate bptr) (OW' : list block) (AD : bn_addrs) : Prop :=
  forall r a, ref_at ls OW AD r a -> ref_at ls' OW' AD r a.

Definition bn_pre (s : PState) (ls : lstate bptr) (m : mem) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
    (sp : word) (lo B : Z) (errv : word) (stack : Z) : Prop :=
  RHEAP s (OW ++ LB) m /\ lib_state ls m OW AD EA
  /\ rauxv_ok m B /\ bv_unsigned sp <= B
  /\ stk bgusegs m lo (bv_unsigned sp) /\ alloc_ceiling <= lo /\ GLOBALS_TOP <= lo /\ lo <= bv_unsigned sp - stack
  /\ rw_cells bgusegs m LX_ERRNO [C4 errv] /\ mem_inv bgusegs m.

Definition bn_post {A : Type} (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (ls : lstate bptr) (OW LB : list block) (lo B : Z) (m : mem) (AD : bn_addrs) (EA : err_addrs)
    (RES : A -> lstate bptr -> list block -> word -> Prop)
    (r : A * lstate bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' OW' (errv' : word),
    ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bgusegs)
    /\ RHEAP s' (OW' ++ LB) m' /\ lib_state (snd r) m' OW' AD EA
    /\ rauxv_ok m' B /\ stk bgusegs m' lo (bv_unsigned sp)
    /\ rw_cells bgusegs m' LX_ERRNO [C4 errv'] /\ mem_inv bgusegs m'
    /\ lx_pres LB (bv_unsigned sp) LIBW_bn m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ refs_stable ls OW (snd r) OW' AD
    /\ RES (fst r) (snd r) OW' a0.

Definition w_lib (OW : list block) (lo sp : Z) (iv : Z * Z) : Prop :=
  (lo <= fst iv /\ snd iv <= sp) \/ (exists b, In b OW /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).

End WithCeiling0.
