(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.BgMallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnModel BnTree BnInv BnSpecs BnMInv BnBridge.
From OSSVerify.Proofs.openssl.bignum.lib.BgP Require Import Layout Lib_iface Lib_kit.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnHeap BnRep BnIface.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Section Env.

  Variables (LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo B SPv FB : Z).
  Variables (s0 : PState) (ls0 : lstate bptr) (OW0 : list block) (m0 : mem).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis LOFB : lo <= FB.
  Hypothesis FBSP : FB <= SPv.
  Hypothesis SPB : SPv <= B.
  Hypothesis SPR : SPv < 2^64.

  Definition cenv (fr : list cell) (st : PState) (ls : lstate bptr) (m : mem) (OW : list block) : Prop :=
    RHEAP st (OW ++ LB) m /\ rauxv_ok m B /\ stk bgpsegs m lo FB /\ (exists errv : word, rw_cells bgpsegs m LX_ERRNO [C4 errv]) /\ mem_inv bgpsegs m
    /\ lx_pres LB SPv LIBW_bn m0 m /\ ps_fa st = ps_fa s0 /\ ps_so st = ps_so s0 /\ refs_stable ls0 OW0 ls OW AD
    /\ rw_cells bgpsegs m FB fr /\ Z.of_nat (cells_size fr) = SPv - FB.

  Lemma ESPv : bv_unsigned (Z_to_bv 64 FB) = FB.
  Proof using CEIL LOFB FBSP SPR. apply unsigned_lit. lia. Qed.

  Definition cpost (st : PState) (ls : lstate bptr) (m : mem) (OW : list block) (st' : PState) (ls' : lstate bptr) (m' : mem) (OW' : list block) : Prop :=
    RHEAP st' (OW' ++ LB) m' /\ lib_state ls' m' OW' AD EA /\ rauxv_ok m' B /\ stk bgpsegs m' lo FB
    /\ (exists errv' : word, rw_cells bgpsegs m' LX_ERRNO [C4 errv']) /\ mem_inv bgpsegs m'
    /\ lx_pres LB FB LIBW_bn m m' /\ ps_fa st' = ps_fa st /\ ps_so st' = ps_so st /\ refs_stable ls OW ls' OW' AD.

End Env.
End WithCeiling0.
