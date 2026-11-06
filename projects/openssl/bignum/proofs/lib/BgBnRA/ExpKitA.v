(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac ZBridge RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import BnAKitA BnCallA AFrameKit AFrameEnv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition pl_fresh (PL : placement) : Prop :=
  pl_bn PL RRecpN = None /\ pl_bn PL RRecpNr = None /\ pl_recp PL = None /\ pl_mont PL = None /\ pl_bn PL RTmod = None.

Section Stmt.
Context {AR : ARun} {UK : UnwindKit}.
Local Notation RT := (@ar_RT AR).

Definition exp_stmtA (ENTRY STACK COST : Z) (depth : nat) (one : bnref -> bnref -> bnref -> bnref -> BM (M:=btree bptr) (ptr:=bptr) unit)
    (sixth : option word) : Prop := forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (rr ra_ rp rm : bnref) (arr ara arp arm ac : Z) (qc : bptr),
  bn_preA Σ ls m OW LB PL EA sp lo STACK COST -> fr_room depth ls OW LB ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx ENTRY (bv_unsigned ra :: ras) ->
  tp = wz TP_A ->
  ref_at ls OW PL rr arr -> ref_at ls OW PL ra_ ara -> ref_at ls OW PL rp arp -> ref_at ls OW PL rm arm ->
  hpl PL rr -> ra_ <> ROne -> rp <> ROne -> rm <> ROne -> pl_ctx PL = Some (ac, qc) ->
  a0 = wz arr -> a1 = wz ara -> a2 = wz arp -> a3 = wz arm -> a4 = wz ac -> (forall w, sixth = Some w -> a5 = w) ->
  implA (one rr ra_ rp rm ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA COST (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ENTRY) fc None m (seg_rom bgasegs)).

Definition exp_stmtA_f (ENTRY STACK COST : Z) (depth : nat) (one : bnref -> bnref -> bnref -> bnref -> BM (M:=btree bptr) (ptr:=bptr) unit)
    (sixth : option word) : Prop := forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (rr ra_ rp rm : bnref) (arr ara arp arm ac : Z) (qc : bptr),
  bn_preA Σ ls m OW LB PL EA sp lo STACK COST -> fr_room depth ls OW LB ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx ENTRY (bv_unsigned ra :: ras) ->
  tp = wz TP_A ->
  ref_at ls OW PL rr arr -> ref_at ls OW PL ra_ ara -> ref_at ls OW PL rp arp -> ref_at ls OW PL rm arm ->
  hpl PL rr -> ra_ <> ROne -> rp <> ROne -> rm <> ROne -> pl_ctx PL = Some (ac, qc) -> pl_fresh PL ->
  a0 = wz arr -> a1 = wz ara -> a2 = wz arp -> a3 = wz arm -> a4 = wz ac -> (forall w, sixth = Some w -> a5 = w) ->
  implA (one rr ra_ rp rm ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA COST (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ENTRY) fc None m (seg_rom bgasegs)).
End Stmt.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma MC0 : 0 <= MC. Proof. unfold MC. lia. Qed.

Section Env.
  Variables (LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs) (lo SPv FB : Z) (s0w raw : word) (rasO : option (list Z)) (TOTAL : Z).
  Variables (Σ0 : rts RT) (ls0 : bstate bptr) (OW0 : list block) (m0 : mem).
  Notation CENV := (cenvA LB PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0).

  End Env.

End WithRT.
