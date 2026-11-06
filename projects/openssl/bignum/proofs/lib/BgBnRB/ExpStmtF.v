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
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import BnAKitAF BnCallAF AFrameKit AFrameEnv ExpKitAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require ExpKitA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Stmt.
Context {AR : ARun} {UK : UnwindKit}.
Local Notation RT := (@ar_RT AR).

Definition exp_stmtAn (ENTRY STACK COST : Z) (depth : nat) (one : bnref -> bnref -> bnref -> bnref -> BM (M:=btree bptr) (ptr:=bptr) unit)
    (sixth : option word) : Prop := forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (rr ra_ rp rm : bnref) (arr ara arp arm ac : Z) (qc : bptr),
  bn_preA Σ ls m OW LB PL EA sp lo STACK COST -> fr_room depth ls OW LB ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx ENTRY (bv_unsigned ra :: ras) ->
  tp = wz TP_A ->
  ref_at ls OW PL rr arr -> ref_at ls OW PL ra_ ara -> ref_at ls OW PL rp arp -> ref_at ls OW PL rm arm ->
  hpl PL rr -> ra_ <> ROne -> rp <> ROne -> rm <> ROne -> nbuf PL ra_ -> pl_ctx PL = Some (ac, qc) ->
  a0 = wz arr -> a1 = wz ara -> a2 = wz arp -> a3 = wz arm -> a4 = wz ac -> (forall w, sixth = Some w -> a5 = w) ->
  implA (one rr ra_ rp rm ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA COST (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ENTRY) fc None m (seg_rom bgbsegs)).

Definition exp_stmtAn_f (ENTRY STACK COST : Z) (depth : nat) (one : bnref -> bnref -> bnref -> bnref -> BM (M:=btree bptr) (ptr:=bptr) unit)
    (sixth : option word) : Prop := forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (rr ra_ rp rm : bnref) (arr ara arp arm ac : Z) (qc : bptr),
  bn_preA Σ ls m OW LB PL EA sp lo STACK COST -> fr_room depth ls OW LB ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx ENTRY (bv_unsigned ra :: ras) ->
  tp = wz TP_A ->
  ref_at ls OW PL rr arr -> ref_at ls OW PL ra_ ara -> ref_at ls OW PL rp arp -> ref_at ls OW PL rm arm ->
  hpl PL rr -> ra_ <> ROne -> rp <> ROne -> rm <> ROne -> nbuf PL ra_ -> pl_ctx PL = Some (ac, qc) -> pl_fresh PL ->
  a0 = wz arr -> a1 = wz ara -> a2 = wz arp -> a3 = wz arm -> a4 = wz ac -> (forall w, sixth = Some w -> a5 = w) ->
  implA (one rr ra_ rp rm ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA COST (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ENTRY) fc None m (seg_rom bgbsegs)).
End Stmt.

Lemma exp_stmtA_of_n : forall {AR : ARun} {UK : UnwindKit} ENTRY STACK COST depth one sixth,
  @exp_stmtAn AR UK ENTRY STACK COST depth one sixth -> @ExpKitA.exp_stmtA AR UK ENTRY STACK COST depth one sixth.
Proof.
  intros AR UK ENTRY STACK COST depth one sixth H. unfold ExpKitA.exp_stmtA. intros until qc.
  intros PRE ROOM UW CTX ETP HAr HAa HAp HAm HPr NROa NROp NROm HPC E0 E1 E2 E3 E4 E5.
  pose proof PRE as (_ & LS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NOFR).
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as (_ & PWF & _).
  eapply H; [exact (BgIfaceF.bn_preA_F _ _ _ _ _ _ _ _ _ _ _ PRE) | exact ROOM | exact UW | exact CTX | exact ETP | exact HAr | exact HAa | exact HAp | exact HAm
            | exact HPr | exact NROa | exact NROp | exact NROm | exact (nbuf_nofr PL ra_ PWF NOFR) | exact HPC | exact E0 | exact E1 | exact E2 | exact E3 | exact E4 | exact E5].
Qed.

Lemma exp_stmtA_f_of_n : forall {AR : ARun} {UK : UnwindKit} ENTRY STACK COST depth one sixth,
  @exp_stmtAn_f AR UK ENTRY STACK COST depth one sixth -> @ExpKitA.exp_stmtA_f AR UK ENTRY STACK COST depth one sixth.
Proof.
  intros AR UK ENTRY STACK COST depth one sixth H. unfold ExpKitA.exp_stmtA_f. intros until qc.
  intros PRE ROOM UW CTX ETP HAr HAa HAp HAm HPr NROa NROp NROm HPC HFR E0 E1 E2 E3 E4 E5.
  pose proof PRE as (_ & LS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NOFR).
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as (_ & PWF & _).
  eapply H; [exact (BgIfaceF.bn_preA_F _ _ _ _ _ _ _ _ _ _ _ PRE) | exact ROOM | exact UW | exact CTX | exact ETP | exact HAr | exact HAa | exact HAp | exact HAm
            | exact HPr | exact NROa | exact NROp | exact NROm | exact (nbuf_nofr PL ra_ PWF NOFR) | exact HPC | exact HFR | exact E0 | exact E1 | exact E2 | exact E3 | exact E4 | exact E5].
Qed.

