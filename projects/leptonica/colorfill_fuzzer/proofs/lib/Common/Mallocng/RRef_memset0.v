(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import decidable.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes
  PureModel VmLedger AllocIface AsanCeil AgentLib MemSplit.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require Import WalksLib.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocShape RefLrSc RefStep RefStmts RefSys RefPieces RefStep3 RefCalloc.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Musl Require Import Memset.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng Require Import RefStepR.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Memset0.
Context {fx : FPState} {RL : Reloc} {RC : RelocCode RL} {RS : RelocSites RL}.
#[local] Existing Instance reloc_layout.

Theorem memset0_refines : memset0_stmt.
Proof.
  unfold memset0_stmt.
  intros md regs mm rom s d n sp ret P L Hp Hvm Hag H2 Hal Hlo0 Hlo Hhi Hhi64 Hwt Hstk H1 Hret H4 H10 H11 H12 HS HK.
  pose proof (minv_init s sp 0 Hlo0 Hlo ltac:(lia) Hhi Hhi64 Hwt) as HI.
  pose proof (mwin_init s mm sp 0 Hstk) as HW.
  rewrite <- (with_vmmaps_same md), <- Hvm. note_win HI.
  unfold m_memset0 in HS |- *. munf.
  destruct (c_eq n (Z_to_bv 64 0)) eqn:Hn.
  - (* [comment removed for export] *)
    mnorm HS.
    mach_br_dir Hp HS true ltac:(by_bool Hn).
    mach_ret Hp HS Hag HK HI Hret.
  - (* [comment removed for export] *)
    mnorm HS.
    destruct (tsafe_stbytes_inv _ _ _ _ _ HS) as (Hok & Hso & EQ); rewrite EQ in HS; rewrite EQ; clear EQ.
    rewrite length_zero_bytes in Hok, Hso.
    pose proof (u64_range d) as Hd0. pose proof (u64_range n) as Hn0.
    pose proof (is0_false_u n Hn) as Hn1.
    pose proof (acc_ok_nowrap s d (Z.of_nat (Z.to_nat (bv_unsigned n))) ltac:(lia) (minv_lo64 _ _ HI) Hok) as Hnw.
    rewrite Z2Nat.id in Hnw by lia.
    unfold MallocTree.mret in HS; cbn [tsafe] in HS.
    lazymatch goal with
    | |- realizes _ _ (tshape (MallocTree.mret ?r ?s') ?L0) => change (tshape (MallocTree.mret r s') L0) with (L0 r s')
    end.
    eapply rz_at_pc;
      [ eapply (memset_at _ regs mm rom (bv_unsigned d) (bv_unsigned n) ret);
        [ mpure Hp | lia | lia | lia
        | rewrite Z_to_bv_bv_unsigned; exact (magree_sok _ _ _ _ Hag (minv_lo64 _ _ HI) Hok Hso)
        | exact Hret | exact H1
        | rewrite Z_to_bv_bv_unsigned; exact H10
        | exact H11
        | rewrite Z_to_bv_bv_unsigned; exact H12
        | ]
      | bveq ].
    intros regs' HA10 HAG.
    rewrite Z_to_bv_bv_unsigned in HA10.
    rewrite (zf_zero_bytes mm d n) by lia.
    lazymatch goal with |- realizes _ _ (?L0 ?r ?s') => eapply (HK r s' _ regs') end;
      [ exact HS
      | apply magree_wbytes; exact Hag
      | reflexivity | reflexivity | reflexivity
      | exact HA10
      | rewrite <- H2; apply HAG; cbv; intuition discriminate
      | intros x Hx; apply HAG; unfold memset_clob;
        pose proof (cs_enum x Hx) as C; cbv [In]; intuition (subst; discriminate)
      | intros a Ha _; cbn [ms_lo ms_hi] in Ha;
        rewrite wbytes_outside by (rewrite length_zero_bytes; first [lia | pose proof (acc_ok_cases _ _ _ Hok) as HC; cbn [ms_lo ms_hi] in HC; lia]);
        reflexivity
      | intros a Ha; lia ].
Qed.
End Memset0.
