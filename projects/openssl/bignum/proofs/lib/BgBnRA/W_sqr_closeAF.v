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
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib BgWords BgArith.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import BnAKitAF BnCallAF AFrameKit AFrameEnv ExpKitAF Fr_sqr W_sqrAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require W_sqr_topAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition BN_SQR_STACKA : Z := 32 + BN_SQR_FIXED_STACKA.
Definition BN_SQR_COSTA : Z := BN_SQR_FIXED_COST.

Section Closed.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).

  Lemma bn_sqr_fixed_top_closedA : forall (CS CM : Z), BN_SQR_FIXED_STACKA <= CS -> BN_SQR_FIXED_COST <= CM -> forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr rx : bnref) (ar ax ac : Z) (qc : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo CS CM ->
    fr_room 1 ls OW LB ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx W_sqr_topAF.BN_SQR_FIXED_TOP (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL rx ax -> hpl PL rr -> rx <> ROne -> nbuf PL rx -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz ac ->
    implA (bn_sqr_fixed_top (tree_ops bptr) rr rx ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA CM (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz W_sqr_topAF.BN_SQR_FIXED_TOP) fc None m (seg_rom bgasegs)).
  Proof. exact bn_sqr_fixed_top_walkA. Qed.

  Lemma BN_sqr_closedA : forall (CS CM : Z), BN_SQR_STACKA <= CS -> BN_SQR_COSTA <= CM -> forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr rx : bnref) (ar ax ac : Z) (qc : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo CS CM ->
    fr_room 1 ls OW LB ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx W_sqr_topAF.BN_SQR (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL rx ax -> hpl PL rr -> rx <> ROne -> nbuf PL rx -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz ac ->
    implA (BN_sqr (tree_ops bptr) rr rx ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA CM (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz W_sqr_topAF.BN_SQR) fc None m (seg_rom bgasegs)).
  Proof.
    intros CS CM HCS HCM. intros until qc. intros PRE ROOM UW CTX E0 HR HX HPr NROx NBx EC E1 E2 E3.
    eapply implA_cost_wk; [| exact HCM].
    eapply (@W_sqr_topAF.BN_sqr_walkA AR UK BE BN_SQR_FIXED_STACKA BN_SQR_FIXED_COST);
      first [ exact (bn_sqr_fixed_top_closedA BN_SQR_FIXED_STACKA BN_SQR_FIXED_COST (Z.le_refl _) (Z.le_refl _))
            | (rewrite BN_SQR_FIXED_STACKA_val; clear; lia)
            | (unfold BN_SQR_FIXED_COST; clear; lia)
            | (eapply bn_preA_wk; [exact PRE | exact HCS | exact HCM])
            | eassumption ].
  Qed.
End Closed.
