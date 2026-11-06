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
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnDivWords BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib BgWords BgArith BgMont BgExp.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_unwind_chain RT_iface RT_iface2 RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import W_ctxA W_ctx_getA W_ctx_endA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import AFrameKit AFrameCall AFrameTac AFrameEnv BnAKitAF BnCallAF W_expandAF W_callsAF W_ctxAF W_ctx_getAF W_ctx_endAF W_lshiftAF W_div_tailAF W_divAF W_bndivAF W_uaddAF W_addAF W_subAF W_set_wordAF W_mulAF W_mulA2F AFrameComp ExpKitAF W_small3A W_calls3AF W_nnmodAF W_mod_mulAF ExpStmtF ExpBodyKitF Fr_exp_simple W_exp_simpleAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require ExpKitA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Closed.
Context {UK : UnwindKit} {BE : BnEdges}.

  Variables (CSQ CQ : Z).
  Hypothesis CSQ0 : 0 <= CSQ.
  Hypothesis CQ0 : 0 <= CQ.
  Hypothesis BN_sqr_walkA : forall (AR1 : ARun)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts (@ar_RT AR1)) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr rx : bnref) (ar ax ac : Z) (qc : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo CSQ CQ ->
    fr_room 1 ls OW LB ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx 0x230fbc (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL rx ax -> hpl PL rr -> rx <> ROne -> nbuf PL rx -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz ac ->
    implA (BN_sqr (tree_ops bptr) rr rx ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA CQ (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x230fbc) fc None m (seg_rom bgbsegs)).

  Definition MM_CS : Z := Z.max CSQ (Z.max BN_MUL_TOP_STACK (Z.max BN_NNMOD_STACK (Z.max BN_CTX_START_STACK (Z.max BN_CTX_GET_STACK BN_CTX_END_STACK)))).
  Definition MM_CM : Z := Z.max CQ BN_MUL_TOP_COST.
  Definition SIMPLE_CS : Z := Z.max (64 + MM_CS) (Z.max BN_SET_WORD_STACK (Z.max BN_NUM_BITS_STACK RT_STACK)).
  Definition SIMPLE_CMM : Z := 2 * MC + MM_CM + BN_NNMOD_COST.
  Definition SIMPLE_STACK : Z := EXP_SIMPLE_FRAME + SIMPLE_CS.
  Definition SIMPLE_COST : Z := 1 + EXP_SIMPLE_TOTAL SIMPLE_CMM.

  Lemma MC0' : 0 <= MC. Proof. unfold MC. lia. Qed.

  Lemma BN_mod_mul_closedF : forall (AR1 : ARun)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts (@ar_RT AR1)) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr ra_ rb rm : bnref) (arr ara arb arm ac : Z) (qc : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo SIMPLE_CS SIMPLE_CMM ->
    fr_room 1 ls OW LB ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx 0x2346cc (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr arr -> ref_at ls OW PL ra_ ara -> ref_at ls OW PL rb arb -> ref_at ls OW PL rm arm ->
    hpl PL rr -> ra_ <> ROne -> rb <> ROne -> rm <> ROne -> nbuf PL ra_ -> nbuf PL rb -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz arr -> a1 = wz ara -> a2 = wz arb -> a3 = wz arm -> a4 = wz ac ->
    implA (BN_mod_mul (tree_ops bptr) rr ra_ rb rm ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA SIMPLE_CMM (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x2346cc) fc None m (seg_rom bgbsegs)).
  Proof.
    intros until qc. intros PRE ROOM UW CTX E0 HAr HAa HAb HAm HPr NRa NRb NRm NBa NBb HPC E1 E2 E3 E4 E5.
    pose proof MC0' as MCP.
    assert (NC0 : 0 <= BN_NNMOD_COST) by (unfold BN_NNMOD_COST, BN_DIV_FT_COST; clear - MCP; lia).
    assert (MCOST : 0 <= BN_MUL_TOP_COST) by (unfold BN_MUL_TOP_COST; clear - MCP; lia).
    eapply (@BN_mod_mul_walkA AR1 UK BE MM_CS MM_CM BN_NNMOD_COST);
      [ unfold MM_CS; clear; lia | unfold MM_CS; clear; lia | unfold MM_CS; clear; lia | unfold MM_CM; clear - CQ0; lia | exact NC0
      | | |
      | eapply bn_preA_wk; [exact PRE | unfold SIMPLE_CS, BN_MOD_MUL_STACK; clear; lia | unfold SIMPLE_CMM, BN_MOD_MUL_COST; clear; lia]
      | exact ROOM | exact UW | exact CTX | exact E0 | exact HAr | exact HAa | exact HAb | exact HAm | exact HPr | exact NRa | exact NRb | exact NRm | exact NBa | exact NBb | exact HPC
      | exact E1 | exact E2 | exact E3 | exact E4 | exact E5 ].
    -
      intros until qc0. intros PRE' ROOM' UW' CTX' T' H1 H2 H3 H4 H5 H6 Q0 Q1 Q2.
      eapply implA_cost_wk; [| unfold MM_CM; apply Z.le_max_l].
      eapply (BN_sqr_walkA AR1); [eapply bn_preA_wk; [exact PRE' | unfold MM_CS; clear; lia | unfold MM_CM; clear; lia] | exact ROOM' | exact UW' | exact CTX' | exact T' | exact H1 | exact H2 | exact H3 | exact H4 | exact H5 | exact H6 | exact Q0 | exact Q1 | exact Q2].
    -
      intros until qc0. intros PRE' UW' CTX' T' H1 H2 H3 H4 H5 H6 H7 H8 H9 Q0 Q1 Q2 Q3.
      eapply implA_cost_wk; [| unfold MM_CM; apply Z.le_max_r].
      eapply (@BN_mul_walkA AR1 UK BE); [eapply bn_preA_wk; [exact PRE' | unfold MM_CS; clear; lia | unfold MM_CM; clear; lia] | exact UW' | exact CTX' | exact T' | exact H1 | exact H2 | exact H3 | exact H4 | exact H5 | exact H6 | exact H7 | exact H8 | exact H9 | exact Q0 | exact Q1 | exact Q2 | exact Q3].
    -
      intros until qc0. intros PRE' UW' CTX' T' H1 H2 H3 H4 H5 H6 H7 H8 Q0 Q1 Q2 Q3.
      eapply (@BN_nnmod_walkA AR1 UK BE); [eapply bn_preA_wk; [exact PRE' | unfold MM_CS; clear; lia | clear; lia] | exact UW' | exact CTX' | exact T' | exact H1 | exact H2 | exact H3 | exact H4 | exact H5 | exact H6 | exact H7 | exact H8 | exact Q0 | exact Q1 | exact Q2 | exact Q3].
  Qed.

  Theorem BN_mod_exp_simple_closedF : forall AR : ARun,
    @exp_stmtAn AR UK BN_MOD_EXP_SIMPLE SIMPLE_STACK SIMPLE_COST 2 (BN_mod_exp_simple (tree_ops bptr)) None.
  Proof.
    intros AR. pose proof MC0' as MCP.
    eapply (@BN_mod_exp_simple_walkA AR UK BE SIMPLE_CS SIMPLE_CMM);
      [ unfold SIMPLE_CS, MM_CS; clear; lia | unfold SIMPLE_CS, MM_CS; clear; lia | unfold SIMPLE_CS, MM_CS; clear; lia | unfold SIMPLE_CS, MM_CS; clear; lia
      | unfold SIMPLE_CS; clear; lia | unfold SIMPLE_CS; clear; lia | unfold SIMPLE_CS; clear; lia
      | unfold SIMPLE_CMM, MM_CM, BN_NNMOD_COST, BN_DIV_FT_COST, BN_MUL_TOP_COST; clear - MCP CQ0; lia
      | exact BN_mod_mul_closedF ].
  Qed.

  Theorem BN_mod_exp_simple_closedA : forall AR : ARun, @ar_FR AR = [] ->
    @ExpKitA.exp_stmtA AR UK BN_MOD_EXP_SIMPLE SIMPLE_STACK SIMPLE_COST 2 (BN_mod_exp_simple (tree_ops bptr)) None.
  Proof. intros AR _. apply exp_stmtA_of_n. exact (BN_mod_exp_simple_closedF AR). Qed.
End Closed.
