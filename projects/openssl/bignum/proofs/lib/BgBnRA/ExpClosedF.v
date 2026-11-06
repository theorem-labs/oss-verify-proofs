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
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout R_unwind_chain RT_iface RT_iface2 RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import W_ctxA W_ctx_getA W_ctx_endA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import AFrameKit AFrameCall AFrameTac AFrameEnv BnAKitAF BnCallAF W_expandAF W_callsAF W_ctxAF W_ctx_getAF W_ctx_endAF W_copyAF W_cmpAF W_usubAF W_lshiftAF W_rshiftAF W_shiftAF W_div_tailAF W_divAF W_bndivAF W_uaddAF W_addAF W_subAF W_set_wordAF W_set_bitAF W_mul_wordAF W_add_wordAF W_mulAF W_mulA2F AFrameComp ExpKitAF W_small3A W_calls3AF W_nnmodAF W_mod_mulAF ExpStmtF ExpBodyKitF.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import W_reciprocalAF W_recp_setAF W_recp_initAF W_recp_freeAF W_div_recpAF W_recpAF Fr_exp_recp W_exp_recpAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import W_from_montAF W_mulOneAF W_mul_montAF W_montAF W_mont_ctxAF W_mont_freeAF W_mont_setAF MontSetClosedAF W_sqrAF W_sqr_closeAF Fr_exp_mont W_exp_montAF W_exp_mont_topAF W_exp_mont_wordAF W_mod_expAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import Fr_exp_simple W_exp_simpleAF ExpSimpleClosedF.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require ExpKitA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac bnd := first [apply Z.leb_le; vm_compute; reflexivity | apply Z.le_refl | lia].

Ltac fin := try eassumption; try (eapply bn_preA_wk; [eassumption | bnd | bnd]); try (eapply fr_room_le; [eassumption | lia]).

Ltac finc L := eapply implA_cost_wk; [eapply L; fin | bnd].

Definition DR_CSR : Z := Z.max BN_CTX_START_STACK (Z.max BN_CTX_GET_STACK (Z.max BN_CTX_END_STACK (Z.max BN_SET_BIT_STACK BN_DIV_TOP_STACK))).
Definition DR_CS : Z := Z.max BN_CTX_START_STACK (Z.max BN_CTX_GET_STACK (Z.max BN_CTX_END_STACK (Z.max BN_NUM_BITS_STACK (Z.max BN_COPY_STACK (Z.max BN_UCMP_STACK
                          (Z.max BN_USUB_STACK (Z.max BN_MUL_TOP_STACK (Z.max BN_RSHIFT_W_STACK (Z.max BN_ADD_WORD_STACK (BN_RECIPROCAL_STACK DR_CSR)))))))))).

Definition RM_CS : Z := Z.max BN_CTX_START_STACK (Z.max BN_CTX_GET_STACK (Z.max BN_CTX_END_STACK (Z.max BN_SQR_STACKA (Z.max BN_MUL_TOP_STACK (BN_DIV_RECP_STACK DR_CS))))).
Definition RM_CM : Z := Z.max BN_SQR_COSTA BN_MUL_TOP_COST.
Definition RM_STACK : Z := BN_MOD_MUL_RECP_STACK RM_CS.
Definition RM_COST : Z := BN_MOD_MUL_RECP_COST RM_CM BN_DIV_RECP_COST.

Definition XR_CSL : Z := Z.max BN_COPY_STACK BN_NUM_BITS_STACK.
Definition XR_CS : Z := Z.max RM_STACK (Z.max BN_CTX_START_STACK (Z.max BN_CTX_GET_STACK (Z.max BN_CTX_END_STACK (Z.max BN_NNMOD_STACK (Z.max BN_SET_WORD_STACK (Z.max BN_NUM_BITS_STACK
                          (Z.max BN_COPY_STACK (Z.max (BN_RECP_CTX_SET_STACK XR_CSL) (Z.max RECP_INIT_STACK (Z.max RECP_FREE_STACK RT_STACK)))))))))).
Definition XR_STACK : Z := BN_MOD_EXP_RECP_STACK XR_CS.
Definition XR_COST : Z := BN_MOD_EXP_RECP_COST RM_COST.

Definition MM_CS : Z := Z.max BN_CTX_START_STACK (Z.max BN_CTX_GET_STACK (Z.max BN_CTX_END_STACK (Z.max BN_SQR_FIXED_STACKA (Z.max BN_MUL_FIXED_STACKA BN_FROM_MONT_WORD_STACK)))).
Definition MM_CM : Z := Z.max BN_SQR_FIXED_COST BN_MUL_TOP_COST.
Definition MM_STACK : Z := MMFT_STACK MM_CS.
Definition MM_COST : Z := MMFT_COST MM_CM BN_FROM_MONT_WORD_COST.
Definition MF_CS : Z := Z.max BN_CTX_START_STACK (Z.max BN_CTX_GET_STACK (Z.max BN_CTX_END_STACK (Z.max BN_COPY_STACK BN_FROM_MONT_WORD_STACK))).
Definition MF_STACK : Z := MONT_FROM2_STACK MF_CS.
Definition MF_COST : Z := MONT_FROM_COST BN_FROM_MONT_WORD_COST.
Definition M2_STACK : Z := MONT_MUL2_STACK MM_STACK.

Definition XM_CS : Z := Z.max BN_CTX_START_STACK (Z.max BN_CTX_GET_STACK (Z.max BN_CTX_END_STACK (Z.max BN_NNMOD_STACK (Z.max BN_SET_WORD_STACK (Z.max BN_NUM_BITS_STACK
                          (Z.max BN_UCMP_STACK (Z.max BN_WEXPAND_STACK (Z.max BN_MONT_CTX_NEW_STACK (Z.max BN_MONT_CTX_FREE_STACK (Z.max RT_STACK
                          (Z.max MM_STACK (Z.max MF_STACK MONT_SET_STACK_A)))))))))))).
Definition XM_STACK : Z := BN_MOD_EXP_MONT_STACK XM_CS.
Definition XM_COST : Z := BN_MOD_EXP_MONT_COST MM_COST MF_COST BN_MONT_CTX_SET_COST.

Definition XW_CS : Z := Z.max BN_CTX_START_STACK (Z.max BN_CTX_GET_STACK (Z.max BN_CTX_END_STACK (Z.max BN_SET_WORD_STACK (Z.max BN_MUL_WORD_STACK (Z.max BN_DIV_TOP_STACK
                          (Z.max BN_NUM_BITS_STACK (Z.max BN_MONT_CTX_NEW_STACK (Z.max BN_MONT_CTX_FREE_STACK (Z.max M2_STACK (Z.max MF_STACK MONT_SET_STACK_A)))))))))).
Definition XW_STACK : Z := BN_MOD_EXP_MONT_WORD_STACK XW_CS.
Definition XW_COST : Z := BN_MOD_EXP_MONT_WORD_COST MM_COST MF_COST BN_MONT_CTX_SET_COST.

Definition EXPC_CALLEE_STACK : Z := Z.max XR_STACK (Z.max XM_STACK XW_STACK).
Definition EXPC_COST : Z := Z.max XR_COST (Z.max XM_COST XW_COST).
Definition EXPC_STACK : Z := BN_MOD_EXP_STACK EXPC_CALLEE_STACK.

Definition SIMPLEC_STACK : Z := SIMPLE_STACK BN_SQR_STACKA.
Definition SIMPLEC_COST : Z := SIMPLE_COST BN_SQR_COSTA.

Lemma exp_stmtAn_f_wk : forall {AR : ARun} {UK : UnwindKit} ENTRY S C (d : nat) S' C' (d' : nat) one sixth,
  @exp_stmtAn_f AR UK ENTRY S C d one sixth -> S <= S' -> C <= C' -> (d <= d')%nat -> @exp_stmtAn_f AR UK ENTRY S' C' d' one sixth.
Proof.
  intros AR UK ENTRY S C d S' C' d' one sixth H HS HC HD. unfold exp_stmtAn_f in *. intros until qc. intros PRE ROOM. intros.
  eapply implA_cost_wk; [| exact HC].
  eapply H; try eassumption; [eapply bn_preA_wk; [exact PRE | exact HS | exact HC] | eapply fr_room_le; [exact ROOM | exact HD]].
Qed.

Section Closed.
Context {UK : UnwindKit} {BE : BnEdges}.

  Lemma BN_div_recp_closedF : forall (AR1 : ARun)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts (@ar_RT AR1)) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr rm : bnref) (ar am an ac : Z) (qc : bptr) (q : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo RM_CS BN_DIV_RECP_COST ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_DIV_RECP (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL rm am -> hpl PL rr -> rm <> ROne -> nbuf PL rm -> recp_at PL an -> In (q, an, 64) LB -> an mod 8 = 0 -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz 0 -> a1 = wz ar -> a2 = wz am -> a3 = wz an -> a4 = wz ac ->
    implA (BN_div_recp (tree_ops bptr) None (Some rr) rm ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA BN_DIV_RECP_COST (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_DIV_RECP) fc None m (seg_rom bgasegs)).
  Proof.
    intros until q. intros PRE. intros.
    eapply (@BN_div_recp_walkA AR1 UK BE DR_CS ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd)
              DR_CSR ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd)); fin.
  Qed.

  Lemma BN_mod_mul_reciprocal_closedF : forall (AR1 : ARun)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts (@ar_RT AR1)) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr rx ry : bnref) (ar ax ay an ac : Z) (qc : bptr) (q : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo XR_CS RM_COST ->
    fr_room 1 ls OW LB ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_MOD_MUL_RECIPROCAL (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL rx ax -> ref_at ls OW PL ry ay -> hpl PL rr -> rx <> ROne -> ry <> ROne -> nbuf PL rx -> nbuf PL ry ->
    recp_at PL an -> In (q, an, 64) LB -> an mod 8 = 0 -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz ay -> a3 = wz an -> a4 = wz ac ->
    implA (BN_mod_mul_reciprocal (tree_ops bptr) rr rx ry ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA RM_COST (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MOD_MUL_RECIPROCAL) fc None m (seg_rom bgasegs)).
  Proof.
    intros until q. intros PRE. intros.
    eapply (@BN_mod_mul_reciprocal_walkA AR1 UK BE RM_CS RM_CM BN_DIV_RECP_COST ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd)); fin.
    -   intros. finc (@BN_sqr_closedA AR1 UK BE BN_SQR_STACKA BN_SQR_COSTA ltac:(bnd) ltac:(bnd)).
    -   intros. finc (@BN_mul_walkA AR1 UK BE).
    -   intros. eapply (BN_div_recp_closedF AR1); fin.
  Qed.

  Theorem BN_mod_exp_recp_closedF : forall AR : ARun,
    @exp_stmtAn_f AR UK BN_MOD_EXP_RECP XR_STACK XR_COST 2 (BN_mod_exp_recp (tree_ops bptr)) None.
  Proof.
    intros AR.
    eapply (@BN_mod_exp_recp_walkA AR UK BE XR_CS XR_CSL RM_COST
              ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd)).
    exact BN_mod_mul_reciprocal_closedF.
  Qed.

  Definition mmft_closedF (AR1 : ARun) :=
    @bn_mul_mont_fixed_top_walkA AR1 UK BE MM_CS MM_CM BN_FROM_MONT_WORD_COST ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd)
      ltac:(intros; finc (@bn_sqr_fixed_top_closedA AR1 UK BE BN_SQR_FIXED_STACKA BN_SQR_FIXED_COST ltac:(bnd) ltac:(bnd)))
      ltac:(intros; finc (@bn_mul_fixed_top_walkA1 AR1 UK BE))
      ltac:(intros; finc (@bn_from_montgomery_word_walkA AR1 UK BE)).
  Definition mod_mul_mont_closedF (AR1 : ARun) := @BN_mod_mul_montgomery_walkA AR1 UK BE MM_STACK MM_COST ltac:(bnd) (mmft_closedF AR1).
  Definition to_mont_ft_closedF (AR1 : ARun) := @bn_to_mont_fixed_top_walkA AR1 UK BE MM_STACK MM_COST ltac:(bnd) (mmft_closedF AR1).
  Definition to_mont_closedF (AR1 : ARun) := @BN_to_montgomery_walkA AR1 UK BE MM_STACK MM_COST ltac:(bnd) (mmft_closedF AR1).
  Definition from_mont_closedF (AR1 : ARun) :=
    @BN_from_montgomery_walkA AR1 UK BE MF_CS BN_FROM_MONT_WORD_COST ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd)
      ltac:(intros; finc (@bn_from_montgomery_word_walkA AR1 UK BE)).

  Theorem BN_mod_exp_mont_closedF : forall AR : ARun,
    @exp_stmtAn_f AR UK BN_MOD_EXP_MONT XM_STACK XM_COST 4 (BN_mod_exp_mont (tree_ops bptr)) (Some (wz 0)).
  Proof.
    intros AR.
    eapply (@BN_mod_exp_mont_walkA AR UK BE XM_CS MM_COST MF_COST BN_MONT_CTX_SET_COST
              ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd)).
    - intros AR1. intros. finc (mmft_closedF AR1).
    - intros AR1. intros. finc (to_mont_ft_closedF AR1).
    - intros AR1. intros. finc (from_mont_closedF AR1).
    - intros AR1. intros. finc (@BN_MONT_CTX_set_closedA AR1 UK BE).
  Qed.

  Definition mont_word_closedF (AR : ARun) :=
    @BN_mod_exp_mont_word_walkA AR UK BE XW_CS MM_COST MF_COST BN_MONT_CTX_SET_COST
      ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd) ltac:(bnd)
      ltac:(intros; finc (mod_mul_mont_closedF AR))
      ltac:(intros; finc (to_mont_closedF AR))
      ltac:(intros; finc (from_mont_closedF AR))
      ltac:(intros; finc (@BN_MONT_CTX_set_closedA AR UK BE)).

  Theorem BN_mod_exp_closedF : forall AR : ARun,
    @exp_stmtAn_f AR UK BN_MOD_EXP EXPC_STACK EXPC_COST 4 (BN_mod_exp (tree_ops bptr)) None.
  Proof.
    intros AR.
    eapply (@BN_mod_exp_walkA AR UK BE EXPC_CALLEE_STACK EXPC_COST 4%nat ltac:(bnd)).
    - eapply exp_stmtAn_f_wk; [exact (BN_mod_exp_recp_closedF AR) | bnd | bnd | lia].
    - eapply exp_stmtAn_f_wk; [exact (BN_mod_exp_mont_closedF AR) | bnd | bnd | lia].
    - intros. finc (mont_word_closedF AR).
  Qed.

  Theorem BN_mod_exp_closedA : forall AR : ARun, @ar_FR AR = [] ->
    @ExpKitA.exp_stmtA_f AR UK BN_MOD_EXP EXPC_STACK EXPC_COST 4 (BN_mod_exp (tree_ops bptr)) None.
  Proof. intros AR _. apply exp_stmtA_f_of_n. exact (BN_mod_exp_closedF AR). Qed.

  Theorem BN_mod_exp_simple_closed2A : forall AR : ARun, @ar_FR AR = [] ->
    @ExpKitA.exp_stmtA AR UK BN_MOD_EXP_SIMPLE SIMPLEC_STACK SIMPLEC_COST 2 (BN_mod_exp_simple (tree_ops bptr)) None.
  Proof.
    intros AR E.
    exact (@BN_mod_exp_simple_closedA UK BE BN_SQR_STACKA BN_SQR_COSTA ltac:(bnd)
             (fun AR1 => @BN_sqr_closedA AR1 UK BE BN_SQR_STACKA BN_SQR_COSTA ltac:(bnd) ltac:(bnd)) AR E).
  Qed.
End Closed.

Lemma EXPC_STACK_ok : 0 <= EXPC_STACK <= 0x18000. Proof. split; bnd. Qed.
Lemma SIMPLEC_STACK_ok : 0 <= SIMPLEC_STACK <= 0x18000. Proof. split; bnd. Qed.
Lemma EXPC_COST_ok : 0 <= EXPC_COST. Proof. bnd. Qed.
Lemma SIMPLEC_COST_ok : 0 <= SIMPLEC_COST. Proof. bnd. Qed.
Lemma EXPC_TOTAL_ok : EXPC_COST + SIMPLEC_COST + 2048 <= 2 ^ 31. Proof. bnd. Qed.
