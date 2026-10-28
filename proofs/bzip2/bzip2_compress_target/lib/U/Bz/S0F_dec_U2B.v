(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts BzContracts0 DecCut DecTac DecAux S0_dec_U13.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDU2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF DecTacFR S0F_decRet S0F_decCutsA.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_gb_E.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_gb_E.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_gb_E.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacFR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCutsA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_gb_E.S0F_gb_C OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_gb_E.S0F_gb_D OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_gb_E.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import U0_decKit.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import DecFast DecFastT.
Local Ltac DecCut.revive H MUL WML AOK ::= DecFast.revive_cached H MUL WML AOK.
Local Ltac DecCut.dpure_from DP ::= DecFast.dpure_from_fast DP.
Local Ltac DecCut.open_dmem DM ::= DecFast.open_dmem_red DM.
Local Ltac DecTac.gb_next keep Wloc IB ::= DecFastT.gb_next_red keep Wloc IB.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzImg0TacFR BzImg0Tac.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require NormFast. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLiaA RelLia.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= RelLiaA.lia_rf.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Local Ltac StoreFast.tlia ::= RelLia.tlia_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Ltac lor8_norm_in H :=
  repeat match type of H with
  | context [Z.lor (Z.shiftl ?a 8) ?b] => rewrite (lor_shiftl8 a b) in H by (dmodel_cbn; unset_Z; lia)
  end.
(* [comment removed for export] *)
Ltac or_lin := first [ rewrite lor_mul256_byte by (unset_Z; lia) | rewrite Z.lor_0_l | rewrite Z.lor_0_r | idtac ].

Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.
  Variable F : nat.
  Hypothesis HMAP : forall F', (F' < F)%nat -> S0F_cut_HMAP A F'.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  Ltac next := gbF_next [S; S + 3152]%Z [(S, S + 68); (S + 3152, S + 3196)]%Z.
  (* [comment removed for export] *)
  Ltac bcrc_tail uc EQ :=
    wstepl; wstepl; wstepl; wstepl; gbv 11%Z 8%Z uc; wstepl; wstepl; wstepl;
    match goal with H : rw_cells _ _ (b_s _ + 3152)%Z _ |- _ => crc_cellA H 24%nat end;
    match goal with H : kq _ _ |- _ => rewrite EQ, dgo_DGo in H end; kq_norm.
  Ltac wb_reg r :=
    let v := reg_val r in lazymatch v with sx32 (Z_to_bv 64 ?b) =>
      let W := fresh "WBr" in assert (W : (bv_unsigned (sx32 (Z_to_bv 64 b)) mod 4294967296 = b)%Z) by (apply sx32_mod32; lia) end.
  Ltac ck := tryif notrap then idtac else idtac.

  Lemma S0F_dec_U2B : S0F_cut_HBCRC A F.
  Proof.
    unfold S0F_cut_HBCRC. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold W14, D14, DSTATE_SIZE in MU. cbn [app blk_ivls b_s b_strm] in MU.
    unfold dinv_HBCRC, nb_ok in DI. destruct DI as [NB SB0].
    (* [comment removed for export] *)
    assert (SB : (0 <= d_sbcrc d < 4294967296)%Z) by exact SB0. clear SB0.
    open_dmemF DM. s2img.
    (* [comment removed for export] *)
    gbF_call (S0F_gb_1c79c A AOK (QF A) (S0F_dec_ret_ok A AOK) _ _ _ _ JK_) MU WM AOK DP FU. next.
    bcrc_tail u1 gb_after_20.
    gbF_call (S0F_gb_1c844 A AOK (QF A) (S0F_dec_ret_ok A AOK) _ _ _ _ JK_) MUL WML AOK DP FU. next.
    bcrc_tail u2 gb_after_21.
    gbF_call (S0F_gb_1c8e8 A AOK (QF A) (S0F_dec_ret_ok A AOK) _ _ _ _ JK_) MUL WML AOK DP FU. next.
    bcrc_tail u3 gb_after_22.
    gbF_call (S0F_gb_1c98c A AOK (QF A) (S0F_dec_ret_ok A AOK) _ _ _ _ JK_) MUL WML AOK DP FU. next.
    bcrc_tail u4 gb_after_23.
    (* [comment removed for export] *)
    gbF_call (S0F_gb_1ca30 A AOK (QF A) (S0F_dec_ret_ok A AOK) _ _ _ _ JK_) MUL WML AOK DP FU. next.
    wstepl. wstepl. gbv 11%Z 1%Z rb.
    sb_step. wstepl. wstepl.
    rewrite gb_after_24, dgo_DGo in KQ.
    (* [comment removed for export] *)
    gbF_call (S0F_gb_1cac8 A AOK (QF A) (S0F_dec_ret_ok A AOK) _ _ _ _ JK_) MUL WML AOK DP FU. next.
    lor8_norm_in HD.
    wstepl. wstepl. wb_reg 12%Z. wstepl. wstepl. wstepl. ck. wstepl. wstepl. wstepl. gbv 10%Z 8%Z v1. wstepl. or_lin. wstepl.
    rewrite gb_after_25, dgo_DGo in KQ.
    (* [comment removed for export] *)
    gbF_call (S0F_gb_1cb6c A AOK (QF A) (S0F_dec_ret_ok A AOK) _ _ _ _ JK_) MUL WML AOK DP FU. next.
    lor8_norm_in HD.
    wstepl. wstepl. wb_reg 12%Z. wstepl. wstepl. wstepl. ck. wstepl. wstepl. wstepl. gbv 10%Z 8%Z v2. wstepl. or_lin. wstepl.
    rewrite gb_after_26, dgo_DGo in KQ.
    (* [comment removed for export] *)
    gbF_call (S0F_gb_1cc10 A AOK (QF A) (S0F_dec_ret_ok A AOK) _ _ _ _ JK_) MUL WML AOK DP FU. next.
    lor8_norm_in HD.
    wstepl. wstepl. wb_reg 12%Z. wstepl. wstepl. wstepl. ck. wstepl. wstepl. wstepl. wstepl. wstepl. gbv 10%Z 8%Z v3.
    wstepl. wstepl. or_lin. wstepl. wstepl. wstepl. wstepl. ck.
    rewrite edge_27 in KQ. kq_norm. lor8_norm_in KQ.
    rewrite if_falseP in KQ by blia.
    wstepl. rewrite ?lor_bs100k. wstepl.
    wstepl; if_cases KO; zify_cond_z KO.
    { rewrite if_trueP in KQ by blia.
      revive_all MUL WML AOK. enter_retF (S0F_dec_ret_data A AOK) DP. }
    rewrite if_falseP in KQ by blia.
    wstepl. wstepl. wstepl. wstepl. if_false_z.
    revive_all MUL WML AOK. enter_nextF HMAP DP.
    unfold dinv_HMAP, nb_ok, op_ok, hdr_ok; dmodel_cbn.
    repeat match goal with |- _ /\ _ => split end; try (intros; exfalso; lia); unset_Z; first [lia | unfold u32; lia].
  Qed.
End R.

End ACeilS1.
