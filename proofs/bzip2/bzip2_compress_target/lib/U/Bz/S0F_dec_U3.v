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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDU2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF DecTacFR S0F_decRet S0F_decCutsA S0F_gb_E.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_gb_G.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_gb_G.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_gb_G.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacFR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCutsA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_gb_E OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_gb_G.S0F_gb_F OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_gb_G OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_gb_G.S0F_gb_H.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require NormFast. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require FLiaA.
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
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= FLiaA.lia_f.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.

Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.
  Variable F : nat.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  Ltac ret_data MUL WML DP :=
    revive_all MUL WML AOK; enter_retF (S0F_dec_ret_data A AOK) DP.
  Ltac next := gbF_next [S; S + 3152; usp + -336]%Z [(S, S + 68); (S + 3152, S + 3196)]%Z.
  (* [comment removed for export] *)
  Ltac endhdr_tail MUL WML DP uc K EQ :=
    wstepl; wstepl; gbv 11%Z 8%Z uc; wstepl; wstepl;
    match goal with H : kq _ _ |- _ => rewrite EQ in H end;
    wstepl; if_cases K; zify_cond_z K;
    [ match goal with H : kq _ _ |- _ => rewrite if_falseP in H by blia; rewrite dgo_DRet in H end; ret_data MUL WML DP
    | match goal with H : kq _ _ |- _ => rewrite if_trueP in H by blia; rewrite dgo_DGo in H end ].
  (* [comment removed for export] *)
  Ltac ccrc_tail uc EQ :=
    wstepl; wstepl; wstepl; wstepl; wstepl; wstepl; gbv 10%Z 8%Z uc; wstepl; wstepl;
    match goal with H : rw_cells _ _ (b_s _ + 3152)%Z _ |- _ => crc_cellA H 28%nat end;
    match goal with H : kq _ _ |- _ => rewrite EQ, dgo_DGo in H end.

  Lemma S0F_dec_U3 : S0F_cut_HEND A F.
  Proof.
    unfold S0F_cut_HEND. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold W14, D14, DSTATE_SIZE in MU. cbn [app blk_ivls b_s b_strm] in MU.
    unfold dinv_HEND, nb_ok in DI.
    open_dmemF DM. s2img.
    (* [comment removed for export] *)
    gbF_call (S0F_gb_1c464 A AOK (QF A) (S0F_dec_ret_ok A AOK) _ _ _ _ JK_) MU WM AOK DP FU. next.
    endhdr_tail MUL WML DP u1 K1 gb_after_42.
    (* [comment removed for export] *)
    gbF_call (S0F_gb_1cd5c A AOK (QF A) (S0F_dec_ret_ok A AOK) _ _ _ _ JK_) MUL WML AOK DP FU. next.
    endhdr_tail MUL WML DP u2 K2 gb_after_43.
    (* [comment removed for export] *)
    gbF_call (S0F_gb_1cdf8 A AOK (QF A) (S0F_dec_ret_ok A AOK) _ _ _ _ JK_) MUL WML AOK DP FU. next.
    endhdr_tail MUL WML DP u3 K3 gb_after_44.
    (* [comment removed for export] *)
    gbF_call (S0F_gb_1ce94 A AOK (QF A) (S0F_dec_ret_ok A AOK) _ _ _ _ JK_) MUL WML AOK DP FU. next.
    endhdr_tail MUL WML DP u4 K4 gb_after_45.
    (* [comment removed for export] *)
    gbF_call (S0F_gb_1cf30 A AOK (QF A) (S0F_dec_ret_ok A AOK) _ _ _ _ JK_) MUL WML AOK DP FU. next.
    endhdr_tail MUL WML DP u5 K5 gb_after_46.
    (* [comment removed for export] *)
    wstepl. wstepl.
    (* [comment removed for export] *)
    gbF_call (S0F_gb_1cfd0 A AOK (QF A) (S0F_dec_ret_ok A AOK) _ _ _ _ JK_) MUL WML AOK DP FU. next.
    ccrc_tail u6 gb_after_47.
    gbF_call (S0F_gb_1d074 A AOK (QF A) (S0F_dec_ret_ok A AOK) _ _ _ _ JK_) MUL WML AOK DP FU. next.
    ccrc_tail u7 gb_after_48.
    gbF_call (S0F_gb_1d118 A AOK (QF A) (S0F_dec_ret_ok A AOK) _ _ _ _ JK_) MUL WML AOK DP FU. next.
    ccrc_tail u8 gb_after_49.
    (* [comment removed for export] *)
    gbF_call (S0F_gb_1d1bc A AOK (QF A) (S0F_dec_ret_ok A AOK) _ _ _ _ JK_) MUL WML AOK DP FU. next.
    wstepl. wstepl. wstepl. wstepl. wstepl. wstepl. wstepl. wstepl. gbv 10%Z 8%Z u9. wstepl. wstepl.
    crc_cellA MIDc 28%nat.
    rewrite gb_after_50, dgo_DRet in KQ.
    wstepl. wstepl.
    revive_all MUL WML AOK. enter_retF (S0F_dec_ret A AOK) DP.
  Qed.
End R.

End ACeilS1.
