(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts DecCut DecTac DecAux.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDU2 DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFB DecTacFB DecTacFRB B0F_decV B0F_decRet B0F_decCutsA B0F_gb_A.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCutsA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_gb_A.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NormFast FLiaA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
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
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecTac2.
Local Ltac AsanKit.a_norm ::= DecTac2.lit_store_fix.

Section ACeilS1. Context {ACEIL__ : ACeil}.
Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok BIHI0 A.
  Hypothesis ASH : act_sh DI_B0 A.
  Variable Q : dres -> machine_state -> Prop.
  Hypothesis HRETOK : B0F_RET_OK A Q.
  Hypothesis HRETD : B0F_RET_DATA A Q.
  Variable F : nat.
  Hypothesis HEND : forall F', (F' < F)%nat -> B0F_cut_HEND A Q F'.
  Hypothesis HBCRC : forall F', (F' < F)%nat -> B0F_cut_HBCRC A Q F'.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  (* [comment removed for export] *)
  Ltac ret_data MUL WML DP :=
    astep; revive_all MUL WML AOK; enter_retF HRETD DP.
  Ltac next := gbF_nextA [S; S + 3152; a_P A; a_P A + 344]%Z [(S, S + 68); (S + 3152, S + 3196)]%Z.
  (* [comment removed for export] *)
  Ltac tail5 uc := arun_lwbuf; arun_gbv 8%Z uc.

  Lemma B0F_dec_U2A : B0F_cut_H14 A Q F.
  Proof.
    unfold B0F_cut_H14. intros until w752. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    unfold dinv_H14, nb_ok in DI. pose proof (dpureF_cbn _ _ _ _ _ _ DP) as CR0.
    open_dmemF DM. b0img.
    (* [comment removed for export] *)
    gbF_call (B0F_gb_aa508 A AOK ASH Q HRETOK _ _ _ _ JK_) MU WM AOK DP FU. next. tail5 u1.
    rewrite gb_after_14 in KQ.
    brun; if_cases K1; zify_cond_z K1.
    2: { (* [comment removed for export] *)
      rewrite if_trueP in KQ by blia. rewrite dgo_DGo in KQ. brun_to 0xab884%Z.
      revive_all MUL WML AOK. enter_nextF HEND DP. unfold dinv_HEND, nb_ok; dmodel_cbn; lia. }
    rewrite if_falseP in KQ by blia.
    (* [comment removed for export] *)
    brun; if_cases K1'; zify_cond_z K1';
      [ rewrite if_trueP in KQ by blia; rewrite dgo_DGo in KQ
      | rewrite if_falseP in KQ by blia; rewrite dgo_DRet in KQ; ret_data MUL WML DP ].
    (* [comment removed for export] *)
    gbF_call (B0F_gb_aa5a4 A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU. next. tail5 u2.
    rewrite gb_after_15 in KQ.
    brun; if_cases K2; zify_cond_z K2; [ rewrite if_trueP in KQ by blia; rewrite dgo_DGo in KQ | rewrite if_falseP in KQ by blia; rewrite dgo_DRet in KQ; ret_data MUL WML DP ].
    gbF_call (B0F_gb_aa634 A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU. next. tail5 u3.
    rewrite gb_after_16 in KQ.
    brun; if_cases K3; zify_cond_z K3; [ rewrite if_trueP in KQ by blia; rewrite dgo_DGo in KQ | rewrite if_falseP in KQ by blia; rewrite dgo_DRet in KQ; ret_data MUL WML DP ].
    gbF_call (B0F_gb_aa6c4 A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU. next. tail5 u4.
    rewrite gb_after_17 in KQ.
    brun; if_cases K4; zify_cond_z K4; [ rewrite if_trueP in KQ by blia; rewrite dgo_DGo in KQ | rewrite if_falseP in KQ by blia; rewrite dgo_DRet in KQ; ret_data MUL WML DP ].
    gbF_call (B0F_gb_aa754 A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU. next. tail5 u5.
    rewrite gb_after_18 in KQ.
    brun; if_cases K5; zify_cond_z K5; [ rewrite if_trueP in KQ by blia; rewrite dgo_DGo in KQ | rewrite if_falseP in KQ by blia; rewrite dgo_DRet in KQ; ret_data MUL WML DP ].
    gbF_call (B0F_gb_aa7e4 A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU. next. tail5 u6.
    rewrite gb_after_19 in KQ.
    brun; if_cases K6; zify_cond_z K6; [ rewrite if_trueP in KQ by blia; rewrite dgo_DGo in KQ | rewrite if_falseP in KQ by blia; rewrite dgo_DRet in KQ; ret_data MUL WML DP ].
    (* [comment removed for export] *)
    brun. if_true_z.
    brun_to 0xaabb4%Z.
    revive_all MUL WML AOK. enter_nextF HBCRC DP. unfold dinv_HBCRC, nb_ok; dmodel_cbn; lia.
  Qed.
End R.
End ACeilS1.
