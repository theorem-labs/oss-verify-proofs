(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts BzContracts0 DecCut DecTac DecTac2 DecAux S0_dec_U13.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF DecTacFR S0F_decRet S0F_decCuts S0F_gb_Q.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacFR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCuts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_gb_Q.
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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require NormFast. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require FLiaA. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require SasFastF.
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
Local Ltac simpl_arr_sizes ::= SasFastF.sas6F_all.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.
Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  Ltac prep DM MU :=
    unfold W14, D14, DSTATE_SIZE in MU; cbn [app blk_ivls b_s b_strm] in MU; open_dmemF DM; s2img.

  (* [comment removed for export] *)
  Lemma S0F_U5_L5I : forall F,
    (forall F', (F' < F)%nat -> S0F_cut_L5I A F') -> (forall F', (F' < F)%nat -> S0F_cut_L5O A F') -> S0F_cut_L5I A F.
  Proof.
    intros F HL5I HL5O. unfold S0F_cut_L5I. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    destruct DI as [[AL NBL] [NG [NS [Hi [Hj SOK]]]]]. prep DM MU.
    gbF_call (S0F_gb_1d940 A AOK (QF A) (S0F_dec_ret_ok A AOK) (S0F_dec_ret A AOK) _ _ _ _ JK_) MU WM AOK DP FU.
    gbF_next [S; S + 25886; usp + -336]%Z [(S, S + 68); (S + 25886, S + 43888); (usp + -336, usp)]%Z.
    unfold r_of in DR. dr_open. hide_all_but_at [S; S + 25886; usp + -336]%Z.
    (* [comment removed for export] *)
    wstepl. wstepl. gbv 14%Z 1%Z ubit.
    wstepl.
    wstepl; if_cases Kbit; zify_cond_z Kbit.
    - (* [comment removed for export] *)
      rewrite edge_32_0' in KQ by lia.
      wstepl. wstepl.
      wstepl; if_cases K18; zify_cond_z K18.
      + (* [comment removed for export] *)
        rewrite if_falseP in KQ by blia.
        wstepl. wstepl. notrap. wstepl. wstepl. wstepl.
        revive_all MUL WML AOK. 
        enter_nextF HL5O DP.
        unfold dinv_L5O, alpha_ok. dmodel_cbn.
        repeat match goal with |- _ /\ _ => split end; try lia.
        replace (Z.min (sv_i L + 1) 18002)%Z with (Z.min (sv_i L) 18002)%Z by lia. exact SOK.
      + (* [comment removed for export] *)
        rewrite if_trueP in KQ by blia.
        wstepl. notrap. wstepl. wstepl. wstepl. wstepl. wstepl. notrap. wstepl. wstepl.
        lazymatch goal with H : u8arr _ _ (S + 25886)%Z _ |- _ =>
          zb8_sb H (sv_i L); try rewrite (Z.mod_small (sv_j L) 256) in H by lia end.
        wstepl. wstepl. notrap. wstepl. wstepl. wstepl.
        revive_all MUL WML AOK.
        enter_nextF HL5O DP.
        unfold dinv_L5O, alpha_ok. dmodel_cbn.
        repeat match goal with |- _ /\ _ => split end; try lia.
        replace (Z.min (sv_i L + 1) 18002)%Z with (Z.min (sv_i L) 18002 + 1)%Z by lia.
        rewrite Z.min_l by lia. apply belown_set; [|lia]. rewrite <- (Z.min_l (sv_i L) 18002) by lia. exact SOK.
    - (* [comment removed for export] *)
      rewrite edge_32_1 in KQ by lia.
      wstepl. wstepl. wstepl. notrap. wstepl.
      wstepl; if_cases KR; zify_cond_z KR.
      + rewrite if_falseP in KQ by blia. rewrite dgo_DGo in KQ.
        revive_all MUL WML AOK.
        enter_nextF HL5I DP.
        unfold dinv_L5I, alpha_ok. dmodel_cbn.
        repeat match goal with |- _ /\ _ => split end; try lia. exact SOK.
      + rewrite if_trueP in KQ by blia. rewrite dgo_DRet in KQ.
        wstepl. wstepl. wstepl.
        revive_all MUL WML AOK. enter_retF (S0F_dec_ret A AOK) DP.
  Qed.

  (* [comment removed for export] *)
  Lemma S0F_U5_L5O : forall F, S0F_cut_L5I A F -> S0F_cut_HUND A F -> S0F_cut_L5O A F.
  Proof.
    intros F HL5I HHUND. unfold S0F_cut_L5O. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    destruct DI as [[AL NBL] [NG [NS [Hi SOK]]]]. prep DM MU.
    destruct (Z_lt_le_dec (sv_i L) (sv_nSelectors L)) as [LT|GE].
    - rewrite K_L5O_lt by exact LT.
      hide_all_but_at [S; usp + -336]%Z.
      pose proof (munch_refl [(S, S); (usp + -336, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
      (* [comment removed for export] *)
      wstepl. if_false_z. step. change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)). mem_after_store. wstepl. wstepl. wstepl. wstepl. wstepl.
      revive_all MUL WML AOK.
      enter_cutF (HL5I _ _ _ JK_) DP.
      unfold dinv_L5I, alpha_ok. dmodel_cbn.
      repeat match goal with |- _ /\ _ => split end; try lia. exact SOK.
    - rewrite K_L5O_ge by exact GE.
      wstepl. if_true_z.
      enter_cutF (HHUND _ _ _ JK_) DP.
      unfold dinv_HUND, alpha_ok. dmodel_cbn.
      repeat match goal with |- _ /\ _ => split end; try lia.
      replace (sv_nSelectors L) with (sv_i L) by lia. exact SOK.
  Qed.
End R.
End ACeilS1.
