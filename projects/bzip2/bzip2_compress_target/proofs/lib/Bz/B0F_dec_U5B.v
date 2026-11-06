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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts DecCut DecTac DecTac2 DecAux.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFB DecTacFB DecTacFRB B0F_decV B0F_decRet B0F_decCuts5 B0F_gb_D.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCuts5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_gb_D.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.   (* [comment removed for export] *)
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
  Hypothesis HRET : B0F_RET A Q.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  (* [comment removed for export] *)
  Lemma B0F_U5_L5I : forall F,
    (forall F', (F' < F)%nat -> B0F_cut_L5I A Q F') -> (forall F', (F' < F)%nat -> B0F_cut_L5O A Q F') -> B0F_cut_L5I A Q F.
  Proof.
    intros F HL5I HL5O. unfold B0F_cut_L5I. intros until w752. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    destruct DI as [[AL NBL] [NG [NS [Hi [Hj SOK]]]]]. open_dmemF DM. b0img.
    gbF_call (B0F_gb_b07d8 A AOK ASH Q HRETOK _ _ _ _ JK_) MU WM AOK DP FU.
    gbF_nextA [S; S + 25886; a_P A; a_P A + 344]%Z [(S, S + 68); (S + 25886, S + 43888); (a_P A + 344, a_P A + 760)]%Z.
    unfold r_of in DR. dr_open. hide_all_but_atF [S; S + 25886; a_P A; a_P A + 344]%Z.
    arun_lwbuf. arun_gbv 1%Z ubit.
    (* [comment removed for export] *)
    brun; if_cases Kbit; zify_cond_z Kbit.
    - (* [comment removed for export] *)
      rewrite edge_32_0' in KQ by lia.
      brun; if_cases K18; zify_cond_z K18.
      + (* [comment removed for export] *)
        rewrite if_falseP in KQ by blia.
        brun_to 0xb0a34%Z.
        revive_all MUL WML AOK.
        enter_nextF HL5O DP.
        unfold dinv_L5O, alpha_ok. dmodel_cbn.
        repeat match goal with |- _ /\ _ => split end; try lia.
        replace (Z.min (sv_i L + 1) 18002)%Z with (Z.min (sv_i L) 18002)%Z by lia. exact SOK.
      + (* [comment removed for export] *)
        rewrite if_trueP in KQ by blia.
        brun_to 0xb0d04%Z.
        lazymatch goal with H : u8arr _ _ (S + 25886)%Z _ |- _ =>
          zb8_sb H (sv_i L); try rewrite (Z.mod_small (sv_j L) 256) in H by lia end.
        brun_to 0xb0a34%Z.
        revive_all MUL WML AOK.
        enter_nextF HL5O DP.
        unfold dinv_L5O, alpha_ok. dmodel_cbn.
        repeat match goal with |- _ /\ _ => split end; try lia.
        replace (Z.min (sv_i L + 1) 18002)%Z with (Z.min (sv_i L) 18002 + 1)%Z by lia.
        rewrite Z.min_l by lia. apply belown_set; [|lia]. rewrite <- (Z.min_l (sv_i L) 18002) by lia. exact SOK.
    - (* [comment removed for export] *)
      rewrite edge_32_1 in KQ by lia.
      (* [comment removed for export] *)
      brun; if_cases KR; zify_cond_z KR.
      + rewrite if_falseP in KQ by blia. rewrite dgo_DGo in KQ.
        brun_to 0xb0a9c%Z.
        revive_all MUL WML AOK.
        enter_nextF HL5I DP.
        unfold dinv_L5I, alpha_ok. dmodel_cbn.
        repeat match goal with |- _ /\ _ => split end; try lia. exact SOK.
      + rewrite if_trueP in KQ by blia. rewrite dgo_DRet in KQ.
        brun_to 0xafb90%Z.
        revive_all MUL WML AOK. enter_retF HRET DP.
  Qed.

  (* [comment removed for export] *)
  Lemma B0F_U5_L5O : forall F, B0F_cut_L5I A Q F -> B0F_cut_HUND A Q F -> B0F_cut_L5O A Q F.
  Proof.
    intros F HL5I HHUND. unfold B0F_cut_L5O. intros until w752. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    destruct DI as [[AL NBL] [NG [NS [Hi SOK]]]]. open_dmemF DM. b0img.
    unfold r_of in DR. dr_open. hide_all_but_atF [S; a_P A; a_P A + 344]%Z.
    pose proof (munch_refl [(a_P A, a_P A + 128); (a_P A + 344, a_P A + 760)]%Z m) as MUL. pose proof (wmono_refl b0segs m) as WML.
    destruct (Z_lt_le_dec (sv_i L) (sv_nSelectors L)) as [LT|GE].
    - rewrite K_L5O_lt by exact LT.
      (* [comment removed for export] *)
      brun. if_cases KX; zify_cond_z KX; [exfalso; lia|].
      brun_to 0xb0a9c%Z. sh_norm.
      revive_all MUL WML AOK.
      enter_cutF (HL5I _ _ _ JK_) DP.
      unfold dinv_L5I, alpha_ok. dmodel_cbn.
      repeat match goal with |- _ /\ _ => split end; try lia. exact SOK.
    - rewrite K_L5O_ge by exact GE.
      brun. if_cases KX; zify_cond_z KX; [|exfalso; lia].
      revive_all MUL WML AOK.
      enter_cutF (HHUND _ _ _ JK_) DP.
      unfold dinv_HUND, alpha_ok. dmodel_cbn.
      repeat match goal with |- _ /\ _ => split end; try lia.
      replace (sv_nSelectors L) with (sv_i L) by lia. exact SOK.
  Qed.
End R.
End ACeilS1.
