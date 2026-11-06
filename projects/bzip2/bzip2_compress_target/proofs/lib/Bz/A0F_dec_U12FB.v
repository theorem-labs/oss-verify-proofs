(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts DecCut DecTac DecTac2 DecAux.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzLemmasT BzLemmasT2 BzWalkArith3 BzDU5 BzDUM BzDU11 BzDU12F DecTacF3 DecAux12F DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU11 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12F OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux12F OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFA DecTacFA DecTacFRA A0F_decV A0F_decRet DecTacSA A0F_decRet3 A0F_decCutsE A0F_decCuts12F A0F_dec_U12FA.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacSA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCutsE OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCuts12F OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_dec_U12FA.
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
  Hypothesis AOK : act_ok AIHI0 A.
  Hypothesis ASH : act_sh DI_A0 A.
  Variable Q : dres -> machine_state -> Prop.
  Hypothesis HRETP3 : A0F_RETP3 A Q.
  Variable F : nat.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).
  Notation TT := (b_tt (a_cx A)).

  Ltac prepS DM MU DP SM :=
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN; pose proof rnums_words_length as RNL; lin_natZ RNL;
    unfold_W14 MU; open_ash ASH AOK;
    lazymatch goal with H : sanchor (b_s _) (a_shs _) |- _ => pose proof (proj2 H : saddr (b_s (a_cx A)) (a_shs A)) as ANS0 end;
    unfold_blk SM MU; open_shb SM; open_dmemF DM; a0img.
  Ltac fold_MU MU SM :=
    lazymatch type of MU with munch ?W ?ma ?mb =>
      let H := fresh "MUf" in
      assert (H : munch (W14 A) ma mb)
        by (unfold W14, DSTATE_SIZE, blk_ivls; rewrite SM; cbn [Z.eqb app]; exact MU);
      clear MU; rename H into MU end.
  Ltac blk_goal D :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let B := fresh "BLK" in assert (B : blk_at a0segs mm cx (blk_of cx D)) end.

  Lemma A0F_U12_AFT : forall sym tt0, A0F_cut_AFT A Q F sym tt0.
  Proof.
    intros sym tt0. unfold A0F_cut_AFT. intros until w720. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    cps_pose (dinv_AFT_facts L d sym tt0 DI) as (TPR & ALL28 & ALL32).
    cps_pose DI as (_ & ORIG & NB1 & NB9 & HDR & TS & SM0 & _).
    cps_pose HDR as (RND & SBC & OPR). cps_pose TS as (STT & SOL & SOCH & SCB).
    pose proof (dpureF_small _ _ _ _ _ _ DP) as SMALL. rewrite SM0 in SMALL. symmetry in SMALL.
    pose proof (dpureF_n _ _ _ _ _ _ DP) as BN.
    prepS DM MU DP SMALL.
    unfold blk_of in BLK. rewrite SMALL in BLK. cbn [Z.eqb blk_at] in BLK. cps_destruct BLK as (_ & TTA & TTL).
    pose proof (act_tt_s _ _ AOK SMALL) as [[TT0 TT1] SEPtt].
    pose proof (act_img_s _ _ AOK : id _) as SEPimg.
    assert (SH8 : forall x, Z.shiftr x 8 = (x / 256)%Z) by (intros; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    unfold aft_tp in TPR. rewrite SH8 in TPR. pose proof (ALL28 (d_origPtr d) ltac:(lia)) as VOR.
    unfold r_of in DR. dr_open. hide_all_but_atF [S; S + 1092; S + 3152; TT; 788152; 804096; a_P A; a_P A + 496]%Z.
    pose proof (munch_refl [(S, S + 68); (S + 1092, S + 1096); (a_P A + 496, a_P A + 728)]%Z m) as MUL. pose proof (wmono_refl a0segs m) as WML.
    kq_intro.
    (* [comment removed for export] *)
    arun_to 0xa7308%Z.
    pose proof (zw32_read a0segs m TT (d_tt d) _ (d_origPtr d) _ TTA ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD.
    astep. clear RD.
    pose proof (ALL28 (zget (d_tt d) (d_origPtr d) / 256)%Z ltac:(lia)) as VTR. pose proof (ALL32 (zget (d_tt d) (d_origPtr d) / 256)%Z) as VTR32.
    (* [comment removed for export] *)
    arun_to 0xa7344%Z. astep. rewrite ?zxb_lit8 by lia.
    arun; if_cases Kbr; zify_cond_z Kbr.
    - (* [comment removed for export] *)
      rewrite (be_aft_nr L d s) in KQ by (unfold aft_tp; rewrite ?SH8; lia). rewrite dgo_DRet in KQ. unfold aft_nr, aft_w, aft_tp in KQ. rewrite !SH8 in KQ.
      remember (zget (d_tt d) (d_origPtr d) / 256)%Z as tp eqn:Etp.
      arun; if_cases Ktp; zify_cond_z Ktp; [exfalso; lia|].
      arun_to 0xa74e0%Z.
      lazymatch goal with TTAc : u32arr _ ?mm TT _ |- _ =>
        pose proof (zw32_read a0segs mm TT (d_tt d) _ tp _ TTAc ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
      astep. clear RD.
      arun_to 0xa7450%Z.
      clear SEPtt SEPimg. revive_all_smA AOK MUL WML.
      lazymatch type of KQ with kq _ (DRet _ _ ?d7 _) => blk_goal d7 end.
      { unfold blk_of. rewrite SMALL. cbn [Z.eqb blk_at]. dmodel_cbn. split; [exact SMALL|]. split; [exact TTA| exact TTL]. }
      clear TTA. fold_MU MU SMALL.
      kq_fold. enter_cutF (HRETP3 _ _ _ _ JK_) DP; [ ret_nb | ].
      intros _. pose proof (dout_ok_aft_nr L d sym tt0 DI Kbr ltac:(lia)) as OK. unfold aft_nr, aft_w, aft_tp in OK. rewrite !SH8 in OK. subst tp. exact OK.
    - (* [comment removed for export] *)
      rewrite (be_aft_r L d s) in KQ by (unfold aft_tp; rewrite ?SH8; lia). rewrite dgo_DRet in KQ. unfold aft_r, aft_w, aft_tp in KQ. rewrite !SH8 in KQ.
      remember (zget (d_tt d) (d_origPtr d) / 256)%Z as tp eqn:Etp.
      (* [comment removed for export] *)
      arun; if_cases Ktp; zify_cond_z Ktp; [exfalso; lia|].
      arun_to 0xa73c0%Z.
      lazymatch goal with TTAc : u32arr _ ?mm TT _ |- _ =>
        pose proof (zw32_read a0segs mm TT (d_tt d) _ tp _ TTAc ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
      astep. clear RD.
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      arun_to 0xa73f0%Z.
      lazymatch goal with MUc : munch ?W (a_m0 A) ?mm, SHRc : shzW _ ?W _ 804096%Z _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (SHRc mm 804096%Z MUc ltac:(lia)) as RDs end.
      change (804096 / 8 + 2147450880)%Z with 2147551392%Z in RDs.
      astep. clear RDs. rewrite ?sxb_z8.
      arun_to 0xa73fc%Z.
      lazymatch goal with RNc : u32arr _ ?mm _ rnums_words |- _ =>
        pose proof (u32arr_read a0segs mm _ rnums_words 0 (Z_to_bv 64 (rNums 0)) _ RNc (rnums_words_nth12 0 ltac:(lia)) ltac:(lia) eq_refl) as RDr end.
      astep. clear RDr. rewrite rNums_0. rewrite ?(sx32_of_Z 619) by lia.
      arun_to 0xa7444%Z.
      change (Z.b2z (617 <? 1)) with 0%Z. rewrite ?Z.lxor_0_r.
      arun_to 0xa7450%Z.
      clear SEPtt SEPimg. revive_all_smA AOK MUL WML.
      lazymatch type of KQ with kq _ (DRet _ _ ?d7 _) => blk_goal d7 end.
      { unfold blk_of. rewrite SMALL. cbn [Z.eqb blk_at]. dmodel_cbn. split; [exact SMALL|]. split; [exact TTA| exact TTL]. }
      clear TTA. fold_MU MU SMALL.
      kq_fold. enter_cutF (HRETP3 _ _ _ _ JK_) DP; [ ret_nb | ].
      intros _. pose proof (dout_ok_aft_r L d sym tt0 DI ltac:(lia) ltac:(lia)) as OK. unfold aft_r, aft_w, aft_tp in OK. rewrite !SH8 in OK. subst tp. exact OK.
  Qed.
End R.

(* [comment removed for export] *)
Lemma A0F_dec_U12F : forall A, act_ok AIHI0 A -> act_sh DI_A0 A -> forall Q, A0F_RETP3 A Q -> forall F, A0F_cut_HFAST A Q F.
Proof.
  intros A AOK ASH Q HP3 F. apply (A0F_U12_HFAST A AOK ASH Q F). intros sym tt0. apply (A0F_U12_AFT A AOK ASH Q HP3 F).
Qed.
End ACeilS1.
