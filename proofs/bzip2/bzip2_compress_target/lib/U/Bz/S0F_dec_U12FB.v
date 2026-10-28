(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts BzContracts0 DecCut DecTac DecTac2 DecTacS DecAux. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import
     BzLemmasT BzLemmasT2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzWalkArith BzWalkArith3 S0_dec_U13 S0_decCuts S0_decCutsE.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU9 BzDU11. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF DecTacFR DecTacF3 S0F_decRet S0F_decCuts S0F_decCutsM S0F_decCutsE.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU11 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacFR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCuts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCutsM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCutsE.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDU12F. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import DecAux12F S0F_dec_U12FA.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import DecFast DecFastT DecFastS.
Local Ltac DecCut.revive H MUL WML AOK ::= DecFast.revive_cached H MUL WML AOK.
Local Ltac DecCut.dpure_from DP ::= DecFast.dpure_from_fast DP.
Local Ltac DecCut.open_dmem DM ::= DecFast.open_dmem_red DM.
Local Ltac DecTac.gb_next keep Wloc IB ::= DecFastT.gb_next_red keep Wloc IB.
Local Ltac DecTacS.revive_sm H AOK SM0 MUL WML ::= DecFastS.revive_sm_cached H AOK SM0 MUL WML.
Local Ltac DecTacS.revive_all_smL AOK SM0 MUL WML LIN DP ::= DecFastS.revive_all_smL_split AOK SM0 MUL WML LIN DP.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzImg0TacFR BzImg0Tac.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require SasFastF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLia.
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
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac simpl_arr_sizes ::= SasFastF.sas6F_all.
Local Ltac StoreFast.tlia ::= RelLia.tlia_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.

Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.
  Variable F : nat.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).
  Notation TT := (b_tt (a_cx A)).

  Ltac prepS DM MU DP SM :=
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN; pose proof rnums_words_length as RNL; lin_natZ RNL;
    unfold W14, D14, DSTATE_SIZE, blk_ivls in MU; rewrite SM in MU; cbn [Z.eqb app b_s b_strm] in MU; open_dmemF DM; s2img.
  Ltac fold_MU MU SM :=
    lazymatch type of MU with munch ?W ?ma ?mb =>
      let H := fresh "MUf" in
      assert (H : munch (W14 DI_S0 cx usp) ma mb)
        by (unfold W14, D14, DSTATE_SIZE, blk_ivls; rewrite SM; cbn [Z.eqb app b_s b_strm di_segs DI_S0]; exact MU);
      clear MU; rename H into MU end.
  Ltac blk_goal D :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let B := fresh "BLK" in assert (B : blk_at s0segs mm cx (blk_of cx D)) end.

  (* [comment removed for export] *)
  Ltac exit_tail MUL WML := do 6 wstepl; revive_all MUL WML AOK.
  Ltac bdec :=
    rewrite ?land3_mod;
    repeat match goal with
      | |- context [(?a <? ?b)%Z] => first [ rewrite (proj2 (Z.ltb_ge a b)) by lia | rewrite (proj2 (Z.ltb_lt a b)) by lia ]
      | |- context [(?a <=? ?b)%Z] => first [ rewrite (proj2 (Z.leb_gt a b)) by lia | rewrite (proj2 (Z.leb_le a b)) by lia ]
      | |- context [(?a =? ?b)%Z] => first [ rewrite (proj2 (Z.eqb_neq a b)) by lia | rewrite (proj2 (Z.eqb_eq a b)) by lia ]
      end;
    cbn [Z.b2z];
    repeat match goal with
      | |- context [Z.lxor ?a ?b] => is_Zlit a; is_Zlit b; let c := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with c
      | |- context [Z.land ?a ?b] => is_Zlit a; is_Zlit b; let c := eval vm_compute in (Z.land a b) in change (Z.land a b) with c
      end.
  Ltac ck := bdec; notrap.

  Lemma S0F_U12_AFT : forall L s J sym tt0, AFTcF A F L s J sym tt0.
  Proof.
    intros L s J sym tt0. unfold AFTcF. intros until pb. intros DM FR ST MU WM MI DP FU DI.
    cps_pose (dinv_AFT_facts L d sym tt0 DI) as (TPR & ALL28 & ALL32).
    cps_pose DI as (_ & ORIG & NB1 & NB9 & HDR & TS & SM0 & _).
    cps_pose HDR as (RND & SBC & OPR). cps_pose TS as (STT & SOL & SOCH & SCB).
    pose proof (dpureF_small _ _ _ _ _ _ DP) as SMALL. rewrite SM0 in SMALL. symmetry in SMALL.
    pose proof (dpureF_n _ _ _ _ _ _ DP) as BN.
    prepS DM MU DP SMALL.
    unfold blk_of in BLK. rewrite SMALL in BLK. cbn [Z.eqb blk_at] in BLK. cps_destruct BLK as (_ & TTA & TTL).
    pose proof (act_tt_s _ _ AOK SMALL) as [[TT0 TT1] SEPtt]. pose proof (act_ok_al _ _ AOK) as ALG. unfold ctx_al in ALG.
    assert (SH8 : forall x, Z.shiftr x 8 = (x / 256)%Z) by (intros; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    unfold aft_tp in TPR. rewrite SH8 in TPR. pose proof (ALL28 (d_origPtr d) ltac:(lia)) as VOR.
    hide_all_but_at [S; S + 1092; S + 3152; TT; usp + -336]%Z.
    pose proof (munch_refl [(S, S + 68); (S + 1092, S + 1096); (usp + -336, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    kq_intro.
    wstepl. wstepl. wstepl. wstepl. wstepl. wstepl. wstepl. wstepl; ck. wstepl. wstepl. wstepl. wstepl. wstepl; ck. wstepl; ck. wstepl. wstepl; ck. (* [comment removed for export] *)
    pose proof (zw32_read s0segs m TT (d_tt d) _ (d_origPtr d) _ TTA ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD.
    wstepl. clear RD. (* [comment removed for export] *)
    hide TTA.
    pose proof (ALL28 (zget (d_tt d) (d_origPtr d) / 256)%Z ltac:(lia)) as VTR. pose proof (ALL32 (zget (d_tt d) (d_origPtr d) / 256)%Z) as VTR32.
    wstepl. wstepl. rewrite zxb_lit8 by lia. (* [comment removed for export] *)
    wstepl. wstepl. (* [comment removed for export] *)
    wstepl. wstepl. (* [comment removed for export] *)
    wstepl; if_cases Kbr; zify_cond_z Kbr.
    - (* [comment removed for export] *)
      rewrite (be_aft_nr L d s) in KQ by (unfold aft_tp; rewrite ?SH8; lia). rewrite dgo_DRet in KQ. unfold aft_nr, aft_w, aft_tp in KQ. rewrite !SH8 in KQ.
      remember (zget (d_tt d) (d_origPtr d) / 256)%Z as tp eqn:Etp.
      wstepl. wstepl. (* [comment removed for export] *)
      wstepl; if_cases Ktp; zify_cond_z Ktp; [exfalso; lia|].
      wstepl. wstepl. wstepl. wstepl; ck. wstepl. wstepl. wstepl; ck. (* [comment removed for export] *)
      pose proof TTA as TTAL. revive TTAL MUL WML AOK.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (zw32_read s0segs mm TT (d_tt d) _ tp _ TTAL ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
      wstepl. clear RD TTAL. (* [comment removed for export] *)
      wstepl. wstepl. (* [comment removed for export] *)
      wstepl. wstepl. wstepl. wstepl. (* [comment removed for export] *)
      exit_tail MUL WML.
      lazymatch type of KQ with kq _ (DRet _ _ ?d7 _) => blk_goal d7 end.
      { unfold blk_of. rewrite SMALL. cbn [Z.eqb blk_at]. dmodel_cbn. split; [exact SMALL|]. split; [exact TTA| exact TTL]. }
      clear TTA. fold_MU MU SMALL.
      kq_fold. enter_cutF (S0F_dec_retc A AOK _ _ _ _ JK_) DP; [ unfold BZ_OK; lia | ret_nb | ].
      intros _. pose proof (dout_ok_aft_nr L d sym tt0 DI Kbr ltac:(lia)) as OK. unfold aft_nr, aft_w, aft_tp in OK. rewrite !SH8 in OK. subst tp. exact OK.
    - (* [comment removed for export] *)
      rewrite (be_aft_r L d s) in KQ by (unfold aft_tp; rewrite ?SH8; lia). rewrite dgo_DRet in KQ. unfold aft_r, aft_w, aft_tp in KQ. rewrite !SH8 in KQ.
      remember (zget (d_tt d) (d_origPtr d) / 256)%Z as tp eqn:Etp.
      wstepl. wstepl. (* [comment removed for export] *)
      (* [comment removed for export] *)
      apply (rw_cells_merge_mid s0segs _ _ _ 7 2) in HD. cbn [firstn skipn cells_size csize cells_bytes cbytes Nat.add app] in HD.
      step. change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)). mem_after_store.
      lazymatch goal with HD' : rw_cells _ _ S (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: C8 (Z_to_bv 64 0) :: ?post) |- _ =>
        apply (rw_cells_split_c8_zero s0segs _ _ [c0; c1; c2; c3; c4; c5; c6] post) in HD'; cbn [app] in HD' end.
      wstepl; if_cases Ktp; zify_cond_z Ktp; [exfalso; lia|].
      wstepl. wstepl. wstepl. wstepl; ck. wstepl. wstepl. wstepl; ck. (* [comment removed for export] *)
      wstepl. pose proof GOT as GOTL. revive GOTL MUL WML AOK. wstepl. clear GOTL. (* [comment removed for export] *)
      pose proof TTA as TTAL. revive TTAL MUL WML AOK.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (zw32_read s0segs mm TT (d_tt d) _ tp _ TTAL ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
      wstepl. clear RD TTAL. (* [comment removed for export] *) wstepl.
      pose proof RN as RNL'. revive RNL' MUL WML AOK.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u32arr_read s0segs mm _ rnums_words 0 (Z_to_bv 64 (rNums 0)) _ RNL' (rnums_words_nth12 0 ltac:(lia)) ltac:(lia) eq_refl) as RDr end.
      wstepl. clear RDr RNL'. (* [comment removed for export] *) rewrite rNums_0. rewrite ?(sx32_of_Z 619) by lia.
      wstepl. wstepl. (* [comment removed for export] *)
      wstepl. wstepl. (* [comment removed for export] *)
      wstepl. wstepl. wstepl. wstepl. wstepl; ck. wstepl. wstepl. wstepl. wstepl. (* [comment removed for export] *) rewrite ?Z.lxor_0_r.
      wstepl. wstepl. wstepl. (* [comment removed for export] *)
      exit_tail MUL WML.
      lazymatch type of KQ with kq _ (DRet _ _ ?d7 _) => blk_goal d7 end.
      { unfold blk_of. rewrite SMALL. cbn [Z.eqb blk_at]. dmodel_cbn. split; [exact SMALL|]. split; [exact TTA| exact TTL]. }
      clear TTA. fold_MU MU SMALL.
      kq_fold. enter_cutF (S0F_dec_retc A AOK _ _ _ _ JK_) DP; [ ret_nb | ].
      intros _. pose proof (dout_ok_aft_r L d sym tt0 DI ltac:(lia) ltac:(lia)) as OK. unfold aft_r, aft_w, aft_tp in OK. rewrite !SH8 in OK. subst tp. exact OK.
  Time Qed.

  (* [comment removed for export] *)
  Lemma S0F_U12_F : S0F_cut_HFAST A F.
  Proof. apply (S0F_U12_HFAST A AOK F). intros. apply S0F_U12_AFT. Qed.
End R.

Lemma S0F_dec_U12F : forall A, act_ok 320 A -> forall F, S0F_cut_HFAST A F.
Proof. intros A AOK F. exact (S0F_U12_F A AOK F). Qed.

End ACeilS1.
