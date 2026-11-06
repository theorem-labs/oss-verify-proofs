(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts BzContracts0 DecCut DecTac DecTac2 DecTacS DecAux
     BzLemmasT BzLemmasT2 BzLemmasMtf BzWalkArith BzWalkArith3 DecAuxR S0_dec_U13 S0_decCuts S0_decCutsM.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM DecCutF DecTacF DecTacFR S0F_decRet S0F_decCuts S0F_decCutsM BzDU9 DecTacF3.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decCuts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decCutsM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF3.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit DecFast DecFastT DecFastS.
Local Ltac DecCut.revive H MUL WML AOK ::= DecFast.revive_cached H MUL WML AOK.
Local Ltac DecCut.dpure_from DP ::= DecFast.dpure_from_fast DP.
Local Ltac DecCut.open_dmem DM ::= DecFast.open_dmem_red DM.
Local Ltac DecTac.gb_next keep Wloc IB ::= DecFastT.gb_next_red keep Wloc IB.
Local Ltac DecTacS.revive_sm H AOK SM0 MUL WML ::= DecFastS.revive_sm_cached H AOK SM0 MUL WML.
Local Ltac DecTacS.revive_all_smL AOK SM0 MUL WML LIN DP ::= DecFastS.revive_all_smL_split AOK SM0 MUL WML LIN DP.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzImg0TacFR BzImg0Tac.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require SasFastF RelLia.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac simpl_arr_sizes ::= SasFastF.sas6F_all.
Local Ltac StoreFast.tlia ::= RelLia.tlia_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
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
  Notation L16 := (b_ll16 (a_cx A)).

  Ltac prep DM MU DP :=
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN; pose proof rnums_words_length as RNL; lin_natZ RNL;
    unfold W14, D14, DSTATE_SIZE in MU; cbn [app blk_ivls b_s b_strm] in MU; open_dmemF DM; s2img.

  (* [comment removed for export] *)
  Ltac prepS DM MU DP SM :=
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN; pose proof rnums_words_length as RNL; lin_natZ RNL;
    unfold W14, D14, DSTATE_SIZE, blk_ivls in MU; rewrite SM in MU; cbn [Z.eqb app b_s b_strm] in MU; open_dmemF DM; s2img.
  Ltac fold_MU MU SM :=
    lazymatch type of MU with munch ?W ?ma ?mb =>
      let H := fresh "MUf" in
      assert (H : munch (W14 DI_S0 cx usp) ma mb)
        by (unfold W14, D14, DSTATE_SIZE, blk_ivls; rewrite SM; cbn [Z.eqb app b_s b_strm di_segs DI_S0]; exact MU);
      clear MU; rename H into MU end.

  (* [comment removed for export] *)
  Ltac revive_smF SM MUL WML LIN DP :=
    clear LIN;
    let L1 := fresh "LINs" in let L2 := fresh "LINm" in
    pose proof (act_lin_core _ _ AOK) as L1;
    first [ pose proof (act_lin_ll _ _ AOK SM) as L2 | pose proof (act_lin_tt _ _ AOK SM) as L2 ];
    revive_all_sm AOK SM MUL WML;
    clear L1 L2; pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section RA.
  Hypothesis HMTFB : S0F_cut_HMTFB A F.

  Lemma S0F_U9_HRUN : S0F_cut_HRUN A F.
  Proof.
    unfold S0F_cut_HRUN. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    prep DM MU DP. cps_destruct DI as (ML & NSR & RO). pose proof RO as RO'. unfold run_okF in RO'.
    pose proof (alpha_ok_state L d (proj1 ML)) as NST.
    assert (NBL : (0 <= sv_nblock L <= 900000)%Z) by (pose proof (proj1 ML) as AL; unfold alpha_ok in AL; tauto).
    hide_all_but_at [usp + -320]%Z.
    pose proof (munch_refl [(usp + -320, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    kq_intro. unfold K_HRUN in KQ.
    wstepl. wstepl. wstepl. (* [comment removed for export] *)
    wstepl; if_cases KN; zify_cond_z KN.
    { (* [comment removed for export] *)
      wstepl. wstepl. wstepl. wstepl.
      rewrite (run_body_ret L d s) in KQ by lia. rewrite dgo_DRet in KQ.
      revive_all MUL WML AOK. kq_fold.
      enter_cutF (S0F_dec_retc A AOK _ _ _ _ JK_) DP; [ ret_nb | apply dpost14_ne; dmodel_cbn; exact NST ]. }
    rewrite (run_body_go L d s) in KQ by lia. change (dgo F (mtf_val_start BZ_X_MTF_3 ?L1 d s)) with (K_HMTFB F L1 d s) in KQ.
    wstepl. (* [comment removed for export] *)
    wstepl. (* [comment removed for export] *)
    rewrite (Z.mul_comm (sv_N L) 2) in *.
    assert (NS01 : sv_nextSym L = 0%Z \/ sv_nextSym L = 1%Z) by lia.
    rewrite (run_delta_shift (sv_nextSym L) (sv_N L)) in KQ by lia.
    destruct (Z.eq_dec (sv_es L) (-1)) as [Ees|NE].
    - rewrite Ees in *.
      wstepl; if_cases K0; zify_cond_z K0.
      + (* [comment removed for export] *)
        wstepl. (* [comment removed for export] *) rewrite swrap32_addm1 by lia.
        replace (sv_nextSym L) with 0%Z in KQ by lia. rewrite Z.pow_0_r, Z.mul_1_r in KQ.
        revive_all MUL WML AOK. enter_sameF HMTFB DP.
        split; [apply dinv_ML_esN; exact ML|]. dmodel_cbn. split; [apply run_okF_step; [exact RO| lia| lia] | lia].
      + (* [comment removed for export] *)
        wstepl. wstepl. rewrite swrap32_addm1 by lia.
        replace (sv_nextSym L) with 1%Z in KQ by lia. rewrite Z.pow_1_r in KQ.
        revive_all MUL WML AOK. enter_sameF HMTFB DP.
        split; [apply dinv_ML_esN; exact ML|]. dmodel_cbn. split; [apply run_okF_step; [exact RO| lia| lia] | lia].
    - assert (ES0 : (0 <= sv_es L)%Z) by lia.
      wstepl; if_cases K0; zify_cond_z K0.
      + wstepl.
        replace (sv_nextSym L) with 0%Z in KQ by lia. rewrite Z.pow_0_r, Z.mul_1_r in KQ.
        revive_all MUL WML AOK. enter_sameF HMTFB DP.
        split; [apply dinv_ML_esN; exact ML|]. dmodel_cbn. split; [apply run_okF_step; [exact RO| lia| lia] | lia].
      + wstepl. wstepl.
        replace (sv_nextSym L) with 1%Z in KQ by lia. rewrite Z.pow_1_r in KQ.
        revive_all MUL WML AOK. enter_sameF HMTFB DP.
        split; [apply dinv_ML_esN; exact ML|]. dmodel_cbn. split; [apply run_okF_step; [exact RO| lia| lia] | lia].
  Time Qed.
  End RA.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section RB.
  Hypothesis HSYM : S0F_cut_SYM A F.
  (* [comment removed for export] *)
  Variables (L : dsv) (s : dstrm) (J : jk) (uc E : Z).
  Notation nb0 := (sv_nblock L).
  Notation nbMAX := (sv_nblockMAX L).

  (* [comment removed for export] *)
  Definition L9cF (pc sc sm : Z) (j : Z) : Prop :=
    forall (x1 x5 x7 x9 x17 x23 x24 x26 x27 x29 x30 x31 : word)
           (d : dst) (m : word -> option byte)
           (j0 : list byte) (f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96 f184 f200 : word) (pb : list byte),
      dmem DI_S0 cx (a_g1 A) (a_sv A) (a_payload A) m (dvF cx J d s) ->
      S0FR A m j0 f8 f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f96
           (Z_to_bv 64 (S + 2124)) (Z_to_bv 64 (S + 7884)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (S + 7820))
           (Z_to_bv 64 (sv_gSel L)) (Z_to_bv 64 (sv_nblockMAX L)) (Z_to_bv 64 (sv_EOB L)) (Z_to_bv 64 (sv_groupNo L))
           (Z_to_bv 64 (S + 57820 + 1032 * sv_gSel L)) (Z_to_bv 64 (S + 51628 + 1032 * sv_gSel L)) f184 (Z_to_bv 64 (sv_gMinlen L)) f200 pb ->
      stk s0segs m (a_lo A) (usp + -320) ->
      munch (W14 DI_S0 cx usp) (a_m0 A) m -> wmono s0segs (a_m0 A) m -> mem_inv s0segs m ->
      dpureF cx (a_b0 A) (a_payload A) J d s ->
      fuel_ok F d s ->
      dinv_L9 L d uc E j -> b_small cx = sm ->
      evt s0segs (QF A (K_L9 F L d s uc (nb0 + j) (E - j)))
        (MS (mkR x1 (Z_to_bv 64 (usp + -320)) (a_gp A) (a_tp A) x5 (Z_to_bv 64 (S + 45436 + 1032 * sv_gSel L)) x7 (Z_to_bv 64 (S + 64036)) x9
                (Z_to_bv 64 (-4)) (Z_to_bv 64 (E - j)) (Z_to_bv 64 uc) (Z_to_bv 64 nbMAX) (Z_to_bv 64 (nbMAX - (nb0 + j))) (Z_to_bv 64 (sc * (nb0 + j))) (Z_to_bv 64 1) x17
                (Z_to_bv 64 (sv_groupPos L)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (sv_nextSym L)) (Z_to_bv 64 (S + 2047)) x23 x24 (Z_to_bv 64 (sv_nSelectors L)) x26 x27
                (Z_to_bv 64 (nb0 + j)) x29 x30 x31)
            (a_F A) (Z_to_bv 64 pc) (a_fc A) None m (seg_rom s0segs)).
  Definition L9ScF := L9cF 0x1edd0 2 1.
  Definition L9FcF := L9cF 0x1ee1c 4 0.

  (* [comment removed for export] *)
  Lemma S0F_U9_L9F : forall j, ((j + 2 <= E)%Z -> L9FcF (j + 1)) -> L9FcF j.
  Proof.
    intros j NXT. unfold L9FcF, L9cF. intros until pb. intros DM FR ST MU WM MI DP FU DI SM.
    prepS DM MU DP SM. cps_pose DI as (MR & RI & UCR & J0 & EJ & ROOM & NSR).
    pose proof (alpha_ok_state L d (proj1 MR)) as NST.
    assert (NBL : (0 <= sv_nblock L <= 900000)%Z) by (pose proof (proj1 MR) as AL; unfold alpha_ok in AL; tauto).
    assert (NBM : sv_nblockMAX L = (100000 * d_bs100k d)%Z) by (pose proof (proj1 (proj2 MR)) as GR; unfold grp_okF in GR; tauto).
    pose proof (dpureF_n _ _ _ _ _ _ DP) as BN. rewrite BN in NBM.
    pose proof (act_tt_s _ _ AOK SM) as [[TT0 TT1] SEPtt].
    unfold blk_of in BLK. rewrite SM in BLK. cbn [Z.eqb blk_at] in BLK. cps_destruct BLK as (_ & TTA & TTL).
    pose proof (dpureF_small _ _ _ _ _ _ DP) as SMALL. rewrite SM in SMALL.
    hide_all_but_at [S + 3152; TT]%Z.
    pose proof (munch_refl [(TT, TT + 400000 * b_n cx)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    kq_intro.
    wstepl. (* [comment removed for export] *)
    wstepl; if_cases Kr; zify_cond_z Kr.
    { (* [comment removed for export] *)
      wstepl. wstepl. (* [comment removed for export] *)
      rewrite (K_L9_fail F L d s uc) in KQ by lia.
      clear SEPtt MUL WML. unfold hidden in *.
      assert (BLK : blk_at s0segs m cx (blk_of cx d)).
      { unfold blk_of. rewrite SM. cbn [Z.eqb blk_at]. split; [exact SM|]. split; [exact TTA| exact TTL]. }
      clear TTA. fold_MU MU SM. kq_fold.
      replace (Z_to_bv 64 (sv_nblockMAX L)) with (Z_to_bv 64 (sv_nblock (sv_set_es (sv_set_nblock L (sv_nblock L + j)) (E - j)))) at 2 by (dmodel_cbn; f_equal; lia).
      enter_cutF (S0F_dec_ret A AOK _ _ _ _ JK_) DP; [ ret_nb | apply dpost14_ne; dmodel_cbn; exact NST ]. }
    wstepl. (* [comment removed for export] *)
    wstepl. (* [comment removed for export] *)
    zw32_sw TTA (sv_nblock L + j)%Z uc ltac:(rewrite unsigned_lit by lia; reflexivity).
    rewrite (K_L9_step F L d s uc) in KQ by lia. rewrite (dstore_fast d) in KQ by exact SMALL.
    wstepl. wstepl. wstepl. wstepl. (* [comment removed for export] *)
    wstepl; if_cases Kl; zify_cond_z Kl.
    - (* [comment removed for export] *)
      clear SEPtt. revive_smF SM MUL WML LIN DP.
      assert (BLK : blk_at s0segs m0 cx (blk_of cx (d_set_tt d (zset (d_tt d) (sv_nblock L + j) uc)))).
      { unfold blk_of. rewrite SM. cbn [Z.eqb blk_at]. dmodel_cbn. split; [exact SM|]. split; [exact TTA| rewrite zw32_length; lia]. }
      clear TTA. fold_MU MU SM.
      pose proof (NXT ltac:(lia)) as NX. unfold L9FcF, L9cF in NX.
      replace (sv_nblock L + j + 1)%Z with (sv_nblock L + (j + 1))%Z in KQ by lia. replace (E - j - 1)%Z with (E - (j + 1))%Z in KQ by lia.
      kq_fold. enter_cutF NX DP; [ apply (dpureF_set_tt _ _ _ _ _ _ _ _ DP); lia | apply (dinv_L9_step_fast L d uc E j DI SMALL); lia | exact SM ].
    - (* [comment removed for export] *)
      wstepl. wstepl.
      clear SEPtt. revive_smF SM MUL WML LIN DP.
      assert (BLK : blk_at s0segs m0 cx (blk_of cx (d_set_tt d (zset (d_tt d) (sv_nblock L + j) uc)))).
      { unfold blk_of. rewrite SM. cbn [Z.eqb blk_at]. dmodel_cbn. split; [exact SM|]. split; [exact TTA| rewrite zw32_length; lia]. }
      clear TTA. fold_MU MU SM.
      rewrite (K_L9_exit F L) in KQ by lia.
      change (dgo F (sym_dispatch ?L2 ?d2 s)) with (K_SYM F L2 d2 s) in KQ.
      pose proof (dpureF_set_tt _ _ _ _ _ _ (sv_nblock L + j) uc DP ltac:(lia)) as DP'.
      kq_fold. enter_cutF (HSYM _ _ _ JK_) DP'.
      replace (sv_nblock L + j + 1)%Z with (sv_nblock L + E)%Z by lia. replace (E - j - 1)%Z with 0%Z by lia.
      apply (dinv_L9_exit_fast L d uc E j DI SMALL); lia.
  Time Qed.

  (* [comment removed for export] *)
  Lemma S0F_U9_L9S : forall j, ((j + 2 <= E)%Z -> L9ScF (j + 1)) -> L9ScF j.
  Proof.
    intros j NXT. unfold L9ScF, L9cF. intros until pb. intros DM FR ST MU WM MI DP FU DI SM.
    prepS DM MU DP SM. cps_pose DI as (MR & RI & UCR & J0 & EJ & ROOM & NSR).
    pose proof (alpha_ok_state L d (proj1 MR)) as NST.
    assert (NBL : (0 <= sv_nblock L <= 900000)%Z) by (pose proof (proj1 MR) as AL; unfold alpha_ok in AL; tauto).
    assert (NBM : sv_nblockMAX L = (100000 * d_bs100k d)%Z) by (pose proof (proj1 (proj2 MR)) as GR; unfold grp_okF in GR; tauto).
    pose proof (dpureF_n _ _ _ _ _ _ DP) as BN. rewrite BN in NBM.
    pose proof (act_ll_s _ _ AOK SM) as [(L160 & L161 & L40 & L41) [SEP16 SEP4]].
    unfold blk_of in BLK. rewrite SM in BLK. cbn [Z.eqb blk_at] in BLK. cps_destruct BLK as (_ & L16A & L16L & L4A & L4L).
    pose proof (dpureF_small _ _ _ _ _ _ DP) as SMALL. rewrite SM in SMALL.
    hide_all_but_at [S + 3152; L16]%Z.
    pose proof (munch_refl [(L16, L16 + 200000 * b_n cx)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    kq_intro.
    wstepl. (* [comment removed for export] *)
    wstepl; if_cases Kr; zify_cond_z Kr.
    { (* [comment removed for export] *)
      wstepl. wstepl. (* [comment removed for export] *)
      rewrite (K_L9_fail F L d s uc) in KQ by lia.
      clear SEP16 SEP4 MUL WML. unfold hidden in *.
      assert (BLK : blk_at s0segs m cx (blk_of cx d)).
      { unfold blk_of. rewrite SM. cbn [Z.eqb blk_at]. split; [exact SM|]. split; [exact L16A| split; [exact L16L| split; [exact L4A| exact L4L]]]. }
      clear L16A L4A. fold_MU MU SM. kq_fold.
      replace (Z_to_bv 64 (sv_nblockMAX L)) with (Z_to_bv 64 (sv_nblock (sv_set_es (sv_set_nblock L (sv_nblock L + j)) (E - j)))) at 2 by (dmodel_cbn; f_equal; lia).
      enter_cutF (S0F_dec_ret A AOK _ _ _ _ JK_) DP; [ ret_nb | apply dpost14_ne; dmodel_cbn; exact NST ]. }
    wstepl. (* [comment removed for export] *)
    wstepl. (* [comment removed for export] *)
    zh16_sh L16A (sv_nblock L + j)%Z.
    rewrite (unsigned_lit uc) in L16A by lia. rewrite (Z.mod_small uc 65536) in L16A by lia.
    rewrite (K_L9_step F L d s uc) in KQ by lia. rewrite (dstore_smallm d) in KQ by lia.
    wstepl. wstepl. wstepl. wstepl. (* [comment removed for export] *)
    wstepl; if_cases Kl; zify_cond_z Kl.
    - (* [comment removed for export] *)
      wstepl. wstepl.
      clear SEP16 SEP4. revive_smF SM MUL WML LIN DP.
      assert (BLK : blk_at s0segs m0 cx (blk_of cx (d_set_ll16 d (zset (d_ll16 d) (sv_nblock L + j) uc)))).
      { unfold blk_of. rewrite SM. cbn [Z.eqb blk_at]. dmodel_cbn. split; [exact SM|]. split; [exact L16A| split; [rewrite zh16_length; lia| split; [exact L4A| exact L4L]]]. }
      clear L16A L4A. fold_MU MU SM.
      rewrite (K_L9_exit F L) in KQ by lia.
      change (dgo F (sym_dispatch ?L2 ?d2 s)) with (K_SYM F L2 d2 s) in KQ.
      pose proof (dpureF_set_ll16 _ _ _ _ _ _ (sv_nblock L + j) uc DP ltac:(lia)) as DP'.
      kq_fold. enter_cutF (HSYM _ _ _ JK_) DP'.
      replace (sv_nblock L + j + 1)%Z with (sv_nblock L + E)%Z by lia. replace (E - j - 1)%Z with 0%Z by lia.
      apply (dinv_L9_exit_small L d uc E j DI); lia.
    - (* [comment removed for export] *)
      wstepl.
      clear SEP16 SEP4. revive_smF SM MUL WML LIN DP.
      assert (BLK : blk_at s0segs m0 cx (blk_of cx (d_set_ll16 d (zset (d_ll16 d) (sv_nblock L + j) uc)))).
      { unfold blk_of. rewrite SM. cbn [Z.eqb blk_at]. dmodel_cbn. split; [exact SM|]. split; [exact L16A| split; [rewrite zh16_length; lia| split; [exact L4A| exact L4L]]]. }
      clear L16A L4A. fold_MU MU SM.
      pose proof (NXT ltac:(lia)) as NX. unfold L9ScF, L9cF in NX.
      replace (sv_nblock L + j + 1)%Z with (sv_nblock L + (j + 1))%Z in KQ by lia. replace (E - j - 1)%Z with (E - (j + 1))%Z in KQ by lia.
      pose proof (dpureF_set_ll16 _ _ _ _ _ _ (sv_nblock L + j) uc DP ltac:(lia)) as DP'.
      kq_fold. enter_cutF NX DP'; [ apply (dinv_L9_step_small L d uc E j DI); lia | exact SM ].
  Time Qed.

  (* [comment removed for export] *)
  Lemma S0F_U9_L9S_all : forall j, (0 <= j < E)%Z -> L9ScF j.
  Proof.
    intros j Hj.
    assert (G : forall k : nat, (Z.of_nat k < E)%Z -> L9ScF (E - 1 - Z.of_nat k)%Z).
    { induction k as [|k IH]; intros Hk.
      - apply S0F_U9_L9S. intros; exfalso; lia.
      - apply S0F_U9_L9S. intros _. replace (E - 1 - Z.of_nat (Datatypes.S k) + 1)%Z with (E - 1 - Z.of_nat k)%Z by lia. apply IH. lia. }
    pose proof (G (Z.to_nat (E - 1 - j)) ltac:(lia)) as G0.
    replace (E - 1 - Z.of_nat (Z.to_nat (E - 1 - j)))%Z with j in G0 by lia. exact G0.
  Qed.
  Lemma S0F_U9_L9F_all : forall j, (0 <= j < E)%Z -> L9FcF j.
  Proof.
    intros j Hj.
    assert (G : forall k : nat, (Z.of_nat k < E)%Z -> L9FcF (E - 1 - Z.of_nat k)%Z).
    { induction k as [|k IH]; intros Hk.
      - apply S0F_U9_L9F. intros; exfalso; lia.
      - apply S0F_U9_L9F. intros _. replace (E - 1 - Z.of_nat (Datatypes.S k) + 1)%Z with (E - 1 - Z.of_nat k)%Z by lia. apply IH. lia. }
    pose proof (G (Z.to_nat (E - 1 - j)) ltac:(lia)) as G0.
    replace (E - 1 - Z.of_nat (Z.to_nat (E - 1 - j)))%Z with j in G0 by lia. exact G0.
  Qed.
  End RB.
End R.

(* [comment removed for export] *)
Lemma S0F_dec_U9a : forall A, act_ok 320 A -> forall F, S0F_cut_HMTFB A F -> S0F_cut_HRUN A F.
Proof. intros A AOK F HB. exact (S0F_U9_HRUN A AOK F HB). Qed.

End ACeilS1.
