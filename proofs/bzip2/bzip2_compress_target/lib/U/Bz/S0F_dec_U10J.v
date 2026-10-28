(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzContracts BzContracts0 DecCut DecTac DecTac2 DecTacS DecAux.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecAuxM DecAuxL. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzLemmasT BzLemmasMtf. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzWalkArith BzWalkArith2 BzWalkArith3 DecAuxR S0_dec_U13 S0_decCuts S0_decCutsM.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAux OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac.DecAuxB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAuxM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAuxL OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasMtf OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAuxR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_dec_U13 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_decCuts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_decCutsM. (* [comment removed for export] *) From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require PropExec. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require SegsS0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzContracts BzContracts0 DecCut DecAux.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecAuxM DecAuxL S0_dec_U13 S0_decCutsM. From Stdlib Require Lia. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU9. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF DecTacFR DecTacF3 S0F_decRet S0F_decCuts S0F_decCutsM.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacFR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCuts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCutsM.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDU10. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import S0F_decCutsL.
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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require SasFastF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require SepFast.
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
Local Ltac StoreFast.tlia ::= SepFast.tlia_dr.
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
  Notation L16 := (b_ll16 (a_cx A)).

  Ltac prep DM MU DP :=
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN; pose proof rnums_words_length as RNL; lin_natZ RNL;
    unfold W14, D14, DSTATE_SIZE in MU; cbn [app blk_ivls b_s b_strm] in MU; open_dmemF DM; s2img.
  Ltac prepS DM MU DP SM :=
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN; pose proof rnums_words_length as RNL; lin_natZ RNL;
    unfold W14, D14, DSTATE_SIZE, blk_ivls in MU; rewrite SM in MU; cbn [Z.eqb app b_s b_strm] in MU; open_dmemF DM; s2img.
  Ltac fold_MU MU SM :=
    lazymatch type of MU with munch ?W ?ma ?mb =>
      let H := fresh "MUf" in
      assert (H : munch (W14 DI_S0 cx usp) ma mb)
        by (unfold W14, D14, DSTATE_SIZE, blk_ivls; rewrite SM; cbn [Z.eqb app b_s b_strm di_segs DI_S0]; exact MU);
      clear MU; rename H into MU end.
  Ltac revive_smF SM MUL WML LIN DP :=
    clear LIN;
    let L1 := fresh "LINs" in let L2 := fresh "LINm" in
    pose proof (act_lin_core _ _ AOK) as L1;
    first [ pose proof (act_lin_ll _ _ AOK SM) as L2 | pose proof (act_lin_tt _ _ AOK SM) as L2 ];
    revive_all_sm AOK SM MUL WML;
    clear L1 L2; pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN.
  Ltac blk_goal D :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let B := fresh "BLK" in assert (B : blk_at s0segs mm cx (blk_of cx D)) end.
  (* [comment removed for export] *)
  Ltac u10_facts MR DP :=
    let AL := fresh "AL" in let GR := fresh "GR" in let TB := fresh "TB" in let BL := fresh "BL" in let CU := fresh "CU" in
    let NST := fresh "NST" in let NBL := fresh "NBL" in let NBM := fresh "NBM" in let BN := fresh "BN" in
    let RP := fresh "RP" in let S0UR := fresh "S0UR" in
    lazymatch type of MR with ml_nomtfF ?L ?d =>
      cps_pose MR as (AL & GR & TB & BL & CU);
      pose proof (alpha_ok_state L d AL) as NST;
      assert (NBL : (0 <= sv_nblock L <= 900000)%Z) by (unfold alpha_ok in AL; tauto);
      assert (NBM : sv_nblockMAX L = (100000 * d_bs100k d)%Z) by (unfold grp_okF in GR; tauto);
      pose proof (dpureF_n _ _ _ _ _ _ DP) as BN; rewrite BN in NBM;
      pose proof (dpureF_rep _ _ _ _ _ _ DP) as RP; unfold drep in RP;
      pose proof (fun i => proj1 (proj2 (proj2 (proj2 RP))) i) as S0UR; cbn beta in S0UR; clear RP
    end.

  Section M.
  Hypothesis HC : S0F_cut_HMTFC A F.
  Variables (L : dsv) (s : dstrm) (J : jk).

  (* [comment removed for export] *)
  Ltac lj_headF S0UR HIST SMALL :=
    let RD := fresh "RD" in let u := fresh "u" in let UR := fresh "UR" in let HU := fresh "HU" in let OB := fresh "OB" in
    wstepl; wstepl; wstepl; wstepl; notrap; (* [comment removed for export] *)
    lazymatch goal with DRs2u : u8arr _ ?mm (_ + 3468)%Z (zb8 ?a _) |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      lazymatch R with context [Z_to_bv 64 ?ucv] =>
      lazymatch goal with UCR : (0 <= ?uc < 256)%Z |- _ =>
        pose proof (S0UR uc) as UR;
        pose proof (zb8_read1 s0segs mm _ a 256 uc _ DRs2u ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end end end;
    wstepl; clear RD; rewrite zxb_lit8 by lia; (* [comment removed for export] *)
    lazymatch goal with |- context [Z_to_bv 64 (zget ?a ?uc)] => set (u := zget a uc) in * end;
    wstepl; wstepl; wstepl; wstepl; notrap; wstepl; (* [comment removed for export] *)
    pose proof (HIST u ltac:(lia)) as HU;
    lazymatch goal with DRunz : u32arr _ ?mm (_ + 68)%Z (zw32 ?a _) |- _ =>
      lazymatch type of HIST with hist_ok _ ?sy ?n => pose proof (occ_bounds sy n u) as OB end; rewrite <- HU in OB;
      pose proof (zw32_read s0segs mm _ a 256 u _ DRunz ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end;
    wstepl; clear RD; (* [comment removed for export] *)
    wstepl; wstepl; notrap; (* [comment removed for export] *)
    wstepl; rewrite zxb_lit8 by lia; rewrite SMALL; (* [comment removed for export] *)
    lazymatch goal with DRunz : u32arr _ _ (_ + 68)%Z (zw32 ?unz _) |- _ =>
      zw32_sw DRunz u (zget unz u + 1)%Z ltac:(rewrite unsigned_lit by lia; reflexivity) end.

  Lemma S0F_U10_LJ : forall uc mb2, LJcF A F L s J uc mb2.
  Proof.
    intros uc mb2. unfold LJcF. intros until pb. intros DM FR ST MU WM MI DP FU MR MA NB UCR MI2 ROW.
    u10_facts MR DP. cps_pose MR as (_ & _ & _ & (NBR & SYMB & HIST) & _).
    pose proof (dpureF_small _ _ _ _ _ _ DP) as SMALL.
    destruct (act_small01 _ _ AOK) as [SM|SM]; rewrite SM in SMALL.
    - (* [comment removed for export] *)
      prepS DM MU DP SM. unfold r_of in DR. dr_open.
      unfold blk_of in BLK. rewrite SM in BLK. cbn [Z.eqb blk_at] in BLK. cps_destruct BLK as (_ & TTA & TTL).
      pose proof (act_tt_s _ _ AOK SM) as [[TT0 TT1] SEPtt].
      hide_all_but_at [S; S + 68; S + 3468; S + 3152; TT; usp + -336]%Z.
      pose proof (munch_refl [(S + 68, S + 1092); (TT, TT + 400000 * b_n cx)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
      kq_intro. rewrite (K_LJ_fast F L d s uc) in KQ by exact SMALL. unfold zincr in KQ.
      pose proof (act_ok_al _ _ AOK) as ALG. unfold ctx_al in ALG.
      lj_headF S0UR HIST SMALL.
      wstepl; oktrap. (* [comment removed for export] *)
      wstepl; notrap. wstepl. wstepl. wstepl. wstepl. wstepl; flags. wstepl; flags. wstepl; notrap.
      wstepl; flags. wstepl; flags. wstepl. wstepl. wstepl; notrap. wstepl; notrap. wstepl. wstepl; notrap. (* [comment removed for export] *)
      zw32_sw TTA (sv_nblock L) u ltac:(rewrite unsigned_lit by lia; reflexivity). (* [comment removed for export] *)
      wstepl. wstepl; notrap. (* [comment removed for export] *)
      pose proof (dpureF_set_unzftab _ _ _ _ _ _ (zset (d_unzftab d) u (zget (d_unzftab d) u + 1)) DP) as DP2.
      pose proof (dpureF_set_tt _ _ _ _ _ _ (sv_nblock L) u DP2 ltac:(lia)) as DP3.
      clear SEPtt. revive_smF SM MUL WML LIN DP.
      lazymatch type of KQ with kq _ (K_HMTFC _ _ ?d3 _) => blk_goal d3 end.
      { unfold blk_of. rewrite SM. cbn [Z.eqb blk_at]. dmodel_cbn. split; [exact SM|]. split; [exact TTA| rewrite zw32_length; lia]. }
      clear TTA. fold_MU MU SM.
      kq_fold. enter_cutF (HC _ _ _ JK_) DP3.
      all: match goal with |- ?g => idtac "LJF" g end.
      apply (dinv_ML_lit_fast L d mb2 uc MR ROW MI2 MA UCR NB ltac:(lia) S0UR SMALL).
    - (* [comment removed for export] *)
      prepS DM MU DP SM. unfold r_of in DR. dr_open.
      unfold blk_of in BLK. rewrite SM in BLK. cbn [Z.eqb blk_at] in BLK. cps_destruct BLK as (_ & L16A & L16L & L4A & L4L).
      pose proof (act_ll_s _ _ AOK SM) as [(L160 & L161 & L40 & L41) [SEP16 SEP4]].
      hide_all_but_at [S; S + 68; S + 3468; S + 3152; L16; usp + -336]%Z.
      pose proof (munch_refl [(S + 68, S + 1092); (L16, L16 + 200000 * b_n cx)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
      kq_intro. rewrite (K_LJ_small F L d s uc) in KQ by lia. unfold zincr in KQ.
      pose proof (act_ok_al _ _ AOK) as ALG. unfold ctx_al in ALG.
      lj_headF S0UR HIST SMALL.
      wstepl; oktrap. (* [comment removed for export] *)
      wstepl; notrap. wstepl. wstepl. wstepl. wstepl. wstepl; flags. wstepl; flags. wstepl; notrap.
      wstepl; flags. wstepl; flags. wstepl. wstepl. wstepl; notrap. wstepl; notrap. wstepl. wstepl; notrap. (* [comment removed for export] *)
      zh16_sh L16A (sv_nblock L). (* [comment removed for export] *)
      rewrite (unsigned_lit u) in L16A by lia. rewrite (Z.mod_small u 65536) in L16A by lia.
      wstepl. wstepl. wstepl; notrap. (* [comment removed for export] *)
      pose proof (dpureF_set_unzftab _ _ _ _ _ _ (zset (d_unzftab d) u (zget (d_unzftab d) u + 1)) DP) as DP2.
      pose proof (dpureF_set_ll16 _ _ _ _ _ _ (sv_nblock L) u DP2 ltac:(lia)) as DP3.
      clear SEP16 SEP4. revive_smF SM MUL WML LIN DP.
      lazymatch type of KQ with kq _ (K_HMTFC _ _ ?d3 _) => blk_goal d3 end.
      { unfold blk_of. rewrite SM. cbn [Z.eqb blk_at]. dmodel_cbn. split; [exact SM|]. split; [exact L16A| split; [rewrite zh16_length; lia| split; [exact L4A| exact L4L]]]. }
      clear L16A L4A. fold_MU MU SM.
      kq_fold. enter_cutF (HC _ _ _ JK_) DP3.
      all: match goal with |- ?g => idtac "LJS" g end.
      apply (dinv_ML_lit_small L d mb2 uc MR ROW MI2 MA UCR NB ltac:(lia) S0UR ltac:(lia)).
  Time Qed.
  End M.
End R.
End ACeilS1.
