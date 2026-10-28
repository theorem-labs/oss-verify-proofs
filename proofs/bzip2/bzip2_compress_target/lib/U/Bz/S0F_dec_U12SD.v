(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzContracts BzContracts0 DecCut DecTac DecTac2 DecTacS DecAux. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzLemmasT BzLemmasT2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzWalkArith BzWalkArith2 BzWalkArith3 BzWalkArith4 S0_dec_U13 S0_decCuts S0_decCutsM S0_decCutsE.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_decRet.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAux OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_dec_U13 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_decCuts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_decCutsM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_decCutsE OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet.S0_indexIntoF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU9 BzDU11 BzDU12F. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF DecTacFR DecTacF3 DecAux12F S0F_decRet S0F_decCuts S0F_decCutsM S0F_decCutsE.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU11 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12F OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacFR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAux12F OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCuts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCutsM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCutsE.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDU12S. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecAux12S S0F_decCuts12S.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_decRet.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDU12S. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecAux12S S0F_decCuts12S.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require LinSplit. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecFast DecFastT DecFastS.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzImg0TacFR BzImg0Tac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require NormFast. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLiaA. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require SasFastF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require SepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require UKit.
Module S0F_dec_U12SC.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAux OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_dec_U13 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_decCuts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_decCutsM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_decCutsE OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet.S0_indexIntoF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU11 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12F OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacFR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAux12F OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCuts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCutsM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCutsE.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12S OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAux12S OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCuts12S.
 Unset Lia Cache.
Import ListNotations. Local Open Scope bv_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.LinSplit OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecFast OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecFastT OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecFastS.
Local Ltac DecCut.revive H MUL WML AOK ::= DecFast.revive_cached H MUL WML AOK.
Local Ltac DecCut.dpure_from DP ::= DecFast.dpure_from_fast DP.
Local Ltac DecCut.open_dmem DM ::= DecFast.open_dmem_red DM.
Local Ltac DecTac.gb_next keep Wloc IB ::= DecFastT.gb_next_red keep Wloc IB.
Local Ltac DecTacS.revive_sm H AOK SM0 MUL WML ::= DecFastS.revive_sm_cached H AOK SM0 MUL WML.
Local Ltac DecTacS.revive_all_smL AOK SM0 MUL WML LIN DP ::= DecFastS.revive_all_smL_split AOK SM0 MUL WML LIN DP.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.NatLit.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzImg0TacFR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzImg0Tac.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= RelLiaA.lia_rf.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Local Ltac simpl_arr_sizes ::= SasFastF.sas6F_all.
Local Ltac StoreFast.tlia ::= SepFast.tlia_dr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.

Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.
  Variable F : nat.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).
  Notation L16 := (b_ll16 (a_cx A)).
  Notation L4 := (b_ll4 (a_cx A)).

  Ltac simpl_arr_sizes ::= SasFastF.sas6F_all.   (* [comment removed for export] *)
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
  Ltac small_facts SF DP :=
    let TS := fresh "TS" in let SM1 := fresh "SM1" in let HDR := fresh "HDR" in let ORIG := fresh "ORIG" in
    let NB1 := fresh "NB1" in let NB9 := fresh "NB9" in let HIST := fresh "HIST" in let SYMB := fresh "SYMB" in
    let UNZ := fresh "UNZ" in let CFP := fresh "CFP" in let HL16 := fresh "HL16" in let HL16R := fresh "HL16R" in let HL4R := fresh "HL4R" in
    cps_pose SF as (TS & SM1 & HDR & ORIG & NB1 & NB9 & HIST & SYMB & UNZ & CFP & HL16 & HL16R & HL4R);
    pose proof (dpureF_small _ _ _ _ _ _ DP) as SMALL; rewrite SM1 in SMALL; symmetry in SMALL;
    pose proof (dpureF_n _ _ _ _ _ _ DP) as BN.

  (* [comment removed for export] *)
  Definition sep_box (P : Prop) := P.
  Ltac box H := lazymatch type of H with ?P => change P with (sep_box P) in H end.
  Ltac unbox H := unfold sep_box in H.
  Ltac ck := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => UKit.u_guard | _ => idtac end.

  Section Sm.
  Variables (L : dsv) (s : dstrm) (J : jk) (sym unz ll16_0 ll4_0 : Z -> Z).
  Notation GLcF := (GLcF A F L s J sym unz ll16_0 ll4_0). Notation PRcF := (PRcF A F L s J sym unz ll16_0 ll4_0).
  Notation TAILcF := (TAILcF A F L s J sym unz ll16_0 ll4_0).

  (* [comment removed for export] *)
  Lemma S0F_U12_PRstep : forall (st : nat) fa fb i j,
    (forall fa' fb' j', PRcF (Datatypes.S st) fa' fb' j j') -> (forall fa' fb' j5, TAILcF fa' fb' j5) -> PRcF st fa fb i j.
  Proof.
    intros st fa fb i j NXT LAST. unfold S0F_decCuts12S.PRcF. intros until pb. intros DM FR ST MU WM MI DP FU SF PRS SLT V16 V4.
    small_facts SF DP.
    destruct (small_pr_pack sym unz ll16_0 ll4_0 (sv_nblock L) (d_origPtr d) ltac:(lia) SYMB HIST HL16
                 ltac:(intros kk; pose proof (HL16R kk); lia) HL4R ORIG) as [NCR PF].
    pose proof (PF st SLT) as X. rewrite PRS in X. cbv zeta in X.
    cps_destruct X as (IR & JR & GR & BJR & FBR & FAR & STEP & JO).
    assert (FAj : (0 <= fa j < 65536)%Z) by (pose proof (FAR j); lia).
    rewrite (Z.shiftr_div_pow2 j 1) in BJR by lia. change (2 ^ 1)%Z with 2%Z in BJR.
    assert (L16j : (0 <= zget (d_ll16 d) j < 65536)%Z) by (rewrite V16; exact FAj).
    assert (L4j : (0 <= zget (d_ll4 d) (j / 2) < 256)%Z) by (rewrite V4; exact BJR).
    assert (IHR : (0 <= i / 65536 < 16)%Z) by lia.
    prepS DM MU DP SMALL. unfold r_of in DR. dr_open.
    unfold blk_of in BLK. rewrite SMALL in BLK. cbn [Z.eqb blk_at] in BLK. cps_destruct BLK as (_ & L16A & L16L & L4A & L4L).
    pose proof (act_ll _ _ AOK SMALL) as [(L160 & L161 & L40 & L41) (SEP16 & _ & _ & SEP4 & _ & _ & SEP164)].
    pose proof (act_ok_al _ _ AOK) as ALG. unfold ctx_al in ALG. cps_destruct ALG as (_ & _ & _ & _ & _ & AL16 & _).
    apply Z.mod_divide in AL16; [|lia]. destruct AL16 as [q16 AL16].
    box SEP16. box SEP4. box SEP164. box JO.
    hide_all_but_at [S; S + 3152; L16; L4; usp + -336]%Z.
    pose proof (munch_refl [(L16, L16 + 200000 * b_n cx); (L4, L4 + 50000 * b_n cx)]%Z m) as MUL.
    pose proof (wmono_refl s0segs m) as WML.
    kq_intro. replace (Datatypes.S (Z.to_nat (sv_nblock L)) - st)%nat with (Datatypes.S (Z.to_nat (sv_nblock L) - st)) in KQ by lia.
    UKit.urun_to 0x27c74%Z. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zh16_read2 s0segs mm L16 (d_ll16 d) _ j _ L16A ltac:(lia) ltac:(lia) L16j ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
    wstepl. clear RD. rewrite zx16_small by lia.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zb8_read1 s0segs mm L4 (d_ll4 d) _ (j / 2)%Z _ L4A ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
    wstepl. clear RD. rewrite zxb_lit8 by lia.
    wstepl. unbox SEP16. unbox SEP4. unbox SEP164. zh16_sh L16A j. (* [comment removed for export] *) box SEP16. box SEP4. box SEP164.
    rewrite (unsigned_lit i) in L16A by lia.
    assert (FAn : forall q, zget (zset (d_ll16 d) j (i mod 65536)) q = fst (BzModel.set_ll fa fb j i) q).
    { intros q. unfold BzModel.set_ll. cbn [fst]. rewrite zget_zset, zfupd_eq, land_65535_mod'. destruct (Z.eqb_spec q j); [reflexivity| apply V16]. }
    assert (GLE : BzModel.get_ll (zget (d_ll16 d)) (zget (d_ll4 d)) j = BzModel.get_ll fa fb j) by (apply get_ll_ext; [apply V16| apply V4]).
    wstepl; if_cases Kpar; zify_cond_z Kpar.
    - (* [comment removed for export] *)
      wstepl; ck. wstepl. wstepl. wstepl; ck.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (zb8_read1 s0segs mm L4 (d_ll4 d) _ (j / 2)%Z _ L4A ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
      wstepl. clear RD. rewrite zxb_lit8 by lia.
      wstepl. wstepl. wstepl.
      pose proof (nib_odd_range' (zget (d_ll4 d) (j / 2)) (i / 65536) L4j IHR) as XR.
      pose proof (set_ll_odd d j i ltac:(lia) Kpar ltac:(lia) ltac:(lia) L4j) as SL.
      assert (FBn : forall y, zget (zset (d_ll4 d) (j / 2) (Z.lor (Z.land (zget (d_ll4 d) (j / 2)) 15) (i / 65536 * 16))) y
                              = snd (BzModel.set_ll fa fb j i) y).
      { intros y. unfold BzModel.set_ll. cbn [snd]. rewrite (Z.shiftr_div_pow2 _ 16) by lia. change (2 ^ 16)%Z with 65536%Z.
        rewrite (set_ll4_odd fb j (i / 65536)); [| lia| lia| exact Kpar].
        rewrite zget_zset, zfupd_eq, V4. destruct (Z.eqb_spec y (j / 2)); [reflexivity| apply V4]. }
      wstepl. wstepl. (* [comment removed for export] *)
      unbox SEP16. unbox SEP4. unbox SEP164. zb8_sb L4A (j / 2)%Z. (* [comment removed for export] *) box SEP16. box SEP4. box SEP164.
      wstepl. wstepl. (* [comment removed for export] *)
      wstepl. wstepl. wstepl. wstepl. (* [comment removed for export] *)
      rewrite (get_ll_asm (zget (d_ll16 d)) (zget (d_ll4 d)) j) by lia. rewrite GLE.
      pose proof (dpureF_set_ll16 _ _ _ _ _ _ j (i mod 65536) DP ltac:(change (2 ^ 16)%Z with 65536%Z; apply Z.mod_pos_bound; lia)) as DP2.
      pose proof (dpureF_set_ll4 _ _ _ _ _ _ (j / 2) (Z.lor (Z.land (zget (d_ll4 d) (j / 2)) 15) (i / 65536 * 16)) DP2 XR) as DP3. clear DP2.
      clear SEP16 SEP4 SEP164. revive_smF SMALL MUL WML LIN DP.
      blk_goal (sl_odd d j i).
      { unfold blk_of, sl_odd. rewrite SMALL. cbn [Z.eqb blk_at]. dmodel_cbn. split; [exact SMALL|].
        split; [exact L16A| split; [rewrite zh16_length; lia| split; [exact L4A| rewrite zb8_length; lia]]]. }
      clear L16A L4A. fold_MU MU SMALL.
      wstepl; if_cases K2; zify_cond_z K2.
      + (* [comment removed for export] *)
        rewrite (K_PR_step_sl F L d s i j _ _ ltac:(lia) SL) in KQ. rewrite GLE in KQ. unfold sl_odd in KQ.
        pose proof (NXT (fst (BzModel.set_ll fa fb j i)) (snd (BzModel.set_ll fa fb j i)) (BzModel.get_ll fa fb j)) as NX.
        unfold S0F_decCuts12S.PRcF in NX.
        replace (Z.to_nat (sv_nblock L) - st)%nat with (Datatypes.S (Z.to_nat (sv_nblock L)) - Datatypes.S st)%nat in KQ by lia.
        kq_fold. enter_cutF NX DP3.
        all: try (apply (smallF_frame L d _ _ _ _ _ SF); reflexivity). all: try exact STEP.
        all: try (intros q; dmodel_cbn; apply FAn). all: try (intros y; dmodel_cbn; apply FBn).
        all: try (dmodel_cbn; assert (Datatypes.S st <> ncyc sym unz (sv_nblock L) (d_origPtr d)) by (unbox JO; intros E; apply K2; apply (proj2 JO); exact E); lia).
        all: try lia.
      + (* [comment removed for export] *)
        rewrite (K_PR_exit_sl F L d s i j _ _ ltac:(lia) SL) in KQ. rewrite GLE in KQ. unfold sl_odd in KQ.
        pose proof (LAST (fst (BzModel.set_ll fa fb j i)) (snd (BzModel.set_ll fa fb j i)) (BzModel.get_ll fa fb j)) as NX.
        unfold S0F_decCuts12S.TAILcF in NX.
        replace (Z_to_bv 64 j) with (Z_to_bv 64 (d_origPtr d)) by (f_equal; lia).
        kq_fold. enter_cutF NX DP3.
        all: try (apply (smallF_frame L d _ _ _ _ _ SF); reflexivity).
        all: try (intros q; dmodel_cbn; apply FAn). all: try (intros y; dmodel_cbn; apply FBn).
        all: try (intros q; unfold BzModel.set_ll; cbn [fst]; rewrite zfupd_eq, land_65535_mod'; destruct (Z.eqb q j); [apply Z.mod_pos_bound; lia| apply FAR]).
        all: try (intros y; unfold BzModel.set_ll; cbn [snd]; rewrite (Z.shiftr_div_pow2 _ 16) by lia; change (2 ^ 16)%Z with 65536%Z;
                  rewrite (set_ll4_odd fb j (i / 65536)); [| lia| lia| exact Kpar]; rewrite zfupd_eq; destruct (Z.eqb y (j / 2)); [rewrite <- V4; exact XR| apply FBR]).
        all: try lia.
    - (* [comment removed for export] *)
      wstepl; ck.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (zb8_read1 s0segs mm L4 (d_ll4 d) _ (j / 2)%Z _ L4A ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
      wstepl. clear RD. rewrite zxb_lit8 by lia.
      wstepl. rewrite (land_m16_byte (zget (d_ll4 d) (j / 2))) by lia. wstepl. wstepl.
      pose proof (nib_even_range (zget (d_ll4 d) (j / 2)) (i / 65536) L4j IHR) as XR.
      pose proof (set_ll_even d j i ltac:(lia) Kpar ltac:(lia)) as SL.
      assert (FBn : forall y, zget (zset (d_ll4 d) (j / 2) (Z.lor (Z.land (zget (d_ll4 d) (j / 2)) 240) (i / 65536))) y
                              = snd (BzModel.set_ll fa fb j i) y).
      { intros y. unfold BzModel.set_ll. cbn [snd]. rewrite (Z.shiftr_div_pow2 _ 16) by lia. change (2 ^ 16)%Z with 65536%Z.
        rewrite (set_ll4_even fb j (i / 65536)); [| lia| lia| exact Kpar].
        rewrite zget_zset, zfupd_eq, V4. destruct (Z.eqb_spec y (j / 2)); [reflexivity| apply V4]. }
      wstepl. wstepl. wstepl. (* [comment removed for export] *)
      unbox SEP16. unbox SEP4. unbox SEP164. zb8_sb L4A (j / 2)%Z. (* [comment removed for export] *) box SEP16. box SEP4. box SEP164.
      wstepl. wstepl. (* [comment removed for export] *)
      wstepl. wstepl. wstepl. wstepl. (* [comment removed for export] *)
      rewrite (get_ll_asm (zget (d_ll16 d)) (zget (d_ll4 d)) j) by lia. rewrite GLE.
      pose proof (dpureF_set_ll16 _ _ _ _ _ _ j (i mod 65536) DP ltac:(change (2 ^ 16)%Z with 65536%Z; apply Z.mod_pos_bound; lia)) as DP2.
      pose proof (dpureF_set_ll4 _ _ _ _ _ _ (j / 2) (Z.lor (Z.land (zget (d_ll4 d) (j / 2)) 240) (i / 65536)) DP2 XR) as DP3. clear DP2.
      clear SEP16 SEP4 SEP164. revive_smF SMALL MUL WML LIN DP.
      blk_goal (sl_even d j i).
      { unfold blk_of, sl_even. rewrite SMALL. cbn [Z.eqb blk_at]. dmodel_cbn. split; [exact SMALL|].
        split; [exact L16A| split; [rewrite zh16_length; lia| split; [exact L4A| rewrite zb8_length; lia]]]. }
      clear L16A L4A. fold_MU MU SMALL.
      wstepl; if_cases K2; zify_cond_z K2.
      + (* [comment removed for export] *)
        rewrite (K_PR_step_sl F L d s i j _ _ ltac:(lia) SL) in KQ. rewrite GLE in KQ. unfold sl_even in KQ.
        pose proof (NXT (fst (BzModel.set_ll fa fb j i)) (snd (BzModel.set_ll fa fb j i)) (BzModel.get_ll fa fb j)) as NX.
        unfold S0F_decCuts12S.PRcF in NX.
        replace (Z.to_nat (sv_nblock L) - st)%nat with (Datatypes.S (Z.to_nat (sv_nblock L)) - Datatypes.S st)%nat in KQ by lia.
        kq_fold. enter_cutF NX DP3.
        all: try (apply (smallF_frame L d _ _ _ _ _ SF); reflexivity). all: try exact STEP.
        all: try (intros q; dmodel_cbn; apply FAn). all: try (intros y; dmodel_cbn; apply FBn).
        all: try (dmodel_cbn; assert (Datatypes.S st <> ncyc sym unz (sv_nblock L) (d_origPtr d)) by (unbox JO; intros E; apply K2; apply (proj2 JO); exact E); lia).
        all: try lia.
      + (* [comment removed for export] *)
        rewrite (K_PR_exit_sl F L d s i j _ _ ltac:(lia) SL) in KQ. rewrite GLE in KQ. unfold sl_even in KQ.
        pose proof (LAST (fst (BzModel.set_ll fa fb j i)) (snd (BzModel.set_ll fa fb j i)) (BzModel.get_ll fa fb j)) as NX.
        unfold S0F_decCuts12S.TAILcF in NX.
        replace (Z_to_bv 64 j) with (Z_to_bv 64 (d_origPtr d)) by (f_equal; lia).
        kq_fold. enter_cutF NX DP3.
        all: try (apply (smallF_frame L d _ _ _ _ _ SF); reflexivity).
        all: try (intros q; dmodel_cbn; apply FAn). all: try (intros y; dmodel_cbn; apply FBn).
        all: try (intros q; unfold BzModel.set_ll; cbn [fst]; rewrite zfupd_eq, land_65535_mod'; destruct (Z.eqb q j); [apply Z.mod_pos_bound; lia| apply FAR]).
        all: try (intros y; unfold BzModel.set_ll; cbn [snd]; rewrite (Z.shiftr_div_pow2 _ 16) by lia; change (2 ^ 16)%Z with 65536%Z;
                  rewrite (set_ll4_even fb j (i / 65536)); [| lia| lia| exact Kpar]; rewrite zfupd_eq; destruct (Z.eqb y (j / 2)); [rewrite <- V4; exact XR| apply FBR]).
        all: try lia.
  Time Qed.

  End Sm.
End R.
End ACeilS1.
End S0F_dec_U12SC.

Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12S OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAux12S OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCuts12S OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_dec_U12SD.S0F_dec_U12SC.
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
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= RelLiaA.lia_rf.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
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
  Notation L16 := (b_ll16 (a_cx A)).
  Notation L4 := (b_ll4 (a_cx A)).

  Ltac simpl_arr_sizes ::= rewrite ?u32s_length, ?u64s_length, ?upd_length, ?zb8_length_nat, ?zw32_length_nat, ?zh16_length_nat in *.
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
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac small_facts SF DP :=
    let TS := fresh "TS" in let SM1 := fresh "SM1" in let HDR := fresh "HDR" in let ORIG := fresh "ORIG" in
    let NB1 := fresh "NB1" in let NB9 := fresh "NB9" in let HIST := fresh "HIST" in let SYMB := fresh "SYMB" in
    let UNZ := fresh "UNZ" in let CFP := fresh "CFP" in let HL16 := fresh "HL16" in let HL16R := fresh "HL16R" in let HL4R := fresh "HL4R" in
    cps_pose SF as (TS & SM1 & HDR & ORIG & NB1 & NB9 & HIST & SYMB & UNZ & CFP & HL16 & HL16R & HL4R);
    pose proof (dpureF_small _ _ _ _ _ _ DP) as SMALL; rewrite SM1 in SMALL; symmetry in SMALL;
    pose proof (dpureF_n _ _ _ _ _ _ DP) as BN.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Section Sm.
  Variables (L : dsv) (s : dstrm) (J : jk) (sym unz ll16_0 ll4_0 : Z -> Z).
  Notation GLcF := (GLcF A F L s J sym unz ll16_0 ll4_0). Notation PRcF := (PRcF A F L s J sym unz ll16_0 ll4_0).
  Notation TAILcF := (TAILcF A F L s J sym unz ll16_0 ll4_0).

  (* [comment removed for export] *)
  Lemma S0F_U12_PR_vac : forall st fa fb i j, (sv_nblock L <= Z.of_nat st)%Z -> PRcF st fa fb i j.
  Proof.
    intros st fa fb i j Hs. unfold S0F_decCuts12S.PRcF. intros until pb. intros DM FR ST MU WM MI DP FU SF PRS SLT V16 V4.
    small_facts SF DP.
    destruct (small_pr_pack sym unz ll16_0 ll4_0 (sv_nblock L) (d_origPtr d) ltac:(lia) SYMB HIST HL16
                 ltac:(intros kk; pose proof (HL16R kk); lia) HL4R ORIG) as [NCR _].
    exfalso. lia.
  Qed.

  Lemma S0F_U12_PR_all : (forall fa fb j5, TAILcF fa fb j5) ->
    forall (dd st : nat) fa fb i j, (sv_nblock L - Z.of_nat st <= Z.of_nat dd)%Z -> PRcF st fa fb i j.
  Proof.
    intros LAST dd. induction dd as [|dd IH]; intros st fa fb i j Hd.
    - apply S0F_U12_PR_vac. lia.
    - apply (S0F_U12_PRstep A AOK F L s J sym unz ll16_0 ll4_0); [| exact LAST]. intros fa' fb' j'. apply IH. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma S0F_U12_GL : (forall fa fb j5, TAILcF fa fb j5) -> forall fa fb fc, GLcF fa fb fc.
  Proof.
    intros LAST fa fb fc. unfold S0F_decCuts12S.GLcF. intros until pb. intros DM FR ST MU WM MI DP FU SF TV V16 V4 VC.
    small_facts SF DP.
    destruct (small_pr_pack sym unz ll16_0 ll4_0 (sv_nblock L) (d_origPtr d) ltac:(lia) SYMB HIST HL16
                 ltac:(intros kk; pose proof (HL16R kk); lia) HL4R ORIG) as [NCR PF].
    pose proof (prst_0 unz ll16_0 ll4_0 (sv_nblock L) (d_origPtr d)) as P0. rewrite TV in P0.
    pose proof (PF 0%nat ltac:(lia)) as X. rewrite P0 in X. cbv zeta in X.
    cps_destruct X as (_ & _ & _ & _ & FBR & FAR & _ & _).
    assert (L16o : (0 <= zget (d_ll16 d) (d_origPtr d) < 65536)%Z) by (rewrite V16; apply FAR).
    assert (L4o : (0 <= zget (d_ll4 d) (d_origPtr d / 2) < 256)%Z) by (rewrite V4; apply FBR).
    assert (GLE : BzModel.get_ll (zget (d_ll16 d)) (zget (d_ll4 d)) (d_origPtr d) = BzModel.get_ll fa fb (d_origPtr d)) by (apply get_ll_ext; [apply V16| apply V4]).
    prepS DM MU DP SMALL. unfold r_of in DR. dr_open.
    pose proof BLK as BLK0.
    unfold blk_of in BLK. rewrite SMALL in BLK. cbn [Z.eqb blk_at] in BLK. cps_destruct BLK as (_ & L16A & L16L & L4A & L4L).
    pose proof (act_ll _ _ AOK SMALL) as [(L160 & L161 & L40 & L41) _].
    pose proof (act_ok_al _ _ AOK) as ALG. unfold ctx_al in ALG. cps_destruct ALG as (_ & _ & _ & _ & _ & AL16 & _).
    apply Z.mod_divide in AL16; [|lia]. destruct AL16 as [q16 AL16].
    hide_all_but_at [S; S + 3152; L16; L4; usp + -336]%Z.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    kq_intro. rewrite K_L27_PR, GLE in KQ.
    UKit.urun_to 0x27bf8%Z. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zb8_read1 s0segs mm L4 (d_ll4 d) _ (d_origPtr d / 2)%Z _ L4A ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
    wstepl. clear RD. rewrite zxb_lit8 by lia.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zh16_read2 s0segs mm L16 (d_ll16 d) _ (d_origPtr d) _ L16A ltac:(lia) ltac:(lia) L16o ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
    wstepl. clear RD. rewrite zx16_small by lia.
    wstepl. wstepl. wstepl. wstepl. wstepl. wstepl. (* [comment removed for export] *)
    rewrite (get_ll_asm (zget (d_ll16 d)) (zget (d_ll4 d)) (d_origPtr d)) by lia. rewrite GLE.
    clear L16A L4A. rename BLK0 into BLK. revive_all MUL WML AOK. fold_MU MU SMALL.
    pose proof (S0F_U12_PR_all LAST (Z.to_nat (sv_nblock L)) 0%nat fa fb (d_origPtr d) (BzModel.get_ll fa fb (d_origPtr d)) ltac:(lia)) as NX.
    unfold S0F_decCuts12S.PRcF in NX.
    kq_fold. enter_cutF NX DP.
    all: try exact SF. all: try exact P0. all: try exact V16. all: try exact V4. all: try lia.
  Time Qed.
  End Sm.
End R.
End ACeilS1.
