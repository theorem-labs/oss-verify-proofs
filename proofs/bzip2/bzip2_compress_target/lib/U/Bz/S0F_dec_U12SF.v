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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem BzDOKS.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU9 BzDU11 BzDU12F. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF DecTacFR DecTacF3 DecAux12F S0F_decRet S0F_decCuts S0F_decCutsM S0F_decCutsE.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU11 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12F OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacFR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAux12F OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCuts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCutsM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCutsE.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDU12S. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecAux12S S0F_decCuts12S S0F_dec_U12SA S0F_dec_U12SB.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_dec_U12SD.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_dec_U12SD.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_decRet.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDU12S. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecAux12S S0F_decCuts12S.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require LinSplit. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecFast DecFastT DecFastS.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzImg0TacFR BzImg0Tac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require NormFast. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLiaA. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require SasFastF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require UKit.
Module S0F_dec_U12SE.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAux OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_dec_U13 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_decCuts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_decCutsM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_decCutsE OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet.S0_indexIntoF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKS.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= RelLiaA.lia_rf.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Local Ltac simpl_arr_sizes ::= SasFastF.sas6F_all.
Local Ltac StoreFast.tlia ::= RelLia.tlia_r.
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
  Ltac exit_tail MUL WML := do 10 wstepl; revive_all MUL WML AOK.
  Ltac ck := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => UKit.u_guard | _ => idtac end.

  Section Sm.
  Variables (L : dsv) (s : dstrm) (J : jk) (sym unz ll16_0 ll4_0 : Z -> Z).
  Notation TAILcF := (TAILcF A F L s J sym unz ll16_0 ll4_0).
  Notation TRcF := (TRcF A F L s J sym unz ll16_0 ll4_0). Notation TNcF := (TNcF A F L s J sym unz ll16_0 ll4_0).

  (* [comment removed for export] *)
  Lemma S0F_U12_TAIL : forall fa fb j5, TRcF fa fb j5 -> TNcF fa fb j5 -> TAILcF fa fb j5.
  Proof.
    intros fa fb j5 TR TN. unfold S0F_decCuts12S.TAILcF. intros until pb. intros DM FR ST MU WM MI DP FU SF FAR FBR V16 V4.
    small_facts SF DP. cps_pose HDR as (RND & SBC & OPR).
    prepS DM MU DP SMALL.
    hide_all_but_at [S; S + 1092; usp + -336]%Z.
    pose proof (munch_refl [(S, S + 68); (S + 1092, S + 1096); (usp + -336, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    kq_intro.
    wstepl. wstepl. wstepl. rewrite zxb_lit8 by lia. (* [comment removed for export] *)
    wstepl. wstepl. (* [comment removed for export] *)
    wstepl; if_cases Kbr; zify_cond_z Kbr.
    - (* [comment removed for export] *)
      rewrite (K_TAIL_nr F L d s j5) in KQ by lia.
      revive_all MUL WML AOK. fold_MU MU SMALL.
      pose proof TN as NX. unfold S0F_decCuts12S.TNcF in NX. kq_fold. enter_cutF NX DP.
      all: try exact SF. all: try exact FAR. all: try exact FBR. all: try exact V16. all: try exact V4. all: try lia.
    - rewrite (K_TAIL_r F L d s j5) in KQ by lia.
      revive_all MUL WML AOK. fold_MU MU SMALL.
      pose proof TR as NX. unfold S0F_decCuts12S.TRcF in NX. kq_fold. enter_cutF NX DP.
      all: try exact SF. all: try exact FAR. all: try exact FBR. all: try exact V16. all: try exact V4. all: try lia.
  Time Qed.

  (* [comment removed for export] *)
  Lemma S0F_U12_TN : forall fa fb j5, TNcF fa fb j5.
  Proof.
    intros fa fb j5. unfold S0F_decCuts12S.TNcF. intros until pb. intros DM FR ST MU WM MI DP FU SF FAR FBR V16 V4 Kbr.
    small_facts SF DP.
    assert (FAo : (0 <= zget (d_ll16 d) (d_origPtr d) < 65536)%Z) by (rewrite V16; apply FAR).
    assert (FBo : (0 <= zget (d_ll4 d) (d_origPtr d / 2) < 256)%Z) by (rewrite V4; apply FBR).
    pose proof (smallF_cftab_range _ _ _ _ _ _ SF) as CFR.
    assert (GLE : BzModel.get_ll (zget (d_ll16 d)) (zget (d_ll4 d)) (d_origPtr d) = get_ll d (d_origPtr d)) by (symmetry; apply get_ll_view).
    pose proof (get_ll_range (zget (d_ll16 d)) (zget (d_ll4 d)) (d_origPtr d) FAo ltac:(rewrite (Z.shiftr_div_pow2 _ 1) by lia; change (2 ^ 1)%Z with 2%Z; lia)) as GR.
    prepS DM MU DP SMALL. chunks_normF.
    pose proof (act_ll _ _ AOK SMALL) as [(L160 & L161 & L40 & L41) (SEP16 & _ & _ & SEP4 & _ & _ & SEP164)].
    pose proof (act_ok_al _ _ AOK) as ALG. unfold ctx_al in ALG. cps_destruct ALG as (ALS & _ & _ & _ & _ & AL16 & _).
    apply Z.mod_divide in AL16; [|lia]. destruct AL16 as [q16 AL16].
    pose proof BLK as BLK0.
    rewrite SMALL in BLK. cbn [Z.eqb blk_at] in BLK. cps_destruct BLK as (_ & L16A & L16L & L4A & L4L).
    hide_all_but_at [S; S + 1092; S + 1096; S + 3152; usp + -336]%Z.
    pose proof (munch_refl [(S, S + 68); (S + 1092, S + 1096); (usp + -336, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    kq_intro.
    wstepl. rewrite BN. rewrite ?sx32_of_Z by lia. wstepl. wstepl. wstepl. (* [comment removed for export] *)
    wstepl; if_cases Ktp; zify_cond_z Ktp; [exfalso; lia|].
    wstepl. wstepl. wstepl. (* [comment removed for export] *)
    call (S0_indexIntoF_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (S + 1096)%Z (zw32 (d_cftab d) 257)).
    1:{ exact CF. } 1:{ rewrite zw32_length_nat; reflexivity. } 1:{ exact MI. } 1:{ lia. } 1:{ clear - ALS. Z.div_mod_to_equations. lia. } 1:{ reflexivity. }
    match goal with H : mem_inv _ _ |- _ => rename H into MI end.
    rewrite (signed_lit_small (d_origPtr d)) by lia. rewrite (iif_zw32 (d_cftab d) (d_origPtr d)) by (intros ii Hii; pose proof (CFR ii Hii); lia).
    pose proof (indexIntoF_range (d_origPtr d) (d_cftab d)) as K0R.
    remember (indexIntoF (d_origPtr d) (d_cftab d)) as k0 eqn:Ek0. try rewrite <- Ek0 in KQ.
    wstepl. wstepl. (* [comment removed for export] *)
    wstepl. (* [comment removed for export] *)
    wstepl. wstepl. (* [comment removed for export] *)
    wstepl. (* [comment removed for export] *)
    wstepl. UKit.urun_to 0x27f68%Z. (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof L4A as L4AL. revive L4AL MUL WML AOK.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zb8_read1 s0segs mm L4 (d_ll4 d) _ (d_origPtr d / 2)%Z _ L4AL ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
    wstepl. clear RD L4AL. rewrite zxb_lit8 by lia.
    (* [comment removed for export] *)
    pose proof L16A as L16AL. revive L16AL MUL WML AOK.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zh16_read2 s0segs mm L16 (d_ll16 d) _ (d_origPtr d) _ L16AL ltac:(lia) ltac:(lia) FAo ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
    wstepl. clear RD L16AL. rewrite zx16_small by lia.
    wstepl. wstepl. wstepl. wstepl. wstepl. wstepl. wstepl. (* [comment removed for export] *)
    rewrite (get_ll_asm (zget (d_ll16 d)) (zget (d_ll4 d)) (d_origPtr d)) by lia. rewrite GLE. rewrite GLE in GR.
    remember (get_ll d (d_origPtr d)) as tp2 eqn:Etp. try rewrite <- Etp in KQ.
    wstepl. wstepl. wstepl; ck. (* [comment removed for export] *)
    clear L16A L4A. rename BLK0 into BLK.
    exit_tail MUL WML. fold_MU MU SMALL.
    unfold sft_nr in KQ. kq_fold. enter_cutF (S0F_dec_retc A AOK _ _ _ _ JK_) DP; [ ret_nb | ].
    intros _. pose proof (dout_ok_sft_nr L d sym unz ll16_0 ll4_0 j5 k0 tp2 SF Kbr ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as OK.
    unfold sft_nr in OK. dmodel_cbn_in OK. dmodel_cbn. exact OK.
  Time Qed.
  End Sm.
End R.
End ACeilS1.
End S0F_dec_U12SE.

Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12S OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAux12S OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCuts12S OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_dec_U12SA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_dec_U12SB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_dec_U12SD.S0F_dec_U12SC OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_dec_U12SD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_dec_U12SF.S0F_dec_U12SE.
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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require NormFast. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLiaA. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require SasFastF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLia.
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
  Ltac exit_tail MUL WML := do 6 wstepl; revive_all MUL WML AOK.
  Ltac ck := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => UKit.u_guard | _ => idtac end.

  Section Sm.
  Variables (L : dsv) (s : dstrm) (J : jk) (sym unz ll16_0 ll4_0 : Z -> Z).
  Notation TRcF := (TRcF A F L s J sym unz ll16_0 ll4_0).

  (* [comment removed for export] *)
  Lemma S0F_U12_TR : forall fa fb j5, TRcF fa fb j5.
  Proof.
    intros fa fb j5. unfold S0F_decCuts12S.TRcF. intros until pb. intros DM FR ST MU WM MI DP FU SF FAR FBR V16 V4 Kbr.
    small_facts SF DP.
    assert (FAo : (0 <= zget (d_ll16 d) (d_origPtr d) < 65536)%Z) by (rewrite V16; apply FAR).
    assert (FBo : (0 <= zget (d_ll4 d) (d_origPtr d / 2) < 256)%Z) by (rewrite V4; apply FBR).
    pose proof (smallF_cftab_range _ _ _ _ _ _ SF) as CFR.
    assert (GLE : BzModel.get_ll (zget (d_ll16 d)) (zget (d_ll4 d)) (d_origPtr d) = get_ll d (d_origPtr d)) by (symmetry; apply get_ll_view).
    pose proof (get_ll_range (zget (d_ll16 d)) (zget (d_ll4 d)) (d_origPtr d) FAo ltac:(rewrite (Z.shiftr_div_pow2 _ 1) by lia; change (2 ^ 1)%Z with 2%Z; lia)) as GR.
    prepS DM MU DP SMALL. chunks_normF.
    pose proof (act_ll _ _ AOK SMALL) as [(L160 & L161 & L40 & L41) (SEP16 & _ & _ & SEP4 & _ & _ & SEP164)].
    pose proof (act_ok_al _ _ AOK) as ALG. unfold ctx_al in ALG. cps_destruct ALG as (ALS & _ & _ & _ & _ & AL16 & _).
    apply Z.mod_divide in AL16; [|lia]. destruct AL16 as [q16 AL16].
    pose proof BLK as BLK0.
    rewrite SMALL in BLK. cbn [Z.eqb blk_at] in BLK. cps_destruct BLK as (_ & L16A & L16L & L4A & L4L).
    hide_all_but_at [S; S + 1092; S + 1096; S + 3152; usp + -336]%Z.
    pose proof (munch_refl [(S, S + 68); (S + 1092, S + 1096); (usp + -336, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    kq_intro.
    wstepl. rewrite BN. rewrite ?sx32_of_Z by lia. wstepl. wstepl. wstepl. (* [comment removed for export] *)
    (* [comment removed for export] *)
    apply (rw_cells_merge_mid s0segs _ _ _ 7 2) in HD. cbn [firstn skipn cells_size csize cells_bytes cbytes Nat.add app] in HD.
    step. change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)). mem_after_store.
    lazymatch goal with HD' : rw_cells _ _ S (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: C8 (Z_to_bv 64 0) :: ?post) |- _ =>
      apply (rw_cells_split_c8_zero s0segs _ _ [c0; c1; c2; c3; c4; c5; c6] post) in HD'; cbn [app] in HD' end.
    wstepl; if_cases Ktp; zify_cond_z Ktp; [exfalso; lia|].
    wstepl. wstepl. wstepl. (* [comment removed for export] *)
    call (S0_indexIntoF_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (S + 1096)%Z (zw32 (d_cftab d) 257)).
    1:{ exact CF. } 1:{ rewrite zw32_length_nat; reflexivity. } 1:{ exact MI. } 1:{ lia. } 1:{ clear - ALS. Z.div_mod_to_equations. lia. } 1:{ reflexivity. }
    match goal with H : mem_inv _ _ |- _ => rename H into MI end.
    rewrite (signed_lit_small (d_origPtr d)) by lia. rewrite (iif_zw32 (d_cftab d) (d_origPtr d)) by (intros ii Hii; pose proof (CFR ii Hii); lia).
    pose proof (indexIntoF_range (d_origPtr d) (d_cftab d)) as K0R.
    remember (indexIntoF (d_origPtr d) (d_cftab d)) as k0 eqn:Ek0. try rewrite <- Ek0 in KQ.
    wstepl. (* [comment removed for export] *)
    wstepl. (* [comment removed for export] *)
    wstepl. (* [comment removed for export] *)
    wstepl. wstepl. (* [comment removed for export] *)
    wstepl. (* [comment removed for export] *)
    wstepl. UKit.urun_to 0x27d84%Z. (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof L4A as L4AL. revive L4AL MUL WML AOK.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zb8_read1 s0segs mm L4 (d_ll4 d) _ (d_origPtr d / 2)%Z _ L4AL ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
    wstepl. clear RD L4AL. rewrite zxb_lit8 by lia.
    (* [comment removed for export] *)
    pose proof L16A as L16AL. revive L16AL MUL WML AOK.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zh16_read2 s0segs mm L16 (d_ll16 d) _ (d_origPtr d) _ L16AL ltac:(lia) ltac:(lia) FAo ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
    wstepl. clear RD L16AL. rewrite zx16_small by lia.
    wstepl. wstepl. wstepl. wstepl. wstepl. wstepl. wstepl. (* [comment removed for export] *)
    rewrite (get_ll_asm (zget (d_ll16 d)) (zget (d_ll4 d)) (d_origPtr d)) by lia. rewrite GLE. rewrite GLE in GR.
    remember (get_ll d (d_origPtr d)) as tp2 eqn:Etp. try rewrite <- Etp in KQ.
    wstepl. wstepl. wstepl; ck. wstepl. wstepl. (* [comment removed for export] *)
    wstepl; if_cases Krn; zify_cond_z Krn; [exfalso; lia|].
    wstepl. wstepl. wstepl; ck. (* [comment removed for export] *)
    wstepl. (* [comment removed for export] *)
    pose proof GOT as GOTL. revive GOTL MUL WML AOK. wstepl. clear GOTL. (* [comment removed for export] *)
    wstepl. wstepl. wstepl; ck. wstepl. wstepl. (* [comment removed for export] *)
    pose proof RN as RNL'. revive RNL' MUL WML AOK.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_read s0segs mm _ rnums_words 0 (Z_to_bv 64 (rNums 0)) _ RNL' (rnums_words_nth12 0 ltac:(lia)) ltac:(lia) eq_refl) as RDr end.
    wstepl. clear RDr RNL'. (* [comment removed for export] *) rewrite rNums_0. rewrite ?(sx32_of_Z 619) by lia.
    wstepl. wstepl. (* [comment removed for export] *) change (Z.b2z (18446744073709551105 <? 1)) with 0%Z.
    wstepl. wstepl. (* [comment removed for export] *)
    repeat match goal with |- context [Z_to_bv 64 (Z.land ?a ?b)] => let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v end.
    wstepl. (* [comment removed for export] *)
    wstepl. wstepl. (* [comment removed for export] *)
    wstepl. wstepl; ck. wstepl. wstepl. wstepl. wstepl. wstepl. (* [comment removed for export] *) change (Z.b2z (617 <? 1)) with 0%Z.
    wstepl. (* [comment removed for export] *) rewrite Z.lxor_0_r.
    wstepl. wstepl. wstepl. (* [comment removed for export] *)
    clear L16A L4A. rename BLK0 into BLK.
    exit_tail MUL WML. fold_MU MU SMALL.
    unfold sft_r in KQ. kq_fold. enter_cutF (S0F_dec_retc A AOK _ _ _ _ JK_) DP; [ ret_nb | ].
    intros _. pose proof (dout_ok_sft_r L d sym unz ll16_0 ll4_0 j5 k0 tp2 SF ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as OK.
    unfold sft_r in OK. dmodel_cbn_in OK. dmodel_cbn. exact OK.
  Time Qed.
  End Sm.

  (* [comment removed for export] *)
  Lemma S0F_U12_S : S0F_cut_HSMALL A F.
  Proof.
    apply (S0F_U12_HSMALL A AOK F). intros L s J sym unz ll16_0 ll4_0.
    destruct (Z_lt_le_dec (sv_nblock L) 1) as [LT|GE].
    - (* [comment removed for export] *)
      unfold S0F_decCuts12S.L27cF. intros. exfalso.
      match goal with SF : smallF _ _ _ _ _ _ |- _ => cps_destruct SF as (_ & _ & _ & ORIG & _); lia end.
    - apply (S0F_U12_L27_all A AOK F L s J sym unz ll16_0 ll4_0 ltac:(lia)).
      apply (S0F_U12_GL A AOK F). intros fa fb j5. apply (S0F_U12_TAIL A AOK F); [apply S0F_U12_TR | apply (S0F_U12_TN A AOK F)].
  Qed.
End R.

Lemma S0F_dec_U12S : forall A, act_ok 320 A -> forall F, S0F_cut_HSMALL A F.
Proof. intros A AOK F. exact (S0F_U12_S A AOK F). Qed.
End ACeilS1.
