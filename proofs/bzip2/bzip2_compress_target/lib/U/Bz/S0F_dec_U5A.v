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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF DecTacFR S0F_decRet S0F_decCuts S0F_gb_I.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_gb_I.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacFR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCuts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_gb_I OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_gb_I.S0F_gb_M.
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
(* [comment removed for export] *)
Lemma ngroups_testF : forall g, (0 <= g < 8)%Z -> Z.land (Z.shiftr 131 g) 1 = 0%Z -> (2 <= g <= 6)%Z.
Proof.
  intros g Hg E.
  assert (C : (g = 0 \/ g = 1 \/ g = 2 \/ g = 3 \/ g = 4 \/ g = 5 \/ g = 6 \/ g = 7)%Z) by lia.
  destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; cbv in E; try lia; discriminate.
Qed.
Lemma ngroups_testF' : forall g, (0 <= g < 8)%Z -> Z.land (Z.shiftr 131 g) 1 <> 0%Z -> (g < 2 \/ 6 < g)%Z.
Proof.
  intros g Hg E.
  assert (C : (g = 0 \/ g = 1 \/ g = 2 \/ g = 3 \/ g = 4 \/ g = 5 \/ g = 6 \/ g = 7)%Z) by lia.
  destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; cbv in E; try lia; exfalso; apply E; reflexivity.
Qed.

Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  Lemma S0F_dec_U5A : forall F, (forall F', (F' < F)%nat -> S0F_cut_L5O A F') -> S0F_cut_HSEL A F.
  Proof.
    intros F HL5O. unfold S0F_cut_HSEL. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold W14, D14, DSTATE_SIZE in MU. cbn [app blk_ivls b_s b_strm] in MU.
    destruct DI as [[AL NBL]].
    open_dmemF DM. s2img.
    (* [comment removed for export] *)
    gbF_call (S0F_gb_1d7ac A AOK (QF A) (S0F_dec_ret_ok A AOK) _ _ _ _ JK_) MU WM AOK DP FU.
    gbF_next [S]%Z [(S, S + 68)]%Z.
    (* [comment removed for export] *)
    wstepl. wstepl. gbv 1%Z 3%Z ng.
    wstepl. wstepl.
    (* [comment removed for export] *)
    wstepl. if_false_z.
    (* [comment removed for export] *)
    wstepl. wstepl. wstepl. revive_all MUL WML AOK. wstepl.
    wstepl; if_cases KNG; zify_cond KNG.
    2: { rewrite Z.mod_small in KNG by lia. apply ngroups_testF' in KNG; [|lia].
      rewrite gb_after_30 in KQ. rewrite dgo_if_true in KQ by blia. rewrite dgo_DRet in KQ.
      wstepl. wstepl. wstepl. wstepl. wstepl. wstepl.
      revive_all MUL WML AOK. enter_retF (S0F_dec_retc A AOK) DP. }
    rewrite Z.mod_small in KNG by lia.
    assert (NG : (2 <= ng <= 6)%Z) by (apply ngroups_testF; [lia | exact KNG]). clear KNG.
    rewrite gb_after_30 in KQ. rewrite dgo_if_false in KQ by blia. rewrite dgo_DGo in KQ.
    (* [comment removed for export] *)
    gbF_call (S0F_gb_1be0c A AOK (QF A) (S0F_dec_ret_ok A AOK) _ _ _ _ JK_) MUL WML AOK DP FU.
    gbF_next [S]%Z [(S, S + 68)]%Z.
    (* [comment removed for export] *)
    wstepl. wstepl. wstepl.
    gbv 10%Z 15%Z ns.
    (* [comment removed for export] *)
    wstepl.
    wstepl; if_cases KS; zify_cond KS.
    { (* [comment removed for export] *)
      rewrite (edge_31_ret ns) in KQ by lia. rewrite dgo_DRet in KQ.
      revive_all MUL WML AOK. enter_retF (S0F_dec_ret_data A AOK) DP. }
    (* [comment removed for export] *)
    wstepl. wstepl.
    rewrite (edge_31 _ ns) in KQ by lia.
    revive_all MUL WML AOK. enter_nextF HL5O DP.
    unfold dinv_L5O, alpha_ok. dmodel_cbn. rewrite Z.min_l by lia.
    repeat match goal with |- _ /\ _ => split end; try lia. apply belown_0.
  Qed.
End R.
End ACeilS1.
