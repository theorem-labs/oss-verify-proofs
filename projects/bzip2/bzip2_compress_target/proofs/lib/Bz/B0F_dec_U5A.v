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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFB DecTacFB DecTacFRB B0F_decV B0F_decRet B0F_decCuts5 B0F_gb_C B0F_gb_D.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCuts5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_gb_C OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_gb_D.
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
  Hypothesis AOK : act_ok BIHI0 A.
  Hypothesis ASH : act_sh DI_B0 A.
  Variable Q : dres -> machine_state -> Prop.
  Hypothesis HRETOK : B0F_RET_OK A Q.
  Hypothesis HRETD : B0F_RET_DATA A Q.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  Ltac next := gbF_nextA [S; a_P A; a_P A + 344]%Z [(S, S + 68); (a_P A + 344, a_P A + 760)]%Z.

  Lemma B0F_dec_U5A : forall F, (forall F', (F' < F)%nat -> B0F_cut_L5O A Q F') -> B0F_cut_HSEL A Q F.
  Proof.
    intros F HL5O. unfold B0F_cut_HSEL. intros until w752. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    destruct DI as [[AL NBL]].
    open_dmemF DM. b0img.
    (* [comment removed for export] *)
    gbF_call (B0F_gb_afe40 A AOK ASH Q HRETOK _ _ _ _ JK_) MU WM AOK DP FU. next.
    arun_lwbuf. arun_gbv 3%Z ng.
    (* [comment removed for export] *)
    brun. if_cases K7; zify_cond_z K7; [exfalso; lia|].
    (* [comment removed for export] *)
    brun; if_cases KNG; zify_cond KNG.
    { rewrite Z.mod_small in KNG by lia. apply ngroups_testF' in KNG; [|lia].
      rewrite gb_after_30 in KQ. rewrite dgo_if_true in KQ by blia. rewrite dgo_DRet in KQ.
      revive_all MUL WML AOK. enter_retF HRETD DP. }
    rewrite Z.mod_small in KNG by lia.
    assert (NG : (2 <= ng <= 6)%Z) by (apply ngroups_testF; [lia | exact KNG]). clear KNG.
    rewrite gb_after_30 in KQ. rewrite dgo_if_false in KQ by blia. rewrite dgo_DGo in KQ.
    (* [comment removed for export] *)
    gbF_call (B0F_gb_afecc A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU. next.
    arun_lwbuf. arun_gbv 15%Z ns.
    (* [comment removed for export] *)
    brun; if_cases KS; zify_cond KS.
    { (* [comment removed for export] *)
      rewrite (edge_31 _ ns) in KQ by lia.
      revive_all MUL WML AOK. enter_nextF HL5O DP.
      unfold dinv_L5O, alpha_ok. dmodel_cbn. rewrite Z.min_l by lia.
      repeat match goal with |- _ /\ _ => split end; try lia. apply belown_0. }
    (* [comment removed for export] *)
    brun_to 0xafb8c%Z.
    rewrite (edge_31_ret ns) in KQ by lia. rewrite dgo_DRet in KQ.
    revive_all MUL WML AOK. enter_retF HRETD DP.
  Qed.
End R.
End ACeilS1.
