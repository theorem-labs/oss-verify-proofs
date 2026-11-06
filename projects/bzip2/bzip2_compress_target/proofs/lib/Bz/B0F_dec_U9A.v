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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU9 DecAuxR DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAuxR OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFB DecTacFB DecTacFRB B0F_decV B0F_decRet B0F_decCutsM.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCutsM.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecAuxH DecTacM.

Section ACeilS1. Context {ACEIL__ : ACeil}.
Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok BIHI0 A.
  Hypothesis ASH : act_sh DI_B0 A.
  Variable Q : dres -> machine_state -> Prop.
  Hypothesis HRET : B0F_RET A Q.
  Variable F : nat.
  Hypothesis HMTFB : B0F_cut_HMTFB A Q F.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  Lemma B0F_U9_HRUN : B0F_cut_HRUN A Q F.
  Proof.
    unfold B0F_cut_HRUN. intros until w752. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    open_dmemF DM. b0img.
    cps_destruct DI as (ML & NSR & RO). pose proof RO as RO'. unfold run_okF in RO'.
    pose proof (alpha_ok_state L d (proj1 ML)) as NST.
    assert (NBL : (0 <= sv_nblock L <= 900000)%Z) by (pose proof (proj1 ML) as AL; unfold alpha_ok in AL; tauto).
    unfold r_of in DR. dr_open. hide_all_but_atF [a_P A; a_P A + 344]%Z.
    pose proof (munch_refl [(a_P A + 344, a_P A + 760)]%Z m) as MUL. pose proof (wmono_refl b0segs m) as WML.
    kq_intro. unfold K_HRUN in KQ.
    (* [comment removed for export] *)
    brun; if_cases KN; zify_cond_z KN.
    { (* [comment removed for export] *)
      brun_to 0xafb90%Z.
      rewrite (run_body_ret L d s) in KQ by lia. rewrite dgo_DRet in KQ.
      revive_all MUL WML AOK. kq_fold.
      enter_cutF (HRET _ _ _ _ JK_) DP; [ ret_nb | apply dpost14_ne; dmodel_cbn; exact NST ]. }
    rewrite (run_body_go L d s) in KQ by lia. change (dgo F (mtf_val_start BZ_X_MTF_3 ?L1 d s)) with (K_HMTFB F L1 d s) in KQ.
    assert (NS01 : sv_nextSym L = 0%Z \/ sv_nextSym L = 1%Z) by lia.
    rewrite (run_delta_shift (sv_nextSym L) (sv_N L)) in KQ by lia.
    (* [comment removed for export] *)
    Ltac lwslotB k :=
      match goal with FR : rw_cells b0segs _ (a_P _ + 344)%Z _ |- _ =>
        let C := fresh "FR8" in pose proof FR as C; hide C; DecTacM.slot_split FR k;
        astep; clear FR; unfold hidden in C; rename C into FR end.
    Ltac fin_run HMTFB MUL WML AOK DP ML RO :=
      revive_all MUL WML AOK; enter_sameF HMTFB DP;
      (split; [apply dinv_ML_esN; exact ML|]); dmodel_cbn; (split; [apply run_okF_step; [exact RO| lia| lia] | lia]).
    (* [comment removed for export] *)
    Ltac runA := (* [comment removed for export] *)
      lwslotB 17%nat; rewrite ?sx32_m1w;
      bstep; rewrite ?zbv_addm1;
      bstep; rewrite ?swrap32_addm1, ?swrap32_m1add by lia;
      brun_to 0xb4b1c%Z.
    Ltac runB := (* [comment removed for export] *)
      brun_to 0xb4ad4%Z;
      lwslotB 17%nat; rewrite ?sx32_m1w;
      bstep; rewrite ?zbv_addm1;
      bstep;
      bstep; rewrite ?swrap32_addm1, ?swrap32_m1add by lia;
      brun_to 0xb4b1c%Z.
    destruct (Z.eq_dec (sv_es L) (-1)) as [Ees|NE].
    - rewrite Ees in *.
      bstep; if_cases K0; zify_cond_z K0.
      + runA.
        replace (sv_nextSym L) with 0%Z in KQ by lia. rewrite Z.pow_0_r, Z.mul_1_r in KQ.
        rewrite ?(Z.mul_comm (sv_N L) 2) in *.
        fin_run HMTFB MUL WML AOK DP ML RO.
      + runB.
        replace (sv_nextSym L) with 1%Z in KQ by lia. rewrite Z.pow_1_r in KQ.
        rewrite ?(Z.mul_comm (sv_N L) 2) in *.
        fin_run HMTFB MUL WML AOK DP ML RO.
    - assert (ES0 : (0 <= sv_es L)%Z) by lia.
      bstep; if_cases K0; zify_cond_z K0.
      + runA.
        replace (sv_nextSym L) with 0%Z in KQ by lia. rewrite Z.pow_0_r, Z.mul_1_r in KQ.
        rewrite ?(Z.mul_comm (sv_N L) 2) in *.
        fin_run HMTFB MUL WML AOK DP ML RO.
      + runB.
        replace (sv_nextSym L) with 1%Z in KQ by lia. rewrite Z.pow_1_r in KQ.
        rewrite ?(Z.mul_comm (sv_N L) 2) in *.
        fin_run HMTFB MUL WML AOK DP ML RO.
  Qed.
End R.
End ACeilS1.

