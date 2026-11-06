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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts DecCut DecTac DecAux.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDU2 DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFA DecTacFA DecTacFRA A0F_decV A0F_decRet A0F_decCutsA A0F_gb_G A0F_gb_H.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCutsA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_gb_G OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_gb_H.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit.
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
  Hypothesis HRETOK : A0F_RET_OK A Q.
  Hypothesis HRETD : A0F_RET_DATA A Q.
  Hypothesis HRETD2 : A0F_RET_DATA2 A Q.
  Hypothesis HRETC : A0F_RETC A Q.
  Variable F : nat.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  (* [comment removed for export] *)
  Ltac ret_data MUL WML DP :=
    astep; revive_all MUL WML AOK; first [ enter_retF HRETD DP | enter_retF HRETD2 DP ].
  Ltac next := gbF_nextA [S; S + 3152; a_P A; a_P A + 496]%Z [(S, S + 68); (S + 3152, S + 3196)]%Z.
  (* [comment removed for export] *)
  Ltac endhdr_tail MUL WML DP uc K EQ :=
    arun_lwbuf; arun_gbv 8%Z uc;
    match goal with H : kq _ _ |- _ => rewrite EQ in H end;
    arun; if_cases K; zify_cond_z K;
    [ match goal with H : kq _ _ |- _ => rewrite if_trueP in H by blia; rewrite dgo_DGo in H end
    | match goal with H : kq _ _ |- _ => rewrite if_falseP in H by blia; rewrite dgo_DRet in H end; ret_data MUL WML DP ].
  (* [comment removed for export] *)
  Ltac ccrc_tail uc EQ nexthead :=
    arun_lwbuf; arun_gbv 8%Z uc; arun_to nexthead;
    match goal with H : rw_cells _ _ (b_s _ + 3152)%Z _ |- _ => crc_cellA H 28%nat end;
    match goal with H : kq _ _ |- _ => rewrite EQ, dgo_DGo in H end.

  Lemma A0F_dec_U3 : A0F_cut_HEND A Q F.
  Proof.
    unfold A0F_cut_HEND. intros until w720. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    unfold dinv_HEND, nb_ok in DI.
    open_dmemF DM. a0img.
    (* [comment removed for export] *)
    gbF_call (A0F_gb_a00c4 A AOK ASH Q HRETOK _ _ _ _ JK_) MU WM AOK DP FU. next.
    endhdr_tail MUL WML DP u1 K1 gb_after_42.
    (* [comment removed for export] *)
    gbF_call (A0F_gb_a0148 A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU. next.
    endhdr_tail MUL WML DP u2 K2 gb_after_43.
    (* [comment removed for export] *)
    gbF_call (A0F_gb_a01cc A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU. next.
    endhdr_tail MUL WML DP u3 K3 gb_after_44.
    (* [comment removed for export] *)
    gbF_call (A0F_gb_a0250 A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU. next.
    endhdr_tail MUL WML DP u4 K4 gb_after_45.
    (* [comment removed for export] *)
    gbF_call (A0F_gb_a02d4 A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU. next.
    endhdr_tail MUL WML DP u5 K5 gb_after_46.
    (* [comment removed for export] *)
    arun_to 0xa0694%Z.
    (* [comment removed for export] *)
    gbF_call (A0F_gb_a0378 A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU. next.
    ccrc_tail u6 gb_after_47 0xa0734%Z.
    gbF_call (A0F_gb_a0418 A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU. next.
    ccrc_tail u7 gb_after_48 0xa07d4%Z.
    gbF_call (A0F_gb_a04b8 A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU. next.
    ccrc_tail u8 gb_after_49 0xa0874%Z.
    (* [comment removed for export] *)
    gbF_call (A0F_gb_a0558 A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU. next.
    match goal with H : aframe _ _ |- _ => view_aframe_mid H end.
    arun_lwbuf. arun_gbv 8%Z u9.
    arun_to 0x9eb7c%Z.
    crc_cellA MIDc 28%nat.
    rewrite gb_after_50, dgo_DRet in KQ.
    revive_all MUL WML AOK. enter_retF HRETC DP.
  Qed.
End R.
End ACeilS1.
