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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFA DecTacFA DecTacFRA A0F_decV A0F_decRet A0F_decCutsA A0F_gb_B A0F_gb_C.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCutsA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_gb_B OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_gb_C.
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

(* [comment removed for export] *)
Ltac lor8_norm_in H :=
  repeat match type of H with
  | context [Z.lor (Z.shiftl ?a 8) ?b] => rewrite (lor_shiftl8 a b) in H by (dmodel_cbn; unset_Z; lia)
  end.
(* [comment removed for export] *)
Ltac or_lin := first [ rewrite lor_mul256_byte by (unset_Z; lia) | rewrite Z.lor_0_l | rewrite Z.lor_0_r | idtac ].

Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok AIHI0 A.
  Hypothesis ASH : act_sh DI_A0 A.
  Variable Q : dres -> machine_state -> Prop.
  Hypothesis HRETOK : A0F_RET_OK A Q.
  Hypothesis HRETP2 : A0F_RETP2 A Q.
  Variable F : nat.
  Hypothesis HMAP : forall F', (F' < F)%nat -> A0F_cut_HMAP A Q F'.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  Ltac next := gbF_nextA [S; S + 3152; a_P A; a_P A + 496]%Z [(S, S + 68); (S + 3152, S + 3196)]%Z.
  (* [comment removed for export] *)
  Ltac nextH := gbF_nextA [S; S + 3152; a_P A; a_P A + 496]%Z [(S, S + 68); (S + 3152, S + 3196); (a_P A + 496, a_P A + 728)]%Z.
  (* [comment removed for export] *)
  Ltac bcrc_tail uc EQ nexthead :=
    arun_lwbuf; arun_gbv 8%Z uc; arun_to nexthead;
    match goal with H : rw_cells _ _ (b_s _ + 3152)%Z _ |- _ => crc_cellA H 24%nat end;
    match goal with H : kq _ _ |- _ => rewrite EQ, dgo_DGo in H end; kq_norm.

  Lemma A0F_dec_U2B : A0F_cut_HBCRC A Q F.
  Proof.
    unfold A0F_cut_HBCRC. intros until w720. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    unfold dinv_HBCRC, nb_ok in DI. destruct DI as [NB SB0].
    assert (SB : (0 <= d_sbcrc d < 4294967296)%Z) by exact SB0. clear SB0.
    open_dmemF DM. a0img.
    (* [comment removed for export] *)
    gbF_call (A0F_gb_9f5bc A AOK ASH Q HRETOK _ _ _ _ JK_) MU WM AOK DP FU. next.
    bcrc_tail u1 gb_after_20 0x9f978%Z.
    gbF_call (A0F_gb_9f65c A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU. next.
    bcrc_tail u2 gb_after_21 0x9fa18%Z.
    gbF_call (A0F_gb_9f6fc A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU. next.
    bcrc_tail u3 gb_after_22 0x9fab8%Z.
    gbF_call (A0F_gb_9f79c A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU. next.
    bcrc_tail u4 gb_after_23 0x9fb54%Z.
    (* [comment removed for export] *)
    gbF_call (A0F_gb_9f838 A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU. next.
    arun_lwbuf. arun_gbv 1%Z rb. arun_to 0x9fbe4%Z.
    sb_step. arun_to 0x9fc00%Z.
    rewrite gb_after_24, dgo_DGo in KQ.
    (* [comment removed for export] *)
    gbF_call (A0F_gb_9f8e4 A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU. next.
    lor8_norm_in HD.
    arun_lwbuf. arun_gbv 8%Z v1. arun_to 0x9fc98%Z. or_lin. arun_to 0x9fc9c%Z.
    rewrite gb_after_25, dgo_DGo in KQ.
    (* [comment removed for export] *)
    gbF_call (A0F_gb_9f980 A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU. next.
    lor8_norm_in HD.
    arun_lwbuf. arun_gbv 8%Z v2. arun_to 0x9fd34%Z. or_lin. arun_to 0x9fd38%Z.
    rewrite gb_after_26, dgo_DGo in KQ.
    (* [comment removed for export] *)
    gbF_call (A0F_gb_9fa1c A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU. nextH.
    lor8_norm_in HD.
    arun_lwbuf. arun_gbv 8%Z v3. arun_to 0x9fdd4%Z. or_lin.
    arun.
    rewrite edge_27 in KQ. kq_norm. lor8_norm_in KQ.
    rewrite if_falseP in KQ by blia.
    if_true_z.
    arun; if_cases KO; zify_cond_z KO.
    2: { rewrite if_trueP in KQ by blia.
         astep. revive_all MUL WML AOK. enter_retF HRETP2 DP. }
    rewrite if_falseP in KQ by blia.
    arun_to 0xa3dc8%Z.
    revive_all MUL WML AOK. enter_nextF HMAP DP.
    unfold dinv_HMAP, nb_ok, op_ok, hdr_ok; dmodel_cbn.
    repeat match goal with |- _ /\ _ => split end; try (intros; exfalso; lia); unset_Z; first [lia | unfold u32; lia].
  Qed.
End R.
End ACeilS1.
