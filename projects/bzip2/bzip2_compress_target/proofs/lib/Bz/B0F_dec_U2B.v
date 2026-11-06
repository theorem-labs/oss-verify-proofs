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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts DecCut DecTac DecAux.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDU2 DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFB DecTacFB DecTacFRB B0F_decV B0F_decRet B0F_decCutsA B0F_gb_B B0F_gb_C.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCutsA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_gb_B OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_gb_C.
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
  Hypothesis AOK : act_ok BIHI0 A.
  Hypothesis ASH : act_sh DI_B0 A.
  Variable Q : dres -> machine_state -> Prop.
  Hypothesis HRETOK : B0F_RET_OK A Q.
  Hypothesis HRETD : B0F_RET_DATA A Q.
  Variable F : nat.
  Hypothesis HMAP : forall F', (F' < F)%nat -> B0F_cut_HMAP A Q F'.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  Ltac next := gbF_nextA [S; S + 3152; a_P A; a_P A + 344]%Z [(S, S + 68); (S + 3152, S + 3196)]%Z.
  (* [comment removed for export] *)
  Ltac nextH := gbF_nextA [S; S + 3152; a_P A; a_P A + 344]%Z [(S, S + 68); (S + 3152, S + 3196); (a_P A + 344, a_P A + 760)]%Z.
  (* [comment removed for export] *)
  Ltac bcrc_tail uc EQ nexthead :=
    arun_lwbuf; arun_gbv 8%Z uc; brun_to nexthead;
    match goal with H : rw_cells _ _ (b_s _ + 3152)%Z _ |- _ => crc_cellA H 24%nat end;
    match goal with H : kq _ _ |- _ => rewrite EQ, dgo_DGo in H end; kq_norm.

  Lemma B0F_dec_U2B : B0F_cut_HBCRC A Q F.
  Proof.
    unfold B0F_cut_HBCRC. intros until w752. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    unfold dinv_HBCRC, nb_ok in DI. destruct DI as [NB SB0].
    assert (SB : (0 <= d_sbcrc d < 4294967296)%Z) by exact SB0. clear SB0.
    open_dmemF DM. b0img.
    (* [comment removed for export] *)
    gbF_call (B0F_gb_aa8f0 A AOK ASH Q HRETOK _ _ _ _ JK_) MU WM AOK DP FU. next.
    bcrc_tail u1 gb_after_20 0xaac60%Z.
    gbF_call (B0F_gb_aa99c A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU. next.
    bcrc_tail u2 gb_after_21 0xaad0c%Z.
    gbF_call (B0F_gb_aaa48 A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU. next.
    bcrc_tail u3 gb_after_22 0xaadb8%Z.
    gbF_call (B0F_gb_aaaf4 A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU. next.
    bcrc_tail u4 gb_after_23 0xaae60%Z.
    (* [comment removed for export] *)
    gbF_call (B0F_gb_aab9c A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU. next.
    arun_lwbuf. arun_gbv 1%Z rb. brun_to 700156%Z.
    sb_step. brun_to 0xaaf18%Z.
    rewrite gb_after_24, dgo_DGo in KQ.
    (* [comment removed for export] *)
    gbF_call (B0F_gb_aac54 A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU. next.
    lor8_norm_in HD.
    arun_lwbuf. arun_gbv 8%Z v1. brun_to 0xaafd4%Z. or_lin. brun_to 0xaafd8%Z.
    rewrite gb_after_25, dgo_DGo in KQ.
    (* [comment removed for export] *)
    gbF_call (B0F_gb_aad14 A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU. next.
    lor8_norm_in HD.
    arun_lwbuf. arun_gbv 8%Z v2. brun_to 0xab094%Z. or_lin. brun_to 0xab098%Z.
    rewrite gb_after_26, dgo_DGo in KQ.
    (* [comment removed for export] *)
    gbF_call (B0F_gb_aadd4 A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU. nextH.
    lor8_norm_in HD.
    (* [comment removed for export] *)
    arun_lwbuf. arun_gbv 8%Z v3. brun_to 0xab15c%Z. or_lin.
    brun_to 0xab18c%Z. wstep. rewrite lor_100000_10 by lia.
    rewrite edge_27 in KQ. kq_norm. lor8_norm_in KQ.
    rewrite if_falseP in KQ by blia.
    brun; if_cases KO; zify_cond_z KO.
    2: { rewrite if_trueP in KQ by blia.
         astep. revive_all MUL WML AOK. enter_retF HRETD DP. }
    rewrite if_falseP in KQ by blia.
    brun_to 0xaf7c4%Z.
    revive_all MUL WML AOK. enter_nextF HMAP DP.
    unfold dinv_HMAP, nb_ok, op_ok, hdr_ok; dmodel_cbn.
    repeat match goal with |- _ /\ _ => split end; try (intros; exfalso; lia); unset_Z; first [lia | unfold u32; lia].
  Qed.
End R.
End ACeilS1.

