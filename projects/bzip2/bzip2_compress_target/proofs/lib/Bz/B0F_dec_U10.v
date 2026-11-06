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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzLemmasMtf BzDU5 BzDUM BzDU10 DecAuxL DecTacF3 DecAux10F DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU10 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAuxL OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux10F OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFB DecTacFB DecTacFRB B0F_decV B0F_decRet DecTacSB B0F_decCutsM B0F_decCutsL B0F_dec_U10J B0F_dec_U10F B0F_dec_U10G.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacSB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCutsM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCutsL OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_dec_U10J OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_dec_U10F OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_dec_U10G.
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
  Hypothesis HC : B0F_cut_HMTFC A Q F.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).
  Notation TT := (b_tt (a_cx A)).
  Notation L16 := (b_ll16 (a_cx A)).

  Ltac prep DM MU DP :=
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN; pose proof rnums_words_length as RNL; lin_natZ RNL;
    unfold_W14 MU; open_ash ASH AOK;
    lazymatch goal with H : sanchor (b_s _) (a_shs _) |- _ => pose proof (proj2 H : saddr (b_s (a_cx A)) (a_shs A)) as ANS0 end;
    open_dmemF DM; b0img.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac mtfa_rdA MA i :=
    let RD := fresh "RD" in let BR := fresh "BR" in
    lazymatch goal with AR : u8arr _ ?mm (b_s (a_cx A) + 3724)%Z (zb8 ?a _) |- _ =>
      pose proof (MA i ltac:(lia)) as BR;
      pose proof (zb8_read1 b0segs mm _ a 4096 i _ AR ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD;
      repeat rewrite zget_zset_other in RD by lia;
      astep; clear RD; rewrite zxb_lit8 by lia end.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac mtfb_rdA ROW i :=
    let RD := fresh "RD" in let E := fresh "ROWv" in
    lazymatch goal with AR : u32arr _ ?mm (b_s (a_cx A) + 7820)%Z (zw32 ?a _) |- _ =>
      pose proof (ROW i ltac:(lia)) as E;
      pose proof (zw32_read b0segs mm _ a 16 i _ AR ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD;
      astep; clear RD end.
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma B0F_U10_HLIT : B0F_cut_HLIT A Q F.
  Proof.
    unfold B0F_cut_HLIT. intros until w752. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    destruct DI as [ML NSR]. pose proof (ml_nomtfF_of_ML L d ML) as MR. cps_pose (mbrow_of_ML L d ML) as (ROW & MTI & MA).
    u10_facts MR DP. cps_pose ML as (_ & _ & _ & _ & (NBR & _ & _) & _).
    assert (NS256 : (sv_nextSym L <= 256)%Z) by (cps_pose ML as (((_ & NIU & _) & _) & (_ & _ & _ & EOBE & _) & _); lia).
    pose proof (mtf_inv_bounds (mtfb d) MTI 0 ltac:(lia)) as PPR. unfold mtfb in PPR.
    prep DM MU DP. lazymatch goal with D : drest_at _ _ _ _ |- _ => unfold r_of in D end. dr_open.
    hide_all_but_atF [S + 3724; S + 7820; a_P A; a_P A + 344]%Z.
    pose proof (munch_refl [(a_P A + 344, a_P A + 760)]%Z m) as MUL. pose proof (wmono_refl b0segs m) as WML.   (* [comment removed for export] *)
    kq_intro.
    (* [comment removed for export] *)
    match goal with FR : rw_cells b0segs _ (a_P _ + 344)%Z _ |- _ =>
      let C := fresh "FR8" in pose proof FR as C; hide C; DecTacM.slot_split FR 0%nat;
      astep; clear FR; unfold hidden in C; rename C into FR end.
    try rewrite (sx32_lit (sv_nblockMAX L)) by lia.
    brun; if_cases Knb; zify_cond_z Knb.
    2: { (* [comment removed for export] *)
      astep.
      rewrite (K_HLIT_ret F L d s) in KQ by lia.
      revive_all MUL WML AOK. kq_fold.
      enter_cutF (HRET _ _ _ _ JK_) DP; [ ret_nb | apply dpost14_ne; dmodel_cbn; exact NST ]. }
    (* [comment removed for export] *)
    brun; if_cases Kg; zify_cond_z Kg. all: swap 1 2.
    { (* [comment removed for export] *)
      assert (LNO : (1 <= (sv_nextSym L - 1) / 16 <= 15)%Z) by (pose proof (Z.div_mod (sv_nextSym L - 1) 16 ltac:(lia)); pose proof (Z.mod_pos_bound (sv_nextSym L - 1) 16 ltac:(lia)); lia).
      pose proof (mtf_inv_bounds (mtfb d) MTI ((sv_nextSym L - 1) / 16) ltac:(lia)) as RL. unfold mtfb in RL.
      rewrite (K_HLIT_gen F L d s) in KQ by lia.
      revive_all MUL WML AOK.
      pose proof (B0F_U10_LGH A AOK ASH Q F HC (mtfb d)) as NX. unfold B0F_cut_LGH in NX.
      kq_fold. enter_cutF (NX L _ s JK_) DP.
      all: try assumption. all: try lia. }
    rewrite (K_HLIT_fast F L d s) in KQ by lia.
    (* [comment removed for export] *)
    brun_to 0xb2840%Z. mtfb_rdA ROW 0%Z.
    brun_to 0xb287c%Z. mtfa_rdA MA (zget (d_mtfbase d) 0 + (sv_nextSym L - 1))%Z.
    (* [comment removed for export] *)
    brun; if_cases K4; zify_cond_z K4.
    - (* [comment removed for export] *)
      brun_to 0xb2a0c%Z.
      rewrite (K_LFA_exit F L d s) in KQ by lia.
      revive_all MUL WML AOK.
      pose proof (B0F_U10_LFB_all A AOK ASH Q F HC (mtfb d) (zget (d_mtfbase d) 0) (zget (d_mtfa d) (zget (d_mtfbase d) 0 + (sv_nextSym L - 1))) (sv_nextSym L - 1) ltac:(lia)) as NX.
      unfold B0F_cut_LFB in NX.
      kq_fold. enter_cutF (NX L _ s JK_) DP.
      all: try assumption. all: try reflexivity. all: try (apply MA; lia). all: try lia.
    - (* [comment removed for export] *)
      brun_to 0xb2894%Z.
      revive_all MUL WML AOK.
      pose proof (B0F_U10_LFA_all A AOK ASH Q F HC (mtfb d) (zget (d_mtfbase d) 0) (zget (d_mtfa d) (zget (d_mtfbase d) 0 + (sv_nextSym L - 1))) (sv_nextSym L) ltac:(lia)) as NX.
      unfold B0F_cut_LFA in NX.
      kq_fold. enter_cutF (NX L _ s JK_) DP.
      all: try assumption. all: try reflexivity. all: try (apply MA; lia). all: try lia.
  Qed.
End R.

Lemma B0F_dec_U10 : forall A, act_ok BIHI0 A -> act_sh DI_B0 A -> forall Q, B0F_RET A Q -> forall F, B0F_cut_HMTFC A Q F -> B0F_cut_HLIT A Q F.
Proof. intros A AOK ASH Q HP2 F HC. exact (B0F_U10_HLIT A AOK ASH Q HP2 F HC). Qed.
End ACeilS1.

