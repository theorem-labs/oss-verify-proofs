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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU8 DecTacF8 DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU8 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF8 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFB DecTacFB DecTacFRB B0F_decV B0F_decRet B0F_decCutsM B0F_decCuts8 B0F_gb_E B0F_gb_F.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCutsM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCuts8 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_gb_E OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_gb_F.
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
  Hypothesis HRETOK : B0F_RET_OK A Q.
  Hypothesis HRET : B0F_RET A Q.
  Variable F : nat.
  (* [comment removed for export] *)
  Hypothesis HSYM : B0F_cut_SYM A Q F.
  (* [comment removed for export] *)
  Hypothesis HL8A : forall F', (F' < F)%nat -> B0F_cut_L8A A Q F'.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  (* [comment removed for export] *)
  Ltac ml_facts ML :=
    let ALK := ident:(ALK) in let GRP := ident:(GRP) in let BLKF := ident:(BLKF) in let CUR := ident:(CUR) in pose proof (dinv_ML_alpha _ _ ML) as [AL15 EOB15];
    pose proof (dinv_ML_gmn _ _ ML) as GMN15;
    let X := fresh in
    pose proof ML as X; cps_destruct X as (ALK & GRP & TABS & MTF & BLKF & CUR);
    pose proof (proj1 BLKF) as NB15; unfold grp_okF in GRP; unfold cur_okF in CUR; unfold alpha_ok in ALK.

  (* [comment removed for export] *)
  Lemma B0F_U8A_loop : B0F_cut_L8A A Q F.
  Proof.
    unfold B0F_cut_L8A. intros until w752. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    assert (S4 : (S mod 4 = 0)%Z) by (pose proof (proj1 ANS) as S8; clear - S8; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    pose proof DI as DI'. cps_destruct DI' as (ML & GD & _). ml_facts ML.
    pose proof (dpureF_n _ _ _ _ _ _ DP) as BN.
    pose proof (grp_decF_zn _ _ _ _ _ _ GD) as ZN. pose proof (grp_decF_zvec d (sv_alphaSize L) (sv_gSel L) (sv_gMinlen L) ltac:(lia) _ _ GD) as ZV.
    open_dmemF DM. b0img. kq_intro.
    unfold r_of in DR. dr_open. hide_all_but_atF [S; S + 45436; S + 51628; S + 57820; a_P A; a_P A + 344]%Z.
    pose proof (munch_refl [(S, S + 68); (a_P A + 344, a_P A + 760)]%Z m) as MUL. pose proof (wmono_refl b0segs m) as WML.
    (* [comment removed for export] *)
    brun; if_cases K20; zify_cond_z K20.
    2: { (* [comment removed for export] *)
      astep.
      rewrite (K_L8_ret F 1) in KQ by lia. revive_all MUL WML AOK.
      kq_fold. enter_cutF (HRET _ _ _ _ JK_) DP; [ ret_nb | apply dpost14_ne; dmodel_cbn; unfold BZ_X_OUTPUT; lia ]. }
    pose proof (grp_decF_limit d (sv_alphaSize L) (sv_gSel L) (sv_gMinlen L) ltac:(lia) _ _ GD ltac:(lia)) as LR.
    (* [comment removed for export] *)
    brun_to 0xb1a08%Z.
    lazymatch goal with H : u32arr _ ?mm (S + 45436)%Z (zw32 ?a ?n) |- _ =>
      pose proof (zw32_read b0segs mm (S + 45436) a n (258 * sv_gSel L + sv_zn L)%Z _ H ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
    astep. clear RD. try rewrite (sx32_lit (zget (d_limit d) _)) by lia.
    (* [comment removed for export] *)
    brun; if_cases KB; zify_cond_z KB.
    - (* [comment removed for export] *)
      cps_destruct (grp_decF_break d (sv_alphaSize L) (sv_gSel L) (sv_gMinlen L) ltac:(lia) _ _ GD ltac:(lia) ltac:(lia)) as (BR1 & BR2 & BR3 & BR4).
      brun_to 0xb1ca0%Z.
      lazymatch goal with H : u32arr _ ?mm (S + 51628)%Z (zw32 ?a ?n) |- _ =>
        pose proof (zw32_read b0segs mm (S + 51628) a n (258 * sv_gSel L + sv_zn L)%Z _ H ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
      astep. clear RD. try rewrite (sx32_lit (zget (d_base d) _)) by lia.
      (* [comment removed for export] *)
      astep. astep. rewrite DecAuxH.Z_to_bv_sub_land64. astep. try rewrite swrap32_sub_land64F.
      try rewrite swrap32_sub_mod64. try rewrite (swrap32_small (sv_zvec L - _)) by lia.
      brun; if_cases KD; [ clear KD | zify_cond KD; exfalso; lia ].
      (* [comment removed for export] *)
      brun_to 0xb23f0%Z.
      lazymatch goal with H : u32arr _ ?mm (S + 57820)%Z (zw32 ?a ?n) |- _ =>
        pose proof (zw32_read b0segs mm (S + 57820) a n (258 * sv_gSel L + (sv_zvec L - zget (d_base d) (258 * sv_gSel L + sv_zn L)))%Z _ H
                      ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
      astep. clear RD.
      change (zget (d_perm d) (258 * sv_gSel L + (sv_zvec L - zget (d_base d) (258 * sv_gSel L + sv_zn L))))%Z with (mvl_sym L d) in *.
      (* [comment removed for export] *)
      rewrite (K_L8_sym1 F L d s) in KQ by lia.
      revive_all MUL WML AOK. enter_sameF HSYM DP.
      apply dinv_SYM_intro; [exact ML | exact BR3].
    - (* [comment removed for export] *)
      brun_to 0xb1a20%Z.
      rewrite (K_L8_more F 1 L d s) in KQ by lia. change (1 + 36)%Z with 37%Z in KQ.
      gbF_call (B0F_gb_b175c A AOK ASH Q HRETOK _ _ _ _ JK_) MUL WML AOK DP FU.
      gbF_nextA [S; a_P A; a_P A + 344]%Z [(S, S + 68); (a_P A + 344, a_P A + 760)]%Z.
      arun_lwbuf. arun_gbv 1%Z zj.
      (* [comment removed for export] *)
      brun_to 0xb1aa4%Z.
      (* [comment removed for export] *)
      try rewrite (Z.lor_comm zj (sv_zvec L * 2)). try rewrite (Z.lor_comm zj (2 * sv_zvec L)).
      first [ rewrite (lor2_bitF (sv_zvec L) zj) by lia | rewrite (lor2_bitF' (sv_zvec L) zj) by lia
            | rewrite (lor_shiftl1_bit (sv_zvec L) zj) by lia | idtac "NOTE: zvec form not normalised" ].
      brun_to 0xb19a4%Z.
      destruct (dinv_L8_step 1 L d zj DI ltac:(lia) ltac:(lia) ltac:(lia)) as [DI' EQ].
      rewrite (K_L8_again37 _ zj _ _ _ (2 * sv_zvec L + zj)%Z) in KQ by (cbn [sv_zvec sv_set_zn]; destruct L; exact EQ).
      revive_all MUL WML AOK. enter_nextF HL8A DP.
      apply (dinv_L8_keep 1 _ d); [exact DI' | apply dkeep_gb; lia].
  Qed.
End R.

Section H.
  Variable A : act14.
  Hypothesis AOK : act_ok BIHI0 A.
  Hypothesis ASH : act_sh DI_B0 A.
  Variable Q : dres -> machine_state -> Prop.
  Hypothesis HRETOK : B0F_RET_OK A Q.
  Variable F : nat.
  Hypothesis HL8A : forall F', (F' < F)%nat -> B0F_cut_L8A A Q F'.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  (* [comment removed for export] *)
  Lemma B0F_U8A_head : B0F_cut_HMTF1 A Q F.
  Proof.
    unfold B0F_cut_HMTF1. intros until w752. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    pose proof DI as DI'. destruct DI' as [ML ZN].
    pose proof (dinv_ML_alpha _ _ ML) as [AL15 EOB15]. pose proof (dinv_ML_gmn _ _ ML) as GMN15.
    pose proof ML as X; cps_destruct X as (ALK & GRP & TABS & MTF & BLKF & CUR). pose proof (proj1 BLKF) as NB15.
    unfold grp_okF in GRP; unfold alpha_ok in ALK. pose proof (dpureF_n _ _ _ _ _ _ DP) as BN.
    open_dmemF DM. b0img.
    kq_intro. rewrite K_HMTF1_drun in KQ.
    (* [comment removed for export] *)
    gbF_call (B0F_gb_b12ec A AOK ASH Q HRETOK _ _ _ _ JK_) MU WM AOK DP FU.
    1: (dmodel_cbn; unset_Z; lia). (* [comment removed for export] *)
    gbF_nextA [S; a_P A; a_P A + 344]%Z [(S, S + 68); (a_P A + 344, a_P A + 760)]%Z.
    (* [comment removed for export] *)
    arun_lwbuf. brun_to 0xb17f0%Z.
    rewrite (zn_maskF (sv_zn L)) by lia.
    gbv 11%Z (sv_zn L) zvec.
    (* [comment removed for export] *)
    match goal with R : (0 <= zvec < _)%Z |- _ => clear R end.
    pose proof (gbval_range bb bl (sv_zn L) ltac:(lia)) as Rzvec. fold zvec in Rzvec.
    (* [comment removed for export] *)
    brun_to 0xb19a4%Z.
    rewrite K_L8_enter36 in KQ.
    revive_all MUL WML AOK. enter_nextF HL8A DP.
    apply (dinv_L8_keep 1 _ d); [| apply dkeep_gb; lia].
    apply dinv_L8_init; [exact ML | exact ZN | rewrite <- ZN; unset_Z; lia | intros; exfalso; lia].
  Qed.
End H.

(* [comment removed for export] *)
Lemma B0F_dec_U8A_L8A : forall A, act_ok BIHI0 A -> act_sh DI_B0 A -> forall Q, B0F_RET_OK A Q -> B0F_RET A Q -> forall F,
  (forall F', (F' <= F)%nat -> B0F_cut_SYM A Q F') -> forall F', (F' <= F)%nat -> B0F_cut_L8A A Q F'.
Proof.
  intros A AOK ASH Q HOK HP2 F HS. induction F as [|F IH]; intros F' HF'.
  - assert (F' = 0%nat) as -> by lia. apply (B0F_U8A_loop A AOK ASH Q HOK HP2 0%nat); [apply HS; lia | intros; exfalso; lia].
  - apply (B0F_U8A_loop A AOK ASH Q HOK HP2 F'); [apply HS; lia |]. intros F'' HF''. apply IH; [| lia]. intros G HG. apply HS. lia.
Qed.

Lemma B0F_dec_U8A : forall A, act_ok BIHI0 A -> act_sh DI_B0 A -> forall Q, B0F_RET_OK A Q -> B0F_RET A Q -> forall F,
  (forall F', (F' < F)%nat -> B0F_cut_SYM A Q F') -> B0F_cut_HMTF1 A Q F.
Proof.
  intros A AOK ASH Q HOK HP2 F HS. apply (B0F_U8A_head A AOK ASH Q HOK F). intros F' HF'. destruct F as [|F0]; [exfalso; lia|].
  apply (B0F_dec_U8A_L8A A AOK ASH Q HOK HP2 F0); [| lia]. intros G HG. apply HS. lia.
Qed.
End ACeilS1.

