(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts BzContracts0 DecCut DecTac DecTac2 DecAux S0_dec_U13.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU8 DecCutF DecTacF DecTacFR DecTacFR2 S0F_decRet S0F_decCutsM S0F_decCuts8.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU8 DecCutF DecTacF DecTacFR DecTacFR2 DecTacF8 S0F_decRet S0F_decCutsM S0F_decCuts8. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0F_gb_O. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0F_gb_K.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require LinSplit DecFast DecFastT.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NatLit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzImg0TacFR BzImg0Tac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NormFast RelLiaA SasFastF RelLia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module S0F_dec_U8A.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDefs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzInv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzContracts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzContracts0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_dec_U13.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU8 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF8 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decCutsM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decCuts8 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_gb_O.S0F_gb_N OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_gb_K.
 Unset Lia Cache.
Import ListNotations. Local Open Scope bv_scope.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.LinSplit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecFast OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecFastT.
Local Ltac DecCut.revive H MUL WML AOK ::= DecFast.revive_cached H MUL WML AOK.
Local Ltac DecCut.dpure_from DP ::= DecFast.dpure_from_fast DP.
Local Ltac DecCut.open_dmem DM ::= DecFast.open_dmem_red DM.
Local Ltac DecTac.gb_next keep Wloc IB ::= DecFastT.gb_next_red keep Wloc IB.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.NatLit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzImg0TacFR OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzImg0Tac.
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
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.
Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.
  Variable F : nat.
  (* [comment removed for export] *)
  Hypothesis HSYM : S0F_cut_SYM A F.
  (* [comment removed for export] *)
  Hypothesis HL8A : forall F', (F' < F)%nat -> S0F_cut_L8A A F'.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  Ltac prep DM MU :=
    unfold W14, D14, DSTATE_SIZE in MU; cbn [app blk_ivls b_s b_strm] in MU; open_dmemF DM; s2img.

  (* [comment removed for export] *)
  Ltac ml_facts ML :=
    let ALK := ident:(ALK) in let GRP := ident:(GRP) in let BLKF := ident:(BLKF) in let CUR := ident:(CUR) in pose proof (dinv_ML_alpha _ _ ML) as [AL15 EOB15];
    pose proof (dinv_ML_gmn _ _ ML) as GMN15;
    let X := fresh in
    pose proof ML as X; cps_destruct X as (ALK & GRP & TABS & MTF & BLKF & CUR);
    pose proof (proj1 BLKF) as NB15; unfold grp_okF in GRP; unfold cur_okF in CUR; unfold alpha_ok in ALK.

  (* [comment removed for export] *)
  Lemma S0F_U8A_loop : S0F_cut_L8A A F.
  Proof.
    unfold S0F_cut_L8A. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    pose proof DI as DI'. cps_destruct DI' as (ML & GD & _). ml_facts ML.
    pose proof (dpureF_n _ _ _ _ _ _ DP) as BN.
    pose proof (grp_decF_zn _ _ _ _ _ _ GD) as ZN. pose proof (grp_decF_zvec d (sv_alphaSize L) (sv_gSel L) (sv_gMinlen L) ltac:(lia) _ _ GD) as ZV.
    prep DM MU. kq_intro.
    (* [comment removed for export] *)
    wstepl. wstepl.
    wstepl; if_cases K20; zify_cond_z K20.
    { (* [comment removed for export] *)
      rewrite (K_L8_ret F 1) in KQ by lia. kq_fold. enter_cutF (S0F_dec_ret A AOK _ _ _ _ JK_) DP; [ ret_nb | apply dpost14_ne; dmodel_cbn; unfold BZ_X_OUTPUT; lia ]. }
    pose proof (grp_decF_limit d (sv_alphaSize L) (sv_gSel L) (sv_gMinlen L) ltac:(lia) _ _ GD ltac:(lia)) as LR.
    (* [comment removed for export] *)
    wstepl. wstepl.
    unfold r_of in DR. dr_open. hide_all_but_at [S; S + 45436; S + 51628; S + 57820; usp + -320]%Z.
    pose proof (munch_refl [(S, S + 68); (usp + -320, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    lazymatch goal with H : u32arr _ ?mm (S + 45436)%Z (zw32 ?a ?n) |- _ =>
      pose proof (zw32_read s0segs mm (S + 45436) a n (258 * sv_gSel L + sv_zn L)%Z _ H ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
    wstepl. clear RD. try rewrite (sx32_lit (zget (d_limit d) _)) by lia.
    (* [comment removed for export] *)
    wstepl; if_cases KB; zify_cond_z KB.
    - (* [comment removed for export] *)
      cps_destruct (grp_decF_break d (sv_alphaSize L) (sv_gSel L) (sv_gMinlen L) ltac:(lia) _ _ GD ltac:(lia) ltac:(lia)) as (BR1 & BR2 & BR3 & BR4).
      wstepl. wstepl.
      lazymatch goal with H : u32arr _ ?mm (S + 51628)%Z (zw32 ?a ?n) |- _ =>
        pose proof (zw32_read s0segs mm (S + 51628) a n (258 * sv_gSel L + sv_zn L)%Z _ H ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
      wstepl. clear RD. try rewrite (sx32_lit (zget (d_base d) _)) by lia.
      (* [comment removed for export] *)
      wstepl. try rewrite swrap32_sub_land64F. try rewrite swrap32_sub_mod64. try rewrite (swrap32_small (sv_zvec L - _)) by lia.
      wstepl. wstepl; if_cases KD; [ zify_cond KD; exfalso; lia | clear KD ].
      (* [comment removed for export] *)
      wstepl. wstepl. wstepl.
      lazymatch goal with H : u32arr _ ?mm (S + 57820)%Z (zw32 ?a ?n) |- _ =>
        pose proof (zw32_read s0segs mm (S + 57820) a n (258 * sv_gSel L + (sv_zvec L - zget (d_base d) (258 * sv_gSel L + sv_zn L)))%Z _ H
                      ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
      wstepl. clear RD.
      change (zget (d_perm d) (258 * sv_gSel L + (sv_zvec L - zget (d_base d) (258 * sv_gSel L + sv_zn L))))%Z with (mvl_sym L d) in *.
      (* [comment removed for export] *)
      rewrite (K_L8_sym1 F L d s) in KQ by lia.
      revive_all MUL WML AOK. enter_sameF HSYM DP.
      apply dinv_SYM_intro; [exact ML | exact BR3].
    - (* [comment removed for export] *)
      wstepl. wstepl.
      rewrite (K_L8_more F 1 L d s) in KQ by lia. change (1 + 36)%Z with 37%Z in KQ.
      gbF_call (S0F_gb_1d33c A AOK (QF A) (S0F_dec_ret_ok A AOK) _ _ _ _ JK_) MUL WML AOK DP FU.
      gbF_next [S; usp + -320]%Z [(S, S + 68); (usp + -320, usp)]%Z.
      (* [comment removed for export] *)
      wstepl. wstepl. wstepl. gbv 12%Z 1%Z zj.
      wstepl. wstepl. wstepl.
      destruct (dinv_L8_step 1 L d zj DI ltac:(lia) ltac:(lia) ltac:(lia)) as [DI' EQ].
      try rewrite (Z.lor_comm zj (sv_zvec L * 2)). try rewrite (Z.lor_comm zj (2 * sv_zvec L)).
      first [ rewrite (lor2_bitF (sv_zvec L) zj) by lia | rewrite (lor2_bitF' (sv_zvec L) zj) by lia
            | rewrite (lor_shiftl1_bit (sv_zvec L) zj) by lia | idtac "NOTE: zvec form not normalised" ].
      (* [comment removed for export] *)
      rewrite (K_L8_again37 _ zj _ _ _ (2 * sv_zvec L + zj)%Z) in KQ by (cbn [sv_zvec sv_set_zn]; destruct L; exact EQ).
      revive_all MUL WML AOK. enter_nextF HL8A DP.
      apply (dinv_L8_keep 1 _ d); [exact DI' | apply dkeep_gb; lia].
  Qed.
End R.

Section H.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.
  Variable F : nat.
  Hypothesis HL8A : forall F', (F' < F)%nat -> S0F_cut_L8A A F'.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  (* [comment removed for export] *)
  Lemma S0F_U8A_head : S0F_cut_HMTF1 A F.
  Proof.
    unfold S0F_cut_HMTF1. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    pose proof DI as DI'. destruct DI' as [ML ZN].
    pose proof (dinv_ML_alpha _ _ ML) as [AL15 EOB15]. pose proof (dinv_ML_gmn _ _ ML) as GMN15.
    pose proof ML as X; cps_destruct X as (ALK & GRP & TABS & MTF & BLKF & CUR). pose proof (proj1 BLKF) as NB15.
    unfold grp_okF in GRP; unfold alpha_ok in ALK. pose proof (dpureF_n _ _ _ _ _ _ DP) as BN.
    unfold W14, D14, DSTATE_SIZE in MU. cbn [app blk_ivls b_s b_strm] in MU. open_dmemF DM. s2img.
    kq_intro. rewrite K_HMTF1_drun in KQ.
    (* [comment removed for export] *)
    gbF_call (S0F_gb_1de10 A AOK (QF A) (S0F_dec_ret_ok A AOK) _ _ _ _ JK_) MU WM AOK DP FU.
    1: (dmodel_cbn; unset_Z; lia). (* [comment removed for export] *)
    gbF_next [S]%Z [(S, S + 68)]%Z.
    (* [comment removed for export] *)
    wstepl. wstepl. wstepl. wstepl. wstepl. wstepl.
    rewrite (zn_maskF (sv_zn L)) by lia.
    gbv 31%Z (sv_zn L) zvec.
    (* [comment removed for export] *)
    match goal with R : (0 <= zvec < _)%Z |- _ => clear R end.
    pose proof (gbval_range bb bl (sv_zn L) ltac:(lia)) as Rzvec. fold zvec in Rzvec.
    (* [comment removed for export] *)
    wstepl. wstepl.
    rewrite K_L8_enter36 in KQ.
    revive_all MUL WML AOK. enter_nextF HL8A DP.
    apply (dinv_L8_keep 1 _ d); [| apply dkeep_gb; lia].
    apply dinv_L8_init; [exact ML | exact ZN | rewrite <- ZN; unset_Z; lia | intros; exfalso; lia].
  Qed.
End H.

(* [comment removed for export] *)
Lemma S0F_dec_U8A_L8A : forall A, act_ok 320 A -> forall F,
  (forall F', (F' <= F)%nat -> S0F_cut_SYM A F') -> forall F', (F' <= F)%nat -> S0F_cut_L8A A F'.
Proof.
  intros A AOK F HS. induction F as [|F IH]; intros F' HF'.
  - assert (F' = 0%nat) as -> by lia. apply (S0F_U8A_loop A AOK 0%nat); [apply HS; lia | intros; exfalso; lia].
  - apply (S0F_U8A_loop A AOK F'); [apply HS; lia |]. intros F'' HF''. apply IH; [| lia]. intros G HG. apply HS. lia.
Qed.

Lemma S0F_dec_U8A : forall A, act_ok 320 A -> forall F,
  (forall F', (F' < F)%nat -> S0F_cut_SYM A F') -> S0F_cut_HMTF1 A F.
Proof.
  intros A AOK F HS. apply (S0F_U8A_head A AOK F). intros F' HF'. destruct F as [|F0]; [exfalso; lia|].
  apply (S0F_dec_U8A_L8A A AOK F0); [| lia]. intros G HG. apply HS. lia.
Qed.

End ACeilS1.
End S0F_dec_U8A.


From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0F_gb_O.
Module S0F_dec_U8B.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDefs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzInv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzContracts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzContracts0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_dec_U13.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU8 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF8 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decCutsM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decCuts8 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_gb_O OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_gb_K.
 Unset Lia Cache.
Import ListNotations. Local Open Scope bv_scope.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.LinSplit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecFast OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecFastT.
Local Ltac DecCut.revive H MUL WML AOK ::= DecFast.revive_cached H MUL WML AOK.
Local Ltac DecCut.dpure_from DP ::= DecFast.dpure_from_fast DP.
Local Ltac DecCut.open_dmem DM ::= DecFast.open_dmem_red DM.
Local Ltac DecTac.gb_next keep Wloc IB ::= DecFastT.gb_next_red keep Wloc IB.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.NatLit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzImg0TacFR OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzImg0Tac.
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
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Ltac ml_facts ML :=
  let ALK := ident:(ALK) in let GRP := ident:(GRP) in let BLKF := ident:(BLKF) in let CUR := ident:(CUR) in pose proof (dinv_ML_alpha _ _ ML) as [AL15 EOB15];
  pose proof (dinv_ML_gmn _ _ ML) as GMN15;
  let X := fresh in
  pose proof ML as X; cps_destruct X as (ALK & GRP & TABS & MTF & BLKF & CUR);
  pose proof (proj1 BLKF) as NB15; unfold grp_okF in GRP; unfold cur_okF in CUR; unfold alpha_ok in ALK.

(* [comment removed for export] *)
Ltac retF_var A AOK DP :=
  kq_fold; enter_cutF (S0F_dec_ret A AOK _ _ _ _ JK_) DP; [ ret_nb | apply dpost14_ne; dmodel_cbn; unfold BZ_X_OUTPUT; lia ].

Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.
  Variable F : nat.
  Hypothesis HRUN : S0F_cut_HRUN A F.
  Hypothesis HEND : S0F_cut_HRUNEND A F.
  Hypothesis HL8D : forall F', (F' < F)%nat -> S0F_cut_L8D A F'.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  Ltac prep DM MU :=
    unfold W14, D14, DSTATE_SIZE in MU; cbn [app blk_ivls b_s b_strm] in MU; open_dmemF DM; s2img.

  (* [comment removed for export] *)
  Lemma S0F_U8B_loop : S0F_cut_L8D A F.
  Proof.
    unfold S0F_cut_L8D. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    pose proof DI as DI'. cps_destruct DI' as (ML & GD & W3). destruct (W3 eq_refl) as [RUNOK NMAX]. ml_facts ML.
    pose proof (dpureF_n _ _ _ _ _ _ DP) as BN. pose proof RUNOK as RUNOK'. unfold run_okF in RUNOK'.
    pose proof (grp_decF_zn _ _ _ _ _ _ GD) as ZN. pose proof (grp_decF_zvec d (sv_alphaSize L) (sv_gSel L) (sv_gMinlen L) ltac:(lia) _ _ GD) as ZV.
    prep DM MU. kq_intro.
    (* [comment removed for export] *)
    wstepl. wstepl.
    wstepl; if_cases K20; zify_cond_z K20.
    2:{ (* [comment removed for export] *) wstepl. rewrite (K_L8_ret F 3) in KQ by lia. retF_var A AOK DP. }
    pose proof (grp_decF_limit d (sv_alphaSize L) (sv_gSel L) (sv_gMinlen L) ltac:(lia) _ _ GD ltac:(lia)) as LR.
    (* [comment removed for export] *)
    wstepl. wstepl.
    unfold r_of in DR. dr_open. hide_all_but_at [S; S + 45436; S + 51628; S + 57820; usp + -320]%Z.
    pose proof (munch_refl [(S, S + 68); (usp + -320, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    lazymatch goal with H : u32arr _ ?mm (S + 45436)%Z (zw32 ?a ?n) |- _ =>
      pose proof (zw32_read s0segs mm (S + 45436) a n (258 * sv_gSel L + sv_zn L)%Z _ H ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
    wstepl. clear RD. try rewrite (sx32_lit (zget (d_limit d) _)) by lia.
    (* [comment removed for export] *)
    wstepl; if_cases KB; zify_cond_z KB.
    - (* [comment removed for export] *)
      cps_destruct (grp_decF_break d (sv_alphaSize L) (sv_gSel L) (sv_gMinlen L) ltac:(lia) _ _ GD ltac:(lia) ltac:(lia)) as (BR1 & BR2 & BR3 & BR4).
      wstepl. wstepl.
      lazymatch goal with H : u32arr _ ?mm (S + 51628)%Z (zw32 ?a ?n) |- _ =>
        pose proof (zw32_read s0segs mm (S + 51628) a n (258 * sv_gSel L + sv_zn L)%Z _ H ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
      wstepl. clear RD. try rewrite (sx32_lit (zget (d_base d) _)) by lia.
      (* [comment removed for export] *)
      wstepl. try rewrite swrap32_sub_land64F. try rewrite swrap32_sub_mod64. try rewrite (swrap32_small (sv_zvec L - _)) by lia.
      wstepl. wstepl; if_cases KD; [ clear KD | zify_cond KD; exfalso; lia ].
      (* [comment removed for export] *)
      wstepl. wstepl. wstepl.
      lazymatch goal with H : u32arr _ ?mm (S + 57820)%Z (zw32 ?a ?n) |- _ =>
        pose proof (zw32_read s0segs mm (S + 57820) a n (258 * sv_gSel L + (sv_zvec L - zget (d_base d) (258 * sv_gSel L + sv_zn L)))%Z _ H
                      ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
      wstepl. clear RD.
      change (zget (d_perm d) (258 * sv_gSel L + (sv_zvec L - zget (d_base d) (258 * sv_gSel L + sv_zn L))))%Z with (mvl_sym L d) in *.
      (* [comment removed for export] *)
      wstepl.
      wstepl; if_cases K2; zify_cond_z K2.
      + (* [comment removed for export] *)
        rewrite (K_L8_runend F L d s) in KQ by lia.
        revive_all MUL WML AOK. enter_sameF HEND DP.
        apply dinv_HRUNEND_intro; [exact DI | lia].
      + (* [comment removed for export] *)
        wstepl. wstepl.
        rewrite (K_L8_run F L d s) in KQ by lia.
        revive_all MUL WML AOK. enter_sameF HRUN DP.
        apply dinv_HRUN_intro; [exact DI | lia | lia].
    - (* [comment removed for export] *)
      wstepl. wstepl.
      rewrite (K_L8_more F 3 L d s) in KQ by lia. change (3 + 36)%Z with 39%Z in KQ.
      gbF_call (S0F_gb_1d3fc A AOK (QF A) (S0F_dec_ret_ok A AOK) _ _ _ _ JK_) MUL WML AOK DP FU.
      gbF_next [S; usp + -320]%Z [(S, S + 68); (usp + -320, usp)]%Z.
      (* [comment removed for export] *)
      wstepl. wstepl. wstepl. gbv 12%Z 1%Z zj.
      wstepl. wstepl. wstepl.
      destruct (dinv_L8_step 3 L d zj DI ltac:(lia) ltac:(lia) ltac:(lia)) as [DI' EQ].
      try rewrite (Z.lor_comm zj (sv_zvec L * 2)). try rewrite (Z.lor_comm zj (2 * sv_zvec L)).
      first [ rewrite (lor2_bitF (sv_zvec L) zj) by lia | rewrite (lor2_bitF' (sv_zvec L) zj) by lia
            | rewrite (lor_shiftl1_bit (sv_zvec L) zj) by lia | idtac "NOTE: zvec form not normalised" ].
      wstepl.
      rewrite (K_L8_again39 _ zj _ _ _ (2 * sv_zvec L + zj)%Z) in KQ by (cbn [sv_zvec sv_set_zn]; destruct L; exact EQ).
      revive_all MUL WML AOK. enter_nextF HL8D DP.
      apply (dinv_L8_keep 3 _ d); [exact DI' | apply dkeep_gb; lia].
  Qed.
End R.

Section G.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.
  Variable F : nat.
  Hypothesis HL8D : forall F', (F' < F)%nat -> S0F_cut_L8D A F'.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  (* [comment removed for export] *)
  Lemma S0F_U8B_gb : S0F_cut_L8G A F.
  Proof.
    unfold S0F_cut_L8G. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    pose proof DI as DI'. destruct DI' as [[ML [RUNOK NMAX]] ZN]. ml_facts ML.
    pose proof (dpureF_n _ _ _ _ _ _ DP) as BN.
    unfold W14, D14, DSTATE_SIZE in MU. cbn [app blk_ivls b_s b_strm] in MU. open_dmemF DM. s2img.
    kq_intro. rewrite K_L8G_drun in KQ.
    (* [comment removed for export] *)
    gbF_call (S0F_gb_1eb6c A AOK (QF A) (S0F_dec_ret_ok A AOK) _ _ _ _ JK_) MU WM AOK DP FU.
    1: (dmodel_cbn; unset_Z; lia).
    gbF_next [S]%Z [(S, S + 68)]%Z.
    (* [comment removed for export] *)
    wstepl. wstepl. wstepl. wstepl. wstepl. wstepl.
    rewrite (zn_maskF (sv_zn L)) by lia.
    gbv 31%Z (sv_zn L) zvec.
    match goal with R : (0 <= zvec < _)%Z |- _ => clear R end.
    pose proof (gbval_range bb bl (sv_zn L) ltac:(lia)) as Rzvec. fold zvec in Rzvec.
    (* [comment removed for export] *)
    wstepl.
    rewrite K_L8_enter38 in KQ.
    revive_all MUL WML AOK. enter_nextF HL8D DP.
    apply (dinv_L8_keep 3 _ d); [| apply dkeep_gb; lia].
    apply dinv_L8G_L8; [exact DI | rewrite <- ZN; unset_Z; lia].
  Qed.
End G.

Section B.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.
  Variable F : nat.
  Hypothesis HL8G : S0F_cut_L8G A F.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  Ltac prep DM MU :=
    unfold W14, D14, DSTATE_SIZE in MU; cbn [app blk_ivls b_s b_strm] in MU; open_dmemF DM; s2img.

  (* [comment removed for export] *)
  Lemma S0F_U8B_head : S0F_cut_HMTFB A F.
  Proof.
    unfold S0F_cut_HMTFB. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    pose proof DI as DI'. destruct DI' as [ML [RUNOK NMAX]]. ml_facts ML.
    pose proof (dpureF_n _ _ _ _ _ _ DP) as BN.
    cps_destruct GRP as (NG2 & NSC2 & SOK & EOBq & NBMq). cps_destruct CUR as (GNO & GPOS & GSEL & GSR & GMQ).
    prep DM MU. kq_intro.
    unfold r_of in DR. dr_open. hide_all_but_at [S + 7884; S + 64012; usp + -320]%Z.
    pose proof (munch_refl [(usp + -320, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    (* [comment removed for export] *)
    wstepl; if_cases K0; zify_cond_z K0.
    - (* [comment removed for export] *)
      wstepl. wstepl. wstepl.
      wstepl; if_cases KS; zify_cond_z KS.
      { (* [comment removed for export] *)
        wstepl. wstepl.
        rewrite (K_HMTFB_ret F L d s) in KQ by lia.
        revive_all MUL WML AOK. kq_fold.
        enter_cutF (S0F_dec_ret A AOK _ _ _ _ JK_) DP; [ ret_nb | apply dpost14_ne; dmodel_cbn; unfold BZ_X_OUTPUT; lia ]. }
      (* [comment removed for export] *)
      wstepl. wstepl. wstepl. wstepl. wstepl. wstepl. wstepl.
      (* [comment removed for export] *)
      pose proof (SOK (sv_groupNo L + 1)%Z ltac:(lia)) as Gg.
      lazymatch goal with H : u8arr _ ?mm (S + 7884)%Z (zb8 ?a ?n) |- _ =>
        pose proof (zb8_read1 s0segs mm (S + 7884) a n (sv_groupNo L + 1)%Z _ H ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
      wstepl. clear RD. rewrite zxb_lit8 by lia.
      set (g := zget (d_sel d) (sv_groupNo L + 1)) in *.
      (* [comment removed for export] *)
      wstepl. wstepl. wstepl. wstepl. wstepl. wstepl. wstepl. wstepl.
      replace (g * 1032)%Z with (1032 * g)%Z by lia.
      (* [comment removed for export] *)
      destruct (TABS g Gg) as [gmn GT].
      assert (MINL : zget (d_minLens d) g = gmn) by (cps_destruct GT as (len0 & lim0 & base0 & perm0 & mx & _ & _ & _ & E); exact E).
      assert (GMN : (1 <= gmn <= 20)%Z) by (cps_destruct GT as (len0 & lim0 & base0 & perm0 & mx & R1 & _); lia).
      lazymatch goal with H : u32arr _ ?mm (S + 64012)%Z (zw32 ?a ?n) |- _ =>
        pose proof (zw32_read s0segs mm (S + 64012) a n g _ H ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
      wstepl. clear RD. rewrite MINL. try (unfold sx32; rewrite (unsigned_lit gmn) by lia; rewrite swrap32_small by lia).
      (* [comment removed for export] *)
      wstepl. replace (S + 1032 * g + 45436)%Z with (S + 45436 + 1032 * g)%Z by lia.
      wstepl. replace (S + 1032 * g + 57820)%Z with (S + 57820 + 1032 * g)%Z by lia.
      wstepl. wstepl. wstepl.
      wstepl. replace (S + 1032 * g + 51628)%Z with (S + 51628 + 1032 * g)%Z by lia.
      wstepl. wstepl.
      (* [comment removed for export] *)
      wstepl. wstepl.
      rewrite (K_HMTFB_go F L d s) in KQ by lia. rewrite <- K_L8G_drun in KQ.
      revive_all MUL WML AOK. enter_sameF HL8G DP.
      all: lazymatch goal with
           | |- dinv_L8G _ _ => apply dinv_L8G_intro; [exact DI | lia]
           | |- _ => rewrite (mvs_L_zero L d) by lia; dmodel_cbn; unset_Z; rewrite ?MINL;
                     lazymatch goal with
                     | |- rw_cells _ _ _ _ =>
                         match goal with H : rw_cells _ _ (bv_unsigned (a_sp A) + -320)%Z _ |- _ => exact_cells H end
                     | |- @eq Z _ _ => lia
                     | |- _ => first [ reflexivity | f_equal; lia ]
                     end
           end.
    - (* [comment removed for export] *)
      wstepl. wstepl. wstepl. wstepl.
      rewrite (K_HMTFB_go F L d s) in KQ by (left; destruct (Z.eqb_spec (sv_groupPos L) 0); [lia | reflexivity]).
      rewrite <- K_L8G_drun in KQ.
      revive_all MUL WML AOK. enter_sameF HL8G DP.
      all: lazymatch goal with
           | |- dinv_L8G _ _ => apply dinv_L8G_intro; [exact DI | lia]
           | |- _ => rewrite (mvs_L_pos L d) by lia; dmodel_cbn; unset_Z;
                     lazymatch goal with
                     | |- rw_cells _ _ _ _ =>
                         match goal with H : rw_cells _ _ (bv_unsigned (a_sp A) + -320)%Z _ |- _ => exact_cells H end
                     | |- @eq Z _ _ => lia
                     | |- _ => first [ reflexivity | f_equal; lia ]
                     end
           end.
  Qed.
End B.

(* [comment removed for export] *)
Lemma S0F_dec_U8B_L8D : forall A, act_ok 320 A -> forall F,
  (forall F', (F' <= F)%nat -> S0F_cut_HRUN A F') -> (forall F', (F' <= F)%nat -> S0F_cut_HRUNEND A F') ->
  forall F', (F' <= F)%nat -> S0F_cut_L8D A F'.
Proof.
  intros A AOK F HR HE. induction F as [|F IH]; intros F' HF'.
  - assert (F' = 0%nat) as -> by lia. apply (S0F_U8B_loop A AOK 0%nat); [apply HR; lia | apply HE; lia | intros; exfalso; lia].
  - apply (S0F_U8B_loop A AOK F'); [apply HR; lia | apply HE; lia |]. intros F'' HF''.
    apply IH; [| | lia]; intros G HG; [apply HR | apply HE]; lia.
Qed.

Lemma S0F_dec_U8B : forall A, act_ok 320 A -> forall F,
  (forall F', (F' < F)%nat -> S0F_cut_HRUN A F') -> (forall F', (F' < F)%nat -> S0F_cut_HRUNEND A F') ->
  S0F_cut_HMTFB A F.
Proof.
  intros A AOK F HR HE. apply (S0F_U8B_head A AOK F). apply (S0F_U8B_gb A AOK F). intros F' HF'.
  destruct F as [|F0]; [exfalso; lia|].
  apply (S0F_dec_U8B_L8D A AOK F0); [| | lia]; intros G HG; [apply HR | apply HE]; lia.
Qed.

End ACeilS1.
End S0F_dec_U8B.


From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0F_gb_O. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0F_gb_K.
Module S0F_dec_U8C.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDefs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzInv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzContracts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzContracts0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_dec_U13.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU8 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF8 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decCutsM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decCuts8 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_gb_O.S0F_gb_P OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_gb_K.S0F_gb_L.
 Unset Lia Cache.
Import ListNotations. Local Open Scope bv_scope.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.LinSplit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecFast OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecFastT.
Local Ltac DecCut.revive H MUL WML AOK ::= DecFast.revive_cached H MUL WML AOK.
Local Ltac DecCut.dpure_from DP ::= DecFast.dpure_from_fast DP.
Local Ltac DecCut.open_dmem DM ::= DecFast.open_dmem_red DM.
Local Ltac DecTac.gb_next keep Wloc IB ::= DecFastT.gb_next_red keep Wloc IB.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.NatLit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzImg0TacFR OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzImg0Tac.
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
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Ltac ml_facts ML :=
  let ALK := ident:(ALK) in let GRP := ident:(GRP) in let BLKF := ident:(BLKF) in let CUR := ident:(CUR) in pose proof (dinv_ML_alpha _ _ ML) as [AL15 EOB15];
  pose proof (dinv_ML_gmn _ _ ML) as GMN15;
  let X := fresh in
  pose proof ML as X; cps_destruct X as (ALK & GRP & TABS & MTF & BLKF & CUR);
  pose proof (proj1 BLKF) as NB15; unfold grp_okF in GRP; unfold cur_okF in CUR; unfold alpha_ok in ALK.

(* [comment removed for export] *)
Ltac retF_var A AOK DP :=
  kq_fold; enter_cutF (S0F_dec_ret A AOK _ _ _ _ JK_) DP; [ ret_nb | apply dpost14_ne; dmodel_cbn; unfold BZ_X_OUTPUT; lia ].

Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.
  Variable F : nat.
  Hypothesis HSYM : S0F_cut_SYM A F.
  Hypothesis HL8D : forall F', (F' < F)%nat -> S0F_cut_L8CD A F'.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  Ltac prep DM MU :=
    unfold W14, D14, DSTATE_SIZE in MU; cbn [app blk_ivls b_s b_strm] in MU; open_dmemF DM; s2img.

  (* [comment removed for export] *)
  Lemma S0F_U8C_loop : S0F_cut_L8CD A F.
  Proof.
    unfold S0F_cut_L8CD. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    pose proof DI as DI'. cps_destruct DI' as (ML & GD & _). ml_facts ML.
    pose proof (dpureF_n _ _ _ _ _ _ DP) as BN.
    pose proof (grp_decF_zn _ _ _ _ _ _ GD) as ZN. pose proof (grp_decF_zvec d (sv_alphaSize L) (sv_gSel L) (sv_gMinlen L) ltac:(lia) _ _ GD) as ZV.
    prep DM MU. kq_intro.
    (* [comment removed for export] *)
    wstepl. wstepl.
    wstepl; if_cases K20; zify_cond_z K20.
    { (* [comment removed for export] *) rewrite (K_L8_ret F 5) in KQ by lia. retF_var A AOK DP. }
    pose proof (grp_decF_limit d (sv_alphaSize L) (sv_gSel L) (sv_gMinlen L) ltac:(lia) _ _ GD ltac:(lia)) as LR.
    (* [comment removed for export] *)
    wstepl. wstepl.
    unfold r_of in DR. dr_open. hide_all_but_at [S; S + 45436; S + 51628; S + 57820; usp + -320]%Z.
    pose proof (munch_refl [(S, S + 68); (usp + -320, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    lazymatch goal with H : u32arr _ ?mm (S + 45436)%Z (zw32 ?a ?n) |- _ =>
      pose proof (zw32_read s0segs mm (S + 45436) a n (258 * sv_gSel L + sv_zn L)%Z _ H ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
    wstepl. clear RD. try rewrite (sx32_lit (zget (d_limit d) _)) by lia.
    (* [comment removed for export] *)
    wstepl; if_cases KB; zify_cond_z KB.
    - (* [comment removed for export] *)
      cps_destruct (grp_decF_break d (sv_alphaSize L) (sv_gSel L) (sv_gMinlen L) ltac:(lia) _ _ GD ltac:(lia) ltac:(lia)) as (BR1 & BR2 & BR3 & BR4).
      wstepl. wstepl.
      lazymatch goal with H : u32arr _ ?mm (S + 51628)%Z (zw32 ?a ?n) |- _ =>
        pose proof (zw32_read s0segs mm (S + 51628) a n (258 * sv_gSel L + sv_zn L)%Z _ H ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
      wstepl. clear RD. try rewrite (sx32_lit (zget (d_base d) _)) by lia.
      (* [comment removed for export] *)
      wstepl. try rewrite swrap32_sub_land64F. try rewrite swrap32_sub_mod64. try rewrite (swrap32_small (sv_zvec L - _)) by lia.
      wstepl. wstepl; if_cases KD; [ zify_cond KD; exfalso; lia | clear KD ].
      (* [comment removed for export] *)
      wstepl. wstepl. wstepl.
      lazymatch goal with H : u32arr _ ?mm (S + 57820)%Z (zw32 ?a ?n) |- _ =>
        pose proof (zw32_read s0segs mm (S + 57820) a n (258 * sv_gSel L + (sv_zvec L - zget (d_base d) (258 * sv_gSel L + sv_zn L)))%Z _ H
                      ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
      wstepl. clear RD.
      change (zget (d_perm d) (258 * sv_gSel L + (sv_zvec L - zget (d_base d) (258 * sv_gSel L + sv_zn L))))%Z with (mvl_sym L d) in *.
      (* [comment removed for export] *)
      rewrite (K_L8_sym5 F L d s) in KQ by lia.
      revive_all MUL WML AOK. enter_sameF HSYM DP.
      apply dinv_SYM_intro; [exact ML | exact BR3].
    - (* [comment removed for export] *)
      wstepl. wstepl.
      rewrite (K_L8_more F 5 L d s) in KQ by lia. change (5 + 36)%Z with 41%Z in KQ.
      gbF_call (S0F_gb_1d49c A AOK (QF A) (S0F_dec_ret_ok A AOK) _ _ _ _ JK_) MUL WML AOK DP FU.
      gbF_next [S; usp + -320]%Z [(S, S + 68); (usp + -320, usp)]%Z.
      (* [comment removed for export] *)
      wstepl. wstepl. wstepl. gbv 12%Z 1%Z zj.
      wstepl. wstepl. wstepl.
      destruct (dinv_L8_step 5 L d zj DI ltac:(lia) ltac:(lia) ltac:(lia)) as [DI' EQ].
      try rewrite (Z.lor_comm zj (sv_zvec L * 2)). try rewrite (Z.lor_comm zj (2 * sv_zvec L)).
      first [ rewrite (lor2_bitF (sv_zvec L) zj) by lia | rewrite (lor2_bitF' (sv_zvec L) zj) by lia
            | rewrite (lor_shiftl1_bit (sv_zvec L) zj) by lia | idtac "NOTE: zvec form not normalised" ].
      wstepl.
      rewrite (K_L8_again41 _ zj _ _ _ (2 * sv_zvec L + zj)%Z) in KQ by (cbn [sv_zvec sv_set_zn]; destruct L; exact EQ).
      revive_all MUL WML AOK. enter_nextF HL8D DP.
      apply (dinv_L8_keep 5 _ d); [exact DI' | apply dkeep_gb; lia].
  Qed.
End R.

Section G.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.
  Variable F : nat.
  Hypothesis HL8D : forall F', (F' < F)%nat -> S0F_cut_L8CD A F'.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  (* [comment removed for export] *)
  Lemma S0F_U8C_gb : S0F_cut_L8CG A F.
  Proof.
    unfold S0F_cut_L8CG. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    pose proof DI as DI'. destruct DI' as [ML ZN]. ml_facts ML.
    pose proof (dpureF_n _ _ _ _ _ _ DP) as BN.
    unfold W14, D14, DSTATE_SIZE in MU. cbn [app blk_ivls b_s b_strm] in MU. open_dmemF DM. s2img.
    kq_intro. rewrite K_L8CG_drun in KQ.
    (* [comment removed for export] *)
    gbF_call (S0F_gb_1e3fc A AOK (QF A) (S0F_dec_ret_ok A AOK) _ _ _ _ JK_) MU WM AOK DP FU.
    1: (dmodel_cbn; unset_Z; lia).
    gbF_next [S]%Z [(S, S + 68)]%Z.
    (* [comment removed for export] *)
    wstepl. wstepl. wstepl. wstepl. wstepl. wstepl.
    rewrite (zn_maskF (sv_zn L)) by lia.
    gbv 31%Z (sv_zn L) zvec.
    match goal with R : (0 <= zvec < _)%Z |- _ => clear R end.
    pose proof (gbval_range bb bl (sv_zn L) ltac:(lia)) as Rzvec. fold zvec in Rzvec.
    (* [comment removed for export] *)
    wstepl.
    rewrite K_L8_enter40 in KQ.
    revive_all MUL WML AOK. enter_nextF HL8D DP.
    apply (dinv_L8_keep 5 _ d); [| apply dkeep_gb; lia].
    apply dinv_L8CG_L8; [exact DI | rewrite <- ZN; unset_Z; lia].
  Qed.
End G.

Section C.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.
  Variable F : nat.
  Hypothesis HL8G : S0F_cut_L8CG A F.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  Ltac prep DM MU :=
    unfold W14, D14, DSTATE_SIZE in MU; cbn [app blk_ivls b_s b_strm] in MU; open_dmemF DM; s2img.

  (* [comment removed for export] *)
  Lemma S0F_U8C_head : S0F_cut_HMTFC A F.
  Proof.
    unfold S0F_cut_HMTFC. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    pose proof DI as DI'. pose proof (DI' : dinv_ML L d) as ML. ml_facts ML.
    pose proof (dpureF_n _ _ _ _ _ _ DP) as BN.
    cps_destruct GRP as (NG2 & NSC2 & SOK & EOBq & NBMq). cps_destruct CUR as (GNO & GPOS & GSEL & GSR & GMQ).
    prep DM MU. kq_intro.
    unfold r_of in DR. dr_open. hide_all_but_at [S + 7884; S + 64012; usp + -320]%Z.
    pose proof (munch_refl [(usp + -320, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    (* [comment removed for export] *)
    wstepl; if_cases K0; zify_cond_z K0.
    - (* [comment removed for export] *)
      wstepl. wstepl. wstepl.
      wstepl; if_cases KS; zify_cond_z KS.
      { (* [comment removed for export] *)
        wstepl. wstepl.
        rewrite (K_HMTFC_ret F L d s) in KQ by lia.
        revive_all MUL WML AOK. kq_fold.
        enter_cutF (S0F_dec_ret A AOK _ _ _ _ JK_) DP; [ ret_nb | apply dpost14_ne; dmodel_cbn; unfold BZ_X_OUTPUT; lia ]. }
      (* [comment removed for export] *)
      wstepl. wstepl. wstepl. wstepl. wstepl. wstepl. wstepl.
      (* [comment removed for export] *)
      pose proof (SOK (sv_groupNo L + 1)%Z ltac:(lia)) as Gg.
      lazymatch goal with H : u8arr _ ?mm (S + 7884)%Z (zb8 ?a ?n) |- _ =>
        pose proof (zb8_read1 s0segs mm (S + 7884) a n (sv_groupNo L + 1)%Z _ H ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
      wstepl. clear RD. rewrite zxb_lit8 by lia.
      set (g := zget (d_sel d) (sv_groupNo L + 1)) in *.
      (* [comment removed for export] *)
      wstepl. wstepl. wstepl. wstepl. wstepl. wstepl. wstepl. wstepl.
      replace (g * 1032)%Z with (1032 * g)%Z by lia.
      (* [comment removed for export] *)
      destruct (TABS g Gg) as [gmn GT].
      assert (MINL : zget (d_minLens d) g = gmn) by (cps_destruct GT as (len0 & lim0 & base0 & perm0 & mx & _ & _ & _ & E); exact E).
      assert (GMN : (1 <= gmn <= 20)%Z) by (cps_destruct GT as (len0 & lim0 & base0 & perm0 & mx & R1 & _); lia).
      lazymatch goal with H : u32arr _ ?mm (S + 64012)%Z (zw32 ?a ?n) |- _ =>
        pose proof (zw32_read s0segs mm (S + 64012) a n g _ H ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
      wstepl. clear RD. rewrite MINL. try (unfold sx32; rewrite (unsigned_lit gmn) by lia; rewrite swrap32_small by lia).
      (* [comment removed for export] *)
      wstepl. replace (S + 1032 * g + 45436)%Z with (S + 45436 + 1032 * g)%Z by lia.
      wstepl. replace (S + 1032 * g + 57820)%Z with (S + 57820 + 1032 * g)%Z by lia.
      wstepl. wstepl. wstepl.
      wstepl. replace (S + 1032 * g + 51628)%Z with (S + 51628 + 1032 * g)%Z by lia.
      wstepl. wstepl.
      (* [comment removed for export] *)
      wstepl. wstepl.
      rewrite (K_HMTFC_go F L d s) in KQ by lia. rewrite <- K_L8CG_drun in KQ.
      revive_all MUL WML AOK. enter_sameF HL8G DP.
      all: lazymatch goal with
           | |- dinv_L8CG _ _ => apply dinv_L8CG_intro; [exact DI | lia]
           | |- _ => rewrite (mvs_L_zero L d) by lia; dmodel_cbn; unset_Z; rewrite ?MINL;
                     lazymatch goal with
                     | |- rw_cells _ _ _ _ =>
                         match goal with H : rw_cells _ _ (bv_unsigned (a_sp A) + -320)%Z _ |- _ => exact_cells H end
                     | |- @eq Z _ _ => lia
                     | |- _ => first [ reflexivity | f_equal; lia ]
                     end
           end.
    - (* [comment removed for export] *)
      wstepl. wstepl. wstepl. wstepl.
      rewrite (K_HMTFC_go F L d s) in KQ by (left; destruct (Z.eqb_spec (sv_groupPos L) 0); [lia | reflexivity]).
      rewrite <- K_L8CG_drun in KQ.
      revive_all MUL WML AOK. enter_sameF HL8G DP.
      all: lazymatch goal with
           | |- dinv_L8CG _ _ => apply dinv_L8CG_intro; [exact DI | lia]
           | |- _ => rewrite (mvs_L_pos L d) by lia; dmodel_cbn; unset_Z;
                     lazymatch goal with
                     | |- rw_cells _ _ _ _ =>
                         match goal with H : rw_cells _ _ (bv_unsigned (a_sp A) + -320)%Z _ |- _ => exact_cells H end
                     | |- @eq Z _ _ => lia
                     | |- _ => first [ reflexivity | f_equal; lia ]
                     end
           end.
  Qed.
End C.

(* [comment removed for export] *)
Lemma S0F_dec_U8C_L8CD : forall A, act_ok 320 A -> forall F,
  (forall F', (F' <= F)%nat -> S0F_cut_SYM A F') -> forall F', (F' <= F)%nat -> S0F_cut_L8CD A F'.
Proof.
  intros A AOK F HS. induction F as [|F IH]; intros F' HF'.
  - assert (F' = 0%nat) as -> by lia. apply (S0F_U8C_loop A AOK 0%nat); [apply HS; lia | intros; exfalso; lia].
  - apply (S0F_U8C_loop A AOK F'); [apply HS; lia |]. intros F'' HF''. apply IH; [| lia]. intros G HG. apply HS. lia.
Qed.

Lemma S0F_dec_U8C : forall A, act_ok 320 A -> forall F,
  (forall F', (F' < F)%nat -> S0F_cut_SYM A F') -> S0F_cut_HMTFC A F.
Proof.
  intros A AOK F HS. apply (S0F_U8C_head A AOK F). apply (S0F_U8C_gb A AOK F). intros F' HF'.
  destruct F as [|F0]; [exfalso; lia|].
  apply (S0F_dec_U8C_L8CD A AOK F0); [| lia]. intros G HG. apply HS. lia.
Qed.

End ACeilS1.
End S0F_dec_U8C.

Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU8 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decCutsM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_decCuts8 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_dec_U8S.S0F_dec_U8A OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_dec_U8S.S0F_dec_U8B OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0F_dec_U8S.S0F_dec_U8C.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit DecFast DecFastT.
Local Ltac DecCut.revive H MUL WML AOK ::= DecFast.revive_cached H MUL WML AOK.
Local Ltac DecCut.dpure_from DP ::= DecFast.dpure_from_fast DP.
Local Ltac DecCut.open_dmem DM ::= DecFast.open_dmem_red DM.
Local Ltac DecTac.gb_next keep Wloc IB ::= DecFastT.gb_next_red keep Wloc IB.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzImg0TacFR BzImg0Tac.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require SasFastF.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac simpl_arr_sizes ::= SasFastF.sas6F_all.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Lemma dinv_HRUN_start : forall L d, dinv_SYM L d -> (sv_nextSym L <= 1)%Z -> dinv_HRUN (sv_set_N (sv_set_es L (-1)) 1) d.
Proof.
  intros L d [ML NS] H. unfold dinv_HRUN. split; [| Lsplit L; split; [lia | apply run_okF_init]].
  apply (dinv_ML_keep L _ d d ML); [destruct L; unfold Lkeep; cbn; repeat split; reflexivity|].
  destruct d; unfold dkeep; cbn; repeat split; try reflexivity.
  destruct ML as [AL _]. unfold alpha_ok in AL. cbn in AL. lia.
Qed.
Lemma dinv_HLIT_start : forall L d, dinv_SYM L d -> sv_nextSym L <> sv_EOB L -> (1 < sv_nextSym L)%Z -> dinv_HLIT L d.
Proof.
  intros L d [ML NS] H1 H2. pose proof (dinv_ML_alpha L d ML) as [AL EOB]. unfold dinv_HLIT. split; [exact ML| lia].
Qed.
Lemma dinv_HEOB_start : forall L d, dinv_SYM L d -> sv_nextSym L = sv_EOB L -> dinv_HEOB L d.
Proof. intros L d [ML NS] H. split; [exact ML | exact H]. Qed.

Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.
  Variable F : nat.
  Hypothesis HEOB : S0F_cut_HEOB A F.
  Hypothesis HLIT : S0F_cut_HLIT A F.
  Hypothesis HRUN : S0F_cut_HRUN A F.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  Lemma S0F_dec_U8S' : S0F_cut_SYM A F.
  Proof.
    unfold S0F_cut_SYM. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    pose proof DI as DI'. destruct DI' as [ML NS]. pose proof (dinv_ML_alpha _ _ ML) as [AL15 EOB15].
    pose proof ML as X; cps_destruct X as (ALK & GRP & TABS & MTF & BLKF & CUR). pose proof (proj1 BLKF) as NB15.
    unfold grp_okF in GRP; unfold alpha_ok in ALK. pose proof (dpureF_n _ _ _ _ _ _ DP) as BN.
    unfold W14, D14, DSTATE_SIZE in MU; cbn [app blk_ivls b_s b_strm] in MU; open_dmemF DM; s2img.
    kq_intro.
    hide_all_but_at [usp + -320]%Z.
    pose proof (munch_refl [(usp + -320, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    (* [comment removed for export] *)
    wstepl.
    wstepl; if_cases KE; zify_cond_z KE.
    { (* [comment removed for export] *)
      rewrite (K_SYM_eob F L d s) in KQ by lia.
      revive_all MUL WML AOK. enter_sameF HEOB DP. apply dinv_HEOB_start; [exact DI | lia]. }
    (* [comment removed for export] *)
    wstepl.
    wstepl; if_cases KL; zify_cond_z KL.
    { rewrite (K_SYM_lit F L d s) in KQ by lia.
      revive_all MUL WML AOK. enter_sameF HLIT DP. apply dinv_HLIT_start; [exact DI | lia | lia]. }
    (* [comment removed for export] *)
    wstepl. wstepl.
    rewrite (K_SYM_run F L d s) in KQ by lia.
    revive_all MUL WML AOK. enter_sameF HRUN DP. apply dinv_HRUN_start; [exact DI | lia].
  Qed.
End R.

Lemma S0F_dec_U8S : forall A, act_ok 320 A -> forall F,
  S0F_cut_HEOB A F -> S0F_cut_HLIT A F -> S0F_cut_HRUN A F -> S0F_cut_SYM A F.
Proof. intros A AOK F HE HL HR. exact (S0F_dec_U8S' A AOK F HE HL HR). Qed.

(* [comment removed for export] *)
Lemma S0F_dec_U8 : forall A, act_ok 320 A -> forall F,
  (forall F', (F' < F)%nat -> S0F_cut_SYM A F') ->
  (forall F', (F' < F)%nat -> S0F_cut_HRUN A F') ->
  (forall F', (F' < F)%nat -> S0F_cut_HRUNEND A F') ->
  S0F_cut_HEOB A F ->
  (S0F_cut_HMTFC A F -> S0F_cut_HLIT A F) ->
  (S0F_cut_HMTFB A F -> S0F_cut_HRUN A F) ->
  (S0F_cut_SYM A F -> S0F_cut_HRUNEND A F) ->
  S0F_cut_HMTFC A F /\ S0F_cut_HLIT A F /\ S0F_cut_HMTFB A F /\ S0F_cut_HRUN A F /\
  S0F_cut_SYM A F /\ S0F_cut_HRUNEND A F /\ S0F_cut_HMTF1 A F.
Proof.
  intros A AOK F HS HR HN HE U10 U9a U9b.
  pose proof (S0F_dec_U8C A AOK F HS) as C. pose proof (U10 C) as L.
  pose proof (S0F_dec_U8B A AOK F HR HN) as B. pose proof (U9a B) as R.
  pose proof (S0F_dec_U8S A AOK F HE L R) as Y. pose proof (U9b Y) as N.
  pose proof (S0F_dec_U8A A AOK F HS) as M1.
  repeat split; assumption.
Qed.

End ACeilS1.
