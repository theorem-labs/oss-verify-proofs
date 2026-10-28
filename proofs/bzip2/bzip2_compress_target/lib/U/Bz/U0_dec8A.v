(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts BzContracts0 DecCut DecTac DecTac2 DecAux S0_dec_U13.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU8. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF DecTacFR DecTacFR2 DecTacF8 S0F_decRet S0F_decCutsM S0F_decCuts8. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_gb_O. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_gb_K.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require LinSplit. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecFast DecFastT.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzImg0TacFR BzImg0Tac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require NormFast. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLiaA. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require SasFastF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module S0F_dec_U8A.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAux OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_dec_U13.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU8 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacFR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacFR2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF8 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCutsM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCuts8 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_gb_O.S0F_gb_N OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_gb_K.
 Unset Lia Cache.
Import ListNotations. Local Open Scope bv_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.LinSplit OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecFast OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecFastT.
Local Ltac DecCut.revive H MUL WML AOK ::= DecFast.revive_cached H MUL WML AOK.
Local Ltac DecCut.dpure_from DP ::= DecFast.dpure_from_fast DP.
Local Ltac DecCut.open_dmem DM ::= DecFast.open_dmem_red DM.
Local Ltac DecTac.gb_next keep Wloc IB ::= DecFastT.gb_next_red keep Wloc IB.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.NatLit.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzImg0TacFR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzImg0Tac.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

Lemma u8_swrap_sub64 : forall a b : Z, (-2^31 <= a - b < 2^31)%Z ->
  bv_swrap 32 (Z.land (a - Z.land b 18446744073709551615) 18446744073709551615 + 0)%Z = (a - b)%Z.
Proof.
  intros a b H. rewrite Z.add_0_r.
  change 18446744073709551615%Z with (Z.ones 64). rewrite !Z.land_ones by lia.
  transitivity (bv_swrap 32 (a - b)%Z); [apply swrap32_eqm | apply swrap32_small; lia].
  change (2^64)%Z with 18446744073709551616%Z. change (2^32)%Z with 4294967296%Z.
  Z.div_mod_to_equations. lia.
Qed.

Section ACeilS1. Context {ACEIL__ : ACeil}.
Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.
  Variable F : nat.
  Hypothesis HSYM : S0F_cut_SYM A F.
  Hypothesis HL8A : forall F', (F' < F)%nat -> S0F_cut_L8A A F'.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  Ltac prep DM MU :=
    unfold W14, D14, DSTATE_SIZE in MU; cbn [app blk_ivls b_s b_strm] in MU; open_dmemF DM; s2img.

  Ltac ml_facts ML :=
    let ALK := ident:(ALK) in let GRP := ident:(GRP) in let BLKF := ident:(BLKF) in let CUR := ident:(CUR) in pose proof (dinv_ML_alpha _ _ ML) as [AL15 EOB15];
    pose proof (dinv_ML_gmn _ _ ML) as GMN15;
    let X := fresh in
    pose proof ML as X; cps_destruct X as (ALK & GRP & TABS & MTF & BLKF & CUR);
    pose proof (proj1 BLKF) as NB15; unfold grp_okF in GRP; unfold cur_okF in CUR; unfold alpha_ok in ALK.

  Ltac al4 SAL :=
    lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      lazymatch c with context [(?x mod 4)%Z] =>
        replace (x mod 4)%Z with 0%Z by (clear - SAL; Z.div_mod_to_equations; lia) end end.

  Lemma S0F_U8A_loop : S0F_cut_L8A A F.
  Proof.
    unfold S0F_cut_L8A. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    pose proof DI as DI'. cps_destruct DI' as (ML & GD & _). ml_facts ML.
    pose proof (dpureF_n _ _ _ _ _ _ DP) as BN. pose proof (proj1 (proj1 (proj2 (proj1 AOK)))) as SAL16.
    pose proof (grp_decF_zn _ _ _ _ _ _ GD) as ZN. pose proof (grp_decF_zvec d (sv_alphaSize L) (sv_gSel L) (sv_gMinlen L) ltac:(lia) _ _ GD) as ZV.
    prep DM MU. kq_intro.
    unfold r_of in DR. dr_open. hide_all_but_at [S; S + 45436; S + 51628; S + 57820; usp + -336]%Z.
    pose proof (munch_refl [(S, S + 68); (usp + -336, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    wstepl. wstepl. wstepl.
    wstepl; if_cases K20; zify_cond_z K20.
    { rewrite (K_L8_ret F 1) in KQ by lia. revive_all MUL WML AOK. kq_fold.
      enter_cutF (S0F_dec_ret A AOK _ _ _ _ JK_) DP; [ ret_nb | apply dpost14_ne; dmodel_cbn; unfold BZ_X_OUTPUT; lia ]. }
    pose proof (grp_decF_limit d (sv_alphaSize L) (sv_gSel L) (sv_gMinlen L) ltac:(lia) _ _ GD ltac:(lia)) as LR.
    wstepl. wstepl. wstepl. wstepl; flags. wstepl; flags.
    wstepl. notrap.
    wstepl; flags. wstepl. wstepl; flags. wstepl; flags. wstepl; flags.
    wstepl. notrap.
    wstepl. wstepl. notrap.
    wstepl; flagsb. wstepl. al4 SAL16. notrap.
    lazymatch goal with H : u32arr _ ?mm (S + 45436)%Z (zw32 ?a ?n) |- _ =>
      pose proof (zw32_read s0segs mm (S + 45436) a n (258 * sv_gSel L + sv_zn L)%Z _ H ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
    wstepl. clear RD. try rewrite (sx32_lit (zget (d_limit d) _)) by lia.
    wstepl.
    wstepl; if_cases KB; zify_cond_z KB.
    - cps_destruct (grp_decF_break d (sv_alphaSize L) (sv_gSel L) (sv_gMinlen L) ltac:(lia) _ _ GD ltac:(lia) ltac:(lia)) as (BR1 & BR2 & BR3 & BR4).
      wstepl. wstepl. wstepl; flags. wstepl; flags.
      wstepl. notrap.
      wstepl; flags. wstepl; flags. wstepl; flags.
      wstepl. notrap.
      wstepl. wstepl. notrap.
      wstepl; flagsb. wstepl. al4 SAL16. notrap.
      lazymatch goal with H : u32arr _ ?mm (S + 51628)%Z (zw32 ?a ?n) |- _ =>
        pose proof (zw32_read s0segs mm (S + 51628) a n (258 * sv_gSel L + sv_zn L)%Z _ H ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
      wstepl. clear RD. try rewrite (sx32_lit (zget (d_base d) _)) by lia.
      wstepl. wstepl. wstepl.
      try rewrite swrap32_sub_land64F. try rewrite swrap32_sub_mod64. try rewrite (swrap32_small (sv_zvec L - _)) by lia.
      wstepl. notrap.
      wstepl. wstepl. wstepl.
      rewrite u8_swrap_sub64 by lia.
      notrap.
      wstepl. wstepl. wstepl. wstepl. notrap.
      wstepl. wstepl; flags. wstepl; flags. wstepl; flags. wstepl. notrap.
      wstepl. wstepl. notrap.
      wstepl; flagsb. wstepl. al4 SAL16. notrap.
      lazymatch goal with H : u32arr _ ?mm (S + 57820)%Z (zw32 ?a ?n) |- _ =>
        pose proof (zw32_read s0segs mm (S + 57820) a n (258 * sv_gSel L + (sv_zvec L - zget (d_base d) (258 * sv_gSel L + sv_zn L)))%Z _ H
                      ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
      wstepl. clear RD.
      change (zget (d_perm d) (258 * sv_gSel L + (sv_zvec L - zget (d_base d) (258 * sv_gSel L + sv_zn L))))%Z with (mvl_sym L d) in *.
      rewrite (K_L8_sym1 F L d s) in KQ by lia.
      revive_all MUL WML AOK. enter_sameF HSYM DP.
      apply dinv_SYM_intro; [exact ML | exact BR3].
    - wstepl. wstepl. wstepl.
      rewrite (K_L8_more F 1 L d s) in KQ by lia. change (1 + 36)%Z with 37%Z in KQ.
      gbF_call (S0F_gb_1d33c A AOK (QF A) (S0F_dec_ret_ok A AOK) _ _ _ _ JK_) MUL WML AOK DP FU.
      gbF_next [S; usp + -336]%Z [(S, S + 68); (usp + -336, usp)]%Z.
      wstepl. wstepl. wstepl.
      wstepl. notrap.
      wstepl. wstepl. gbv 24%Z 1%Z zj.
      wstepl. wstepl. wstepl. wstepl. wstepl. wstepl.
      destruct (dinv_L8_step 1 L d zj DI ltac:(lia) ltac:(lia) ltac:(lia)) as [DI' EQ].
      rewrite (Z.lor_comm zj (sv_zvec L * 2)) in FR. rewrite (lor2_bitF (sv_zvec L) zj) in FR by lia.
      try rewrite (Z.lor_comm zj (sv_zvec L * 2)). try rewrite (Z.lor_comm zj (2 * sv_zvec L)).
      first [ rewrite (lor2_bitF (sv_zvec L) zj) by lia | rewrite (lor2_bitF' (sv_zvec L) zj) by lia
            | rewrite (lor_shiftl1_bit (sv_zvec L) zj) by lia | idtac "NOTE: zvec form not normalised" ].
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
    gbF_call (S0F_gb_1de10 A AOK (QF A) (S0F_dec_ret_ok A AOK) _ _ _ _ JK_) MU WM AOK DP FU.
    1: (dmodel_cbn; unset_Z; lia).
    gbF_next [S; usp + -336]%Z [(S, S + 68); (usp + -336, usp)]%Z.
    wstepl. wstepl. wstepl. wstepl. wstepl. wstepl.
    rewrite (zn_maskF (sv_zn L)) by lia.
    gbv 11%Z (sv_zn L) zvec.
    match goal with R : (0 <= zvec < _)%Z |- _ => clear R end.
    pose proof (gbval_range bb bl (sv_zn L) ltac:(lia)) as Rzvec. fold zvec in Rzvec.
    wstepl. wstepl. wstepl.
    rewrite K_L8_enter36 in KQ.
    revive_all MUL WML AOK. enter_nextF HL8A DP.
    apply (dinv_L8_keep 1 _ d); [| apply dkeep_gb; lia].
    apply dinv_L8_init; [exact ML | exact ZN | rewrite <- ZN; unset_Z; lia | intros; exfalso; lia].
  Qed.
End H.

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
