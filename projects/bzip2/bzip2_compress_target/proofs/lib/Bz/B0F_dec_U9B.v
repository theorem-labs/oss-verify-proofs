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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzLemmasMtf BzDU5 BzDUM BzDU9 DecTacF3 DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFB DecTacFB DecTacFRB B0F_decV B0F_decRet DecTacSB B0F_decCutsM B0F_decCuts9.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacSB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCutsM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCuts9.
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

Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac.DecAuxB.   (* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.
Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok BIHI0 A.
  Hypothesis ASH : act_sh DI_B0 A.
  Variable Q : dres -> machine_state -> Prop.
  Hypothesis HRET : B0F_RET A Q.
  Variable F : nat.
  Hypothesis HSYM : B0F_cut_SYM A Q F.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).
  Notation TT := (b_tt (a_cx A)).
  Notation L16 := (b_ll16 (a_cx A)).

  (* [comment removed for export] *)
  Ltac prepS DM MU DP SM :=
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN; pose proof rnums_words_length as RNL; lin_natZ RNL;
    unfold_W14 MU; open_ash ASH AOK;
    lazymatch goal with H : sanchor (b_s _) (a_shs _) |- _ => pose proof (proj2 H : saddr (b_s (a_cx A)) (a_shs A)) as ANS0 end;
    unfold_blk SM MU; open_shb SM; open_dmemF DM; b0img.
  (* [comment removed for export] *)
  Ltac blk_al :=
    let AL := fresh "ALc" in pose proof (act_ok_al _ _ AOK) as AL; unfold ctx_alA in AL;
    let T4 := fresh "TT4" in assert (T4 : (TT mod 4 = 0)%Z) by (destruct AL as (_ & _ & _ & _ & X & _); clear - X; Z.div_mod_to_equations; lia);
    let L2 := fresh "L162" in assert (L2 : (L16 mod 2 = 0)%Z) by (destruct AL as (_ & _ & _ & _ & _ & X & _); clear - X; Z.div_mod_to_equations; lia);
    clear AL.
  (* [comment removed for export] *)
  Ltac lwslotB k :=
    match goal with FR : rw_cells b0segs _ (a_P _ + 344)%Z _ |- _ =>
      let C := fresh "FR8" in pose proof FR as C; hide C; DecTacM.slot_split FR k;
      astep; clear FR; unfold hidden in C; rename C into FR end.
  Ltac fold_MU MU SM :=
    lazymatch type of MU with munch ?W ?ma ?mb =>
      let H := fresh "MUf" in
      assert (H : munch (W14 A) ma mb)
        by (unfold W14, DSTATE_SIZE, blk_ivls; rewrite SM; cbn [Z.eqb app]; exact MU);
      clear MU; rename H into MU end.

  (* [comment removed for export] *)
  Lemma B0F_U9_L9F : forall uc E j, ((j + 2 <= E)%Z -> B0F_cut_L9F A Q F uc E (j + 1)) -> B0F_cut_L9F A Q F uc E j.
  Proof.
    intros uc E j NXT. unfold B0F_cut_L9F. intros until w752. intros DM FRL FRH AF ST MU WM MI DP DI SM FU.
    prepS DM MU DP SM. blk_al. cps_pose DI as (MR & RI & UCR & J0 & EJ & ROOM & NSR).
    pose proof (alpha_ok_state L d (proj1 MR)) as NST.
    assert (NBL : (0 <= sv_nblock L <= 900000)%Z) by (pose proof (proj1 MR) as AL; unfold alpha_ok in AL; tauto).
    assert (NBM : sv_nblockMAX L = (100000 * d_bs100k d)%Z) by (pose proof (proj1 (proj2 MR)) as GR; unfold grp_okF in GR; tauto).
    pose proof (dpureF_n _ _ _ _ _ _ DP) as BN. rewrite BN in NBM.
    pose proof (act_tt_s _ _ AOK SM) as [[TT0 TT1] SEPtt].
    unfold blk_of in BLK. rewrite SM in BLK. cbn [Z.eqb blk_at] in BLK. cps_destruct BLK as (_ & TTA & TTL).
    pose proof (dpureF_small _ _ _ _ _ _ DP) as SMALL. rewrite SM in SMALL.
    unfold r_of in DR. dr_open. hide_all_but_atF [S + 3152; TT; a_P A; a_P A + 344]%Z.
    pose proof (munch_refl [(TT, TT + 400000 * b_n cx); (a_P A + 344, a_P A + 760)]%Z m) as MUL. pose proof (wmono_refl b0segs m) as WML.
    kq_intro.
    (* [comment removed for export] *)
    brun; if_cases Kr; zify_cond_z Kr.
    { (* [comment removed for export] *)
      brun_to 0xafb90%Z.
      rewrite (K_L9_fail F L d s uc) in KQ by lia.
      clear SEPtt. revive_all_smA AOK MUL WML.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mg _) =>
        assert (BLK : blk_at b0segs mg cx (blk_of cx d))
          by (unfold blk_of; rewrite SM; cbn [Z.eqb blk_at]; split; [exact SM|]; split; [exact TTA| exact TTL]) end.
      clear TTA. fold_MU MU SM. kq_fold.
      enter_cutF (HRET _ _ _ _ JK_) DP; [ ret_nb | apply dpost14_ne; dmodel_cbn; exact NST ]. }
    (* [comment removed for export] *)
    brun_to 0xb5a30%Z.
    zw32_sw TTA (sv_nblock L + j)%Z uc ltac:(rewrite unsigned_lit by lia; reflexivity).
    rewrite (K_L9_step F L d s uc) in KQ by lia. rewrite (dstore_fast d) in KQ by exact SMALL.
    (* [comment removed for export] *)
    brun; if_cases Kl; zify_cond_z Kl. all: swap 1 2.   (* [comment removed for export] *)
    - (* [comment removed for export] *)
      brun_to 0xb23f4%Z.
      clear SEPtt. revive_all_smA AOK MUL WML.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mg _) =>
        assert (BLK : blk_at b0segs mg cx (blk_of cx (d_set_tt d (zset (d_tt d) (sv_nblock L + j) uc))))
          by (unfold blk_of; rewrite SM; cbn [Z.eqb blk_at]; dmodel_cbn; split; [exact SM|]; split; [exact TTA| rewrite zw32_length; lia]) end.
      clear TTA. fold_MU MU SM.
      rewrite (K_L9_exit F L) in KQ by lia.
      change (dgo F (sym_dispatch ?L2 ?d2 s)) with (K_SYM F L2 d2 s) in KQ.
      pose proof (dpureF_set_tt _ _ _ _ _ _ (sv_nblock L + j) uc DP ltac:(lia)) as DP'.
      kq_fold. enter_cutF (HSYM _ _ _ JK_) DP'.
      replace (sv_nblock L + j + 1)%Z with (sv_nblock L + E)%Z by lia. replace (E - j - 1)%Z with 0%Z by lia.
      apply (dinv_L9_exit_fast L d uc E j DI SMALL); lia.
    - (* [comment removed for export] *)
      brun_to 0xb59c4%Z.
      clear SEPtt. revive_all_smA AOK MUL WML.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mg _) =>
        assert (BLK : blk_at b0segs mg cx (blk_of cx (d_set_tt d (zset (d_tt d) (sv_nblock L + j) uc))))
          by (unfold blk_of; rewrite SM; cbn [Z.eqb blk_at]; dmodel_cbn; split; [exact SM|]; split; [exact TTA| rewrite zw32_length; lia]) end.
      clear TTA. fold_MU MU SM.
      pose proof (NXT ltac:(lia)) as NX. unfold B0F_cut_L9F in NX.
      replace (sv_nblock L + j + 1)%Z with (sv_nblock L + (j + 1))%Z in KQ by lia. replace (E - j - 1)%Z with (E - (j + 1))%Z in KQ by lia.
      kq_fold. enter_cutF (NX L _ s JK_) DP; [ apply (dpureF_set_tt _ _ _ _ _ _ _ _ DP); lia | apply (dinv_L9_step_fast L d uc E j DI SMALL); lia | exact SM ].
  Qed.

  (* [comment removed for export] *)
  Lemma B0F_U9_L9S : forall uc E j, ((j + 2 <= E)%Z -> B0F_cut_L9S A Q F uc E (j + 1)) -> B0F_cut_L9S A Q F uc E j.
  Proof.
    intros uc E j NXT. unfold B0F_cut_L9S. intros until w752. intros DM FRL FRH AF ST MU WM MI DP DI SM FU.
    prepS DM MU DP SM. blk_al. cps_pose DI as (MR & RI & UCR & J0 & EJ & ROOM & NSR).
    pose proof (alpha_ok_state L d (proj1 MR)) as NST.
    assert (NBL : (0 <= sv_nblock L <= 900000)%Z) by (pose proof (proj1 MR) as AL; unfold alpha_ok in AL; tauto).
    assert (NBM : sv_nblockMAX L = (100000 * d_bs100k d)%Z) by (pose proof (proj1 (proj2 MR)) as GR; unfold grp_okF in GR; tauto).
    pose proof (dpureF_n _ _ _ _ _ _ DP) as BN. rewrite BN in NBM.
    pose proof (act_ll_s _ _ AOK SM) as [(L160 & L161 & L40 & L41) [SEP16 SEP4]].
    unfold blk_of in BLK. rewrite SM in BLK. cbn [Z.eqb blk_at] in BLK. cps_destruct BLK as (_ & L16A & L16L & L4A & L4L).
    pose proof (dpureF_small _ _ _ _ _ _ DP) as SMALL. rewrite SM in SMALL.
    unfold r_of in DR. dr_open. hide_all_but_atF [S + 3152; L16; a_P A; a_P A + 344]%Z.
    pose proof (munch_refl [(L16, L16 + 200000 * b_n cx); (a_P A + 344, a_P A + 760)]%Z m) as MUL. pose proof (wmono_refl b0segs m) as WML.
    kq_intro.
    brun; if_cases Kr; zify_cond_z Kr.
    { (* [comment removed for export] *)
      brun_to 0xafb90%Z.
      rewrite (K_L9_fail F L d s uc) in KQ by lia.
      clear SEP16 SEP4. revive_all_smA AOK MUL WML.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mg _) =>
        assert (BLK : blk_at b0segs mg cx (blk_of cx d))
          by (unfold blk_of; rewrite SM; cbn [Z.eqb blk_at]; split; [exact SM|]; split; [exact L16A| split; [exact L16L| split; [exact L4A| exact L4L]]]) end.
      clear L16A L4A. fold_MU MU SM. kq_fold.
      enter_cutF (HRET _ _ _ _ JK_) DP; [ ret_nb | apply dpost14_ne; dmodel_cbn; exact NST ]. }
    brun_to 0xb5958%Z.
    zh16_sh L16A (sv_nblock L + j)%Z.
    rewrite (unsigned_lit uc) in L16A by lia. rewrite (Z.mod_small uc 65536) in L16A by lia.
    rewrite (K_L9_step F L d s uc) in KQ by lia. rewrite (dstore_smallm d) in KQ by lia.
    brun; if_cases Kl; zify_cond_z Kl. all: swap 1 2.   (* [comment removed for export] *)
    - (* [comment removed for export] *)
      brun_to 0xb23f4%Z.
      clear SEP16 SEP4. revive_all_smA AOK MUL WML.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mg _) =>
        assert (BLK : blk_at b0segs mg cx (blk_of cx (d_set_ll16 d (zset (d_ll16 d) (sv_nblock L + j) uc))))
          by (unfold blk_of; rewrite SM; cbn [Z.eqb blk_at]; dmodel_cbn; split; [exact SM|]; split; [exact L16A| split; [rewrite zh16_length; lia| split; [exact L4A| exact L4L]]]) end.
      clear L16A L4A. fold_MU MU SM.
      rewrite (K_L9_exit F L) in KQ by lia.
      change (dgo F (sym_dispatch ?L2 ?d2 s)) with (K_SYM F L2 d2 s) in KQ.
      pose proof (dpureF_set_ll16 _ _ _ _ _ _ (sv_nblock L + j) uc DP ltac:(lia)) as DP'.
      kq_fold. enter_cutF (HSYM _ _ _ JK_) DP'.
      replace (sv_nblock L + j + 1)%Z with (sv_nblock L + E)%Z by lia. replace (E - j - 1)%Z with 0%Z by lia.
      apply (dinv_L9_exit_small L d uc E j DI); lia.
    - (* [comment removed for export] *)
      brun_to 0xb58f0%Z.
      clear SEP16 SEP4. revive_all_smA AOK MUL WML.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mg _) =>
        assert (BLK : blk_at b0segs mg cx (blk_of cx (d_set_ll16 d (zset (d_ll16 d) (sv_nblock L + j) uc))))
          by (unfold blk_of; rewrite SM; cbn [Z.eqb blk_at]; dmodel_cbn; split; [exact SM|]; split; [exact L16A| split; [rewrite zh16_length; lia| split; [exact L4A| exact L4L]]]) end.
      clear L16A L4A. fold_MU MU SM.
      pose proof (NXT ltac:(lia)) as NX. unfold B0F_cut_L9S in NX.
      replace (sv_nblock L + j + 1)%Z with (sv_nblock L + (j + 1))%Z in KQ by lia. replace (E - j - 1)%Z with (E - (j + 1))%Z in KQ by lia.
      pose proof (dpureF_set_ll16 _ _ _ _ _ _ (sv_nblock L + j) uc DP ltac:(lia)) as DP'.
      kq_fold. enter_cutF (NX L _ s JK_) DP'; [ apply (dinv_L9_step_small L d uc E j DI); lia | exact SM ].
  Qed.

  (* [comment removed for export] *)
  Lemma B0F_U9_L9S_all : forall uc E j, (0 <= j < E)%Z -> B0F_cut_L9S A Q F uc E j.
  Proof.
    intros uc E j Hj.
    assert (G : forall k : nat, (Z.of_nat k < E)%Z -> B0F_cut_L9S A Q F uc E (E - 1 - Z.of_nat k)%Z).
    { induction k as [|k IH]; intros Hk.
      - apply B0F_U9_L9S. intros; exfalso; lia.
      - apply B0F_U9_L9S. intros _. replace (E - 1 - Z.of_nat (Datatypes.S k) + 1)%Z with (E - 1 - Z.of_nat k)%Z by lia. apply IH. lia. }
    pose proof (G (Z.to_nat (E - 1 - j)) ltac:(lia)) as G0.
    replace (E - 1 - Z.of_nat (Z.to_nat (E - 1 - j)))%Z with j in G0 by lia. exact G0.
  Qed.
  Lemma B0F_U9_L9F_all : forall uc E j, (0 <= j < E)%Z -> B0F_cut_L9F A Q F uc E j.
  Proof.
    intros uc E j Hj.
    assert (G : forall k : nat, (Z.of_nat k < E)%Z -> B0F_cut_L9F A Q F uc E (E - 1 - Z.of_nat k)%Z).
    { induction k as [|k IH]; intros Hk.
      - apply B0F_U9_L9F. intros; exfalso; lia.
      - apply B0F_U9_L9F. intros _. replace (E - 1 - Z.of_nat (Datatypes.S k) + 1)%Z with (E - 1 - Z.of_nat k)%Z by lia. apply IH. lia. }
    pose proof (G (Z.to_nat (E - 1 - j)) ltac:(lia)) as G0.
    replace (E - 1 - Z.of_nat (Z.to_nat (E - 1 - j)))%Z with j in G0 by lia. exact G0.
  Qed.

  (* [comment removed for export] *)
  Ltac head_loadsA MTA S0UR HIST :=
    let RD := fresh "RD" in let pp := fresh "pp" in let q := fresh "q" in let uc := fresh "uc" in
    let QR := fresh "QR" in let UR := fresh "UR" in let HU := fresh "HU" in let OB := fresh "OB" in
    (* [comment removed for export] *)
    astep; astep; astep;
    rewrite ?(land64_small (sv_es _)) by ulia; rewrite ?(swrap32_small (sv_es _ + 1)) by ulia;
    brun_to 0xb57f8%Z;
    lazymatch goal with DRmtfb : u32arr _ ?mm (_ + 7820)%Z (zw32 ?a _) |- _ =>
      pose proof (zw32_read b0segs mm _ a 16 0 _ DRmtfb ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end;
    astep; clear RD;
    lazymatch goal with |- context [Z_to_bv 64 (zget ?a 0)] => set (pp := zget a 0) in * end;
    brun_to 0xb5830%Z;
    pose proof (MTA pp ltac:(lia)) as QR;
    lazymatch goal with DRmtfa : u8arr _ ?mm (_ + 3724)%Z (zb8 ?a _) |- _ =>
      pose proof (zb8_read1 b0segs mm _ a 4096 pp _ DRmtfa ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end;
    astep; clear RD; rewrite zxb_lit8 by lia;
    lazymatch goal with |- context [Z_to_bv 64 (zget ?a pp)] => set (q := zget a pp) in * end;
    brun_to 0xb5854%Z;
    pose proof (S0UR q) as UR;
    lazymatch goal with DRs2u : u8arr _ ?mm (_ + 3468)%Z (zb8 ?a _) |- _ =>
      pose proof (zb8_read1 b0segs mm _ a 256 q _ DRs2u ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end;
    astep; clear RD; rewrite zxb_lit8 by lia;
    lazymatch goal with |- context [Z_to_bv 64 (zget ?a q)] => set (uc := zget a q) in * end;
    pose proof (HIST uc ltac:(lia)) as HU;
    lazymatch goal with DRunz : u32arr _ _ (_ + 68)%Z (zw32 ?a _) |- _ =>
      lazymatch type of HIST with hist_ok _ ?sy ?n => pose proof (occ_bounds sy n uc) as OB end; rewrite <- HU in OB end;
    brun_to 0xb5880%Z;
    lazymatch goal with DRunz : u32arr _ ?mm (_ + 68)%Z (zw32 ?a _) |- _ =>
      pose proof (zw32_read b0segs mm _ a 256 uc _ DRunz ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end;
    astep; clear RD.

  Lemma B0F_U9_HRUNEND : B0F_cut_HRUNEND A Q F.
  Proof.
    unfold B0F_cut_HRUNEND. intros until w752. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    cps_destruct DI as (ML & NSR & ESR). cps_pose ML as (AL & GR & TB & MT & BL & CU).
    pose proof (alpha_ok_state L d AL) as NST.
    assert (NBL : (0 <= sv_nblock L <= 900000)%Z) by (unfold alpha_ok in AL; tauto).
    assert (NBM : sv_nblockMAX L = (100000 * d_bs100k d)%Z) by (unfold grp_okF in GR; tauto).
    cps_pose BL as (NBR & SYMB & HIST). destruct MT as [MTI MTA].
    pose proof (mtf_inv_bounds _ MTI 0 ltac:(lia)) as PPR. unfold mtfb in PPR.
    pose proof (dpureF_rep _ _ _ _ _ _ DP) as RP. unfold drep in RP. cps_destruct RP as (_ & _ & _ & S0UR & _).
    pose proof (dpureF_n _ _ _ _ _ _ DP) as BN. rewrite BN in NBM.
    pose proof (dpureF_small _ _ _ _ _ _ DP) as SMALL.
    destruct (act_small01 _ _ AOK) as [SM|SM]; rewrite SM in SMALL.
    - (* [comment removed for export] *)
      prepS DM MU DP SM. unfold r_of in DR. dr_open.
      hide_all_but_atF [S; S + 68; S + 3468; S + 3724; S + 7820; a_P A; a_P A + 344]%Z.
      pose proof (munch_refl [(S + 68, S + 1092); (a_P A + 344, a_P A + 760)]%Z m) as MUL. pose proof (wmono_refl b0segs m) as WML.
      kq_intro. unfold K_HRUNEND in KQ. rewrite run_exit_K in KQ. unfold run_d1, run_uc in KQ.
      destruct (Z.eq_dec (sv_es L) (-1)) as [Ees|NE].
      + (* [comment removed for export] *)
        rewrite Ees in *.
        replace (-1 + 1)%Z with 0%Z in KQ by lia.
        head_loadsA MTA S0UR HIST.
        (* [comment removed for export] *)
        brun_to 0xb589c%Z.
        zw32_sw DRunz uc (zget (d_unzftab d) uc + 0)%Z ltac:(rewrite unsigned_lit by lia; f_equal; lia).
        (* [comment removed for export] *)
        brun_to 0xb58b4%Z. astep. rewrite ?zxb_lit8 by lia. rewrite ?SMALL.
        brun_to 0xb23f4%Z.
        rewrite (K_L9_exit F L) in KQ by lia.
        change (dgo F (sym_dispatch ?L2 ?d2 s)) with (K_SYM F L2 d2 s) in KQ.
        revive_all_smA AOK MUL WML. fold_MU MU SM.
        pose proof (dpureF_set_unzftab _ _ _ _ _ _ (zset (d_unzftab d) uc (zget (d_unzftab d) uc + 0)) DP) as DP'.
        kq_fold. enter_cutF (HSYM _ _ _ JK_) DP'. apply (dinv_SYM_run0 L d uc ML); ulia.
      + assert (ES0 : (0 <= sv_es L)%Z) by lia.
        head_loadsA MTA S0UR HIST.
        set (E := (sv_es L + 1)%Z) in *.
        brun_to 0xb589c%Z.
        rewrite ?(land64_small (sv_es L)) by ulia. rewrite ?(swrap32_small (sv_es L + 1)) by ulia. fold E.
        zw32_sw DRunz uc (zget (d_unzftab d) uc + E)%Z ltac:(rewrite unsigned_lit by ulia; f_equal; ulia).
        brun_to 0xb58b4%Z. astep. rewrite ?zxb_lit8 by lia. rewrite ?SMALL.
        (* [comment removed for export] *)
        brun; if_cases Kz; zify_cond_z Kz; [exfalso; ulia|].
        (* [comment removed for export] *)
        lwslotB 0%nat. try rewrite (sx32_lit (sv_nblockMAX L)) by ulia.
        brun; if_cases Kmx; zify_cond_z Kmx; [exfalso; ulia|].
        brun_to 0xb59c4%Z. sh_norm.
        revive_all_smA AOK MUL WML. fold_MU MU SM.
        lazymatch type of KQ with kq _ (K_L9 ?F0 ?L0 ?d1 ?s0 ?u0 ?nb ?e) =>
          replace (K_L9 F0 L0 d1 s0 u0 nb e) with (K_L9 F0 L0 d1 s0 u0 (nb + 0) (e - 0))%Z in KQ by (f_equal; lia) end.
        pose proof (B0F_U9_L9F_all uc E 0 ltac:(ulia)) as NX. unfold B0F_cut_L9F in NX.
        pose proof (dpureF_set_unzftab _ _ _ _ _ _ (zset (d_unzftab d) uc (zget (d_unzftab d) uc + E)) DP) as DP'.
        kq_fold. enter_cutF (NX L _ s JK_) DP'; [ apply (dinv_L9_entry L d uc E ML); ulia | exact SM ].
    - (* [comment removed for export] *)
      prepS DM MU DP SM. unfold r_of in DR. dr_open.
      hide_all_but_atF [S; S + 68; S + 3468; S + 3724; S + 7820; a_P A; a_P A + 344]%Z.
      pose proof (munch_refl [(S + 68, S + 1092); (a_P A + 344, a_P A + 760)]%Z m) as MUL. pose proof (wmono_refl b0segs m) as WML.
      kq_intro. unfold K_HRUNEND in KQ. rewrite run_exit_K in KQ. unfold run_d1, run_uc in KQ.
      destruct (Z.eq_dec (sv_es L) (-1)) as [Ees|NE].
      + rewrite Ees in *.
        replace (-1 + 1)%Z with 0%Z in KQ by lia.
        head_loadsA MTA S0UR HIST.
        brun_to 0xb589c%Z.
        zw32_sw DRunz uc (zget (d_unzftab d) uc + 0)%Z ltac:(rewrite unsigned_lit by lia; f_equal; lia).
        brun_to 0xb58b4%Z. astep. rewrite ?zxb_lit8 by lia. rewrite ?SMALL.
        brun_to 0xb23f4%Z.
        rewrite (K_L9_exit F L) in KQ by lia.
        change (dgo F (sym_dispatch ?L2 ?d2 s)) with (K_SYM F L2 d2 s) in KQ.
        revive_all_smA AOK MUL WML. fold_MU MU SM.
        pose proof (dpureF_set_unzftab _ _ _ _ _ _ (zset (d_unzftab d) uc (zget (d_unzftab d) uc + 0)) DP) as DP'.
        kq_fold. enter_cutF (HSYM _ _ _ JK_) DP'. apply (dinv_SYM_run0 L d uc ML); ulia.
      + assert (ES0 : (0 <= sv_es L)%Z) by lia.
        head_loadsA MTA S0UR HIST.
        set (E := (sv_es L + 1)%Z) in *.
        brun_to 0xb589c%Z.
        rewrite ?(land64_small (sv_es L)) by ulia. rewrite ?(swrap32_small (sv_es L + 1)) by ulia. fold E.
        zw32_sw DRunz uc (zget (d_unzftab d) uc + E)%Z ltac:(rewrite unsigned_lit by ulia; f_equal; ulia).
        brun_to 0xb58b4%Z. astep. rewrite ?zxb_lit8 by lia. rewrite ?SMALL.
        brun; if_cases Kz; zify_cond_z Kz; [exfalso; ulia|].
        lwslotB 0%nat. try rewrite (sx32_lit (sv_nblockMAX L)) by ulia.
        brun; if_cases Kmx; zify_cond_z Kmx; [exfalso; ulia|].
        brun_to 0xb58f0%Z. sh_norm.
        revive_all_smA AOK MUL WML. fold_MU MU SM.
        lazymatch type of KQ with kq _ (K_L9 ?F0 ?L0 ?d1 ?s0 ?u0 ?nb ?e) =>
          replace (K_L9 F0 L0 d1 s0 u0 nb e) with (K_L9 F0 L0 d1 s0 u0 (nb + 0) (e - 0))%Z in KQ by (f_equal; lia) end.
        pose proof (B0F_U9_L9S_all uc E 0 ltac:(ulia)) as NX. unfold B0F_cut_L9S in NX.
        pose proof (dpureF_set_unzftab _ _ _ _ _ _ (zset (d_unzftab d) uc (zget (d_unzftab d) uc + E)) DP) as DP'.
        kq_fold. enter_cutF (NX L _ s JK_) DP'; [ apply (dinv_L9_entry L d uc E ML); ulia | exact SM ].
  Qed.
End R.
End ACeilS1.

