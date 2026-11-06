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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzLemmasMtf BzDU5 BzDUM BzDU10 DecAuxL DecTacF3 DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU10 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAuxL OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFB DecTacFB DecTacFRB B0F_decV B0F_decRet DecTacSB B0F_decCutsM B0F_decCutsL.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacSB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCutsM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCutsL.
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

Section ACeilS1. Context {ACEIL__ : ACeil}.
Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok BIHI0 A.
  Hypothesis ASH : act_sh DI_B0 A.
  Variable Q : dres -> machine_state -> Prop.
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
  Ltac fold_MU MU SM :=
    lazymatch type of MU with munch ?W ?ma ?mb =>
      let H := fresh "MUf" in
      assert (H : munch (W14 A) ma mb)
        by (unfold W14, DSTATE_SIZE, blk_ivls; rewrite SM; cbn [Z.eqb app]; exact MU);
      clear MU; rename H into MU end.
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
  Ltac lj_headA S0UR HIST SMALL :=
    let RD := fresh "RD" in let u := fresh "u" in let UR := fresh "UR" in let HU := fresh "HU" in let OB := fresh "OB" in
    brun_to 0xb2ae0%Z;
    lazymatch goal with DRs2u : u8arr _ ?mm (_ + 3468)%Z (zb8 ?a _), UCR : (0 <= ?uc < 256)%Z |- _ =>
        pose proof (S0UR uc) as UR;
        pose proof (zb8_read1 b0segs mm _ a 256 uc _ DRs2u ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end;
    astep; clear RD; rewrite zxb_lit8 by lia;
    lazymatch goal with |- context [Z_to_bv 64 (zget ?a ?uc)] => set (u := zget a uc) in * end;
    pose proof (HIST u ltac:(lia)) as HU;
    lazymatch goal with DRunz : u32arr _ _ (_ + 68)%Z (zw32 ?a _) |- _ =>
      lazymatch type of HIST with hist_ok _ ?sy ?n => pose proof (occ_bounds sy n u) as OB end; rewrite <- HU in OB end;
    brun_to 0xb2b08%Z;
    lazymatch goal with DRunz : u32arr _ ?mm (_ + 68)%Z (zw32 ?a _) |- _ =>
      pose proof (zw32_read b0segs mm _ a 256 u _ DRunz ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end;
    astep; clear RD;
    brun_to 0xb2b20%Z;
    lazymatch goal with DRunz : u32arr _ _ (_ + 68)%Z (zw32 ?unz _) |- _ =>
      zw32_sw DRunz u (zget unz u + 1)%Z ltac:(rewrite unsigned_lit by lia; reflexivity) end;
    brun_to 0xb2b3c%Z; astep; rewrite ?zxb_lit8 by lia; rewrite ?SMALL.

  Lemma B0F_U10_LJ : forall uc mb2, B0F_cut_LJ A Q F uc mb2.
  Proof.
    intros uc mb2. unfold B0F_cut_LJ. intros until w752. intros DM FRL FRH AF ST MU WM MI DP MR MA NB UCR MI2 ROW FU.
    u10_facts MR DP. cps_pose MR as (_ & _ & _ & (NBR & SYMB & HIST) & _).
    pose proof (dpureF_small _ _ _ _ _ _ DP) as SMALL.
    destruct (act_small01 _ _ AOK) as [SM|SM]; rewrite SM in SMALL.
    - (* [comment removed for export] *)
      prepS DM MU DP SM. blk_al. unfold r_of in DR. dr_open.
      unfold blk_of in BLK. rewrite SM in BLK. cbn [Z.eqb blk_at] in BLK. cps_destruct BLK as (_ & TTA & TTL).
      pose proof (act_tt_s _ _ AOK SM) as [[TT0 TT1] SEPtt].
      hide_all_but_atF [S; S + 68; S + 3468; S + 3152; TT; a_P A; a_P A + 344]%Z.
      pose proof (munch_refl [(S + 68, S + 1092); (TT, TT + 400000 * b_n cx); (a_P A + 344, a_P A + 760)]%Z m) as MUL. pose proof (wmono_refl b0segs m) as WML.
      kq_intro. rewrite (K_LJ_fast F L d s uc) in KQ by exact SMALL. unfold zincr in KQ.
      lj_headA S0UR HIST SMALL.
      (* [comment removed for export] *)
      brun_to 0xb2c30%Z.
      zw32_sw TTA (sv_nblock L) u ltac:(rewrite unsigned_lit by lia; reflexivity).
      (* [comment removed for export] *)
      brun_to 0xb2c40%Z.
      pose proof (dpureF_set_unzftab _ _ _ _ _ _ (zset (d_unzftab d) u (zget (d_unzftab d) u + 1)) DP) as DP2.
      pose proof (dpureF_set_tt _ _ _ _ _ _ (sv_nblock L) u DP2 ltac:(lia)) as DP3.
      clear SEPtt. revive_all_smA AOK MUL WML.
      lazymatch type of KQ with kq _ (K_HMTFC _ _ ?d3 _) =>
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mg _) => assert (BLK : blk_at b0segs mg cx (blk_of cx d3)) end end.
      { unfold blk_of. rewrite SM. cbn [Z.eqb blk_at]. dmodel_cbn. split; [exact SM|]. split; [exact TTA| rewrite zw32_length; lia]. }
      clear TTA. fold_MU MU SM.
      kq_fold. enter_cutF (HC _ _ _ JK_) DP3.
      apply (dinv_ML_lit_fast L d mb2 uc MR ROW MI2 MA UCR NB ltac:(lia) S0UR SMALL).
    - (* [comment removed for export] *)
      prepS DM MU DP SM. blk_al. unfold r_of in DR. dr_open.
      unfold blk_of in BLK. rewrite SM in BLK. cbn [Z.eqb blk_at] in BLK. cps_destruct BLK as (_ & L16A & L16L & L4A & L4L).
      pose proof (act_ll_s _ _ AOK SM) as [(L160 & L161 & L40 & L41) [SEP16 SEP4]].
      hide_all_but_atF [S; S + 68; S + 3468; S + 3152; L16; a_P A; a_P A + 344]%Z.
      pose proof (munch_refl [(S + 68, S + 1092); (L16, L16 + 200000 * b_n cx); (a_P A + 344, a_P A + 760)]%Z m) as MUL. pose proof (wmono_refl b0segs m) as WML.
      kq_intro. rewrite (K_LJ_small F L d s uc) in KQ by lia. unfold zincr in KQ.
      lj_headA S0UR HIST SMALL.
      brun_to 0xb2bb8%Z.
      zh16_sh L16A (sv_nblock L).
      rewrite (unsigned_lit u) in L16A by lia. rewrite (Z.mod_small u 65536) in L16A by lia.
      brun_to 0xb2c40%Z.
      pose proof (dpureF_set_unzftab _ _ _ _ _ _ (zset (d_unzftab d) u (zget (d_unzftab d) u + 1)) DP) as DP2.
      pose proof (dpureF_set_ll16 _ _ _ _ _ _ (sv_nblock L) u DP2 ltac:(lia)) as DP3.
      clear SEP16 SEP4. revive_all_smA AOK MUL WML.
      lazymatch type of KQ with kq _ (K_HMTFC _ _ ?d3 _) =>
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mg _) => assert (BLK : blk_at b0segs mg cx (blk_of cx d3)) end end.
      { unfold blk_of. rewrite SM. cbn [Z.eqb blk_at]. dmodel_cbn. split; [exact SM|]. split; [exact L16A| split; [rewrite zh16_length; lia| split; [exact L4A| exact L4L]]]. }
      clear L16A L4A. fold_MU MU SM.
      kq_fold. enter_cutF (HC _ _ _ JK_) DP3.
      apply (dinv_ML_lit_small L d mb2 uc MR ROW MI2 MA UCR NB ltac:(lia) S0UR ltac:(lia)).
  Qed.
End R.
End ACeilS1.

