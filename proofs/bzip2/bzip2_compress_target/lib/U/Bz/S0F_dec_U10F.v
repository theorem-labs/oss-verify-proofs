(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzContracts BzContracts0 DecCut DecTac DecTac2 DecTacS DecAux.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecAuxM DecAuxL. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzLemmasT BzLemmasMtf. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzWalkArith BzWalkArith2 BzWalkArith3 DecAuxR S0_dec_U13 S0_decCuts S0_decCutsM.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAux OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac.DecAuxB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAuxM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAuxL OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasMtf OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAuxR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_dec_U13 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_decCuts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_decCutsM. (* [comment removed for export] *) From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require PropExec. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require SegsS0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzContracts BzContracts0 DecCut DecAux.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecAuxM DecAuxL S0_dec_U13 S0_decCutsM. From Stdlib Require Lia. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU9. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF DecTacFR DecTacF3 S0F_decRet S0F_decCuts S0F_decCutsM.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacFR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCuts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCutsM.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDU10. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import S0F_decCutsL DecAux10F S0F_dec_U10J.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzWalkArith4.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import DecFast DecFastT DecFastS.
Local Ltac DecCut.revive H MUL WML AOK ::= DecFast.revive_cached H MUL WML AOK.
Local Ltac DecCut.dpure_from DP ::= DecFast.dpure_from_fast DP.
Local Ltac DecCut.open_dmem DM ::= DecFast.open_dmem_red DM.
Local Ltac DecTac.gb_next keep Wloc IB ::= DecFastT.gb_next_red keep Wloc IB.
Local Ltac DecTacS.revive_sm H AOK SM0 MUL WML ::= DecFastS.revive_sm_cached H AOK SM0 MUL WML.
Local Ltac DecTacS.revive_all_smL AOK SM0 MUL WML LIN DP ::= DecFastS.revive_all_smL_split AOK SM0 MUL WML LIN DP.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzImg0TacFR BzImg0Tac.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require SasFastF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLia.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac simpl_arr_sizes ::= SasFastF.sas6F_all.
Local Ltac StoreFast.tlia ::= RelLia.tlia_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.

Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.
  Variable F : nat.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).
  Notation TT := (b_tt (a_cx A)).
  Notation L16 := (b_ll16 (a_cx A)).

  Ltac prep DM MU DP :=
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN; pose proof rnums_words_length as RNL; lin_natZ RNL;
    unfold W14, D14, DSTATE_SIZE in MU; cbn [app blk_ivls b_s b_strm] in MU; open_dmemF DM; s2img.
  (* [comment removed for export] *)
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

  Section M.
  Hypothesis HC : S0F_cut_HMTFC A F.
  Variables (L : dsv) (s : dstrm) (J : jk) (mb : Z -> Z).
  Notation LFAcF := (LFAcF A F L s J mb). Notation LFBcF := (LFBcF A F L s J mb). Notation LFZcF := (LFZcF A F L s J mb).
  Let LJ := S0F_U10_LJ A AOK F HC L s J.

  (* [comment removed for export] *)
  Ltac fprep DM MU DP MR :=
    u10_facts MR DP; prep DM MU DP; lazymatch goal with D : drest_at _ _ _ _ |- _ => unfold r_of in D end; dr_open.
  (* [comment removed for export] *)
  Ltac mtfa_rdF MA i :=
    let RD := fresh "RD" in let BR := fresh "BR" in
    lazymatch goal with AR : u8arr _ ?mm (b_s (a_cx A) + 3724)%Z (zb8 ?a _) |- _ =>
      pose proof (MA i ltac:(lia)) as BR;
      pose proof (zb8_read1 s0segs mm _ a 4096 i _ AR ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD;
      repeat rewrite zget_zset_other in RD by lia;
      wstepl; clear RD; rewrite zxb_lit8 by lia end.
  Ltac mtfa_wrF i :=
    lazymatch goal with AR : u8arr _ ?mm (b_s (a_cx A) + 3724)%Z (zb8 ?a _) |- _ => zb8_sb AR i end.
  (* [comment removed for export] *)
  Ltac u10_side MR MA ROW :=
    lazymatch goal with
    | |- ml_nomtfF _ _ => repeat first [apply ml_nomtfF_set_mtfa | apply ml_nomtfF_set_mtfbase]; exact MR
    | |- mtfa_ok _ => rewrite ?d_mtfa_set_mtfa, ?d_mtfa_set_mtfbase; repeat (apply mtfa_ok_set; [ | first [ lia | apply MA; lia ] ]); exact MA
    | |- mbrow _ _ => try (repeat apply mbrow_set_mtfa; exact ROW)
    | |- _ => first [ assumption | lia | idtac ]
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0F_U10_LFZ : forall pp uc, LFZcF pp uc.
  Proof.
    intros pp uc. unfold S0F_decCutsL.LFZcF. intros until pb. intros DM FR ST MU WM MI DP FU MR MA MTI ROW NB UCR PP.
    fprep DM MU DP MR. pose proof (mtf_inv_bounds mb MTI 0 ltac:(lia)) as PPR.
    hide_all_but_at [S + 3724; S + 7820]%Z.
    pose proof (munch_refl [(S + 3724, S + 7820)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    kq_intro. rewrite K_LFB_exit in KQ.
    wstepl. wstepl; notrap. wstepl; notrap. wstepl. (* [comment removed for export] *)
    mtfa_wrF pp. (* [comment removed for export] *)
    pose proof (dpureF_set_mtfa _ _ _ _ _ _ pp uc DP ltac:(lia)) as DP'.
    revive_all MUL WML AOK.
    pose proof (LJ uc mb) as NX. unfold LJcF in NX.
    kq_fold. enter_cutF NX DP'; u10_side MR MA ROW.
  Time Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0F_U10_LFB : forall pp uc k, ((2 <= k)%Z -> LFBcF pp uc (k - 1)) -> LFBcF pp uc k.
  Proof.
    intros pp uc k NXT. unfold S0F_decCutsL.LFBcF. intros until pb. intros DM FR ST MU WM MI DP FU MR MA MTI ROW NB UCR PP K.
    fprep DM MU DP MR. pose proof (mtf_inv_bounds mb MTI 0 ltac:(lia)) as PPR.
    hide_all_but_at [S + 3724; S + 7820]%Z.
    pose proof (munch_refl [(S + 3724, S + 7820)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    kq_intro. rewrite (K_LFB_step F L d s pp k uc) in KQ by lia.
    wstepl. wstepl. wstepl; notrap. wstepl; notrap. wstepl. wstepl; notrap. wstepl; notrap. wstepl. (* [comment removed for export] *)
    mtfa_rdF MA (pp + k - 1)%Z. (* [comment removed for export] *)
    wstepl. wstepl. (* [comment removed for export] *)
    mtfa_wrF (pp + k)%Z. (* [comment removed for export] *)
    wstepl. (* [comment removed for export] *)
    pose proof (dpureF_set_mtfa _ _ _ _ _ _ (pp + k) (zget (d_mtfa d) (pp + k - 1)) DP ltac:(lia)) as DP'.
    revive_all MUL WML AOK.
    wstepl; if_cases K2; zify_cond_z K2.
    - pose proof (NXT ltac:(lia)) as NX. unfold S0F_decCutsL.LFBcF in NX.
      kq_fold. enter_cutF NX DP'; u10_side MR MA ROW.
    - pose proof (S0F_U10_LFZ pp uc) as NX. unfold S0F_decCutsL.LFZcF in NX.
      replace (k - 1)%Z with 0%Z in KQ by lia.
      kq_fold. enter_cutF NX DP'; u10_side MR MA ROW.
  Time Qed.
  Lemma S0F_U10_LFB_all : forall pp uc k, (1 <= k <= 3)%Z -> LFBcF pp uc k.
  Proof.
    intros pp uc k Hk.
    assert (G : forall n : nat, (n <= 2)%nat -> LFBcF pp uc (1 + Z.of_nat n)%Z).
    { induction n as [|n IH]; intros Hn.
      - apply S0F_U10_LFB. intros; exfalso; lia.
      - apply S0F_U10_LFB. intros _. replace (1 + Z.of_nat (Datatypes.S n) - 1)%Z with (1 + Z.of_nat n)%Z by lia. apply IH. lia. }
    replace k with (1 + Z.of_nat (Z.to_nat (k - 1)))%Z by lia. apply G. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0F_U10_LFA : forall pp uc mm, ((9 <= mm)%Z -> LFAcF pp uc (mm - 4)) -> LFAcF pp uc mm.
  Proof.
    intros pp uc mm NXT. unfold S0F_decCutsL.LFAcF. intros until pb. intros DM FR ST MU WM MI DP FU MR MA MTI ROW NB UCR NSR PP MM.
    fprep DM MU DP MR. pose proof (mtf_inv_bounds mb MTI 0 ltac:(lia)) as PPR.
    hide_all_but_at [S + 3724; S + 7820; usp + -336]%Z.
    pose proof (munch_refl [(S + 3724, S + 7820)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    kq_intro. rewrite (K_LFA_step F L d s pp (mm - 1) uc) in KQ by lia.
    replace (pp + (mm - 1))%Z with (pp + mm - 1)%Z in KQ by lia. replace (pp + mm - 1 - 1)%Z with (pp + mm - 2)%Z in KQ by lia.
    replace (pp + mm - 1 - 2)%Z with (pp + mm - 3)%Z in KQ by lia. replace (pp + mm - 1 - 3)%Z with (pp + mm - 4)%Z in KQ by lia.
    replace (pp + mm - 1 - 4)%Z with (pp + mm - 5)%Z in KQ by lia. replace (mm - 1 - 4)%Z with (mm - 5)%Z in KQ by lia.
    wstepl. replace (bv_swrap 32 (Z.land (pp - 3) 18446744073709551615 + mm)) with (pp - 3 + mm)%Z by (symmetry; apply BzWalkArith4.swrap32_land64_add; lia).
    wstepl. wstepl. wstepl; notrap. wstepl. wstepl; notrap. wstepl; notrap. wstepl. (* [comment removed for export] *)
    mtfa_rdF MA (pp + mm - 2)%Z. (* [comment removed for export] *)
    wstepl. wstepl. (* [comment removed for export] *)
    mtfa_wrF (pp + mm - 1)%Z. (* [comment removed for export] *)
    wstepl; notrap. wstepl; notrap. wstepl. (* [comment removed for export] *)
    mtfa_rdF MA (pp + mm - 3)%Z. (* [comment removed for export] *)
    wstepl. wstepl. (* [comment removed for export] *)
    mtfa_wrF (pp + mm - 2)%Z. (* [comment removed for export] *)
    wstepl; notrap. wstepl; notrap. wstepl. mtfa_rdF MA (pp + mm - 4)%Z. (* [comment removed for export] *)
    wstepl. wstepl. (* [comment removed for export] *)
    mtfa_wrF (pp + mm - 3)%Z. (* [comment removed for export] *)
    wstepl; notrap. wstepl; notrap. wstepl. (* [comment removed for export] *)
    mtfa_rdF MA (pp + mm - 5)%Z. (* [comment removed for export] *)
    wstepl. wstepl. (* [comment removed for export] *)
    mtfa_wrF (pp + mm - 4)%Z. wstepl. (* [comment removed for export] *)
    pose proof (dpureF_set_mtfa _ _ _ _ _ _ (pp + mm - 1) (zget (d_mtfa d) (pp + mm - 2)) DP ltac:(apply MA; lia)) as DP1.
    pose proof (dpureF_set_mtfa _ _ _ _ _ _ (pp + mm - 2) (zget (d_mtfa d) (pp + mm - 3)) DP1 ltac:(apply MA; lia)) as DP2.
    pose proof (dpureF_set_mtfa _ _ _ _ _ _ (pp + mm - 3) (zget (d_mtfa d) (pp + mm - 4)) DP2 ltac:(apply MA; lia)) as DP3.
    pose proof (dpureF_set_mtfa _ _ _ _ _ _ (pp + mm - 4) (zget (d_mtfa d) (pp + mm - 5)) DP3 ltac:(apply MA; lia)) as DP4.
    clear DP1 DP2 DP3.
    revive_all MUL WML AOK.
    wstepl; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      pose proof (NXT ltac:(lia)) as NX. unfold S0F_decCutsL.LFAcF in NX.
      replace (mm - 5)%Z with (mm - 4 - 1)%Z in KQ by lia.
      kq_fold. enter_cutF NX DP4; u10_side MR MA ROW.
    - (* [comment removed for export] *)
      wstepl.
      rewrite (K_LFA_exit F L) in KQ by lia.
      wstepl; if_cases K0; zify_cond_z K0.
      + pose proof (S0F_U10_LFZ pp uc) as NX. unfold S0F_decCutsL.LFZcF in NX.
        replace (mm - 5)%Z with 0%Z in KQ by lia.
        kq_fold. enter_cutF NX DP4; u10_side MR MA ROW.
        + wstepl. pose proof (S0F_U10_LFB_all pp uc (mm - 5)%Z ltac:(lia)) as NX. unfold S0F_decCutsL.LFBcF in NX.
        kq_fold. enter_cutF NX DP4; u10_side MR MA ROW.
    Time Qed.
  Lemma S0F_U10_LFA_all : forall pp uc mm, (5 <= mm <= 16)%Z -> LFAcF pp uc mm.
  Proof.
    intros pp uc mm Hm.
    assert (G : forall n : nat, (n <= 2)%nat -> forall mm', (5 <= mm' <= 8 + 4 * Z.of_nat n)%Z -> (mm' <= 16)%Z -> LFAcF pp uc mm').
    { induction n as [|n IH]; intros Hn mm' H1 H2.
      - apply S0F_U10_LFA. intros; exfalso; lia.
      - apply S0F_U10_LFA. intros H9. apply IH; lia. }
    apply (G 2%nat); lia.
  Qed.
  End M.
End R.
End ACeilS1.
