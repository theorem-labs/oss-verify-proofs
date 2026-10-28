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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require UKit. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzSepTac.
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
  Notation LROcF := (LROcF A F L s J mb). Notation LRIcF := (LRIcF A F L s J mb).
  Let LJ := S0F_U10_LJ A AOK F HC L s J.

  Ltac fprep DM MU DP MR :=
    u10_facts MR DP; prep DM MU DP; lazymatch goal with D : drest_at _ _ _ _ |- _ => unfold r_of in D end; dr_open.
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
  Ltac mtfb_rdF ROW i :=
    let RD := fresh "RD" in let E := fresh "ROWv" in
    lazymatch goal with AR : u32arr _ ?mm (b_s (a_cx A) + 7820)%Z (zw32 ?a _) |- _ =>
      pose proof (ROW i ltac:(lia)) as E;
      pose proof (zw32_read s0segs mm _ a 16 i _ AR ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD;
      wstepl; clear RD end.
  Ltac mtfb_wrF i v :=
    lazymatch goal with AR : u32arr _ ?mm (b_s (a_cx A) + 7820)%Z (zw32 ?a _) |- _ =>
      zw32_sw AR i v ltac:(rewrite unsigned_lit by lia; first [reflexivity | f_equal; lia]) end.
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
  Lemma S0F_U10_LRI : forall lno uc ii j,
    ((j < 15)%Z -> LRIcF lno uc ii (j + 1)) -> ((1 <= ii)%Z -> LROcF lno uc (ii - 1)) -> LRIcF lno uc ii j.
  Proof.
    intros lno uc ii j NXT ROWc. unfold S0F_decCutsL.LRIcF. intros until pb. intros DM FR ST MU WM MI DP FU MR MA NB UCR LNO HII HJ MTI MA0 ROW.
    fprep DM MU DP MR.
    pose proof (mb_reb_range mb lno MTI ii ii ltac:(lia) ltac:(lia)) as R1.
    assert (RV : mb_reb mb lno ii ii = mb_aft mb lno ii) by (unfold mb_reb; rewrite Z.ltb_irrefl; reflexivity).
    hide_all_but_at [S + 3724; S + 7820; usp + -336]%Z.
    pose proof (munch_refl [(S + 3724, S + 7884); (usp + -336, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    kq_intro. rewrite (K_LRI_step F L d s uc ii j) in KQ by lia.
    mtfb_rdF ROW ii. (* [comment removed for export] *)
    wstepl. wstepl. wstepl. wstepl; UKit.u_guard. wstepl. wstepl; UKit.u_guard. wstepl. wstepl; UKit.u_guard. wstepl. wstepl; UKit.u_guard. wstepl; UKit.u_guard. wstepl. (* [comment removed for export] *)
    mtfa_rdF MA (zget (d_mtfbase d) ii + (15 - j))%Z. (* [comment removed for export] *)
    wstepl. (* [comment removed for export] *)
    mtfa_wrF (3855 + 16 * ii - j)%Z. (* [comment removed for export] *)
    wstepl. (* [comment removed for export] *)
    pose proof (dpureF_set_mtfa _ _ _ _ _ _ (3855 + 16 * ii - j) (zget (d_mtfa d) (zget (d_mtfbase d) ii + (15 - j))) DP ltac:(apply MA; lia)) as DP'.
    wstepl; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      revive_all MUL WML AOK.
      pose proof (NXT ltac:(lia)) as NX. unfold S0F_decCutsL.LRIcF in NX.
      kq_fold. enter_cutF NX DP'; u10_side MR MA ROW.
    - (* [comment removed for export] *)
      wstepl. (* [comment removed for export] *)
      mtfb_wrF ii (3840 + 16 * ii)%Z. (* [comment removed for export] *)
      replace (j + 1)%Z with 16%Z in KQ by lia. rewrite (K_LRI_exit F L) in KQ.
      pose proof (dpureF_set_mtfbase _ _ _ _ _ _ (zset (d_mtfbase d) ii (3840 + 16 * ii)) DP') as DP''.
      assert (ROW' : forall D, d_mtfbase D = zset (d_mtfbase d) ii (3840 + 16 * ii) -> mbrow D (mb_reb mb lno (ii - 1))).
      { intros D E. apply (mbrow_ext _ (zfupd (mb_reb mb lno ii) ii (3840 + 16 * ii))).
        - intros l Hl. symmetry. apply (mb_reb_step mb lno ii). lia.
        - apply (mbrow_set_gen d); [exact ROW| exact E]. }
      revive_all MUL WML AOK.
      wstepl. (* [comment removed for export] *)
      wstepl; if_cases K2; zify_cond_z K2.
      + (* [comment removed for export] *)
        pose proof (ROWc ltac:(lia)) as NX. unfold S0F_decCutsL.LROcF in NX.
        kq_fold. enter_cutF NX DP''; u10_side MR MA ROW.
        all: try (apply ROW'; dmodel_cbn; reflexivity).
      + (* [comment removed for export] *)
        wstepl.
        replace (ii - 1)%Z with (-1)%Z in KQ, ROW' by lia. rewrite (K_LRO_exit F L) in KQ.
        pose proof (LJ uc (mb_reb mb lno (-1))) as NX. unfold LJcF in NX.
        kq_fold. enter_cutF NX DP''; u10_side MR MA ROW.
        all: try (apply mtf_home_inv; apply mb_reb_home).
        all: try (apply ROW'; dmodel_cbn; reflexivity).
  Time Qed.
  Lemma S0F_U10_LRI_all : forall lno uc ii, ((1 <= ii)%Z -> LROcF lno uc (ii - 1)) -> forall j, (1 <= j <= 15)%Z -> LRIcF lno uc ii j.
  Proof.
    intros lno uc ii ROWc j Hj.
    assert (G : forall n : nat, (n <= 14)%nat -> LRIcF lno uc ii (15 - Z.of_nat n)%Z).
    { induction n as [|n IH]; intros Hn.
      - apply S0F_U10_LRI; [intros; exfalso; lia| exact ROWc].
      - apply S0F_U10_LRI; [intros _| exact ROWc]. replace (15 - Z.of_nat (Datatypes.S n) + 1)%Z with (15 - Z.of_nat n)%Z by lia. apply IH. lia. }
    replace j with (15 - Z.of_nat (Z.to_nat (15 - j)))%Z by lia. apply G. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0F_U10_LRO : forall lno uc ii, ((1 <= ii)%Z -> LROcF lno uc (ii - 1)) -> LROcF lno uc ii.
  Proof.
    intros lno uc ii ROWc. unfold S0F_decCutsL.LROcF. intros until pb. intros DM FR ST MU WM MI DP FU MR MA NB UCR LNO HII MTI MA0 ROW.
    fprep DM MU DP MR.
    pose proof (mb_reb_range mb lno MTI ii ii ltac:(lia) ltac:(lia)) as R1.
    hide_all_but_at [S + 3724; S + 7820; usp + -336]%Z.
    pose proof (munch_refl [(S + 3724, S + 7884)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    kq_intro. rewrite (K_LRO_row F L d s uc ii) in KQ by lia. rewrite (K_LRI_step F L d s uc ii 0) in KQ by lia.
    rewrite !Z.sub_0_r in KQ.
    wstepl. wstepl. wstepl; UKit.u_guard. wstepl. wstepl. wstepl. (* [comment removed for export] *)
    mtfb_rdF ROW ii. (* [comment removed for export] *)
    wstepl. wstepl. wstepl. wstepl; UKit.u_guard. wstepl. wstepl; UKit.u_guard. wstepl. wstepl; UKit.u_guard. wstepl. wstepl; UKit.u_guard. wstepl; UKit.u_guard. wstepl. (* [comment removed for export] *)
    mtfa_rdF MA (zget (d_mtfbase d) ii + 15)%Z. (* [comment removed for export] *)
    wstepl. (* [comment removed for export] *)
    mtfa_wrF (3855 + 16 * ii)%Z. (* [comment removed for export] *)
    wstepl. (* [comment removed for export] *)
    pose proof (dpureF_set_mtfa _ _ _ _ _ _ (3855 + 16 * ii) (zget (d_mtfa d) (zget (d_mtfbase d) ii + 15)) DP ltac:(apply MA; lia)) as DP'.
    wstepl; if_cases Kc; zify_cond_z Kc; [| exfalso; lia].
    revive_all MUL WML AOK.
    pose proof (S0F_U10_LRI_all lno uc ii ROWc 1 ltac:(lia)) as NX. unfold S0F_decCutsL.LRIcF in NX.
    replace (15 - 0)%Z with 15%Z in KQ by lia. change (0 + 1)%Z with 1%Z in KQ.
    kq_fold. enter_cutF NX DP'; u10_side MR MA ROW.
    all: match goal with |- ?g => idtac "LROX" g end.
  Time Qed.
  Lemma S0F_U10_LRO_all : forall lno uc ii, (0 <= ii <= 15)%Z -> LROcF lno uc ii.
  Proof.
    intros lno uc ii Hii.
    assert (G : forall n : nat, (n <= 15)%nat -> LROcF lno uc (Z.of_nat n)).
    { induction n as [|n IH]; intros Hn.
      - apply S0F_U10_LRO. intros; exfalso; lia.
      - apply S0F_U10_LRO. intros _. replace (Z.of_nat (Datatypes.S n) - 1)%Z with (Z.of_nat n) by lia. apply IH. lia. }
    replace ii with (Z.of_nat (Z.to_nat ii)) by lia. apply G. lia.
  Qed.
  End M.
End R.
End ACeilS1.
