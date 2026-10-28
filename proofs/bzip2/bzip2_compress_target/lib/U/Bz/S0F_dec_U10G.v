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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDU10. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import S0F_decCutsL DecAux10F S0F_dec_U10J S0F_dec_U10R.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require UKit.
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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require NormFast. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLiaA. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require SasFastF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLia.
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
Local Ltac lia ::= RelLiaA.lia_rf.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
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
  Notation LGHcF := (LGHcF A F L s J mb). Notation LGCcF := (LGCcF A F L s J mb). Notation LGEcF := (LGEcF A F L s J mb).
  Notation LGDcF := (LGDcF A F L s J mb). Notation LROcF := (LROcF A F L s J mb).
  Let LJ := S0F_U10_LJ A AOK F HC L s J.
  Let LRO15 := fun lno uc => S0F_U10_LRO_all A AOK F HC L s J mb lno uc 15 ltac:(lia).

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
      repeat (first [ rewrite zget_zset_same in RD | rewrite zget_zset_other in RD by lia ]);
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
  Lemma S0F_U10_LGD : forall lno uc l, ((2 <= l)%Z -> LGDcF lno uc (l - 1)) -> LGDcF lno uc l.
  Proof.
    intros lno uc l NXT. unfold S0F_decCutsL.LGDcF. intros until pb. intros DM FR ST MU WM MI DP FU MR MA NB UCR LNO HL MTI ROW.
    fprep DM MU DP MR.
    pose proof (mb_mid_range mb lno MTI LNO l l ltac:(lia) ltac:(lia)) as R1.
    pose proof (mb_mid_range mb lno MTI LNO l (l - 1) ltac:(lia) ltac:(lia)) as R2.
    pose proof (mtf_inv_bounds mb MTI (l - 1) ltac:(lia)) as R3. pose proof (mtf_inv_bounds mb MTI l ltac:(lia)) as R4.
    pose proof (mtf_inv_bounds mb MTI lno ltac:(lia)) as R5.
    pose proof (mb_mid_val mb lno l ltac:(lia)) as V1. pose proof (mb_mid_below mb lno l (l - 1) ltac:(lia) ltac:(lia)) as V2.
    assert (V1R : (16 <= mb_mid mb lno l l - 1 <= 4081)%Z) by (rewrite V1; destruct (Z.eqb_spec l lno); lia).
    hide_all_but_at [S + 3724; S + 7820; usp + -336]%Z.
    pose proof (munch_refl [(S + 3724, S + 7884); (usp + -336, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    kq_intro. rewrite (K_LGD_step F L d s uc l) in KQ by lia.
    wstepl. wstepl; UKit.u_guard. wstepl. wstepl; UKit.u_guard. wstepl. wstepl. mtfb_rdF ROW l. (* [comment removed for export] *)
    wstepl. wstepl; UKit.u_guard. wstepl. (* [comment removed for export] *)
    mtfb_wrF l (zget (d_mtfbase d) l - 1)%Z. (* [comment removed for export] *)
    wstepl; UKit.u_guard. wstepl. wstepl. mtfb_rdF ROW (l - 1)%Z. (* [comment removed for export] *)
    wstepl. wstepl; UKit.u_guard. wstepl. wstepl. wstepl; UKit.u_guard. wstepl; UKit.u_guard. wstepl; UKit.u_guard. wstepl. wstepl; UKit.u_guard. wstepl; UKit.u_guard. wstepl. (* [comment removed for export] *)
    mtfa_rdF MA (zget (d_mtfbase d) (l - 1) + 15)%Z. (* [comment removed for export] *)
    wstepl. (* [comment removed for export] *)
    mtfa_wrF (zget (d_mtfbase d) l - 1)%Z. (* [comment removed for export] *)
    wstepl. (* [comment removed for export] *)
    pose proof (dpureF_set_mtfbase _ _ _ _ _ _ (zset (d_mtfbase d) l (zget (d_mtfbase d) l - 1)) DP) as DP1.
    pose proof (dpureF_set_mtfa _ _ _ _ _ _ (zget (d_mtfbase d) l - 1) (zget (d_mtfa d) (zget (d_mtfbase d) (l - 1) + 15)) DP1 ltac:(apply MA; lia)) as DP2.
    assert (ROW1 : forall D, d_mtfbase D = zset (d_mtfbase d) l (zget (d_mtfbase d) l - 1) -> mbrow D (mb_mid mb lno (l - 1))).
    { intros D E. apply (mbrow_ext _ (zfupd (mb_mid mb lno l) l (zget (d_mtfbase d) l - 1))).
      - intros l' Hl'. rewrite (ROW l) by lia. symmetry. apply (mb_mid_step mb lno l). lia.
      - apply (mbrow_set_gen d); [exact ROW| exact E]. }
    wstepl; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      revive_all MUL WML AOK.
      pose proof (NXT ltac:(lia)) as NX. unfold S0F_decCutsL.LGDcF in NX.
      kq_fold. enter_cutF NX DP2; u10_side MR MA ROW.
      all: try (apply ROW1; dmodel_cbn; reflexivity).
    - (* [comment removed for export] *)
      assert (L1 : l = 1%Z) by lia. subst l.
      replace (1 - 1)%Z with 0%Z in KQ by lia. rewrite (K_LGD_exit F L) in KQ. rewrite (K_LGT_eq F L) in KQ. cbv zeta in KQ. dmodel_cbn_in KQ.
      replace (zget (zset (d_mtfbase d) 1 (zget (d_mtfbase d) 1 - 1)) 0) with (zget (d_mtfbase d) 0) in KQ by (rewrite zget_zset_other by lia; reflexivity).
      replace (1 - 1)%Z with 0%Z in V2, R3 by lia.
      pose proof (mtf_inv_bounds mb MTI 0 ltac:(lia)) as R0.
      wstepl. (* [comment removed for export] *)
      mtfb_rdF ROW 0%Z. (* [comment removed for export] *)
      wstepl. wstepl; UKit.u_guard. wstepl. wstepl. (* [comment removed for export] *)
      mtfb_wrF 0%Z (zget (d_mtfbase d) 0 - 1)%Z. (* [comment removed for export] *)
      wstepl; UKit.u_guard. wstepl; UKit.u_guard. wstepl. (* [comment removed for export] *)
      mtfa_wrF (zget (d_mtfbase d) 0 - 1)%Z. (* [comment removed for export] *)
      wstepl. mtfb_rdF ROW 0%Z. (* [comment removed for export] *)
      pose proof (dpureF_set_mtfa _ _ _ _ _ _ (zget (d_mtfbase d) 0 - 1) uc DP2 ltac:(lia)) as DP3.
      pose proof (dpureF_set_mtfbase _ _ _ _ _ _ (zset (zset (d_mtfbase d) 1 (zget (d_mtfbase d) 1 - 1)) 0 (zget (d_mtfbase d) 0 - 1)) DP3) as DP4.
      assert (A0 : mb_aft mb lno 0 = (mb 0 - 1)%Z) by (unfold mb_aft; cbn [Z.leb andb]; destruct (Z.ltb_spec 0 lno); [reflexivity| lia]).
      assert (ROW0 : forall D, d_mtfbase D = zset (zset (d_mtfbase d) 1 (zget (d_mtfbase d) 1 - 1)) 0 (zget (d_mtfbase d) 0 - 1) -> mbrow D (mb_aft mb lno)).
      { intros D E. apply (mbrow_ext _ (zfupd (mb_mid mb lno 0) 0 (zget (d_mtfbase d) 0 - 1))).
        - intros l' Hl'. rewrite (ROW 0%Z) by lia. rewrite V2. rewrite (mb_aft_of_mid mb lno ltac:(lia) l' ltac:(lia)).
          rewrite (mb_mid_bot mb lno 0) by lia. cbn [Z.eqb]. reflexivity.
        - apply (mbrow_set_gen (d_set_mtfbase d (zset (d_mtfbase d) 1 (zget (d_mtfbase d) 1 - 1)))); [apply ROW1; destruct d; reflexivity| rewrite E; destruct d; reflexivity]. }
      wstepl; if_cases K0; zify_cond_z K0.
      + (* [comment removed for export] *)
        replace (zget (d_mtfbase d) 0 - 1 =? 0)%Z with false in KQ by (symmetry; apply Z.eqb_neq; lia).
        revive_all MUL WML AOK.
        pose proof (LJ uc (mb_aft mb lno)) as NX. unfold LJcF in NX.
        kq_fold. enter_cutF NX DP4; u10_side MR MA ROW.
          all: try (apply (mb_aft_inv mb lno MTI); rewrite A0; lia).
        all: try (apply ROW0; dmodel_cbn; reflexivity).
      + (* [comment removed for export] *)
        replace (zget (d_mtfbase d) 0 - 1 =? 0)%Z with true in KQ by (symmetry; apply Z.eqb_eq; lia).
        do 3 wstepl.
        revive_all MUL WML AOK.
        pose proof (LRO15 lno uc) as NX. unfold S0F_decCutsL.LROcF in NX.
        kq_fold. enter_cutF NX DP4; u10_side MR MA ROW.
          all: try (rewrite A0; lia).
        all: try (apply (mbrow_ext _ (mb_aft mb lno)); [intros l' Hl'; rewrite mb_reb_top by lia; reflexivity | apply ROW0; dmodel_cbn; reflexivity]).
  Time Qed.
  Lemma S0F_U10_LGD_all : forall lno uc l, (1 <= l)%Z -> LGDcF lno uc l.
  Proof.
    intros lno uc l Hl.
    assert (G : forall n : nat, LGDcF lno uc (1 + Z.of_nat n)%Z).
    { induction n as [|n IH].
      - apply S0F_U10_LGD. intros; exfalso; lia.
      - apply S0F_U10_LGD. intros _. replace (1 + Z.of_nat (Datatypes.S n) - 1)%Z with (1 + Z.of_nat n)%Z by lia. exact IH. }
    replace l with (1 + Z.of_nat (Z.to_nat (l - 1)))%Z by lia. apply G.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0F_U10_LGE : forall lno uc, LGEcF lno uc.
  Proof.
    intros lno uc. unfold S0F_decCutsL.LGEcF. intros until pb. intros DM FR ST MU WM MI DP FU MR MA MTI ROW NB UCR LNO.
    fprep DM MU DP MR.
    pose proof (mtf_inv_bounds mb MTI lno ltac:(lia)) as R5. pose proof (ROW lno ltac:(lia)) as ROWl.
    hide_all_but_at [S + 3724; S + 7820; usp + -336]%Z.
    pose proof (munch_refl [(S + 3724, S + 7884); (usp + -336, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    kq_intro. rewrite (K_LGE_eq F L d s lno uc) in KQ.
    wstepl. wstepl; UKit.u_guard. (* [comment removed for export] *)
    mtfb_wrF lno (zget (d_mtfbase d) lno + 1)%Z. (* [comment removed for export] *)
    do 6 wstepl.
    pose proof (dpureF_set_mtfbase _ _ _ _ _ _ (zset (d_mtfbase d) lno (zget (d_mtfbase d) lno + 1)) DP) as DP1.
    assert (ROW1 : forall D, d_mtfbase D = zset (d_mtfbase d) lno (zget (d_mtfbase d) lno + 1) -> mbrow D (mb_mid mb lno lno)).
    { intros D E. apply (mbrow_ext _ (zfupd mb lno (zget (d_mtfbase d) lno + 1))).
      - intros l' Hl'. rewrite ROWl. rewrite mb_mid_top, zfupd_eq. destruct (Z.eqb_spec l' lno); [subst; reflexivity| reflexivity].
      - apply (mbrow_set_gen d); [exact ROW| exact E]. }
    revive_all MUL WML AOK.
    pose proof (S0F_U10_LGD_all lno uc lno ltac:(lia)) as NX. unfold S0F_decCutsL.LGDcF in NX.
    kq_fold. enter_cutF NX DP1; u10_side MR MA ROW.
    all: try (apply ROW1; dmodel_cbn; reflexivity).
  Time Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0F_U10_LGC : forall lno uc k, ((mb lno + 1 < k)%Z -> LGCcF lno uc (k - 1)) -> LGCcF lno uc k.
  Proof.
    intros lno uc k NXT. unfold S0F_decCutsL.LGCcF. intros until pb. intros DM FR ST MU WM MI DP FU MR MA MTI ROW NB UCR LNO K.
    fprep DM MU DP MR.
    pose proof (mtf_inv_bounds mb MTI lno ltac:(lia)) as R5. pose proof (ROW lno ltac:(lia)) as ROWl.
    hide_all_but_at [S + 3724; S + 7820]%Z.
    pose proof (munch_refl [(S + 3724, S + 7884)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    kq_intro. rewrite (K_LGC_step F L d s lno k uc) in KQ by lia.
    wstepl. wstepl. wstepl; UKit.u_guard. wstepl; UKit.u_guard. wstepl. wstepl; UKit.u_guard. wstepl. mtfa_rdF MA (k - 1)%Z. (* [comment removed for export] *)
    wstepl. mtfa_wrF k. (* [comment removed for export] *)
    mtfb_rdF ROW lno. (* [comment removed for export] *)
    wstepl. (* [comment removed for export] *)
    pose proof (dpureF_set_mtfa _ _ _ _ _ _ k (zget (d_mtfa d) (k - 1)) DP ltac:(apply MA; lia)) as DP1.
    revive_all MUL WML AOK.
    wstepl; if_cases K2; zify_cond_z K2.
    - pose proof (NXT ltac:(lia)) as NX. unfold S0F_decCutsL.LGCcF in NX.
      kq_fold. enter_cutF NX DP1; u10_side MR MA ROW.
    - pose proof (S0F_U10_LGE lno uc) as NX. unfold S0F_decCutsL.LGEcF in NX.
      rewrite (K_LGC_exit' F L _ s lno (k - 1) uc) in KQ by (rewrite d_mtfbase_set_mtfa; lia).
      kq_fold. enter_cutF NX DP1; u10_side MR MA ROW.
  Time Qed.
  Lemma S0F_U10_LGC_all : forall lno uc k, (mb lno < k <= mb lno + 15)%Z -> LGCcF lno uc k.
  Proof.
    intros lno uc k Hk.
    assert (G : forall n : nat, LGCcF lno uc (mb lno + 1 + Z.of_nat n)%Z).
    { induction n as [|n IH].
      - apply S0F_U10_LGC. intros; exfalso; lia.
      - apply S0F_U10_LGC. intros _. replace (mb lno + 1 + Z.of_nat (Datatypes.S n) - 1)%Z with (mb lno + 1 + Z.of_nat n)%Z by lia. exact IH. }
    replace k with (mb lno + 1 + Z.of_nat (Z.to_nat (k - mb lno - 1)))%Z by lia. apply G.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0F_U10_LGH : LGHcF.
  Proof.
    unfold S0F_decCutsL.LGHcF. intros until pb. intros DM FR ST MU WM MI DP FU MR MA MTI ROW NB NSR.
    fprep DM MU DP MR.
    cps_pose (lno_off_range (sv_nextSym L - 1) ltac:(lia)) as (LNR & OFR & NNE). unfold MTFL_SIZE in LNR, OFR, NNE.
    set (lno := ((sv_nextSym L - 1) / 16)%Z) in *. set (off := ((sv_nextSym L - 1) mod 16)%Z) in *.
    pose proof (mtf_inv_bounds mb MTI lno ltac:(lia)) as R5. pose proof (ROW lno ltac:(lia)) as ROWl.
    hide_all_but_at [S + 3724; S + 7820; usp + -336]%Z.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    kq_intro.
    wstepl. wstepl; UKit.u_guard. (* [comment removed for export] *)
    wstepl. wstepl. wstepl. wstepl; UKit.u_guard. (* [comment removed for export] *)
    mtfb_rdF ROW lno. (* [comment removed for export] *)
    wstepl. flagsb. (* [comment removed for export] *)
    replace ((sv_nextSym L - 1) mod 16)%Z with off by reflexivity.
    wstepl. wstepl. wstepl; UKit.u_guard. wstepl. wstepl; UKit.u_guard. wstepl. wstepl. wstepl. wstepl. wstepl; UKit.u_guard. wstepl; UKit.u_guard. wstepl. mtfb_rdF ROW lno. (* [comment removed for export] *)
    mtfa_rdF MA (zget (d_mtfbase d) lno + off)%Z. (* [comment removed for export] *)
    revive_all MUL WML AOK.
    wstepl; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      pose proof (S0F_U10_LGE lno (zget (d_mtfa d) (zget (d_mtfbase d) lno + off))) as NX. unfold S0F_decCutsL.LGEcF in NX.
      rewrite (K_LGC_exit' F L d s lno) in KQ by (unset_Z; lia).
      kq_fold. enter_cutF NX DP; u10_side MR MA ROW.
      all: try (apply MA; unset_Z; lia).
    - pose proof (S0F_U10_LGC_all lno (zget (d_mtfa d) (zget (d_mtfbase d) lno + off)) (zget (d_mtfbase d) lno + off)%Z ltac:(unset_Z; lia)) as NX.
      unfold S0F_decCutsL.LGCcF in NX.
      kq_fold. enter_cutF NX DP; u10_side MR MA ROW.
      all: try (apply MA; unset_Z; lia).
  Time Qed.
  End M.
End R.
End ACeilS1.
