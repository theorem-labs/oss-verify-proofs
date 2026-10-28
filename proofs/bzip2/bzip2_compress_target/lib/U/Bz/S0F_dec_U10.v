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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDU10. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import S0F_decCutsL DecAux10F S0F_dec_U10J S0F_dec_U10R S0F_dec_U10F S0F_dec_U10G.
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
Lemma u10_rw_cells_lw_C8 : forall segs m A pre v post ad,
  rw_cells segs m A (pre ++ C8 v :: post) -> ad = wa (A + Z.of_nat (cells_size pre)) ->
  ov_read_bytes segs m ad 4 = Some (le4 v).
Proof.
  intros segs m A pre v post ad [[Hwf Hb] _] ->.
  apply cells_wf_app in Hwf. destruct Hwf as [Wp _].
  pose proof (cells_bytes_length pre Wp) as Lp.
  rewrite cells_bytes_app in Hb. cbn [cells_bytes cbytes] in Hb.
  rewrite (bytes_at_read segs m A _ (Z.of_nat (cells_size pre)) 4 Hb); [| lia| rewrite !length_app, length_le8, Lp; lia].
  f_equal. rewrite Nat2Z.id, skipn_app, Lp, Nat.sub_diag. rewrite skipn_all2 by (rewrite Lp; lia). cbn [skipn app].
  change (skipn 0 (le8 v ++ cells_bytes post)) with (le8 v ++ cells_bytes post).
  rewrite firstn_app, length_le8. change (4 - 8)%nat with 0%nat. cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.

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

  Ltac mtfa_rdF MA i :=
    let RD := fresh "RD" in let BR := fresh "BR" in
    lazymatch goal with AR : u8arr _ ?mm (b_s (a_cx A) + 3724)%Z (zb8 ?a _) |- _ =>
      pose proof (MA i ltac:(lia)) as BR;
      pose proof (zb8_read1 s0segs mm _ a 4096 i _ AR ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD;
      wstepl; clear RD; rewrite zxb_lit8 by lia end.
  Ltac mtfb_rdF ROW i :=
    let RD := fresh "RD" in let E := fresh "ROWv" in
    lazymatch goal with AR : u32arr _ ?mm (b_s (a_cx A) + 7820)%Z (zw32 ?a _) |- _ =>
      pose proof (ROW i ltac:(lia)) as E;
      pose proof (zw32_read s0segs mm _ a 16 i _ AR ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD;
      wstepl; clear RD end.

  Lemma S0F_U10_HLIT : S0F_cut_HLIT A F.
  Proof.
    unfold S0F_cut_HLIT. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    destruct DI as [ML NSR]. pose proof (ml_nomtfF_of_ML L d ML) as MR. cps_pose (mbrow_of_ML L d ML) as (ROW & MTI & MA).
    u10_facts MR DP. cps_pose ML as (_ & _ & _ & _ & (NBR & _ & _) & _).
    assert (NS256 : (sv_nextSym L <= 256)%Z) by (cps_pose ML as (((_ & NIU & _) & _) & (_ & _ & _ & EOBE & _) & _); lia).
    pose proof (mtf_inv_bounds (mtfb d) MTI 0 ltac:(lia)) as PPR. unfold mtfb in PPR.
    prep DM MU DP. lazymatch goal with D : drest_at _ _ _ _ |- _ => unfold r_of in D end. dr_open.
    hide_all_but_at [S + 3724; S + 7820; usp + -336]%Z.
    pose proof (munch_refl [(usp + -336, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    kq_intro.
    pose proof (u10_rw_cells_lw_C8 s0segs m (usp + -336) [_; _; _; _; _; _; _; _; _; _; _; _] _ _ (Z_to_bv 64 (usp + -240)) FR ltac:(cbn [cells_size csize Nat.add]; unfold wa; f_equal; lia)) as RD.
    wstepl. clear RD. wstepl. (* [comment removed for export] *)
    wstepl; if_cases Knb; zify_cond_z Knb.
    2: { (* [comment removed for export] *)
      rewrite (K_HLIT_ret F L d s) in KQ by lia.
      wstepl. wstepl. wstepl. wstepl. wstepl.
      revive_all MUL WML AOK. kq_fold.
      enter_cutF (S0F_dec_retc A AOK _ _ _ _ JK_) DP; [ ret_nb | apply dpost14_ne; dmodel_cbn; exact NST ]. }
    wstepl. wstepl. wstepl; notrap. wstepl. (* [comment removed for export] *)
    wstepl; if_cases Kg; zify_cond_z Kg.
    2: { (* [comment removed for export] *)
      assert (LNO : (1 <= (sv_nextSym L - 1) / 16 <= 15)%Z) by (pose proof (Z.div_mod (sv_nextSym L - 1) 16 ltac:(lia)); pose proof (Z.mod_pos_bound (sv_nextSym L - 1) 16 ltac:(lia)); lia).
      pose proof (mtf_inv_bounds (mtfb d) MTI ((sv_nextSym L - 1) / 16) ltac:(lia)) as RL. unfold mtfb in RL.
      rewrite (K_HLIT_gen F L d s) in KQ by lia.
      revive_all MUL WML AOK.
      pose proof (S0F_U10_LGH A AOK F HC L s J (mtfb d)) as NX. unfold S0F_decCutsL.LGHcF in NX.
      kq_fold. enter_cutF NX DP.
      all: try assumption. all: try lia. }
    rewrite (K_HLIT_fast F L d s) in KQ by lia.
    wstepl. (* [comment removed for export] *)
    mtfb_rdF ROW 0%Z. (* [comment removed for export] *)
    wstepl. wstepl. wstepl; notrap. wstepl. wstepl. wstepl. wstepl; notrap. wstepl. (* [comment removed for export] *)
    mtfa_rdF MA (zget (d_mtfbase d) 0 + (sv_nextSym L - 1))%Z. (* [comment removed for export] *)
    wstepl. (* [comment removed for export] *)
    wstepl; if_cases K4; zify_cond_z K4.
    - (* [comment removed for export] *)
      wstepl. (* [comment removed for export] *)
      rewrite (K_LFA_exit F L d s) in KQ by lia.
      revive_all MUL WML AOK.
      pose proof (S0F_U10_LFB_all A AOK F HC L s J (mtfb d) (zget (d_mtfbase d) 0) (zget (d_mtfa d) (zget (d_mtfbase d) 0 + (sv_nextSym L - 1))) (sv_nextSym L - 1) ltac:(lia)) as NX.
      unfold S0F_decCutsL.LFBcF in NX.
      kq_fold. enter_cutF NX DP.
      all: try assumption. all: try reflexivity. all: try (apply MA; lia). all: try lia.
    - (* [comment removed for export] *)
      do 3 wstepl.
      revive_all MUL WML AOK.
      pose proof (S0F_U10_LFA_all A AOK F HC L s J (mtfb d) (zget (d_mtfbase d) 0) (zget (d_mtfa d) (zget (d_mtfbase d) 0 + (sv_nextSym L - 1))) (sv_nextSym L) ltac:(lia)) as NX.
      unfold S0F_decCutsL.LFAcF in NX.
      replace (sv_nextSym L - 1)%Z with (sv_nextSym L - 1)%Z in KQ by lia.
      kq_fold. enter_cutF NX DP.
      all: try assumption. all: try reflexivity. all: try (apply MA; lia). all: try lia.
  Time Qed.
  End M.
End R.

Lemma S0F_dec_U10 : forall A, act_ok 320 A -> forall F, S0F_cut_HMTFC A F -> S0F_cut_HLIT A F.
Proof. intros A AOK F HC. exact (S0F_U10_HLIT A AOK F HC). Qed.

End ACeilS1.
