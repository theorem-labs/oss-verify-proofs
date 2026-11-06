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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzLemmasT BzLemmasT2 BzWalkArith BzWalkArith2 BzWalkArith3 BzWalkArith4 BzDU9 DecAux12F BzDU5 BzDUM BzDU11 BzDU12F BzDU12S DecAux12S BzDOKS DecTacF3 DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux12F OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU11 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12F OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12S OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux12S OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKS OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFB DecTacFB DecTacFRB B0F_decV B0F_decRet DecTacSB B0F_decCutsE B0F_decCuts12S.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacSB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCutsE OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCuts12S.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecAuxR.

Section ACeilS1. Context {ACEIL__ : ACeil}.
Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok BIHI0 A.
  Hypothesis ASH : act_sh DI_B0 A.
  Variable Q : dres -> machine_state -> Prop.
  Variable F : nat.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  Ltac prepS DM MU DP SM :=
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN; pose proof rnums_words_length as RNL; lin_natZ RNL;
    unfold_W14 MU; open_ash ASH AOK;
    lazymatch goal with H : sanchor (b_s _) (a_shs _) |- _ => pose proof (proj2 H : saddr (b_s (a_cx A)) (a_shs A)) as ANS0 end;
    unfold_blk SM MU; open_shb SM; open_dmemF DM; b0img.
  Ltac fold_MU MU SM :=
    lazymatch type of MU with munch ?W ?ma ?mb =>
      let H := fresh "MUf" in
      assert (H : munch (W14 A) ma mb)
        by (unfold W14, DSTATE_SIZE, blk_ivls; rewrite SM; cbn [Z.eqb app]; exact MU);
      clear MU; rename H into MU end.
  (* [comment removed for export] *)
  Ltac small_facts SF DP :=
    let TS := fresh "TS" in let SM1 := fresh "SM1" in let HDR := fresh "HDR" in let ORIG := fresh "ORIG" in
    let NB1 := fresh "NB1" in let NB9 := fresh "NB9" in let HIST := fresh "HIST" in let SYMB := fresh "SYMB" in
    let UNZ := fresh "UNZ" in let CFP := fresh "CFP" in let HL16 := fresh "HL16" in let HL16R := fresh "HL16R" in let HL4R := fresh "HL4R" in
    cps_pose SF as (TS & SM1 & HDR & ORIG & NB1 & NB9 & HIST & SYMB & UNZ & CFP & HL16 & HL16R & HL4R);
    pose proof (dpureF_small _ _ _ _ _ _ DP) as SMALL; rewrite SM1 in SMALL; symmetry in SMALL;
    pose proof (dpureF_n _ _ _ _ _ _ DP) as BN.

  Ltac blk_goal D :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let B := fresh "BLK" in assert (B : blk_at b0segs mm cx (blk_of cx D)) end.
  Notation L16 := (b_ll16 (a_cx A)).
  Notation L4 := (b_ll4 (a_cx A)).
  (* [comment removed for export] *)
  Ltac lin_al16 :=
    let AL := fresh "AL" in pose proof (act_ok_al _ _ AOK) as AL; unfold ctx_alA in AL;
    let A1 := fresh "ALS" in let A2 := fresh "AL16" in let A3 := fresh "AL4" in
    destruct AL as (A1 & _ & _ & _ & _ & A2 & A3);
    apply DecAuxR.mod16_linR in A1; apply DecAuxR.mod16_linR in A2; apply DecAuxR.mod16_linR in A3;
    let q1 := fresh "qS" in set (q1 := (S / 16)%Z) in A1; clearbody q1;
    let q2 := fresh "q16" in set (q2 := (L16 / 16)%Z) in A2; clearbody q2;
    let q3 := fresh "q4" in set (q3 := (L4 / 16)%Z) in A3; clearbody q3.

  (* [comment removed for export] *)
  Ltac sh_norm_hi :=
    repeat match goal with
    | AN : sanchor ?X ?SHX, H : rw_cells _ _ (a_P _ + 344)%Z _ |- _ =>
        lazymatch type of H with context [((X + ?o) / 8 + 2147450880)%Z] =>
          is_Zlit o; let q := eval vm_compute in (o / 8)%Z in rewrite (sanchor_addr_lit X SHX o q AN eq_refl) in H end
    end.
  (* [comment removed for export] *)
  Definition sep_box (P : Prop) := P.
  Ltac box H := lazymatch type of H with ?P => change P with (sep_box P) in H end.
  Ltac unbox H := unfold sep_box in H.

  Section Sm.
  Variables (sym unz ll16_0 ll4_0 : Z -> Z).
  Notation GLc fa fb fc := (B0F_cut_GL A Q F fa fb fc sym unz ll16_0 ll4_0).
  Notation PRc st fa fb i j := (B0F_cut_PR A Q F st fa fb i j sym unz ll16_0 ll4_0).
  Notation TAILc fa fb j5 := (B0F_cut_TAIL A Q F fa fb j5 sym unz ll16_0 ll4_0).

  (* [comment removed for export] *)
  Lemma B0F_U12_PRstep : forall (st : nat) fa fb i j,
    (forall fa' fb' j', PRc (Datatypes.S st) fa' fb' j j') -> (forall fa' fb' j5, TAILc fa' fb' j5) -> PRc st fa fb i j.
  Proof.
    intros st fa fb i j NXT LAST. unfold B0F_cut_PR. intros until w752. intros DM FRL FRH AF ST MU WM MI DP SF PRS SLT V16 V4 FU.
    small_facts SF DP.
    destruct (small_pr_pack sym unz ll16_0 ll4_0 (sv_nblock L) (d_origPtr d) ltac:(lia) SYMB HIST HL16
                 ltac:(intros kk; pose proof (HL16R kk); lia) HL4R ORIG) as [NCR PF].
    pose proof (PF st SLT) as X. rewrite PRS in X. cbv zeta in X.
    cps_destruct X as (IR & JR & GR & BJR & FBR & FAR & STEP & JO). box JO.
    assert (FAj : (0 <= fa j < 65536)%Z) by (pose proof (FAR j); lia).
    rewrite (Z.shiftr_div_pow2 j 1) in BJR by lia. change (2 ^ 1)%Z with 2%Z in BJR.
    assert (L16j : (0 <= zget (d_ll16 d) j < 65536)%Z) by (rewrite V16; exact FAj).
    assert (L4j : (0 <= zget (d_ll4 d) (j / 2) < 256)%Z) by (rewrite V4; exact BJR).
    assert (IHR : (0 <= i / 65536 < 16)%Z) by lia.
    prepS DM MU DP SMALL. lin_al16. unfold r_of in DR. dr_open.
    unfold blk_of in BLK. rewrite SMALL in BLK. cbn [Z.eqb blk_at] in BLK. cps_destruct BLK as (_ & L16A & L16L & L4A & L4L).
    pose proof (act_ll _ _ AOK SMALL) as [(L160 & L161 & L40 & L41) (SEP16 & _ & _ & _ & _ & SEP4 & _ & _ & _ & _ & SEP164)].
    hide_all_but_atF [S; S + 3152; L16; L4; a_P A; a_P A + 344]%Z.
    pose proof (munch_refl [(L16, L16 + 200000 * b_n cx); (L4, L4 + 50000 * b_n cx); (a_P A + 344, a_P A + 760)]%Z m) as MUL.
    pose proof (wmono_refl b0segs m) as WML.
    kq_intro. replace (Datatypes.S (Z.to_nat (sv_nblock L)) - st)%nat with (Datatypes.S (Z.to_nat (sv_nblock L) - st)) in KQ by lia.
    (* [comment removed for export] *)
    brun_to 0xb37f0%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zh16_read2 b0segs mm L16 (d_ll16 d) _ j _ L16A ltac:(lia) ltac:(lia) L16j ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
    astep. clear RD. rewrite zx16_small by lia.
    (* [comment removed for export] *)
    brun_to 0xb37fc%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zb8_read1 b0segs mm L4 (d_ll4 d) _ (j / 2)%Z _ L4A ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
    astep. clear RD. rewrite zxb_lit8 by lia.
    brun_to 0xb380c%Z.   (* [comment removed for export] *)
    zh16_sh L16A j. (* [comment removed for export] *)
    rewrite (unsigned_lit i) in L16A by lia.
    (* [comment removed for export] *)
    assert (FAn : forall q, zget (zset (d_ll16 d) j (i mod 65536)) q = fst (BzModel.set_ll fa fb j i) q).
    { intros q. unfold BzModel.set_ll. cbn [fst]. rewrite zget_zset, zfupd_eq, land_65535_mod'. destruct (Z.eqb_spec q j); [reflexivity| apply V16]. }
    assert (GLE : BzModel.get_ll (zget (d_ll16 d)) (zget (d_ll4 d)) j = BzModel.get_ll fa fb j) by (apply get_ll_ext; [apply V16| apply V4]).
    (* [comment removed for export] *)
    brun; if_cases Kpar; zify_cond_z Kpar.
    -
      (* [comment removed for export] *)
      brun_to 0xb3854%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (zb8_read1 b0segs mm L4 (d_ll4 d) _ (j / 2)%Z _ L4A ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
      astep. clear RD. rewrite zxb_lit8 by lia.
      brun_to 0xb386c%Z.
      pose proof (nib_odd_range' (zget (d_ll4 d) (j / 2)) (i / 65536) L4j IHR) as XR.
      pose proof (set_ll_odd d j i ltac:(lia) Kpar ltac:(lia) ltac:(lia) L4j) as SL.
      assert (FBn : forall y, zget (zset (d_ll4 d) (j / 2) (Z.lor (Z.land (zget (d_ll4 d) (j / 2)) 15) (i / 65536 * 16))) y
                              = snd (BzModel.set_ll fa fb j i) y).
      { intros y. unfold BzModel.set_ll. cbn [snd]. rewrite (Z.shiftr_div_pow2 _ 16) by lia. change (2 ^ 16)%Z with 65536%Z.
        rewrite (set_ll4_odd fb j (i / 65536)); [| lia| lia| exact Kpar].
        rewrite zget_zset, zfupd_eq, V4. destruct (Z.eqb_spec y (j / 2)); [reflexivity| apply V4]. }
      zb8_sb L4A (j / 2)%Z.
      (* [comment removed for export] *)
      brun_to 0xb3898%Z.
      rewrite (get_ll_asm (zget (d_ll16 d)) (zget (d_ll4 d)) j) by lia. rewrite GLE.
      pose proof (dpureF_set_ll16 _ _ _ _ _ _ j (i mod 65536) DP ltac:(change (2 ^ 16)%Z with 65536%Z; apply Z.mod_pos_bound; lia)) as DP2.
      pose proof (dpureF_set_ll4 _ _ _ _ _ _ (j / 2) (Z.lor (Z.land (zget (d_ll4 d) (j / 2)) 15) (i / 65536 * 16)) DP2 XR) as DP3. clear DP2.
      brun; if_cases K2; zify_cond_z K2.
      + (* [comment removed for export] *)
        assert (NC : Datatypes.S st <> ncyc sym unz (sv_nblock L) (d_origPtr d)) by (unbox JO; intros E; apply K2; apply (proj2 JO); exact E).
        clear SEP16 SEP4 SEP164 JO. revive_all_smA AOK MUL WML.
        blk_goal (sl_odd d j i).
        { unfold blk_of, sl_odd. rewrite SMALL. cbn [Z.eqb blk_at]. dmodel_cbn. split; [exact SMALL|].
          split; [exact L16A| split; [rewrite zh16_length; lia| split; [exact L4A| rewrite zb8_length; lia]]]. }
        clear L16A L4A. fold_MU MU SMALL.
        rewrite (K_PR_step_sl F L d s i j _ _ ltac:(lia) SL) in KQ. rewrite GLE in KQ. unfold sl_odd in KQ.
        pose proof (NXT (fst (BzModel.set_ll fa fb j i)) (snd (BzModel.set_ll fa fb j i)) (BzModel.get_ll fa fb j)) as NX.
        unfold B0F_cut_PR in NX.
        replace (Z.to_nat (sv_nblock L) - st)%nat with (Datatypes.S (Z.to_nat (sv_nblock L)) - Datatypes.S st)%nat in KQ by lia.
        kq_fold. enter_cutF (NX L _ s JK_) DP3.
        all: try (apply (smallF_frame L d _ _ _ _ _ SF); reflexivity). all: try exact STEP.
        all: try (intros q; dmodel_cbn; apply FAn). all: try (intros y; dmodel_cbn; apply FBn).
        all: try (dmodel_cbn; lia).
        all: try lia.
      + (* [comment removed for export] *)
        brun_to 0xb38fc%Z.
        lazymatch goal with H : rw_cells _ _ (a_P A + 344)%Z _ |- _ => rewrite K2 in H end.
        clear SEP16 SEP4 SEP164 JO. revive_all_smA AOK MUL WML.
        blk_goal (sl_odd d j i).
        { unfold blk_of, sl_odd. rewrite SMALL. cbn [Z.eqb blk_at]. dmodel_cbn. split; [exact SMALL|].
          split; [exact L16A| split; [rewrite zh16_length; lia| split; [exact L4A| rewrite zb8_length; lia]]]. }
        clear L16A L4A. fold_MU MU SMALL.
        rewrite (K_PR_exit_sl F L d s i j _ _ ltac:(lia) SL) in KQ. rewrite GLE in KQ. unfold sl_odd in KQ.
        pose proof (LAST (fst (BzModel.set_ll fa fb j i)) (snd (BzModel.set_ll fa fb j i)) (BzModel.get_ll fa fb j)) as NX.
        unfold B0F_cut_TAIL in NX.
        kq_fold. enter_cutF (NX L _ s JK_) DP3.
        all: try (apply (smallF_frame L d _ _ _ _ _ SF); reflexivity).
        all: try (intros q; dmodel_cbn; apply FAn). all: try (intros y; dmodel_cbn; apply FBn).
        all: try (intros q; unfold BzModel.set_ll; cbn [fst]; rewrite zfupd_eq, land_65535_mod'; destruct (Z.eqb q j); [apply Z.mod_pos_bound; lia| apply FAR]).
        all: try (intros y; unfold BzModel.set_ll; cbn [snd]; rewrite (Z.shiftr_div_pow2 _ 16) by lia; change (2 ^ 16)%Z with 65536%Z;
                  rewrite (set_ll4_odd fb j (i / 65536)); [| lia| lia| exact Kpar]; rewrite zfupd_eq; destruct (Z.eqb y (j / 2)); [rewrite <- V4; exact XR| apply FBR]).
        all: try lia.
    -
      (* [comment removed for export] *)
      brun_to 0xb3824%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (zb8_read1 b0segs mm L4 (d_ll4 d) _ (j / 2)%Z _ L4A ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
      astep. clear RD. rewrite zxb_lit8 by lia.
      astep. rewrite BzWalkArith4.land_m16_byte by lia.
      brun_to 0xb386c%Z.
      pose proof (nib_even_range (zget (d_ll4 d) (j / 2)) (i / 65536) L4j IHR) as XR.
      pose proof (set_ll_even d j i ltac:(lia) Kpar ltac:(lia)) as SL.
      assert (FBn : forall y, zget (zset (d_ll4 d) (j / 2) (Z.lor (Z.land (zget (d_ll4 d) (j / 2)) 240) (i / 65536))) y
                              = snd (BzModel.set_ll fa fb j i) y).
      { intros y. unfold BzModel.set_ll. cbn [snd]. rewrite (Z.shiftr_div_pow2 _ 16) by lia. change (2 ^ 16)%Z with 65536%Z.
        rewrite (set_ll4_even fb j (i / 65536)); [| lia| lia| exact Kpar].
        rewrite zget_zset, zfupd_eq, V4. destruct (Z.eqb_spec y (j / 2)); [reflexivity| apply V4]. }
      zb8_sb L4A (j / 2)%Z.
      (* [comment removed for export] *)
      brun_to 0xb3898%Z.
      rewrite (get_ll_asm (zget (d_ll16 d)) (zget (d_ll4 d)) j) by lia. rewrite GLE.
      pose proof (dpureF_set_ll16 _ _ _ _ _ _ j (i mod 65536) DP ltac:(change (2 ^ 16)%Z with 65536%Z; apply Z.mod_pos_bound; lia)) as DP2.
      pose proof (dpureF_set_ll4 _ _ _ _ _ _ (j / 2) (Z.lor (Z.land (zget (d_ll4 d) (j / 2)) 240) (i / 65536)) DP2 XR) as DP3. clear DP2.
      brun; if_cases K2; zify_cond_z K2.
      + (* [comment removed for export] *)
        assert (NC : Datatypes.S st <> ncyc sym unz (sv_nblock L) (d_origPtr d)) by (unbox JO; intros E; apply K2; apply (proj2 JO); exact E).
        clear SEP16 SEP4 SEP164 JO. revive_all_smA AOK MUL WML.
        blk_goal (sl_even d j i).
        { unfold blk_of, sl_even. rewrite SMALL. cbn [Z.eqb blk_at]. dmodel_cbn. split; [exact SMALL|].
          split; [exact L16A| split; [rewrite zh16_length; lia| split; [exact L4A| rewrite zb8_length; lia]]]. }
        clear L16A L4A. fold_MU MU SMALL.
        rewrite (K_PR_step_sl F L d s i j _ _ ltac:(lia) SL) in KQ. rewrite GLE in KQ. unfold sl_even in KQ.
        pose proof (NXT (fst (BzModel.set_ll fa fb j i)) (snd (BzModel.set_ll fa fb j i)) (BzModel.get_ll fa fb j)) as NX.
        unfold B0F_cut_PR in NX.
        replace (Z.to_nat (sv_nblock L) - st)%nat with (Datatypes.S (Z.to_nat (sv_nblock L)) - Datatypes.S st)%nat in KQ by lia.
        kq_fold. enter_cutF (NX L _ s JK_) DP3.
        all: try (apply (smallF_frame L d _ _ _ _ _ SF); reflexivity). all: try exact STEP.
        all: try (intros q; dmodel_cbn; apply FAn). all: try (intros y; dmodel_cbn; apply FBn).
        all: try (dmodel_cbn; lia).
        all: try lia.
      + (* [comment removed for export] *)
        brun_to 0xb38fc%Z.
        lazymatch goal with H : rw_cells _ _ (a_P A + 344)%Z _ |- _ => rewrite K2 in H end.
        clear SEP16 SEP4 SEP164 JO. revive_all_smA AOK MUL WML.
        blk_goal (sl_even d j i).
        { unfold blk_of, sl_even. rewrite SMALL. cbn [Z.eqb blk_at]. dmodel_cbn. split; [exact SMALL|].
          split; [exact L16A| split; [rewrite zh16_length; lia| split; [exact L4A| rewrite zb8_length; lia]]]. }
        clear L16A L4A. fold_MU MU SMALL.
        rewrite (K_PR_exit_sl F L d s i j _ _ ltac:(lia) SL) in KQ. rewrite GLE in KQ. unfold sl_even in KQ.
        pose proof (LAST (fst (BzModel.set_ll fa fb j i)) (snd (BzModel.set_ll fa fb j i)) (BzModel.get_ll fa fb j)) as NX.
        unfold B0F_cut_TAIL in NX.
        kq_fold. enter_cutF (NX L _ s JK_) DP3.
        all: try (apply (smallF_frame L d _ _ _ _ _ SF); reflexivity).
        all: try (intros q; dmodel_cbn; apply FAn). all: try (intros y; dmodel_cbn; apply FBn).
        all: try (intros q; unfold BzModel.set_ll; cbn [fst]; rewrite zfupd_eq, land_65535_mod'; destruct (Z.eqb q j); [apply Z.mod_pos_bound; lia| apply FAR]).
        all: try (intros y; unfold BzModel.set_ll; cbn [snd]; rewrite (Z.shiftr_div_pow2 _ 16) by lia; change (2 ^ 16)%Z with 65536%Z;
                  rewrite (set_ll4_even fb j (i / 65536)); [| lia| lia| exact Kpar]; rewrite zfupd_eq; destruct (Z.eqb y (j / 2)); [rewrite <- V4; exact XR| apply FBR]).
        all: try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma B0F_U12_PR_vac : forall st fa fb i j, (900000 <= Z.of_nat st)%Z -> PRc st fa fb i j.
  Proof.
    intros st fa fb i j Hs. unfold B0F_cut_PR. intros until w752. intros DM FRL FRH AF ST MU WM MI DP SF PRS SLT V16 V4 FU.
    small_facts SF DP.
    destruct (small_pr_pack sym unz ll16_0 ll4_0 (sv_nblock L) (d_origPtr d) ltac:(lia) SYMB HIST HL16
                 ltac:(intros kk; pose proof (HL16R kk); lia) HL4R ORIG) as [NCR _].
    exfalso. lia.
  Qed.

  Lemma B0F_U12_PR_all : (forall fa fb j5, TAILc fa fb j5) ->
    forall (dd st : nat) fa fb i j, (900000 - Z.of_nat st <= Z.of_nat dd)%Z -> PRc st fa fb i j.
  Proof.
    intros LAST dd. induction dd as [|dd IH]; intros st fa fb i j Hd.
    - apply B0F_U12_PR_vac. lia.
    - apply B0F_U12_PRstep; [| exact LAST]. intros fa' fb' j'. apply IH. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma B0F_U12_GL : (forall fa fb j5, TAILc fa fb j5) -> forall fa fb fc, GLc fa fb fc.
  Proof.
    intros LAST fa fb fc. unfold B0F_cut_GL. intros until w752. intros DM FRL FRH AF ST MU WM MI DP SF TV V16 V4 VC FU.
    small_facts SF DP.
    destruct (small_pr_pack sym unz ll16_0 ll4_0 (sv_nblock L) (d_origPtr d) ltac:(lia) SYMB HIST HL16
                 ltac:(intros kk; pose proof (HL16R kk); lia) HL4R ORIG) as [NCR PF].
    pose proof (prst_0 unz ll16_0 ll4_0 (sv_nblock L) (d_origPtr d)) as P0. rewrite TV in P0.
    pose proof (PF 0%nat ltac:(lia)) as X. rewrite P0 in X. cbv zeta in X.
    cps_destruct X as (_ & _ & _ & _ & FBR & FAR & _ & _).
    assert (L16o : (0 <= zget (d_ll16 d) (d_origPtr d) < 65536)%Z) by (rewrite V16; apply FAR).
    assert (L4o : (0 <= zget (d_ll4 d) (d_origPtr d / 2) < 256)%Z) by (rewrite V4; apply FBR).
    assert (GLE : BzModel.get_ll (zget (d_ll16 d)) (zget (d_ll4 d)) (d_origPtr d) = BzModel.get_ll fa fb (d_origPtr d)) by (apply get_ll_ext; [apply V16| apply V4]).
    prepS DM MU DP SMALL. lin_al16. unfold r_of in DR. dr_open.
    unfold blk_of in BLK. rewrite SMALL in BLK. cbn [Z.eqb blk_at] in BLK. cps_destruct BLK as (_ & L16A & L16L & L4A & L4L).
    pose proof (act_ll _ _ AOK SMALL) as [(L160 & L161 & L40 & L41) _].
    hide_all_but_atF [S; S + 3152; L16; L4; a_P A; a_P A + 344]%Z.
    pose proof (munch_refl [(a_P A + 344, a_P A + 760)]%Z m) as MUL. pose proof (wmono_refl b0segs m) as WML.
    kq_intro. rewrite K_L27_PR, GLE in KQ.
    (* [comment removed for export] *)
    brun_to 0xb3718%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zh16_read2 b0segs mm L16 (d_ll16 d) _ (d_origPtr d) _ L16A ltac:(lia) ltac:(lia) L16o ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
    astep. clear RD. rewrite zx16_small by lia.
    brun_to 0xb3720%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zb8_read1 b0segs mm L4 (d_ll4 d) _ (d_origPtr d / 2)%Z _ L4A ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
    astep. clear RD. rewrite zxb_lit8 by lia.
    brun_to 0xb3744%Z. sh_norm. sh_norm_hi.
    rewrite (get_ll_asm (zget (d_ll16 d)) (zget (d_ll4 d)) (d_origPtr d)) by lia. rewrite GLE.
    revive_all_smA AOK MUL WML.
    blk_goal d.
    { unfold blk_of. rewrite SMALL. cbn [Z.eqb blk_at]. split; [exact SMALL|].
      split; [exact L16A| split; [exact L16L| split; [exact L4A| exact L4L]]]. }
    clear L16A L4A. fold_MU MU SMALL.
    pose proof (B0F_U12_PR_all LAST (Z.to_nat 900000) 0%nat fa fb (d_origPtr d) (BzModel.get_ll fa fb (d_origPtr d)) ltac:(lia)) as NX.
    unfold B0F_cut_PR in NX.
    kq_fold. enter_cutF (NX L _ s JK_) DP.
    all: try exact SF. all: try exact P0. all: try exact V16. all: try exact V4. all: try lia.
  Qed.
  End Sm.
End R.
End ACeilS1.

