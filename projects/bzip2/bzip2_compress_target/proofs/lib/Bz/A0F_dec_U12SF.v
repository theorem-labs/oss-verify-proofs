(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts DecCut DecTac DecTac2 DecAux.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzLemmasT BzLemmasT2 BzWalkArith BzWalkArith2 BzWalkArith3 BzWalkArith4 BzDU9 DecAux12F BzDU5 BzDUM BzDU11 BzDU12F BzDU12S DecAux12S BzDOKS DecTacF3 DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux12F OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU11 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12F OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12S OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux12S OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKS OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFA DecTacFA DecTacFRA A0F_decV A0F_decRet A0F_decRet3 DecTacSA A0F_decCutsE A0F_decCuts12S.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require AsanCut A0F_leafCut A0F_idx A0F_dec_U12SA A0F_dec_U12SB A0F_dec_U12SD.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacSA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCutsE OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCuts12S.
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
  Hypothesis AOK : act_ok AIHI0 A.
  Hypothesis ASH : act_sh DI_A0 A.
  Variable Q : dres -> machine_state -> Prop.
  Variable F : nat.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  Ltac prepS DM MU DP SM :=
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN; pose proof rnums_words_length as RNL; lin_natZ RNL;
    unfold_W14 MU; open_ash ASH AOK;
    lazymatch goal with H : sanchor (b_s _) (a_shs _) |- _ => pose proof (proj2 H : saddr (b_s (a_cx A)) (a_shs A)) as ANS0 end;
    unfold_blk SM MU; open_shb SM; open_dmemF DM; a0img.
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
      let B := fresh "BLK" in assert (B : blk_at a0segs mm cx (blk_of cx D)) end.
  Notation L16 := (b_ll16 (a_cx A)).
  Notation L4 := (b_ll4 (a_cx A)).

  Ltac sh_norm_hyp H :=
    repeat match goal with
    | AN : sanchor ?X ?SHX |- _ =>
        lazymatch type of H with context [((X + ?o) / 8 + 2147450880)%Z] =>
          is_Zlit o; let q := eval vm_compute in (o / 8)%Z in rewrite (sanchor_addr_lit X SHX o q AN eq_refl) in H end
    end.
  Ltac sh_norm_slots :=
    repeat match goal with H : rw_cells _ _ (a_P _ + 496)%Z _ |- _ => progress sh_norm_hyp H end;
    repeat match goal with H : rw_cells _ _ (a_P _) _ |- _ => progress sh_norm_hyp H end.

  Section Sm.
  Variables (sym unz ll16_0 ll4_0 : Z -> Z).
  Notation TAILc fa fb j5 := (A0F_cut_TAIL A Q F fa fb j5 sym unz ll16_0 ll4_0).
  Notation CALLN fa fb j5 := (A0F_call_IDXN A Q F fa fb j5 sym unz ll16_0 ll4_0).
  Notation CALLR fa fb j5 := (A0F_call_IDXR A Q F fa fb j5 sym unz ll16_0 ll4_0).

  (* [comment removed for export] *)
  Lemma A0F_U12_TAIL : forall fa fb j5, CALLN fa fb j5 -> CALLR fa fb j5 -> TAILc fa fb j5.
  Proof.
    intros fa fb j5 HN HR. unfold A0F_cut_TAIL. intros until w720. intros DM FRL FRH AF ST MU WM MI DP SF FAR FBR V16 V4 FU.
    small_facts SF DP. cps_pose HDR as (RND & SBC & OPR).
    prepS DM MU DP SMALL.
    unfold r_of in DR. dr_open. hide_all_but_atF [S; S + 1092; a_P A; a_P A + 496]%Z.
    pose proof (munch_refl [(S, S + 68); (S + 1092, S + 1096); (a_P A, a_P A + 96); (a_P A + 496, a_P A + 728)]%Z m) as MUL. pose proof (wmono_refl a0segs m) as WML.
    kq_intro.
    (* [comment removed for export] *)
    arun_to 0xa6f00%Z. astep. rewrite ?zxb_lit8 by lia.
    arun; if_cases Kbr; zify_cond_z Kbr.
    - (* [comment removed for export] *)
      rewrite (K_TAIL_nr F L d s j5) in KQ by lia.
      arun_to 0xa71e8%Z. astep. rewrite BN. rewrite ?sx32_of_Z by lia.
      arun; if_cases Ktp; zify_cond_z Ktp; [exfalso; lia|].
      arun_to 0x84210%Z. sh_norm. sh_norm_slots.
      revive_all MUL WML AOK. fold_MU MU SMALL.
      pose proof HN as NX. unfold A0F_call_IDXN in NX. kq_fold. enter_cutF (NX L d s JK_) DP.
      all: first [ exact SF | exact FAR | exact FBR | exact V16 | exact V4 | lia ].
    - (* [comment removed for export] *)
      rewrite (K_TAIL_r F L d s j5) in KQ by lia.
      arun_to 0xa6f64%Z. astep. rewrite BN. rewrite ?sx32_of_Z by lia.
      arun; if_cases Ktp; zify_cond_z Ktp; [exfalso; lia|].
      arun_to 0x84210%Z. sh_norm. sh_norm_slots.
      revive_all MUL WML AOK. fold_MU MU SMALL.
      pose proof HR as NX. unfold A0F_call_IDXR in NX. kq_fold. enter_cutF (NX L d s JK_) DP.
      all: first [ exact SF | exact FAR | exact FBR | exact V16 | exact V4 | lia ].
  Qed.
  End Sm.

  Section SmR.
  Hypothesis HRETP3 : A0F_RETP3 A Q.
  Variables (sym unz ll16_0 ll4_0 : Z -> Z).
  Notation L16 := (b_ll16 (a_cx A)).
  Notation L4 := (b_ll4 (a_cx A)).

  (* [comment removed for export] *)
  Lemma A0F_U12_TNR : forall fa fb j5, A0F_cut_IDXNR A Q F fa fb j5 sym unz ll16_0 ll4_0.
  Proof.
    intros fa fb j5. unfold A0F_cut_IDXNR. intros until w720. intros DM FRL FRH AF ST MU WM MI DP SF FAR FBR V16 V4 Kbr FU.
    small_facts SF DP.
    assert (FAo : (0 <= zget (d_ll16 d) (d_origPtr d) < 65536)%Z) by (rewrite V16; apply FAR).
    assert (FBo : (0 <= zget (d_ll4 d) (d_origPtr d / 2) < 256)%Z) by (rewrite V4; apply FBR).
    pose proof (smallF_cftab_range _ _ _ _ _ _ SF) as CFR.
    assert (GLE : BzModel.get_ll (zget (d_ll16 d)) (zget (d_ll4 d)) (d_origPtr d) = get_ll d (d_origPtr d)) by (symmetry; apply get_ll_view).
    pose proof (get_ll_range (zget (d_ll16 d)) (zget (d_ll4 d)) (d_origPtr d) FAo ltac:(rewrite (Z.shiftr_div_pow2 _ 1) by lia; change (2 ^ 1)%Z with 2%Z; lia)) as GR.
    prepS DM MU DP SMALL.
    repeat match goal with H : rw_cells _ _ _ _ |- _ => progress dmodel_cbn_in H end.
    unfold blk_of in BLK. dmodel_cbn_in BLK. rewrite SMALL in BLK. cbn [Z.eqb blk_at] in BLK. cps_destruct BLK as (_ & L16A & L16L & L4A & L4L).
    pose proof (act_ll _ _ AOK SMALL) as [(L160 & L161 & L40 & L41) (SEP16 & _ & _ & _ & _ & SEP4 & _ & _ & _ & _ & _)].
    unfold r_of in DR. dr_open. hide_all_but_atF [S; S + 1092; S + 3152; L16; L4; a_P A; a_P A + 496]%Z.
    pose proof (munch_refl [(S, S + 68); (S + 1092, S + 1096); (a_P A + 496, a_P A + 728)]%Z m) as MUL. pose proof (wmono_refl a0segs m) as WML.
    kq_intro.
    rewrite (signed_lit_small (d_origPtr d)) by lia. rewrite (iif_zw32 (d_cftab d) (d_origPtr d)) by (intros ii Hii; pose proof (CFR ii Hii); lia).
    pose proof (indexIntoF_range (d_origPtr d) (d_cftab d)) as K0R.
    remember (indexIntoF (d_origPtr d) (d_cftab d)) as k0 eqn:Ek0. try rewrite <- Ek0 in KQ.
    (* [comment removed for export] *)
    arun_to 0xa7270%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zh16_read2 a0segs mm L16 (d_ll16 d) _ (d_origPtr d) _ L16A ltac:(lia) ltac:(lia) FAo ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
    astep. clear RD. rewrite zx16_small by lia.
    arun_to 0xa7278%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zb8_read1 a0segs mm L4 (d_ll4 d) _ (d_origPtr d / 2)%Z _ L4A ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
    astep. clear RD. rewrite zxb_lit8 by lia.
    arun_to 0xa7294%Z.
    rewrite (get_ll_asm (zget (d_ll16 d)) (zget (d_ll4 d)) (d_origPtr d)) by lia. rewrite GLE. rewrite GLE in GR.
    remember (get_ll d (d_origPtr d)) as tp2 eqn:Etp. try rewrite <- Etp in KQ.
    (* [comment removed for export] *)
    arun_to 0xa7450%Z.
    clear SEP16 SEP4. revive_all_smA AOK MUL WML.
    lazymatch type of KQ with kq _ (DRet _ _ ?d7 _) => blk_goal d7 end.
    { unfold blk_of, sft_nr. dmodel_cbn. rewrite SMALL. cbn [Z.eqb blk_at]. split; [exact SMALL|].
      split; [exact L16A| split; [exact L16L| split; [exact L4A| exact L4L]]]. }
    clear L16A L4A. fold_MU MU SMALL.
    unfold sft_nr in KQ. kq_fold. enter_cutF (HRETP3 _ _ _ _ JK_) DP; [ ret_nb | ].
    intros _. pose proof (dout_ok_sft_nr L d sym unz ll16_0 ll4_0 j5 k0 tp2 SF Kbr ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as OK.
    unfold sft_nr in OK. dmodel_cbn_in OK. dmodel_cbn. exact OK.
  Qed.

  (* [comment removed for export] *)
  Lemma A0F_U12_TRR : forall fa fb j5, A0F_cut_IDXRR A Q F fa fb j5 sym unz ll16_0 ll4_0.
  Proof.
    intros fa fb j5. unfold A0F_cut_IDXRR. intros until w720. intros DM FRL FRH AF ST MU WM MI DP SF FAR FBR V16 V4 Kbr FU.
    small_facts SF DP.
    assert (FAo : (0 <= zget (d_ll16 d) (d_origPtr d) < 65536)%Z) by (rewrite V16; apply FAR).
    assert (FBo : (0 <= zget (d_ll4 d) (d_origPtr d / 2) < 256)%Z) by (rewrite V4; apply FBR).
    pose proof (smallF_cftab_range _ _ _ _ _ _ SF) as CFR.
    assert (GLE : BzModel.get_ll (zget (d_ll16 d)) (zget (d_ll4 d)) (d_origPtr d) = get_ll d (d_origPtr d)) by (symmetry; apply get_ll_view).
    pose proof (get_ll_range (zget (d_ll16 d)) (zget (d_ll4 d)) (d_origPtr d) FAo ltac:(rewrite (Z.shiftr_div_pow2 _ 1) by lia; change (2 ^ 1)%Z with 2%Z; lia)) as GR.
    prepS DM MU DP SMALL.
    repeat match goal with H : rw_cells _ _ _ _ |- _ => progress dmodel_cbn_in H end.
    unfold blk_of in BLK. dmodel_cbn_in BLK. rewrite SMALL in BLK. cbn [Z.eqb blk_at] in BLK. cps_destruct BLK as (_ & L16A & L16L & L4A & L4L).
    pose proof (act_ll _ _ AOK SMALL) as [(L160 & L161 & L40 & L41) (SEP16 & _ & _ & _ & _ & SEP4 & _ & _ & _ & _ & _)].
    pose proof (act_img_s _ _ AOK : id _) as SEPimg.
    unfold r_of in DR. dr_open. hide_all_but_atF [S; S + 1092; S + 3152; L16; L4; 788152; 804096; a_P A; a_P A + 496]%Z.
    pose proof (munch_refl [(S, S + 68); (S + 1092, S + 1096); (a_P A + 496, a_P A + 728)]%Z m) as MUL. pose proof (wmono_refl a0segs m) as WML.
    kq_intro.
    rewrite (signed_lit_small (d_origPtr d)) by lia. rewrite (iif_zw32 (d_cftab d) (d_origPtr d)) by (intros ii Hii; pose proof (CFR ii Hii); lia).
    pose proof (indexIntoF_range (d_origPtr d) (d_cftab d)) as K0R.
    remember (indexIntoF (d_origPtr d) (d_cftab d)) as k0 eqn:Ek0. try rewrite <- Ek0 in KQ.
    arun_to 0xa6ff0%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zh16_read2 a0segs mm L16 (d_ll16 d) _ (d_origPtr d) _ L16A ltac:(lia) ltac:(lia) FAo ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
    astep. clear RD. rewrite zx16_small by lia.
    arun_to 0xa6ff8%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zb8_read1 a0segs mm L4 (d_ll4 d) _ (d_origPtr d / 2)%Z _ L4A ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
    astep. clear RD. rewrite zxb_lit8 by lia.
    arun_to 0xa7014%Z.
    rewrite (get_ll_asm (zget (d_ll16 d)) (zget (d_ll4 d)) (d_origPtr d)) by lia. rewrite GLE. rewrite GLE in GR.
    remember (get_ll d (d_origPtr d)) as tp2 eqn:Etp. try rewrite <- Etp in KQ.
    (* [comment removed for export] *)
    arun_to 0xa7078%Z.
    lazymatch goal with MUc : munch ?W (a_m0 A) ?mm, SHRc : shzW _ ?W _ 804096%Z _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (SHRc mm 804096%Z MUc ltac:(lia)) as RDs end.
    change (804096 / 8 + 2147450880)%Z with 2147551392%Z in RDs.
    astep. clear RDs. rewrite ?sxb_z8.
    (* [comment removed for export] *)
    arun_to 0xa7088%Z.
    lazymatch goal with RNc : u32arr _ ?mm _ rnums_words |- _ =>
      pose proof (u32arr_read a0segs mm _ rnums_words 0 (Z_to_bv 64 (rNums 0)) _ RNc (rnums_words_nth12 0 ltac:(lia)) ltac:(lia) eq_refl) as RDr end.
    astep. clear RDr. rewrite rNums_0. rewrite ?(sx32_of_Z 619) by lia.
    (* [comment removed for export] *)
    arun_to 0xa7444%Z.
    change (Z.b2z (617 <? 1)) with 0%Z. rewrite ?Z.lxor_0_r.
    arun_to 0xa7450%Z.
    clear SEP16 SEP4 SEPimg. revive_all_smA AOK MUL WML.
    lazymatch type of KQ with kq _ (DRet _ _ ?d7 _) => blk_goal d7 end.
    { unfold blk_of, sft_r. dmodel_cbn. rewrite SMALL. cbn [Z.eqb blk_at]. split; [exact SMALL|].
      split; [exact L16A| split; [exact L16L| split; [exact L4A| exact L4L]]]. }
    clear L16A L4A. fold_MU MU SMALL.
    unfold sft_r in KQ. kq_fold. enter_cutF (HRETP3 _ _ _ _ JK_) DP; [ ret_nb | ].
    intros _. pose proof (dout_ok_sft_r L d sym unz ll16_0 ll4_0 j5 k0 tp2 SF ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as OK.
    unfold sft_r in OK. dmodel_cbn_in OK. dmodel_cbn. exact OK.
  Qed.
  End SmR.

  (* [comment removed for export] *)
  Lemma A0F_U12_S :
    (forall fa fb j5 sym unz ll16_0 ll4_0, A0F_call_IDXN A Q F fa fb j5 sym unz ll16_0 ll4_0) ->
    (forall fa fb j5 sym unz ll16_0 ll4_0, A0F_call_IDXR A Q F fa fb j5 sym unz ll16_0 ll4_0) -> A0F_cut_HSMALL A Q F.
  Proof.
    intros HN HR. apply (A0F_dec_U12SA.A0F_U12_HSMALL A AOK ASH Q F). intros sym unz ll16_0 ll4_0.
    apply (A0F_dec_U12SB.A0F_U12_L27_all A AOK ASH Q F sym unz ll16_0 ll4_0).
    apply (A0F_dec_U12SD.A0F_U12_GL A AOK ASH Q F sym unz ll16_0 ll4_0). intros fa fb j5.
    apply A0F_U12_TAIL; [apply HN| apply HR].
  Qed.
End R.

(* [comment removed for export] *)
Lemma A0F_dec_U12S : forall A, act_ok AIHI0 A -> act_sh DI_A0 A -> forall Q F,
  (forall fa fb j5 sym unz ll16_0 ll4_0, A0F_call_IDXN A Q F fa fb j5 sym unz ll16_0 ll4_0) ->
  (forall fa fb j5 sym unz ll16_0 ll4_0, A0F_call_IDXR A Q F fa fb j5 sym unz ll16_0 ll4_0) -> A0F_cut_HSMALL A Q F.
Proof. intros A AOK ASH Q F. exact (A0F_U12_S A AOK ASH Q F). Qed.
Lemma A0F_dec_U12S_retN : forall A, act_ok AIHI0 A -> act_sh DI_A0 A -> forall Q, A0F_RETP3 A Q ->
  forall F fa fb j5 sym unz ll16_0 ll4_0, A0F_cut_IDXNR A Q F fa fb j5 sym unz ll16_0 ll4_0.
Proof. intros A AOK ASH Q HP3 F fa fb j5 sym unz ll16_0 ll4_0. exact (A0F_U12_TNR A AOK ASH Q F HP3 sym unz ll16_0 ll4_0 fa fb j5). Qed.
Lemma A0F_dec_U12S_retR : forall A, act_ok AIHI0 A -> act_sh DI_A0 A -> forall Q, A0F_RETP3 A Q ->
  forall F fa fb j5 sym unz ll16_0 ll4_0, A0F_cut_IDXRR A Q F fa fb j5 sym unz ll16_0 ll4_0.
Proof. intros A AOK ASH Q HP3 F fa fb j5 sym unz ll16_0 ll4_0. exact (A0F_U12_TRR A AOK ASH Q F HP3 sym unz ll16_0 ll4_0 fa fb j5). Qed.

(* [comment removed for export] *)
Lemma A0F_idx_lift : forall A, act_ok AIHI0 A -> act_sh DI_A0 A -> (AIHI0 <= b_s (a_cx A))%Z ->
  forall (J : jk) (dm : dst) (s : dstrm) (m : word -> option byte)
         (ra gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (Fr : bvmap 5 word) (fc : bv 32),
  dmem DI_A0 (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m (dvF (a_cx A) J dm s) ->
  stk a0segs m (a_lo A) (a_P A) -> munch (W14 A) (a_m0 A) m -> mem_inv a0segs m ->
  AsanCut.aconsts AsanCut.A0C m ->
  evt a0segs (A0F_leafCut.indexIntoF_apost a0segs ra (Z_to_bv 64 (a_P A)) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Fr fc
                (bv_signed a0) (b_s (a_cx A) + 1096) (zw32 (d_cftab dm) 257) (a_lo A) m)
      (MS (mkR ra (Z_to_bv 64 (a_P A)) gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (b_s (a_cx A) + 1096)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x84210) fc None m (seg_rom a0segs)).
Proof.
  intros A AOK ASH HI J dm s m ra gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc DM ST MU MI AC.
  pose proof (alin_core _ _ AOK) as LIN. cbv zeta in LIN.
  assert (PU : bv_unsigned (Z_to_bv 64 (a_P A)) = a_P A) by (apply unsigned_lit; lia).
  pose proof (A0F_idx.A0_indexIntoF ra (Z_to_bv 64 (a_P A)) gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (b_s (a_cx A) + 1096)) a2 a3 a4 a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m (b_s (a_cx A) + 1096)%Z (a_lo A) (zw32 (d_cftab dm) 257)) as SPEC.
  cbv zeta in SPEC. cbn [AsanCut.aci_segs AsanCut.aci_hi AsanCut.aci_c CmpCut.ci_segs CmpCut.ci_hi AsanCut.A0C] in SPEC. rewrite PU in SPEC.
  apply SPEC; clear SPEC.
  - reflexivity.
  - destruct DM as (_ & _ & CF & _). exact CF.
  - rewrite zw32_length_nat. reflexivity.
  - exact MI.
  - exact ST.
  - lia.
  - right. lia.
  - exact AC.
  - lia.
  - lia.
  - destruct ASH as (SHS & _). cbv zeta in SHS. a0img.
    eapply (shzW_sub a0segs (W14 A) [(a_P A - 16, a_P A)]%Z (a_m0 A) m _ _ _ _ SHS MU); [ | lia | lia ].
    unfold sub_fp, W14. intros x Ho. cbn [outside app] in Ho |- *. destruct Ho as (_ & _ & H3 & _). split; [lia | exact I].
Qed.
End ACeilS1.
