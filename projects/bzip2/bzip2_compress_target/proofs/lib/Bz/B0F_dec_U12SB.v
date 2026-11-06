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

  Section Sm.
  Variables (sym unz ll16_0 ll4_0 : Z -> Z).
  Notation L27c i fa fb fc := (B0F_cut_L27 A Q F i fa fb fc sym unz ll16_0 ll4_0).
  Notation GLc fa fb fc := (B0F_cut_GL A Q F fa fb fc sym unz ll16_0 ll4_0).

  Lemma B0F_U12_L27 : forall i fa fb fc,
    (forall fa' fb' fc', L27c (i + 1)%Z fa' fb' fc') ->
    (forall fa' fb' fc', GLc fa' fb' fc') -> L27c i fa fb fc.
  Proof.
    intros i fa fb fc NXT LAST. unfold B0F_cut_L27. intros until w752. intros DM FRL FRH AF ST MU WM MI DP SF TV V16 V4 VC Hi FU.
    small_facts SF DP.
    pose proof (small_step_pack sym unz ll16_0 ll4_0 (sv_nblock L) (d_origPtr d) ltac:(lia) SYMB HIST HL16
                  ltac:(intros kk; pose proof (HL16R kk); lia) HL4R ORIG i Hi) as SP.
    rewrite TV in SP. cbv zeta in SP. cps_destruct SP as (UC & UCR & VR & VHR & BYR & FAR & FBR & FCR & STEP).
    rewrite (Z.shiftr_div_pow2 _ 16) in VHR by lia. rewrite (Z.shiftr_div_pow2 i 1) in BYR by lia.
    change (2 ^ 16)%Z with 65536%Z in VHR, FAR. change (2 ^ 1)%Z with 2%Z in BYR.
    assert (Euc : (zget (d_ll16 d) i mod 256)%Z = sym i) by (rewrite V16, <- UC; symmetry; apply BzLemmasT.lo8_mod).
    set (ucr := (zget (d_ll16 d) i mod 256)%Z) in *.
    assert (Ek : zget (d_cftabCopy d) ucr = fc (sym i)) by (rewrite Euc; apply VC; lia).
    set (kr := zget (d_cftabCopy d) ucr) in *.
    assert (KR : (0 <= kr < sv_nblock L)%Z) by (rewrite Ek; exact VR).
    assert (KHR : (0 <= kr / 65536 < 16)%Z) by (rewrite Ek; exact VHR).
    assert (OLDR : (0 <= zget (d_ll4 d) (i / 2) < 256)%Z) by (rewrite V4; apply FBR).
    assert (L16iR : (0 <= zget (d_ll16 d) i < 65536)%Z) by (rewrite V16; apply FAR).
    prepS DM MU DP SMALL. lin_al16. unfold r_of in DR. dr_open.
    unfold blk_of in BLK. rewrite SMALL in BLK. cbn [Z.eqb blk_at] in BLK. cps_destruct BLK as (_ & L16A & L16L & L4A & L4L).
    pose proof (act_ll _ _ AOK SMALL) as [(L160 & L161 & L40 & L41) (SEP16 & _ & _ & _ & _ & SEP4 & _ & _ & _ & _ & SEP164)].
    hide_all_but_atF [S + 3152; S + 2124; L16; L4; a_P A; a_P A + 344]%Z.
    pose proof (munch_refl [(S + 2124, S + 3152); (L16, L16 + 200000 * b_n cx); (L4, L4 + 50000 * b_n cx)]%Z m) as MUL.
    pose proof (wmono_refl b0segs m) as WML.
    kq_intro.
    (* [comment removed for export] *)
    brun_to 0xb348c%Z.
    pose proof (zh16_read_lo b0segs m L16 (d_ll16 d) _ i _ L16A ltac:(lia) ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD.
    astep. clear RD. rewrite zxb_lit8 by (unset_Z; lia).
    (* [comment removed for export] *)
    brun_to 0xb34b4%Z.
    pose proof (zw32_read b0segs m (S + 2124) (d_cftabCopy d) 257 ucr _ DRcfc ltac:(unset_Z; lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD.
    astep. clear RD. change (zget (d_cftabCopy d) ucr) with kr. rewrite ?(sx32_of_Z kr) by lia.
    brun_to 0xb34bc%Z.   (* [comment removed for export] *)
    zh16_sh L16A i. (* [comment removed for export] *)
    rewrite (unsigned_lit kr) in L16A by lia.
    (* [comment removed for export] *)
    assert (CFCn : forall q, (0 <= q < 256)%Z -> zget (zset (d_cftabCopy d) ucr (kr + 1)) q = zfupd fc (sym i) (fc (sym i) + 1)%Z q).
    { intros q Hq. rewrite zget_zset, zfupd_eq, Ek, <- Euc. destruct (Z.eqb_spec q ucr); [reflexivity| apply VC; exact Hq]. }
    assert (FAn : forall q, zget (zset (d_ll16 d) i (kr mod 65536)) q = fst (BzModel.set_ll fa fb i (fc (sym i))) q).
    { intros q. unfold BzModel.set_ll. cbn [fst]. rewrite zget_zset, zfupd_eq, land_65535_mod', Ek. destruct (Z.eqb_spec q i); [reflexivity| apply V16]. }
    (* [comment removed for export] *)
    brun; if_cases Kpar; zify_cond_z Kpar.
    -
      (* [comment removed for export] *)
      brun_to 0xb3564%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (zb8_read1 b0segs mm L4 (d_ll4 d) _ (i / 2)%Z _ L4A ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
      astep. clear RD. rewrite zxb_lit8 by lia.
      brun_to 0xb3580%Z.
      rewrite (K_L27_step_odd F L d s i) in KQ by (unset_Z; lia). fold ucr in KQ. fold kr in KQ.
      pose proof (nib_odd_range' (zget (d_ll4 d) (i / 2)) (kr / 65536) OLDR KHR) as XR.
      zb8_sb L4A (i / 2)%Z.
      (* [comment removed for export] *)
      brun_to 0xb358c%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (zw32_read b0segs mm (S + 2124) (d_cftabCopy d) 257 ucr _ DRcfc ltac:(unset_Z; lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
      astep. clear RD. change (zget (d_cftabCopy d) ucr) with kr. rewrite ?(sx32_of_Z kr) by lia.
      brun_to 0xb35a4%Z.
      zw32_sw DRcfc ucr (kr + 1)%Z ltac:(rewrite unsigned_lit by lia; reflexivity).
      pose proof (dpureF_set_ll16 _ _ _ _ _ _ i (kr mod 65536) DP ltac:(change (2 ^ 16)%Z with 65536%Z; apply Z.mod_pos_bound; lia)) as DP2.
      pose proof (dpureF_set_ll4 _ _ _ _ _ _ (i / 2) (Z.lor (Z.land (zget (d_ll4 d) (i / 2)) 15) (kr / 65536 * 16)) DP2 XR) as DP3.
      pose proof (dpureF_set_cftabCopy _ _ _ _ _ _ (zset (d_cftabCopy d) ucr (kr + 1)) DP3) as DP4. clear DP2 DP3.
      assert (FBn : forall y, zget (zset (d_ll4 d) (i / 2) (Z.lor (Z.land (zget (d_ll4 d) (i / 2)) 15) (kr / 65536 * 16))) y
                              = snd (BzModel.set_ll fa fb i (fc (sym i))) y).
      { intros y. unfold BzModel.set_ll. cbn [snd]. rewrite (Z.shiftr_div_pow2 _ 16) by lia. change (2 ^ 16)%Z with 65536%Z.
        rewrite (set_ll4_odd fb i (fc (sym i) / 65536)); [| lia| lia| exact Kpar].
        rewrite zget_zset, zfupd_eq, V4, Ek. destruct (Z.eqb_spec y (i / 2)); [reflexivity| apply V4]. }
      (* [comment removed for export] *)
      brun; if_cases K2; zify_cond_z K2.
      + (* [comment removed for export] *)
        brun_to 0xb3438%Z. try replace (2 * i + 2)%Z with (2 * (i + 1))%Z by lia.
        clear SEP16 SEP4 SEP164. revive_all_smA AOK MUL WML.
        lazymatch type of KQ with kq _ (K_L27 _ _ ?d3 _ _) => blk_goal d3 end.
        { unfold blk_of. rewrite SMALL. cbn [Z.eqb blk_at]. dmodel_cbn. split; [exact SMALL|].
          split; [exact L16A| split; [rewrite zh16_length; lia| split; [exact L4A| rewrite zb8_length; lia]]]. }
        clear L16A L4A. fold_MU MU SMALL.
        pose proof (NXT (fst (BzModel.set_ll fa fb i (fc (sym i)))) (snd (BzModel.set_ll fa fb i (fc (sym i)))) (zfupd fc (sym i) (fc (sym i) + 1)%Z)) as NX.
        unfold B0F_cut_L27 in NX. kq_fold. enter_cutF (NX L _ s JK_) DP4.
        all: try (apply (smallF_frame L d _ _ _ _ _ SF); reflexivity). all: try exact STEP.
        all: try (intros q; dmodel_cbn; apply FAn). all: try (intros y; dmodel_cbn; apply FBn). all: try (intros q Hq; dmodel_cbn; apply CFCn; exact Hq).
        all: try lia.
      + (* [comment removed for export] *)
        brun_to 0xb3634%Z.
        clear SEP16 SEP4 SEP164. revive_all_smA AOK MUL WML.
        lazymatch type of KQ with kq _ (K_L27 _ _ ?d3 _ _) => blk_goal d3 end.
        { unfold blk_of. rewrite SMALL. cbn [Z.eqb blk_at]. dmodel_cbn. split; [exact SMALL|].
          split; [exact L16A| split; [rewrite zh16_length; lia| split; [exact L4A| rewrite zb8_length; lia]]]. }
        clear L16A L4A. fold_MU MU SMALL.
        pose proof (LAST (fst (BzModel.set_ll fa fb i (fc (sym i)))) (snd (BzModel.set_ll fa fb i (fc (sym i)))) (zfupd fc (sym i) (fc (sym i) + 1)%Z)) as NX.
        unfold B0F_cut_GL in NX. replace (i + 1)%Z with (sv_nblock L) in KQ by lia. kq_fold. enter_cutF (NX L _ s JK_) DP4.
        all: try (apply (smallF_frame L d _ _ _ _ _ SF); reflexivity). all: try (replace (sv_nblock L) with (i + 1)%Z by lia; exact STEP).
        all: try (intros q; dmodel_cbn; apply FAn). all: try (intros y; dmodel_cbn; apply FBn). all: try (intros q Hq; dmodel_cbn; apply CFCn; exact Hq).
        all: try lia.
    -
      (* [comment removed for export] *)
      brun_to 0xb3520%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (zb8_read1 b0segs mm L4 (d_ll4 d) _ (i / 2)%Z _ L4A ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
      astep. clear RD. rewrite zxb_lit8 by lia.
      astep. rewrite BzWalkArith4.land_m16_byte by lia.
      brun_to 0xb3580%Z.
      rewrite (K_L27_step_even F L d s i) in KQ by (unset_Z; lia). fold ucr in KQ. fold kr in KQ.
      pose proof (nib_even_range (zget (d_ll4 d) (i / 2)) (kr / 65536) OLDR KHR) as XR.
      zb8_sb L4A (i / 2)%Z.
      (* [comment removed for export] *)
      brun_to 0xb358c%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (zw32_read b0segs mm (S + 2124) (d_cftabCopy d) 257 ucr _ DRcfc ltac:(unset_Z; lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
      astep. clear RD. change (zget (d_cftabCopy d) ucr) with kr. rewrite ?(sx32_of_Z kr) by lia.
      brun_to 0xb35a4%Z.
      zw32_sw DRcfc ucr (kr + 1)%Z ltac:(rewrite unsigned_lit by lia; reflexivity).
      pose proof (dpureF_set_ll16 _ _ _ _ _ _ i (kr mod 65536) DP ltac:(change (2 ^ 16)%Z with 65536%Z; apply Z.mod_pos_bound; lia)) as DP2.
      pose proof (dpureF_set_ll4 _ _ _ _ _ _ (i / 2) (Z.lor (Z.land (zget (d_ll4 d) (i / 2)) 240) (kr / 65536)) DP2 XR) as DP3.
      pose proof (dpureF_set_cftabCopy _ _ _ _ _ _ (zset (d_cftabCopy d) ucr (kr + 1)) DP3) as DP4. clear DP2 DP3.
      assert (FBn : forall y, zget (zset (d_ll4 d) (i / 2) (Z.lor (Z.land (zget (d_ll4 d) (i / 2)) 240) (kr / 65536))) y
                              = snd (BzModel.set_ll fa fb i (fc (sym i))) y).
      { intros y. unfold BzModel.set_ll. cbn [snd]. rewrite (Z.shiftr_div_pow2 _ 16) by lia. change (2 ^ 16)%Z with 65536%Z.
        rewrite (set_ll4_even fb i (fc (sym i) / 65536)); [| lia| lia| exact Kpar].
        rewrite zget_zset, zfupd_eq, V4, Ek. destruct (Z.eqb_spec y (i / 2)); [reflexivity| apply V4]. }
      (* [comment removed for export] *)
      brun; if_cases K2; zify_cond_z K2.
      + (* [comment removed for export] *)
        brun_to 0xb3438%Z. try replace (2 * i + 2)%Z with (2 * (i + 1))%Z by lia.
        clear SEP16 SEP4 SEP164. revive_all_smA AOK MUL WML.
        lazymatch type of KQ with kq _ (K_L27 _ _ ?d3 _ _) => blk_goal d3 end.
        { unfold blk_of. rewrite SMALL. cbn [Z.eqb blk_at]. dmodel_cbn. split; [exact SMALL|].
          split; [exact L16A| split; [rewrite zh16_length; lia| split; [exact L4A| rewrite zb8_length; lia]]]. }
        clear L16A L4A. fold_MU MU SMALL.
        pose proof (NXT (fst (BzModel.set_ll fa fb i (fc (sym i)))) (snd (BzModel.set_ll fa fb i (fc (sym i)))) (zfupd fc (sym i) (fc (sym i) + 1)%Z)) as NX.
        unfold B0F_cut_L27 in NX. kq_fold. enter_cutF (NX L _ s JK_) DP4.
        all: try (apply (smallF_frame L d _ _ _ _ _ SF); reflexivity). all: try exact STEP.
        all: try (intros q; dmodel_cbn; apply FAn). all: try (intros y; dmodel_cbn; apply FBn). all: try (intros q Hq; dmodel_cbn; apply CFCn; exact Hq).
        all: try lia.
      + (* [comment removed for export] *)
        brun_to 0xb3634%Z.
        clear SEP16 SEP4 SEP164. revive_all_smA AOK MUL WML.
        lazymatch type of KQ with kq _ (K_L27 _ _ ?d3 _ _) => blk_goal d3 end.
        { unfold blk_of. rewrite SMALL. cbn [Z.eqb blk_at]. dmodel_cbn. split; [exact SMALL|].
          split; [exact L16A| split; [rewrite zh16_length; lia| split; [exact L4A| rewrite zb8_length; lia]]]. }
        clear L16A L4A. fold_MU MU SMALL.
        pose proof (LAST (fst (BzModel.set_ll fa fb i (fc (sym i)))) (snd (BzModel.set_ll fa fb i (fc (sym i)))) (zfupd fc (sym i) (fc (sym i) + 1)%Z)) as NX.
        unfold B0F_cut_GL in NX. replace (i + 1)%Z with (sv_nblock L) in KQ by lia. kq_fold. enter_cutF (NX L _ s JK_) DP4.
        all: try (apply (smallF_frame L d _ _ _ _ _ SF); reflexivity). all: try (replace (sv_nblock L) with (i + 1)%Z by lia; exact STEP).
        all: try (intros q; dmodel_cbn; apply FAn). all: try (intros y; dmodel_cbn; apply FBn). all: try (intros q Hq; dmodel_cbn; apply CFCn; exact Hq).
        all: try lia.
  Qed.
  Lemma B0F_U12_L27_all : (forall fa fb fc, GLc fa fb fc) -> forall i fa fb fc, L27c i fa fb fc.
  Proof.
    intros LAST.
    assert (G : forall k : nat, forall i fa fb fc, (900000 - Z.of_nat k <= i)%Z -> L27c i fa fb fc).
    { induction k as [|k IH]; intros i fa fb fc Hk.
      - (* [comment removed for export] *)
        unfold B0F_cut_L27. intros until w752. intros DM FRL FRH AF ST MU WM MI DP SF TV V16 V4 VC Hi FU. exfalso.
        cps_pose SF as (_ & _ & _ & _ & _ & NB9 & _). cbn in Hk. lia.
      - apply B0F_U12_L27; [intros fa' fb' fc'; apply IH; lia | exact LAST]. }
    intros i fa fb fc. destruct (Z_lt_le_dec i 0) as [N|P].
    - unfold B0F_cut_L27. intros until w752. intros DM FRL FRH AF ST MU WM MI DP SF TV V16 V4 VC Hi FU. exfalso. lia.
    - apply (G (Z.to_nat 900000)). lia.
  Qed.
  End Sm.
End R.
End ACeilS1.

