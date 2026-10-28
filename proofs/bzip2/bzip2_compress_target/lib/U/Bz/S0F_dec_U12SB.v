(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzContracts BzContracts0 DecCut DecTac DecTac2 DecTacS DecAux. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzLemmasT BzLemmasT2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzWalkArith BzWalkArith2 BzWalkArith3 BzWalkArith4 S0_dec_U13 S0_decCuts S0_decCutsM S0_decCutsE.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_decRet.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAux OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_dec_U13 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_decCuts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_decCutsM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_decCutsE OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet.S0_indexIntoF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU9 BzDU11 BzDU12F. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF DecTacFR DecTacF3 DecAux12F S0F_decRet S0F_decCuts S0F_decCutsM S0F_decCutsE.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU11 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12F OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacFR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAux12F OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCuts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCutsM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCutsE.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDU12S. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import DecAux12S S0F_decCuts12S.
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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require NormFast. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLiaA. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require SasFastF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require SepFast.
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
Local Ltac Lib.ZBridge.flia ::= first [ RangeFast.rc_lia | first [ assumption | Lib.ZBridge.slim; lia | lia ] ].
Local Ltac Lib.ZBridge.mlia ::= first [ RangeFast.rc_lia | Z.div_mod_to_equations; lia ].
Local Ltac Bz.BzTac.mlia ::= first [ RangeFast.rc_lia | Z.div_mod_to_equations; lia ].
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= RelLiaA.lia_rf.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Local Ltac simpl_arr_sizes ::= SasFastF.sas6F_all.
Local Ltac StoreFast.tlia ::= SepFast.tlia_dr.
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
  Notation L16 := (b_ll16 (a_cx A)).
  Notation L4 := (b_ll4 (a_cx A)).

  Ltac simpl_arr_sizes ::= SasFastF.sas6F_all.   (* [comment removed for export] *)
  Ltac prepS DM MU DP SM :=
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN; pose proof rnums_words_length as RNL; lin_natZ RNL;
    unfold W14, D14, DSTATE_SIZE, blk_ivls in MU; rewrite SM in MU; cbn [Z.eqb app b_s b_strm] in MU; open_dmemF DM; s2img.
  Ltac fold_MU MU SM :=
    lazymatch type of MU with munch ?W ?ma ?mb =>
      let H := fresh "MUf" in
      assert (H : munch (W14 DI_S0 cx usp) ma mb)
        by (unfold W14, D14, DSTATE_SIZE, blk_ivls; rewrite SM; cbn [Z.eqb app b_s b_strm di_segs DI_S0]; exact MU);
      clear MU; rename H into MU end.
  Ltac revive_smF SM MUL WML LIN DP :=
    clear LIN;
    let L1 := fresh "LINs" in let L2 := fresh "LINm" in
    pose proof (act_lin_core _ _ AOK) as L1;
    first [ pose proof (act_lin_ll _ _ AOK SM) as L2 | pose proof (act_lin_tt _ _ AOK SM) as L2 ];
    revive_all_sm AOK SM MUL WML;
    clear L1 L2; pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN.
  Ltac blk_goal D :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let B := fresh "BLK" in assert (B : blk_at s0segs mm cx (blk_of cx D)) end.
  (* [comment removed for export] *)
  Ltac small_facts SF DP :=
    let TS := fresh "TS" in let SM1 := fresh "SM1" in let HDR := fresh "HDR" in let ORIG := fresh "ORIG" in
    let NB1 := fresh "NB1" in let NB9 := fresh "NB9" in let HIST := fresh "HIST" in let SYMB := fresh "SYMB" in
    let UNZ := fresh "UNZ" in let CFP := fresh "CFP" in let HL16 := fresh "HL16" in let HL16R := fresh "HL16R" in let HL4R := fresh "HL4R" in
    cps_pose SF as (TS & SM1 & HDR & ORIG & NB1 & NB9 & HIST & SYMB & UNZ & CFP & HL16 & HL16R & HL4R);
    pose proof (dpureF_small _ _ _ _ _ _ DP) as SMALL; rewrite SM1 in SMALL; symmetry in SMALL;
    pose proof (dpureF_n _ _ _ _ _ _ DP) as BN.

  (* [comment removed for export] *)
  Definition sep_box (P : Prop) := P.
  Ltac box H := lazymatch type of H with ?P => change P with (sep_box P) in H end.
  Ltac unbox H := unfold sep_box in H.

  Section Sm.
  Variables (L : dsv) (s : dstrm) (J : jk) (sym unz ll16_0 ll4_0 : Z -> Z).
  Notation L27cF := (L27cF A F L s J sym unz ll16_0 ll4_0). Notation GLcF := (GLcF A F L s J sym unz ll16_0 ll4_0).

  Lemma S0F_U12_L27 : forall i fa fb fc, (0 <= i < sv_nblock L)%Z ->
    (forall fa' fb' fc', (i + 1 < sv_nblock L)%Z -> L27cF (i + 1) fa' fb' fc') ->
    (forall fa' fb' fc', (i + 1)%Z = sv_nblock L -> GLcF fa' fb' fc') -> L27cF i fa fb fc.
  Proof.
    intros i fa fb fc Hi NXT LAST. unfold S0F_decCuts12S.L27cF. intros until pb. intros DM FR ST MU WM MI DP FU SF TV V16 V4 VC IR.
    small_facts SF DP.
    pose proof (small_step_pack sym unz ll16_0 ll4_0 (sv_nblock L) (d_origPtr d) ltac:(lia) SYMB HIST HL16
                  ltac:(intros kk; pose proof (HL16R kk); lia) HL4R ORIG i Hi) as SP.
    rewrite TV in SP. cbv zeta in SP. cps_destruct SP as (UC & UCR & VR & VHR & BYR & FAR & FBR & FCR & STEP).
    rewrite (Z.shiftr_div_pow2 _ 16) in VHR by lia. rewrite (Z.shiftr_div_pow2 i 1) in BYR by lia.
    change (2 ^ 16)%Z with 65536%Z in VHR, FAR. change (2 ^ 1)%Z with 2%Z in BYR.
    (* [comment removed for export] *)
    assert (Euc : (zget (d_ll16 d) i mod 256)%Z = sym i) by (rewrite V16, <- UC; symmetry; apply BzLemmasT.lo8_mod).
    set (ucr := (zget (d_ll16 d) i mod 256)%Z) in *.
    assert (Ek : zget (d_cftabCopy d) ucr = fc (sym i)) by (rewrite Euc; apply VC; lia).
    set (kr := zget (d_cftabCopy d) ucr) in *.
    assert (KR : (0 <= kr < sv_nblock L)%Z) by (rewrite Ek; exact VR).
    assert (KHR : (0 <= kr / 65536 < 16)%Z) by (rewrite Ek; exact VHR).
    assert (OLDR : (0 <= zget (d_ll4 d) (i / 2) < 256)%Z) by (rewrite V4; apply FBR).
    assert (L16iR : (0 <= zget (d_ll16 d) i < 65536)%Z) by (rewrite V16; apply FAR).
    prepS DM MU DP SMALL. unfold r_of in DR. dr_open.
    unfold blk_of in BLK. rewrite SMALL in BLK. cbn [Z.eqb blk_at] in BLK. cps_destruct BLK as (_ & L16A & L16L & L4A & L4L).
    pose proof (act_ll _ _ AOK SMALL) as [(L160 & L161 & L40 & L41) (SEP16 & _ & _ & SEP4 & _ & _ & SEP164)].
    pose proof (act_ok_al _ _ AOK) as AL. unfold ctx_al in AL. destruct AL as (_ & _ & _ & _ & _ & AL16 & _).
    pose proof (Z.div_mod L16 16 ltac:(lia)) as E16. rewrite AL16, Z.add_0_r in E16. set (q16 := (L16 / 16)%Z) in E16. clearbody q16. clear AL16.
    box SEP16. box SEP4. box SEP164.
    hide_all_but_at [usp + -336; S + 3152; S + 2124; L16; L4]%Z.
    pose proof (munch_refl [(S + 2124, S + 3152); (L16, L16 + 200000 * b_n cx); (L4, L4 + 50000 * b_n cx)]%Z m) as MUL.
    pose proof (wmono_refl s0segs m) as WML.
    kq_intro.
    wstepl. wstepl. wstepl. wstepl; flags. (* [comment removed for export] *)
    wstepl; flags. wstepl; notrap. wstepl; notrap. wstepl; notrap.
    wstepl. wstepl. wstepl; notrap.
    pose proof (zh16_read_lo s0segs m L16 (d_ll16 d) _ i _ L16A ltac:(lia) ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD.
    wstepl. clear RD. rewrite zxb_lit8 by (unset_Z; lia). (* [comment removed for export] *)
    wstepl. wstepl. (* [comment removed for export] *)
    wstepl; notrap.
    pose proof (zw32_read s0segs m (S + 2124) (d_cftabCopy d) 257 ucr _ DRcfc ltac:(unset_Z; lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD.
    wstepl. clear RD. (* [comment removed for export] *)
    wstepl. (* [comment removed for export] *)
    wstepl. wstepl. wstepl.
    unbox SEP16. unbox SEP4. unbox SEP164. zh16_sh L16A i. (* [comment removed for export] *) box SEP16. box SEP4. box SEP164.
    fold kr in L16A. rewrite (unsigned_lit kr) in L16A by lia.
    wstepl. (* [comment removed for export] *)
    wstepl; flags. wstepl; flags. wstepl; flags. wstepl; flags. wstepl; flags. wstepl; flags.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zb8_read1 s0segs mm L4 (d_ll4 d) _ (i / 2)%Z _ L4A ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
    (* [comment removed for export] *)
    assert (CFCn : forall q, (0 <= q < 256)%Z -> zget (zset (d_cftabCopy d) ucr (kr + 1)) q = zfupd fc (sym i) (fc (sym i) + 1)%Z q).
    { intros q Hq. rewrite zget_zset, zfupd_eq, Ek, <- Euc. destruct (Z.eqb_spec q ucr); [reflexivity| apply VC; exact Hq]. }
    assert (FAn : forall q, zget (zset (d_ll16 d) i (kr mod 65536)) q = fst (BzModel.set_ll fa fb i (fc (sym i))) q).
    { intros q. unfold BzModel.set_ll. cbn [fst]. rewrite zget_zset, zfupd_eq, land_65535_mod', Ek. destruct (Z.eqb_spec q i); [reflexivity| apply V16]. }
    (* [comment removed for export] *)
    wstepl; if_cases Kpar; zify_cond_z Kpar.
    - (* [comment removed for export] *)
      wstepl; notrap. wstepl; notrap. wstepl; notrap.
      change (zget (d_cftabCopy d) ucr) with kr.
      rewrite (K_L27_step_odd F L d s i) in KQ by (unset_Z; lia). fold ucr in KQ. fold kr in KQ.
      pose proof (nib_odd_range' (zget (d_ll4 d) (i / 2)) (kr / 65536) OLDR KHR) as XR.
      wstepl. wstepl. wstepl; notrap.
      wstepl. clear RD. rewrite zxb_lit8 by lia.
      wstepl. wstepl. wstepl.
      unbox SEP16. unbox SEP4. unbox SEP164. zb8_sb L4A (i / 2)%Z. (* [comment removed for export] *)
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (zw32_read s0segs mm (S + 2124) (d_cftabCopy d) 257 ucr _ DRcfc ltac:(unset_Z; lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
      wstepl. clear RD. change (zget (d_cftabCopy d) ucr) with kr.
      wstepl. wstepl; notrap.
      zw32_sw DRcfc ucr (kr + 1)%Z ltac:(rewrite unsigned_lit by lia; reflexivity). box SEP16. box SEP4. box SEP164.
      pose proof (dpureF_set_ll16 _ _ _ _ _ _ i (kr mod 65536) DP ltac:(change (2 ^ 16)%Z with 65536%Z; apply Z.mod_pos_bound; lia)) as DP2.
      pose proof (dpureF_set_ll4 _ _ _ _ _ _ (i / 2) (Z.lor (Z.land (zget (d_ll4 d) (i / 2)) 15) (kr / 65536 * 16)) DP2 XR) as DP3.
      pose proof (dpureF_set_cftabCopy _ _ _ _ _ _ (zset (d_cftabCopy d) ucr (kr + 1)) DP3) as DP4. clear DP2 DP3.
      assert (FBn : forall y, zget (zset (d_ll4 d) (i / 2) (Z.lor (Z.land (zget (d_ll4 d) (i / 2)) 15) (kr / 65536 * 16))) y
                              = snd (BzModel.set_ll fa fb i (fc (sym i))) y).
      { intros y. unfold BzModel.set_ll. cbn [snd]. rewrite (Z.shiftr_div_pow2 _ 16) by lia. change (2 ^ 16)%Z with 65536%Z.
        rewrite (set_ll4_odd fb i (fc (sym i) / 65536)); [| lia| lia| exact Kpar].
        rewrite zget_zset, zfupd_eq, V4, Ek. destruct (Z.eqb_spec y (i / 2)); [reflexivity| apply V4]. }
      clear SEP16 SEP4 SEP164. revive_smF SMALL MUL WML LIN DP.
      lazymatch type of KQ with kq _ (K_L27 _ _ ?d3 _ _) => blk_goal d3 end.
      { unfold blk_of. rewrite SMALL. cbn [Z.eqb blk_at]. dmodel_cbn. split; [exact SMALL|].
        split; [exact L16A| split; [rewrite zh16_length; lia| split; [exact L4A| rewrite zb8_length; lia]]]. }
      clear L16A L4A. fold_MU MU SMALL.
      wstepl. wstepl. wstepl; if_cases K2; zify_cond_z K2.
      + pose proof (NXT (fst (BzModel.set_ll fa fb i (fc (sym i)))) (snd (BzModel.set_ll fa fb i (fc (sym i)))) (zfupd fc (sym i) (fc (sym i) + 1)%Z) ltac:(lia)) as NX.
        unfold S0F_decCuts12S.L27cF in NX. kq_fold. enter_cutF NX DP4.
        all: try (apply (smallF_frame L d _ _ _ _ _ SF); reflexivity). all: try exact STEP.
        all: try (intros q; dmodel_cbn; apply FAn). all: try (intros y; dmodel_cbn; apply FBn). all: try (intros q Hq; dmodel_cbn; apply CFCn; exact Hq).
        all: try lia.
      + pose proof (LAST (fst (BzModel.set_ll fa fb i (fc (sym i)))) (snd (BzModel.set_ll fa fb i (fc (sym i)))) (zfupd fc (sym i) (fc (sym i) + 1)%Z) ltac:(lia)) as NX.
        unfold S0F_decCuts12S.GLcF in NX. replace (i + 1)%Z with (sv_nblock L) in KQ by lia. kq_fold. enter_cutF NX DP4.
        all: try (apply (smallF_frame L d _ _ _ _ _ SF); reflexivity). all: try (replace (sv_nblock L) with (i + 1)%Z by lia; exact STEP).
        all: try (intros q; dmodel_cbn; apply FAn). all: try (intros y; dmodel_cbn; apply FBn). all: try (intros q Hq; dmodel_cbn; apply CFCn; exact Hq).
        all: try lia.
    - (* [comment removed for export] *)
      wstepl; notrap. wstepl; notrap. wstepl; notrap.
      change (zget (d_cftabCopy d) ucr) with kr.
      rewrite (K_L27_step_even F L d s i) in KQ by (unset_Z; lia). fold ucr in KQ. fold kr in KQ.
      pose proof (nib_even_range (zget (d_ll4 d) (i / 2)) (kr / 65536) OLDR KHR) as XR.
      wstepl. clear RD. rewrite zxb_lit8 by lia.
      wstepl. wstepl. wstepl. wstepl.
      unbox SEP16. unbox SEP4. unbox SEP164. zb8_sb L4A (i / 2)%Z. (* [comment removed for export] *)
      rewrite (land_m16_byte _ OLDR), (Z.mod_small _ 256 XR) in L4A.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (zw32_read s0segs mm (S + 2124) (d_cftabCopy d) 257 ucr _ DRcfc ltac:(unset_Z; lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
      wstepl. clear RD. change (zget (d_cftabCopy d) ucr) with kr.
      wstepl. wstepl; notrap.
      zw32_sw DRcfc ucr (kr + 1)%Z ltac:(rewrite unsigned_lit by lia; reflexivity). box SEP16. box SEP4. box SEP164.
      pose proof (dpureF_set_ll16 _ _ _ _ _ _ i (kr mod 65536) DP ltac:(change (2 ^ 16)%Z with 65536%Z; apply Z.mod_pos_bound; lia)) as DP2.
      pose proof (dpureF_set_ll4 _ _ _ _ _ _ (i / 2) (Z.lor (Z.land (zget (d_ll4 d) (i / 2)) 240) (kr / 65536)) DP2 XR) as DP3.
      pose proof (dpureF_set_cftabCopy _ _ _ _ _ _ (zset (d_cftabCopy d) ucr (kr + 1)) DP3) as DP4. clear DP2 DP3.
      assert (FBn : forall y, zget (zset (d_ll4 d) (i / 2) (Z.lor (Z.land (zget (d_ll4 d) (i / 2)) 240) (kr / 65536))) y
                              = snd (BzModel.set_ll fa fb i (fc (sym i))) y).
      { intros y. unfold BzModel.set_ll. cbn [snd]. rewrite (Z.shiftr_div_pow2 _ 16) by lia. change (2 ^ 16)%Z with 65536%Z.
        rewrite (set_ll4_even fb i (fc (sym i) / 65536)); [| lia| lia| exact Kpar].
        rewrite zget_zset, zfupd_eq, V4, Ek. destruct (Z.eqb_spec y (i / 2)); [reflexivity| apply V4]. }
      clear SEP16 SEP4 SEP164. revive_smF SMALL MUL WML LIN DP.
      lazymatch type of KQ with kq _ (K_L27 _ _ ?d3 _ _) => blk_goal d3 end.
      { unfold blk_of. rewrite SMALL. cbn [Z.eqb blk_at]. dmodel_cbn. split; [exact SMALL|].
        split; [exact L16A| split; [rewrite zh16_length; lia| split; [exact L4A| rewrite zb8_length; lia]]]. }
      clear L16A L4A. fold_MU MU SMALL.
      wstepl. wstepl. wstepl; if_cases K2; zify_cond_z K2.
      + pose proof (NXT (fst (BzModel.set_ll fa fb i (fc (sym i)))) (snd (BzModel.set_ll fa fb i (fc (sym i)))) (zfupd fc (sym i) (fc (sym i) + 1)%Z) ltac:(lia)) as NX.
        unfold S0F_decCuts12S.L27cF in NX. kq_fold. enter_cutF NX DP4.
        all: try (apply (smallF_frame L d _ _ _ _ _ SF); reflexivity). all: try exact STEP.
        all: try (intros q; dmodel_cbn; apply FAn). all: try (intros y; dmodel_cbn; apply FBn). all: try (intros q Hq; dmodel_cbn; apply CFCn; exact Hq).
        all: try lia.
      + pose proof (LAST (fst (BzModel.set_ll fa fb i (fc (sym i)))) (snd (BzModel.set_ll fa fb i (fc (sym i)))) (zfupd fc (sym i) (fc (sym i) + 1)%Z) ltac:(lia)) as NX.
        unfold S0F_decCuts12S.GLcF in NX. replace (i + 1)%Z with (sv_nblock L) in KQ by lia. kq_fold. enter_cutF NX DP4.
        all: try (apply (smallF_frame L d _ _ _ _ _ SF); reflexivity). all: try (replace (sv_nblock L) with (i + 1)%Z by lia; exact STEP).
        all: try (intros q; dmodel_cbn; apply FAn). all: try (intros y; dmodel_cbn; apply FBn). all: try (intros q Hq; dmodel_cbn; apply CFCn; exact Hq).
        all: try lia.
  Time Qed.

  Lemma S0F_U12_L27_all : (1 <= sv_nblock L)%Z -> (forall fa fb fc, GLcF fa fb fc) -> L27cF 0 ll16_0 ll4_0 (psum unz).
  Proof.
    intros Hn LAST.
    assert (G : forall k : nat, (Z.of_nat k < sv_nblock L)%Z -> forall fa fb fc, L27cF (sv_nblock L - 1 - Z.of_nat k)%Z fa fb fc).
    { induction k as [|k IH]; intros Hk fa fb fc.
      - apply S0F_U12_L27; [lia| intros; exfalso; lia| intros fa' fb' fc' _; apply LAST].
      - apply S0F_U12_L27; [lia| intros fa' fb' fc' _| intros; exfalso; lia].
        replace (sv_nblock L - 1 - Z.of_nat (Datatypes.S k) + 1)%Z with (sv_nblock L - 1 - Z.of_nat k)%Z by lia. apply IH. lia. }
    pose proof (G (Z.to_nat (sv_nblock L - 1)) ltac:(lia)) as G0.
    replace (sv_nblock L - 1 - Z.of_nat (Z.to_nat (sv_nblock L - 1)))%Z with 0%Z in G0 by lia. apply G0.
  Qed.
  End Sm.
End R.
End ACeilS1.
