(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzDefs BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts BzContracts0 BzWalkArith DecCut S0_bzd_out S0_bzd_loop1.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem CmpArith BzCLemmas1.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut BzDOK BzDOKp BzDFrame. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDFrame OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_bzd_out.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_bzd_vspec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_out OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_vspec.S0F_bzd_fnr2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import S0F_bzd_vspec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require U0_bzd_fnrK.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_bzd_loop1.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_bzd_loop3s.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_bzd_loop3s.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_bzd_loop3s S0F_bzd_loop4.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_loop1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_loop3s.S0F_bzd_loop2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_loop3s.S0F_bzd_loop3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_loop3s OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_loop4.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzImg0TacF.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require NormFast. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLiaA RelLia.
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
Local Ltac StoreFast.tlia ::= RelLia.tlia_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Lemma urv_cases : forall rv, (-5 <= rv <= 4)%Z ->
  ((0 <= rv)%Z /\ bv_unsigned (Z_to_bv 64 rv) = rv) \/ ((rv < 0)%Z /\ bv_unsigned (Z_to_bv 64 rv) = (rv + 2^64)%Z).
Proof.
  intros rv H. destruct (Z_lt_dec rv 0) as [L|L].
  - right. split; [exact L|]. apply unsigned_lit_neg. lia.
  - left. split; [lia|]. apply unsigned_lit. lia.
Qed.

Lemma beq_rv4 : forall rv, (-5 <= rv <= 4)%Z -> bv_eqb (Z_to_bv 64 rv) (Z_to_bv 64 4) = (rv =? 4)%Z.
Proof.
  intros rv H. unfold bv_eqb. rewrite (unsigned_lit 4) by lia.
  destruct (urv_cases rv H) as [[A B]|[A B]]; rewrite B; [reflexivity|].
  destruct (Z.eqb_spec rv 4); [lia|]. apply Z.eqb_neq. lia.
Qed.

Section BZD.
  Variable z : bzdctx.
  Hypothesis ZOK : bzdctx_ok z.
  Hypothesis DEC : dec14F_spec DI_S0.
  Hypothesis VFR : FASTR_spec.
  Hypothesis VSNR : SMALLNR_spec.
  Hypothesis VSR : SMALLR_spec.
  Notation cx := (z_cx z).
  (* [comment removed for export] *)
  Hypothesis NN0 : (1 <= b_n (z_cx z))%Z -> b_small (z_cx z) = 0%Z -> b_tt (z_cx z) <> 0%Z.
  Hypothesis NN1 : (1 <= b_n (z_cx z))%Z -> b_small (z_cx z) = 1%Z -> b_ll16 (z_cx z) <> 0%Z /\ b_ll4 (z_cx z) <> 0%Z.
  Notation S := (b_s (z_cx z)). Notation STRM := (b_strm (z_cx z)). Notation usp := (bv_unsigned (z_sp z)).
  Notation DST := (b_dst (z_cx z)). Notation dlen := (b_dlen (z_cx z)). Notation lo := (z_lo z). Notation uspi := (bv_unsigned (z_spi z)).

  Ltac zlin :=
    let CX := ident:(CX) in let Z' := fresh "ZOK" in pose proof ZOK as Z';
    cps_destruct Z' as (CX & USP & LO1 & LO2 & FJL & PAYL & SPI & SPI2);
    let CL := fresh "CL" in pose proof (proj1 CX) as CL; unfold ctx_lin in CL; cbv zeta in CL;
    cps_destruct CL as (LS1 & LS2 & LR1 & LR2 & LR3 & LR4 & LD1 & LD2 & LD3 & LD4 & LP1 & LP2 & _ & LSTRM & LSM & LN & LTT & LL16 & LL4);
    bz_ceil; unfold DSTATE_SIZE, CEILING, STACK_TOP, IMG_HI_MAX, D14 in *;
    pose proof (word_urange (z_sp z)) as USPR; pose proof (word_urange (z_spi z)) as USPIR;
    pose proof crc_words_length as CWL; pose proof rnums_words_length as RNL.
  Ltac ofmkc := cbn [o_cx o_J o_d o_s o_g1 o_s1v o_SP o_gp o_tp o_F o_fc o_KQ o_m0 fmkc] in *.
  Ltac splits := lazymatch goal with |- _ /\ _ => split; splits | |- _ => idtac end.
  (* [comment removed for export] *)
  Ltac hide_disj := repeat match goal with H : ?A \/ ?B |- _ => change (A \/ B) with (id (A \/ B)) in H end.

  (* [comment removed for export] *)
  Definition FLKat (rpc : Z) (f : nat) (C : Z -> Prop) : Prop :=
    forall (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x9 x24 t3 t4 t5 t6 : word) (m : word -> option byte)
           (rv : Z) (J : jk) (d : dst) (s : dstrm) (dbytes rest : list byte),
      FCH z m J d s dbytes rest ->
      munch (WBZ z) (z_m0 z) m -> wmono s0segs (z_m0 z) m -> mem_inv s0segs m ->
      FFACTS z J rv d s -> C rv ->
      (d_state d = BZ_X_OUTPUT -> (b_len cx / 6 - d_blockNo d < Z.of_nat f)%Z) ->
      evt s0segs (bzd_fpost z (K_L f (rv, d, s)))
          (MS (ZR z rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x9 (Z_to_bv 64 rv) x24 t3 t4 t5 t6) (z_F z) (Z_to_bv 64 rpc) (z_fc z) None m (seg_rom s0segs)).

  Lemma bzd_fend : forall f, FLKat 0x15d28 f (fun rv => rv = 4%Z).
  Proof.
    intros f. unfold FLKat. intros until rest. intros CH MU WM MI FA Erv BND.
    cps_destruct CH as (DM & CRC & DE & FR & ST). pose proof DE as DE'. cps_destruct DE' as (DSTA & DL & Edb & Lout).
    pose proof DM as DM'. unfold dmem in DM'. cps_destruct DM' as (HD & NBU & CF & MID & SAV & DR & SM & BLK & PAY & GOT & SV & RNA).
    cbn [di_segs di_got di_stderrp di_crc di_rnums DI_S0] in *.
    cps_destruct FA as (DP & Rst & Rcc & Hav & (OUTW & ENDR & Rrv)).
    pose proof (dpureF_verb _ _ _ _ _ _ DP) as Everb.
    zlin. unfold ZR. unfold FIMG in CRC. clear LTT LL16 LL4. hide_disj.
    dvF_cbn_in HD. dvF_cbn_in MID. dvF_cbn_in SM. rewrite Everb in HD.
    specialize (ENDR Erv). rewrite Erv. rewrite K_L_end.
    wstep. wstep. wstep. if_cases Kc; zify_cond Kc.
    - assert (EQ : d_cccrc d = d_sccrc d)
        by (rewrite <- (sx32_mod32 (d_cccrc d)), <- (sx32_mod32 (d_sccrc d)) by lia; first [rewrite Kc; reflexivity | rewrite <- Kc; reflexivity]).
      rewrite EQ, Z.eqb_refl.
      wstep. wstep. eapply bzd_fepi; [exact ZOK| exact FR| exact ST| exact MU| exact WM| exact MI| exact DM| exact CRC| exact DE| exact DP| first [exact Rrv | unfold BZ_OK, BZ_DATA_ERROR, BZ_STREAM_END; lia]].
    - assert (NE : d_cccrc d <> d_sccrc d) by (intros E; apply Kc; rewrite E; reflexivity).
      replace (d_cccrc d =? d_sccrc d) with false by (symmetry; apply Z.eqb_neq; exact NE).
      wstep. wstep. eapply (bzd_fepi z ZOK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m BZ_DATA_ERROR);
        [exact FR| exact ST| exact MU| exact WM| exact MI| exact DM| exact CRC| exact DE| exact DP| first [exact Rrv | unfold BZ_OK, BZ_DATA_ERROR, BZ_STREAM_END; lia]].
  Qed.

  Lemma bzd_fout : forall f, (forall f', f = Datatypes.S f' -> FLK2 z f') -> FLKat 0x15ca0 f (fun rv => rv <> 4%Z).
  Proof.
    intros f IHf. unfold FLKat. intros until rest. intros CH MU WM MI FA NErv BND.
    cps_destruct CH as (DM & CRC & DE & FR & ST). pose proof DE as DE'. cps_destruct DE' as (DSTA & DL & Edb & Lout).
    pose proof DM as DM'. unfold dmem in DM'. cps_destruct DM' as (HD & NBU & CF & MID & SAV & DR & SM & BLK & PAY & GOT & SV & RNA).
    cbn [di_segs di_got di_stderrp di_crc di_rnums DI_S0] in *.
    cps_destruct FA as (DP & Rst & Rcc & Hav & (OUTW & ENDR & Rrv)).
    pose proof (dpureF_verb _ _ _ _ _ _ DP) as Everb. pose proof (dpureF_small _ _ _ _ _ _ DP) as Esm.
    pose proof (dpureF_n _ _ _ _ _ _ DP) as En. pose proof (dpureF_cbn _ _ _ _ _ _ DP) as [Rbn0 Rcred].
    cbn [bs_len bs_of] in Rcred. pose proof (dpureF_bl _ _ _ _ _ _ DP) as Rbl.
    assert (BNle : (d_blockNo d <= b_len cx / 6)%Z) by (apply Z.div_le_lower_bound; lia).
    zlin. unfold ZR. unfold FIMG in CRC. clear LTT LL16 LL4. hide_disj.
    dvF_cbn_in HD. dvF_cbn_in MID. dvF_cbn_in SM. rewrite Everb in HD.
    wstep. wstep. wstep. if_cases Ks; zify_cond Ks.
    { rewrite (K_L_ret f rv d s NErv) by (unfold BZ_X_OUTPUT; lia).
      eapply bzd_fepi; [exact ZOK| exact FR| exact ST| exact MU| exact WM| exact MI| exact DM| exact CRC| exact DE| exact DP| first [exact Rrv | unfold BZ_OK, BZ_DATA_ERROR, BZ_STREAM_END; lia]]. }
      (* [comment removed for export] *)
      assert (Hst : d_state d = BZ_X_OUTPUT) by (unfold BZ_X_OUTPUT; lia).
      specialize (OUTW Hst). specialize (BND Hst).
      destruct f as [|f']; [exfalso; lia|]. specialize (IHf f' eq_refl).
      assert (BND' : (b_len cx / 6 - d_blockNo d <= Z.of_nat f')%Z) by lia.
      rewrite (K_L_go f' rv d s NErv Hst).
      pose proof OUTW as OUTW'. cps_destruct OUTW' as (Eol & Rtp & NK & Rsnb1 & Ecb & Rsb & Rr01 & Rrnd & Rcf & Eoc & Rn9).
      assert (N1 : (1 <= b_n cx)%Z) by (clear -Rn9 En; lia).
      pose proof (NN0 N1) as NN0'. pose proof (NN1 N1) as NN1'.
      (* [comment removed for export] *)
      wstep. wstep. if_true. wstep. if_true. wstep. wstep.
      assert (Rsm : (0 <= d_small d <= 1)%Z) by (clear -Esm LSM; unfold id in LSM; lia).
      assert (Rrd : (0 <= d_rand d <= 1)%Z) by (clear -Rr01; unfold id in Rr01; lia).
      cbv beta. rewrite (byte_lit_unsigned (d_small d)), (byte_lit_unsigned (d_rand d)) by lia.
      (* [comment removed for export] *)
      wstep. if_cases Ksm; zify_cond Ksm.
      + (* [comment removed for export] *)
        assert (Hsm : b_small cx = 0%Z) by (clear -Ksm Esm LSM Rsm; unfold id in LSM; lia).
        dvF_cbn_in BLK. unfold blk_of in BLK. rewrite Hsm in BLK. cbn [Z.eqb blk_at] in BLK. cps_destruct BLK as (_ & TTA & TTL).
        (* [comment removed for export] *)
        wstep. if_cases Kbr; zify_cond Kbr.
        * (* [comment removed for export] *)
          eapply (U0_bzd_fnrK.S0F_fastnr (fmkc z m J d s f')).
          -- eapply fmkc_ok; [exact ZOK| exact N1| exact DP| exact OUTW| exact Hav| exact DE].
          -- eapply fmkc_okF; [exact ZOK| exact NN0'| exact Hsm].
          -- eapply fmkc_al; eassumption.
          -- eapply (bzd_fjoinF z ZOK DEC N1 NN0' NN1' f' m J d s (r_of d) IHf Hsm DP eq_refl Rcc Rsb BND' CF DR PAY SV FR ST MU WM).
          -- eapply (bzd_fexitF z ZOK m J d s f' (r_of d) Hsm DP eq_refl CF DR PAY SV FR ST MU WM).
          -- unfold DSg. ofmkc. dvF_cbn. rewrite Everb. splits; [exact HD| exact NBU| exact MID| exact SM].
          -- exact DE.
          -- unfold FROf, FGOT. ofmkc. splits; [exact SAV| exact TTA| exact CRC| exact RNA| exact GOT| exact MI].
          -- apply munch_refl.
          -- apply wmono_refl.
          -- ofmkc. lia.
        * (* [comment removed for export] *)
          eapply (VFR (fmkc z m J d s f')).
          -- eapply fmkc_ok; [exact ZOK| exact N1| exact DP| exact OUTW| exact Hav| exact DE].
          -- eapply fmkc_okF; [exact ZOK| exact NN0'| exact Hsm].
          -- eapply fmkc_al; eassumption.
          -- eapply (bzd_fjoinF z ZOK DEC N1 NN0' NN1' f' m J d s (r_of d) IHf Hsm DP eq_refl Rcc Rsb BND' CF DR PAY SV FR ST MU WM).
          -- eapply (bzd_fexitF z ZOK m J d s f' (r_of d) Hsm DP eq_refl CF DR PAY SV FR ST MU WM).
          -- unfold DSg. ofmkc. dvF_cbn. rewrite Everb. splits; [exact HD| exact NBU| exact MID| exact SM].
          -- exact DE.
          -- unfold FROf, FGOT. ofmkc. splits; [exact SAV| exact TTA| exact CRC| exact RNA| exact GOT| exact MI].
          -- apply munch_refl.
          -- apply wmono_refl.
          -- ofmkc. lia.
      + (* [comment removed for export] *)
        assert (Hsm : b_small cx = 1%Z) by (clear -Ksm Esm LSM Rsm; unfold id in LSM; lia).
        dvF_cbn_in BLK. unfold blk_of in BLK. rewrite Hsm in BLK. cbn [Z.eqb blk_at] in BLK. cps_destruct BLK as (_ & L16A & L16L & L4A & L4L).
        (* [comment removed for export] *)
        assert (STA : (STRM mod 16 = 0)%Z) by (pose proof (fmkc_al z ZOK m J d s f') as X; unfold foctx_al in X; cbn [o_cx fmkc] in X; exact (proj2 X)).
        assert (L7 : Z.land STRM 7 = 0%Z) by (change 7%Z with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
        wstep. fstep. wstep. fstep. wstep. rewrite ?L7. try change (Z.b2z (0 <? 1)) with 1%Z. try change (Z.land 1 1) with 1%Z.
        wstep. if_cases Kbr; zify_cond Kbr.
        * (* [comment removed for export] *)
          eapply (VSNR (fmkc z m J d s f')).
          -- eapply fmkc_ok; [exact ZOK| exact N1| exact DP| exact OUTW| exact Hav| exact DE].
          -- eapply fmkc_okS; [exact ZOK| exact NN1'| exact Hsm].
          -- eapply fmkc_al; eassumption.
          -- eapply (bzd_fjoinS z ZOK DEC N1 NN0' NN1' f' m J d s (r_of d) IHf Hsm DP eq_refl Rcc Rsb BND' DR PAY SV FR ST MU WM).
          -- eapply (bzd_fexitS z ZOK m J d s f' (r_of d) Hsm DP eq_refl DR PAY SV FR ST MU WM).
          -- unfold DSg. ofmkc. dvF_cbn. rewrite Everb. splits; [exact HD| exact NBU| exact MID| exact SM].
          -- exact DE.
          -- unfold FROs, FGOT. ofmkc. splits; [exact SAV| exact L16A| exact L4A| exact CF| exact CRC| exact RNA| exact GOT| exact MI].
          -- apply munch_refl.
          -- apply wmono_refl.
          -- ofmkc. lia.
        * (* [comment removed for export] *)
          eapply (VSR (fmkc z m J d s f')).
          -- eapply fmkc_ok; [exact ZOK| exact N1| exact DP| exact OUTW| exact Hav| exact DE].
          -- eapply fmkc_okS; [exact ZOK| exact NN1'| exact Hsm].
          -- eapply fmkc_al; eassumption.
          -- eapply (bzd_fjoinS z ZOK DEC N1 NN0' NN1' f' m J d s (r_of d) IHf Hsm DP eq_refl Rcc Rsb BND' DR PAY SV FR ST MU WM).
          -- eapply (bzd_fexitS z ZOK m J d s f' (r_of d) Hsm DP eq_refl DR PAY SV FR ST MU WM).
          -- unfold DSg. ofmkc. dvF_cbn. rewrite Everb. splits; [exact HD| exact NBU| exact MID| exact SM].
          -- exact DE.
          -- unfold FROs, FGOT. ofmkc. splits; [exact SAV| exact L16A| exact L4A| exact CF| exact CRC| exact RNA| exact GOT| exact MI].
          -- apply munch_refl.
          -- apply wmono_refl.
          -- ofmkc. lia.
  Qed.

  Lemma bzd_fL2 : forall f, (forall f', f = Datatypes.S f' -> FLK2 z f') -> FLK z f /\ FLK2 z f.
  Proof.
    intros f IHf. pose proof (bzd_fout f IHf) as OUT. pose proof (bzd_fend f) as END. unfold FLKat in OUT, END.
    split; unfold FLK, FLK2, FLKp; intros until rest; intros CH MU WM MI FA BND;
      pose proof CH as CH'; cps_destruct CH' as (DM & CRC & DE & FR & ST);
      pose proof DM as DM'; unfold dmem in DM'; cps_destruct DM' as (HD & NBU & CF & MID & SAV & DR & SM & BLK & PAY & GOT & SV & RNA);
      cbn [di_segs di_got di_stderrp di_crc di_rnums DI_S0] in *;
      pose proof FA as FA'; cps_destruct FA' as (DP & Rst & Rcc & Hav & (OUTW & ENDR & Rrv));
      pose proof (dpureF_verb _ _ _ _ _ _ DP) as Everb;
      zlin; unfold ZR; dvF_cbn_in HD; rewrite Everb in HD;
      destruct (Z.eqb_spec rv 4) as [Erv|NErv].
    - subst rv. wstep. wstep. wstep. notrap. wstep. wstep. wstep. wstep. if_false.
      eapply (END _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m 4%Z J d s dbytes rest); first [eassumption | reflexivity].
    - wstep. wstep. wstep. if_cases Kr; zify_cond Kr.
      2:{ exfalso. destruct (urv_cases rv Rrv) as [[A B]|[A B]]; rewrite ?B in Kr; lia. }
      wstep. eapply OUT; eassumption.
    - subst rv. wstep. wstep. wstep. notrap. wstep. wstep. wstep. if_true.
      eapply (END _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m 4%Z J d s dbytes rest); first [eassumption | reflexivity].
    - wstep. wstep. wstep. if_cases Kr; zify_cond Kr.
      { exfalso. destruct (urv_cases rv Rrv) as [[A B]|[A B]]; rewrite ?B in Kr; lia. }
      eapply OUT; eassumption.
  Qed.

  Lemma bzd_fLK2 : forall f, FLK z f /\ FLK2 z f.
  Proof.
    induction f as [|f IH]; apply bzd_fL2.
    - intros f' E. discriminate E.
    - intros f' E. injection E as <-. exact (proj2 IH).
  Qed.

  Lemma bzd_fLK : forall f, FLK z f.
  Proof. intros f. exact (proj1 (bzd_fLK2 f)). Qed.
End BZD.
End ACeilS1.
