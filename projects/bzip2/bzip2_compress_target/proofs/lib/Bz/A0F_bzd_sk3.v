(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzTac BzDefs BzInv BzTables BzLemmasT BzLemmasMtf BzContracts BzWalkArith DecCut S0_bzd_out S0_bzd_loop1 BzSepTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem CmpArith BzCLemmas1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut BzDOK BzDOKp BzDFrame DecCutF DecTacF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDFrame OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import S0F_bzd_out S0F_bzd_outS S0F_bzd_loop1.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit DecCutA DecCutFA A0F_decV A0F_bzdV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0F_bzd_skV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0F_bzd_loop3s.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0F_bzd_loop5.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require A0F_bzd_sk1 A0F_bzd_sk2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Ltac unhide_disj := repeat match goal with H : id (?A \/ ?B) |- _ => unfold id in H end.
Ltac hide_disj := repeat match goal with H : ?A \/ ?B |- _ => change (A \/ B) with (id (A \/ B)) in H end.
Local Ltac tlia ::= first [ Zify.zify; xlia zchecker
                         | sf_unhide; unhide_disj;
                           first [ zify_prune_neg; Zify.zify; xlia zchecker
                                 | zify_prune_plain; Zify.zify; xlia zchecker
                                 | Zify.zify; xlia zchecker ] ].
Local Ltac tslia ::= tslia_sep.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NormFast RelLiaA SasFastF RelLiaS.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
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
Local Ltac tlia ::= RelLiaS.tlia_bzd_r.
Local Ltac BzSepTac.tlia1 ::= RelLiaS.tlia1_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold; AsanKit.sh_norm.
Section ACeilS1. Context {ACEIL__ : ACeil}.

Section BZD.
  Variable z : bzdctx.
  Variable SHS : Z. Variable w0 : word.
  Variable QF : Z * dst * dstrm -> machine_state -> Prop.
  Hypothesis ZOK : bzdctx_okA z SHS.
  Notation cx := (z_cx z).
  Notation S := (b_s (z_cx z)). Notation STRM := (b_strm (z_cx z)). Notation SRC := (b_src (z_cx z)). Notation len := (b_len (z_cx z)).
  Notation DST := (b_dst (z_cx z)). Notation dlen := (b_dlen (z_cx z)). Notation n := (b_n (z_cx z)).
  Notation TT := (b_tt (z_cx z)). Notation L16 := (b_ll16 (z_cx z)). Notation L4 := (b_ll4 (z_cx z)).
  Notation usp := (bv_unsigned (z_sp z)). Notation uspi := (bv_unsigned (z_spi z)). Notation lo := (z_lo z).
  Notation KRet := (A0_KRet z QF). Notation KCall := (A0_KCall z SHS w0 QF).
  Notation FCHA := (A0F_bzd_skV.FCHA z SHS w0). Notation FIMGA := A0F_bzd_skV.FIMGA. Notation FDESTA := (A0F_bzd_skV.FDESTA z).
  Notation WLA := (A0F_bzd_skV.WLA z). Notation FSAVA := (A0F_bzd_skV.FSAVA z).
  Notation fmkcA := (A0F_bzd_skV.fmkcA z QF).

  (* [comment removed for export] *)
  Ltac hide H := lazymatch type of H with ?T => change T with (id T) in H end.
  Ltac splits := lazymatch goal with |- _ /\ _ => split; splits | |- _ => idtac end.
  Ltac ofmkc := cbn [o_cx o_J o_d o_s o_g1 o_s1v o_SP o_gp o_tp o_F o_fc o_KQ o_m0 A0F_bzd_skV.fmkcA] in *.
  (* [comment removed for export] *)
  Ltac zok :=
    let Z' := fresh "ZOK" in pose proof ZOK as Z';
    cps_destruct Z' as (((LS1 & LS2) & (LM1 & LM2) & (LR1 & LR2 & LR3) & (LD1 & LD2) & LDL & (AL1 & AL2) & LSM & LN & (LO1 & LO2 & LO3) & SPI & SPI2 & PAYL)
                        & ANS & (D_SM & D_SR & D_SD & D_MR & D_MD & D_RD & IA_S & IA_M & IA_D) & BTT & B16 & B4 & B164);
    unfold disj, bzd_img_apart in *; pose proof alloc_ceiling_range as ACR;
    pose proof (word_urange (z_sp z)) as USPR; pose proof (word_urange (z_spi z)) as USPIR;
    pose proof crc_words_length as CWL; pose proof rnums_words_length as RNL;
    lazymatch goal with HA : sanchor _ _ |- _ => pose proof (proj2 HA : saddr S SHS) as ANS0 end.
  Hypothesis VFNR : FASTNR_aspec. Hypothesis VFR : FASTR_aspec.
  Hypothesis VSNR : SMALLNR_aspec. Hypothesis VSR : SMALLR_aspec.
  (* [comment removed for export] *)
  Hypothesis NN0 : (1 <= n)%Z -> b_small cx = 0%Z -> TT <> 0%Z.
  Hypothesis NN1 : (1 <= n)%Z -> b_small cx = 1%Z -> L16 <> 0%Z /\ L4 <> 0%Z.
  Hypothesis SHL : bzd_sh z WLA (z_m0 z).
  Notation FLKA := (A0F_bzd_skV.FLKA z SHS w0 QF).
  Let bzd_fepiA := A0F_bzd_sk1.bzd_fepiA z SHS w0 QF ZOK.
  Let fmkc_okA := A0F_bzd_sk1.fmkc_okA z SHS QF ZOK.
  Let fmkc_okFA := A0F_bzd_sk1.fmkc_okFA z SHS QF.
  Let fmkc_okSA := A0F_bzd_sk1.fmkc_okSA z SHS QF.

  Ltac cl := cbn [disjoint_from]; unfold A0F_bzd_skV.FSAVA; simpl_sizes; repeat split; try exact I; lia.
  (* [comment removed for export] *)
  Lemma dispatch_transport : forall (mm m' : word -> option byte) (dbytes : list byte) (rr : drest) (k : blk) (cf : list word) (c1 c2 c3 : list cell) (g1 sv : word),
    munch ([(uspi, uspi + 296)])%Z mm m' -> wmono a0segs mm m' ->
    (forall A n0, blk_range cx A n0 -> (0 < A /\ A + n0 <= alloc_ceiling)%Z) ->
    bytes_at a0segs mm SRC (z_payload z) -> u8arr a0segs mm DST dbytes -> Z.of_nat (length dbytes) = dlen ->
    u32arr a0segs mm 802816 crc_words -> u32arr a0segs mm 804096 rnums_words ->
    ro_cells a0segs mm 788152 [C8 (Z_to_bv 64 784720); C8 g1; C8 (Z_to_bv 64 784728); C8 (Z_to_bv 64 802816); C8 (Z_to_bv 64 804096)] -> ro_cells a0segs mm 784720 [C8 sv] ->
    rw_cells a0segs mm (uspi + 296) FSAVA -> u32arr a0segs mm (S + 1096) cf -> length cf = 257%nat ->
    drest_at a0segs mm S rr -> blk_at a0segs mm cx k ->
    rw_cells a0segs mm (S + 1092) c1 -> cells_size c1 = 4%nat -> rw_cells a0segs mm (S + 3152) c2 -> cells_size c2 = 44%nat ->
    rw_cells a0segs mm (S + 64036) c3 -> cells_size c3 = 108%nat -> stk a0segs mm lo uspi ->
    bytes_at a0segs m' SRC (z_payload z) /\ u8arr a0segs m' DST dbytes /\
    u32arr a0segs m' 802816 crc_words /\ u32arr a0segs m' 804096 rnums_words /\
    ro_cells a0segs m' 788152 [C8 (Z_to_bv 64 784720); C8 g1; C8 (Z_to_bv 64 784728); C8 (Z_to_bv 64 802816); C8 (Z_to_bv 64 804096)] /\ ro_cells a0segs m' 784720 [C8 sv] /\
    rw_cells a0segs m' (uspi + 296) FSAVA /\ u32arr a0segs m' (S + 1096) cf /\
    drest_at a0segs m' S rr /\ blk_at a0segs m' cx k /\
    rw_cells a0segs m' (S + 1092) c1 /\ rw_cells a0segs m' (S + 3152) c2 /\ rw_cells a0segs m' (S + 64036) c3 /\ stk a0segs m' lo uspi.
  Proof.
    intros until sv. intros MU2 WM2 BLKS PAY DSTA DL CRC RNA GOT SV FS CF CFL DR BLK C1 L1 C2 L2 C3 L3 ST. zok.
    clear D_SM D_SR D_SD D_MR D_MD D_RD IA_S IA_M IA_D BTT B16 B4 B164 LSM.
    splits.
    - eapply bytes_at_transport; [exact PAY| exact MU2|]. rewrite PAYL. cl.
    - eapply u8arr_transport; [exact DSTA| exact MU2| exact WM2|]. rewrite DL. cl.
    - eapply u32arr_transport; [exact CRC| exact MU2| exact WM2|]. rewrite CWL. cl.
    - eapply u32arr_transport; [exact RNA| exact MU2| exact WM2|]. rewrite RNL. cl.
    - eapply ro_cells_transport; [exact GOT| exact MU2|]. cl.
    - eapply ro_cells_transport; [exact SV| exact MU2|]. cl.
    - eapply rw_cells_transport; [exact FS| exact MU2| exact WM2|]. cl.
    - eapply u32arr_transport; [exact CF| exact MU2| exact WM2|]. rewrite CFL. cl.
    - eapply drest_transport; [exact DR| exact MU2| exact WM2| | |]; cl.
    - eapply blk_at_transport; [exact BLK| exact MU2| exact WM2|].
      intros A n0 HR. pose proof (BLKS A n0 HR) as RA. clear -RA LO1 LO2 LO3 SPI ACR. cl.
    - eapply rw_cells_transport; [exact C1| exact MU2| exact WM2|]. rewrite L1. cl.
    - eapply rw_cells_transport; [exact C2| exact MU2| exact WM2|]. rewrite L2. cl.
    - eapply rw_cells_transport; [exact C3| exact MU2| exact WM2|]. rewrite L3. cl.
    - eapply stk_transport_disjoint; [exact ST| exact MU2| exact WM2|]. cl.
  Qed.

  Lemma bzd_fLA : forall f, KRet WLA -> (forall f', f = Datatypes.S f' -> KCall WLA f') -> FLKA f.
  Proof.
    intros f KR KC. unfold A0F_bzd_skV.FLKA. intros until rest. intros CH MU WM MI FA BND.
    cps_destruct CH as (DM & CRC & DE & FR & FS & ST). pose proof DE as DE'. cps_destruct DE' as (DSTA & DL & Edb & Lout).
    pose proof DM as DM'. unfold DecCutA.dmem in DM'. cps_destruct DM' as (HD & NBU & CF & MID & SAV & DR & SM & BLK & PAY & GOT & SV & RNA).
    a0img.
    cps_destruct FA as (DP & Rst & Rcc & Hav & (OUTW & ENDR & Rrv)).
    pose proof (dpureF_verb _ _ _ _ _ _ DP) as Everb. pose proof (dpureF_small _ _ _ _ _ _ DP) as Esm.
    pose proof (dpureF_n _ _ _ _ _ _ DP) as En. pose proof (dpureF_cbn _ _ _ _ _ _ DP) as [Rbn0 Rcred].
    cbn [bs_len bs_of] in Rcred. pose proof (dpureF_bl _ _ _ _ _ _ DP) as Rbl.
    zok. pose proof SHL as SHL0. cps_destruct SHL0 as (SHs & SHt & SHd & SHc & SHr & _ & _). unfold A0F_bzd_skV.WLA in MU, SHs, SHt, SHd, SHc, SHr.
    hide_disj. unfold A0F_bzd_skV.ZRA. unfold A0F_bzd_skV.FIMGA in CRC.
    dvF_cbn_in HD. dvF_cbn_in NBU. dvF_cbn_in MID. dvF_cbn_in SM. dvF_cbn_in SAV. rewrite Everb in HD. unfold bzd_slots in FR.
    (* [comment removed for export] *)
    wstep. wstep. wstep. rewrite (S0F_bzd_loop5.beq_rv4 rv Rrv). destruct (Z.eqb_spec rv 4) as [Erv|NErv].
    - (* [comment removed for export] *)
      specialize (ENDR Erv). rewrite Erv. rewrite K_L_end. hide BND. hide OUTW.
      (* [comment removed for export] *)
      arun_to 0x8733c%Z. try rewrite (sx32_of_Z 0) by lia.
      (* [comment removed for export] *)
      arun_to 0x87370%Z.
      (* [comment removed for export] *)
      wstep. if_cases Kc; zify_cond Kc.
      + assert (EQ : d_cccrc d = d_sccrc d)
          by (rewrite <- (sx32_mod32 (d_cccrc d)), <- (sx32_mod32 (d_sccrc d)) by (clear -Rcc ENDR; lia); rewrite Kc; reflexivity).
        rewrite EQ, Z.eqb_refl. clear Kc.
        wstep. wstep.
        eapply (bzd_fepiA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BZ_STREAM_END J d s dbytes rest KR);
          [unfold bzd_slots; exact FR| exact FS| exact ST| unfold A0F_bzd_skV.WLA; exact MU| exact WM| exact MI| exact DM| exact CRC| exact DE| exact DP| unfold BZ_STREAM_END; lia].
      + assert (NE : d_cccrc d <> d_sccrc d) by (intros E; apply Kc; rewrite E; reflexivity).
        replace (d_cccrc d =? d_sccrc d) with false by (symmetry; apply Z.eqb_neq; exact NE). clear Kc NE.
        wstep. wstep.
        eapply (bzd_fepiA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BZ_DATA_ERROR J d s dbytes rest KR);
          [unfold bzd_slots; exact FR| exact FS| exact ST| unfold A0F_bzd_skV.WLA; exact MU| exact WM| exact MI| exact DM| exact CRC| exact DE| exact DP| unfold BZ_DATA_ERROR; lia].
    - (* [comment removed for export] *)
      arun_to 0x87058%Z. try rewrite (sx32_of_Z (d_state d)) by (clear -Rst; lia).
      wstep. wstep. wstep. if_cases Ks; zify_cond Ks.
      { (* [comment removed for export] *)
        rewrite (K_L_ret f rv d s NErv) by (unfold BZ_X_OUTPUT; clear -Ks Rst; lia). clear Ks.
        wstep.
        eapply (bzd_fepiA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rv J d s dbytes rest KR);
          [unfold bzd_slots; exact FR| exact FS| exact ST| unfold A0F_bzd_skV.WLA; exact MU| exact WM| exact MI| exact DM| exact CRC| exact DE| exact DP| exact Rrv]. }
      (* [comment removed for export] *)
      assert (Hst : d_state d = BZ_X_OUTPUT) by (unfold BZ_X_OUTPUT; clear -Ks Rst; lia). clear Ks.
      specialize (OUTW Hst). specialize (BND Hst).
      destruct f as [|f']; [exfalso; clear -BND Rbl Rbn0 Rcred LR2; assert (0 <= len / 6)%Z by (apply Z.div_pos; lia); lia|]. specialize (KC f' eq_refl).
      rewrite (K_L_go f' rv d s NErv Hst).
      assert (BND' : (len / 6 - d_blockNo d <= Z.of_nat f')%Z) by (clear -BND; lia). clear BND.
      pose proof OUTW as OUTW'. cps_destruct OUTW' as (Eol & Rtp & NK & Rsnb1 & Ecb & Rsb & Rr01 & Rrnd & Rcf & Eoc & Rn9).
      assert (N1 : (1 <= n)%Z) by (clear -Rn9 En; lia).
      pose proof (NN0 N1) as NN0'. pose proof (NN1 N1) as NN1'.
      assert (Rsm : (0 <= d_small d <= 1)%Z) by (clear -Esm LSM; unfold id in LSM; lia).
      assert (Rrd : (0 <= d_rand d <= 1)%Z) by (clear -Rr01; lia).
      assert (BLKR : forall A n0, blk_range cx A n0 -> (0 < A /\ A + n0 <= alloc_ceiling)%Z).
      { intros A n0 [(Hs0 & -> & ->) | (Hs1 & [(-> & ->) | (-> & ->)])].
        - exact (proj1 (BTT (NN0' Hs0))). - exact (proj1 (B16 (proj1 (NN1' Hs1)))). - exact (proj1 (B4 (proj2 (NN1' Hs1)))). }
      assert (Hst2 : d_state d = 2%Z) by exact Hst. rewrite Hst2 in HD.
      hide OUTW. hide NK. hide Rr01. hide Rrnd. hide Rcf. hide NN0'. hide NN1'. hide BLKR. hide BTT. hide B16. hide B4. hide B164.
      (* [comment removed for export] *)
      hide PAY. hide DSTA. hide CRC. hide RNA. hide GOT. hide SV. hide FS. hide CF. hide DR. hide BLK. hide NBU. hide MID. hide SAV. hide ST.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (munch_refl ([(uspi, uspi + 296)])%Z mm) as MUd; pose proof (wmono_refl a0segs mm) as WMd end.
      (* [comment removed for export] *)
      arun_to 0x844b4%Z. cbv beta. rewrite (byte_lit_unsigned (d_small d)) by (clear -Rsm; lia).
      (* [comment removed for export] *)
      arun_to 0x844c4%Z. cbv beta. rewrite (byte_lit_unsigned (d_rand d)) by (clear -Rrd; lia).
      (* [comment removed for export] *)
      arun_to 0x84518%Z.
      (* [comment removed for export] *)
      Ltac unhide_disp MUd WMd PAY DSTA DL CRC RNA GOT SV FS CF DR BLK NBU MID SAV ST BLKR :=
        unfold id in PAY, DSTA, CRC, RNA, GOT, SV, FS, CF, DR, BLK, NBU, MID, SAV, ST, BLKR;
        let X := fresh "X" in
        pose proof (dispatch_transport _ _ _ _ _ _ _ _ _ _ _ MUd WMd BLKR PAY DSTA DL CRC RNA GOT SV FS CF (zw32_length_nat _ _) DR BLK NBU eq_refl MID eq_refl SAV eq_refl ST) as X;
        clear PAY DSTA CRC RNA GOT SV FS CF DR BLK NBU MID SAV ST;
        cps_destruct X as (PAY & DSTA & CRC & RNA & GOT & SV & FS & CF & DR & BLK & NBU & MID & SAV & ST).
      (* [comment removed for export] *)
      Ltac v_ok DP OUTW Hav DSTA DL Edb Lout := unfold id in OUTW; eapply fmkc_okA; [exact DP| exact OUTW| exact Hav| unfold A0F_bzd_skV.FDESTA; splits; [exact DSTA| exact DL| exact Edb| exact Lout]].
      Ltac v_dsg HD NBU MID SM Hst2 Everb := unfold DSgA; ofmkc; a0img; dvF_cbn; rewrite Hst2, Everb; splits; [exact_cells HD| exact NBU| exact MID| exact SM].
      Ltac v_dest DSTA DL Edb Lout := unfold DESTgA; ofmkc; a0img; splits; [exact DSTA| exact DL| exact Edb| exact Lout].
      (* [comment removed for export] *)
      wstep. if_cases Ksm; zify_cond Ksm.
      + (* [comment removed for export] *)
        assert (Hsm : b_small cx = 1%Z) by (clear -Ksm Esm LSM Rsm; unfold id in LSM; lia). clear Ksm.
        (* [comment removed for export] *)
        arun_to 0x8454c%Z. try rewrite (sx32_of_Z (s_avail_out s)) by (clear -Hav LDL; lia).
        (* [comment removed for export] *)
        arun_to 0x84564%Z.
        unhide_disp MUd WMd PAY DSTA DL CRC RNA GOT SV FS CF DR BLK NBU MID SAV ST BLKR. clear MUd WMd.
        unfold id in NN1'. destruct (NN1' Hsm) as [NZ16 NZ4].
        dvF_cbn_in BLK. unfold blk_of in BLK. rewrite Hsm in BLK. cbn [Z.eqb blk_at] in BLK. cps_destruct BLK as (_ & L16A & L16L & L4A & L4L).
        wstep. if_cases Kbr; zify_cond Kbr.
        * (* [comment removed for export] *)
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
            eapply (VSR (fmkcA m1 J d s f') SHS w0);
            [ v_ok DP OUTW Hav DSTA DL Edb Lout
            | eapply fmkc_okSA; [exact ZOK| exact Hsm| exact NZ16| exact NZ4]
            | exact ANS
            | exact (A0F_bzd_sk1.fmkc_sh z QF WLA m1 m1 J d s f' (A0F_bzd_sk1.bzd_sh_rebase z WLA (z_m0 z) m1 SHL MU))
            | eapply (A0F_bzd_sk2.bzd_fjoinSA z SHS w0 QF ZOK SHL f' m1 J d s (r_of d) KR KC Hsm NZ16 NZ4 DP eq_refl Rcc Rsb BND' DR PAY SV FS ST MU WM)
            | eapply (A0F_bzd_sk1.bzd_fexitSA z SHS w0 QF ZOK m1 J d s f' (r_of d) KR Hsm DP eq_refl DR PAY SV FS ST MU WM)
            | v_dsg HD NBU MID SM Hst2 Everb
            | v_dest DSTA DL Edb Lout
            | unfold bzd_slots; exact FR
            | unfold FROsA, FGOTA; ofmkc; a0img; splits; [exact SAV| exact L16A| exact L4A| exact CF| exact CRC| exact RNA| exact GOT| exact MI]
            | apply munch_refl | apply wmono_refl
            | ofmkc; clear -Kbr Rrd; lia ] end.
        * (* [comment removed for export] *)
          wstep.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
            eapply (VSNR (fmkcA m1 J d s f') SHS w0);
            [ v_ok DP OUTW Hav DSTA DL Edb Lout
            | eapply fmkc_okSA; [exact ZOK| exact Hsm| exact NZ16| exact NZ4]
            | exact ANS
            | exact (A0F_bzd_sk1.fmkc_sh z QF WLA m1 m1 J d s f' (A0F_bzd_sk1.bzd_sh_rebase z WLA (z_m0 z) m1 SHL MU))
            | eapply (A0F_bzd_sk2.bzd_fjoinSA z SHS w0 QF ZOK SHL f' m1 J d s (r_of d) KR KC Hsm NZ16 NZ4 DP eq_refl Rcc Rsb BND' DR PAY SV FS ST MU WM)
            | eapply (A0F_bzd_sk1.bzd_fexitSA z SHS w0 QF ZOK m1 J d s f' (r_of d) KR Hsm DP eq_refl DR PAY SV FS ST MU WM)
            | v_dsg HD NBU MID SM Hst2 Everb
            | v_dest DSTA DL Edb Lout
            | unfold bzd_slots; exact FR
            | unfold FROsA, FGOTA; ofmkc; a0img; splits; [exact SAV| exact L16A| exact L4A| exact CF| exact CRC| exact RNA| exact GOT| exact MI]
            | apply munch_refl | apply wmono_refl
            | ofmkc; clear -Kbr Rrd; lia ] end.
      + (* [comment removed for export] *)
        assert (Hsm : b_small cx = 0%Z) by (clear -Ksm Esm LSM Rsm; unfold id in LSM; lia). clear Ksm.
        astep. astep.
        unhide_disp MUd WMd PAY DSTA DL CRC RNA GOT SV FS CF DR BLK NBU MID SAV ST BLKR. clear MUd WMd.
        unfold id in NN0'. pose proof (NN0' Hsm) as TNZ.
        dvF_cbn_in BLK. unfold blk_of in BLK. rewrite Hsm in BLK. cbn [Z.eqb blk_at] in BLK. cps_destruct BLK as (_ & TTA & TTL).
        wstep. if_cases Kbr; zify_cond Kbr.
        * (* [comment removed for export] *)
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
            eapply (VFNR (fmkcA m1 J d s f') SHS w0);
            [ v_ok DP OUTW Hav DSTA DL Edb Lout
            | eapply fmkc_okFA; [exact ZOK| exact Hsm| exact TNZ]
            | exact ANS
            | exact (A0F_bzd_sk1.fmkc_sh z QF WLA m1 m1 J d s f' (A0F_bzd_sk1.bzd_sh_rebase z WLA (z_m0 z) m1 SHL MU))
            | eapply (A0F_bzd_sk2.bzd_fjoinFA z SHS w0 QF ZOK SHL f' m1 J d s (r_of d) KR KC Hsm TNZ DP eq_refl Rcc Rsb BND' CF DR PAY SV FS ST MU WM)
            | eapply (A0F_bzd_sk1.bzd_fexitFA z SHS w0 QF ZOK m1 J d s f' (r_of d) KR Hsm DP eq_refl CF DR PAY SV FS ST MU WM)
            | v_dsg HD NBU MID SM Hst2 Everb
            | v_dest DSTA DL Edb Lout
            | unfold bzd_slots; exact FR
            | unfold FROfA, FGOTA; ofmkc; a0img; splits; [exact SAV| exact TTA| exact CRC| exact RNA| exact GOT| exact MI]
            | apply munch_refl | apply wmono_refl
            | ofmkc; clear -Kbr Rrd; lia ] end.
        * (* [comment removed for export] *)
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
            eapply (VFR (fmkcA m1 J d s f') SHS w0);
            [ v_ok DP OUTW Hav DSTA DL Edb Lout
            | eapply fmkc_okFA; [exact ZOK| exact Hsm| exact TNZ]
            | exact ANS
            | exact (A0F_bzd_sk1.fmkc_sh z QF WLA m1 m1 J d s f' (A0F_bzd_sk1.bzd_sh_rebase z WLA (z_m0 z) m1 SHL MU))
            | eapply (A0F_bzd_sk2.bzd_fjoinFA z SHS w0 QF ZOK SHL f' m1 J d s (r_of d) KR KC Hsm TNZ DP eq_refl Rcc Rsb BND' CF DR PAY SV FS ST MU WM)
            | eapply (A0F_bzd_sk1.bzd_fexitFA z SHS w0 QF ZOK m1 J d s f' (r_of d) KR Hsm DP eq_refl CF DR PAY SV FS ST MU WM)
            | v_dsg HD NBU MID SM Hst2 Everb
            | v_dest DSTA DL Edb Lout
            | unfold bzd_slots; exact FR
            | unfold FROfA, FGOTA; ofmkc; a0img; splits; [exact SAV| exact TTA| exact CRC| exact RNA| exact GOT| exact MI]
            | apply munch_refl | apply wmono_refl
            | ofmkc; clear -Kbr Rrd; lia ] end.
  Time Qed.
End BZD.
End ACeilS1.
