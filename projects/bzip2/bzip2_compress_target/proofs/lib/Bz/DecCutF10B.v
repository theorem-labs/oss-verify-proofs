(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzInv BzTables BzContracts DecCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK DecCutF BzDU10M DecCutF10.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU10M OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF10.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutB.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutB.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil}.
Local Open Scope Z_scope.
Section WithImg.
  Variable I : dimg.
  Let segs := di_segs I.

  (* [comment removed for export] *)
  Lemma raw_dvFA_d : forall (d : dst) (cx : bctx) (g1 sv : word) (payload : list byte) (m : word -> option byte)
                           (h : dsh) (nbu : Z) (cf : list word) (dm : dsm) (j1 : list byte) (snb : Z) (j2 : list byte)
                           (r : drest) (b0 : bzs) (ai : Z) (til tih : word) (k : blk) (s : dstrm),
    let J := jk_of h j1 j2 b0 til tih in
    (* [comment removed for export] *)
    rw_cells segs m (b_s cx) (HEAD_CELLS h) ->
    rw_cells segs m (b_s cx + 1092) [C4 (Z_to_bv 64 nbu)] ->
    u32arr segs m (b_s cx + 1096) cf -> length cf = 257%nat ->
    rw_cells segs m (b_s cx + 3152) (MID_CELLS dm) ->
    rw_cells segs m (b_s cx + 64036) (SAVE_CELLS j1 snb j2) ->
    drest_at segs m (b_s cx) r ->
    rw_cells segs m (b_strm cx) (STRM_CELLS (bupd b0 ai til tih)) ->
    blk_at segs m cx k ->
    bytes_at segs m (b_src cx) payload ->
    ro_cells segs m (di_got I) [C8 (Z_to_bv 64 (di_stderrp I)); C8 g1; C8 (Z_to_bv 64 (di_stderrp I + 8)); C8 (Z_to_bv 64 (di_crc I)); C8 (Z_to_bv 64 (di_rnums I))] ->
    ro_cells segs m (di_stderrp I) [C8 sv] ->
    u32arr segs m (di_rnums I) rnums_words ->
    (* [comment removed for export] *)
    d_out_ch d = bv_unsigned (sh_soch h) -> d_out_len d = sh_solen h -> d_rand d = bv_unsigned (sh_brand h) ->
    d_rNToGo d = sh_rNToGo h -> d_rTPos d = sh_rTPos h -> d_origPtr d = sh_origPtr h ->
    d_tPos d = bv_unsigned (sh_tPos h) -> d_k0 d = bv_unsigned (sh_k0 h) ->
    d_unzftab d = warr (r_unz r) -> d_nused d = nbu -> d_cftab d = warr cf -> d_cftabCopy d = warr (r_cfc r) ->
    d_tt d = blk_tt k -> d_ll16 d = blk_l16 k -> d_ll4 d = blk_l4 k ->
    d_sbcrc d = bv_unsigned (sm_sbcrc dm) -> d_sccrc d = bv_unsigned (sm_sccrc dm) mod 2 ^ 32 -> d_cbcrc d = bv_unsigned (sm_cbcrc dm) ->
    d_nInUse d = sm_nInUse dm -> d_inUse d = barr (r_inUse r) -> d_inUse16 d = barr (r_in16 r) -> d_s2u d = barr (r_s2u r) ->
    d_mtfa d = barr (r_mtfa r) -> d_mtfbase d = warr (r_mtfb r) -> d_sel d = barr (r_sel r) -> d_selMtf d = barr (r_selm r) ->
    d_len d = barr (r_len r) -> d_limit d = warr (r_lim r) -> d_base d = warr (r_base r) -> d_perm d = warr (r_perm r) ->
    d_minLens d = warr (r_minl r) ->
    (* [comment removed for export] *)
    sh_strm h = b_strm cx ->
    d_state d = sh_state h -> d_bsBuff d = sh_bsBuff h -> d_bsLive d = sh_bsLive h -> d_bs100k d = sh_n h ->
    d_small d = bv_unsigned (sh_small h) -> d_blockNo d = sh_cbn h -> d_verb d = sh_verb h ->
    Z_to_bv 64 (d_cccrc d) = sm_cccrc dm -> sv_nblock (d_sv d) = snb ->
    sm_tt dm = b_tt cx -> sm_ll16 dm = b_ll16 cx -> sm_ll4 dm = b_ll4 cx ->
    (* [comment removed for export] *)
    bs_S b0 = b_s cx -> bs_src b0 = b_src cx -> bs_len b0 = b_len cx -> bs_dst b0 = b_dst cx -> bs_dlen b0 = b_dlen cx ->
    bs_av b0 = s_avail_out s -> ai = Z.of_nat (length (s_in s)) ->
    dmem I cx g1 sv payload m (dvF cx J d s) /\ jk_wf J /\ jk_static b0 J /\ drep d.
  Proof.
    intros until s. cbv zeta.
    intros HD NBU CF Lcf MID SAV DR STRM BLK PAY GOT SEV RN.
    intros Joch Jolen Jrand Jrn Jrt Jorig Jtpos Jk0 Junz Jnbu Jcf Jcfc Jtt Jl16 Jl4 Jsb Jsc Jcb Jniu Jiu Ji16 Js2u Jmtfa Jmtfb Jsel Jselm
           Jlen Jlim Jbase Jperm Jminl.
    intros Hstrm Dst Dbb Dbl Dn Dsm Dcbn Dverb Dcc Dsnb Ett El16 El4 HbS Hsrc Hlen Hdst Hdlen Hav Hai.
    (* [comment removed for export] *)
    pose proof HD as HD'. destruct HD' as [[WFh _] _]. cbn [cells_wf cell_wf] in WFh.
    cps_destruct WFh as (_ & _ & _ & Lp1 & _ & _ & Lp2 & _ & _ & _ & _ & _ & _ & Lp3 & _).
    pose proof SAV as SAV'. destruct SAV' as [[WFs _] _]. cbn [cells_wf cell_wf] in WFs. cps_destruct WFs as (Lj1 & _ & Lj2 & _).
    pose proof STRM as STRM'. destruct STRM' as [[WFb _] _]. cbn [cells_wf cell_wf bupd bs_q1 bs_q2] in WFb.
    cps_destruct WFb as (_ & _ & _ & _ & Lq1 & _ & _ & _ & _ & Lq2 & _).
    split; [| split; [| split]].
    - (* [comment removed for export] *)
      unfold dvF. apply dmem_intro; fold segs.
      + (* [comment removed for export] *)
        eapply rw_cells_eqv; [exact HD|]. unfold hd_of. cbn [j_p1 j_p2 j_p3 jk_of].
        rewrite Joch, Jolen, Jrand, Jrn, Jrt, Jorig, Jtpos, Jk0, Dst, Dbb, Dbl, Dn, Dsm, Dcbn, Dverb, <- Hstrm.
        rewrite !Z_to_bv8_unsigned, !Z_to_bv_bv_unsigned. destruct h; reflexivity.
      + (* [comment removed for export] *) rewrite Jnbu. exact NBU.
      + (* [comment removed for export] *) rewrite Jcf. apply u32arr_warr; [exact CF| rewrite Lcf; reflexivity].
      + (* [comment removed for export] *)
        eapply rw_cells_same_bytes; [| | | exact MID].
        * unfold mid_of. rewrite Jsb, Jsc, Jcb, Jniu, Dcc, Ett, El16, El4.
          cbn [cells_bytes cbytes sm_tt sm_ll16 sm_ll4 sm_sbcrc sm_sccrc sm_cbcrc sm_cccrc sm_nInUse].
          rewrite !Z_to_bv_bv_unsigned.
          rewrite <- (le4_lit_mod32 (sm_sccrc dm) (bv_unsigned (sm_sccrc dm) mod 2 ^ 32)) by (rewrite Z.mod_mod by lia; reflexivity).
          reflexivity.
        * reflexivity.
        * cbn. repeat split.
      + (* [comment removed for export] *) cbn [j_s1 j_s2 jk_of]. rewrite Dsnb. exact SAV.
      + (* [comment removed for export] *)
        unfold r_of. rewrite Junz, Jcfc, Jiu, Ji16, Js2u, Jmtfa, Jmtfb, Jsel, Jselm, Jlen, Jlim, Jbase, Jperm, Jminl.
        cps_destruct DR as ((A1&L1)&(A2&L2)&(A3&L3)&(A4&L4)&(A5&L5)&(A6&L6)&(A7&L7)&(A8&L8)&(A9&L9)&(A10&L10)&(A11&L11)&(A12&L12)&(A13&L13)&(A14&L14)).
        unfold drest_at. cbn [r_unz r_cfc r_inUse r_in16 r_s2u r_mtfa r_mtfb r_sel r_selm r_len r_lim r_base r_perm r_minl].
        rewrite !zw32_length, !zb8_length by lia.
        repeat match goal with |- _ /\ _ => split end; try reflexivity;
          first [ eapply u32arr_warr; eassumption | eapply u8arr_barr; eassumption ].
      + (* [comment removed for export] *)
        eapply rw_cells_eqv; [exact STRM|]. unfold bs_of, bupd.
        cbn [j_til j_tih j_q1 j_tol j_toh j_q2 j_bzalloc j_bzfree j_opaque jk_of
             bs_src bs_len bs_ai bs_til bs_tih bs_q1 bs_dst bs_dlen bs_av bs_tol bs_toh bs_q2 bs_S bs_bzalloc bs_bzfree bs_opaque].
        rewrite <- HbS, <- Hsrc, <- Hlen, <- Hdst, <- Hdlen, Hav, Hai. destruct b0; reflexivity.
      + (* [comment removed for export] *)
        unfold blk_of. rewrite Jtt, Jl16, Jl4. destruct k as [ws|l16 l4]; cbn [blk_at] in BLK.
        * cps_destruct BLK as (SM & U & LU). rewrite SM. cbn [Z.eqb blk_tt]. cbn [blk_at].
          split; [exact SM|]. split; [apply u32arr_warr; [exact U| exact LU] | apply zw32_length; lia].
        * cps_destruct BLK as (SM & U16 & L16 & U4 & L4). rewrite SM. cbn [Z.eqb blk_l16 blk_l4]. cbn [blk_at].
          split; [exact SM|]. split; [| split; [| split]].
          -- replace (200000 * b_n cx) with (2 * (100000 * b_n cx)) by lia. apply u8arr_harr; [exact U16| lia].
          -- unfold zh16. apply tab_length. lia.
          -- apply u8arr_barr; [exact U4| exact L4].
          -- apply zb8_length. lia.
      + exact PAY.
      + exact GOT.
      + exact SEV.
      + exact RN.
    - (* [comment removed for export] *) unfold jk_wf. cbn [j_p1 j_p2 j_p3 j_s1 j_s2 j_q1 j_q2 jk_of]. repeat split; assumption.
    - (* [comment removed for export] *) unfold jk_static. cbn [j_q1 j_q2 j_tol j_toh j_bzalloc j_bzfree j_opaque jk_of]. repeat split; reflexivity.
    - (* [comment removed for export] *) unfold drep. rewrite Jtt, Jl16, Jl4, Js2u, Jsc, Jmtfa.
      split; [apply blk_tt_range|]. split; [apply blk_l16_range|]. split; [apply blk_l4_range|].
      split; [apply barr_range|]. split; [apply Z.mod_pos_bound; lia| apply barr_range].
  Qed.

  (* [comment removed for export] *)
  Lemma raw_dvFA : forall (P : dst -> dst) (cx : bctx) (g1 sv : word) (payload : list byte) (m : word -> option byte)
                         (h : dsh) (nbu : Z) (cf : list word) (dm : dsm) (j1 : list byte) (snb : Z) (j2 : list byte)
                         (r : drest) (b0 : bzs) (ai : Z) (til tih : word) (k : blk) (s : dstrm),
    let jd := jd_of h nbu cf dm r k in
    let J := jk_of h j1 j2 b0 til tih in
    junk_kept P ->
    (* [comment removed for export] *)
    rw_cells segs m (b_s cx) (HEAD_CELLS h) ->
    rw_cells segs m (b_s cx + 1092) [C4 (Z_to_bv 64 nbu)] ->
    u32arr segs m (b_s cx + 1096) cf -> length cf = 257%nat ->
    rw_cells segs m (b_s cx + 3152) (MID_CELLS dm) ->
    rw_cells segs m (b_s cx + 64036) (SAVE_CELLS j1 snb j2) ->
    drest_at segs m (b_s cx) r ->
    rw_cells segs m (b_strm cx) (STRM_CELLS (bupd b0 ai til tih)) ->
    blk_at segs m cx k ->
    bytes_at segs m (b_src cx) payload ->
    ro_cells segs m (di_got I) [C8 (Z_to_bv 64 (di_stderrp I)); C8 g1; C8 (Z_to_bv 64 (di_stderrp I + 8)); C8 (Z_to_bv 64 (di_crc I)); C8 (Z_to_bv 64 (di_rnums I))] ->
    ro_cells segs m (di_stderrp I) [C8 sv] ->
    u32arr segs m (di_rnums I) rnums_words ->
    (* [comment removed for export] *)
    sh_strm h = b_strm cx ->
    d_state (P jd) = sh_state h -> d_bsBuff (P jd) = sh_bsBuff h -> d_bsLive (P jd) = sh_bsLive h -> d_bs100k (P jd) = sh_n h ->
    d_small (P jd) = bv_unsigned (sh_small h) -> d_blockNo (P jd) = sh_cbn h -> d_verb (P jd) = sh_verb h ->
    Z_to_bv 64 (d_cccrc (P jd)) = sm_cccrc dm -> sv_nblock (d_sv (P jd)) = snb ->
    sm_tt dm = b_tt cx -> sm_ll16 dm = b_ll16 cx -> sm_ll4 dm = b_ll4 cx ->
    (* [comment removed for export] *)
    bs_S b0 = b_s cx -> bs_src b0 = b_src cx -> bs_len b0 = b_len cx -> bs_dst b0 = b_dst cx -> bs_dlen b0 = b_dlen cx ->
    bs_av b0 = s_avail_out s -> ai = Z.of_nat (length (s_in s)) ->
    dmem I cx g1 sv payload m (dvF cx J (P jd) s) /\ jk_wf J /\ jk_static b0 J /\ drep (P jd).
  Proof.
    intros until s. cbv zeta. intros JKP. intros.
    pose proof (JKP (jd_of h nbu cf dm r k)) as X.
    cbn [jd_of d_out_ch d_out_len d_rand d_rNToGo d_rTPos d_origPtr d_tPos d_k0 d_unzftab d_nused d_cftab d_cftabCopy d_tt d_ll16 d_ll4
         d_sbcrc d_sccrc d_cbcrc d_nInUse d_inUse d_inUse16 d_s2u d_mtfa d_mtfbase d_sel d_selMtf d_len d_limit d_base d_perm d_minLens] in X.
    decompose [and] X.
    eapply raw_dvFA_d; eassumption.
  Qed.
End WithImg.
End ACeilS1.
