(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image Arr Frame Mem MState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.MallocP Require Import RMallocRep.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim ZApi ZHarness ZApiL ZHarnessL ZApiC ZHarnessC ZInstC Stdio.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Zlib_iface Zc_iface Z_kit Z_dview Z_drep Z_dkit Z_zrd Z_defl_iface Z_defl_path Zg_defl_path Zg_defl_path2 Zg_defl_pathi2 Zg_defl_iface Zg_defl_iface2 Z_dinit_kit Z_deflate Zc_zrd.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Deflate DeflateSafe RefDeflateRel RefDeflSafeI1 RefDeflSafeI2 RefDeflSafeI4 BoundFw BoundCall ZApiInst ZApiInstC ZTaint ZTaintC.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wq := (Z_to_bv 64).

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Local Transparent the_zapiC.

Section CLOSE.
  Hypothesis HDEFL : deflate_in_stmtg2.

  Theorem deflate_proofC : forall R : zreps, Zlib_iface.zr_d R = zr_dC -> deflate_stmtC R.
  Proof.
    intros R RD. unfold deflate_stmtC. intros until B.
    intros ZP ZR PB PF PNI PNI2 CO CL CNO CNO2 HIL HAO T1 T2 T3 T4 HFL SEPO SEPI CIMG SBO SBI SIO ZLS SIF STK CEIL GLO LOSP SP16 SPB B63 MI -> ->.
    rewrite RD in ZR. unfold deflate_postC. rewrite RD.
    unfold dsc_tin, dsc_tout in *. cbn [dc_deflate the_zapiC ZApiInstC.zinstC] in *.
    unfold Prelim.zlength, ZIface.zlength in *.
    destruct ZR as (L & sa & b & ELB & ES & DQ & DR & PT & DCL & ZOK). subst LBz.
    assert (HIL' : ZIface.zlength inp < 2 ^ 31) by (unfold ZIface.zlength; exact HIL).
    assert (HTIN' : zs_total_in (dz_z ds) + ZIface.zlength inp < 2 ^ 63) by (unfold ZIface.zlength; clear - T1 T2; lia).
    pose proof (zdc_call_facts sa inp ds ao flush DR PT ZOK HIL' HTIN' HAO PF HFL) as FACTS.
    pose proof (czcC_path sa inp ds ao flush DR PT ZOK HIL' HAO PF HFL) as PATH.
    cbv zeta in FACTS. unfold ZIface.zlength in FACTS.
    destruct (zdc_deflate inp ds ao flush) as [[[x' consumed] bs] rc].
    remember (fst (deflate_core (cd0C sa inp ds ao) flush)) as sF eqn:EsF.
    remember (snd (deflate_core (cd0C sa inp ds ao) flush)) as rcF eqn:ErcF.
    destruct FACTS as (DR' & PT' & ZOK' & Erc & Ebs & Etin' & Etout' & Emsg' & Edt' & Ead' & TI & RNI & AI & Eco & TO & AOU & LBS & ROOM & BSB).

    set (tin := zs_total_in (dz_z ds)) in *. set (tout := zs_total_out (dz_z ds)) in *.
    pose proof ZOK as (Rti & Rto & _). fold tin in Rti. fold tout in Rto.
    assert (LOUT : length (to_bytes oldc) = length oldc) by apply to_bytes_length.

    remember (dl_io L NI NO) as L' eqn:EL'.
    pose proof (st_lay _ _ _ _ (proj2 DQ)) as LAY.
    destruct b as [[[[psp pw] pp] ph] pb]. unfold zd_blocks in SBO, SBI. unfold zd_blocks.
    assert (INb : forall y, In y [(pb, dl_Ab L, 65536); (ph, dl_Ah L, 65536); (pp, dl_Ap L, 65536); (pw, dl_Aw L, 65536); (psp, dl_As L, 5968)] ->
                  (blk_addr y + blk_size y <= NO \/ NO + ao <= blk_addr y) /\ (blk_addr y + blk_size y <= NI \/ NI + Z.of_nat (length inp) <= blk_addr y))
      by (intros y Hy; split; [exact (SBO y Hy)| exact (SBI y Hy)]).
    pose proof (INb _ ltac:(left; reflexivity)) as Yb. pose proof (INb _ ltac:(right; left; reflexivity)) as Yh.
    pose proof (INb _ ltac:(do 2 right; left; reflexivity)) as Yp. pose proof (INb _ ltac:(do 3 right; left; reflexivity)) as Yw.
    pose proof (INb _ ltac:(do 4 right; left; reflexivity)) as Ys. clear INb SBO SBI. cbn [blk_addr blk_size fst snd] in Yb, Yh, Yp, Yw, Ys.

    apply box in Yb. apply box in Yh. apply box in Yp. apply box in Yw. apply box in Ys. apply box in CIMG. apply box in SIO.
    unfold dlay_ceil in DCL. unfold strm_in_frame, ZS_SIZEOF in SIF. unfold Z_DEFLATE_STACK in LOSP. unfold Layout.GLOBALS_TOP in GLO.

    remember (to_bytes oldc) as rest0 eqn:Erest0.
    assert (LR0 : Z.of_nat (length rest0) = ao) by (clear - LOUT CL; lia).

    assert (DREP0 : DREP m L' (cd0C sa inp ds ao)).
    { split.
      - destruct (proj1 DQ) as (p3 & resv & ZQ). exists p1, p2, p3, resv.
        assert (ZS : rw_cells psegs m S (zs_pub NI (Z.of_nat (length inp)) tin NO ao tout p1 p2 ++ zs_priv_cells L (zs_msg (dz_z ds)) (zs_data_type (dz_z ds)) (zs_adler (dz_z ds)) p3 resv)).
        { apply (proj2 (Startup_glue.rw_cells_app psegs m S _ _)). split; [exact ZP|]. rewrite ES in ZQ.
          lazymatch goal with |- rw_cells _ _ (_ + Z.of_nat ?n) _ => replace (Z.of_nat n) with 48 by reflexivity end. exact ZQ. }
        subst L'. unfold dl_io, zs_call_cells, zs_priv_cells, cd0C, czcC. cbn [dl_S dl_As dl_NI dl_NO ds_strm set_strm cstrm_of_call zc_input zc_avail_out zc_strm
          cs_next_in cs_avail_in cs_total_in cs_out_rev cs_avail_out cs_total_out cs_msg cs_data_type cs_adler length Z.of_nat app].
        rewrite ES. unfold zs_pub, zs_priv_cells in ZS. cbn [app] in ZS.
        fold tin. fold tout. unfold ZIface.zlength.
        close_cells ZS.
      - subst L'. apply DST_io. apply DST_set_strm; [intros H; exact H| exact (proj2 DQ)]. }

    assert (DIN0 : din m L' inp).
    { subst L'. unfold din, dl_io. cbn [dl_NI]. exact PB. }
    assert (DOUT0 : dout m L' rest0 (ds_strm (cd0C sa inp ds ao))).
    { subst L'. unfold dout, outv, dl_io, cd0C, czcC. cbn [dl_NO ds_strm set_strm cstrm_of_call cs_out_rev rev zb8 map length skipn app]. subst rest0. exact CO. }
    pose proof (relro_clean_of_zl _ ZLS) as RC.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (BEL : dlay_below L' lo (bv_unsigned sp)).
    { subst L'. unfold dlay_below, dl_io. cbn [dl_S dl_As dl_Aw dl_Ap dl_Ah dl_Ab]. rewrite ES. clear - DCL CEIL GLO SIF. lia. }
    assert (IO : dio_sep L' (ZIface.zlength (zc_input (czcC inp ds ao))) (Z.of_nat (length rest0)) lo).
    { unfold czcC, ZIface.zlength. cbn [zc_input]. rewrite LR0. subst L'. unfold dl_io.
      pose proof (unbox _ Yb) as Xb. pose proof (unbox _ Yh) as Xh. pose proof (unbox _ Yp) as Xp. pose proof (unbox _ Yw) as Xw. pose proof (unbox _ Ys) as Xs.
      pose proof (unbox _ CIMG) as XI. pose proof (unbox _ SIO) as XIO.
      constructor; cbn [dl_NI dl_NO dl_As dl_Aw dl_Ap dl_Ah dl_Ab]; unfold apart.
      - clear - PNI SEPI. lia.
      - clear - CNO HAO SEPO. lia.
      - clear - XI. lia.
      - clear - XIO. lia.
      - clear - Xs. lia. - clear - Xw. lia. - clear - Xp. lia. - clear - Xh. lia. - clear - Xb. lia.
      - clear - Xs. lia. - clear - Xw. lia. - clear - Xp. lia. - clear - Xh. lia. - clear - Xb. lia. }
    assert (ROOM' : (length (cs_out_rev (ds_strm (fst (deflate_core (cd0C sa inp ds ao) flush)))) <= length rest0)%nat).
    { rewrite <- EsF. clear - ROOM LR0. lia. }
    eapply evt_mono.
    { eapply (HDEFL L' (cd0C sa inp ds ao) flush inp rest0 lo);
        [ exact DREP0 | exact DIN0 | exact DOUT0 | exact MI | exact RC | exact STK
        | unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK; clear - LOSP; lia | exact SP16 | exact BEL | exact IO
        | exact (HFL3C flush HFL) | exact PATH | exact ROOM'
        | subst L'; unfold dl_io; cbn [dl_S]; rewrite ES; reflexivity | reflexivity ]. }
    intros ms' POST. cbv beta.
    destruct POST as (u0 & u1 & u2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & STK' & DREP' & DIN' & DOUT').
    rewrite <- EsF, <- ErcF in *.
    destruct DREP' as [ZS' ST']. destruct ZS' as (q1 & q2 & q3 & qr & ZS').
    subst L'. unfold zs_call_cells, zs_priv_cells, dl_io in ZS'. cbn [dl_S dl_NI dl_NO dl_As app] in ZS'. rewrite ES in ZS'.
    lazymatch type of ZS' with rw_cells _ _ _ ?cs =>
      let a := eval cbv beta iota delta [firstn] in (firstn 8 cs) in let b' := eval cbv beta iota delta [skipn] in (skipn 8 cs) in
      change (rw_cells psegs m' S (a ++ b')) in ZS' end.
    apply Startup_glue.rw_cells_app in ZS'. destruct ZS' as [ZP' ZQ'].
    lazymatch type of ZQ' with rw_cells _ _ (_ + Z.of_nat ?n) _ => replace (Z.of_nat n) with 48 in ZQ' by reflexivity end.
    unfold dout, dl_io in DOUT'. cbn [dl_NO] in DOUT'.
    assert (TOX : cs_total_out (ds_strm sF) = tout + Z.of_nat (length (cs_out_rev (ds_strm sF)))).
    { rewrite TO. apply wrap64_id. clear - Rto ROOM T4 HAO. lia. }
    do 15 eexists. exists m', q1, q2.
    split; [reflexivity|].
    split.
    {
      pose proof (unbox _ CIMG) as XI.
      apply (munch_shrink _ _ _ _ MU). intros y OUT. cbn [map app blk_addr blk_size fst snd outside dl_io dl_S dl_As dl_Aw dl_Ap dl_Ah dl_Ab dl_NO] in OUT |- *.
      rewrite ES. unfold ZS_SIZEOF in OUT. pose proof (bv_unsigned_in_range 64 y) as Ry. unfold bv_modulus in Ry. cbn in Ry.
      destruct (Z.le_gt_cases (NO + Z.of_nat (length bs)) (bv_unsigned y)) as [H1|H1]; [destruct (Z.lt_ge_cases (bv_unsigned y) (NO + ao)) as [H2|H2]|].
      - right.
        set (i := Z.to_nat (bv_unsigned y - NO)).
        assert (Ei : wa (NO + Z.of_nat i) = y) by (subst i; apply bv_eq; rewrite wa_unsigned by (clear - H1 H2 Ry LBS CNO; lia); clear - H1 H2 Ry LBS CNO; lia).
        pose proof CO as OREST.
        destruct OREST as [(_ & _ & B1) _]. destruct DOUT' as [(_ & _ & B2) _].
        assert (Li : (i < length rest0)%nat) by (subst i; clear - H1 H2 LR0 LBS; lia).
        pose proof (B1 i Li) as Q1. pose proof (B2 i ltac:(rewrite outv_length; [exact Li| exact ROOM'])) as Q2.
        rewrite (nth_error_outv_tail rest0 _ i ROOM') in Q2 by (subst i; clear - H1 LBS CNO; lia).
        rewrite Ei in Q1, Q2.
        assert (ROM : seg_rom psegs y = None) by (apply RMallocRep.ref_seg_rom_none; clear - XI H1 H2 CNO LBS; lia).
        unfold mrd in Q1, Q2. rewrite ROM in Q1, Q2. rewrite <- Q1 in Q2. destruct (m y), (m' y); congruence.
      - left. clear - OUT H1 H2 LR0 LBS ROOM. lia.
      - left. clear - OUT H1 LR0 LBS ROOM. lia. }
    split; [exact WM|]. split; [exact MI'|]. split; [exact STK'|].
    split; [rewrite Erc; unfold wint, MallocRep.wz; reflexivity|].
    split; [rewrite Eco; exact RNI|]. split; [clear - LBS ROOM; lia|]. split; [exact BSB|].
    split; [rewrite Etin', TI; clear - T1 RNI; lia|].
    split; [rewrite Etout', TOX; clear - T3 ROOM; lia|].
    split.
    { unfold zs_pub. rewrite Etin', Etout', Eco, LBS, TI, TOX. rewrite AI, AOU in ZP'. rewrite TI, TOX in ZP'. close_cells ZP'. }
    split.
    { rewrite <- ES. apply (zr_dC_intro m' L sF (psp, pw, pp, ph, pb) x').
      - split; [| exact (DST_io_back _ _ _ _ _ ST')]. exists q3, qr. rewrite Emsg', Edt', Ead'. unfold zs_priv_cells. rewrite ES. exact ZQ'.
      - exact DR'.
      - exact PT'.
      - exact DCL.
      - exact ZOK'. }

    replace (to_bytes (zstore oldc 0 bs)) with (outv rest0 (ds_strm sF)); [exact DOUT'|].
    rewrite zstore_at by (clear - CL ROOM LBS LOUT; lia).
    rewrite to_bytes_app, to_bytes_app, to_bytes_firstn, to_bytes_skipn, to_bytes_skipn. cbn [Z.to_nat firstn skipn].
    unfold outv. subst rest0. rewrite Ebs. unfold zb8, to_bytes. rewrite length_rev. reflexivity.
  Qed.
End CLOSE.
End WithCeiling0.
