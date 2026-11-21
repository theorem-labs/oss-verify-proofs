(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image Arr Frame Mem MState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.MallocU Require Import RMallocRep.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim ZApi ZHarness ZApiL ZHarnessL ZInstL Stdio.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Zlib_iface Zl_iface Z_dview Z_drep Z_dkit Z_zrd Z_defl_iface Z_defl_path Zg_defl_path Zg_defl_pathi Zg_defl_iface Z_dinit_kit Z_deflate Zl_zrd.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Deflate DeflateSafe RefDeflateRel RefDeflSafeI1 RefDeflSafeI2 RefDeflSafeI4 BoundFw BoundCall ZApiInst ZApiInstL ZTaintL DeflateTaintRelG.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wq := (Z_to_bv 64).


Section PURE.
  Variables (sa : deflate_state) (inp : list Z) (x : dstream) (ao flush : Z).
  Hypothesis DR : DRELL sa x.
  Hypothesis PT : PATG sa.
  Hypothesis ZOK : zstrm_okP (dz_z x).
  Hypothesis HIL : ZIface.zlength inp < 2 ^ 31.
  Hypothesis HTIN : zs_total_in (dz_z x) + ZIface.zlength inp < 2 ^ 63.
  Hypothesis HAO : 0 <= ao < 2 ^ 31.
  Hypothesis HD : Forall (fun c => 0 <= c < 256) inp.
  Hypothesis HFL : flush = Z_NO_FLUSH \/ flush = Z_FINISH.

  Definition czcL : ZCall := mkZCall inp ao (dz_z x).
  Definition cd0L : deflate_state := set_strm sa (cstrm_of_call czcL).

  Lemma czcL_wf : dcall_wf czcL.
  Proof.
    unfold dcall_wf, czcL. cbn [zc_strm zc_avail_out zc_input]. split; [exact ZOK|]. split; [lia|]. split; [lia|]. exact HD.
  Qed.

  Lemma HFL3 : flush = Z_NO_FLUSH \/ flush = Z_FINISH \/ flush = Z_BLOCK.
  Proof. destruct HFL as [F|F]; [left| right; left]; exact F. Qed.

  Lemma czcL_path : defl_pathg inp flush (deflate_core cd0L flush) cd0L.
  Proof.
    destruct (zr_dL_facts sa x DR) as (HDD & WS & HS & LBS).
    exact (defl_pathg_intro sa czcL flush HDD czcL_wf PT WS HS LBS HFL3 HIL (proj2 HAO)).
  Qed.

  Lemma czcL_SV : SV (cstrm_of_call czcL) (fst (deflate_core cd0L flush)) /\ PATG (fst (deflate_core cd0L flush))
                  /\ fwT (fst (deflate_core cd0L flush)) = zs_total_in (dz_z x).
  Proof.
    destruct (zr_dL_facts sa x DR) as (HDD & WS & HS & LBS).
    destruct (deflate_core_P2g sa czcL flush HDD czcL_wf PT WS HS LBS HFL3 HIL (proj2 HAO)) as [PF [DCF _]].
    split; [exact (proj2 DCF)|]. split; [exact PF|].
    destruct czcL_path as [[_ E] _]. rewrite E. unfold fwT, cd0L. cbn [ds_strm set_strm cstrm_of_call cs_total_in cs_next_in].
    unfold czcL. cbn [zc_strm]. rewrite Z.sub_0_r. rewrite wrap64_mod. apply Z.mod_small. destruct ZOK as ((T0 & T1) & _). lia.
  Qed.

  Lemma zdl_call_facts :
    let sF := fst (deflate_core cd0L flush) in let cF := ds_strm sF in
    let '(x', consumed, bs, rc) := zdl_deflate inp x ao flush in
    DRELL sF x' /\ PATG sF /\ zstrm_okP (dz_z x')
    /\ rc = snd (deflate_core cd0L flush) /\ bs = rev (cs_out_rev cF)
    /\ zs_total_in (dz_z x') = cs_total_in cF /\ zs_total_out (dz_z x') = cs_total_out cF
    /\ zs_msg (dz_z x') = cs_msg cF /\ zs_data_type (dz_z x') = cs_data_type cF /\ zs_adler (dz_z x') = cs_adler cF
    /\ cs_total_in cF = zs_total_in (dz_z x) + cs_next_in cF
    /\ 0 <= cs_next_in cF <= ZIface.zlength inp /\ cs_avail_in cF = ZIface.zlength inp - cs_next_in cF /\ consumed = cs_next_in cF
    /\ cs_total_out cF = wrap64 (zs_total_out (dz_z x) + Z.of_nat (length (cs_out_rev cF)))
    /\ cs_avail_out cF = ao - Z.of_nat (length (cs_out_rev cF))
    /\ ZIface.zlength bs = Z.of_nat (length (cs_out_rev cF)) /\ Z.of_nat (length (cs_out_rev cF)) <= ao
    /\ Forall (fun c => 0 <= c < 256) bs.
  Proof.
    cbv zeta. pose proof czcL_wf as Hzc.
    pose proof (DRELL_zdl_deflate sa inp x ao flush DR Hzc HFL) as ZD. cbv zeta in ZD. fold czcL in ZD.
    destruct (zdl_deflate inp x ao flush) as [[[x' consumed] bs] rc].
    destruct czcL_SV as (SVF & PATF & FT).
    unfold deflate_m in ZD. fold cd0L in ZD.
    destruct (deflate_core cd0L flush) as [sF rcF] eqn:EC. cbn [fst snd] in *.
    destruct ZD as (DR' & EZ & ECO & EBS & ERC).
    unfold zret_of_cs in EZ, ECO, EBS, ERC. cbn [zr_strm zr_consumed zr_output zr_rc] in EZ, ECO, EBS, ERC.
    pose proof (sv_inlen _ _ SVF) as I1. pose proof (sv_nin _ _ SVF) as I2. pose proof (sv_ain _ _ SVF) as I3.
    pose proof (sv_out _ _ SVF) as O1. pose proof (sv_aout _ _ SVF) as O2. pose proof (sv_tout _ _ SVF) as O3.
    pose proof (sv_tin _ _ SVF) as T1. pose proof (sv_outb _ _ SVF) as OB.
    assert (IL : arr_len (cs_input (cstrm_of_call czcL)) = ZIface.zlength inp) by (cbn [cstrm_of_call cs_input]; rewrite arr_len_of_list; reflexivity).
    rewrite IL in I1.
    assert (EO0 : cs_out_rev (cstrm_of_call czcL) = [] /\ cs_avail_out (cstrm_of_call czcL) = ao /\ cs_total_out (cstrm_of_call czcL) = zs_total_out (dz_z x))
      by (unfold czcL; cbn; repeat split; reflexivity).
    destruct EO0 as (EO1 & EO2 & EO3). rewrite EO1, EO2 in O1. rewrite EO1, EO3 in O3. cbn [zlen length Z.of_nat] in O1, O3. rewrite Z.sub_0_r in O3.
    assert (LBS : ZIface.zlength bs = Z.of_nat (length (cs_out_rev (ds_strm sF)))).
    { rewrite EBS. unfold cs_output. rewrite rev_append_rev, app_nil_r. unfold ZIface.zlength. rewrite length_rev. reflexivity. }
    unfold zlen in O1, O3. cbn [length Z.of_nat] in O1.
    unfold fwT in FT.
    assert (TI : cs_total_in (ds_strm sF) = zs_total_in (dz_z x) + cs_next_in (ds_strm sF)).
    { apply (BoundCall.wrap64_sub_inj _ _ _ ltac:(rewrite FT; symmetry; apply wrap64_id; destruct ZOK as ((A0 & A1) & _); lia) T1).
      destruct ZOK as ((A0 & A1) & _). unfold ZIface.zlength in HIL, HTIN, I1. lia. }
    split; [exact DR'|]. split; [exact PATF|].
    split. { rewrite <- EZ. unfold zstrm_okP, zstrm_of_cs. cbn [zs_total_in zs_total_out zs_adler zs_data_type].
             split; [exact T1|]. split; [rewrite O3; apply wrap64_range|]. split; [exact (sv_adler _ _ SVF)| exact (sv_dt _ _ SVF)]. }
    split; [exact ERC|].
    split; [rewrite EBS; unfold cs_output; rewrite rev_append_rev, app_nil_r; reflexivity|].
    rewrite <- EZ. unfold zstrm_of_cs. cbn [zs_total_in zs_total_out zs_msg zs_data_type zs_adler].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact TI|]. split; [lia|]. split; [lia|]. split; [exact ECO|]. split; [exact O3|]. split; [lia|]. split; [exact LBS|]. split; [lia|].
    rewrite EBS. unfold cs_output. rewrite rev_append_rev, app_nil_r. apply Forall_rev. exact OB.
  Qed.
End PURE.


Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Local Transparent the_zapiL.

Section CLOSE.
  Hypothesis HDEFL : deflate_in_stmtg.

  Theorem deflate_proofL : forall R : zrepsL, zrd R = zr_dL -> deflate_stmtL R.
  Proof.
    intros R RD. unfold deflate_stmtL. intros until B.
    intros ZP ZR PB PF PNI PNI2 CO CL CNO CNO2 HIL HAO T1 T2 T3 T4 HFL SEPO SEPI CIMG SBO SBI SIO ZLS SIF STK CEIL GLO LOSP SP16 SPB B63 MI -> ->.
    rewrite RD in ZR. unfold deflate_postL. rewrite RD.
    unfold dsl_tin, dsl_tout in *. cbn [dl_deflate the_zapiL ZApiInstL.zinstL] in *.
    unfold Prelim.zlength, ZIface.zlength in *.
    destruct ZR as (L & sa & b & ELB & ES & DQ & DR & PT & DCL & ZOK). subst LBz.
    assert (HIL' : ZIface.zlength inp < 2 ^ 31) by (unfold ZIface.zlength; exact HIL).
    assert (HTIN' : zs_total_in (dz_z ds) + ZIface.zlength inp < 2 ^ 63) by (unfold ZIface.zlength; clear - T1 T2; lia).
    pose proof (zdl_call_facts sa inp ds ao flush DR PT ZOK HIL' HTIN' HAO PF HFL) as FACTS.
    pose proof (czcL_path sa inp ds ao flush DR PT ZOK HIL' HAO PF HFL) as PATH.
    cbv zeta in FACTS. unfold ZIface.zlength in FACTS.
    destruct (zdl_deflate inp ds ao flush) as [[[x' consumed] bs] rc].
    remember (fst (deflate_core (cd0L sa inp ds ao) flush)) as sF eqn:EsF.
    remember (snd (deflate_core (cd0L sa inp ds ao) flush)) as rcF eqn:ErcF.
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
    assert (DREP0 : DREP m L' (cd0L sa inp ds ao)).
    { split.
      - destruct (proj1 DQ) as (p3 & resv & ZQ). exists p1, p2, p3, resv.
        assert (ZS : rw_cells usegs m S (zs_pub NI (Z.of_nat (length inp)) tin NO ao tout p1 p2 ++ zs_priv_cells L (zs_msg (dz_z ds)) (zs_data_type (dz_z ds)) (zs_adler (dz_z ds)) p3 resv)).
        { apply (proj2 (Startup_glue.rw_cells_app usegs m S _ _)). split; [exact ZP|]. rewrite ES in ZQ.
          lazymatch goal with |- rw_cells _ _ (_ + Z.of_nat ?n) _ => replace (Z.of_nat n) with 48 by reflexivity end. exact ZQ. }
        subst L'. unfold dl_io, zs_call_cells, zs_priv_cells, cd0L, czcL. cbn [dl_S dl_As dl_NI dl_NO ds_strm set_strm cstrm_of_call zc_input zc_avail_out zc_strm
          cs_next_in cs_avail_in cs_total_in cs_out_rev cs_avail_out cs_total_out cs_msg cs_data_type cs_adler length Z.of_nat app].
        rewrite ES. unfold zs_pub, zs_priv_cells in ZS. cbn [app] in ZS.
        fold tin. fold tout. unfold ZIface.zlength.
        close_cells ZS.
      - subst L'. apply DST_io. apply DST_set_strm; [intros H; exact H| exact (proj2 DQ)]. }
    assert (DIN0 : din m L' inp).
    { subst L'. unfold din, dl_io. cbn [dl_NI]. exact PB. }
    assert (DOUT0 : dout m L' rest0 (ds_strm (cd0L sa inp ds ao))).
    { subst L'. unfold dout, outv, dl_io, cd0L, czcL. cbn [dl_NO ds_strm set_strm cstrm_of_call cs_out_rev rev zb8 map length skipn app]. subst rest0. exact CO. }
    pose proof (relro_clean_of_zl _ ZLS) as RC.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (BEL : dlay_below L' lo (bv_unsigned sp)).
    { subst L'. unfold dlay_below, dl_io. cbn [dl_S dl_As dl_Aw dl_Ap dl_Ah dl_Ab]. rewrite ES. clear - DCL CEIL GLO SIF. lia. }
    assert (IO : dio_sep L' (ZIface.zlength (zc_input (czcL inp ds ao))) (Z.of_nat (length rest0)) lo).
    { unfold czcL, ZIface.zlength. cbn [zc_input]. rewrite LR0. subst L'. unfold dl_io.
      pose proof (unbox _ Yb) as Xb. pose proof (unbox _ Yh) as Xh. pose proof (unbox _ Yp) as Xp. pose proof (unbox _ Yw) as Xw. pose proof (unbox _ Ys) as Xs.
      pose proof (unbox _ CIMG) as XI. pose proof (unbox _ SIO) as XIO.
      constructor; cbn [dl_NI dl_NO dl_As dl_Aw dl_Ap dl_Ah dl_Ab]; unfold apart.
      - clear - PNI SEPI. lia.
      - clear - CNO HAO SEPO. lia.
      - clear - XI. lia.
      - clear - XIO. lia.
      - clear - Xs. lia. - clear - Xw. lia. - clear - Xp. lia. - clear - Xh. lia. - clear - Xb. lia.
      - clear - Xs. lia. - clear - Xw. lia. - clear - Xp. lia. - clear - Xh. lia. - clear - Xb. lia. }
    assert (ROOM' : (length (cs_out_rev (ds_strm (fst (deflate_core (cd0L sa inp ds ao) flush)))) <= length rest0)%nat).
    { rewrite <- EsF. clear - ROOM LR0. lia. }
    eapply evt_mono.
    { eapply (HDEFL L' (cd0L sa inp ds ao) flush inp rest0 lo);
        [ exact DREP0 | exact DIN0 | exact DOUT0 | exact MI | exact RC | exact STK
        | unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK; clear - LOSP; lia | exact SP16 | exact BEL | exact IO
        | exact (HFL3 flush HFL) | exact PATH | exact ROOM'
        | subst L'; unfold dl_io; cbn [dl_S]; rewrite ES; reflexivity | reflexivity ]. }
    intros ms' POST. cbv beta.
    destruct POST as (u0 & u1 & u2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & STK' & DREP' & DIN' & DOUT').
    rewrite <- EsF, <- ErcF in *.
    destruct DREP' as [ZS' ST']. destruct ZS' as (q1 & q2 & q3 & qr & ZS').
    subst L'. unfold zs_call_cells, zs_priv_cells, dl_io in ZS'. cbn [dl_S dl_NI dl_NO dl_As app] in ZS'. rewrite ES in ZS'.
    lazymatch type of ZS' with rw_cells _ _ _ ?cs =>
      let a := eval cbv beta iota delta [firstn] in (firstn 8 cs) in let b' := eval cbv beta iota delta [skipn] in (skipn 8 cs) in
      change (rw_cells usegs m' S (a ++ b')) in ZS' end.
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
        assert (ROM : seg_rom usegs y = None) by (apply RMallocRep.ref_seg_rom_none; clear - XI H1 H2 CNO LBS; lia).
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
    { rewrite <- ES. apply (zr_dL_intro m' L sF (psp, pw, pp, ph, pb) x').
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
