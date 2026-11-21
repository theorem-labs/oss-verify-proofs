(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Z_defl_kit Z_defl_arms F_memcpy.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate SendModel FillWinModel RefDeflFast1 RefDeflFastM DeflateSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* 1.4 (zl14-cmp): the inlined flush_pending keeps len in s2 (1.3.1: s3, then zero-extended into s2) *)
Ltac join_x18 v pcj :=
  lazymatch goal with
  | |- evt _ _ (MS (TNode ?Lt None (TNode ?A ?o2 (TNode (TNode (TNode TEmpty (Some _) TEmpty) ?o10 ?B) ?o6 ?C))) ?F _ ?fc None ?m ?rom) =>
      eapply (evt_cut psegs (fun ms' => ms' = MS (TNode Lt None (TNode A o2 (TNode (TNode (TNode TEmpty (Some v) TEmpty) o10 B) o6 C))) F (wz pcj) fc None m rom))
  end.

Section PENDG.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : defl_ctx L inp rest0 lo r me.
Hypothesis HTFB : tr_flush_bits_stmt.

Lemma defl_pendg : forall (Q : machine_state -> Prop) (d : deflate_state)
    (y1 y5 y6 y7 y9 y12 y15 y16 y17 y28 y29 y30 y31 : word) (m : mem),
  DINV L rest0 lo r me d m ->
  (flush = 0 \/ flush = 4 \/ flush = 5) ->
  0 <= cs_avail_out (ds_strm d) < 2^31 -> 0 <= cs_avail_in (ds_strm d) < 2^31 -> - 2 <= ds_last_flush d <= 5 ->
  0 <= ds_pending d <= 65536 -> ds_lit_bufsize d = 16384 ->
  (cs_avail_out (ds_strm d) <> 0 -> ds_pending d <> 0 -> fp_ok (set_last_flush d flush)) ->
  (cs_avail_out (ds_strm d) <> 0 -> ds_pending d <> 0 -> 0 <= ds_status (flush_pending (set_last_flush d flush)) < 1000) ->
  (cs_avail_out (ds_strm d) <> 0 -> ds_pending d <> 0 -> Box (length (cs_out_rev (ds_strm (flush_pending (set_last_flush d flush)))) <= length rest0)%nat) ->

  (cs_avail_out (ds_strm d) = 0 -> DKE L rest0 lo r F fc me Q (wz (-5)) (fst (err_return d Z_BUF_ERROR))) ->

  (cs_avail_out (ds_strm d) <> 0 -> ds_pending d <> 0 -> cs_avail_out (ds_strm (flush_pending (set_last_flush d flush))) = 0 ->
   DKL L flush rest0 lo r F fc me Q (flush_pending (set_last_flush d flush))) ->
  (cs_avail_out (ds_strm d) <> 0 -> ds_pending d <> 0 -> cs_avail_out (ds_strm (flush_pending (set_last_flush d flush))) <> 0 ->
   DKB L flush rest0 lo r F fc me Q (flush_pending (set_last_flush d flush))) ->

  (cs_avail_out (ds_strm d) <> 0 -> ds_pending d = 0 -> rank_err d flush ->
   DKE L rest0 lo r F fc me Q (wz (-5)) (fst (err_return (set_last_flush d flush) Z_BUF_ERROR))) ->
  (cs_avail_out (ds_strm d) <> 0 -> ds_pending d = 0 -> ~ rank_err d flush -> DKB L flush rest0 lo r F fc me Q (set_last_flush d flush)) ->
  evt psegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) y9 (wz (dl_S L)) (wz flush) y12 (wz (ds_status d)) (wz (cs_avail_in (ds_strm d))) y15 y16 y17
                       (r_s2 r) (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) y28 y29 y30 y31) F (wz 0x16fa0) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros (DR & DOUT & ROOM & FR & STK & MU & WM & MI) HFL RAO RAI RLF RP LBS FPOK RST2 ROOMF KBUF KLF KB1 KRK KB0.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp. apply box in SP16.
  pose proof DR as DR0.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_zs ZS. open_A GA. lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold defl_frame in FR. unfold defl_W in MU.
  zs. zstep. if_cases KAO; zify_cond KAO; rewrite ?unsigned_lit in KAO by lia.
  -
    eapply (defl_buferr L inp rest0 lo r F fc me CTX Q d 0x17058); [left; reflexivity| |apply KBUF; lia].
    split; [exact DR0|]. split; [exact DOUT|]. split; [exact ROOM|]. split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| exact MI].
  - pose proof (munch_refl [(dl_As L, dl_As L + 212)] m) as MUf. pose proof (wmono_refl psegs m) as WMf.
    zs. zs. zs. name_mem mA. zs. zs. zstep.
    tr_groups MUf WMf.
    remember (set_last_flush d flush) as s1 eqn:Es1.
    assert (ST1 : DST mA L s1).
    { rewrite Es1. constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY1]. }
    assert (DOUT1 : dout mA L rest0 (ds_strm s1)).
    { rewrite Es1. dsred. apply (dout_munch _ m mA L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia. }
    if_cases KP; zify_cond KP; rewrite ?unsigned_lit in KP by lia.
    +
      assert (P0 : ds_pending d = 0) by lia.
      specialize (KRK ltac:(lia) P0). specialize (KB0 ltac:(lia) P0). clear KLF KB1 KBUF FPOK ROOMF RST2.
      assert (DI1 : DINV L rest0 lo r me s1 mA).
      { split; [split; [rewrite Es1; dsred; do 4 eexists; exact ZS| exact ST1]|]. split; [exact DOUT1|]. split; [rewrite Es1; dsred; exact ROOM|].
        split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. }
      assert (C_C1C : forall (a12 y14 y15 y16 : word), a12 = wz 0 -> ~ rank_err d flush ->
        evt psegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) (wz (dl_S L)) (wz (dl_S L)) (wz flush) a12 (wz (ds_status d)) y14 y15 y16 y17
                       (r_s2 r) (r_s3 r) (r_s4 r) (r_s5 r) (wz flush) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) y28 y29 y30 y31) F (wz 0x17078) fc None mA (seg_rom psegs))).
      { intros a12 z14 z15 z16 -> NR. specialize (KB0 NR). unfold DKB, deflR in KB0.
        replace (wz 0) with (wz (ds_pending s1)) by (rewrite Es1; dsred; rewrite P0; reflexivity).
        replace (wz (ds_status d)) with (wz (ds_status s1)) by (rewrite Es1; reflexivity).
        eapply KB0. exact DI1. }
      clear KB0.
      zstep. if_cases KI; zify_cond KI; rewrite ?unsigned_lit in KI by lia.
      *
        zs. zs. zstep. if_cases KF4; zify_cond KF4; rewrite ?unsigned_lit in KF4 by lia.
        -- apply C_C1C; [reflexivity|]. unfold rank_err, Z_FINISH. lia.
        -- assert (F05 : flush = 0 \/ flush = 5) by lia.
           assert (HLF : ds_last_flush d = -2 \/ ds_last_flush d = -1 \/ ds_last_flush d = 0 \/ ds_last_flush d = 1 \/ ds_last_flush d = 2
                         \/ ds_last_flush d = 3 \/ ds_last_flush d = 4 \/ ds_last_flush d = 5) by lia.
           destruct F05 as [F0|F0]; rewrite F0 in *;
           destruct HLF as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; do 11 zs; zstep; if_cases KR.

           all: first [ exfalso; revert KR; vm_compute; intros KR; discriminate KR
                      | clear KR; apply C_C1C; [reflexivity|]; unfold rank_err, RANK; rewrite E; cbn; lia
                      | clear KR; eapply (defl_buferr L inp rest0 lo r F fc me CTX Q s1 0x173c8); [right; left; reflexivity| exact DI1| apply KRK; unfold rank_err, RANK, Z_FINISH; rewrite E; cbn; lia] ].
      * zs. apply C_C1C; [reflexivity|]. unfold rank_err. lia.
    +
      assert (PN0 : ds_pending d <> 0) by lia.
      specialize (FPOK ltac:(lia) PN0). specialize (ROOMF ltac:(lia) PN0). specialize (RST2 ltac:(lia) PN0).
      specialize (KLF ltac:(lia) PN0). specialize (KB1 ltac:(lia) PN0). clear KRK KB0 KBUF.
      destruct FPOK as [BI FPK]. rewrite Es1 in BI, FPK. change (ds_lit_bufsize (set_last_flush d flush)) with (ds_lit_bufsize d) in BI, FPK. rewrite LBS in BI, FPK.
      change (16384 * 4) with 65536 in BI, FPK. rewrite <- Es1 in BI, FPK. cbv zeta in FPK.
      pose proof (tr_flush_bits_strm' s1) as ES.
      pose proof (flush_pending_eq s1) as EF. cbv zeta in EF.
      destruct FPK as (RP1 & RPB & RPO0 & RPO1 & RTO).
      clear GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend MUf WMf.
      assert (ESS : ds_strm s1 = ds_strm d) by (rewrite Es1; reflexivity).
      rewrite ESS in ES, DOUT1. unfold dout in DOUT1.
      assert (OL0 : (length (cs_out_rev (ds_strm d)) <= length rest0)%nat) by (exact (unbox _ ROOM)).
      pose proof (outv_length rest0 (ds_strm d) OL0) as OL. clear OL0.

      assert (C_BEC : forall (X' : deflate_state) (a11 a12 y1 y5 y6 y7 y13 y14 y15 y16 y17 y18 y19 y21 y22 y28 y29 y30 y31 : word) (m' : mem),
        X' = flush_pending s1 -> DINV L rest0 lo r me X' m' -> 0 <= cs_avail_out (ds_strm X') < 2^31 ->
        a11 = wz (cs_avail_out (ds_strm X')) -> a12 = wz (ds_pending X') ->
        evt psegs Q (MS (deflR L flush r y1 y5 y6 y7 (wz (dl_S L)) a11 a12 y13 y14 y15 y16 y17 y18 y19 y21 y22 y28 y29 y30 y31)
                        F (wz 0x17044) fc None m' (seg_rom psegs))).
      { intros X' a11 a12 z1 z5 z6 z7 z13 z14 z15 z16 z17 z18 z19 z21 z22 z28 z29 z30 z31 m' EX' DI' RAO' -> ->.
        (* 1.4: sext.w a1,a1 before the beqz *)
        unfold deflR. zs. zstep. if_cases KA'; zify_cond KA'; rewrite ?unsigned_lit in KA' by lia.
        - rewrite EX' in *. eapply (KLF ltac:(lia)). exact DI'.
        - pose proof DI' as DI0. destruct DI' as (DR' & _ & _ & FR' & STK' & _ & _ & MI').
          destruct DR' as [_ ST']. destruct ST' as [GA' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. open_A GA'.
          rewrite EX' in *.
          zs. zs. zs. eapply (KB1 ltac:(lia)). exact DI0. }
      clear KLF KB1.
      zs. zs.
      call (HTFB L s1).
      1:{ exact ST1. } 1:{ eassumption. } 1:{ exact BI. } 1:{ exact RPB. } 1:{ reflexivity. }
      name_mem mC.
      remember (tr_flush_bits s1) as d1 eqn:Ed1.
      assert (EL : fp_len d1 = if cs_avail_out (ds_strm d) <? ds_pending d1 then cs_avail_out (ds_strm d) else ds_pending d1).
      { unfold fp_len. rewrite ES, wrap32_id by lia. reflexivity. }
      remember (fp_len d1) as flen eqn:Eflen. clear Eflen.
      destruct POST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENSd LAYd]. open_A GA.
      pose proof (munch_refl [(dl_S L, dl_S L + 112); (dl_As L, dl_As L + 212); (dl_NO L, dl_NO L + Z.of_nat (length rest0))] mC) as MUf.
      pose proof (wmono_refl psegs mC) as WMf.
      (* 1.4: mv a0,s1; ld a2 (pending, whole); lwu a1 (avail_out); mv s2,a2; bltu a2,a1 (taken = pending < avail_out) *)
      zs. zs. zs. zs. zstep.
      assert (FL : 0 <= flen /\ flen <= cs_avail_out (ds_strm d) /\ flen <= ds_pending d1) by (destruct (Z.ltb_spec (cs_avail_out (ds_strm d)) (ds_pending d1)); lia).
      join_x18 (wz flen) 0x16fe0.
      { if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
        - assert (E : flen = ds_pending d1) by (destruct (Z.ltb_spec (cs_avail_out (ds_strm d)) (ds_pending d1)); lia).
          rewrite E. apply evt_done. reflexivity.
        - assert (E : flen = cs_avail_out (ds_strm d)) by (destruct (Z.ltb_spec (cs_avail_out (ds_strm d)) (ds_pending d1)); lia).
          rewrite E. zstep. apply evt_done. reflexivity. }
      intros ms' ->. clear EL.
      zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia.
      *
        assert (EX : flush_pending s1 = d1) by (rewrite EF; replace (flen =? 0) with true by (symmetry; apply Z.eqb_eq; lia); reflexivity).
        assert (DI : DINV L rest0 lo r me d1 mC).
        { split; [split|].
          - rewrite ES. do 4 eexists. exact ZS.
          - constructor; [do 5 eexists; exact GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                         | exact Gwin| exact Gprev| exact Ghead| exact Gpend| exact LENSd| exact LAYd].
          - split; [unfold dout; rewrite ES; exact DOUT1|]. split; [rewrite ES; exact ROOM|].
            split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. }
        eapply (C_BEC d1); [symmetry; exact EX| exact DI| rewrite ES; lia| rewrite ES; reflexivity| reflexivity].
      *
        replace (flen =? 0) with false in EF by (symmetry; apply Z.eqb_neq; lia).
        (* 1.4: no sll/srl zero-extension of len *)
        do 4 zstep. rewrite ?Z.mod_small by lia.
        remember (length (cs_out_rev (ds_strm d))) as k eqn:Ek.
        assert (KL : (k + Z.to_nat flen <= length rest0)%nat).
        { apply unbox in ROOMF. rewrite EF, fp_tail_out, cs_emit_out_len', ES, <- Ek, arr_slice_length' in ROOMF. lia. }
        pose proof (u8arr_sub_bytes _ (dl_Ab L) _ (Z.to_nat (ds_pending_out d1)) (Z.to_nat flen) Gpend ltac:(rewrite av8_length; lia)) as SRC.
        rewrite av8_slice in SRC by lia. rewrite Z2Nat.id in SRC by lia.
        assert (LSRC : length (map (Z_to_bv 8) (arr_slice (ds_pending_buf d1) (ds_pending_out d1) flen)) = Z.to_nat flen)
          by (rewrite length_map; apply arr_slice_length').
        destruct (u8arr_split3 _ (dl_NO L) _ k (Z.to_nat flen) DOUT1 ltac:(rewrite OL; lia)) as (O1 & O2 & O3). clear DOUT1.
        assert (LO1 : length (firstn k (outv rest0 (ds_strm d))) = k) by (rewrite length_firstn, OL; lia).
        assert (LO3 : length (skipn (k + Z.to_nat flen) (outv rest0 (ds_strm d))) = (length rest0 - (k + Z.to_nat flen))%nat) by (rewrite length_skipn, OL; lia).
        call (memcpy_Z (dl_NO L + Z.of_nat k) (dl_Ab L + ds_pending_out d1) flen).
        1:{ exact SRC. } 1:{ exact LSRC. } 1:{ exact O2. } 1:{ zsep. } 1:{ eassumption. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
        name_mem mD.
        pose proof (u8arr_join3k _ (dl_NO L) _ _ _ k (Z.to_nat flen) LO1 O1 PC O3) as OUT.
        fold (zb8 (arr_slice (ds_pending_buf d1) (ds_pending_out d1) flen)) in OUT.
        rewrite <- (arr_slice_length' (ds_pending_buf d1) (ds_pending_out d1) flen) in OUT. rewrite Ek in OUT.
        rewrite <- outv_emit in OUT by (rewrite <- Ek, arr_slice_length'; exact KL).
        assert (OL' : length (outv rest0 (cs_emit (ds_strm d) (arr_slice (ds_pending_buf d1) (ds_pending_out d1) flen))) = length rest0).
        { apply outv_length. rewrite cs_emit_out_len, arr_slice_length', <- Ek. lia. }
        clear O1 O3 PC POST SRC LSRC LO1 LO3.
        do 16 zs. zstep.
        if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
        --
          unfold fp_tail in EF. cbv zeta in EF. replace (ds_pending d1 - flen =? 0) with false in EF by (symmetry; apply Z.eqb_neq; lia).
          tr_groups MUf WMf.
          match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (DI : DINV L rest0 lo r me (flush_pending s1) mm) end.
          { split; [rewrite EF; split|split; [rewrite EF|split; [exact ROOMF|]]].
            - rewrite ES. eexists _, _, _, _; unfold zs_call_cells, zs_priv_cells; cbn [app]; unfold cs_emit; dsred;
              rewrite ?rev_append_rev, ?length_app, ?length_rev, ?arr_slice_length', <- ?Ek; close_cells ZS.
            - constructor; [eexists _, _, _, _, _; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                           | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENSd | exact LAYd].
            - unfold dout. rewrite ES; dsred; exact OUT.
            - split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. }
          eapply (C_BEC (flush_pending s1)); [reflexivity| exact DI| rewrite EF; dsred; rewrite ES; lia| rewrite EF; dsred; rewrite ES; reflexivity| rewrite EF; dsred; reflexivity].
        --
          do 3 zs.
          unfold fp_tail in EF. cbv zeta in EF. replace (ds_pending d1 - flen =? 0) with true in EF by (symmetry; apply Z.eqb_eq; lia).
          tr_groups MUf WMf.
          match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (DI : DINV L rest0 lo r me (flush_pending s1) mm) end.
          { split; [rewrite EF; split|split; [rewrite EF|split; [exact ROOMF|]]].
            - rewrite ES. eexists _, _, _, _; unfold zs_call_cells, zs_priv_cells; cbn [app]; unfold cs_emit; dsred;
              rewrite ?rev_append_rev, ?length_app, ?length_rev, ?arr_slice_length', <- ?Ek; close_cells ZS.
            - constructor; [eexists _, _, _, _, _; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                           | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENSd | exact LAYd].
            - unfold dout. rewrite ES; dsred; exact OUT.
            - split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. }
          eapply (C_BEC (flush_pending s1)); [reflexivity| exact DI| rewrite EF; dsred; rewrite ES; lia| rewrite EF; dsred; rewrite ES; reflexivity| rewrite EF; dsred; f_equal; lia].
Qed.
End PENDG.
