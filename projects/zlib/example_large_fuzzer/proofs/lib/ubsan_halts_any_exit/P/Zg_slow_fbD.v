(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit F_memcpy.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk DeflateOverlay SendModel FillWinModel
  RefFlushBlk13 RefDeflFast1 RefDeflFastM RefDeflFast6 ZCorollaries.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section FBD.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.
Hypothesis HTFBLK : tr_flush_block_stmt.
Hypothesis HTFB : tr_flush_bits_stmt.

Lemma slow_fbD : forall (Q : machine_state -> Prop) (X : deflate_state)
    (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x25 x28 x29 x30 x31 : word) (m : mem),
  SINV L flush rest0 lo r me X m ->
  flush_ok X 0 -> ds_lit_bufsize X = 16384 -> ds_w_size X = 32768 -> 0 <= cs_avail_out (ds_strm X) < 2^31 ->
  (length (cs_out_rev (ds_strm (flush_block_only X 0))) <= length rest0)%nat ->
  SKx L flush rest0 lo r F fc me Q 0x1a058 (flush_block_only X 0) ->
  evt psegs Q (MS (slowR L r x1 x5 x6 x7 (wz flush) (wz (ds_strstart X)) x11 x12 x13 x14 x15 x16 x17 x18 x19 x25 x28 x29 x30 x31) F (wz 0x19ee0) fc None m (seg_rom psegs)).

Proof.
  intros until m. intros (DR & DOUT & _ & (j0 & FR) & STK & MU & WM & MI) FOK LBS WSX RAO ROOM HK.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp.
  apply box in SP16.
  assert (OL0 : (length (cs_out_rev (ds_strm X)) <= length rest0)%nat) by (pose proof (fbo_out_mono X 0); lia).
  pose proof (outv_length rest0 (ds_strm X) OL0) as OL. clear OL0.
  apply box in ROOM.
  destruct (fbo_buf_ok X 0 FOK WSX) as (BOK & ELEN & EBP & EBN).
  destruct (flush_ok_fbo X 0 FOK LBS) as (FBS & BI & Rdiff & Rbs & Rss & Rla & Rwb & BI9 & PB10 & RP10 & RPO10 & RPOL & RTO).
  rewrite WSX in Rss, Rla.
  pose proof DR as DR0. destruct DR as [ZS ST]. open_DST ST. open_A GA. lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold slowR. unfold slow_frame in FR. unfold slow_W in MU.
  assert (RBS : - 2^63 <= ds_block_start X < 2^63) by lia.

  zs. zs.
  eapply (evt_cut psegs (fun ms' => ms' = _)).
  { if_cases KB; zify_cond KB.
    -
      assert (NEG : ds_block_start X < 0) by (change (2^63) with 9223372036854775808 in RBS; Z.div_mod_to_equations; lia).
      do 4 zs. rewrite ?Z.mod_small by lia.
      replace (wz 0) with (wz (match fb_buf X with Some off => dl_Aw L + off | None => 0 end)) at 1 by (rewrite (EBN NEG); reflexivity).
      apply evt_done. reflexivity.
    - assert (POS : 0 <= ds_block_start X) by (change (2^63) with 9223372036854775808 in RBS; Z.div_mod_to_equations; lia).
      do 8 zs. rewrite ?Z.mod_small by lia.
      replace (wz (dl_Aw L + Z.land (ds_block_start X) 4294967295)) with (wz (match fb_buf X with Some off => dl_Aw L + off | None => 0 end))
        by (rewrite (EBP POS); fold (wrap32 (ds_block_start X)); rewrite wrap32_id by lia; reflexivity).
      apply evt_done. reflexivity. }
  intros ms' ->.
  replace (wz (ds_strstart X - ds_block_start X mod 18446744073709551616)) with (wz (fb_len X))
    by (apply Z_to_bv_eqm; rewrite ELEN; Z.div_mod_to_equations; lia).
  zs.

  assert (RL : relro_clean m) by (apply (slow_relro L inp rest0 lo r me CTX); exact MU).
  assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -128)) = bv_unsigned (r_sp r) + -128) by (apply unsigned_lit; lia).
  clear GA ZS GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend.
  unfold dout in DOUT.

  call (HTFBLK L X (fb_buf X) (fb_len X) 0 lo).
  1:{ exact DR0. } 1:{ exact MI. } 1:{ exact RL. } 1:{ rewrite ESP. exact STK. } 1:{ unfold Z_TRFB_STACK in *. lia. }
  1:{ rewrite ESP. pose proof (unbox _ SP16). Z.div_mod_to_equations. lia. }
  1:{ unfold dlay_below. lia. }
  1:{ exact BI. } 1:{ exact FBS. } 1:{ exact BOK. } 1:{ unfold fb_len. apply wrap64_range. } 1:{ lia. }
  1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  name_mem mA. rewrite ESP in PC.
  change (tr_flush_block X (fb_buf X) (fb_len X) 0) with (fbo1 X 0) in POST.
  pose proof (fbo_eq X 0) as EFB.
  destruct (tfb_keep X 0) as (E1 & _ & EO & EAO). pose proof (fbo3_strm X 0) as ES.
  unfold fbo3, fbo2 in EFB, ES, BI9, PB10, RP10, RPO10, RPOL, RTO.
  remember (fbo1 X 0) as X1 eqn:EX1.
  assert (DOUT1 : u8arr psegs mA (dl_NO L) (outv rest0 (ds_strm X1))) by (unfold outv; rewrite EO; exact DOUT).
  assert (OL1 : length (outv rest0 (ds_strm X1)) = length rest0) by (unfold outv; rewrite EO; exact OL).
  assert (RAO1 : 0 <= cs_avail_out (ds_strm X1) < 2^31) by (rewrite EAO; exact RAO).
  clear DOUT OL.
  destruct POST as [ZS ST]. open_zs ZS.
  destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS1 LAY1]. open_A GA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] mA) as MUf. pose proof (wmono_refl psegs mA) as WMf.

  do 4 zs. name_mem mB.
  tr_groups MUf WMf.
  remember (set_block_start X1 (ds_strstart X1)) as X2 eqn:EX2.
  assert (ST2 : DST mB L X2).
  { rewrite EX2. constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS1 | exact LAY1]. }
  clear MUf WMf GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend.

  zs. zs.
  call (HTFB L X2).
  1:{ exact ST2. } 1:{ eassumption. } 1:{ exact BI9. } 1:{ exact PB10. } 1:{ reflexivity. }
  name_mem mC.
  remember (tr_flush_bits X2) as d1 eqn:Ed1.
  assert (EL : fp_len d1 = if cs_avail_out (ds_strm X1) <? ds_pending d1 then cs_avail_out (ds_strm X1) else ds_pending d1).
  { unfold fp_len. rewrite ES, wrap32_id by lia. reflexivity. }
  remember (fp_len d1) as flen eqn:Eflen. clear Eflen.
  clear FOK LBS WSX RAO BOK ELEN EBP EBN FBS BI Rdiff Rbs Rss Rla Rwb DR0 RBS RL E1 EO EAO ST2 LENS I0 BI9 PB10 EX1 EX2 Ed1.
  destruct POST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENSd LAYd]. open_A GA.
  pose proof (munch_refl [(dl_S L, dl_S L + 112); (dl_As L, dl_As L + 212); (dl_NO L, dl_NO L + Z.of_nat (length rest0))] mC) as MUf.
  pose proof (wmono_refl psegs mC) as WMf.

  zs. zs. zstep. (* 1.4: ld pending whole, lwu avail_out *)
  assert (FL : 0 <= flen /\ flen <= cs_avail_out (ds_strm X1) /\ flen <= ds_pending d1) by (destruct (Z.ltb_spec (cs_avail_out (ds_strm X1)) (ds_pending d1)); lia).
  eapply (evt_cut psegs (fun ms' => ms' = _)).
  { if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
    - replace (cs_avail_out (ds_strm X1) <? ds_pending d1) with false in EL by (symmetry; apply Z.ltb_ge; lia).
      replace (wz (ds_pending d1)) with (wz flen) by (f_equal; lia). apply evt_done. reflexivity.
    - assert (EA : flen = cs_avail_out (ds_strm X1)) by (destruct (Z.ltb_spec (cs_avail_out (ds_strm X1)) (ds_pending d1)); lia).
      zstep. apply evt_done. rewrite EA. reflexivity. }
  intros ms' ->. clear EL.
  zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia.
  -
    assert (SI : SINV L flush rest0 lo r me (flush_block_only X 0) mC).
    { replace (flen =? 0) with true in EFB by (symmetry; apply Z.eqb_eq; lia).
      split; [rewrite EFB; split|split; [rewrite EFB|split; [exact ROOM|]]].
      - rewrite ES. do 4 eexists. exact ZS.
      - constructor; [do 5 eexists; exact GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                     | exact Gwin| exact Gprev| exact Ghead| exact Gpend| exact LENSd| exact LAYd].
      - rewrite ES; exact DOUT1.
      - split; [exists j0; exact FR|]. split; [exact PC|]. split; [exact MU|]. split; [exact WM| eassumption]. }

    eapply HK. exact SI.

  -
    replace (flen =? 0) with false in EFB by (symmetry; apply Z.eqb_neq; lia).
    do 4 zstep. rewrite ?Z.mod_small by lia.
    remember (length (cs_out_rev (ds_strm X1))) as k eqn:Ek.
    assert (KL : (k + Z.to_nat flen <= length rest0)%nat).
    { apply unbox in ROOM. rewrite EFB, fp_tail_out, cs_emit_out_len', ES, <- Ek, arr_slice_length' in ROOM. lia. }
    pose proof (u8arr_sub_bytes _ (dl_Ab L) _ (Z.to_nat (ds_pending_out d1)) (Z.to_nat flen) Gpend ltac:(rewrite av8_length; lia)) as SRC.
    rewrite av8_slice in SRC by lia. rewrite Z2Nat.id in SRC by lia.
    assert (LSRC : length (map (Z_to_bv 8) (arr_slice (ds_pending_buf d1) (ds_pending_out d1) flen)) = Z.to_nat flen)
      by (rewrite length_map; apply arr_slice_length').
    destruct (u8arr_split3 _ (dl_NO L) _ k (Z.to_nat flen) DOUT1 ltac:(rewrite OL1; lia)) as (O1 & O2 & O3). clear DOUT1.
    assert (LO1 : length (firstn k (outv rest0 (ds_strm X1))) = k) by (rewrite length_firstn, OL1; lia).
    assert (LO3 : length (skipn (k + Z.to_nat flen) (outv rest0 (ds_strm X1))) = (length rest0 - (k + Z.to_nat flen))%nat) by (rewrite length_skipn, OL1; lia).
    call (memcpy_Z (dl_NO L + Z.of_nat k) (dl_Ab L + ds_pending_out d1) flen).
    1:{ exact SRC. } 1:{ exact LSRC. } 1:{ exact O2. } 1:{ zsep. } 1:{ eassumption. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
    pose proof (u8arr_join3k _ (dl_NO L) _ _ _ k (Z.to_nat flen) LO1 O1 PC0 O3) as OUT.
    fold (zb8 (arr_slice (ds_pending_buf d1) (ds_pending_out d1) flen)) in OUT.
    rewrite <- (arr_slice_length' (ds_pending_buf d1) (ds_pending_out d1) flen) in OUT. rewrite Ek in OUT.
    rewrite <- outv_emit in OUT by (rewrite <- Ek, arr_slice_length'; exact KL).
    assert (OL' : length (outv rest0 (cs_emit (ds_strm X1) (arr_slice (ds_pending_buf d1) (ds_pending_out d1) flen))) = length rest0).
    { apply outv_length. rewrite cs_emit_out_len, arr_slice_length', <- Ek. lia. }
    clear O1 O3 PC0 POST SRC LSRC LO1 LO3.
    do 16 zs.
    if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
    +
      unfold fp_tail in EFB. cbv zeta in EFB. replace (ds_pending d1 - flen =? 0) with false in EFB by (symmetry; apply Z.eqb_neq; lia).
      tr_groups MUf WMf.
      match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (SI : SINV L flush rest0 lo r me (flush_block_only X 0) mm) end.
      { split; [rewrite EFB; split|split; [rewrite EFB|split; [exact ROOM|]]].
        - rewrite ES. eexists _, _, _, _; unfold zs_call_cells, zs_priv_cells; cbn [app]; unfold cs_emit; dsred;
          rewrite ?rev_append_rev, ?length_app, ?length_rev, ?arr_slice_length', <- ?Ek; close_cells ZS.
        - constructor; [eexists _, _, _, _, _; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                       | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENSd | exact LAYd].
        - rewrite ES; dsred; exact OUT.
        - split; [exists j0; exact FR|]. split; [exact PC|]. split; [exact MU|]. split; [exact WM| eassumption]. }

      eapply HK. exact SI.

    +

      do 2 zs.

      unfold fp_tail in EFB. cbv zeta in EFB. replace (ds_pending d1 - flen =? 0) with true in EFB by (symmetry; apply Z.eqb_eq; lia).
      tr_groups MUf WMf.
      match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (SI : SINV L flush rest0 lo r me (flush_block_only X 0) mm) end.
      { split; [rewrite EFB; split|split; [rewrite EFB|split; [exact ROOM|]]].
        - rewrite ES. eexists _, _, _, _; unfold zs_call_cells, zs_priv_cells; cbn [app]; unfold cs_emit; dsred;
          rewrite ?rev_append_rev, ?length_app, ?length_rev, ?arr_slice_length', <- ?Ek; close_cells ZS.
        - constructor; [eexists _, _, _, _, _; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                       | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENSd | exact LAYd].
        - rewrite ES; dsred; exact OUT.
        - split; [exists j0; exact FR|]. split; [exact PC|]. split; [exact MU|]. split; [exact WM| eassumption]. }

      eapply HK. exact SI.

Qed.
End FBD.
