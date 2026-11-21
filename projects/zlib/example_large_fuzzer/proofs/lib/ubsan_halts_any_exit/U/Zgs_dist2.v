(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Z_tr_rod Z_ukit Zgs_dist1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk FillWinModel LmatchModel
  RefDeflFast1 RefDeflFastM RefDeflFast6 RefDeflSlow2 RefDeflSlow3 RefDeflSlow6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Section DIST2.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (fj : list byte) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.
Hypothesis HFL : 0 <= flush <= 5.
Definition KINS (Q : machine_state -> Prop) (T : deflate_state) (mi : Z) (v11 v12 : word) : Prop :=
  forall (y1 y5 y6 y7 y15 y16 y17 y28 y29 y30 y31 : word) (m' : mem),
    SINV L flush rest0 lo r fj me T m' ->
    evt usegs Q (MS (slowR L flush r y1 y5 y6 y7 (wz (ds_strstart T + 1)) v11 v12 (wz mi) (wz (ds_prev_length T - 1)) y15 y16 y17 y28 y29 y30 y31)
                    F (wz 0x1a440) fc None m' (seg_rom usegs)).
Lemma shr55_7 : forall dd, 0 <= dd -> Z.shiftr (dd * 281474976710656) 55 = Z.shiftr dd 7.
Proof.
  intros dd Hd. rewrite !Z.shiftr_div_pow2 by lia. change (2^55) with (281474976710656 * 128). change (2^7) with 128.
  rewrite <- Z.div_div by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.
Lemma d_code_idx : forall dd, d_code dd = arr_get dist_code_a (if dd <? 256 then dd else 256 + Z.shiftr dd 7).
Proof. intros dd. unfold d_code. destruct (dd <? 256); reflexivity. Qed.
Lemma slow_tdist2 : forall (Q : machine_state -> Prop) (S : deflate_state) (dd : Z)
    (y1 y5 y6 y7 y15 y16 y17 y28 y29 y30 y31 : word) (m : mem),
  SINV L flush rest0 lo r fj me S m ->
  0 <= dd < 32768 ->
  0 <= ds_strstart S <= 65536 -> 1 <= ds_lookahead S <= 65536 -> 3 <= ds_prev_length S <= 258 -> ds_prev_length S - 1 <= ds_lookahead S ->
  3 <= ds_strstart S + ds_lookahead S <= 65536 -> 0 <= ds_sym_next S < 2^18 -> 0 <= ds_sym_end S < 2^18 ->
  (forall i, 0 <= i < 61 -> 0 <= arr_get (ds_dyn_dtree_fc S) i < 65536) ->
  KINS Q (dist2_st (sdist2 S (d_code dd))) (ds_strstart S + ds_lookahead S - 3) (wz (ds_sym_next S)) (wz (ds_sym_end S)) ->
  evt usegs Q (MS (slowR L flush r y1 y5 y6 y7 (wz (ds_strstart S)) (wz (ds_lookahead S)) (wz 70560) (wz dd) (wz (dd * 281474976710656)) y15 y16 y17 y28 y29 y30 y31)
                  F (wz 0x1a3ac) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros (DR & DOUT & ROOM & FR & STK & MU & WM & MI) Rdd Rss Rla Rpl PLLA RSL Rsn Rse Rdfc HK.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16. unfold Z_NO_FLUSH, Z_FINISH in HFL.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA. open_D GD. open_ct Gdt.
  pose proof (ln_dtf _ LENS) as Ldtf.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  pose proof (lo_s _ LAY) as BKs. unfold blk_ok in BKs.
  unfold slowR. unfold slow_frame in FR. unfold slow_W in MU.
  name_mem mA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_As L + 2504, dl_As L + 2748)] mA) as MUf. pose proof (wmono_refl usegs mA) as WMf.
  assert (Rdci : 0 <= (if dd <? 256 then dd else 256 + Z.shiftr dd 7) < 512).
  { destruct (Z.ltb_spec dd 256); [lia|]. rewrite Z.shiftr_div_pow2 by lia. change (2^7) with 128. Z.div_mod_to_equations. lia. }
  zstep. zstep. zstep.
  eapply (evt_cut usegs (fun ms' => exists v14, ms' = MS (slowR L flush r y1 y5 y6 y7 (wz (ds_strstart S)) (wz (ds_lookahead S)) (wz 72464) (wz (if dd <? 256 then dd else 256 + Z.shiftr dd 7)) v14 (wz 255) y16 y17 y28 y29 y30 y31)
                                                              F (wz 0x1a3c0) fc None mA (seg_rom usegs))).
  { if_cases KDD; zify_cond KDD; rewrite ?unsigned_lit in KDD by lia.
    -
      apply evt_done. eexists. unfold slowR.
      replace (dd <? 256) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
    -
      zstep. rewrite (shr55_7 dd) by lia. zstep.
      apply evt_done. eexists. unfold slowR.
      replace (dd <? 256) with false by (symmetry; apply Z.ltb_ge; lia). replace (dd ≫ 7 + 256) with (256 + dd ≫ 7) by lia. reflexivity. }
  intros ms' (v14 & ->). unfold slowR.
  pose proof (d_code_idx dd) as EDC.
  remember (if dd <? 256 then dd else 256 + Z.shiftr dd 7) as dci eqn:Edci. clear Edci.
  zstep. try rewrite (zb_lxor_ones 72464) by lia. gF. zstep.
  pose proof (rod_dist_code _ MI) as TDC. unfold Z_DIST_CODE in TDC.
  ld8ro TDC dist_code_a 512 72464 dci dc Edc ltac:(pose proof (dist_code_range dci Rdci); lia).
  clear TDC. pose proof (dist_code_range dci Rdci) as Rdc30. rewrite <- Edc in Rdc30. rewrite <- EDC in Edc.
  zstep. gF. zstep. rewrite ?Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. gF. zstep.
  pose proof (u16arr_read usegs _ (dl_As L + 2504) (avct (ds_dyn_dtree_fc S) (ds_dyn_dtree_dl S) 61) (2 * dc)
                (wz (arr_get (ds_dyn_dtree_fc S) dc)) (wa (dl_As L + 2504 + dc * 4)) Gdt
                (avct_nth_fc _ _ 61 dc ltac:(lia)) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zs. clear RD.
  zs. zs. zs. zstep.
  ct_store_fc Gdt (ds_dyn_dtree_fc S) (ds_dyn_dtree_dl S) 61 (dl_As L + 2504) dc (wrap16 (arr_get (ds_dyn_dtree_fc S) dc + 1))
    ltac:(first [apply le2_swrap16_inc_mod | apply le2_swrap16_inc | apply le2_sx16_inc]; apply Rdfc; lia).
  zstep. zs. zstep. zstep. zs. zs. zs. zs. zs. zstep. zs. name_mem mB.
  zstep.
  tr_groups MUf WMf.
  subst dc. unfold KINS in HK. unfold slowR in HK.
  replace (wz (ds_strstart S + ds_lookahead S + -3)) with (wz (ds_strstart S + ds_lookahead S - 3)) by (f_equal; lia).
  replace (wz (ds_strstart S + 1)) with (wz (ds_strstart (dist2_st (sdist2 S (d_code dd))) + 1)) by reflexivity.
  replace (wz (ds_prev_length S + -3)) with (wz (ds_prev_length (dist2_st (sdist2 S (d_code dd))) - 1)) by (unfold dist2_st, sdist2; dsred; f_equal; lia).
  eapply HK.
  split; [split|].
  - exact ZS.
  - unfold dist2_st, sdist2. constructor;
      [do 5 eexists; unfold dsA_cells; dsred; close_cells GA | exact GB| exact GC| do 5 eexists; exact GD
      | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
      | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens_set LENS | exact LAY1].
  - split; [apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
    split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.
Lemma slow_ins : forall (n : nat) (Q : machine_state -> Prop) (X : deflate_state) (mi : Z) (v11 v12 : word),
  ILI X -> ds_prev_length X = Z.of_nat n -> (1 <= n)%nat -> Z.of_nat n <= 258 -> ds_strstart X + Z.of_nat n + 1 <= 65536 -> 0 <= mi -> mi + 2 < 65536 ->
  (forall (y1 y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m' : mem),
     SINV L flush rest0 lo r fj me (deflate_slow_insert n X mi) m' ->
     evt usegs Q (MS (slowR L flush r y1 y5 y6 y7 (wz (ds_strstart (deflate_slow_insert n X mi) + 1)) v11 v12 y13 y14 y15 y16 y17 y28 y29 y30 y31)
                     F (wz 0x1a640) fc None m' (seg_rom usegs))) ->
  KINS Q X mi v11 v12.
Proof.
  induction n as [|n IH]; intros Q X mi v11 v12 HI PLn N1 N258 SSn MI0 MI2 KEXIT; [lia|].
  unfold KINS. intros until m'. intros (DR & DOUT & ROOM & FR & STK & MU & WM & MI).
  destruct (ILI_step X mi HI) as (HI' & ESS' & EPL').
  destruct HI as (Rss & Rih & Rhm & Rwm & Rhs & Rwb & Rhb).
  pose proof CTX as CTX0. destruct CTX0 as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16.
  pose proof HFL as HFL'. unfold Z_NO_FLUSH, Z_FINISH in HFL'.
  assert (FIN : forall (Y : deflate_state) (a1 a5 a6 a7 a15 a16 a17 a28 a29 a30 a31 : word) (mm : mem) (k1 k2 k3 k4 k5 : list byte),
    dzs mm L (ds_strm X) ->
    rw_cells usegs mm (dl_As L) (dsA_cells L Y k1 k2 k3 k4 k5) ->
    (forall v k1' k2' k3' k4' k5' mm', munch [(dl_As L, dl_As L + 212)] mm mm' -> wmono usegs mm mm' ->
       rw_cells usegs mm' (dl_As L) (dsA_cells L (set_prev_length Y v) k1' k2' k3' k4' k5') ->
       DST mm' L (set_prev_length (if ds_strstart X + 1 <=? mi then ins_str (set_strstart X (ds_strstart X + 1)) (ds_strstart X + 1)
                                   else set_strstart X (ds_strstart X + 1)) v)) ->
    dout mm L rest0 (ds_strm X) -> rw_cells usegs mm (bv_unsigned (r_sp r) + -128) (slow_frame fj r) -> stk usegs mm lo (bv_unsigned (r_sp r) + -128) ->
    munch (slow_W L rest0 lo r) me mm -> wmono usegs me mm -> mem_inv usegs mm ->
    evt usegs Q (MS (slowR L flush r a1 a5 a6 a7 (wz (ds_strstart X + 1)) v11 v12 (wz mi) (wz (ds_prev_length X - 1)) a15 a16 a17 a28 a29 a30 a31)
                    F (wz 0x1a430) fc None mm (seg_rom usegs))).
  { intros until k5. intros ZS GA REST DOUT' FR' STK' MU' WM' MI'. unfold slowR. unfold dsA_cells in GA. unfold slow_frame in FR'. unfold slow_W in MU'.
    lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
    pose proof (munch_refl [(dl_As L, dl_As L + 212)] mm) as MUs. pose proof (wmono_refl usegs mm) as WMs.
    zs. name_mem mB. zs. zs.
    tr_groups MUs WMs.
    assert (ESTRM : ds_strm (insl_st X mi) = ds_strm X) by (unfold insl_st, RefDeflSlow2.ins_str; destruct (ds_strstart X + 1 <=? mi); reflexivity).
    assert (SI' : SINV L flush rest0 lo r fj me (insl_st X mi) mB).
    { split; [split|].
      - rewrite ESTRM. exact ZS.
      - unfold insl_st. eapply (REST _ _ _ _ _ _ mB MUs WMs). unfold dsA_cells. dsred. close_cells GA.
      - rewrite ESTRM. split; [apply (dout_munch _ mm mB L rest0 _ DOUT' ROOM MUs WMs); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
        split; [exact FR'|]. split; [exact STK'|]. split; [exact MU'|]. split; [exact WM'| eassumption]. }
    zstep. if_cases KX; zify_cond KX.
    -
      assert (N0 : n = 0%nat) by (rewrite PLn in KX; Z.div_mod_to_equations; lia).
      subst n. rewrite (slow_insert_last X mi PLn) in KEXIT. unfold slowR in KEXIT.
      replace (wz (ds_strstart X + 2)) with (wz (ds_strstart (insl_st X mi) + 1)) by (rewrite ESS'; f_equal; lia).
      eapply KEXIT. exact SI'.
    -
      assert (N1' : (1 <= n)%nat) by (rewrite PLn in KX; Z.div_mod_to_equations; lia).
      destruct n as [|n']; [lia|].
      rewrite (slow_insert_more n' X mi PLn) in KEXIT.
      replace (wz (ds_strstart X + 2)) with (wz (ds_strstart (insl_st X mi) + 1)) by (rewrite ESS'; f_equal; lia).
      replace (wz (ds_prev_length X - 1 + -1)) with (wz (ds_prev_length (insl_st X mi) - 1)) by (rewrite EPL'; f_equal; lia).
      unfold KINS, slowR in IH.
      eapply (IH Q (insl_st X mi) mi v11 v12 HI'); [rewrite EPL', PLn; lia| lia| lia| rewrite ESS'; lia| exact MI0| exact MI2| exact KEXIT| exact SI']. }
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  pose proof (lo_h _ LAY) as BKh. unfold blk_ok in BKh. pose proof (lo_p _ LAY) as BKp. unfold blk_ok in BKp.
  unfold slowR. unfold slow_frame in FR. unfold slow_W in MU.
  name_mem mA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_Ap L, dl_Ap L + 65536); (dl_Ah L, dl_Ah L + 65536)] mA) as MUf. pose proof (wmono_refl usegs mA) as WMf.
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] mA) as MUs.
  zs. zstep.
  if_cases KI; zify_cond KI; rewrite ?unsigned_lit in KI by lia.
  -
    name_mem mS. clear MUf. tr_groups MUs WMf.
    eapply (FIN (set_strstart X (ds_strstart X + 1)) _ _ _ _ _ _ _ _ _ _ _ mS); [exact ZS| unfold dsA_cells; dsred; exact GA| | | exact FR| exact STK| exact MU| exact WM| eassumption].
    2:{ apply (dout_munch _ mA mS L rest0 _ DOUT ROOM MUs WMf). cbn [disjoint_from]. slia. }
    intros v k1' k2' k3' k4' k5' mm' MU2 WM2 GA2.
    replace (ds_strstart X + 1 <=? mi) with false by (symmetry; apply Z.leb_gt; lia).
    clear GA. tr_groups MU2 WM2.
    constructor; [do 5 eexists; exact GA2 | exact GB| exact GC| exact GD
        | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
        | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY1].
  -
    name_mem mS.
    assert (GwinS : dwin mS L X) by (apply (dwin_munch mA mS L X _ Gwin MUs WMf); cbn [disjoint_from]; slia).
    assert (GprevS : dprev mS L X) by (apply (dprev_munch mA mS L X _ Gprev MUs WMf); cbn [disjoint_from]; slia).
    assert (GheadS : dhead mS L X) by (apply (dhead_munch mA mS L X _ Ghead MUs WMf); cbn [disjoint_from]; slia).
    clear Gwin Gprev Ghead MUs. rename GwinS into Gwin. rename GprevS into Gprev. rename GheadS into Ghead.
    pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_Ap L, dl_Ap L + 65536); (dl_Ah L, dl_Ah L + 65536)] mS) as MUg. pose proof (wmono_refl usegs mS) as WMg.
    open_u16 Gprev. open_u16 Ghead.
    pose proof (ln_prev _ LENS) as Lprev. pose proof (ln_head _ LENS) as Lhead.
    zs. gF. zs. zstep. zstep. zstep. rewrite ?Z.mod_small by lia. zstep. gF. zstep. zstep. zstep. gX. gF.
    zs.
    ld8 Gwin (ds_window X) 65536 (dl_Aw L) (ds_strstart X + 3) ltac:(apply Rwb; lia).
    zs. zs. zs. zs. zs.
    rewrite (hash_mach X (ds_ins_h X) (arr_get (ds_window X) (ds_strstart X + 3))) by lia.
    pose proof (update_hash_range X (ds_ins_h X) (arr_get (ds_window X) (ds_strstart X + 3)) ltac:(lia)) as Rhv.
    remember (update_hash X (ds_ins_h X) (arr_get (ds_window X) (ds_strstart X + 3))) as h eqn:Eh.
    zstep. zstep. rewrite (shl32_shr31 h) by lia. zstep. zs.
    gF. zstep. zstep. zstep. gX. gF. zstep.
    assert (ALh : (dl_Ah L + 2 * h) mod 2 = 0) by (clear - BKh Rhv; Z.div_mod_to_equations; lia).
    first [rewrite (land1_mod2 _ ALh) | replace (2 * h + dl_Ah L) with (dl_Ah L + 2 * h) by lia; rewrite (land1_mod2 _ ALh)]. gF.
    zs. zs. zstep. try rewrite (Z.land_comm (ds_w_mask X) (ds_strstart X + 1)). zstep. zstep.
    rewrite ?Z.shiftl_mul_pow2 by lia. change (2^1) with 2. rewrite ?(Z.mul_comm _ 2).
    pose proof (LmatchModel.land_upper_both (ds_strstart X + 1) (ds_w_mask X) ltac:(lia) ltac:(lia)) as Rpi.
    remember (Z.land (ds_strstart X + 1) (ds_w_mask X)) as pi eqn:Epi.
    gF. zstep. zstep. zstep. gX. gF. zstep.
    assert (ALp : (dl_Ap L + 2 * pi) mod 2 = 0) by (clear - BKp Rpi; Z.div_mod_to_equations; lia).
    first [rewrite (land1_mod2 _ ALp) | replace (2 * pi + dl_Ap L) with (dl_Ap L + 2 * pi) by lia; rewrite (land1_mod2 _ ALp) | replace (dl_Ap L + pi * 2) with (dl_Ap L + 2 * pi) by lia; rewrite (land1_mod2 _ ALp)]. gF.
    pose proof (Rhb h ltac:(lia)) as Rhh.
    ld16 Ghead (ds_head X) 32768 (dl_Ah L) h ltac:(apply Rhb; lia).
    st16 Gprev (ds_prev X) 32768 (dl_Ap L) pi (arr_get (ds_head X) h) ltac:(reflexivity).
    gT.
    st16 Ghead (ds_head X) 32768 (dl_Ah L) h (wrap16 (ds_strstart X + 1)) ltac:(apply le2_wz_mod; rewrite unsigned_lit by lia; rewrite wrap16_mod, Z.mod_mod by lia; reflexivity).
    name_mem mB.
    tr_groups MUf WMf. tr_groups MUg WMg.
    subst h pi. replace (ds_strstart X + 3) with (ds_strstart X + 1 + 2) in * by lia.
    eapply (FIN (ins_str (set_strstart X (ds_strstart X + 1)) (ds_strstart X + 1)) _ _ _ _ _ _ _ _ _ _ _ mB); [exact ZS| unfold dsA_cells, RefDeflSlow2.ins_str; dsred; exact GA| | | exact FR| exact STK| exact MU| exact WM| eassumption].
    2:{ apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf). cbn [disjoint_from]. slia. }
    intros v k1' k2' k3' k4' k5' mm' MU2 WM2 GA2.
    replace (ds_strstart X + 1 <=? mi) with true by (symmetry; apply Z.leb_le; lia).
    clear GA.
    change (dprev mB L (ins_str (set_strstart X (ds_strstart X + 1)) (ds_strstart X + 1))) in Gprev.
    change (dhead mB L (ins_str (set_strstart X (ds_strstart X + 1)) (ds_strstart X + 1))) in Ghead.
    tr_groups MU2 WM2.
    unfold RefDeflSlow2.ins_str. constructor; [do 5 eexists; unfold dsA_cells; dsred; unfold dsA_cells, RefDeflSlow2.ins_str in GA2; dsred in GA2; exact GA2 | exact GB| exact GC| exact GD
        | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
        | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens_set LENS | exact LAY1].
Qed.
Definition KA (Q : machine_state -> Prop) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m' : mem),
    SINV L flush rest0 lo r fj me X m' ->
    evt usegs Q (MS (slowR L flush r y1 y5 y6 y7 (wz (ds_strstart X)) y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31) F (wz 0x1a654) fc None m' (seg_rom usegs)).
Lemma slow_dexit : forall (Q : machine_state -> Prop) (Xf : deflate_state) (sn se : Z)
    (y1 y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m : mem),
  SINV L flush rest0 lo r fj me Xf m -> 0 <= sn < 2^32 -> 0 <= se < 2^32 ->
  (sn <> se -> SK L flush rest0 lo r fj F fc me Q Z_SLOW_HEAD (exit_st Xf)) ->
  (sn = se -> KA Q (exit_st Xf)) ->
  evt usegs Q (MS (slowR L flush r y1 y5 y6 y7 (wz (ds_strstart Xf + 1)) (wz sn) (wz se) y13 y14 y15 y16 y17 y28 y29 y30 y31) F (wz 0x1a640) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros (DR & DOUT & ROOM & FR & STK & MU & WM & MI) Rsn Rse KH0 KA0.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16. unfold Z_NO_FLUSH, Z_FINISH in HFL.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold slowR. unfold slow_frame in FR. unfold slow_W in MU. unfold SK, Z_SLOW_HEAD, slowR in KH0. unfold KA, slowR in KA0.
  name_mem mA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] mA) as MUf. pose proof (wmono_refl usegs mA) as WMf.
  zstep. zs. zs. zs. name_mem mB.
  tr_groups MUf WMf.
  assert (SI' : SINV L flush rest0 lo r fj me (exit_st Xf) mB).
  { split; [split|].
    - exact ZS.
    - unfold exit_st. constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA | exact GB| exact GC| exact GD
        | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
        | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY1].
    - split; [apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
      split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. }
  zstep. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia.
  - eapply (KH0 KB). exact SI'.
  - replace (wz (ds_strstart Xf + 1)) with (wz (ds_strstart (exit_st Xf))) by reflexivity.
    eapply (KA0 KB). exact SI'.
Qed.
End DIST2.
