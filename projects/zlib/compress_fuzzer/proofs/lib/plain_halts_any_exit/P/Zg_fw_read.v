(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import InitMem Z_kit Z_dview Z_drep Z_dkit Z_defl_iface Z_slow_model Z_slow_kit Z_tr_kit Z_adler32 Z_fw_model Z_fw_kit Z_fw_high
     Zg_adler32_iface Zg_defl_iface Zg_sto_model Zg_sto_ole Zg_sto_rdo Zg_fw_model Zg_fw_insert Zg_fw_tail.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState DeflateLz FillWinModel AdlerModel RefDeflStored1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Ltac join_x9g v pcj :=
  lazymatch goal with
  | |- evt _ _ (MS (TNode (TNode ?A ?x1 (TNode (TNode ?B (Some _) ?C) ?x5 ?D)) None ?E) ?F _ ?fc None ?m ?rom) =>
      eapply (evt_cut psegs (fun ms' => ms' = MS (TNode (TNode A x1 (TNode (TNode B (Some v) C) x5 D)) None E) F (wz pcj) fc None m rom))
  end.

Section READ.
Variables (L : dlay) (inp : list Z) (nout lo : Z) (r : sregs) (fj : list byte) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : fw_ctx L inp nout lo r me.
Hypothesis LOG : lo <= bv_unsigned (r_sp r) - Z_FILLWIN_STACKG.
Hypothesis HADL : adler32_stmt.

Lemma fwg_read : forall (X : deflate_state) (more : Z)
    (y1 y5 y6 y7 y9 y10 y12 y13 y14 y15 y16 y17 y19 y21 y25 y27 y28 y29 y30 y31 : word) (m : mem),
  FWINV L inp lo r fj me X m -> fw_wf 32768 32768 X -> ds_wrap X <> 2 -> cs_avail_in (ds_strm X) < 2^31 ->
  din_tie inp X ->
  more = ds_window_size X - ds_lookahead X - ds_strstart X -> (more = 0 -> 262 < ds_lookahead X) ->
  (cs_avail_in (ds_strm X) <> 0 -> 262 <= ds_lookahead X + more) ->
  evt psegs (fw_post_gen r F fc L (fill_window_high (fwB X more)) inp lo me)
    (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -112)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) y9 y10 (wz (ds_strstart X)) y12 y13 y14 y15 y16 y17
             (wz more) y19 (wz (dl_As L + 5932)) y21 (wz 3) (wz 2) (wz 261) y25 (wz 1) y27 y28 y29 y30 y31)
        F (wz Z_FW_READ) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros INV FW W2 AI TIE EM ZM FULL. unfold Z_FW_READ.
  pose proof INV as INV0. destruct INV as (DR & DIN & FR & STK & MU & WM & MI). unfold fw_W in MU. unfold fw_frame in FR.
  pose proof CTX as CTX'. destruct CTX' as [LOsp SP16 LAY0 BEL IO DIN0]. unfold Z_FILLWIN_STACK in LOsp. unfold Z_FILLWIN_STACKG in LOG.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY. pose proof BEL as BEL'. below_open BEL'. pose proof IO as IO'. io_open IO'.
  pose proof FW as FW0. destruct FW as [_ _ Wwl Wwsz _ _ _ _ _ _ _ Wins Wlook Wsl _ _ _ Wni Wai Winl Wti Wwr Wad1 _ _ _ _ Wib].
  destruct TIE as [TIE1 TIE2]. rewrite TIE1, arr_len_of_list in Winl.
  open_DST ST. open_A GA. open_zs ZS.
  zs. zs.
  zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia.
  {
    rewrite (fwB_0 X more) by lia. apply (fw_high L inp nout lo r fj F fc me CTX X); [exact INV0| exact FW0]. }

  remember (rb_len X more) as n eqn:En.
  pose proof (rb_len_range X more ltac:(lia) ltac:(lia)) as RN. rewrite <- En in RN. destruct RN as (RN1 & RN2 & RN3).
  zs. zstep. join_x9g (wz n) 0x169ac.
  { if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
    - apply evt_done. replace n with (cs_avail_in (ds_strm X)) by (rewrite En; unfold rb_len; destruct (Z.ltb_spec more (cs_avail_in (ds_strm X))); lia). reflexivity.
    - zstep. apply evt_done. replace n with more by (rewrite En; unfold rb_len; destruct (Z.ltb_spec more (cs_avail_in (ds_strm X))); lia). reflexivity. }
  intros ms' ->.
  zs.
  zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
  {
    assert (N0 : n = 0) by (apply (proj2 RN3); left; exact K2). rewrite N0.
    rewrite (fwB_g0 X more ltac:(lia) ltac:(rewrite <- En; exact N0)).
    apply (fwg_tail L inp nout lo r fj F fc me CTX X 0); [exact INV0| exact FW0| lia| lia| intros; exfalso; lia]. }

  assert (Pn : 0 < n) by (destruct (Z.eq_dec n 0) as [E0|E0]; [destruct (proj1 RN3 E0); lia| lia]).
  clear INV0.
  rewrite TIE1, arr_len_of_list in Wib.
  remember (arr_slice (arr_of_list inp) (cs_next_in (ds_strm X)) n) as l eqn:El.
  assert (Ll : length (zb8 l) = Z.to_nat n) by (rewrite zb8_length, El; apply arr_slice_length').
  assert (Bl : Forall (fun b => 0 <= b < 256) l).
  { rewrite El. apply Forall_forall. intros b Hb. eapply (arr_slice_In (arr_of_list inp) (cs_next_in (ds_strm X)) n b); [| exact Hb].
    intros i Hi. apply Wib. lia. }
  pose proof (din_bytes m L inp (cs_next_in (ds_strm X)) n DIN ltac:(lia) ltac:(lia) ltac:(lia)) as SRC. rewrite <- El in SRC.

  open_win Gwin.
  destruct (u8arr_split3 _ (dl_Aw L) _ (Z.to_nat (ds_strstart X + ds_lookahead X)) (Z.to_nat n) Gwin ltac:(rewrite av8_length; lia)) as (O1 & O2 & O3). clear Gwin.
  rewrite !Z2Nat.id in O2 by lia. rewrite !Z2Nat.id in O3 by lia.
  assert (LO1 : length (firstn (Z.to_nat (ds_strstart X + ds_lookahead X)) (av8 (ds_window X) 65536)) = Z.to_nat (ds_strstart X + ds_lookahead X)) by (rewrite length_firstn, av8_length; lia).
  assert (LO3 : length (skipn (Z.to_nat (ds_strstart X + ds_lookahead X) + Z.to_nat n) (av8 (ds_window X) 65536)) = (Z.to_nat 65536 - (Z.to_nat (ds_strstart X + ds_lookahead X) + Z.to_nat n))%nat)
    by (rewrite length_skipn, av8_length; lia).
  replace (dl_Aw L + (ds_strstart X + ds_lookahead X)) with (dl_Aw L + ds_lookahead X + ds_strstart X) in O2 by lia.
  pose proof (munch_refl [(lo, bv_unsigned (r_sp r) + -112); (dl_S L, dl_S L + 112); (dl_Aw L, dl_Aw L + 65536)] m) as MUf. pose proof (wmono_refl psegs m) as WMf.
  zs. zs. zs. zs.
  zs. zs. zs. zs. rewrite ?Z.mod_small by lia. zs. zs. rewrite ?Z.mod_small by lia. zs. zs.

  zstep. call (memcpy_Z (dl_Aw L + ds_lookahead X + ds_strstart X) (dl_NI L + cs_next_in (ds_strm X)) n).
  1:{ exact SRC. } 1:{ exact Ll. } 1:{ exact O2. } 1:{ zsep. } 1:{ eassumption. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
  name_mem mc.
  pose proof (proj1 (u8arr_of_rw_cells psegs mc _ _ _ PC)) as BY.
  replace (dl_Aw L + ds_lookahead X + ds_strstart X) with (dl_Aw L + (ds_strstart X + ds_lookahead X)) in PC by lia.
  pose proof (u8arr_join3z _ (dl_Aw L) _ _ _ (ds_strstart X + ds_lookahead X) n ltac:(lia) ltac:(lia) LO1 O1 PC O3) as WIN.
  unfold zb8 in WIN. rewrite El in WIN.
  rewrite (av8_blit' (ds_window X) (arr_of_list inp) 65536 (ds_strstart X + ds_lookahead X) (cs_next_in (ds_strm X)) n) in WIN by lia.
  rewrite arr_blit_upd, <- El in WIN.
  pose proof (arr_len_blit (ds_window X) (ds_strstart X + ds_lookahead X) (arr_of_list inp) (cs_next_in (ds_strm X)) n) as LNW.
  rewrite arr_blit_upd, <- El, Wwl in LNW.
  pose proof (av8_zlength (arr_upd (ds_window X) (ds_strstart X + ds_lookahead X) l) 65536 ltac:(lia)) as LWF.
  clear O1 O3 PC POST LO1 LO3 SRC.
  assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -112)) = bv_unsigned (r_sp r) + -112) by (apply unsigned_lit; lia).

  assert (KJ : forall (mA : mem) (adl : Z) (v1 v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 : word),
    adl = rbn_adler X l ->
    rw_cells psegs mA (dl_S L)
      [C8 (wz (dl_NI L + cs_next_in (ds_strm X))); C4 (wz (cs_avail_in (ds_strm X) - n)); CB 4 zp1; C8 (wz (cs_total_in (ds_strm X)));
       C8 (wz (dl_NO L + Z.of_nat (length (cs_out_rev (ds_strm X))))); C4 (wz (cs_avail_out (ds_strm X))); CB 4 zp2;
       C8 (wz (cs_total_out (ds_strm X))); C8 (wz (msg_ptr (cs_msg (ds_strm X)))); C8 (wz (dl_As L));
       C8 (wz Z_ZCALLOC); C8 (wz Z_ZCFREE); C8 (wz 0); C4 (wz (cs_data_type (ds_strm X))); CB 4 zp3; C8 (wz adl); C8 zresv] ->
    rw_cells psegs mA (dl_As L) (dsA_cells L X hA1 hA2 hA3 hA4 hA5) ->
    u8arr psegs mA (dl_Aw L) (av8 (arr_upd (ds_window X) (ds_strstart X + ds_lookahead X) l) 65536) ->
    rw_cells psegs mA (bv_unsigned (r_sp r) + -112) (fw_frame r fj) -> stk psegs mA lo (bv_unsigned (r_sp r) + -112) ->
    munch [(lo, bv_unsigned (r_sp r)); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + 5968); (dl_Aw L, dl_Aw L + 65536);
           (dl_Ap L, dl_Ap L + 2 * 32768); (dl_Ah L, dl_Ah L + 2 * 32768)] me mA -> wmono psegs me mA ->
    munch [(lo, bv_unsigned (r_sp r) + -112); (dl_S L, dl_S L + 112); (dl_Aw L, dl_Aw L + 65536)] m mA -> wmono psegs m mA -> mem_inv psegs mA ->
    evt psegs (fw_post_gen r F fc L (fill_window_high (fwB X more)) inp lo me)
      (MS (mkR v1 (wz (bv_unsigned (r_sp r) + -112)) (r_gp r) (r_tp r) v5 v6 v7 (wz (dl_As L)) (wz n) v10 v11 v12 v13 v14 v15 v16 v17
               (wz n) (wz (dl_Aw L + ds_lookahead X + ds_strstart X)) (wz (dl_As L + 5932)) y21 (wz 3) (wz 2) (wz 261) y25 (wz 1) (wz (dl_S L)) v28 v29 v30 v31)
          F (wz 0x16a20) fc None mA (seg_rom psegs))).
  { clear ZS GA WIN BY FR STK MU WM MUf WMf LWF. try clear MI0.
    intros mA adl v1 v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 EADL ZS GA WIN FR STK MU WM MUf WMf MI. unfold fw_frame in FR. unfold dsA_cells in GA.
    pose proof (av8_zlength (arr_upd (ds_window X) (ds_strstart X + ds_lookahead X) l) 65536 ltac:(lia)) as LWF.
    zs. zs. zs. zs. zs. zs. zs.
    rewrite (fwB_gn X more n K0 En Pn W2). rewrite TIE1, <- El.
    name_mem mB. tr_groups MUf WMf.
    apply (fwg_tail L inp nout lo r fj F fc me CTX (set_strm (set_window X (arr_upd (ds_window X) (ds_strstart X + ds_lookahead X) l)) (rbn_strm X l n)) n).
    - split; [split|].
      + exists zp1, zp2, zp3, zresv. cbn [ds_strm set_strm]. rewrite rbn_cells, <- EADL. close_cells ZS.
      + constructor.
        * exists hA1, hA2, hA3, hA4, hA5. unfold dsA_cells. dsred. close_cells GA.
        * exact GB. * exact GC. * exact GD. * exact Glt. * exact Gdt. * exact Gbt. * exact Gblc. * exact Gheap. * exact Gdep.
        * unfold dwin. dsred. exact WIN.
        * exact Gprev. * exact Ghead. * exact Gpend.
        * destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13].
          constructor; dsred; [exact l1|exact l2|exact l3|exact l4|exact l5|exact l6|exact l7|exact l8|exact l9|exact LNW|exact l11|exact l12|exact l13].
        * exact LAY.
      + split; [exact (fw_din L inp nout lo r me CTX mB MU)|]. split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| exact MI].
    - pose proof (read_buf_wf 32768 32768 X (ds_strstart X + ds_lookahead X) more FW0 eq_refl ltac:(lia) ltac:(lia)) as RW.
      cbv zeta in RW. rewrite (read_buf_eqn X _ more n En Pn W2) in RW. rewrite fst_pr in RW. rewrite TIE1, <- El in RW. exact (proj1 RW).
    - lia.
    - dsred. lia.
    - dsred. rewrite rbn_avail_in. intros Hsmall. rewrite En in Hsmall |- *. unfold rb_len in *.
      destruct (Z.ltb_spec more (cs_avail_in (ds_strm X))); [exfalso; pose proof (FULL K0); lia| lia]. }

  zs. zs. zstep. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia; [exfalso; lia|].
  zstep. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia.
  -
    apply (KJ mc (cs_adler (ds_strm X))); [unfold rbn_adler; replace (ds_wrap X =? 1) with false by (symmetry; apply Z.eqb_neq; exact K4); reflexivity
      | exact ZS| exact GA| exact WIN| exact FR| exact STK| exact MU| exact WM| exact MUf| exact WMf| assumption].
  -
    zs. zs. zs.
    assert (E12 : wz n = wz (Z.of_nat (length (zb8 l)))) by (rewrite Ll; f_equal; lia).
    set_x12 (wz (Z.of_nat (length (zb8 l)))) E12. clear E12.
    zstep. call (adler32_call HADL (cs_adler (ds_strm X)) (dl_Aw L + ds_lookahead X + ds_strstart X) lo (zb8 l)).
    1:{ apply Wad1. exact K4. } 1:{ lia. } 1:{ rewrite Ll. lia. } 1:{ rewrite Ll. lia. } 1:{ exact BY. } 1:{ assumption. }
    1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. lia. } 1:{ rewrite Ll. lia. }
    rewrite ESP in *.
    replace (adler32_z_spec (cs_adler (ds_strm X)) (dl_Aw L + ds_lookahead X + ds_strstart X) (zb8 l)) with (adler32_upd (cs_adler (ds_strm X)) l)
      by (symmetry; apply adler32_upd_spec; [pose proof (Wad1 K4); lia | lia | exact Bl]).
    zstep. zs. name_mem md.
    apply (KJ md (adler32_upd (cs_adler (ds_strm X)) l)); [unfold rbn_adler; rewrite K4; reflexivity
      | exact ZS| exact GA| exact WIN| exact FR| assumption| exact MU| exact WM| exact MUf| exact WMf| assumption].
Qed.
End READ.
