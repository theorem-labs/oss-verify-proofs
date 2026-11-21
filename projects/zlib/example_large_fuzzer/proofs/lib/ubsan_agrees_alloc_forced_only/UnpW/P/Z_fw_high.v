(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import InitMem. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_defl_iface Z_slow_kit F_memset Z_fw_model Z_fw_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState DeflateLz FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section HIGH.
Variables (L : dlay) (inp : list Z) (nout lo : Z) (r : sregs) (fj : list byte) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : fw_ctx L inp nout lo r me.

Lemma fw_high : forall (X : deflate_state)
    (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word) (m : mem),
  FWINV L inp lo r fj me X m -> fw_wf 32768 32768 X ->
  evt psegs (fw_post_gen r F fc L (fill_window_high X) inp lo me)
    (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -112)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19
             (wz (dl_As L + 5932)) y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
        F (wz Z_FW_HIGH) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros (DR & DIN & FR & STK & MU & WM & MI) FW. unfold Z_FW_HIGH. unfold fw_W in MU.
  destruct CTX as [LOsp SP16 LAY0 BEL IO DIN0]. unfold Z_FILLWIN_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY. pose proof BEL as BEL'. below_open BEL'.
  destruct FW as [Wws _ Wwl Wwsz _ _ _ _ _ _ _ Wins Wlook Wsl _ _ Whw _ _ _ _ _ _ _ _ _ _ _].
  open_DST ST. open_A GA. open_D GD.
  pose proof (munch_refl [(dl_As L + 5881, dl_As L + 5968); (dl_Aw L, dl_Aw L + DS_WIN)] m) as MUf. pose proof (wmono_refl psegs m) as WMf.

  assert (KEEP : forall m1 (y ya yb : word), m1 = m ->
    evt psegs (fw_post_gen r F fc L X inp lo me)
      (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -112)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) y (wz (ds_high_water X)) (wz (ds_window_size X)) ya y13 y14 y15 y16 y17 yb y19
               (wz (dl_As L + 5932)) y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31) F (wz Z_FW_EPI) fc None m1 (seg_rom psegs))).
  { intros m1 y ya yb ->. apply (fw_epi L inp nout lo r fj F fc me CTX X). split; [split; [exact ZS|]|].
    - constructor; [exists hA1, hA2, hA3, hA4, hA5; exact GA| exact GB| exact GC| exists hD0, hD1, hD2, hD3, hD4; exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc
                   | exact Gheap| exact Gdep| exact Gwin| exact Gprev| exact Ghead| exact Gpend| exact LENS| exact LAY].
    - split; [exact DIN|]. split; [exact FR|]. split; [exact STK|]. split; [unfold fw_W; exact MU|]. split; [exact WM| exact MI]. }
  zs. zs.
  zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
  {   rewrite (fwh_none X) by lia. unfold Z_FW_EPI in KEEP. apply KEEP. reflexivity. }
  zs. zs. zs.
  zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
  -
    zs. zstep. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
    {   rewrite (fwh_c X) by (unfold WIN_INIT, MAX_MATCH; lia). unfold Z_FW_EPI in KEEP. apply KEEP. reflexivity. }
    zs. zs.
    assert (IB : fwh_init_b X = (if ds_window_size X - ds_high_water X <? ds_lookahead X + ds_strstart X + 258 - ds_high_water X
                                 then ds_window_size X - ds_high_water X else ds_lookahead X + ds_strstart X + 258 - ds_high_water X)).
    { unfold fwh_init_b, WIN_INIT, MAX_MATCH. cbv zeta. rewrite (Z.add_comm (ds_strstart X) (ds_lookahead X)). reflexivity. }
    zstep. eapply (evt_cut psegs (fun ms' => ms' = _)).
    { if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia.
      - replace (wz (ds_lookahead X + ds_strstart X + 258 - ds_high_water X)) with (wz (fwh_init_b X))
          by (f_equal; rewrite IB; destruct (Z.ltb_spec (ds_window_size X - ds_high_water X) (ds_lookahead X + ds_strstart X + 258 - ds_high_water X)); lia).
        apply evt_done. reflexivity.
      - zstep. apply evt_done.
        replace (wz (ds_window_size X - ds_high_water X)) with (wz (fwh_init_b X))
          by (f_equal; rewrite IB; destruct (Z.ltb_spec (ds_window_size X - ds_high_water X) (ds_lookahead X + ds_strstart X + 258 - ds_high_water X)); lia).
        reflexivity. }
    intros ms' ->.
    assert (RIB : 0 <= fwh_init_b X /\ ds_high_water X + fwh_init_b X <= ds_window_size X) by (rewrite IB; destruct (_ <? _) eqn:E4; [apply Z.ltb_lt in E4| apply Z.ltb_ge in E4]; lia).
    clear IB. assert (RI1 : 0 <= fwh_init_b X) by lia. assert (RI2 : ds_high_water X + fwh_init_b X <= 65536) by lia. assert (RI3 : 0 <= ds_high_water X) by lia.
    zs. zs. zs. zs. rewrite ?Z.mod_small by lia. zs.
    open_win Gwin.
    destruct (u8arr_split3 _ (dl_Aw L) _ (Z.to_nat (ds_high_water X)) (Z.to_nat (fwh_init_b X)) Gwin ltac:(rewrite av8_length; lia)) as (O1 & O2 & O3). clear Gwin.
    assert (LO1 : length (firstn (Z.to_nat (ds_high_water X)) (av8 (ds_window X) 65536)) = Z.to_nat (ds_high_water X)) by (rewrite length_firstn, av8_length; lia).
    assert (LO3 : length (skipn (Z.to_nat (ds_high_water X) + Z.to_nat (fwh_init_b X)) (av8 (ds_window X) 65536)) = (Z.to_nat 65536 - Z.to_nat (ds_high_water X) - Z.to_nat (fwh_init_b X))%nat)
      by (rewrite length_skipn, av8_length; lia).
    replace (dl_Aw L + Z.of_nat (Z.to_nat (ds_high_water X))) with (dl_Aw L + ds_high_water X) in O2 by lia.
    zstep.
    lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut; [eapply memset_callZ with (D := dl_Aw L + ds_high_water X) (C := 0) (N := fwh_init_b X); [exact O2| eassumption| lia| lia| lia| lia] | post_call segs mm] end.
    name_mem mc.
    replace (dl_Aw L + ds_high_water X) with (dl_Aw L + Z.of_nat (Z.to_nat (ds_high_water X))) in POST by lia.
    pose proof (u8arr_join3k mc (dl_Aw L) _ _ _ _ _ LO1 O1 POST O3) as WIN. clear O1 POST O3 LO1 LO3.
    change (Z_to_bv 8 (0 mod 256)) with (Z_to_bv 8 0) in WIN.
    replace (Z.to_nat (ds_high_water X) + Z.to_nat (fwh_init_b X))%nat with (Z.to_nat (ds_high_water X + fwh_init_b X)) in WIN by lia.
    rewrite <- (av8_fill0 (ds_window X) 65536 (ds_high_water X) (fwh_init_b X)) in WIN by lia.
    assert (LWF : Z.of_nat (length (av8 (arr_fill (ds_window X) (ds_high_water X) (fwh_init_b X) 0) 65536)) = 65536) by (rewrite av8_length; lia).
    zs. zs. zs.
    name_mem mF. tr_groups MUf WMf.
    rewrite (fwh_b X) by (unfold WIN_INIT, MAX_MATCH; lia).
    apply (fw_epi L inp nout lo r fj F fc me CTX). split; [split|].
    + unfold dzs. dsred. exact ZS.
    + constructor.
      * do 5 eexists. unfold dsA_cells. dsred. close_cells GA.
      * exact GB. * exact GC.
      * do 5 eexists. unfold dsD_cells. dsred. close_cells GD.
      * exact Glt. * exact Gdt. * exact Gbt. * exact Gblc. * exact Gheap. * exact Gdep.
      * unfold dwin. dsred. exact WIN.
      * exact Gprev. * exact Ghead. * exact Gpend.
      * destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13].
        constructor; dsred; rewrite ?arr_len_fill; [exact l1|exact l2|exact l3|exact l4|exact l5|exact l6|exact l7|exact l8|exact l9|exact l10|exact l11|exact l12|exact l13].
      * exact LAY.
    + split; [exact (fw_din L inp nout lo r me CTX mF MU)|]. split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| assumption].
  -
    zs. zs.
    assert (IA : fwh_init_a X = (if 258 <? ds_window_size X - (ds_lookahead X + ds_strstart X) then 258 else ds_window_size X - (ds_lookahead X + ds_strstart X))).
    { unfold fwh_init_a, WIN_INIT, MAX_MATCH. cbv zeta. rewrite (Z.add_comm (ds_strstart X) (ds_lookahead X)). reflexivity. }
    zstep. eapply (evt_cut psegs (fun ms' => ms' = _)).
    { if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia.
      - replace (wz (ds_window_size X - (ds_lookahead X + ds_strstart X))) with (wz (fwh_init_a X))
          by (f_equal; rewrite IA; destruct (Z.ltb_spec 258 (ds_window_size X - (ds_lookahead X + ds_strstart X))); lia).
        apply evt_done. reflexivity.
      - zstep. apply evt_done.
        replace (wz 258) with (wz (fwh_init_a X))
          by (f_equal; rewrite IA; destruct (Z.ltb_spec 258 (ds_window_size X - (ds_lookahead X + ds_strstart X))); lia).
        reflexivity. }
    intros ms' ->.
    assert (RIA : 0 <= fwh_init_a X /\ ds_lookahead X + ds_strstart X + fwh_init_a X <= ds_window_size X)
      by (rewrite IA; destruct (Z.ltb_spec 258 (ds_window_size X - (ds_lookahead X + ds_strstart X))); lia).
    clear IA. assert (RI1 : 0 <= fwh_init_a X) by lia. assert (RI2 : ds_lookahead X + ds_strstart X + fwh_init_a X <= 65536) by lia.
    assert (RI3 : 0 <= ds_lookahead X + ds_strstart X) by lia.
    zs. zs. zs. zs.
    open_win Gwin.
    destruct (u8arr_split3 _ (dl_Aw L) _ (Z.to_nat (ds_lookahead X + ds_strstart X)) (Z.to_nat (fwh_init_a X)) Gwin ltac:(rewrite av8_length; lia)) as (O1 & O2 & O3). clear Gwin.
    assert (LO1 : length (firstn (Z.to_nat (ds_lookahead X + ds_strstart X)) (av8 (ds_window X) 65536)) = Z.to_nat (ds_lookahead X + ds_strstart X)) by (rewrite length_firstn, av8_length; lia).
    assert (LO3 : length (skipn (Z.to_nat (ds_lookahead X + ds_strstart X) + Z.to_nat (fwh_init_a X)) (av8 (ds_window X) 65536))
                  = (Z.to_nat 65536 - Z.to_nat (ds_lookahead X + ds_strstart X) - Z.to_nat (fwh_init_a X))%nat)
      by (rewrite length_skipn, av8_length; lia).
    replace (dl_Aw L + Z.of_nat (Z.to_nat (ds_lookahead X + ds_strstart X))) with (dl_Aw L + (ds_lookahead X + ds_strstart X)) in O2 by lia.
    zstep.
    lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut; [eapply memset_callZ with (D := dl_Aw L + (ds_lookahead X + ds_strstart X)) (C := 0) (N := fwh_init_a X); [exact O2| eassumption| lia| lia| lia| lia] | post_call segs mm] end.
    name_mem mc.
    replace (dl_Aw L + (ds_lookahead X + ds_strstart X)) with (dl_Aw L + Z.of_nat (Z.to_nat (ds_lookahead X + ds_strstart X))) in POST by lia.
    pose proof (u8arr_join3k mc (dl_Aw L) _ _ _ _ _ LO1 O1 POST O3) as WIN. clear O1 POST O3 LO1 LO3.
    change (Z_to_bv 8 (0 mod 256)) with (Z_to_bv 8 0) in WIN.
    replace (Z.to_nat (ds_lookahead X + ds_strstart X) + Z.to_nat (fwh_init_a X))%nat with (Z.to_nat ((ds_strstart X + ds_lookahead X) + fwh_init_a X)) in WIN by lia.
    replace (Z.to_nat (ds_lookahead X + ds_strstart X)) with (Z.to_nat (ds_strstart X + ds_lookahead X)) in WIN by lia.
    rewrite <- (av8_fill0 (ds_window X) 65536 (ds_strstart X + ds_lookahead X) (fwh_init_a X)) in WIN by lia.
    assert (LWF : Z.of_nat (length (av8 (arr_fill (ds_window X) (ds_strstart X + ds_lookahead X) (fwh_init_a X) 0) 65536)) = 65536) by (rewrite av8_length; lia).
    zs. zs. zs.
    name_mem mF. tr_groups MUf WMf.
    rewrite (fwh_a X) by (unfold WIN_INIT, MAX_MATCH; lia).
    apply (fw_epi L inp nout lo r fj F fc me CTX). split; [split|].
    + unfold dzs. dsred. exact ZS.
    + constructor.
      * do 5 eexists. unfold dsA_cells. dsred. close_cells GA.
      * exact GB. * exact GC.
      * do 5 eexists. unfold dsD_cells. dsred. close_cells GD.
      * exact Glt. * exact Gdt. * exact Gbt. * exact Gblc. * exact Gheap. * exact Gdep.
      * unfold dwin. dsred. exact WIN.
      * exact Gprev. * exact Ghead. * exact Gpend.
      * destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13].
        constructor; dsred; rewrite ?arr_len_fill; [exact l1|exact l2|exact l3|exact l4|exact l5|exact l6|exact l7|exact l8|exact l9|exact l10|exact l11|exact l12|exact l13].
      * exact LAY.
    + split; [exact (fw_din L inp nout lo r me CTX mF MU)|]. split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| assumption].
Qed.
End HIGH.
