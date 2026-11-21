(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_slow_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_defl_iface Z_slow_model.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_trees_iface.

Module Z_fw_kit.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_slow_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_defl_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_trees_iface.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface.Z_fw_model.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState DeflateLz FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition Z_FW_EPI : Z := 0x16d28.
Definition Z_FW_HIGH : Z := 0x16c84.     (* 1.4 UBSan: the high-water read is ld a2,20(s2) (high_water at s + 5952) *)
Definition Z_FW_READ : Z := 0x16ad0.
Definition Z_FW_TAIL : Z := 0x16b2c.
Definition Z_FW_SLIDE : Z := 0x169ac.

Definition fw_frame (j0 : list byte) (r : sregs) : list cell :=
  [CB 8 j0; C8 (r_s9 r); C8 (r_s8 r); C8 (r_s7 r); C8 (r_s6 r); C8 (r_s5 r); C8 (r_s4 r); C8 (r_s3 r); C8 (r_s2 r); C8 (r_s1 r); C8 (r_s0 r); C8 (r_ra r)].

Definition fw_W (L : dlay) (lo : Z) (r : sregs) : list ivl :=
  [(lo, bv_unsigned (r_sp r)); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + DS_SIZE); (dl_Aw L, dl_Aw L + DS_WIN);
   (dl_Ap L, dl_Ap L + 2 * DS_NPREV); (dl_Ah L, dl_Ah L + 2 * DS_NHEAD)].

Record fw_ctx (L : dlay) (inp : list Z) (nout lo : Z) (r : sregs) (me : mem) : Prop := mkFWctx {
  fc_lo : lo <= bv_unsigned (r_sp r) - Z_FILLWIN_STACK;
  fc_sp16 : bv_unsigned (r_sp r) mod 16 = 0;
  fc_lay : dlay_ok L;
  fc_bel : dlay_below L lo (bv_unsigned (r_sp r));
  fc_io : dio_sep L (zlength inp) nout lo;
  fc_din : din me L inp }.

Definition FWINV (L : dlay) (inp : list Z) (lo : Z) (r : sregs) (me : mem) (X : deflate_state) (m : mem) : Prop :=
  DREP m L X /\ din m L inp
  /\ (exists j0, rw_cells usegs m (bv_unsigned (r_sp r) + -96) (fw_frame j0 r))
  /\ stk usegs m lo (bv_unsigned (r_sp r) + -96)
  /\ munch (fw_W L lo r) me m /\ wmono usegs me m /\ mem_inv usegs m.

Definition fw_post_gen (r : sregs) (F : bvmap 5 word) (fc : bv 32) (L : dlay) (dF : deflate_state) (inp : list Z) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (r_ra r) (r_sp r) (r_gp r) (r_tp r) t0 t1 t2 (r_s0 r) (r_s1 r) a0 a1 a2 a3 a4 a5 a6 a7
                  (r_s2 r) (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) t3 t4 t5 t6)
             F (ret_pc (r_ra r)) fc None m' (seg_rom usegs)
    /\ munch (fw_W L lo r) m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned (r_sp r))
    /\ DREP m' L dF /\ din m' L inp.

Lemma fill_window_post_gen : forall r F fc L d inp lo m,
  fill_window_post (r_ra r) (r_sp r) (r_gp r) (r_tp r) (r_s0 r) (r_s1 r) (r_s2 r) (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r)
    F fc L d inp lo m = fw_post_gen r F fc L (fill_window d) inp lo m.
Proof. intros. reflexivity. Qed.

Section KIT.
Variables (L : dlay) (inp : list Z) (nout lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : fw_ctx L inp nout lo r me.

Lemma fw_din : forall m, munch (fw_W L lo r) me m -> din m L inp.
Proof.
  intros m MU. destruct CTX as [LOsp SP16 LAY BEL IO DIN]. unfold Z_FILLWIN_STACK in LOsp. unfold din in *.
  eapply bytes_at_transport; [exact DIN| exact MU|]. unfold fw_W. cbn [disjoint_from]. rewrite zb8_length.
  below_open BEL. pose proof IO as I0. io_open I0. unfold zlength in *.
  pose proof (io_is _ _ _ _ IO) as J1. pose proof (io_iw _ _ _ _ IO) as J2. pose proof (io_ip _ _ _ _ IO) as J3.
  pose proof (io_ih _ _ _ _ IO) as J4. pose proof (io_ib _ _ _ _ IO) as J5.
  unfold apart, zlength in *. repeat split; lia.
Qed.

Lemma fw_epi : forall (dF : deflate_state)
    (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y28 y29 y30 y31 : word) (m' : mem),
  FWINV L inp lo r me dF m' ->
  evt usegs (fw_post_gen r F fc L dF inp lo me)
    (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -96)) (r_gp r) (r_tp r) y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24
             y25 (r_s10 r) (r_s11 r) y28 y29 y30 y31)
        F (wz Z_FW_EPI) fc None m' (seg_rom usegs)).
Proof.
  intros until m'. intros (DR & DIN & (j0 & FR) & STK & MU & WM & MI). unfold fw_frame in FR. unfold Z_FW_EPI.
  pose proof (fc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_FILLWIN_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 12 zs. release_frame FR STK (bv_unsigned (r_sp r)). zs.
  apply evt_done. unfold fw_post_gen. do 15 eexists. exists m'.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK|]. split; [exact DR| exact DIN].
Qed.
End KIT.
End Z_fw_kit.


Module Z_fw_high.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_slow_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_defl_iface F_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ukit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface.Z_fw_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_fw.Z_fw_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState DeflateLz FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Ltac join_x8 v pcj :=
  lazymatch goal with
  | |- evt _ _ (MS (TNode ?A None (TNode (TNode (TNode ?B (Some _) ?C) ?x4 ?D) ?x2 ?E)) ?F _ ?fc None ?m ?rom) =>
      eapply (evt_cut usegs (fun ms' => ms' = MS (TNode A None (TNode (TNode (TNode B (Some v) C) x4 D) x2 E)) F (wz pcj) fc None m rom))
  end.

Section HIGH.
Variables (L : dlay) (inp : list Z) (nout lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : fw_ctx L inp nout lo r me.

Lemma fw_high : forall (X : deflate_state)
    (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31 : word) (m : mem),
  FWINV L inp lo r me X m -> fw_wf 32768 32768 X ->
  evt usegs (fw_post_gen r F fc L (fill_window_high X) inp lo me)
    (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -96)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) y9 y10 y11 y12 y13 y14 y15 y16 y17 (wz (dl_As L + 5932)) y19
             y20 y21 y22 y23 y24 (wz 1) (r_s10 r) (r_s11 r) y28 y29 y30 y31)
        F (wz Z_FW_HIGH) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros (DR & DIN & (j0 & FR) & STK & MU & WM & MI) FW. unfold Z_FW_HIGH. unfold fw_W in MU. unfold fw_frame in FR.
  destruct CTX as [LOsp SP16 LAY0 BEL IO DIN0]. unfold Z_FILLWIN_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY. pose proof BEL as BEL'. below_open BEL'.
  destruct FW as [Wws _ Wwl Wwsz _ _ _ _ _ _ _ Wins Wlook Wsl _ _ Whw _ _ _ _ _ _ _ _ _ _ _].
  open_DST ST. open_A GA. open_D GD.
  pose proof (munch_refl [(dl_As L + 5881, dl_As L + 5968); (dl_Aw L, dl_Aw L + DS_WIN)] m) as MUf. pose proof (wmono_refl usegs m) as WMf.
  assert (KEEP : forall m1 (y ya yb yc : word), m1 = m ->
    evt usegs (fw_post_gen r F fc L X inp lo me)
      (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -96)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) y ya (wz (ds_window_size X)) (wz (ds_high_water X)) yb y14 y15 y16 y17
               (wz (dl_As L + 5932)) y19 y20 y21 y22 y23 y24 (wz 1) (r_s10 r) (r_s11 r) y28 y29 y30 y31) F (wz Z_FW_EPI) fc None m1 (seg_rom usegs))).
  { intros m1 y ya yb yc ->. apply (fw_epi L inp nout lo r F fc me CTX X). split; [split; [exact ZS|]|].
    - constructor; [exists hA1, hA2, hA3, hA4, hA5; exact GA| exact GB| exact GC| exists hD0, hD1, hD2, hD3, hD4; exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc
                   | exact Gheap| exact Gdep| exact Gwin| exact Gprev| exact Ghead| exact Gpend| exact LENS| exact LAY].
    - split; [exact DIN|]. split; [eexists; exact FR|]. split; [exact STK|]. split; [unfold fw_W; exact MU|]. split; [exact WM| exact MI]. }
  zs. zs.
  zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
  { rewrite (fwh_none X) by lia. unfold Z_FW_EPI in KEEP. apply (KEEP m y9 y10 y13 y13). reflexivity. }
  zs. zs. zs.
  zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
  -
    zstep. zstep. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
    { rewrite (fwh_c X) by (unfold WIN_INIT, MAX_MATCH; lia). unfold Z_FW_EPI in KEEP.
      apply (KEEP m _ _ _ y13). reflexivity. }
    zs. zstep. gF. zstep. zstep. zstep. gX.
    zstep. zstep.
    assert (IB : fwh_init_b X = (if ds_window_size X - ds_high_water X <? ds_lookahead X + ds_strstart X + 258 - ds_high_water X
                                 then ds_window_size X - ds_high_water X else ds_lookahead X + ds_strstart X + 258 - ds_high_water X)).
    { unfold fwh_init_b, WIN_INIT, MAX_MATCH. cbv zeta. rewrite (Z.add_comm (ds_strstart X) (ds_lookahead X)). reflexivity. }
    zstep. join_x8 (wz (fwh_init_b X)) 0x16d0c.
    { if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia.
      - apply evt_done. repeat f_equal. rewrite IB. destruct (Z.ltb_spec (ds_window_size X - ds_high_water X) (ds_lookahead X + ds_strstart X + 258 - ds_high_water X)); lia.
      - zstep. apply evt_done. repeat f_equal. rewrite IB. destruct (Z.ltb_spec (ds_window_size X - ds_high_water X) (ds_lookahead X + ds_strstart X + 258 - ds_high_water X)); lia. }
    intros ms' ->.
    assert (RIB : 0 <= fwh_init_b X /\ ds_high_water X + fwh_init_b X <= ds_window_size X) by (rewrite IB; destruct (_ <? _) eqn:E4; [apply Z.ltb_lt in E4| apply Z.ltb_ge in E4]; lia).
    clear IB. assert (RI1 : 0 <= fwh_init_b X) by lia. assert (RI2 : ds_high_water X + fwh_init_b X <= 65536) by lia. assert (RI3 : 0 <= ds_high_water X) by lia.
    zstep. zstep. rewrite ?Z.mod_small by lia. zstep.
    open_win Gwin.
    destruct (u8arr_split3 _ (dl_Aw L) _ (Z.to_nat (ds_high_water X)) (Z.to_nat (fwh_init_b X)) Gwin ltac:(rewrite av8_length; lia)) as (O1 & O2 & O3). clear Gwin.
    assert (LO1 : length (firstn (Z.to_nat (ds_high_water X)) (av8 (ds_window X) 65536)) = Z.to_nat (ds_high_water X)) by (rewrite length_firstn, av8_length; lia).
    assert (LO3 : length (skipn (Z.to_nat (ds_high_water X) + Z.to_nat (fwh_init_b X)) (av8 (ds_window X) 65536)) = (Z.to_nat 65536 - Z.to_nat (ds_high_water X) - Z.to_nat (fwh_init_b X))%nat)
      by (rewrite length_skipn, av8_length; lia).
    replace (dl_Aw L + Z.of_nat (Z.to_nat (ds_high_water X))) with (dl_Aw L + ds_high_water X) in O2 by lia.
    replace (wz (ds_high_water X + dl_Aw L)) with (wz (dl_Aw L + ds_high_water X)) by (f_equal; lia).
    zstep.
    lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut; [eapply memset_callZ with (D := dl_Aw L + ds_high_water X) (C := 0) (N := fwh_init_b X); [exact O2| eassumption| lia| lia| lia| lia] | clear O2; post_call segs mm] end.
    name_mem mc.
    replace (dl_Aw L + ds_high_water X) with (dl_Aw L + Z.of_nat (Z.to_nat (ds_high_water X))) in POST by lia.
    pose proof (u8arr_join3k mc (dl_Aw L) _ _ _ _ _ LO1 O1 POST O3) as WIN. clear O1 POST O3 LO1 LO3.
    change (Z_to_bv 8 (0 mod 256)) with (Z_to_bv 8 0) in WIN.
    replace (Z.to_nat (ds_high_water X) + Z.to_nat (fwh_init_b X))%nat with (Z.to_nat (ds_high_water X + fwh_init_b X)) in WIN by lia.
    rewrite <- (av8_fill0 (ds_window X) 65536 (ds_high_water X) (fwh_init_b X)) in WIN by lia.
    assert (LWF : Z.of_nat (length (av8 (arr_fill (ds_window X) (ds_high_water X) (fwh_init_b X) 0) 65536)) = 65536) by (rewrite av8_length; lia).
    zs. zstep. zs.
    name_mem mF. tr_groups MUf WMf.
    rewrite (fwh_b X) by (unfold WIN_INIT, MAX_MATCH; lia).
    apply (fw_epi L inp nout lo r F fc me CTX). split; [split|].
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
    + split; [exact (fw_din L inp nout lo r me CTX mF MU)|]. split; [eexists; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| assumption].
  -
    zs. zstep. gF. gF. gF. zstep. zstep.
    assert (IA : fwh_init_a X = (if ds_window_size X - (ds_lookahead X + ds_strstart X) <? 258 then ds_window_size X - (ds_lookahead X + ds_strstart X) else 258)).
    { unfold fwh_init_a, WIN_INIT, MAX_MATCH. cbv zeta. rewrite (Z.add_comm (ds_strstart X) (ds_lookahead X)).
      destruct (Z.ltb_spec 258 (ds_window_size X - (ds_lookahead X + ds_strstart X))), (Z.ltb_spec (ds_window_size X - (ds_lookahead X + ds_strstart X)) 258); lia. }
    zstep. join_x8 (wz (fwh_init_a X)) 0x16cc4.
    { if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia.
      - apply evt_done. repeat f_equal. rewrite IA. destruct (Z.ltb_spec (ds_window_size X - (ds_lookahead X + ds_strstart X)) 258); lia.
      - zstep. apply evt_done. repeat f_equal. rewrite IA. destruct (Z.ltb_spec (ds_window_size X - (ds_lookahead X + ds_strstart X)) 258); lia. }
    intros ms' ->.
    assert (RIA : 0 <= fwh_init_a X /\ ds_lookahead X + ds_strstart X + fwh_init_a X <= ds_window_size X)
      by (rewrite IA; destruct (Z.ltb_spec (ds_window_size X - (ds_lookahead X + ds_strstart X)) 258); lia).
    clear IA. assert (RI1 : 0 <= fwh_init_a X) by lia. assert (RI2 : ds_lookahead X + ds_strstart X + fwh_init_a X <= 65536) by lia.
    assert (RI3 : 0 <= ds_lookahead X + ds_strstart X) by lia.
    zstep. zstep.
    open_win Gwin.
    destruct (u8arr_split3 _ (dl_Aw L) _ (Z.to_nat (ds_lookahead X + ds_strstart X)) (Z.to_nat (fwh_init_a X)) Gwin ltac:(rewrite av8_length; lia)) as (O1 & O2 & O3). clear Gwin.
    assert (LO1 : length (firstn (Z.to_nat (ds_lookahead X + ds_strstart X)) (av8 (ds_window X) 65536)) = Z.to_nat (ds_lookahead X + ds_strstart X)) by (rewrite length_firstn, av8_length; lia).
    assert (LO3 : length (skipn (Z.to_nat (ds_lookahead X + ds_strstart X) + Z.to_nat (fwh_init_a X)) (av8 (ds_window X) 65536))
                  = (Z.to_nat 65536 - Z.to_nat (ds_lookahead X + ds_strstart X) - Z.to_nat (fwh_init_a X))%nat)
      by (rewrite length_skipn, av8_length; lia).
    replace (dl_Aw L + Z.of_nat (Z.to_nat (ds_lookahead X + ds_strstart X))) with (dl_Aw L + (ds_lookahead X + ds_strstart X)) in O2 by lia.
    replace (wz (ds_lookahead X + ds_strstart X + dl_Aw L)) with (wz (dl_Aw L + (ds_lookahead X + ds_strstart X))) by (f_equal; lia).
    zstep.
    lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut; [eapply memset_callZ with (D := dl_Aw L + (ds_lookahead X + ds_strstart X)) (C := 0) (N := fwh_init_a X); [exact O2| eassumption| lia| lia| lia| lia] | clear O2; post_call segs mm] end.
    name_mem mc.
    replace (dl_Aw L + (ds_lookahead X + ds_strstart X)) with (dl_Aw L + Z.of_nat (Z.to_nat (ds_lookahead X + ds_strstart X))) in POST by lia.
    pose proof (u8arr_join3k mc (dl_Aw L) _ _ _ _ _ LO1 O1 POST O3) as WIN. clear O1 POST O3 LO1 LO3.
    change (Z_to_bv 8 (0 mod 256)) with (Z_to_bv 8 0) in WIN.
    replace (Z.to_nat (ds_lookahead X + ds_strstart X) + Z.to_nat (fwh_init_a X))%nat with (Z.to_nat ((ds_strstart X + ds_lookahead X) + fwh_init_a X)) in WIN by lia.
    replace (Z.to_nat (ds_lookahead X + ds_strstart X)) with (Z.to_nat (ds_strstart X + ds_lookahead X)) in WIN by lia.
    rewrite <- (av8_fill0 (ds_window X) 65536 (ds_strstart X + ds_lookahead X) (fwh_init_a X)) in WIN by lia.
    assert (LWF : Z.of_nat (length (av8 (arr_fill (ds_window X) (ds_strstart X + ds_lookahead X) (fwh_init_a X) 0) 65536)) = 65536) by (rewrite av8_length; lia).
    zstep. zstep. zs.
    name_mem mF. tr_groups MUf WMf.
    rewrite (fwh_a X) by (unfold WIN_INIT, MAX_MATCH; lia).
    apply (fw_epi L inp nout lo r F fc me CTX). split; [split|].
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
    + split; [exact (fw_din L inp nout lo r me CTX mF MU)|]. split; [eexists; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| assumption].
Qed.
End HIGH.
End Z_fw_high.


Module Z_fw_tail.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_slow_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_defl_iface Z_slow_model.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ukit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface.Z_fw_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_fw.Z_fw_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_fw.Z_fw_high OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState DeflateLz FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section TAIL.
Variables (L : dlay) (inp : list Z) (nout lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : fw_ctx L inp nout lo r me.

Lemma fw_tail : forall (X : deflate_state) (n : Z)
    (y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y19 y22 y23 y28 y29 y30 y31 : word) (m : mem),
  FWINV L inp lo r me X m -> fw_wf 32768 32768 X -> ds_insert X = 0 ->
  (n = 0 \/ n = 1) -> ds_strstart X + ds_lookahead X + n <= 65536 ->
  (ds_lookahead X + n <= 261 -> cs_avail_in (ds_strm X) = 0) ->
  evt usegs (fw_post_gen r F fc L (fill_window_high (fw_ins0 (set_lookahead X (ds_lookahead X + n)))) inp lo me)
    (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -96)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) y9 (wz n) y11 y12 y13 y14 y15 y16 y17
             (wz (dl_As L + 5932)) y19 (wz 3) (wz 32) y22 (wz 261) y23 (wz 1) (r_s10 r) (r_s11 r) y28 y29 y30 y31)
        F (wz Z_FW_TAIL) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros (DR & DIN & (j0 & FR) & STK & MU & WM & MI) FW INS Hn SLN EXIT. unfold Z_FW_TAIL. unfold fw_W in MU. unfold fw_frame in FR.
  pose proof CTX as CTX'. destruct CTX' as [LOsp SP16 LAY0 BEL IO DIN0]. unfold Z_FILLWIN_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY. pose proof BEL as BEL'. below_open BEL'.
  pose proof (lo_S _ LAY) as BKS.
  pose proof FW as FW0. destruct FW as [Wws Wwsr Wwl Wwsz Wpl Wwm Whs Whsr Whl Whm Whsh Wins Wlook Wsl Wms Wih Whw Wni Wai Winl Wti Wwr Wad1 Wad2 Wwb Wpb Whb Wib].
  clear Wwsr Wpl Wwm Whsr Whl Wms Wni Winl Wti Wwr Wad1 Wad2 Wpb Whb Wib.
  open_DST ST. open_A GA. open_D GD. open_win Gwin.
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] m) as MUf. pose proof (wmono_refl usegs m) as WMf.
  rewrite INS in GD.
  assert (KEND : forall (X3 : deflate_state) (mA : mem) (v5 v6 v7 v11 v12 v13 v14 v15 v16 v17 v28 : word),
    dzs mA L (ds_strm X) -> DST mA L X3 -> ds_strm X3 = ds_strm X -> fw_wf 32768 32768 X3 ->
    rw_cells usegs mA (bv_unsigned (r_sp r) + -96) (fw_frame j0 r) -> stk usegs mA lo (bv_unsigned (r_sp r) + -96) ->
    munch [(lo, bv_unsigned (r_sp r)); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + 5968); (dl_Aw L, dl_Aw L + 65536);
           (dl_Ap L, dl_Ap L + 2 * 32768); (dl_Ah L, dl_Ah L + 2 * 32768)] me mA -> wmono usegs me mA -> mem_inv usegs mA ->
    evt usegs (fw_post_gen r F fc L (fill_window_high X3) inp lo me)
      (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -96)) (r_gp r) (r_tp r) v5 v6 v7 (wz (dl_As L)) y9 (wz (ds_lookahead X + n)) v11 v12 v13 v14 v15 v16 v17
               (wz (dl_As L + 5932)) y19 (wz 3) (wz 32) y22 (wz 261) y23 (wz 1) (r_s10 r) (r_s11 r) v28 y29 y30 y31)
          F (wz 0x16c68) fc None mA (seg_rom usegs))).
  { intros X3 mA v5 v6 v7 v11 v12 v13 v14 v15 v16 v17 v28 ZSA STA ES3 FW3 FRA STKA MUA WMA MIA.
    destruct STA as [A3 B3 C3 D3 lt3 dt3 bt3 blc3 heap3 dep3 win3 prev3 head3 pend3 LENS3 LAY3].
    destruct A3 as (g1 & g2 & g3 & g4 & g5 & A3). unfold dsA_cells in A3. destruct ZSA as (q1 & q2 & q3 & q4 & ZSA). unfold zs_call_cells, zs_priv_cells in ZSA. cbn [app] in ZSA.
    unfold fw_frame in FRA.
    zstep. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia.
    - apply (fw_high L inp nout lo r F fc me CTX X3). 2:{ exact FW3. }
      split; [split; [exists q1, q2, q3, q4; rewrite ES3; exact ZSA| ]|].
      + constructor; [exists g1, g2, g3, g4, g5; exact A3| exact B3| exact C3| exact D3| exact lt3| exact dt3| exact bt3| exact blc3| exact heap3| exact dep3
                     | exact win3| exact prev3| exact head3| exact pend3| exact LENS3| exact LAY3].
      + split; [exact (fw_din L inp nout lo r me CTX mA MUA)|]. split; [eexists; exact FRA|]. split; [exact STKA|]. split; [exact MUA|]. split; [exact WMA| exact MIA].
    - zs. gF. zstep. al8 (dl_S L). gF. zs. rewrite (EXIT ltac:(lia)). zstep. if_false.
      apply (fw_high L inp nout lo r F fc me CTX X3). 2:{ exact FW3. }
      split; [split; [exists q1, q2, q3, q4; rewrite ES3; exact ZSA| ]|].
      + constructor; [exists g1, g2, g3, g4, g5; exact A3| exact B3| exact C3| exact D3| exact lt3| exact dt3| exact bt3| exact blc3| exact heap3| exact dep3
                     | exact win3| exact prev3| exact head3| exact pend3| exact LENS3| exact LAY3].
      + split; [exact (fw_din L inp nout lo r me CTX mA MUA)|]. split; [eexists; exact FRA|]. split; [exact STKA|]. split; [exact MUA|]. split; [exact WMA| exact MIA]. }
  zs. zs. zs. zs. rewrite ?Z.add_0_l. zs.
  zstep. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by lia.
  -
    replace (fw_ins0 (set_lookahead X (ds_lookahead X + n))) with (set_lookahead X (ds_lookahead X + n))
      by (unfold fw_ins0; dsred; rewrite INS; replace (MIN_MATCH <=? ds_lookahead X + n + 0) with false by (symmetry; apply Z.leb_gt; unfold MIN_MATCH; lia); reflexivity).
    name_mem mA. tr_groups MUf WMf.
    apply KEND; [exact ZS| | reflexivity| | exact FR| exact STK| exact MU| exact WM| assumption].
    + constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| do 5 eexists; unfold dsD_cells; dsred; close_cells GD
                   | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep| exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS| exact LAY].
    + destruct FW0; constructor; dsred; first [assumption | lia].
  -
    zs. zs. zs. zstep. zstep. rewrite ?Z.mod_small by lia. rewrite Z.sub_0_r.
    zs. gF. zstep. zstep. zstep. gX. gF.
    ld8 Gwin (ds_window X) 65536 (dl_Aw L) (ds_strstart X) ltac:(apply Wwb; lia).
    zs. zs.
    gF.
    zstep. zstep. zstep. rewrite ?Z.mod_small by lia. zstep. rewrite zb_lxor_ones by lia. gF.
    zs.
    ld8 Gwin (ds_window X) 65536 (dl_Aw L) (ds_strstart X + 1) ltac:(apply Wwb; lia).
    zs. zs. zs. zs.
    rewrite (Z.mod_small (arr_get (ds_window X) (ds_strstart X)) 18446744073709551616) by (pose proof (Wwb (ds_strstart X) ltac:(lia)); lia).
    rewrite (hash_mach X (arr_get (ds_window X) (ds_strstart X)) (arr_get (ds_window X) (ds_strstart X + 1))) by lia.
    pose proof (update_hash_range X (arr_get (ds_window X) (ds_strstart X)) (arr_get (ds_window X) (ds_strstart X + 1)) ltac:(lia)) as Rhv.
    remember (update_hash X (arr_get (ds_window X) (ds_strstart X)) (arr_get (ds_window X) (ds_strstart X + 1))) as h eqn:Eh.
    zs.
    zstep. if_true.
    replace (fw_ins0 (set_lookahead X (ds_lookahead X + n)))
      with (set_ins_h (set_ins_h (set_lookahead X (ds_lookahead X + n)) (arr_get (ds_window X) (ds_strstart X))) h).
    2:{ unfold fw_ins0. dsred. rewrite INS, Z.sub_0_r. replace (MIN_MATCH <=? ds_lookahead X + n + 0) with true by (symmetry; apply Z.leb_le; unfold MIN_MATCH; lia).
        rewrite Eh. reflexivity. }
    name_mem mA. tr_groups MUf WMf.
    apply KEND; [exact ZS| | reflexivity| | exact FR| exact STK| exact MU| exact WM| assumption].
    + constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| do 5 eexists; unfold dsD_cells; dsred; close_cells GD
                   | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep| exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS| exact LAY].
    + subst h. destruct FW0; constructor; dsred; first [assumption | lia | apply update_hash_range; lia].
Qed.
End TAIL.
End Z_fw_tail.


Module Z_fw_read.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_slow_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_defl_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_readbuf Z_ukit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface.Z_fw_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_fw.Z_fw_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_fw.Z_fw_high OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_fw.Z_fw_tail OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_readbuf OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState DeflateLz FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section READ.
Variables (L : dlay) (inp : list Z) (nout lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : fw_ctx L inp nout lo r me.

Lemma fw_read : forall (X : deflate_state) (more : Z)
    (y1 y5 y6 y7 y10 y12 y13 y14 y15 y16 y17 y19 y22 y23 y28 y29 y30 y31 : word) (m : mem),
  FWINV L inp lo r me X m -> fw_wf 32768 32768 X -> ds_insert X = 0 -> ds_wrap X <> 2 -> cs_avail_in (ds_strm X) <= 1 ->
  din_tie inp X ->
  more = ds_window_size X - ds_lookahead X - ds_strstart X -> (more = 0 -> 262 < ds_lookahead X) ->
  evt usegs (fw_post_gen r F fc L (fill_window_high (fwB X more)) inp lo me)
    (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -96)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) (wz more) y10 (wz (ds_strstart X)) y12 y13 y14 y15 y16 y17
             (wz (dl_As L + 5932)) y19 (wz 3) (wz 32) y22 (wz 261) y23 (wz 1) (r_s10 r) (r_s11 r) y28 y29 y30 y31)
        F (wz Z_FW_READ) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros INV FW INS W2 AI TIE EM ZM. unfold Z_FW_READ.
  pose proof INV as INV0. destruct INV as (DR & DIN & (j0 & FR) & STK & MU & WM & MI). unfold fw_W in MU. unfold fw_frame in FR.
  pose proof CTX as CTX'. destruct CTX' as [LOsp SP16 LAY0 BEL IO DIN0]. unfold Z_FILLWIN_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof DR as DR0. destruct DR0 as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY. pose proof BEL as BEL'. below_open BEL'.
  pose proof (lo_S _ LAY) as BKS.
  pose proof FW as FW0. destruct FW as [_ _ Wwl Wwsz _ _ _ _ _ _ _ Wins Wlook Wsl _ _ _ Wni Wai Winl _ _ _ _ _ _ _ _].
  open_DST ST. open_A GA. open_zs ZS.
  zs. gF. zstep. al8 (dl_S L). gF.
  zs.
  zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia.
  {
    rewrite (fwB_0 X more) by lia. apply (fw_high L inp nout lo r F fc me CTX X); [exact INV0| exact FW0]. }
  assert (A1 : cs_avail_in (ds_strm X) = 1) by lia. clear K0 AI.
  zs. zstep. zstep. rewrite ?Z.mod_small by lia. zstep. gF. zstep. zstep. zstep. gX.
  zs. zstep. gF. zstep. zstep. gX.
  clear GA ZS GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend.
  zstep. zstep.
  remember (wz (bv_unsigned (r_sp r) + -96)) as spw eqn:Espw.
  assert (ESP : bv_unsigned spw = bv_unsigned (r_sp r) + -96) by (rewrite Espw; apply unsigned_lit; lia).
  call (read_buf_spec L X inp nout lo more (ds_lookahead X + (dl_Aw L + ds_strstart X))).
  1:{ exact DR. } 1:{ exact DIN. } 1:{ exact TIE. } 1:{ exact MI. } 1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. unfold Z_READBUF_STACK. lia. }
  1:{ rewrite ESP. clear - SP16 RSP LOsp. Z.div_mod_to_equations. lia. } 1:{ unfold dlay_below in *. rewrite ESP. lia. } 1:{ exact IO. }
  1:{ exact FW0. } 1:{ exact W2. } 1:{ exact A1. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
  lazymatch goal with H : stk usegs _ lo (bv_unsigned spw) |- _ => rewrite ESP in H; rename H into STK1 end.
  lazymatch goal with H : DREP _ L (fst _) |- _ => rename H into DR1 end.
  lazymatch goal with H : din _ L inp |- _ => rename H into DIN1 end.
  subst spw.
  destruct (read_buf_small X (ds_strstart X + ds_lookahead X) more) as (R1 & R2 & R3 & R4 & R5 & _ & _).
  pose proof (read_buf_wf 32768 32768 X (ds_strstart X + ds_lookahead X) more FW0 eq_refl ltac:(lia) ltac:(lia)) as RW. cbv zeta in RW.
  remember (read_buf X (RB_window (ds_strstart X + ds_lookahead X)) more) as rb eqn:Erb.
  unfold fwB. rewrite A1. cbn [Z.eqb Pos.eqb]. rewrite <- Erb.
  rewrite (fw_insert_0 (set_lookahead (fst rb) (ds_lookahead (fst rb) + snd rb))) by (dsred; rewrite R5; exact INS).
  apply (fw_tail L inp nout lo r F fc me CTX (fst rb) (snd rb)).
  - split; [exact DR1|]. split; [exact DIN1|]. split; [eexists; exact FR|]. split; [exact STK1|]. split; [exact MU|]. split; [exact WM| assumption].
  - exact (proj1 RW).
  - rewrite R5. exact INS.
  - unfold rb_len in R1. rewrite A1 in R1. destruct (Z.ltb_spec more 1); lia.
  - unfold rb_len in R1. rewrite A1 in R1. destruct (Z.ltb_spec more 1); lia.
  - unfold rb_len in R1, R2. rewrite A1 in R1, R2. destruct (Z.ltb_spec more 1); lia.
Qed.
End READ.
End Z_fw_read.


Module Z_fw_slide.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_slow_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_defl_iface Z_slow_model.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ukit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface.Z_fw_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_fw.Z_fw_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState DeflateLz FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition Z_SH1 : Z := 0x16a44.
Definition Z_SH1X : Z := 0x16a70.
Definition Z_SH2 : Z := 0x16a9c.
Definition Z_SH2X : Z := 0x16ac8.     (* 1.4 UBSan: the prev loop exits to the new sw s9,28(s2) (s->slid = 1), then the addw *)
Definition Z_FW_TRAP : Z := 0x16d60.
Definition Z_FW_TRAPA : Z := 0x16d5c.


Lemma av8_blit_down : forall a N sofs n, 0 <= n -> n <= sofs -> sofs + n <= N -> N <= arr_len a ->
  av8 (arr_blit a 0 a sofs n) N = firstn (Z.to_nat n) (skipn (Z.to_nat sofs) (av8 a N)) ++ skipn (Z.to_nat n) (av8 a N).
Proof.
  intros a N sofs n Hn Hs HN HL. apply list_ext_nth.
  - rewrite length_app, length_firstn, !length_skipn, !av8_length. lia.
  - intros j Hj. rewrite av8_length in Hj.
    replace j with (Z.to_nat (Z.of_nat j)) at 1 by lia. rewrite av8_nth by lia. rewrite arr_get_blit. unfold arr_inb.
    destruct (Z_lt_le_dec (Z.of_nat j) n) as [C|C].
    + replace ((0 <=? Z.of_nat j) && (Z.of_nat j <? 0 + Z.max 0 n) && ((0 <=? Z.of_nat j) && (Z.of_nat j <? arr_len a))) with true
        by (symmetry; rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia).
      rewrite nth_error_app1 by (rewrite length_firstn, length_skipn, av8_length; lia).
      rewrite nth_error_firstn. destruct (Nat.ltb_spec j (Z.to_nat n)); [|lia].
      rewrite nth_error_skipn. replace (Z.to_nat sofs + j)%nat with (Z.to_nat (sofs + (Z.of_nat j - 0))) by lia.
      rewrite av8_nth by lia. reflexivity.
    + replace ((0 <=? Z.of_nat j) && (Z.of_nat j <? 0 + Z.max 0 n) && ((0 <=? Z.of_nat j) && (Z.of_nat j <? arr_len a))) with false
        by (symmetry; rewrite !andb_false_iff, !Z.ltb_ge; lia).
      rewrite nth_error_app2 by (rewrite length_firstn, length_skipn, av8_length; lia).
      rewrite length_firstn, length_skipn, av8_length, nth_error_skipn.
      replace (Z.to_nat n + (j - Nat.min (Z.to_nat n) (Z.to_nat N - Z.to_nat sofs)))%nat with (Z.to_nat (Z.of_nat j)) by lia.
      rewrite av8_nth by lia. reflexivity.
Qed.

Lemma u8arr_join2z : forall m A (b1 b2 : list byte) n, Z.of_nat (length b1) = n ->
  rw_cells usegs m A [CB (Z.to_nat n) b1] -> u8arr usegs m (A + n) b2 -> u8arr usegs m A (b1 ++ b2).
Proof.
  intros m A b1 b2 n L H1 H2. apply u8arr_app. split; [eapply u8arr_of_rw_cells; exact H1| rewrite L; exact H2].
Qed.

Definition fw_slide4 (s : deflate_state) (more : Z) : deflate_state :=
  set_block_start (set_strstart (set_match_start
    (set_window s (arr_blit (ds_window s) 0 (ds_window s) 32768 (32768 - more)))
    (wrap32 (ds_match_start s - 32768))) (ds_strstart s - 32768)) (ds_block_start s - 32768).

Lemma fw_slide_eq0 : forall s more, ds_insert s = 0 -> 32768 <= ds_strstart s -> ds_w_size s = 32768 -> ds_hash_size s = 32768 ->
  0 <= more <= 32768 ->
  fw_slide s 32768 more
  = set_prev (set_head (fw_slide4 s more) (slide_hash_loop (Z.to_nat 32768) (ds_head s) 32768 32768))
             (slide_hash_loop (Z.to_nat 32768) (ds_prev s) 32768 32768).
Proof.
  intros s more INS SS WS HS HM. unfold fw_slide, fw_slide4. cbv zeta. dsred. rewrite INS.
  replace (ds_strstart s - 32768 <? 0) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota beta.
  unfold slide_hash. dsred. rewrite WS, HS. rewrite (wrap32_id (32768 - more)) by lia. reflexivity.
Qed.

Lemma shm_mach : forall v, 0 <= v < 65536 ->
  Z.land ((Z.b2z (v <? (v - 32768) mod 18446744073709551616) + -1) mod 18446744073709551616) ((v - 32768) mod 18446744073709551616)
  = shm 32768 v.
Proof.
  intros v Hv. rewrite shm_small by lia. destruct (Z.leb_spec 32768 v) as [C|C].
  - rewrite (Z.mod_small (v - 32768)) by lia. replace (v <? v - 32768) with false by (symmetry; apply Z.ltb_ge; lia).
    cbn [Z.b2z]. change ((0 + -1) mod 18446744073709551616) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
  - replace ((v - 32768) mod 18446744073709551616) with (v - 32768 + 18446744073709551616) by (Z.div_mod_to_equations; lia).
    replace (v <? v - 32768 + 18446744073709551616) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn [Z.b2z]. change ((1 + -1) mod 18446744073709551616) with 0. apply Z.land_0_l.
Qed.

Lemma ms_mach : forall v, le4 (wz (bv_swrap 32 (bv_unsigned (sx32 (wz v)) - 32768))) = le4 (wz (wrap32 (v - 32768))).
Proof.
  intros v. apply le4_wz_mod. unfold sx32. rewrite !Z_to_bv_unsigned, wrap32_mod.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul N.sub N.of_nat Pos.of_succ_nat].
  Z.div_mod_to_equations. lia.
Qed.

Lemma bs_guard : forall bs, - 2 ^ 62 <= bs < 2 ^ 62 ->
  Z.b2z (Z.lxor ((bs mod 18446744073709551616 - 32768) mod 18446744073709551616) 9223372036854775808
         <? Z.lxor (bs mod 18446744073709551616) 9223372036854775808) = 1.
Proof.
  intros bs Hbs. change 9223372036854775808 with (2^63).
  rewrite !zb_lxor_sign by (Z.div_mod_to_equations; lia).
  replace (_ <? _) with true; [reflexivity|]. symmetry. apply Z.ltb_lt.
  change (2^63) with 9223372036854775808. change (2^64) with 18446744073709551616.
  destruct (Z_lt_le_dec bs 0).
  - replace (bs mod 18446744073709551616) with (bs + 18446744073709551616) by (Z.div_mod_to_equations; lia).
    rewrite (Z.mod_small (bs + 18446744073709551616 - 32768)) by lia.
    Z.div_mod_to_equations. lia.
  - rewrite (Z.mod_small bs) by lia.
    destruct (Z_lt_le_dec bs 32768).
    + replace ((bs - 32768) mod 18446744073709551616) with (bs - 32768 + 18446744073709551616) by (Z.div_mod_to_equations; lia).
      Z.div_mod_to_equations. lia.
    + rewrite (Z.mod_small (bs - 32768)) by lia. Z.div_mod_to_equations. lia.
Qed.

Ltac st16u ARR a n A idx v EQ :=
  let SOK := fresh "SOK" in
  pose proof (u16arr_store_ok usegs _ A (av16 a n) idx (wa (A + 2 * idx)) ARR ltac:(rewrite av16_length; lia) eq_refl) as SOK;
  zstep;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le2 ?w)) _) =>
      let E := addr_expr a0 in
      let ARR' := fresh "ARRn" in
      pose proof (av16_write m0 A a n idx w v ARR ltac:(lia) ltac:(lia) ltac:(EQ)) as ARR';
      unfold u16arr in ARR';
      replace (A + 2 * idx) with E in ARR' by lia;
      let LN := fresh "L16" in pose proof (av16_zlength (arr_set a idx v) n ltac:(lia)) as LN;
      let LA := fresh "LNA" in pose proof (arr_len_set a idx v) as LA;
      clear ARR; store_done; rename ARR' into ARR
  end.


Definition shpost1 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (pcx A : Z) (a' : arr) (m : mem) : machine_state -> Prop :=
  fun ms' => exists x14 x15 m',
    ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (wz 32768) x11 (wz 0) (wz A) x14 x15 x16 x17 x18 x19 (wz 3) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
             F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch [(A, A + 65536)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' A (u16s (av16 a' 32768)).

Definition shpost2 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (pcx A : Z) (a' : arr) (m : mem) : machine_state -> Prop :=
  fun ms' => exists x14 x15 m',
    ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (wz 32768) x11 (wz A) (wz 0) x14 x15 x16 x17 x18 x19 (wz 3) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
             F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch [(A, A + 65536)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' A (u16s (av16 a' 32768)).

Section LOOPS.

Lemma shloop_h : forall (n : nat) (k : Z) (a : arr) (A : Z)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  k = Z.of_nat (S n) -> k <= 32768 ->
  u8arr usegs m A (u16s (av16 a 32768)) -> arr_len a = 32768 -> (forall i, 0 <= i < 32768 -> 0 <= arr_get a i < 65536) ->
  mem_inv usegs m -> 2 <= A -> A + 65536 < 2^62 ->
  evt usegs (shpost1 x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc Z_SH1X A
                    (slide_hash_loop (Z.to_nat k) a k 32768) m)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (wz 32768) x11 (wz k) (wz (A + 2 * k)) x14 x15 x16 x17 x18 x19 (wz 3) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (wz Z_SH1) fc None m (seg_rom usegs)).
Proof.
  intros n. induction n as [n IH] using lt_wf_ind.
  intros until m. intros Hk Kle ARR LEN RNG MI A2 AH. unfold Z_SH1.
  assert (K1 : 1 <= k) by lia.
  pose proof (av16_zlength a 32768 ltac:(lia)) as L16.
  pose proof (RNG (k - 1) ltac:(lia)) as Rv.
  pose proof (munch_refl [(A, A + 65536)] m) as MU0. pose proof (wmono_refl usegs m) as WM0.
  gF.
  ld16 ARR a 32768 A (k - 1) ltac:(exact Rv).
  zs. zstep. zstep. zstep. rewrite (shm_mach (arr_get a (k - 1))) by exact Rv.
  pose proof (shm_range 32768 (arr_get a (k - 1))) as Rs.
  zstep. zs.
  st16u ARR a 32768 A (k - 1) (shm 32768 (arr_get a (k - 1))) ltac:(reflexivity).
  zstep. rewrite (slide_hash_loop_step k a 32768) by exact K1. cbv zeta.
  name_mem m1.
  zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  -
    replace (k - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (wz (A + 2 * k + -2)) with (wz (A + 2 * (k - 1))) by (f_equal; lia).
    replace (wz (k + -1)) with (wz (k - 1)) by (f_equal; lia).
    eapply evt_mono.
    + eapply (IH (n - 1)%nat ltac:(lia) (k - 1) _ A); [lia| lia| exact ARR| rewrite arr_len_set; exact LEN| | assumption| lia| lia].
      intros i Hi. rewrite arr_get_set. destruct (_ && _); [exact Rs| apply RNG; exact Hi].
    + intros ms' (x14' & x15' & m2 & -> & MU2 & WM2 & MI2 & ARR2). exists x14', x15', m2.
      split; [reflexivity|]. split; [eapply munch_trans; [exact MU0| exact MU2]|]. split; [eapply wmono_trans; [exact WM0| exact WM2]|].
      split; [exact MI2| exact ARR2].
  -
    replace (k - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
    replace (wz (A + 2 * k + -2)) with (wz A) by (f_equal; lia).
    replace (wz (k + -1)) with (wz 0) by (f_equal; lia).
    apply evt_done. unfold shpost1, Z_SH1X. eexists _, _, m1.
    split; [reflexivity|]. split; [exact MU0|]. split; [exact WM0|]. split; [assumption| exact ARR].
Qed.

Lemma shloop_p : forall (n : nat) (k : Z) (a : arr) (A : Z)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  k = Z.of_nat (S n) -> k <= 32768 ->
  u8arr usegs m A (u16s (av16 a 32768)) -> arr_len a = 32768 -> (forall i, 0 <= i < 32768 -> 0 <= arr_get a i < 65536) ->
  mem_inv usegs m -> 2 <= A -> A + 65536 < 2^62 ->
  evt usegs (shpost2 x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc Z_SH2X A
                    (slide_hash_loop (Z.to_nat k) a k 32768) m)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (wz 32768) x11 (wz (A + 2 * k)) (wz k) x14 x15 x16 x17 x18 x19 (wz 3) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (wz Z_SH2) fc None m (seg_rom usegs)).
Proof.
  intros n. induction n as [n IH] using lt_wf_ind.
  intros until m. intros Hk Kle ARR LEN RNG MI A2 AH. unfold Z_SH2.
  assert (K1 : 1 <= k) by lia.
  pose proof (av16_zlength a 32768 ltac:(lia)) as L16.
  pose proof (RNG (k - 1) ltac:(lia)) as Rv.
  pose proof (munch_refl [(A, A + 65536)] m) as MU0. pose proof (wmono_refl usegs m) as WM0.
  gF.
  ld16 ARR a 32768 A (k - 1) ltac:(exact Rv).
  zs. zstep. zstep. zstep. rewrite (shm_mach (arr_get a (k - 1))) by exact Rv.
  pose proof (shm_range 32768 (arr_get a (k - 1))) as Rs.
  zstep. zs.
  st16u ARR a 32768 A (k - 1) (shm 32768 (arr_get a (k - 1))) ltac:(reflexivity).
  zstep. rewrite (slide_hash_loop_step k a 32768) by exact K1. cbv zeta.
  name_mem m1.
  zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  -
    replace (k - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (wz (A + 2 * k + -2)) with (wz (A + 2 * (k - 1))) by (f_equal; lia).
    replace (wz (k + -1)) with (wz (k - 1)) by (f_equal; lia).
    eapply evt_mono.
    + eapply (IH (n - 1)%nat ltac:(lia) (k - 1) _ A); [lia| lia| exact ARR| rewrite arr_len_set; exact LEN| | assumption| lia| lia].
      intros i Hi. rewrite arr_get_set. destruct (_ && _); [exact Rs| apply RNG; exact Hi].
    + intros ms' (x14' & x15' & m2 & -> & MU2 & WM2 & MI2 & ARR2). exists x14', x15', m2.
      split; [reflexivity|]. split; [eapply munch_trans; [exact MU0| exact MU2]|]. split; [eapply wmono_trans; [exact WM0| exact WM2]|].
      split; [exact MI2| exact ARR2].
  -
    replace (k - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
    replace (wz (A + 2 * k + -2)) with (wz A) by (f_equal; lia).
    replace (wz (k + -1)) with (wz 0) by (f_equal; lia).
    apply evt_done. unfold shpost2, Z_SH2X. eexists _, _, m1.
    split; [reflexivity|]. split; [exact MU0|]. split; [exact WM0|]. split; [assumption| exact ARR].
Qed.

End LOOPS.


Section SLIDE.
Variables (L : dlay) (inp : list Z) (nout lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : fw_ctx L inp nout lo r me.

Lemma fw_slide_stage : forall (X : deflate_state) (more : Z) (Q : machine_state -> Prop)
    (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y23 y28 y29 y30 y31 : word) (m : mem),
  FWINV L inp lo r me X m -> fw_wf 32768 32768 X -> ds_insert X = 0 ->
  65274 <= ds_strstart X -> more = 65536 - ds_lookahead X - ds_strstart X ->
  - 2 ^ 62 <= ds_block_start X < 2 ^ 62 ->
  (forall (mA : mem) (v1 v5 v6 v7 v10 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 : word),
     FWINV L inp lo r me (fw_slide X 32768 more) mA ->
     evt usegs Q (MS (mkR v1 (wz (bv_unsigned (r_sp r) + -96)) (r_gp r) (r_tp r) v5 v6 v7 (wz (dl_As L)) (wz (32768 + more)) v10 (wz (ds_strstart X - 32768)) v12 v13 v14 v15 v16 v17
                      (wz (dl_As L + 5932)) (wz 32768) (wz 3) (wz 32) y22 (wz 261) y23 (wz 1) (r_s10 r) (r_s11 r) v28 v29 v30 v31)
                  F (wz Z_FW_READ) fc None mA (seg_rom usegs))) ->
  evt usegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -96)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) (wz more) y10 y11 y12 y13 y14 y15 y16 y17
                   (wz (dl_As L + 5932)) (wz 32768) (wz 3) (wz 32) y22 (wz 261) y23 (wz 1) (r_s10 r) (r_s11 r) y28 y29 y30 y31)
               F (wz Z_FW_SLIDE) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros INV FW INS SS EM RBS K. unfold Z_FW_SLIDE.
  destruct INV as (DR & DIN & (j0 & FR) & STK & MU & WM & MI). unfold fw_W in MU. unfold fw_frame in FR.
  pose proof CTX as CTX'. destruct CTX' as [LOsp SP16 LAY0 BEL IO DIN0]. unfold Z_FILLWIN_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY. pose proof BEL as BEL'. below_open BEL'.
  pose proof FW as FW0. destruct FW as [Wws _ Wwl Wwsz Wpl _ Whs _ Whl _ _ Wins Wlook Wsl Wms _ _ _ _ _ _ _ _ _ _ Wpb Whb _].
  open_DST ST. open_A GA. open_D GD. rewrite INS in GD.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_Aw L, dl_Aw L + 65536)] m) as MUf. pose proof (wmono_refl usegs m) as WMf.
  open_win Gwin.
  pose proof (u8arr_sub_bytes _ (dl_Aw L) _ (Z.to_nat 32768) (Z.to_nat (32768 - more)) Gwin ltac:(rewrite av8_length; lia)) as SRC.
  destruct (u8arr_split3 _ (dl_Aw L) _ 0%nat (Z.to_nat (32768 - more)) Gwin ltac:(rewrite av8_length; lia)) as (_ & O2 & O3). clear Gwin LW.
  cbn [skipn] in O2. replace (dl_Aw L + Z.of_nat 0) with (dl_Aw L) in O2 by lia.
  remember (firstn (Z.to_nat (32768 - more)) (skipn (Z.to_nat 32768) (av8 (ds_window X) 65536))) as src eqn:Esrc.
  assert (Lsrc : length src = Z.to_nat (32768 - more)) by (rewrite Esrc, length_firstn, length_skipn, av8_length; lia).
  replace (Z.of_nat (Z.to_nat 32768)) with 32768 in SRC by lia.
  remember (skipn (0 + Z.to_nat (32768 - more)) (av8 (ds_window X) 65536)) as w3 eqn:Ew3.
  assert (LO3 : Z.of_nat (length w3) = 65536 - (32768 - more)) by (rewrite Ew3, length_skipn, av8_length; lia).
  replace (dl_Aw L + Z.of_nat 0 + Z.of_nat (Z.to_nat (32768 - more))) with (dl_Aw L + (32768 - more)) in O3 by lia.
  zs. zstep. gF. zstep. zstep. zstep. gX.
  zs. zs. zs. rewrite ?Z.mod_small by lia.
  zstep.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [ eapply (memcpy_Z (dl_Aw L) (dl_Aw L + 32768) (32768 - more));
                      [exact SRC| exact Lsrc| exact O2| lia| eassumption| lia| lia| lia]
                    | clear O2 SRC; post_call segs mm ] end.
  name_mem mc.
  pose proof (u8arr_join2z mc (dl_Aw L) src w3 (32768 - more) ltac:(lia) PC O3) as WIN. clear PC O3 POST LO3.
  subst src w3. replace (0 + Z.to_nat (32768 - more))%nat with (Z.to_nat (32768 - more)) in WIN by lia.
  rewrite <- (av8_blit_down (ds_window X) 65536 32768 (32768 - more)) in WIN by lia.
  pose proof (arr_len_blit (ds_window X) 0 (ds_window X) 32768 (32768 - more)) as LNW. rewrite Wwl in LNW.
  remember (arr_blit (ds_window X) 0 (ds_window X) 32768 (32768 - more)) as w' eqn:Ew'.
  pose proof (av8_zlength w' 65536 ltac:(lia)) as LWF.
  zs. zs. zs. zstep. zs. zs. zstep. zstep. zs. zs.
  rewrite (bs_guard (ds_block_start X)) by lia. change (Z.b2z (9223372036854775808 <? 9223372036854808576)) with 1. gF.
  zs. zs.
  zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia; [| exfalso; lia].
  assert (AH2 : 2 <= dl_Ah L /\ dl_Ah L mod 2 = 0) by (pose proof (lo_h _ LAY) as BH; unfold blk_ok in BH; clear - BH; Z.div_mod_to_equations; lia).
  assert (AP2 : 2 <= dl_Ap L /\ dl_Ap L mod 2 = 0) by (pose proof (lo_p _ LAY) as BH; unfold blk_ok in BH; clear - BH; Z.div_mod_to_equations; lia).
  zs. rewrite Whs. zs. zstep. zstep. gF. zstep. zstep. zstep. gX. zstep. rewrite (land1_mod2 (dl_Ah L) (proj2 AH2)). gF. zs. rewrite Wws.
  replace (wz (65536 + dl_Ah L)) with (wz (dl_Ah L + 2 * 32768)) by (f_equal; lia).
  name_mem mA. tr_groups MUf WMf. clear MUf WMf.
  pose proof (munch_refl [(dl_Ap L, dl_Ap L + 65536); (dl_Ah L, dl_Ah L + 65536); (dl_As L + 5881, dl_As L + 5968)] mA) as MUf. pose proof (wmono_refl usegs mA) as WMf.
  open_u16 Ghead. open_u16 Gprev.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [ eapply (shloop_h (Z.to_nat 32767) 32768 (ds_head X) (dl_Ah L)); [lia| lia| exact Ghead| exact Whl| exact Whb| assumption| lia| lia]
                    | clear Ghead; post_call segs mm ] end.
  rename POST into HEAD. remember (slide_hash_loop (Z.to_nat 32768) (ds_head X) 32768 32768) as hd eqn:Ehd.
  assert (LNH : arr_len hd = 32768) by (rewrite Ehd, slide_hash_loop_len; exact Whl).
  pose proof (av16_zlength hd 32768 ltac:(lia)) as L16h.
  apply box in Ehd.
  zs. zstep. zstep. gF. zstep. zstep. zstep. gX. zstep. rewrite (land1_mod2 (dl_Ap L) (proj2 AP2)). gF. zstep.
  replace (wz (65536 + dl_Ap L)) with (wz (dl_Ap L + 2 * 32768)) by (f_equal; lia).
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [ eapply (shloop_p (Z.to_nat 32767) 32768 (ds_prev X) (dl_Ap L)); [lia| lia| exact Gprev| exact Wpl| exact Wpb| assumption| lia| lia]
                    | clear Gprev; post_call segs mm ] end.
  rename POST into PREV. remember (slide_hash_loop (Z.to_nat 32768) (ds_prev X) 32768 32768) as pv eqn:Epv.
  assert (LNP : arr_len pv = 32768) by (rewrite Epv, slide_hash_loop_len; exact Wpl).
  pose proof (av16_zlength pv 32768 ltac:(lia)) as L16p.
  zs. zs. name_mem mF. tr_groups MUf WMf.
  apply K. apply unbox in Ehd.
  rewrite (fw_slide_eq0 X more INS ltac:(lia) Wws Whs ltac:(lia)). rewrite <- Ehd, <- Epv.
  split; [split|].
  - exact ZS.
  - constructor.
    + exists hA1, hA2, hA3, hA4, hA5. unfold fw_slide4, dsA_cells. dsred. eapply rw_cells_sim; [exact GA| cells_sim_tac]. all: apply ms_mach.
    + exact GB. + exact GC.
    + do 5 eexists. unfold fw_slide4, dsD_cells. dsred. rewrite INS. close_cells GD.
    + exact Glt. + exact Gdt. + exact Gbt. + exact Gblc. + exact Gheap. + exact Gdep.
    + unfold dwin, fw_slide4. dsred. rewrite <- Ew'. exact WIN.
    + unfold dprev, u16arr, fw_slide4. dsred. exact PREV.
    + unfold dhead, u16arr, fw_slide4. dsred. exact HEAD.
    + exact Gpend.
    + destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13].
      constructor; unfold fw_slide4; dsred; [exact l1|exact l2|exact l3|exact l4|exact l5|exact l6|exact l7|exact l8|exact l9| rewrite <- Ew'; lia |exact LNP|exact LNH|exact l13].
    + exact LAY.
  - split; [exact (fw_din L inp nout lo r me CTX mF MU)|]. split; [eexists; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| assumption].
Qed.
End SLIDE.
End Z_fw_slide.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ukit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface.Z_fw_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_fw.Z_fw_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_fw.Z_fw_high OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_fw.Z_fw_tail OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_fw.Z_fw_read OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_fw.Z_fw_slide OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState DeflateLz FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Theorem fill_window_spec : fill_window_stmt.
Proof.
  unfold fill_window_stmt. intros until m. intros DR DIN TIE MI STK LO SP16 BEL IO FW INS W2 AI RBS ->. unfold Z_FILL_WINDOW.
  set (r := mkSR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  enough (G : evt usegs (fw_post_gen r F fc L (fill_window d) inp lo m)
                (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (dl_As L)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz 0x16920) fc None m (seg_rom usegs))) by exact G.
  pose proof (st_lay _ _ _ _ (proj2 DR)) as LAY.
  assert (CTX : fw_ctx L inp nout lo r m) by (constructor; assumption).
  rewrite (fill_window_eq1 d FW INS AI).
  pose proof (fwA_facts d FW INS) as FA. pose proof (proj1 (fw_more_eq d FW INS)) as EMQ.
  lay_open LAY. pose proof BEL as BEL0. below_open BEL0. pose proof IO as I0. io_open I0. unfold Z_FILLWIN_STACK in LO.
  pose proof (lo_s _ LAY) as BKs. unfold blk_ok in BKs.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof FW as FW0. destruct FW as [Wws _ Wwl Wwsz _ _ Whs _ _ _ _ Wins Wlook Wsl _ _ _ _ _ _ _ _ _ _ _ _ _ _].
  pose proof DR as DR0. destruct DR0 as [_ ST]. destruct ST as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. open_A GA.
  pose proof (munch_refl (fw_W L lo r) m) as MU. unfold fw_W in MU. cbn [r_sp r] in MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUf. pose proof (wmono_refl usegs m) as WMf.
  carve_frame 96%nat STK.
  do 12 zs.
  zs. zstep. al8 (dl_As L). gF.
  zs. zs. rewrite Wws. zs. zs. zs. zs. zs. zs. zs. zs. zs.
  zs. zs. rewrite Wws. zs. zs. zs. rewrite ?Z.mod_small by lia. zs. zs. zs.
  name_mem mH. clear GA.
  assert (INV : FWINV L inp lo r m d mH).
  { split.
    { apply (DREP_agree m mH L d DR).
      - eapply ag_blocks_munch; [exact LAY| exact MUf| exact WMf| | | | |]; cbn [disjoint_from]; slia.
      - apply (agree_on_of_munch [(lo, bv_unsigned sp)]); [exact MUf| exact WMf| lia| lia| cbn [disjoint_from]; slia]. }
    split; [exact (fw_din L inp nout lo r m CTX mH MU)|]. split; [eexists; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| assumption]. }
  clear MUf WMf FR STK MU WM.
  replace (wz (ds_window_size d - (ds_lookahead d + ds_strstart d))) with (wz (fw_more0 d)) by (unfold fw_more0; f_equal; lia).
  zstep. if_cases KS; zify_cond KS; rewrite ?unsigned_lit in KS by lia.
  -
    unfold fwA, moreA, slide_cond. replace (65274 <=? ds_strstart d) with false by (symmetry; apply Z.leb_gt; lia).
    apply (fw_read L inp nout lo r F fc m CTX d (fw_more0 d)); [exact INV| exact FW0| exact INS| exact W2| exact AI| exact TIE| unfold fw_more0; lia| ].
    unfold fwA, moreA, slide_cond in FA. replace (65274 <=? ds_strstart d) with false in FA by (symmetry; apply Z.leb_gt; lia). apply FA.
  -
    unfold fwA, moreA, slide_cond in FA |- *. replace (65274 <=? ds_strstart d) with true in FA |- * by (symmetry; apply Z.leb_le; lia).
    rewrite EMQ in FA |- *. destruct FA as (FW1 & INS1 & WR1 & ZS1 & _ & EM1 & _ & ZL1).
    destruct (fw_slide_wf 32768 32768 d (fw_more0 d) FW0 ltac:(lia) ltac:(unfold fw_more0; lia)) as (_ & _ & _ & ES1).
    eapply (fw_slide_stage L inp nout lo r F fc m CTX d (fw_more0 d)); [exact INV| exact FW0| exact INS| lia| unfold fw_more0; lia| exact RBS|].
    intros mA v1 v5 v6 v7 v10 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 INV1.
    replace (wz (32768 + fw_more0 d)) with (wz (fw_more0 d + 32768)) by (f_equal; lia).
    replace (wz (ds_strstart d - 32768)) with (wz (ds_strstart (fw_slide d 32768 (fw_more0 d)))) by (f_equal; exact ES1).
    apply (fw_read L inp nout lo r F fc m CTX (fw_slide d 32768 (fw_more0 d)) (fw_more0 d + 32768));
      [exact INV1| exact FW1| exact INS1| rewrite WR1; exact W2| rewrite ZS1; exact AI| unfold din_tie; rewrite ZS1; exact TIE| exact EM1| exact ZL1].
Qed.
