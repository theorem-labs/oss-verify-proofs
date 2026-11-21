(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import InitMem Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_kit Z_tr_kit Z_fw_slide
     Zg_defl_iface Zg_sto_model Zg_sto_ole Zg_sto_kit Zg_sto_rdo.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk SendModel FillWinModel
     RefDeflStored1 RefDeflStored2 RefDeflStored4 RefDeflStored5 RefDeflStored6 RefDeflStored7 RefDeflStored8 RefDeflStored9 RefDeflSafeS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition Z_STO_HW1 : Z := 0x184e8.
Definition Z_STO_APPEND : Z := 0x18444.

Lemma strm_set_matches : forall s v, ds_strm (set_matches s v) = ds_strm s. Proof. reflexivity. Qed.
Lemma strm_set_strstart : forall s v, ds_strm (set_strstart s v) = ds_strm s. Proof. reflexivity. Qed.
Lemma strm_set_window : forall s v, ds_strm (set_window s v) = ds_strm s. Proof. reflexivity. Qed.
Lemma win_set_strstart : forall s v, ds_window (set_strstart s v) = ds_window s. Proof. reflexivity. Qed.
Lemma win_set_matches : forall s v, ds_window (set_matches s v) = ds_window s. Proof. reflexivity. Qed.

Lemma hw_sl_fix : forall s, ds_high_water (sl_fix s) = ds_high_water s.
Proof. intros s. unfold sl_fix. destruct (ds_matches s <? 2); dsred; destruct (_ <? ds_insert _); dsred; reflexivity. Qed.

Lemma sl_fix_dec : forall s,
  sl_fix s = set_insert (set_matches s (if ds_matches s <? 2 then ds_matches s + 1 else ds_matches s))
                        (if ds_strstart s <? ds_insert s then ds_strstart s else ds_insert s).
Proof.
  intros s. unfold sl_fix. destruct (ds_matches s <? 2); dsred; destruct (ds_strstart s <? ds_insert s); destruct s; reflexivity.
Qed.

Ltac join_x9 v pcj :=
  lazymatch goal with
  | |- evt _ _ (MS (TNode (TNode ?A ?x1 (TNode (TNode ?B (Some _) ?C) ?x5 ?D)) None ?E) ?F _ ?fc None ?m ?rom) =>
      eapply (evt_cut psegs (fun ms' => ms' = MS (TNode (TNode A x1 (TNode (TNode B (Some v) C) x5 D)) None E) F (wz pcj) fc None m rom))
  end.

Section USED.
Variables (L : dlay) (flush ai0 : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : sto_ctx L inp rest0 lo r me.

Lemma sto_hw1 : forall (Q : machine_state -> Prop) (lz : Z) (Y : deflate_state)
    (y1 y5 y6 y7 y9 y12 y14 y15 y16 y17 y18 y19 y20 y21 y22 y27 y28 y29 y30 y31 : word) (m' : mem),
  STOINV L flush ai0 lz rest0 lo r me Y m' -> 0 <= ds_strstart Y < 2^32 -> 0 <= ds_high_water Y -> ds_high_water Y < ds_strstart Y ->
  TK11 L flush ai0 lz rest0 lo r F fc me Q Z_STO_LASTT (hw_st Y) ->
  evt psegs Q (MS (stoR L r y1 y5 y6 y7 y9 (wz (ds_strstart Y)) (wz (ds_strstart Y)) y12 (wz flush) y14 y15 y16 y17 y18 y19 y20 y21 y22 y27 y28 y29 y30 y31)
                  F (wz Z_STO_HW1) fc None m' (seg_rom psegs)).
Proof using CTX inp.
  intros until m'. intros INV RSTR RHW HLT K.
  pose proof INV as (DR & DOUT & RM & (j0 & FR) & STK & MU & WM & MI). unfold sto_frame in FR. unfold Z_STO_HW1, stoR, stoR7.
  pose proof (tc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_STORED_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY.
  pose proof (tc_bel _ _ _ _ _ _ CTX) as BEL. below_open BEL. pose proof (tc_io _ _ _ _ _ _ CTX) as IO. pose proof IO as IO'. io_open IO'.
  open_DST ST. open_D GD. unfold sto_W, slow_W in MU.
  pose proof (munch_refl [(dl_As L + 5881, dl_As L + 5968)] m') as MUf. pose proof (wmono_refl psegs m') as WMf.
  zs. name_mem mB.
  replace (wz (ds_strstart Y)) with (wz (ds_strstart (hw_st Y))) by (destruct (hw_st_facts Y) as (E & _); rewrite E; reflexivity).
  unfold TK11 in K. eapply K.
  unfold hw_st. replace (ds_high_water Y <? ds_strstart Y) with true by (symmetry; apply Z.ltb_lt; exact HLT).
  tr_groups MUf WMf.
  split; [split; [first [exact ZS| eapply dzs_munch; [exact ZS| exact MUf| exact WMf| cbn [disjoint_from]; slia]]|]|].
  { constructor; [exact GA| exact GB| exact GC| eexists _, _, _, _, _; unfold dsD_cells; dsred; close_cells GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS| exact LAY]. }
  split; [first [exact DOUT| eapply (dout_munch _ m' mB); [exact DOUT| exact RM| exact MUf| exact WMf| cbn [disjoint_from]; slia]]|].
  split; [exact RM|]. split; [eexists; unfold sto_frame; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| assumption].
Qed.

Definition app_st (inp : list Z) (W : deflate_state) (used : Z) : deflate_state :=
  set_block_start (set_insert (set_strstart
    (set_window W (arr_upd (ds_window W) (ds_strstart W) (arr_slice (arr_of_list inp) (cs_next_in (ds_strm W) - used) used)))
    (ds_strstart W + used)) (ins_add (ds_insert W) used (ds_w_size W))) (ds_strstart W + used).

Lemma sto_append : forall (Q : machine_state -> Prop) (lz : Z) (W : deflate_state) (used : Z)
    (y1 y5 y6 y7 y10 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y27 y28 y29 y30 y31 : word) (m' : mem),
  STOINV L flush ai0 lz rest0 lo r me W m' ->
  cs_input (ds_strm W) = arr_of_list inp -> ds_w_size W = 32768 ->
  0 < used < 32768 -> 0 <= ds_strstart W -> ds_strstart W + used <= 65536 -> 0 <= ds_insert W <= 32768 -> 0 <= ds_high_water W < 2^64 ->
  used <= cs_next_in (ds_strm W) -> cs_next_in (ds_strm W) <= zlength inp ->
  TK11 L flush ai0 lz rest0 lo r F fc me Q Z_STO_LASTT (hw_st (app_st inp W used)) ->
  evt psegs Q (MS (stoR L r y1 y5 y6 y7 (wz used) y10 (wz (ds_strstart W)) y12 y13 y14 y15 y16 y17 (wz used) y19 y20 y21 y22 y27 y28 y29 y30 y31)
                  F (wz Z_STO_APPEND) fc None m' (seg_rom psegs)).
Proof using CTX.
  intros until m'. intros INV INPW WSW RU RSTR RSU RINS RHW RUNI RNIL K.
  pose proof INV as (DR & DOUT & RM & (j0 & FR) & STK & MU & WM & MI). unfold sto_frame in FR. unfold Z_STO_APPEND, stoR, stoR7.
  pose proof (tc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_STORED_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY.
  pose proof (tc_bel _ _ _ _ _ _ CTX) as BEL. pose proof BEL as BEL'. below_open BEL'. pose proof (tc_io _ _ _ _ _ _ CTX) as IO. pose proof IO as IO'. io_open IO'.
  pose proof (sto_din _ _ _ _ _ _ CTX m' MU) as DIN.
  open_DST ST. open_A GA. open_D GD. open_zs ZS. open_win Gwin. unfold sto_W, slow_W in MU.
  zstep. zstep. zstep. zstep. zstep. rewrite (Z.mod_small (ds_strstart W)) by lia. zstep. zstep. zstep.

  pose proof (din_bytes m' L inp (cs_next_in (ds_strm W) - used) used DIN ltac:(lia) ltac:(lia) ltac:(lia)) as SRC.
  remember (arr_slice (arr_of_list inp) (cs_next_in (ds_strm W) - used) used) as l eqn:El.
  assert (Ll : length (zb8 l) = Z.to_nat used) by (rewrite zb8_length, El; apply arr_slice_length').
  destruct (u8arr_split3 _ (dl_Aw L) _ (Z.to_nat (ds_strstart W)) (Z.to_nat used) Gwin ltac:(rewrite av8_length; lia)) as (O1 & O2 & O3). clear Gwin.
  rewrite !Z2Nat.id in O2 by lia. rewrite !Z2Nat.id in O3 by lia.
  assert (LO1 : length (firstn (Z.to_nat (ds_strstart W)) (av8 (ds_window W) 65536)) = Z.to_nat (ds_strstart W)) by (rewrite length_firstn, av8_length; lia).
  assert (LO3 : length (skipn (Z.to_nat (ds_strstart W) + Z.to_nat used) (av8 (ds_window W) 65536)) = (Z.to_nat 65536 - (Z.to_nat (ds_strstart W) + Z.to_nat used))%nat)
    by (rewrite length_skipn, av8_length; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    pose proof (munch_refl [(dl_Aw L, dl_Aw L + 65536); (dl_As L, dl_As L + 212); (dl_As L + 5881, dl_As L + 5968)] mc) as MUf;
    pose proof (wmono_refl psegs mc) as WMf end.
  replace (dl_NI L + cs_next_in (ds_strm W) - used) with (dl_NI L + (cs_next_in (ds_strm W) - used)) by lia.
  zstep. call (memcpy_Z (dl_Aw L + ds_strstart W) (dl_NI L + (cs_next_in (ds_strm W) - used)) used).
  1:{ exact SRC. } 1:{ exact Ll. } 1:{ exact O2. } 1:{ zsep. } 1:{ eassumption. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
  pose proof (u8arr_join3z _ (dl_Aw L) _ _ _ (ds_strstart W) used ltac:(lia) ltac:(lia) LO1 O1 PC O3) as WIN.
  unfold zb8 in WIN. rewrite El in WIN. rewrite (av8_blit' (ds_window W) (arr_of_list inp) 65536 (ds_strstart W) (cs_next_in (ds_strm W) - used) used) in WIN by (pose proof (ln_win _ LENS); lia).
  rewrite arr_blit_upd, <- El in WIN.
  pose proof (arr_len_blit (ds_window W) (ds_strstart W) (arr_of_list inp) (cs_next_in (ds_strm W) - used) used) as LNW.
  rewrite arr_blit_upd, <- El, (ln_win _ LENS) in LNW.
  pose proof (av8_zlength (arr_upd (ds_window W) (ds_strstart W) l) 65536 ltac:(lia)) as LWF.
  clear O1 O3 PC POST SRC LO1 LO3.

  zs. zs. zs. zs. zs. zs.
  pose proof (ins_add_eq (ds_insert W) used (ds_w_size W) ltac:(lia) ltac:(lia) ltac:(lia)) as [EIA RIA].
  remember (if used <? ds_w_size W - ds_insert W then used else ds_w_size W - ds_insert W) as mn eqn:Emn.
  zstep. join_x9 (wz mn) 0x18488.
  { br_cases K1.
    - replace (wz mn) with (wz used) by (f_equal; rewrite Emn; destruct (Z.ltb_spec used (ds_w_size W - ds_insert W)); lia). apply evt_done. reflexivity.
    - zstep. replace (wz mn) with (wz (ds_w_size W - ds_insert W)) by (f_equal; rewrite Emn; destruct (Z.ltb_spec used (ds_w_size W - ds_insert W)); lia).
      apply evt_done. reflexivity. }
  intros ms' ->.
  zs. zs. zs. zs. zs. rewrite (Z.mod_small (ds_strstart W + used)) by lia. zs. zs. name_mem mB.

  tr_groups MUf WMf.
  assert (INV' : STOINV L flush ai0 lz rest0 lo r me (app_st inp W used) mB).
  { unfold app_st. split; [split; [eexists _, _, _, _; exact ZS|]|].
    { constructor; [eexists _, _, _, _, _; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| eexists _, _, _, _, _; unfold dsD_cells; dsred; close_cells GD
                   | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                   | unfold dwin; dsred; rewrite <- El; exact WIN| exact Gprev| exact Ghead| exact Gpend| | exact LAY].
      destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13].
      constructor; dsred; rewrite <- ?El; [exact l1| exact l2| exact l3| exact l4| exact l5| exact l6| exact l7| exact l8| exact l9| exact LNW| exact l11| exact l12| exact l13]. }
    split; [eapply (dout_munch _ m' mB); [exact DOUT| exact RM| exact MUf| exact WMf| cbn [disjoint_from]; slia]|].
    split; [exact RM|]. split; [eexists; unfold sto_frame; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| assumption]. }
  clear ZS GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep WIN Gprev Ghead Gpend.
  zstep. br_cases K2.
  - change (wz (ds_strstart W + used)) with (wz (ds_strstart (app_st inp W used))).
    replace (wz (ds_strstart (app_st inp W used))) with (wz (ds_strstart (hw_st (app_st inp W used)))) by (destruct (hw_st_facts (app_st inp W used)) as (E & _); rewrite E; reflexivity).
    unfold TK11 in K. eapply K.
    unfold hw_st. replace (ds_high_water (app_st inp W used) <? ds_strstart (app_st inp W used)) with false
      by (symmetry; apply Z.ltb_ge; cbn [ds_high_water ds_strstart app_st set_block_start set_insert set_strstart set_window]; lia).
    exact INV'.
  - zstep. change (wz (ds_strstart W + used)) with (wz (ds_strstart (app_st inp W used))).
    eapply (sto_hw1 Q lz (app_st inp W used)); [exact INV'| cbn [ds_strstart app_st set_block_start set_insert set_strstart]; lia
      | cbn [ds_high_water app_st set_block_start set_insert set_strstart set_window]; lia
      | cbn [ds_high_water ds_strstart app_st set_block_start set_insert set_strstart set_window]; lia| exact K].
Qed.

Variables (Q : machine_state -> Prop) (lz : Z) (XL : deflate_state).
Let used := ai0 - cs_avail_in (ds_strm XL).
Hypothesis HVL : so_inv XL.
Hypothesis WS : ds_w_size XL = 32768.
Hypothesis INP : cs_input (ds_strm XL) = arr_of_list inp.
Hypothesis RAI0 : 0 <= ai0 < 2^31.
Hypothesis RAIL : 0 <= cs_avail_in (ds_strm XL) <= ai0.
Hypothesis RUNI : used <= cs_next_in (ds_strm XL).
Hypothesis K : TK11 L flush ai0 lz rest0 lo r F fc me Q Z_STO_LASTT (hw_st (st_wupd XL used)).

Lemma used_eq : forall (y1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y27 y28 y29 y30 y31 : word) (m' : mem),
  STOINV L flush ai0 lz rest0 lo r me XL m' -> used = 0 ->
  evt psegs Q (MS (stoR L r y1 y5 y6 y7 (wz ai0) (wz (dl_S L)) (wz (cs_avail_in (ds_strm XL))) y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y27 y28 y29 y30 y31)
                  F (wz 0x183b4) fc None m' (seg_rom psegs)).
Proof using K RUNI RAIL RAI0 INP WS HVL used CTX inp.
  intros until m'. intros INV EU.
  pose proof INV as (DR & DOUT & RM & (j0 & FR) & STK & MU & WM & MI). unfold sto_frame in FR. unfold stoR, stoR7.
  pose proof (tc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_STORED_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY.
  pose proof (tc_bel _ _ _ _ _ _ CTX) as BEL. pose proof BEL as BEL'. below_open BEL'.
  pose proof (tc_io _ _ _ _ _ _ CTX) as IO. pose proof IO as IO'. io_open IO'.
  pose proof (vi_str _ HVL) as Vstr. pose proof (vi_bs _ HVL) as Vbs. pose proof (vi_wsz _ HVL) as Vwsz. pose proof (vi_ins _ HVL) as Vins.
  pose proof (vi_mat _ HVL) as Vmat. pose proof (vi_hw _ HVL) as Vhw. pose proof (vi_ni _ HVL) as Vni. pose proof (vi_inlen _ HVL) as Vinl.
  rewrite WS in Vstr, Vwsz, Vins. rewrite INP, arr_len_of_list in Vinl.
  pose proof (st_wupd_facts XL used) as [EHW ESTRM].
  open_DST ST. open_A GA. open_D GD. open_zs ZS. unfold sto_W, slow_W in MU.
  pose proof (munch_refl [(dl_Aw L, dl_Aw L + 65536); (dl_As L, dl_As L + 212); (dl_As L + 5881, dl_As L + 5968)] m') as MUf.
  pose proof (wmono_refl psegs m') as WMf.
  rewrite EU, st_wupd_0 in K.
  zs. zstep. zs. zstep. zstep. br_cases K1.
  - eapply (sto_hw1 Q lz XL); [| lia| lia| lia| exact K].
    split; [split; [eexists _, _, _, _; exact ZS|]|].
    { constructor; [eexists _, _, _, _, _; exact GA| exact GB| exact GC| eexists _, _, _, _, _; exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                   | exact Gwin| exact Gprev| exact Ghead| exact Gpend| exact LENS| exact LAY]. }
    split; [exact DOUT|]. split; [exact RM|]. split; [eexists; unfold sto_frame; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| assumption].
  - zstep.
    replace (wz (ds_strstart XL)) with (wz (ds_strstart (hw_st XL))) by (destruct (hw_st_facts XL) as (E & _); rewrite E; reflexivity).
    unfold TK11 in K. eapply K.
    unfold hw_st. replace (ds_high_water XL <? ds_strstart XL) with false by (symmetry; apply Z.ltb_ge; lia).
    split; [split; [eexists _, _, _, _; exact ZS|]|].
    { constructor; [eexists _, _, _, _, _; exact GA| exact GB| exact GC| eexists _, _, _, _, _; exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                   | exact Gwin| exact Gprev| exact Ghead| exact Gpend| exact LENS| exact LAY]. }
    split; [exact DOUT|]. split; [exact RM|]. split; [eexists; unfold sto_frame; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| assumption].
Qed.

Lemma used_ne : forall (y1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y27 y28 y29 y30 y31 : word) (m' : mem),
  STOINV L flush ai0 lz rest0 lo r me XL m' -> used <> 0 ->
  evt psegs Q (MS (stoR L r y1 y5 y6 y7 (wz ai0) (wz (dl_S L)) (wz (cs_avail_in (ds_strm XL))) y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y27 y28 y29 y30 y31)
                  F (wz 0x183dc) fc None m' (seg_rom psegs)).
Proof using K RUNI RAIL RAI0 INP WS HVL used CTX inp.
  intros until m'. intros INV NU.
  pose proof INV as (DR & DOUT & RM & (j0 & FR) & STK & MU & WM & MI). unfold sto_frame in FR. unfold stoR, stoR7.
  pose proof (tc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_STORED_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY.
  pose proof (tc_bel _ _ _ _ _ _ CTX) as BEL. pose proof BEL as BEL'. below_open BEL'.
  pose proof (tc_io _ _ _ _ _ _ CTX) as IO. pose proof IO as IO'. io_open IO'.
  pose proof (vi_str _ HVL) as Vstr. pose proof (vi_bs _ HVL) as Vbs. pose proof (vi_wsz _ HVL) as Vwsz. pose proof (vi_ins _ HVL) as Vins.
  pose proof (vi_mat _ HVL) as Vmat. pose proof (vi_hw _ HVL) as Vhw. pose proof (vi_ni _ HVL) as Vni. pose proof (vi_inlen _ HVL) as Vinl.
  rewrite WS in Vstr, Vwsz, Vins. rewrite INP, arr_len_of_list in Vinl.
  pose proof (st_wupd_facts XL used) as [EHW ESTRM].
  open_DST ST. open_A GA. open_D GD. open_zs ZS. unfold sto_W, slow_W in MU.
  pose proof (munch_refl [(dl_Aw L, dl_Aw L + 65536); (dl_As L, dl_As L + 212); (dl_As L + 5881, dl_As L + 5968)] m') as MUf.
  pose proof (wmono_refl psegs m') as WMf.
  pose proof (sto_din _ _ _ _ _ _ CTX m' MU) as DIN.
  zs. zs. fold used. zs. zstep. br_cases K1.
  -
    rewrite (st_wupd_sup XL used NU ltac:(lia)) in K. cbv zeta in K. rewrite !strm_set_matches, !win_set_matches, INP in K.
    open_win Gwin.
    zstep. zstep. zstep. zs. zstep. clear DIN.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (sto_din _ _ _ _ _ _ CTX mc MU) as DIN end.
    pose proof (din_bytes _ L inp (cs_next_in (ds_strm XL) - ds_w_size XL) (ds_w_size XL) DIN ltac:(lia) ltac:(lia) ltac:(lia)) as SRC.
    remember (arr_slice (arr_of_list inp) (cs_next_in (ds_strm XL) - ds_w_size XL) (ds_w_size XL)) as l eqn:El.
    assert (Ll : length (zb8 l) = Z.to_nat (ds_w_size XL)) by (rewrite zb8_length, El; apply arr_slice_length').
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      destruct (u8arr_split3 _ (dl_Aw L) _ (Z.to_nat 0) (Z.to_nat (ds_w_size XL)) Gwin ltac:(rewrite av8_length; lia)) as (O1 & O2 & O3); clear Gwin;
      rewrite !Z2Nat.id in O2 by lia; rewrite !Z2Nat.id in O3 by lia;
      assert (LO1 : length (firstn (Z.to_nat 0) (av8 (ds_window XL) 65536)) = Z.to_nat 0) by (rewrite length_firstn, av8_length; lia);
      assert (LO3 : length (skipn (Z.to_nat 0 + Z.to_nat (ds_w_size XL)) (av8 (ds_window XL) 65536)) = (Z.to_nat 65536 - (Z.to_nat 0 + Z.to_nat (ds_w_size XL)))%nat)
        by (rewrite length_skipn, av8_length; lia) end.
    replace (dl_NI L + cs_next_in (ds_strm XL) - ds_w_size XL) with (dl_NI L + (cs_next_in (ds_strm XL) - ds_w_size XL)) by lia.
    replace (dl_Aw L + 0) with (dl_Aw L) in O2 by lia. replace (dl_Aw L + 0 + ds_w_size XL) with (dl_Aw L + ds_w_size XL) in O3 by lia.
    zstep. call (memcpy_Z (dl_Aw L) (dl_NI L + (cs_next_in (ds_strm XL) - ds_w_size XL)) (ds_w_size XL)).
    1:{ exact SRC. } 1:{ exact Ll. } 1:{ exact O2. } 1:{ zsep. } 1:{ eassumption. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
    pose proof (u8arr_join2z _ (dl_Aw L) _ _ (ds_w_size XL) ltac:(rewrite Ll; lia) PC O3) as WIN.
    pose proof (av8_blit' (ds_window XL) (arr_of_list inp) 65536 0 (cs_next_in (ds_strm XL) - ds_w_size XL) (ds_w_size XL) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(pose proof (ln_win _ LENS); lia)) as EBL.
    cbn [Z.to_nat firstn app Nat.add] in EBL. unfold zb8 in WIN. rewrite El in WIN. rewrite <- Ll, zb8_length, El, arr_slice_length' in WIN.
    match type of EBL with ?a = _ => match type of WIN with u8arr _ _ _ ?b => replace b with a in WIN by reflexivity end end.
    rewrite EBL, arr_blit_upd, <- El in WIN. clear EBL.
    pose proof (arr_len_blit (ds_window XL) 0 (arr_of_list inp) (cs_next_in (ds_strm XL) - ds_w_size XL) (ds_w_size XL)) as LNW.
    rewrite arr_blit_upd, <- El, (ln_win _ LENS) in LNW.
    pose proof (av8_zlength (arr_upd (ds_window XL) 0 l) 65536 ltac:(lia)) as LWF.
    clear O1 O3 PC POST SRC LO1 LO3.
    zs. zs. zs. zs. zstep. zstep. rewrite (Z.mod_small (ds_w_size XL)) by lia. zs. zstep. name_mem mB.
    tr_groups MUf WMf.
    match type of K with TK11 _ _ _ _ _ _ _ _ _ _ _ _ (hw_st ?W) =>
    assert (INV' : STOINV L flush ai0 lz rest0 lo r me W mB);
    [ split; [split; [eexists _, _, _, _; exact ZS|]|];
      [ constructor; [eexists _, _, _, _, _; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| eexists _, _, _, _, _; unfold dsD_cells; dsred; close_cells GD
                     | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                     | unfold dwin; dsred; exact WIN| exact Gprev| exact Ghead| exact Gpend| | exact LAY];
        destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13];
        constructor; dsred; [exact l1| exact l2| exact l3| exact l4| exact l5| exact l6| exact l7| exact l8| exact l9| exact LNW| exact l11| exact l12| exact l13]
      | split; [eapply (dout_munch _ m' mB); [exact DOUT| exact RM| exact MUf| exact WMf| cbn [disjoint_from]; slia]|];
        split; [exact RM|]; split; [eexists; unfold sto_frame; exact FR|]; split; [exact STK|]; split; [exact MU|]; split; [exact WM| assumption] ]
    | ];
    clear ZS GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep WIN Gprev Ghead Gpend;
    zstep; br_cases K2;
    [   change (wz (ds_w_size XL)) with (wz (ds_strstart W));
      replace (wz (ds_strstart W)) with (wz (ds_strstart (hw_st W))) by (destruct (hw_st_facts W) as (E & _); rewrite E; reflexivity);
      unfold TK11 in K; eapply K;
      unfold hw_st; replace (ds_high_water W <? ds_strstart W) with false by (symmetry; apply Z.ltb_ge; exact K2); exact INV'
    | change (wz (ds_w_size XL)) with (wz (ds_strstart W));
      eapply (sto_hw1 Q lz W); [exact INV'| cbn [ds_strstart set_block_start set_insert set_strstart]; lia
        | cbn [ds_high_water set_block_start set_insert set_strstart set_window set_matches]; lia
        | cbn [ds_high_water ds_strstart set_block_start set_insert set_strstart set_window set_matches]; lia| exact K] ]
    end.
  -
    zstep. zs. zstep. zstep. zstep. rewrite (Z.mod_small used) by lia. zstep. br_cases K2.
    +
      rewrite (st_wupd_app XL used NU ltac:(lia) ltac:(lia)) in K. cbv zeta in K. rewrite ?win_set_strstart, ?strm_set_window, ?strm_set_strstart, INP in K.
      change (set_block_start (set_insert (set_strstart (set_window XL (arr_upd (ds_window XL) (ds_strstart XL) (arr_slice (arr_of_list inp) (cs_next_in (ds_strm XL) - used) used)))
                (ds_strstart XL + used)) (ins_add (ds_insert XL) used (ds_w_size XL))) (ds_strstart XL + used)) with (app_st inp XL used) in K.
      eapply (sto_append Q lz XL used); [exact INV| exact INP| exact WS| lia| lia| lia| lia| lia| lia| lia| exact K].
    +
      rewrite (st_wupd_sla XL used NU ltac:(lia) ltac:(lia)) in K. cbv zeta in K. rewrite ?win_set_strstart in K.
      match type of K with context [sl_fix ?x] => assert (HX2 : exists X2, X2 = x) by (eexists; reflexivity) end.
      destruct HX2 as [X2 EX2]. rewrite <- EX2 in K.
      pose proof (sl_fix_facts X2) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). pose proof (hw_sl_fix X2) as E8.
      assert (EIN2 : cs_input (ds_strm X2) = arr_of_list inp) by (rewrite EX2, strm_set_window, strm_set_strstart; exact INP).
      assert (EWS2 : ds_w_size X2 = ds_w_size XL) by (rewrite EX2; reflexivity).
      assert (ENI2 : cs_next_in (ds_strm X2) = cs_next_in (ds_strm XL)) by (rewrite EX2; reflexivity).
      assert (EM2 : ds_matches X2 = ds_matches XL) by (rewrite EX2; reflexivity).
      assert (ES2 : ds_strstart X2 = ds_strstart XL - ds_w_size XL) by (rewrite EX2; reflexivity).
      assert (EI2 : ds_insert X2 = ds_insert XL) by (rewrite EX2; reflexivity).
      assert (EHW2 : ds_high_water X2 = ds_high_water XL) by (rewrite EX2; reflexivity).
      assert (K' : TK11 L flush ai0 lz rest0 lo r F fc me Q Z_STO_LASTT (hw_st (app_st inp (sl_fix X2) used))).
      { unfold app_st. rewrite E3, E5, EWS2. rewrite E3, EIN2 in K. exact K. }
      clear K.
      open_win Gwin.
      zstep. zs. zs. zstep. zstep. zstep. rewrite (Z.mod_small (ds_strstart XL - ds_w_size XL)) by lia.

      pose proof (u8arr_sub_bytes _ (dl_Aw L) _ (Z.to_nat (ds_w_size XL)) (Z.to_nat (ds_strstart XL - ds_w_size XL)) Gwin ltac:(rewrite av8_length; lia)) as SRC.
      rewrite av8_slice in SRC by lia. rewrite Z2Nat.id in SRC by lia.
      assert (LSRC : length (map (Z_to_bv 8) (arr_slice (ds_window XL) (ds_w_size XL) (ds_strstart XL - ds_w_size XL))) = Z.to_nat (ds_strstart XL - ds_w_size XL))
        by (rewrite length_map; apply arr_slice_length').
      destruct (u8arr_split3 _ (dl_Aw L) _ (Z.to_nat 0) (Z.to_nat (ds_strstart XL - ds_w_size XL)) Gwin ltac:(rewrite av8_length; lia)) as (O1 & O2 & O3). clear Gwin.
      rewrite !Z2Nat.id in O2 by lia. rewrite !Z2Nat.id in O3 by lia.
      replace (dl_Aw L + 0) with (dl_Aw L) in O2 by lia. replace (dl_Aw L + 0 + (ds_strstart XL - ds_w_size XL)) with (dl_Aw L + (ds_strstart XL - ds_w_size XL)) in O3 by lia.
      zstep. call (memcpy_Z (dl_Aw L) (dl_Aw L + ds_w_size XL) (ds_strstart XL - ds_w_size XL)).
      1:{ exact SRC. } 1:{ exact LSRC. } 1:{ exact O2. } 1:{ lia. } 1:{ eassumption. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
      pose proof (u8arr_join2z _ (dl_Aw L) _ _ (ds_strstart XL - ds_w_size XL) ltac:(rewrite LSRC; lia) PC O3) as WIN.
      pose proof (av8_blit' (ds_window XL) (ds_window XL) 65536 0 (ds_w_size XL) (ds_strstart XL - ds_w_size XL) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(pose proof (ln_win _ LENS); lia)) as EBL.
      cbn [Z.to_nat firstn app Nat.add] in EBL. rewrite <- LSRC, length_map, arr_slice_length' in WIN.
      match type of EBL with ?a = _ => match type of WIN with u8arr _ _ _ ?b => replace b with a in WIN by reflexivity end end.
      rewrite EBL, arr_blit_upd in WIN. clear EBL.
      pose proof (arr_len_blit (ds_window XL) 0 (ds_window XL) (ds_w_size XL) (ds_strstart XL - ds_w_size XL)) as LNW.
      rewrite arr_blit_upd, (ln_win _ LENS) in LNW.
      pose proof (av8_zlength (arr_upd (ds_window XL) 0 (arr_slice (ds_window XL) (ds_w_size XL) (ds_strstart XL - ds_w_size XL))) 65536 ltac:(lia)) as LWF.
      try clear O1. clear O3 PC POST SRC LSRC.

      let slide_leaf := fun mv iv => (
  assert (EWd : set_insert (set_matches X2 mv) iv = sl_fix X2)
    by (rewrite (sl_fix_dec X2), EM2, ES2, EI2;
        repeat (match goal with |- context [if ?c then _ else _] =>
                  first [replace c with true by (symmetry; apply Z.ltb_lt; lia) | replace c with false by (symmetry; apply Z.ltb_ge; lia)]; cbv iota end);
        reflexivity);
  replace (wz (ds_strstart XL - ds_w_size XL)) with (wz (ds_strstart (sl_fix X2))) by (rewrite E1, ES2; reflexivity);
  eapply (sto_append Q lz (sl_fix X2) used);
  [ rewrite <- EWd, EX2;
    split; [split; [eexists _, _, _, _; exact ZS|]|];
    [ constructor; [eexists _, _, _, _, _; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| eexists _, _, _, _, _; unfold dsD_cells; dsred; close_cells GD
                   | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                   | unfold dwin; dsred; exact WIN| exact Gprev| exact Ghead| exact Gpend| | exact LAY];
      destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13];
      constructor; dsred; [exact l1| exact l2| exact l3| exact l4| exact l5| exact l6| exact l7| exact l8| exact l9| exact LNW| exact l11| exact l12| exact l13]
    | split; [eapply (dout_munch _ m' mB); [exact DOUT| exact RM| exact MUf| exact WMf| cbn [disjoint_from]; slia]|];
      split; [exact RM|]; split; [eexists; unfold sto_frame; exact FR|]; split; [exact STK|]; split; [exact MU|]; split; [exact WM| assumption] ]
  | rewrite E3; exact EIN2 | rewrite E5, EWS2; exact WS | lia | rewrite E1, ES2; lia | rewrite E1, ES2; lia
  | rewrite E4, ES2, EI2; destruct (Z.ltb_spec (ds_strstart XL - ds_w_size XL) (ds_insert XL)); lia
  | rewrite E8, EHW2; lia | rewrite E3, ENI2; lia | rewrite E3, ENI2; lia | exact K' ]) in
      zs; zstep; zstep; br_cases Km;
      [ | zs; zs ];
      (zs; zs; zstep; br_cases Ki; [ | zs ]); name_mem mB; tr_groups MUf WMf;
      [ slide_leaf (ds_matches XL) (ds_insert XL)
      | slide_leaf (ds_matches XL) (ds_strstart XL - ds_w_size XL)
      | slide_leaf (ds_matches XL + 1) (ds_insert XL)
      | slide_leaf (ds_matches XL + 1) (ds_strstart XL - ds_w_size XL) ].
Qed.
Lemma sto_used : TK10 L flush ai0 lz rest0 lo r F fc me Q Z_STO_BREAK (dl_S L) XL.
Proof using K RUNI RAIL RAI0 INP WS HVL used CTX inp.
  unfold TK10. intros until m'. intros INV.
  pose proof INV as (DR & DOUT & RM & (j0 & FR) & STK & MU & WM & MI). unfold sto_frame in FR. unfold Z_STO_BREAK, stoR, stoR7.
  pose proof (tc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_STORED_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. open_zs ZS.
  zs. zstep. zstep. br_cases K0.
  - eapply used_ne; [exact INV| subst used; lia].
  - eapply used_eq; [exact INV| subst used; lia].
Qed.

Lemma sto_used2 : TK10 L flush ai0 lz rest0 lo r F fc me Q Z_STO_BREAK2 (dl_S L) XL.
Proof using K RUNI RAIL RAI0 INP WS HVL used CTX inp.
  unfold TK10. intros until m'. intros INV.
  pose proof INV as (DR & DOUT & RM & (j0 & FR) & STK & MU & WM & MI). unfold sto_frame in FR. unfold Z_STO_BREAK2, stoR, stoR7.
  pose proof (tc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_STORED_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. open_zs ZS.
  zs. zs. zstep. zstep. br_cases K0.
  - eapply used_eq; [exact INV| subst used; lia].
  - eapply used_ne; [exact INV| subst used; lia].
Qed.
End USED.
