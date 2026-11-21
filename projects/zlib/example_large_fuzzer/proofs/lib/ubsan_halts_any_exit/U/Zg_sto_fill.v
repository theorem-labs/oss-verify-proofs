(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import InitMem Z_kit Zg_sto_model.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_kit Z_tr_kit Z_fw_slide Z_ukit
     Zg_adler32_iface Zg_readbuf Zg_defl_iface Zg_sto_ole Zg_sto_kit Zg_sto_head Zg_sto_used.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk SendModel FillWinModel
     RefDeflStored1 RefDeflStored2 RefDeflStored4 RefDeflStored5 RefDeflStored6 RefDeflStored7 RefDeflStored8 RefDeflStored9 RefDeflSafeS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition Z_STO_RD2 : Z := 0x18c20.
Definition Z_STO_LASTT2 : Z := 0x18b4c.

Lemma or4_eq : forall flush, 0 <= flush <= 5 -> (Z.lor flush 4 = 4 <-> (flush = Z_NO_FLUSH \/ flush = Z_FINISH)).
Proof.
  intros flush H. unfold Z_NO_FLUSH, Z_FINISH.
  assert (C : flush = 0 \/ flush = 1 \/ flush = 2 \/ flush = 3 \/ flush = 4 \/ flush = 5) by lia.
  destruct C as [-> |[-> |[-> |[-> |[-> | ->]]]]]; (split; [intros E; cbv in E; first [lia | discriminate E] | intros [E|E]; try lia; reflexivity]).
Qed.

Lemma lor4_range : forall flush, 0 <= flush <= 5 -> 0 <= Z.lor flush 4 < 8.
Proof.
  intros flush H. assert (C : flush = 0 \/ flush = 1 \/ flush = 2 \/ flush = 3 \/ flush = 4 \/ flush = 5) by lia.
  destruct C as [-> |[-> |[-> |[-> |[-> | ->]]]]]; cbv; split; try (intros E; discriminate E); reflexivity.
Qed.

Lemma win_set_block_start : forall s v, ds_window (set_block_start s v) = ds_window s. Proof. reflexivity. Qed.

Section FILL.
Variables (L : dlay) (flush ai0 : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : sto_ctx L inp rest0 lo r me.
Hypothesis HFL : 0 <= flush <= 5.

Definition KFILL (Q : machine_state -> Prop) (X : deflate_state) : Prop := TK11 L flush ai0 1 rest0 lo r F fc me Q Z_STO_FILL X.

Definition KRD2 (Q : machine_state -> Prop) (X : deflate_state) (have : Z) : Prop :=
  forall (y1 y5 y6 y7 y9 y10 y12 y13 y14 y15 y16 y17 y20 y28 y29 y30 y31 : word) (m' : mem),
    STOINV L flush rest0 lo r me X m' ->
    evt usegs Q (MS (stoR L flush ai0 1 r y1 y5 y6 y7 y9 y10 (wz (ds_strstart X)) y12 y13 y14 y15 y16 y17 (wz have) y20 y28 y29 y30 y31)
                    F (wz Z_STO_RD2) fc None m' (seg_rom usegs)).

Lemma sto_lastt2 : forall (Q : machine_state -> Prop) (lz last : Z) (X2 : deflate_state),
  lz = 1 - last -> 0 <= last <= 1 ->
  0 <= ds_strstart X2 < 2^32 -> 0 <= cs_avail_in (ds_strm X2) < 2^31 -> 0 <= ds_block_start X2 < 2^63 ->
  (last = 1 -> TK10 L flush ai0 lz rest0 lo r F fc me Q Z_STO_EPIBU 3 X2) ->
  (last = 0 -> flush <> Z_NO_FLUSH -> flush <> Z_FINISH -> cs_avail_in (ds_strm X2) = 0 -> ds_strstart X2 = ds_block_start X2 ->
     TK10 L flush ai0 lz rest0 lo r F fc me Q Z_STO_EPI 1 X2) ->
  (last = 0 -> (negb (flush =? Z_NO_FLUSH) && negb (flush =? Z_FINISH) && (cs_avail_in (ds_strm X2) =? 0) && (ds_strstart X2 =? ds_block_start X2)) = false ->
     KFILL Q X2) ->
  TK11 L flush ai0 lz rest0 lo r F fc me Q Z_STO_LASTT2 X2.
Proof using HFL CTX inp.
  intros Q lz last X2 Elz RL RSTR RAI RBS KFD KBD KF. unfold TK11. intros until m'. intros INV.
  pose proof INV as (DR & DOUT & RM & FR & STK & MU & WM & MI). unfold sto_frame in FR. unfold Z_STO_LASTT2, stoR.
  pose proof (tc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_STORED_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY.
  pose proof (lo_S _ LAY) as BKS. unfold blk_ok in BKS.
  open_DST ST. open_A GA. open_zs ZS. subst lz.
  zstep. br_cases K0.
  { zstep. zstep. unfold TK10 in KFD. eapply (KFD ltac:(lia)). exact INV. }
  assert (Hl0 : last = 0) by lia. rewrite Hl0. change (1 - 0) with 1.
  zs. zstep. zstep.
  destruct (or4_eq flush HFL) as [OR1 OR2]. pose proof (lor4_range flush HFL) as RLOR.
  zstep. br_cases K1; rewrite ?unsigned_lit in K1 by lia.
  {
    unfold KFILL, TK11 in KF. eapply KF; [exact Hl0| |exact INV].
    destruct (OR1 K1) as [E|E]; rewrite E; reflexivity. }
  assert (NF : flush <> Z_NO_FLUSH /\ flush <> Z_FINISH).
  { split; intros E; apply K1; apply OR2; [left|right]; exact E. }
  zs. gF. zstep. al8 (dl_S L). gF. zs. zstep. br_cases K2.
  {
    unfold KFILL, TK11 in KF. eapply KF; [exact Hl0| |exact INV].
    replace (cs_avail_in (ds_strm X2) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Bool.andb_false_r. reflexivity. }
  zs. zstep. br_cases K3.
  {
    unfold KFILL, TK11 in KF. eapply KF; [exact Hl0| |exact INV].
    replace (ds_strstart X2 =? ds_block_start X2) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Bool.andb_false_r. reflexivity. }
  zstep. zstep. unfold TK10 in KBD. rewrite Hl0 in KBD. change (1 - 0) with 1 in KBD. destruct NF as [NF1 NF2].
  eapply (KBD eq_refl NF1 NF2 ltac:(lia) ltac:(lia)). exact INV.
Qed.

Lemma sto_lastt : forall (Q : machine_state -> Prop) (lz last : Z) (Y : deflate_state),
  lz = 1 - last -> 0 <= last <= 1 ->
  0 <= ds_strstart Y < 2^32 -> 0 <= ds_high_water Y < 2^64 -> 0 <= cs_avail_in (ds_strm Y) < 2^31 -> 0 <= ds_block_start Y < 2^63 ->
  (last = 1 -> TK10 L flush ai0 lz rest0 lo r F fc me Q Z_STO_EPIBU 3 (hw_st Y)) ->
  (last = 0 -> flush <> Z_NO_FLUSH -> flush <> Z_FINISH -> cs_avail_in (ds_strm (hw_st Y)) = 0 -> ds_strstart (hw_st Y) = ds_block_start (hw_st Y) ->
     TK10 L flush ai0 lz rest0 lo r F fc me Q Z_STO_EPI 1 (hw_st Y)) ->
  (last = 0 -> (negb (flush =? Z_NO_FLUSH) && negb (flush =? Z_FINISH) && (cs_avail_in (ds_strm (hw_st Y)) =? 0) && (ds_strstart (hw_st Y) =? ds_block_start (hw_st Y))) = false ->
     KFILL Q (hw_st Y)) ->
  TK L flush ai0 lz rest0 lo r F fc me Q Z_STO_LASTT Y.
Proof using HFL CTX inp.
  intros Q lz last Y Elz RL RSTR RHW RAI RBS KFD KBD KF. unfold TK. intros until m'. intros INV.
  pose proof INV as (DR & DOUT & RM & FR & STK & MU & WM & MI). unfold sto_frame in FR. unfold Z_STO_LASTT, stoR.
  pose proof (tc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_STORED_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY.
  pose proof (tc_bel _ _ _ _ _ _ CTX) as BEL. below_open BEL. pose proof (tc_io _ _ _ _ _ _ CTX) as IO. pose proof IO as IO'. io_open IO'.
  pose proof (hw_st_facts Y) as (Hs & Hb & Hst & Hws & Hw).
  open_DST ST. open_A GA. open_D GD. unfold sto_W, slow_W in MU.
  pose proof (munch_refl [(dl_As L + 5881, dl_As L + 5968)] m') as MUf. pose proof (wmono_refl usegs m') as WMf.
  zs. zs. zstep. br_cases K1.
  -
    replace (wz (ds_strstart Y)) with (wz (ds_strstart (hw_st Y))) by (rewrite Hs; reflexivity).
    eapply (sto_lastt2 Q lz last (hw_st Y) Elz RL); [rewrite Hs; exact RSTR| rewrite Hst; exact RAI| rewrite Hb; exact RBS| exact KFD| exact KBD| exact KF|].
    unfold hw_st. replace (ds_high_water Y <? ds_strstart Y) with false by (symmetry; apply Z.ltb_ge; exact K1).
    split; [split; [exact ZS|]|].
    { constructor; [eexists _, _, _, _, _; exact GA| exact GB| exact GC| eexists _, _, _, _, _; exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                   | exact Gwin| exact Gprev| exact Ghead| exact Gpend| exact LENS| exact LAY]. }
    split; [exact DOUT|]. split; [exact RM|]. split; [unfold sto_frame; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| assumption].
  - zs. name_mem mB.
    replace (wz (ds_strstart Y)) with (wz (ds_strstart (hw_st Y))) by (rewrite Hs; reflexivity).
    eapply (sto_lastt2 Q lz last (hw_st Y) Elz RL); [rewrite Hs; exact RSTR| rewrite Hst; exact RAI| rewrite Hb; exact RBS| exact KFD| exact KBD| exact KF|].
    unfold hw_st. replace (ds_high_water Y <? ds_strstart Y) with true by (symmetry; apply Z.ltb_lt; exact K1).
    tr_groups MUf WMf.
    split; [split; [first [exact ZS| eapply dzs_munch; [exact ZS| exact MUf| exact WMf| cbn [disjoint_from]; slia]]|]|].
    { constructor; [eexists _, _, _, _, _; exact GA| exact GB| exact GC| eexists _, _, _, _, _; unfold dsD_cells; dsred; close_cells GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                   | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS| exact LAY]. }
    split; [first [exact DOUT| eapply (dout_munch _ m' mB); [exact DOUT| exact RM| exact MUf| exact WMf| cbn [disjoint_from]; slia]]|].
    split; [exact RM|]. split; [unfold sto_frame; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| assumption].
Qed.

Variables (Q : machine_state -> Prop) (X2 : deflate_state).
Let have := ds_window_size X2 - ds_strstart X2.
Hypothesis HV2 : so_inv X2.
Hypothesis WS : ds_w_size X2 = 32768.
Hypothesis RAI : 0 <= cs_avail_in (ds_strm X2) < 2^31.
Hypothesis K : KRD2 Q (fst (st_slide3 X2 have)) (snd (st_slide3 X2 have)).

Lemma sto_slide2 : KFILL Q X2.
Proof using K RAI WS HV2 have CTX inp.
  unfold KFILL, TK11. intros until m'. intros INV.
  pose proof INV as (DR & DOUT & RM & FR & STK & MU & WM & MI). unfold sto_frame in FR. unfold Z_STO_FILL, stoR.
  pose proof (tc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_STORED_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY.
  pose proof (tc_bel _ _ _ _ _ _ CTX) as BEL. pose proof BEL as BEL'. below_open BEL'. pose proof (tc_io _ _ _ _ _ _ CTX) as IO. pose proof IO as IO'. io_open IO'.
  pose proof (vi_str _ HV2) as Vstr. pose proof (vi_bs _ HV2) as Vbs. pose proof (vi_wsz _ HV2) as Vwsz. pose proof (vi_ins _ HV2) as Vins.
  pose proof (vi_mat _ HV2) as Vmat. rewrite WS in Vstr, Vwsz, Vins.
  pose proof (lo_S _ LAY) as BKS. unfold blk_ok in BKS.
  open_DST ST. open_A GA. open_D GD. open_zs ZS. unfold sto_W, slow_W in MU. unfold KRD2 in K.
  pose proof (munch_refl [(dl_Aw L, dl_Aw L + 65536); (dl_As L, dl_As L + 212); (dl_As L + 5881, dl_As L + 5968)] m') as MUf.
  pose proof (wmono_refl usegs m') as WMf.
  zs. gF. zstep. al8 (dl_S L). gF. rd_lo4 GA 104%nat. zs. zs. zs. fold have. zstep. br_cases K1.
  {
    rewrite (st_slide3_false X2 have) in K by (apply Bool.andb_false_iff; left; apply Z.ltb_ge; exact K1). rewrite fst_pr, snd_pr in K.
    eapply K. exact INV. }
  zs. zs. zstep. br_cases K2.
  {
    rewrite (st_slide3_false X2 have) in K by (apply Bool.andb_false_iff; right; apply Z.leb_gt; exact K2). rewrite fst_pr, snd_pr in K.
    eapply K. exact INV. }
  assert (EC : (have <? cs_avail_in (ds_strm X2)) && (ds_w_size X2 <=? ds_block_start X2) = true).
  { apply Bool.andb_true_iff. split; [apply Z.ltb_lt; exact K1| apply Z.leb_le; exact K2]. }
  rewrite (st_slide3_true X2 have EC) in K. cbv zeta in K. rewrite fst_pr, snd_pr, ?win_set_block_start, ?win_set_strstart in K.
  rewrite (wrap32_mod (have + ds_w_size X2)), (Z.mod_small (have + ds_w_size X2)) in K by lia.
  match type of K with context [sl_fix ?x] => assert (HX : exists X, X = x) by (eexists; reflexivity) end.
  destruct HX as [X EX]. rewrite <- EX in K.
  pose proof (sl_fix_facts X) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). pose proof (hw_sl_fix X) as E8.
  assert (EM2 : ds_matches X = ds_matches X2) by (rewrite EX; reflexivity).
  assert (ES2 : ds_strstart X = ds_strstart X2 - ds_w_size X2) by (rewrite EX; reflexivity).
  assert (EI2 : ds_insert X = ds_insert X2) by (rewrite EX; reflexivity).
  open_win Gwin.
  zs. zstep. zs. zstep. zs. zs. gF. zstep. zstep. zstep. gX. zstep. zstep. rewrite (Z.mod_small (ds_strstart X2 - ds_w_size X2)) by lia.
  pose proof (u8arr_sub_bytes _ (dl_Aw L) _ (Z.to_nat (ds_w_size X2)) (Z.to_nat (ds_strstart X2 - ds_w_size X2)) Gwin ltac:(rewrite av8_length; lia)) as SRC.
  rewrite av8_slice in SRC by lia. rewrite Z2Nat.id in SRC by lia.
  assert (LSRC : length (map (Z_to_bv 8) (arr_slice (ds_window X2) (ds_w_size X2) (ds_strstart X2 - ds_w_size X2))) = Z.to_nat (ds_strstart X2 - ds_w_size X2))
    by (rewrite length_map; apply arr_slice_length').
  destruct (u8arr_split3 _ (dl_Aw L) _ (Z.to_nat 0) (Z.to_nat (ds_strstart X2 - ds_w_size X2)) Gwin ltac:(rewrite av8_length; lia)) as (O1 & O2 & O3). clear Gwin.
  rewrite !Z2Nat.id in O2 by lia. rewrite !Z2Nat.id in O3 by lia.
  replace (dl_Aw L + 0) with (dl_Aw L) in O2 by lia. replace (dl_Aw L + 0 + (ds_strstart X2 - ds_w_size X2)) with (dl_Aw L + (ds_strstart X2 - ds_w_size X2)) in O3 by lia.
  zstep. call (memcpy_Z (dl_Aw L) (dl_Aw L + ds_w_size X2) (ds_strstart X2 - ds_w_size X2)).
  1:{ exact SRC. } 1:{ exact LSRC. } 1:{ exact O2. } 1:{ lia. } 1:{ eassumption. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
  pose proof (u8arr_join2z _ (dl_Aw L) _ _ (ds_strstart X2 - ds_w_size X2) ltac:(rewrite LSRC; lia) PC O3) as WIN.
  pose proof (av8_blit' (ds_window X2) (ds_window X2) 65536 0 (ds_w_size X2) (ds_strstart X2 - ds_w_size X2) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(pose proof (ln_win _ LENS); lia)) as EBL.
  cbn [Z.to_nat firstn app Nat.add] in EBL. rewrite <- LSRC, length_map, arr_slice_length' in WIN.
  match type of EBL with ?a = _ => match type of WIN with u8arr _ _ _ ?b => replace b with a in WIN by reflexivity end end.
  rewrite EBL, arr_blit_upd in WIN. clear EBL.
  pose proof (arr_len_blit (ds_window X2) 0 (ds_window X2) (ds_w_size X2) (ds_strstart X2 - ds_w_size X2)) as LNW.
  rewrite arr_blit_upd, (ln_win _ LENS) in LNW.
  pose proof (av8_zlength (arr_upd (ds_window X2) 0 (arr_slice (ds_window X2) (ds_w_size X2) (ds_strstart X2 - ds_w_size X2))) 65536 ltac:(lia)) as LWF.
  try clear O1. clear O3 PC POST SRC LSRC.
  let leaf := fun mv iv => (
    assert (EWd : set_insert (set_matches X mv) iv = sl_fix X)
      by (rewrite (sl_fix_dec X), EM2, ES2, EI2;
          repeat (match goal with |- context [if ?c then _ else _] =>
                    first [replace c with true by (symmetry; apply Z.ltb_lt; lia) | replace c with false by (symmetry; apply Z.ltb_ge; lia)]; cbv iota end);
          reflexivity);
    replace (wz (ds_strstart X2 - ds_w_size X2)) with (wz (ds_strstart (sl_fix X))) by (rewrite E1, ES2; reflexivity);
    replace (wz (ds_w_size X2 + have)) with (wz (have + ds_w_size X2)) by (f_equal; lia);
    eapply K; rewrite <- EWd, EX;
    split; [split; [eexists _, _, _, _; exact ZS|]|];
    [ constructor; [eexists _, _, _, _, _; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| eexists _, _, _, _, _; unfold dsD_cells; dsred; close_cells GD
                   | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                   | unfold dwin; dsred; exact WIN| exact Gprev| exact Ghead| exact Gpend| | exact LAY];
      destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13];
      constructor; dsred; [exact l1| exact l2| exact l3| exact l4| exact l5| exact l6| exact l7| exact l8| exact l9| exact LNW| exact l11| exact l12| exact l13]
    | split; [eapply (dout_munch _ m' mB); [exact DOUT| exact RM| exact MUf| exact WMf| cbn [disjoint_from]; slia]|];
      split; [exact RM|]; split; [unfold sto_frame; exact FR|]; split; [exact STK|]; split; [exact MU|]; split; [exact WM| assumption] ]) in
  zs; zstep; zstep; br_cases Km;
  [ | zstep; zs ];
  (zs; zs; zs; zs; zstep; br_cases Ki; [ | zs ]); name_mem mB; tr_groups MUf WMf;
  [ leaf (ds_matches X2) (ds_insert X2)
  | leaf (ds_matches X2) (ds_strstart X2 - ds_w_size X2)
  | leaf (ds_matches X2 + 1) (ds_insert X2)
  | leaf (ds_matches X2 + 1) (ds_strstart X2 - ds_w_size X2) ].
Qed.
End FILL.
