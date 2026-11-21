(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees HuffTree HuffHeap HuffBuild HuffBuild2 HuffGen HuffGen2 HuffPen HuffSpec DeflateInvKeep.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import FillWinModel TreeModel BuildTreeModel GenBitlenModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma cty_bt : forall X t FC DL HP HL HM DP BC OL SL MC,
  cty (bt_upd X t FC DL HP HL HM DP BC OL SL MC) -> u16a FC /\ u16a DL /\ u8a DP /\ u16a BC.
Proof.
  intros X t FC DL HP HL HM DP BC OL SL MC C.
  pose proof (cty_tree_fc _ t C) as A. pose proof (cty_tree_dl _ t C) as B.
  pose proof (ct_dep _ C) as D. pose proof (ct_blc _ C) as E.
  rewrite bt_tree_fc in A. rewrite bt_tree_dl in B. rewrite bt_depth in D. rewrite bt_bl_count in E. auto.
Qed.


Section GB.
Variables (s : deflate_state) (t : tree_id) (FC0 : arr) (BC : arr) (OL SL : Z).
Variables (FC DL HP DP : arr) (sub : Z -> htree).

Local Set Warnings "-notation-for-abbreviation".
Local Notation elems := (sd_elems t).
Local Notation UPl := (UP FC0 t).
Local Notation uu := (u t FC0).
Local Notation MCv := (MCP FC0 t).
Local Notation ML := (sd_max_length t).
Local Notation hm := (hm t FC0).
Local Notation HP7 := (HP7 t FC0 HP).
Local Notation leafp := (leafp t FC0 HP).
Local Notation RS := (RS t FC0).
Local Notation ind := (ind t FC0 HP).
Local Notation X6 DLc BCc OLc SLc := (bt_upd s t FC DLc HP7 1 (hm - 1) DP BCc OLc SLc MCv).

Hypothesis INV : Inv4 t FC0 (uu - 1) FC DL HP 1 hm DP sub.

Lemma gb1_ok_intro : forall f h DLc BCc OLc SLc ovc, hm <= h <= 573 -> 0 <= OL < 2 ^ 64 -> 0 <= SL < 2 ^ 64 ->
  GI t FC0 OL SL FC DL HP h DLc BCc OLc SLc ovc -> gb1_ok t MCv f (X6 DLc BCc OLc SLc) h ovc.
Proof.
  induction f as [|f IH]; intros h DLc BCc OLc SLc ovc Hh OLr SLr G; cbn [gb1_ok]; [exact I|].
  unfold HEAP_SIZE. destruct (Z.ltb_spec h 573); [|exact I].
  pose proof (u_ge2 t FC0) as UG. pose proof (elems_tsize t) as ET.
  split.
  - unfold Dad, heap_get. autorewrite with btupd.
    rewrite (g_todo _ _ _ _ _ _ _ _ _ _ _ _ _ G h) by lia.
    destruct (parent_pos t FC0 FC DL HP DP sub INV h ltac:(lia)) as (hp & Hhp & Ep). rewrite <- Ep.
    pose proof (ids_range t FC0 FC DL HP DP sub INV hp ltac:(lia)) as [R _]. lia.
  - destruct (gb_step s t FC0 OL SL FC DL HP DP sub INV OLr SLr h DLc BCc OLc SLc ovc ltac:(lia) G) as (DL1 & BC1 & OL1 & SL1 & ov1 & E1 & G1).
    rewrite E1. apply IH; [lia| exact OLr| exact SLr| exact G1].
Qed.

Lemma gb2_ok_intro : forall f DLx OLx SLx BCx rex, LI t FC0 BCx rex -> 1 <= rex ->
  gb2_ok ML f (X6 DLx BCx OLx SLx) (2 * rex).
Proof.
  induction f as [|f IH]; intros DLx OLx SLx BCx rex L Hrex; cbn [gb2_ok]; [exact I|].
  rewrite afind_flat.
  pose proof (trip_facts s t FC0 FC DL HP DP sub INV BCx rex L Hrex) as TF. cbv zeta in TF. destruct TF as (Hr & _ & _ & _ & _ & L').
  split; [lia|].
  destruct (Z.ltb_spec 0 (2 * rex - 2)); [|exact I].
  unfold bl_count_get, bl_count_set. autorewrite with btupd.
  replace (2 * rex - 2) with (2 * (rex - 1)) by lia.
  match goal with |- gb2_ok _ _ (bt_upd _ _ _ _ _ _ _ _ ?B _ _ _) _ => replace B with (atrip ML BCx) end.
  - apply IH; [exact L'| lia].
  - unfold atrip, bl_adj. reflexivity.
Qed.

Lemma gb3i_ok_intro : forall f bits n h DLx BCx OLx SLx, hm <= h <= 573 -> 0 <= n <= RS ind hm h ->
  gb3i_ok t MCv f (X6 DLx BCx OLx SLx) bits n h.
Proof.
  induction f as [|f IH]; intros bits n h DLx BCx OLx SLx Hh Hn; cbn [gb3i_ok]; [exact I|].
  destruct (Z.eqb_spec n 0); cbn [negb]; [exact I|].
  pose proof (u_ge2 t FC0) as UG. pose proof (elems_tsize t) as ET.
  assert (Hgt : hm < h).
  { destruct (Z.eq_dec h hm) as [E|]; [|lia]. rewrite E in Hn. rewrite RS_nil in Hn. lia. }
  split; [unfold HuffGen.hm in *; lia|].
  unfold heap_get at 1. autorewrite with btupd.
  pose proof (ids_range t FC0 FC DL HP DP sub INV (h - 1) ltac:(lia)) as [R _].
  split; [lia|].
  pose proof (GB3i_flat t MCv s FC DLx HP7 1 (hm - 1) DP BCx OLx SLx bits n h) as E. cbv zeta in E. rewrite E. clear E.
  pose proof (RS_snoc t FC0 ind hm (h - 1) ltac:(lia)) as RSS. replace (h - 1 + 1) with h in RSS by lia.
  unfold HuffGen2.ind in RSS at 3. unfold HuffGen.leafp in RSS. revert RSS.
  destruct (Z.ltb_spec MCv (arr_get HP7 (h - 1))); cbn [negb]; intros RSS.
  - apply IH; lia.
  - destruct (arr_get DLx (arr_get HP7 (h - 1)) =? bits); apply IH; lia.
Qed.

Lemma gb3_ok_intro : forall f bits h DLx OLx BCf SLx, LI t FC0 BCf 0 -> 0 <= bits <= ML -> hm <= h <= 573 ->
  arr_len DLx = tsize t -> 0 <= OLx < 2 ^ 64 ->
  RS ind h 573 = isum (arr_get BCf) ML - isum (arr_get BCf) bits ->
  gb3_ok t MCv f (X6 DLx BCf OLx SLx) bits h.
Proof.
  induction f as [|f IH]; intros bits h DLx OLx BCf SLx LIf Hbits Hh LEN HOLx DONE; cbn [gb3_ok]; [exact I|].
  destruct (Z.eqb_spec bits 0) as [->|NZ]; cbn [negb]; [exact I|].
  unfold bl_count_get. autorewrite with btupd.
  pose proof LIf as [LBC NN OUT CNT KK _ _]. pose proof (ML_range t FC0 FC DL HP DP sub INV) as MR. pose proof (u_ge2 t FC0) as UU.
  pose proof (leaves_count t FC0 FC DL HP DP sub INV) as LC.
  assert (REM : RS ind hm h = isum (arr_get BCf) bits).
  { pose proof (RS_app t FC0 ind hm h 573) as A. unfold HuffGen2.RS in A, DONE |- *. rewrite SUM_hm in *. unfold cntB in CNT. lia. }
  assert (Bb : 0 <= arr_get BCf bits <= isum (arr_get BCf) bits).
  { split; [apply NN; lia|]. apply isum_le1; [lia| lia| intros; apply NN; lia]. }
  split; [apply gb3i_ok_intro; lia|].
  destruct (gb_loop3i s t FC0 FC DL HP DP sub INV BCf SLx 574 bits (arr_get BCf bits) h DLx OLx ltac:(lia) ltac:(lia) ltac:(unfold HuffGen.hm in *; lia) LEN ltac:(lia) HOLx)
    as (h' & DLx' & OLx' & E1 & R1 & C1 & _ & _ & L1 & O1 & _).
  rewrite E1. apply IH; [exact LIf| lia| lia| exact L1| exact O1|].
  rewrite <- (RS_app t FC0 ind h' h 573), C1, DONE.
  pose proof (isum_snoc (arr_get BCf) (bits - 1) ltac:(lia)) as IS. replace (bits - 1 + 1) with bits in IS by lia. lia.
Qed.
End GB.

Section BT.
Variables (X : deflate_state) (t : tree_id).
Hypothesis PRE : bt_pre X t.
Hypothesis CT : cty X.

Theorem bt_safe_intro : bt_safe X t.
Proof.
  destruct PRE as [TL Fnn FB OLr SLr].
  pose proof (tree_lens_fc X t TL) as LFC. pose proof (tree_lens_dl X t TL) as LDL.
  assert (LHP : arr_len (ds_heap X) = 573) by (unfold tree_lens in TL; tauto).
  assert (LDP : arr_len (ds_depth X) = 573) by (unfold tree_lens in TL; tauto).
  assert (LBC : arr_len (ds_bl_count X) = 16) by (unfold tree_lens in TL; tauto).
  pose proof (elems_tsize t) as ET.
  pose proof (pads_facts t (tree_fc X t)) as (NDU & RNGU & U2 & PD & _).
  pose proof (UP_len_elems t (tree_fc X t)) as UE.
  set (FC0 := tree_fc X t) in *.
  unfold bt_safe. cbv zeta.
  split. { intros i Hi. apply (cty_tree_fc _ t CT). fold FC0. rewrite LFC. exact Hi. }
  split; [exact OLr|]. split; [exact SLr|].
  assert (E0 : set_heap_max (set_heap_len X 0) HEAP_SIZE
               = bt_upd X t FC0 (tree_dl X t) (ds_heap X) 0 573 (ds_depth X) (ds_bl_count X) (ds_opt_len X) (ds_static_len X) (max_code X t)).
  { rewrite <- (bt_upd_self X t) at 1. autorewrite with btupd. reflexivity. }
  assert (C0 : cty (bt_upd X t FC0 (tree_dl X t) (ds_heap X) 0 573 (ds_depth X) (ds_bl_count X) (ds_opt_len X) (ds_static_len X) (max_code X t))).
  { rewrite <- E0. apply cty_set_heap_max. apply cty_set_heap_len. exact CT. }
  rewrite E0. clear E0.
  destruct (loop1_flat X t FC0 573 (ds_bl_count X) (ds_opt_len X) (ds_static_len X) (max_code X t)
              (Z.to_nat (sd_elems t)) 0 (tree_dl X t) (ds_heap X) 0 (ds_depth X) (-1)
              ltac:(lia) ltac:(lia) LHP LDP LDL ltac:(reflexivity) ltac:(intros; lia) ltac:(intros; lia) ltac:(reflexivity))
    as (DL1 & HP1 & DP1 & E1 & LHP1 & LDP1 & LDL1 & HHP1 & HDL1).
  destruct (loop2_flat X t FC0 573 (ds_bl_count X) (ds_opt_len X) (ds_static_len X) (max_code X t) LFC
              DL1 HP1 DP1 OLr SLr LHP1 LDP1 HHP1)
    as (FC2 & HP2 & DP2 & E2 & LFC2 & LHP2 & LDP2 & HFC2 & HHP2).
  set (OL2 := wrap64 (ds_opt_len X - zlen (pads FC0 t))) in *.
  set (SL2 := if stree_has t then wrap64 (ds_static_len X - sl_pad t FC0) else ds_static_len X) in *.
  assert (OL2r : 0 <= OL2 < 2 ^ 64) by (subst OL2; apply wrap64_range).
  assert (SL2r : 0 <= SL2 < 2 ^ 64) by (subst SL2; destruct (stree_has t); [apply wrap64_range| exact SLr]).
  assert (C2 : cty (bt_upd X t FC2 DL1 HP2 (zlen (UP FC0 t)) 573 DP2 (ds_bl_count X) OL2 SL2 (MCP FC0 t))).
  { pose proof (cty_set_max_code _ t (MCP FC0 t) (cty_build_tree_loop2 2 _ t (last (Ulist FC0 t) (-1)) (cty_build_tree_loop1 (Z.to_nat (sd_elems t)) _ t (sd_elems t) 0 (-1) C0))) as C.
    rewrite E1 in C. cbn [fst] in C. rewrite E2 in C. cbn [fst] in C. autorewrite with btupd in C. exact C. }
  pose proof (cty_bt _ _ _ _ _ _ _ _ _ _ _ _ C2) as (U16FC2 & U16DL1 & U8DP2 & _).
  rewrite E1, E2. rewrite !bt_set_max_code, !bt_heap_len.
  assert (UPR : forall i, 1 <= i <= zlen (UP FC0 t) -> 0 <= arr_get HP2 i < tsize t).
  { intros i Hi. rewrite HHP2 by exact Hi. pose proof (RNGU (nth (Z.to_nat (i - 1)) (UP FC0 t) 0) ltac:(apply nth_In; unfold zlen in Hi; lia)). lia. }
  split. { intros i Hi. autorewrite with btupd. apply UPR. exact Hi. }
  split. { intros i Hi. autorewrite with btupd. apply U8DP2. rewrite LDP2. exact Hi. }
  split. { intros i Hi. autorewrite with btupd. apply U16FC2. rewrite LFC2. exact Hi. }
  destruct (heapify_flat0 X t FC2 DL1 (zlen (UP FC0 t)) 573 DP2 (ds_bl_count X) OL2 SL2 (MCP FC0 t) HP2 LHP2 ltac:(unfold u in UE; lia))
    as (HP3 & E3 & LHP3 & RR3 & OK3).
  pose proof (inv4_start t FC0 ltac:(intros j Hj; unfold Freq in Fnn; apply Fnn; exact Hj)
                FC2 DL1 HP3 DP2 LFC2 LDL1 LHP3 LDP2 HFC2 HDL1
                ltac:(exists HP2; split; [exact RR3| exact HHP2]) OK3) as I0.
  destruct (loop4_inv X t FC0 (ds_bl_count X) OL2 SL2 (MCP FC0 t) FB
              573%nat 0 FC2 DL1 HP3 (u t FC0) 573 DP2 _ (sd_elems t) I0 ltac:(unfold u in *; lia) ltac:(unfold u in *; lia) ltac:(lia))
    as (FC & DL & HP & DP & sub & E4 & INV).
  replace (573 - 2 * (u t FC0 - 1)) with (hm t FC0) in E4, INV by (unfold hm; lia).
  replace (0 + (u t FC0 - 1)) with (u t FC0 - 1) in INV by lia.
  unfold u in E3, E4.
  assert (C4 : cty (bt_upd X t FC DL HP 1 (hm t FC0) DP (ds_bl_count X) OL2 SL2 (MCP FC0 t))).
  { rewrite <- E4, <- E3. apply cty_build_tree_loop4. apply cty_build_tree_loop3. exact C2. }
  pose proof (cty_bt _ _ _ _ _ _ _ _ _ _ _ _ C4) as (U16FC & U16DL & U8DP & U16BC).
  rewrite E3, E4. unfold SMALLEST. autorewrite with btupd.
  pose proof INV as INV'. destruct INV' as [(L1 & L2 & L3 & L4) HK HOK HINJ HRNG HLEAF HINT HDAD HFC HWS HWO HWH HSUB HHB HDL0].
  pose proof (u_ge2 t FC0) as UG.
  split.
  { intros h Hh. autorewrite with btupd. unfold HEAP_SIZE in Hh. rewrite arr_get_set_other by lia.
    destruct (HRNG h ltac:(unfold PP; right; lia)) as [[_ R]|R]; lia. }
  split. { intros i Hi. autorewrite with btupd. apply U16DL. rewrite L2. exact Hi. }
  change (arr_set HP (hm t FC0 - 1) (arr_get HP 1)) with (HP7 t FC0 HP).
  rewrite (HP7_root t FC0 FC DL HP DP sub INV). fold (root HP).
  replace (hm t FC0 - 1 + 1) with (hm t FC0) by lia.
  pose proof (GI_start t FC0 (ds_bl_count X) OL2 SL2 FC DL HP DP sub INV LBC OL2r SL2r) as G0.
  split. { apply (gb1_ok_intro X t FC0 OL2 SL2 FC DL HP DP sub INV); [lia| exact OL2r| exact SL2r| exact G0]. }
  destruct (gb_loop1 X t FC0 OL2 SL2 FC DL HP DP sub INV OL2r SL2r 573 (hm t FC0) _ _ _ _ _ ltac:(lia) ltac:(lia) G0)
    as (DLc & BCc & OLc & SLc & ovc & EG & G).
  rewrite EG.
  pose proof (pass1_summary t FC0 OL2 SL2 FC DL HP DP sub INV OL2r SL2r DLc BCc OLc SLc ovc G) as (SDL & SZ & SBC & SOL & SSL & SOV & LDLc & LBCc).
  pose proof (excess_identity t FC0 0 FC DL HP DP sub INV) as (EK & EO & NN).
  pose proof (ML_range t FC0 FC DL HP DP sub INV) as MR.
  pose proof (MC_facts t FC0 FC DL HP DP sub INV) as [MCr _].
  assert (OV : ovc = 2 * N t FC0 DL HP) by (rewrite (g_ov _ _ _ _ _ _ _ _ _ _ _ _ _ G); exact EO).
  assert (OLcr : 0 <= OLc < 2 ^ 64) by (rewrite SOL; apply wrap64_range).
  split.
  { intros Hov. assert (N1 : 1 <= N t FC0 DL HP) by lia.
    pose proof (LI_start t FC0 0 FC DL HP DP sub INV BCc LBCc SBC) as L0.
    assert (Nk : N t FC0 DL HP <= u t FC0 - 1).
    { unfold N, isum.
      assert (Gb : forall l, zsum (map (fun i : Z => if sd_max_length t <=? nd DL HP (sd_elems t + i - 1) then 1 else 0) l) <= zlen l).
      { induction l; [change (0 <= zlen (@nil Z)); unfold zlen; cbn [length]; lia|]. cbn [map zsum]. rewrite zlen_cons. destruct (_ <=? _); lia. }
      etransitivity; [apply Gb|]. unfold zlen. rewrite ziota_length. lia. }
    rewrite OV. split.
    - apply (gb2_ok_intro X t FC0 FC DL HP DP sub INV). exact L0. exact N1.
    - destruct (gb_loop2 X t FC0 FC DL HP DP sub INV DLc OLc SLc 573 BCc (N t FC0 DL HP) L0 N1 ltac:(lia)) as (BCf & E2' & LIf).
      rewrite E2'. unfold HEAP_SIZE. apply (gb3_ok_intro X t FC0 FC DL HP DP sub INV); [exact LIf| lia| unfold hm in *; lia| exact LDLc| exact OLcr|].
      unfold HEAP_SIZE. rewrite RS_nil. lia. }
  assert (EGB : gen_bitlen (bt_upd X t FC DL (HP7 t FC0 HP) 1 (hm t FC0 - 1) DP (ds_bl_count X) OL2 SL2 (MCP FC0 t)) t
                = if ovc =? 0 then bt_upd X t FC DLc (HP7 t FC0 HP) 1 (hm t FC0 - 1) DP BCc OLc SLc (MCP FC0 t)
                  else gen_bitlen_loop3 (Z.to_nat (sd_max_length t)) (gen_bitlen_loop2 573 (bt_upd X t FC DLc (HP7 t FC0 HP) 1 (hm t FC0 - 1) DP BCc OLc SLc (MCP FC0 t)) (sd_max_length t) ovc) t (MCP FC0 t) (sd_max_length t) HEAP_SIZE).
  { unfold gen_bitlen. autorewrite with btupd. rewrite (HP7_root t FC0 FC DL HP DP sub INV). fold (root HP).
    replace (hm t FC0 - 1 + 1) with (hm t FC0) by lia. rewrite EG. reflexivity. }
  rewrite EGB. intros i Hi.
  destruct (Z.eqb_spec ovc 0) as [Z0|NZ].
  - unfold Len. autorewrite with btupd.
    destruct (in_dec Z.eq_dec i (UP FC0 t)) as [IN|NIN].
    + rewrite (SDL i IN). pose proof (nd_leaf_range t FC0 FC DL HP DP sub INV i IN). lia.
    + rewrite (SZ i ltac:(lia) NIN). lia.
  - destruct (gen_bitlen_overflow X t FC0 (ds_bl_count X) OL2 SL2 FC DL HP DP sub INV DLc BCc OLc SLc ovc LBC OL2r SL2r G NZ)
      as (DLf & BCf & OLf & E3' & _ & _ & RNG & ZZ & _).
    rewrite E3'. unfold Len. autorewrite with btupd.
    destruct (in_dec Z.eq_dec i (UP FC0 t)) as [IN|NIN].
    + pose proof (RNG i IN). lia.
    + rewrite (ZZ i ltac:(lia) NIN). lia.
Qed.
End BT.
