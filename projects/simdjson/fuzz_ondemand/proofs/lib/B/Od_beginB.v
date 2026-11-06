(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout Sj_akit Od_defsB Od_pluslB Od_headB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ od_load_hook | solve_load_base | solve_load_image ].

Lemma land7_eq : forall a r, (a mod 8 = r)%Z -> Z.land a 7 = r.
Proof. intros a r H. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.

Lemma Z_to_le_bytes_of_bytes : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b r IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8)%Z with 256%Z in Hb.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8)%Z with (2 ^ 8)%Z.
    rewrite <- Z.land_ones by lia.
    apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.lor_spec.
    destruct (Z.ltb_spec k 8) as [L|G].
    + rewrite Z.ones_spec_low by lia. rewrite Z.shiftl_spec_low by lia. rewrite orb_false_r, andb_true_r. reflexivity.
    + rewrite Z.ones_spec_high by lia. rewrite andb_false_r. symmetry.
      rewrite <- (Z.mod_small (bv_unsigned b) (2 ^ 8)) by (change (2 ^ 8)%Z with 256%Z; lia).
      apply Z.mod_pow2_bits_high. lia.
  - rewrite Z.shiftr_lor, Z.shiftr_shiftl_l by lia. change (8 - 8)%Z with 0%Z. rewrite Z.shiftl_0_r.
    rewrite (Z.shiftr_div_pow2 (bv_unsigned b)) by lia. rewrite Z.div_small by (change (2 ^ 8)%Z with 256%Z; lia).
    rewrite Z.lor_0_l. exact IH.
Qed.
Lemma le8_surj : forall bs : list byte, length bs = 8%nat -> exists v : Z, le8 (Z_to_bv 64 v) = bs.
Proof.
  intros bs H. exists (bytes_le_to_Z bs). unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with (2 ^ (8 * Z.of_nat 8))%Z.
  rewrite Z_to_le_bytes_mod by lia. rewrite <- H at 1. apply Z_to_le_bytes_of_bytes.
Qed.

Definition pre_k8 (c72 : cell) (j8 j16 j24 j32 j40 j48 j56 j64 j80 j88 : list byte) : list cell :=
  [CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; c72; CB 8 j80; CB 8 j88].
Definition pre_k96 (E : oaenv) (j96 j104 j144 j152 j160 j176 j184 j192 j200 j208 j216 j224 j232 : list byte) : list cell :=
  [CB 8 j96; CB 8 j104; C8 (wz 0); C8 (wz (oa_F E)); C8 (wz (oa_F E)); C8 (wz (o_COPY E)); CB 8 j144; CB 8 j152; CB 8 j160;
   C8 (wz (oa_F E + 96)); CB 8 j176; CB 8 j184; CB 8 j192; CB 8 j200; CB 8 j208; CB 8 j216; CB 8 j224; CB 8 j232].

Definition pre_k240 (E : oaenv) (c240 : cell) (v280 v328 v368 : Z) (c336 c352 : cell) (j264 j272 j288 j296 j304 j312 j320 j344 j360 j376 : list byte) : list cell :=
  [c240; C8 (wz (oa_F E / 8 + 2147450880)); C8 (wz (o_act E)); CB 8 j264; CB 8 j272; C8 (wz v280); CB 8 j288; CB 8 j296;
   CB 8 j304; CB 8 j312; CB 8 j320; C8 (wz v328); c336; CB 8 j344; c352; CB 8 j360; C8 (wz v368); CB 8 j376].
Definition OD_PRE (E : oaenv) (m1 : mem) : Prop :=
  (exists j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88, rw_cells bsegs m1 (oa_S1 E + 8) (pre_k8 (CB 8 j72) j8 j16 j24 j32 j40 j48 j56 j64 j80 j88)) /\
  (exists j96 j104 j144 j152 j160 j176 j184 j192 j200 j208 j216 j224 j232,
     rw_cells bsegs m1 (oa_S1 E + 96) (pre_k96 E j96 j104 j144 j152 j160 j176 j184 j192 j200 j208 j216 j224 j232)) /\
  (exists j240 j264 j272 j288 j296 j304 j312 j320 j336 j344 j352 j360 j376,
     rw_cells bsegs m1 (oa_S1 E + 240)
       (pre_k240 E (CB 8 j240) (oa_F E + 224) (oa_F E + 208) (oa_F E + 200) (CB 8 j336) (CB 8 j352) j264 j272 j288 j296 j304 j312 j320 j344 j360 j376)) /\
  (exists junk, rw_cells bsegs m1 (oa_F E + 192) [CB 64 junk]) /\
  rw_cells bsegs m1 (oa_F E + 96) (od_parser_cells E) /\
  rw_cells bsegs m1 (o_IMPL E) (dpi_cells E) /\
  (exists ws, u32arr bsegs m1 (o_IDX E) ws /\ idx_ok E ws) /\
  bytes_at bsegs m1 (o_BUF E) (padded_bytes (o_bs E)) /\
  wr_at bsegs m1 (o_SB E) (o_CAP E) /\
  ro_cells bsegs m1 OD_DPI_VT od_vt_cells /\
  ro_cells bsegs m1 OD_GOT_TABS od_got_cells /\
  mem_inv bsegs m1 /\
  stk bsegs m1 (o_lo E) (oa_S1 E).

Lemma od_pre_words : forall (E : oaenv) (m : mem) c240 v280 v328 v368 j336 j352 j264 j272 j288 j296 j304 j312 j320 j344 j360 j376,
  rw_cells bsegs m (oa_S1 E + 240) (pre_k240 E c240 v280 v328 v368 (CB 8 j336) (CB 8 j352) j264 j272 j288 j296 j304 j312 j320 j344 j360 j376) ->
  exists v336 v352,
    rw_cells bsegs m (oa_S1 E + 240) (pre_k240 E c240 v280 v328 v368 (C8 (wz v336)) (C8 (wz v352)) j264 j272 j288 j296 j304 j312 j320 j344 j360 j376).
Proof.
  intros E m c240 v280 v328 v368 j336 j352 j264 j272 j288 j296 j304 j312 j320 j344 j360 j376 H.
  pose proof H as [[W _] _].
  unfold pre_k240 in W. cbn [cells_wf cell_wf] in W.
  assert (L336 : length j336 = 8%nat) by tauto. assert (L352 : length j352 = 8%nat) by tauto.
  destruct (le8_surj j336 L336) as [v336 EV1]. destruct (le8_surj j352 L352) as [v352 EV2]. exists v336, v352.
  eapply rw_cells_recell; [exact H| | |].
  - unfold pre_k240. cbn [cells_wf cell_wf]. tauto.
  - unfold pre_k240, wz. cbn [cells_bytes cbytes]. rewrite EV1, EV2. reflexivity.
  - unfold pre_k240. cbn [cells_size csize]. reflexivity.
Qed.

Section Begin.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Hypothesis HG : od_shb E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation n := (o_n E).

  Lemma od_consts : forall (Q : machine_state -> Prop) vs v v240 v336 v352 xra xt0 xt1 xt2 xa0 xa3 xa4 xa6 xa7 xs2 xs3 xs4 xs6 xs9 xt3 xt4 xt5 xt6 xF xfc (m0 m1 : mem)
      j8 j16 j24 j32 j40 j48 j56 j64 j80 j88 j96 j104 j144 j152 j160 j176 j184 j192 j200 j208 j216 j224 j232
      j264 j272 j288 j296 j304 j312 j320 j344 j360 j376 v280 v368 W,
    mem_inv bsegs m1 -> munch W m0 m1 -> wmono bsegs m0 m1 -> W = od_W E ->
    (0 <= v <= 1)%Z -> (vs mod 8 = 0)%Z -> (0 <= vs < 2^47)%Z ->
    rw_cells bsegs m1 (oa_S1 E + 8) (pre_k8 (C8 (wz (oa_F E + 104))) j8 j16 j24 j32 j40 j48 j56 j64 j80 j88) ->
    rw_cells bsegs m1 (oa_S1 E + 96) (pre_k96 E j96 j104 j144 j152 j160 j176 j184 j192 j200 j208 j216 j224 j232) ->
    rw_cells bsegs m1 (oa_S1 E + 240)
      (pre_k240 E (C8 (wz v240)) v280 (vs + 16) v368 (C8 (wz v336)) (C8 (wz v352)) j264 j272 j288 j296 j304 j312 j320 j344 j360 j376) ->
    (forall xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xt3' xt4' xt5' xt6' (m' : mem),
       mem_inv bsegs m' -> munch W m0 m' -> wmono bsegs m0 m' -> munch [(oa_S1 E + 8, oa_S1 E + 384)%Z] m1 m' -> wmono bsegs m1 m' ->
       rw_cells bsegs m' (oa_S1 E + 8) (fr_k8 E (v - 1)) ->
       rw_cells bsegs m' (oa_S1 E + 96) (fr_k96 E (v + 1) v (CB 8 j96) (CB 8 j104) (CB 8 j224) (CB 8 j232)) ->
       rw_cells bsegs m' (oa_S1 E + 240) (fr_k240 E vs v240 v v336 v352 (CB 8 j272) (CB 8 j304) (CB 8 j320) (CB 8 j376)) ->
       evt bsegs Q (MS (mkR xra (Z_to_bv 64 (oa_S1 E)) (o_gp E) (o_tp E) xt0' xt1' xt2' (Z_to_bv 64 (oa_USP E)) (Z_to_bv 64 (oa_S1 E))
                            xa0' xa1' xa2' xa3' xa4' xa5' xa6' (Z_to_bv 64 (vs + 8))
                            (Z_to_bv 64 v) (Z_to_bv 64 (vs + 32)) (Z_to_bv 64 (o_act E)) (Z_to_bv 64 v) xs6
                            (Z_to_bv 64 2147450880) (Z_to_bv 64 (vs + 36)) (Z_to_bv 64 4)
                            (Z_to_bv 64 (oa_F E + 32)) (Z_to_bv 64 vs) xt3' xt4' xt5' xt6')
                       xF (Z_to_bv 64 OD_HEAD) xfc None m' (seg_rom bsegs))) ->
    evt bsegs Q (MS (mkR xra (Z_to_bv 64 (oa_S1 E)) (o_gp E) (o_tp E) xt0 xt1 xt2 (Z_to_bv 64 (oa_USP E)) (Z_to_bv 64 (oa_S1 E))
                         xa0 (Z_to_bv 64 (vs + 32)) (Z_to_bv 64 v) xa3 xa4 (Z_to_bv 64 (vs + 8)) xa6 xa7
                         xs2 xs3 xs4 (Z_to_bv 64 v) xs6 (Z_to_bv 64 2147450880) (Z_to_bv 64 (vs + 36)) xs9
                         (Z_to_bv 64 (oa_F E + 32)) (Z_to_bv 64 vs) xt3 xt4 xt5 xt6)
                    xF (Z_to_bv 64 0x97468) xfc None m1 (seg_rom bsegs)).
  Proof using OK.
    intros until W. intros MI MU WM EW VV VS8 VSR FR8 FR96 FR240 K.
    od_env OK. subst W. unfold od_W in MU.
    unfold pre_k8, wz in FR8. unfold pre_k96, wz in FR96. unfold pre_k240, wz in FR240.
    pose proof (munch_refl [(oa_S1 E + 8, oa_S1 E + 384)%Z] m1) as MUL. pose proof (wmono_refl bsegs m1) as WML.
    assert (L32 : Z.land (vs + 32) 7 = 0%Z) by (apply land7_eq; lia).

    ostep. ostep. ostep. ostep. ostep. ostep. ostep. ostep. ostep. rewrite ?L32. ostep.

    do 16 zstep.

    ostep. ostep. ostep. lstep. ostep. ostep. ostep. lstep. ostep. lstep. ostep. lstep. ostep. lstep.
    ostep. lstep. ostep. ostep. lstep. ostep. ostep.

    ostep. lstep. ostep. lstep. ostep. lstep. ostep. lstep. ostep. lstep. ostep. lstep. ostep. ostep. lstep.
    ostep. ostep. lstep. ostep. lstep. ostep. ostep. ostep. ostep. ostep. ostep.
    eapply evt_eq.
    2: { eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MI); [unfold od_W; exact MU| exact WM| exact MUL| exact WML| | |].
         - eapply rw_cells_eq; [exact FR8|]. unfold fr_k8. od_cells_eq.
         - eapply rw_cells_eq; [exact FR96|]. unfold fr_k96. od_cells_eq.
         - eapply rw_cells_eq; [exact FR240|]. unfold fr_k240. od_cells_eq. }
    unfold OD_HEAD. od_st_eq.
  Qed.

  Definition OD_REST (m1 : mem) : Prop :=
    rw_cells bsegs m1 (oa_F E + 96) (od_parser_cells E) /\
    rw_cells bsegs m1 (o_IMPL E) (dpi_cells E) /\
    (exists ws, u32arr bsegs m1 (o_IDX E) ws /\ idx_ok E ws) /\
    bytes_at bsegs m1 (o_BUF E) (padded_bytes (o_bs E)) /\
    wr_at bsegs m1 (o_SB E) (o_CAP E) /\
    ro_cells bsegs m1 OD_DPI_VT od_vt_cells /\
    ro_cells bsegs m1 OD_GOT_TABS od_got_cells /\
    mem_inv bsegs m1 /\ munch (od_W E) (o_m0 E) m1 /\ wmono bsegs (o_m0 E) m1 /\
    stk bsegs m1 (o_lo E) (oa_S1 E).

  Ltac rest_open H :=
    let ws := fresh "ws" in
    destruct H as (PARS & DPI & (ws & IDXA & IDXL & IDXF) & BUFRO & SBW & VT & GOT & MI & MU & WM & ST);
    unfold od_parser_cells in PARS; unfold dpi_cells in DPI; unfold od_vt_cells, OD_DPI_VT in VT; unfold od_got_cells, OD_GOT_TABS in GOT; unfold od_W in MU;
    unfold wz in PARS, DPI;
    lazymatch type of BUFRO with
    | bytes_at _ _ _ (padded_bytes ?bs) => let PBL := fresh "PBL" in pose proof (padded_bytes_blen bs) as PBL
    end.
  Ltac rest_close :=
    unfold OD_REST, od_parser_cells, dpi_cells, od_vt_cells, od_got_cells, od_W, OD_DPI_VT, OD_GOT_TABS, idx_ok;
    split; [eassumption|]; split; [eassumption|];
    split; [ eexists; split; [eassumption| split; eassumption] | ];
    split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
    split; [eassumption|]; split; [eassumption|]; split; eassumption.

  Lemma od_invalid : forall (Q : machine_state -> Prop) st v336 v352 xra xt0 xt1 xt2 xa0 xa3 xa4 xa6 xa7 xs2 xs3 xs4 xs6 xs9 xt3 xt4 xt5 xt6 xF xfc m1
      j8 j16 j24 j32 j40 j48 j56 j64 j80 j88 j96 j104 j144 j152 j160 j176 j184 j192 j200 j208 j216 j224 j232
      j264 j272 j288 j296 j304 j312 j320 j344 j360 j376 j241 j252 v280 v368,
    rw_cells bsegs m1 (oa_S1 E + 8) (pre_k8 (C8 (wz (oa_F E + 104))) j8 j16 j24 j32 j40 j48 j56 j64 j80 j88) ->
    rw_cells bsegs m1 (oa_S1 E + 96) (pre_k96 E j96 j104 j144 j152 j160 j176 j184 j192 j200 j208 j216 j224 j232) ->
    rw_cells bsegs m1 (oa_S1 E + 240)
      (pre_k240 E (C8 (wz 0)) v280 16 v368 (C8 (wz v336)) (C8 (wz v352)) j264 j272 j288 j296 j304 j312 j320 j344 j360 j376) ->
    rw_cells bsegs m1 (oa_F E + 192) (iter_cells E st j241 j252) ->
    OD_REST m1 -> frm0 xfc -> od_exit_k E Q ->
    evt bsegs Q (MS (mkR xra (Z_to_bv 64 (oa_S1 E)) (o_gp E) (o_tp E) xt0 xt1 xt2 (Z_to_bv 64 (oa_USP E)) (Z_to_bv 64 (oa_S1 E))
                         xa0 (Z_to_bv 64 32) (Z_to_bv 64 0) xa3 xa4 (Z_to_bv 64 8) xa6 xa7
                         xs2 xs3 xs4 (Z_to_bv 64 0) xs6 (Z_to_bv 64 2147450880) (Z_to_bv 64 36) xs9
                         (Z_to_bv 64 (oa_F E + 32)) (Z_to_bv 64 0) xt3 xt4 xt5 xt6)
                    xF (Z_to_bv 64 0x97468) xfc None m1 (seg_rom bsegs)).
  Proof using OK.
    intros until v368. intros FR8 FR96 FR240 ITER REST FRM KX.
    od_env OK. pose proof KX as KX0. unfold od_exit_k, OD_EXIT in KX0.
    pose proof REST as (_ & _ & _ & _ & _ & _ & _ & MI0 & MU0 & WM0 & _).
    unfold iter_cells in ITER. unfold wz in ITER.

    eapply evt_eq.
    2: { eapply (od_consts Q 0 0 0 v336 v352 xra xt0 xt1 xt2 xa0 xa3 xa4 xa6 xa7 xs2 xs3 xs4 xs6 xs9 xt3 xt4 xt5 xt6 xF xfc (o_m0 E) m1);
           [exact MI0| exact MU0| exact WM0| reflexivity| lia| reflexivity| lia| exact FR8| exact FR96| exact FR240|].
         intros xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xt3' xt4' xt5' xt6' m3 MI3 MU3 WM3 MUc WMc F8 F96 F240.
         clear FR8 FR96 FR240 MI0 MU0 WM0.
         assert (REST3 : OD_REST m3).
         { rest_open REST. clear MU WM MI. lazymatch type of ITER with rw_cells _ ?m _ _ => transport_after_call bsegs m m3 MUc WMc end.
           pose proof MU3 as MU. pose proof WM3 as WM. pose proof MI3 as MI. unfold od_W in MU. rest_close. }
         lazymatch type of ITER with rw_cells _ ?m _ _ => transport_after_call bsegs m m3 MUc WMc end.
         clear MUc WMc REST MI3 MU3 WM3.
         assert (INVH : ODINVg E 0 (-1) 1 0 0 0 v336 v352 st m3).
         { rest_open REST3. unfold ODINVg. do 8 eexists. od_close_invc. }
         clear F8 F96 F240 ITER REST3.
         od_open_inv INVH. unfold OD_HEAD.

         zstep. if_true. zstep. zstep. if_true. lstep. lstep. zstep. zstep.
         od_cur_mem ltac:(fun mm => assert (INVA : ODINVg E 0 (-1) 1 0 0 0 0 0 st mm) by od_close_inv).
         eapply evt_eq; [| eapply (od_disp_err E OK Q st 0%Z (-1)%Z 1%Z 0%Z 0%Z 0%Z 0%Z 0%Z); [exact FRM| exact INVA| intros w352 ya0 ya1 ya2 ya3 ys6 ys10 ys11 yt4 m' INV']];
           [unfold OD_DISP; od_st_eq|].
         unfold OD_PLUS.
         clear - INV' FRM KX0 OK.
         od_open_inv INV'. od_env OK.

         zstep. zstep. zstep. zstep. zstep. zstep. zstep. if_false. zstep. zstep. if_true. zstep. zstep. if_false. zstep.
         eapply evt_eq; [| eapply (KX0 st 0%Z (-1)%Z 1%Z 0%Z 0%Z 0%Z 0%Z w352); [exact FRM| od_close_inv]]. od_st_eq. }
    od_st_eq.
  Qed.

  Theorem od_iterate : forall (Q : machine_state -> Prop) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs6 xs9 xt3 xt4 xt5 xt6 xF xfc m1,
    OD_PRE E m1 -> frm0 xfc -> o_m0 E = m1 -> od_exit_k E Q ->
    (tokT (o_bs E) (o_idxs E) (o_n E - 1) = C_RBRACKET -> od_head_k E Q od_init) ->
    evt bsegs Q (MS (mkR xra (Z_to_bv 64 (oa_S1 E)) (o_gp E) (o_tp E) xt0 xt1 xt2 (Z_to_bv 64 (oa_USP E)) (Z_to_bv 64 (oa_S1 E))
                         xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                         xs2 xs3 (Z_to_bv 64 (oa_F E + 104)) (Z_to_bv 64 (o_BUF E)) xs6 (Z_to_bv 64 2147450880) (Z_to_bv 64 (oa_F E + 228)) xs9
                         (Z_to_bv 64 (oa_F E + 32)) (Z_to_bv 64 (oa_F E + 192)) xt3 xt4 xt5 xt6)
                    xF (Z_to_bv 64 OD_ITER) xfc None m1 (seg_rom bsegs)).
  Proof using OK HG.
    intros Q xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs6 xs9 xt3 xt4 xt5 xt6 xF xfc m1 PRE FRM EM0 KX KH.
    destruct PRE as ((j8 & j16 & j24 & j32 & j40 & j48 & j56 & j64 & j72 & j80 & j88 & FR8)
                     & (j96 & j104 & j144 & j152 & j160 & j176 & j184 & j192 & j200 & j208 & j216 & j224 & j232 & FR96)
                     & (j240 & j264 & j272 & j288 & j296 & j304 & j312 & j320 & j336 & j344 & j352 & j360 & j376 & FR240)
                     & (junk & ITJ) & PARS & DPI & (ws & IDXA & IDXL & IDXF) & BUFRO & SBW & VT & GOT & MI & ST).
    destruct (od_pre_words E m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR240) as (v336 & v352 & FR240'). clear FR240. rename FR240' into FR240.
    od_env OK. unfold OD_ITER. unfold pre_k8 in FR8. unfold pre_k96, wz in FR96. unfold pre_k240, wz in FR240.
    unfold od_parser_cells in PARS. unfold dpi_cells in DPI. unfold od_vt_cells, OD_DPI_VT in VT. unfold od_got_cells, OD_GOT_TABS in GOT.
    unfold wz in PARS, DPI.
    pose proof (padded_bytes_blen bs) as PBL.
    pose proof (munch_refl (od_W E) m1) as MU. pose proof (wmono_refl bsegs m1) as WM. unfold od_W in MU.
    rewrite <- EM0 in MU at 1. rewrite <- EM0 in WM at 1.
    apply (rw_cells_split_CB bsegs m1 _ [] 64 junk [] [8;8;8;8;8;8;1;7;4;4]%nat) in ITJ; [|reflexivity].
    cbn [mk_CB_cells app] in ITJ.
    repeat match type of ITJ with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in ITJ; clearbody j end.
    rename ITJ into ITER.

    ostep. ostep. uok. ostep. ual. ostep. if_true. ostep. ostep. ostep. ostep. ostep. ostep. ostep. if_false.
    ostep. ostep. uok. ostep. ual3 (o_IDX E). ostep. if_true. ostep. ostep. uok.

    ostep. ostep. ostep. ostep. ostep. ostep. ostep. ostep. if_false.
    ostep. ostep. ostep. ostep. lstep. ostep. lstep. lstep. ostep.
    apply (rw_cells_C8_C4 bsegs _ _ [C8 _; C8 _; C8 _; C8 _] _ (Z_to_bv 64 0) (Z_to_bv 64 1)) in ITER; [| exact od_le8_err_depth]. cbn [app] in ITER.

    ostep. odnorm. ostep. ostep. utrap. ostep. ostep. if_true.
    ostep. ostep. ostep. zstep. if_true.

    pose proof (od_tokI_range E S1 0 ltac:(lia)) as TR0. pose proof (od_tokT_range E BOK 0) as CR0.
    pose proof (od_tokI_range E S1 (n + -1) ltac:(lia)) as TRL. pose proof (od_tokT_range E BOK (n + -1)) as CRL.
    pose proof (od_tokI_range E S1 n ltac:(lia)) as TRN.
    pose proof (od_tokI_range E S1 1 ltac:(lia)) as TR1. pose proof (od_tokT_range E BOK 1) as CR1.
    pose proof (tokT_n bs idxs S1) as TN0.
    od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws 0 ltac:(eassumption) (conj IDXL IDXF) ltac:(lia)) as RDI0;
                               pose proof (tokB_read mm E (tokI bs idxs 0) ltac:(eassumption) ltac:(lia)) as RDB0).
    replace (o_IDX E + 4 * 0)%Z with (o_IDX E) in RDI0 by lia.
    fold (tokT bs idxs 0) in RDB0.
    set (c0 := tokT bs idxs 0) in *. set (off0 := tokI bs idxs 0) in *.

    ostep. odnorm. ostep. ostep. if_false. ostep. utrap. ostep. ual3 (o_IDX E). ostep. if_false.
    ostep. ostep. ostep. ostep. ostep. if_true.
    ostep. odnorm. ostep. ostep. utrap. ostep. ostep. ostep. unz. ostep. if_false. ostep. utrap.
    ochk. ostep. odnorm. ostep. zstep.
    if_cases K0; zify_cond K0.
    {
      lstep. ostep. ostep. ostep. ostep. lstep. ostep. ostep. ostep. ostep.
      od_cur_mem ltac:(fun mm => assert (REST : OD_REST mm) by rest_close).
      eapply evt_eq; [| eapply (od_invalid Q (mkO 0 1 0 true 0) v336 v352); [| | | | exact REST| exact FRM| exact KX]]; [od_st_eq| | | |].
      - eapply rw_cells_eq; [eassumption|]. unfold pre_k8. od_cells_eq.
      - eapply rw_cells_eq; [eassumption|]. unfold pre_k96. od_cells_eq.
      - eapply rw_cells_eq; [eassumption|]. unfold pre_k240. od_cells_eq.
      - eapply rw_cells_eq; [exact ITER|]. unfold iter_cells. od_cells_eq. }

    ostep. utrap. ostep. ostep. utrap. ostep. ostep. ostep. ostep. ostep. if_false. ostep. ostep. if_true.

    ostep. ostep. utrap. ostep. ual. ostep. if_false. ostep. ochk.
    ostep. ostep. utrap. ostep. ual. ostep. if_false. ostep. ochk.
    ostep. odnorm.
    ostep. utrap. ostep. ostep. ostep. ostep.
    rewrite ?(Z.mod_small (n + -1) 4294967296) by lia.
    od_opidx_inline HG ST.
    od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (n + -1) ltac:(eassumption) (conj IDXL IDXF) ltac:(lia)) as RDIL;
                               pose proof (tokB_read mm E (tokI bs idxs (n + -1)) ltac:(eassumption) ltac:(lia)) as RDBL).
    fold (tokT bs idxs (n + -1)) in RDBL.
    set (cl := tokT bs idxs (n + -1)) in *. set (offl := tokI bs idxs (n + -1)) in *.

    ostep. ostep. ostep. ostep. ostep. if_true.
    ostep. odnorm. ostep. ostep. utrap. ostep. ostep. ostep. unz. ostep. if_false. ostep. utrap.
    ochk. ostep. odnorm. ostep. zstep.
    if_cases KL; zify_cond KL.
    {
      ostep. ostep. lstep. lstep. ostep. utrap. lstep. ostep. ostep. ostep. ostep. lstep. ostep. ostep. lstep. ostep. ostep. ostep.
      od_cur_mem ltac:(fun mm => assert (REST : OD_REST mm) by rest_close).
      eapply evt_eq; [| eapply (od_invalid Q (mkO 1 0 28 false 0) v336 v352); [| | | | exact REST| exact FRM| exact KX]]; [od_st_eq| | | |].
      - eapply rw_cells_eq; [eassumption|]. unfold pre_k8. od_cells_eq.
      - eapply rw_cells_eq; [eassumption|]. unfold pre_k96. od_cells_eq.
      - eapply rw_cells_eq; [eassumption|]. unfold pre_k240. od_cells_eq.
      - eapply rw_cells_eq; [exact ITER|]. unfold iter_cells. od_cells_eq. }
    assert (HLAST : tokT bs idxs (n - 1) = C_RBRACKET) by (replace (n - 1)%Z with (n + -1)%Z by lia; unfold C_RBRACKET; fold cl; lia).

    ostep. ostep. utrap. ostep. ual. ostep. if_false. ostep. ochk.
    ostep. ostep. utrap. ostep. ual. ostep. if_false. ostep. ochk.
    ostep. odnorm. ostep.
    od_opidx_inline HG ST.
    od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws n ltac:(eassumption) (conj IDXL IDXF) ltac:(lia)) as RDIN;
                               pose proof (tokB_read mm E (tokI bs idxs n) ltac:(eassumption) ltac:(lia)) as RDBN;
                               pose proof (tokI_read mm E ws 1 ltac:(eassumption) (conj IDXL IDXF) ltac:(lia)) as RDI1;
                               pose proof (tokB_read mm E (tokI bs idxs 1) ltac:(eassumption) ltac:(lia)) as RDB1).
    fold (tokT bs idxs n) in RDBN. fold (tokT bs idxs 1) in RDB1. rewrite TN0 in RDBN.
    replace (o_IDX E + 4 * 1)%Z with (o_IDX E + 4)%Z in RDI1 by lia.
    set (c1 := tokT bs idxs 1) in *. set (off1 := tokI bs idxs 1) in *. set (offn := tokI bs idxs n) in *.

    ostep. ostep. ostep. ostep. ostep. if_true.
    ostep. odnorm. ostep. ostep. ostep. utrap. ostep. ostep. ostep. unz. ostep. if_false. ostep. utrap.
    ochk. ostep. odnorm. ostep. ostep. if_true.

    ostep. ostep. ostep. utrap. ostep. ostep. if_false. ostep. odnorm. ostep. ostep. if_false. ostep. ual3 (o_IDX E + 4)%Z. ostep. if_false.
    ostep. ostep. ostep. ostep. ostep. if_true.
    ostep. odnorm. ostep. ostep. utrap. ostep. ostep. ostep. unz. ostep. if_false. ostep. utrap.
    ochk. ostep. odnorm. ostep. zstep.
    assert (N2 : (2 <= n)%Z).
    { destruct (Z.eq_dec n 1) as [N1|N1]; [|lia]. exfalso.
      assert (EQ : cl = c0) by (unfold cl, c0; f_equal; lia). lia. }

    assert (K_FIN : forall st ya0 ya2 ya3 ya4 mm j241' j252',
              (st = mkO 1 2 0 true 0 \/ (st = mkO 2 0 0 true 0 /\ c1 = 93%Z)) ->
              rw_cells bsegs mm (oa_S1 E + 8) (pre_k8 (C8 (wz (oa_F E + 104))) j8 j16 j24 j32 j40 j48 j56 j64 j80 j88) ->
              rw_cells bsegs mm (oa_S1 E + 96) (pre_k96 E j96 j104 j144 j152 j160 j176 j184 j192 j200 j208 j216 j224 j232) ->
              rw_cells bsegs mm (oa_S1 E + 240)
                (pre_k240 E (CB 8 j240) (oa_F E + 224) (oa_F E + 208) (oa_F E + 200) (C8 (wz v336)) (C8 (wz v352)) j264 j272 j288 j296 j304 j312 j320 j344 j360 j376) ->
              rw_cells bsegs mm (oa_F E + 192)
                [C8 (Z_to_bv 64 (o_BUF E)); C8 (Z_to_bv 64 (o_IDX E + 4 * o_pos st)); C8 (Z_to_bv 64 (oa_F E + 96)); C8 (Z_to_bv 64 (o_SB E));
                 C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 (o_IDX E)); C1 (Z_to_bv 8 0); CB 7 j241'; C4 (Z_to_bv 64 0); CB 4 j252'] ->
              OD_REST mm ->
              evt bsegs Q (MS (mkR (Z_to_bv 64 0x973a0) (Z_to_bv 64 (oa_S1 E)) (o_gp E) (o_tp E) xt0 xt1 xt2 (Z_to_bv 64 (oa_USP E)) (Z_to_bv 64 (oa_S1 E))
                                   ya0 (Z_to_bv 64 (o_depth st)) ya2 ya3 ya4 (Z_to_bv 64 (oa_F E + 200)) xa6 xa7
                                   (Z_to_bv 64 (o_IDX E)) xs3 (Z_to_bv 64 (oa_F E + 104)) (Z_to_bv 64 (o_BUF E)) xs6 (Z_to_bv 64 2147450880)
                                   (Z_to_bv 64 (oa_F E + 228)) xs9 (Z_to_bv 64 (oa_F E + 32)) (Z_to_bv 64 (oa_F E + 192)) xt3 xt4 xt5 xt6)
                              xF (Z_to_bv 64 0x97454) xfc None mm (seg_rom bsegs))).
    { intros st ya0 ya2 ya3 ya4 mm j241' j252' HST F8 F96 F240 ITER2 REST2.
      clear FR8 FR96 FR240 ITER PARS DPI IDXA IDXL IDXF BUFRO SBW VT GOT MI MU WM ST RDI0 RDB0 RDIL RDBL RDIN RDBN RDI1 RDB1.
      unfold pre_k8, wz in F8. unfold pre_k96, wz in F96. unfold pre_k240, wz in F240.
      rest_open REST2.
      assert (DR : (0 <= o_depth st <= 2)%Z) by (destruct HST as [->|[-> _]]; cbn; lia).

      ostep. ostep. ostep. ostep. ostep.
      od_cur_mem ltac:(fun mm' => assert (REST3 : OD_REST mm') by rest_close).
      od_cur_mem ltac:(fun mm' =>
        eapply evt_eq;
          [| eapply (od_consts Q (oa_F E + 192) 1 (o_IDX E) v336 v352 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (o_m0 E) mm');
               [exact MI| unfold od_W; exact MU| exact WM| reflexivity| lia| | lia| | | |]]).
      1: od_st_eq.
      1: { Z.div_mod_to_equations. lia. }
      all: cycle 1.
      { eapply rw_cells_eq; [eassumption|]. unfold pre_k96. od_cells_eq. }
      { eapply rw_cells_eq; [eassumption|]. unfold pre_k240. od_cells_eq. }
      2: { eapply rw_cells_eq; [eassumption|]. unfold pre_k8. od_cells_eq. }
      intros xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xt3' xt4' xt5' xt6' m3 MI3 MU3 WM3 MUc WMc G8 G96 G240.
             clear F8 F96 F240 REST3.
             clear MU WM MI.
             lazymatch type of ITER2 with rw_cells _ ?m _ _ => transport_after_call bsegs m m3 MUc WMc end.
             clear MUc WMc.
             pose proof MU3 as MU. pose proof WM3 as WM. pose proof MI3 as MI. unfold od_W in MU.
             assert (INVH : ODINVh E v336 v352 st m3).
             { unfold ODINVg. do 8 eexists.
               unfold ODINVc. split; [exact G8|]. split; [exact G96|]. split; [exact G240|].
               split; [do 2 eexists; eapply rw_cells_eq; [exact ITER2|]; unfold iter_cells; destruct HST as [->|[-> _]]; od_cells_eq|].
               rest_close. }
             eapply evt_eq; [| eapply (KH HLAST st v336 v352 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3); [| exact FRM| exact INVH]]; [unfold OD_HEAD; od_st_eq|].
             left. unfold od_next_ok, od_head_ok, sbo_ok, od_init.
             pose proof (od_tokI_range E S1 (Z.min 1 n) ltac:(lia)). pose proof (od_tokI_range E S1 (Z.min 2 n) ltac:(lia)).
             destruct HST as [->|[-> HC1]]; cbn [o_pos o_depth o_err o_alive o_sbo].
             + split; [lia|]. split; [reflexivity|]. split; [split; [lia| fold bs idxs; lia]|]. split; [reflexivity|].
               right; right. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia| fold bs idxs; lia].
             + split; [lia|]. split; [reflexivity|]. split; [split; [lia| fold bs idxs; lia]|]. split; [reflexivity|].
               right; left. split; [reflexivity|]. split; [reflexivity| lia]. }
    if_cases K1; zify_cond K1.
    -
      ostep.
      od_cur_mem ltac:(fun mm => assert (REST : OD_REST mm) by rest_close).
      eapply evt_eq; [| eapply (K_FIN (mkO 1 2 0 true 0)); [left; reflexivity| | | | | exact REST]]; [od_st_eq| | | |].
      + eapply rw_cells_eq; [eassumption|]. unfold pre_k8. od_cells_eq.
      + eapply rw_cells_eq; [eassumption|]. unfold pre_k96. od_cells_eq.
      + eapply rw_cells_eq; [eassumption|]. unfold pre_k240. od_cells_eq.
      + eapply rw_cells_eq; [exact ITER|]. od_cells_eq.
    -
      ostep. ostep. utrap. ostep. utrap. ostep. ostep. utrap. ostep. ostep. ostep. ostep.
      od_cur_mem ltac:(fun mm => assert (REST : OD_REST mm) by rest_close).
      eapply evt_eq; [| eapply (K_FIN (mkO 2 0 0 true 0)); [right; split; [reflexivity| lia]| | | | | exact REST]]; [od_st_eq| | | |].
      + eapply rw_cells_eq; [eassumption|]. unfold pre_k8. od_cells_eq.
      + eapply rw_cells_eq; [eassumption|]. unfold pre_k96. od_cells_eq.
      + eapply rw_cells_eq; [eassumption|]. unfold pre_k240. od_cells_eq.
      + eapply rw_cells_eq; [exact ITER|]. od_cells_eq.
  Qed.
End Begin.
