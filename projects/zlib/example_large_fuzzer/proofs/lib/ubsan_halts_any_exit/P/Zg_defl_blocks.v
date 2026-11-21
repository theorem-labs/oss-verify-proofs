(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import InitMem Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Z_defl_model Z_defl_kit
     Z_flushpend Z_defl_arms Z_adler32 Zg_adler32_iface Zg_defl_iface Z_defl_path Zg_defl_path.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate SendModel FillWinModel RefDeflSlow6 RefDeflSafeS DeflateSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition Z_CFG_TABLE : Z := 0x29238.

Lemma cfg_cell_at : forall m a, relro_clean m ->
  (a = 0x29280 \/ a = 0x29290 \/ a = 0x292a0 \/ a = 0x292b0 \/ a = 0x292c0 \/ a = 0x292d0) ->
  rw_cells psegs m a [C8 (wz Z_DEFLATE_SLOW)].
Proof.
  intros m a RC Ha. unfold relro_clean, RELRO_LO, RELRO_HI in RC. unfold Z_DEFLATE_SLOW.
  pose (cs := [C8 (wz 0x1985c)]).
  destruct Ha as [-> |[-> |[-> |[-> |[-> | ->]]]]];
  (lazymatch goal with |- rw_cells _ _ ?b _ =>
     apply (InitMem.rw_cells_recast psegs m b [CB 8 (cells_bytes cs)] cs);
     [ apply (InitMem.rw_cells_image0 psegs m b (cells_bytes cs));
       [ intros x Hx; apply RC; change (Z.of_nat (length (cells_bytes cs))) with 8 in Hx; lia
       | vm_compute; reflexivity | lia | change (Z.of_nat (length (cells_bytes cs))) with 8; lia ]
     | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ] end).
Qed.

Lemma cfg_cell : forall m lv, relro_clean m -> 4 <= lv <= 9 -> rw_cells psegs m (Z_CFG_TABLE + 16 * lv + 8) [C8 (wz Z_DEFLATE_SLOW)].
Proof.
  intros m lv RC H. apply cfg_cell_at; [exact RC|]. unfold Z_CFG_TABLE.
  assert (C : lv = 4 \/ lv = 5 \/ lv = 6 \/ lv = 7 \/ lv = 8 \/ lv = 9) by lia.
  destruct C as [-> |[-> |[-> |[-> |[-> | ->]]]]]; cbn; tauto.
Qed.

Section BLOCKSG.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : defl_ctx L inp rest0 lo r me.
Hypothesis HTFB : tr_flush_bits_stmt.
Hypothesis HSTO : deflate_stored_stmt.
Hypothesis HSLOW : deflate_slow_stmtg.

Lemma defl_lf0 : forall (Q : machine_state -> Prop) (X : deflate_state)
    (y1 y5 y6 y7 y10 y11 y13 y14 y15 y16 y17 y18 y19 y21 y22 y28 y29 y30 y31 : word) (m' : mem),
  DINV L rest0 lo r me X m' -> DKE L rest0 lo r F fc me Q (wz 0) (set_last_flush X (-1)) ->
  evt psegs Q (MS (deflR L flush r y1 y5 y6 y7 y10 y11 (wz 0) y13 y14 y15 y16 y17 y18 y19 y21 y22 y28 y29 y30 y31)
                  F (wz 0x17c74) fc None m' (seg_rom psegs)).
Proof.
  intros until m'. intros (DR & DOUT & ROOM & FR & STK & MU & WM & MI) HK.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp. apply box in SP16.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA. lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold deflR. unfold defl_frame in FR. unfold defl_W in MU.
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] m') as MUf. pose proof (wmono_refl psegs m') as WMf.
  zs. zs. name_mem mA.
  tr_groups MUf WMf.
  eapply HK.
  split; [split|].
  - exact ZS.
  - constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY1].
  - split; [apply (dout_munch _ m' mA L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|].
    split; [exact ROOM|]. split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.

Lemma defl_bstate : forall (Q : machine_state -> Prop) (X1 : deflate_state) (b : block_state)
    (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y21 y22 y28 y29 y30 y31 : word) (m : mem),
  DINV L rest0 lo r me X1 m -> 0 <= cs_avail_out (ds_strm X1) < 2^31 -> (flush = 0 \/ flush = 4 \/ flush = 5) ->
  (b = need_more -> cs_avail_out (ds_strm X1) = 0 -> DKL L flush rest0 lo r F fc me Q X1) ->
  (b = need_more -> cs_avail_out (ds_strm X1) <> 0 -> DKE L rest0 lo r F fc me Q (wz 0) X1) ->
  (b = finish_started -> cs_avail_out (ds_strm X1) = 0 -> DKL L flush rest0 lo r F fc me Q (set_status X1 FINISH_STATE)) ->
  (b = finish_started -> cs_avail_out (ds_strm X1) <> 0 -> DKE L rest0 lo r F fc me Q (wz 0) (set_status X1 FINISH_STATE)) ->
  (b = finish_done -> DK L flush rest0 lo r F fc me Q 0x17d24 (set_status X1 FINISH_STATE)) ->
  (b = block_done -> flush = 5 /\ fp_ok X1 /\ ds_lit_bufsize X1 = 16384
     /\ Box (length (cs_out_rev (ds_strm (flush_pending X1))) <= length rest0)%nat
     /\ 0 <= cs_avail_out (ds_strm (flush_pending X1)) < 2^31
     /\ (cs_avail_out (ds_strm (flush_pending X1)) = 0 -> DKE L rest0 lo r F fc me Q (wz 0) (set_last_flush (flush_pending X1) (-1)))
     /\ (cs_avail_out (ds_strm (flush_pending X1)) <> 0 -> DK L flush rest0 lo r F fc me Q 0x17d24 (flush_pending X1))) ->
  evt psegs Q (MS (deflR L flush r y1 y5 y6 y7 (wz (bs_code b)) y11 y12 y13 y14 y15 y16 y17 y18 y19 y21 y22 y28 y29 y30 y31)
                  F (wz 0x17c1c) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros DI RAO HFL KNM0 KNM1 KFS0 KFS1 KFD KBD.
  pose proof CTX as CTX'. destruct CTX' as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp.
  pose proof DI as (DR & DOUT & ROOM & FR & STK & MU & WM & MI).
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1]. open_A GA.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold deflR. unfold defl_frame in FR. unfold defl_W in MU.
  assert (C900 : forall (s2 : deflate_state) (z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z18 z19 z21 z22 z28 z29 z30 z31 : word) (mm : mem),
    DINV L rest0 lo r me s2 mm -> 0 <= cs_avail_out (ds_strm s2) < 2^31 ->
    (cs_avail_out (ds_strm s2) = 0 -> DKL L flush rest0 lo r F fc me Q s2) ->
    (cs_avail_out (ds_strm s2) <> 0 -> DKE L rest0 lo r F fc me Q (wz 0) s2) ->
    evt psegs Q (MS (deflR L flush r z1 z5 z6 z7 (wz (dl_S L)) z11 z12 z13 z14 z15 z16 z17 z18 z19 z21 z22 z28 z29 z30 z31)
                    F (wz 0x17c68) fc None mm (seg_rom psegs))).
  { intros s2 z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z18 z19 z21 z22 z28 z29 z30 z31 mm DI2 RA2 K0 K1.
    pose proof DI2 as DI0. destruct DI2 as (DR2 & _). destruct DR2 as [ZS2 _]. open_zs ZS2.
    unfold deflR. zs. zstep. if_cases KA0; zify_cond KA0; rewrite ?unsigned_lit in KA0 by lia.
    - zs. zs. eapply (K1 ltac:(lia)). exact DI0.
    - unfold DKL, deflR in K0. eapply (K0 ltac:(lia)). exact DI0. }
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] m) as MUf. pose proof (wmono_refl psegs m) as WMf.
  destruct b; cbn [bs_code].
  -
    do 4 zs. zstep. closed_br. zs. zstep. closed_br.
    eapply (C900 X1); [exact DI| exact RAO| apply KNM0; reflexivity| apply KNM1; reflexivity].
  -
    destruct (KBD eq_refl) as (F5 & FPOK & LBS & ROOMF & RAOF & KB0 & KB1).
    do 4 zs. zstep. closed_br. zs. zstep. closed_br. zs. zs. zstep. closed_br. zs.
    zstep. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia; [| exfalso; lia].
    zs.
    assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -64)) = bv_unsigned (r_sp r) + -64) by (apply unsigned_lit; lia).
    clear GA ZS GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend MUf WMf.
    zstep. call (flush_pending_spec HTFB L X1 rest0 (zlength inp) lo).
    1:{ exact (proj1 DI). } 1:{ exact DOUT. } 1:{ exact MI. } 1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
    1:{ exact IO. } 1:{ exact FPOK. } 1:{ rewrite LBS. reflexivity. } 1:{ exact RAO. } 1:{ exact (unbox _ ROOMF). } 1:{ reflexivity. }
    name_mem mD.
    lazymatch goal with H : stk psegs mD _ _ |- _ => rename H into STKF end. rewrite ESP in STKF.
    lazymatch goal with H : DREP mD L _ |- _ => rename H into DRF end.
    lazymatch goal with H : dout mD L _ _ |- _ => rename H into DOF end.
    assert (DIF : DINV L rest0 lo r me (flush_pending X1) mD).
    { split; [exact DRF|]. split; [exact DOF|]. split; [exact ROOMF|]. split; [exact FR|]. split; [exact STKF|]. split; [exact MU|]. split; [exact WM| eassumption]. }
    pose proof DRF as [ZSF _]. open_zs ZSF.
    zs. zs. zs. zstep. if_cases KA1; zify_cond KA1; rewrite ?unsigned_lit in KA1 by lia.
    +
      rewrite KA1. eapply (defl_lf0 Q (flush_pending X1)); [exact DIF| exact (KB0 KA1)].
    + unfold DK, deflR in KB1. eapply (KB1 ltac:(lia)). exact DIF.
  -
    do 4 zs. zstep. closed_br. zs. zs. name_mem mB.
    tr_groups MUf WMf.
    assert (DIB : DINV L rest0 lo r me (set_status X1 FINISH_STATE) mB).
    { split; [split|].
      - exact ZS.
      - constructor; [do 5 eexists; unfold dsA_cells, FINISH_STATE; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                     | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY1].
      - split; [dsred; apply (dout_munch _ m mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|].
        split; [exact ROOM|]. split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. }
    zs. zstep. closed_br.
    eapply (C900 (set_status X1 FINISH_STATE)); [exact DIB| exact RAO| apply KFS0; reflexivity| apply KFS1; reflexivity].
  -
    do 4 zs. zstep. closed_br. zs. zs. name_mem mB.
    tr_groups MUf WMf.
    assert (DIB : DINV L rest0 lo r me (set_status X1 FINISH_STATE) mB).
    { split; [split|].
      - exact ZS.
      - constructor; [do 5 eexists; unfold dsA_cells, FINISH_STATE; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                     | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY1].
      - split; [dsred; apply (dout_munch _ m mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|].
        split; [exact ROOM|]. split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. }
    zs. zstep. closed_br. zs. zs. zstep. closed_br.
    unfold DK, deflR in KFD. eapply (KFD eq_refl). exact DIB.
Qed.

Lemma defl_rung : forall (Q : machine_state -> Prop) (X : deflate_state),
  (flush = 0 \/ flush = 4 \/ flush = 5) -> (ds_level X = 0 \/ 4 <= ds_level X <= 9) -> 0 <= ds_strategy X <= 1 ->
  din_tie inp X -> ds_w_size X = 32768 -> ds_hash_size X = 32768 -> ds_lit_bufsize X = 16384 -> ds_wrap X <> 2 -> ds_wrap X <> 0 -> - 2 <= ds_wrap X <= 2 ->
  cs_avail_in (ds_strm X) < 2^31 -> 0 <= cs_avail_out (ds_strm X) < 2^31 ->
  (ds_level X = 0 -> st_entry X /\ ds_pending_buf_size X = 65536) -> (ds_level X <> 0 -> slow_safe X flush) ->
  Box (length (cs_out_rev (ds_strm (fst (dblk X flush)))) <= length rest0)%nat ->
  0 <= cs_avail_out (ds_strm (fst (dblk X flush))) < 2^31 ->
  (snd (dblk X flush) = need_more -> cs_avail_out (ds_strm (fst (dblk X flush))) = 0 -> DKL L flush rest0 lo r F fc me Q (fst (dblk X flush))) ->
  (snd (dblk X flush) = need_more -> cs_avail_out (ds_strm (fst (dblk X flush))) <> 0 -> DKE L rest0 lo r F fc me Q (wz 0) (fst (dblk X flush))) ->
  (snd (dblk X flush) = finish_started -> cs_avail_out (ds_strm (fst (dblk X flush))) = 0 -> DKL L flush rest0 lo r F fc me Q (set_status (fst (dblk X flush)) FINISH_STATE)) ->
  (snd (dblk X flush) = finish_started -> cs_avail_out (ds_strm (fst (dblk X flush))) <> 0 -> DKE L rest0 lo r F fc me Q (wz 0) (set_status (fst (dblk X flush)) FINISH_STATE)) ->
  (snd (dblk X flush) = finish_done -> DK L flush rest0 lo r F fc me Q 0x17d24 (set_status (fst (dblk X flush)) FINISH_STATE)) ->
  (snd (dblk X flush) = block_done -> flush = 5 /\ fp_ok (fst (dblk X flush)) /\ ds_lit_bufsize (fst (dblk X flush)) = 16384
     /\ Box (length (cs_out_rev (ds_strm (flush_pending (fst (dblk X flush))))) <= length rest0)%nat
     /\ 0 <= cs_avail_out (ds_strm (flush_pending (fst (dblk X flush)))) < 2^31
     /\ (cs_avail_out (ds_strm (flush_pending (fst (dblk X flush)))) = 0 -> DKE L rest0 lo r F fc me Q (wz 0) (set_last_flush (flush_pending (fst (dblk X flush))) (-1)))
     /\ (cs_avail_out (ds_strm (flush_pending (fst (dblk X flush)))) <> 0 -> DK L flush rest0 lo r F fc me Q 0x17d24 (flush_pending (fst (dblk X flush))))) ->
  DK L flush rest0 lo r F fc me Q 0x17bac X.
Proof.
  intros Q X HFL LV SG TIE WS HS LBS WR W0 WRG RAI RAO SE SAFE ROOMF RAO2 KNM0 KNM1 KFS0 KFS1 KFD KBD.
  unfold DK. intros until m'. intros DI. pose proof DI as (DR & DOUT & ROOM & FR & STK & MU & WM & MI). rename m' into m.
  pose proof CTX as CTX'. destruct CTX' as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp.
  assert (RL : relro_clean m) by (apply (defl_relro L inp rest0 lo r me CTX); exact MU).
  assert (DINm : din m L inp) by (apply (defl_din L inp rest0 lo r me CTX); exact MU).
  pose proof DR as DR0. destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA. lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold deflR. unfold defl_frame in FR. unfold defl_W in MU.
  assert (RLV : - 2^31 <= ds_level X < 2^31) by lia. assert (RSG : - 2^31 <= ds_strategy X < 2^31) by lia.
  assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -64)) = bv_unsigned (r_sp r) + -64) by (apply unsigned_lit; lia).
  assert (F05 : 0 <= flush <= 5) by lia.
  assert (AFTER : forall (mA : mem) (y1' y5' y6' y7' y11' y12' y13' y14' y15' y16' y17' y28' y29' y30' y31' : word),
    DINV L rest0 lo r me (fst (dblk X flush)) mA ->
    evt psegs Q (MS (deflR L flush r y1' y5' y6' y7' (wz (bs_code (snd (dblk X flush)))) y11' y12' y13' y14' y15' y16' y17' y18 y19 y21 y22 y28' y29' y30' y31')
                    F (wz 0x17c1c) fc None mA (seg_rom psegs))).
  { intros. eapply defl_bstate; eassumption. }
  zs. zstep. if_cases KL; zify_cond KL; rewrite ?signed_wz in KL by lia.
  -
    destruct (SE ltac:(lia)) as [SEN PBS].
    unfold dblk in *. replace (ds_level X =? 0) with true in * by (symmetry; apply Z.eqb_eq; lia).
    clear GA ZS GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend.
    zs. zstep. call (HSTO L X flush inp rest0 lo).
    1:{ exact DR0. } 1:{ exact DINm. } 1:{ exact TIE. } 1:{ exact DOUT. } 1:{ exact MI. } 1:{ rewrite ESP. exact STK. }
    1:{ rewrite ESP. unfold Z_STORED_STACK. lia. } 1:{ rewrite ESP. Z.div_mod_to_equations. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
    1:{ exact IO. } 1:{ exact SEN. } 1:{ exact F05. } 1:{ exact WS. } 1:{ exact LBS. } 1:{ exact PBS. } 1:{ exact WR. }
    1:{ exact RAI. } 1:{ exact RAO. } 1:{ exact (unbox _ ROOMF). } 1:{ reflexivity. } 1:{ reflexivity. }
    name_mem mA.
    lazymatch goal with H : stk psegs mA _ _ |- _ => rename H into STKA end. rewrite ESP in STKA.
    lazymatch goal with H : DREP mA L _ |- _ => rename H into DRA end.
    lazymatch goal with H : dout mA L _ _ |- _ => rename H into DOA end.
    zstep. apply AFTER.
    split; [exact DRA|]. split; [exact DOA|]. split; [exact ROOMF|]. split; [exact FR|]. split; [exact STKA|]. split; [exact MU|]. split; [exact WM| eassumption].
  -
    specialize (SAFE ltac:(lia)).
    unfold dblk in *. replace (ds_level X =? 0) with false in * by (symmetry; apply Z.eqb_neq; lia).
    zs. zs. zstep. if_cases KS3; zify_cond KS3; rewrite ?signed_wz in KS3 by lia; [exfalso; lia|].
    zs. zstep. if_cases KS2; zify_cond KS2; rewrite ?signed_wz in KS2 by lia; [| exfalso; lia].
    zs. zs. zs. zs.
    rewrite (Z.shiftl_mul_pow2 (ds_level X) 4) by lia. change (2^4) with 16.
    pose proof (cfg_cell m (ds_level X) RL ltac:(lia)) as CFG. unfold Z_CFG_TABLE, Z_DEFLATE_SLOW in CFG.
    replace (168504 + 16 * ds_level X + 8) with (168504 + ds_level X * 16 + 8) in CFG by lia.
    zs. zs.
    clear GA ZS GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend CFG.
    zstep. call (HSLOW L X flush inp rest0 lo).
    1:{ exact DR0. } 1:{ exact DINm. } 1:{ exact TIE. } 1:{ exact DOUT. } 1:{ exact MI. } 1:{ exact RL. } 1:{ rewrite ESP. exact STK. }
    1:{ rewrite ESP. unfold Z_SLOW_STACK. lia. } 1:{ rewrite ESP. Z.div_mod_to_equations. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
    1:{ exact IO. } 1:{ exact SAFE. } 1:{ exact F05. } 1:{ exact WS. } 1:{ exact HS. } 1:{ exact LBS. } 1:{ exact WR. } 1:{ exact W0. } 1:{ exact WRG. }
    1:{ exact RAI. } 1:{ exact RAO. } 1:{ exact (unbox _ ROOMF). } 1:{ reflexivity. } 1:{ reflexivity. }
    name_mem mA.
    lazymatch goal with H : stk psegs mA _ _ |- _ => rename H into STKA end. rewrite ESP in STKA.
    lazymatch goal with H : DREP mA L _ |- _ => rename H into DRA end.
    lazymatch goal with H : dout mA L _ _ |- _ => rename H into DOA end.
    apply AFTER.
    split; [exact DRA|]. split; [exact DOA|]. split; [exact ROOMF|]. split; [exact FR|]. split; [exact STKA|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.
Lemma defl_blk98g : forall (Q : machine_state -> Prop) (X : deflate_state),
  (flush = 0 \/ flush = 4 \/ flush = 5) -> cs_avail_in (ds_strm X) = 0 -> 0 <= ds_lookahead X < 2^31 -> 0 <= ds_status X < 1000 ->
  (negb (ds_lookahead X =? 0) || (negb (flush =? Z_NO_FLUSH) && negb (ds_status X =? FINISH_STATE)) = true -> DK L flush rest0 lo r F fc me Q 0x17bac X) ->
  (negb (ds_lookahead X =? 0) || (negb (flush =? Z_NO_FLUSH) && negb (ds_status X =? FINISH_STATE)) = false -> flush = 0 -> DKE L rest0 lo r F fc me Q (wz 0) X) ->
  (negb (ds_lookahead X =? 0) || (negb (flush =? Z_NO_FLUSH) && negb (ds_status X =? FINISH_STATE)) = false -> flush <> 0 -> DK L flush rest0 lo r F fc me Q 0x17d24 X) ->
  DK L flush rest0 lo r F fc me Q 0x17ba4 X.
Proof.
  intros Q X HFL AI0 RLA RST KRUN KOK KFIN. unfold DK. intros until m'. intros DI.
  pose proof DI as DI0. destruct DI as (DR & _). destruct DR as [_ ST]. destruct ST as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. open_A GA.
  unfold deflR. unfold Z_NO_FLUSH, FINISH_STATE in *.
  zs. zstep. if_cases KLA; zify_cond KLA; rewrite ?unsigned_lit in KLA by lia.
  -
    replace (ds_lookahead X =? 0) with true in * by (symmetry; apply Z.eqb_eq; lia). cbn [negb orb] in *.
    zstep. if_cases KF0; zify_cond KF0; rewrite ?unsigned_lit in KF0 by lia.
    + assert (F0 : flush = 0) by lia. replace (flush =? 0) with true in * by (symmetry; apply Z.eqb_eq; lia). cbn [negb andb] in *.
      zs. zs. eapply (KOK eq_refl F0). exact DI0.
    + assert (F4 : flush <> 0) by lia. replace (flush =? 0) with false in * by (symmetry; apply Z.eqb_neq; lia). cbn [negb andb] in *.
      zs. zs. zstep. if_cases KS; zify_cond KS; rewrite ?unsigned_lit in KS by lia.
      * replace (ds_status X =? 666) with false in * by (symmetry; apply Z.eqb_neq; lia). cbn [negb] in *.
        unfold DK, deflR in KRUN. eapply (KRUN eq_refl). exact DI0.
      * replace (ds_status X =? 666) with true in * by (symmetry; apply Z.eqb_eq; lia). cbn [negb] in *.
        zs. unfold DK, deflR in KFIN. eapply (KFIN eq_refl F4). exact DI0.
  - replace (ds_lookahead X =? 0) with false in * by (symmetry; apply Z.eqb_neq; lia). cbn [negb orb] in *.
    unfold DK, deflR in KRUN. eapply (KRUN eq_refl). exact DI0.
Qed.

Lemma defl_blk90g : forall (Q : machine_state -> Prop) (X : deflate_state),
  0 <= cs_avail_in (ds_strm X) < 2^31 ->
  (cs_avail_in (ds_strm X) <> 0 -> DK L flush rest0 lo r F fc me Q 0x17bac X) ->
  (cs_avail_in (ds_strm X) = 0 -> DK L flush rest0 lo r F fc me Q 0x17ba4 X) ->
  DK L flush rest0 lo r F fc me Q 0x17b9c X.
Proof.
  intros Q X RAI KRUN K98. unfold DK. intros until m'. intros DI.
  pose proof DI as DI0. destruct DI as (DR & _). destruct DR as [ZS _]. open_zs ZS.
  unfold deflR. zs. zstep. if_cases KAI; zify_cond KAI; rewrite ?unsigned_lit in KAI by lia.
  - unfold DK, deflR in KRUN. eapply (KRUN ltac:(lia)). exact DI0.
  - unfold DK, deflR in K98. eapply (K98 ltac:(lia)). exact DI0.
Qed.
End BLOCKSG.
