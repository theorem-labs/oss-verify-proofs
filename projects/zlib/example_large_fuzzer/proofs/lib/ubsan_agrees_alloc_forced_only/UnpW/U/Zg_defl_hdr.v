(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_defl_model.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Z_defl_kit Z_defl_arms Z_putmsb Z_flushpend Z_adler32 Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate SendModel FillWinModel DeflateSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hflags (X : deflate_state) : Z :=
  if ds_level X <? 2 then 0 else if ds_level X <? 6 then 1 else if ds_level X =? 6 then 2 else 3.
(* [comment removed for export] *)
Definition hw0 (f : Z) : Z := if f =? 0 then 30721 else if f =? 1 then 30814 else if f =? 2 then 30876 else 30938.
Definition hw1 (f : Z) : Z := if f =? 0 then 30783 else if f =? 1 then 30845 else if f =? 2 then 30907 else 30969.
(* [comment removed for export] *)
Definition hdr_fin (s3 : deflate_state) : deflate_state := set_status (set_strm s3 (cset_adler (ds_strm s3) adler32_init)) BUSY_STATE.

Lemma hflags_range : forall X, hflags X = 0 \/ hflags X = 1 \/ hflags X = 2 \/ hflags X = 3.
Proof. intros X. unfold hflags. destruct (_ <? 2); [tauto|]. destruct (_ <? 6); [tauto|]. destruct (_ =? 6); tauto. Qed.

Lemma zhdr_eqgU : forall s, ds_w_bits s = 15 -> 0 <= ds_strategy s <= 1 ->
  zhdr_st s = hdr_fin (if ds_strstart s =? 0 then putShortMSB s (hw0 (hflags s)) else put_adler (putShortMSB s (hw1 (hflags s)))).
Proof.
  intros s WB SG. unfold zhdr_st, hdr_fin, put_adler. rewrite WB.
  replace (Z_HUFFMAN_ONLY <=? ds_strategy s) with false by (symmetry; apply Z.leb_gt; unfold Z_HUFFMAN_ONLY; lia). cbn [orb].
  replace (if ds_level s <? 2 then 0 else if ds_level s <? 6 then 1 else if ds_level s =? 6 then 2 else 3) with (hflags s) by reflexivity.
  cbv zeta. change (ds_strstart (putShortMSB s ?h)) with (ds_strstart s).
  destruct (hflags_range s) as [E|[E|[E|E]]]; rewrite E;
    destruct (ds_strstart s =? 0); cbn [negb]; cbv beta iota; unfold hw0, hw1; cbn [Z.eqb Pos.eqb];
    lazymatch goal with |- context [putShortMSB s (?a + (31 - ?b mod 31))] =>
      let v := eval vm_compute in (a + (31 - b mod 31)) in change (a + (31 - b mod 31)) with v end;
    reflexivity.
Qed.

(* [comment removed for export] *)
Lemma psm_facts : forall Y b, ds_strstart (putShortMSB Y b) = ds_strstart Y /\ ds_pending (putShortMSB Y b) = ds_pending Y + 1 + 1
                            /\ ds_strm (putShortMSB Y b) = ds_strm Y /\ ds_lit_bufsize (putShortMSB Y b) = ds_lit_bufsize Y.
Proof. intros Y b. unfold putShortMSB, put_byte. dsred. repeat split; reflexivity. Qed.

Section HDRG.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : defl_ctx L inp rest0 lo r me.
Hypothesis HTFB : tr_flush_bits_stmt.

(* [comment removed for export] *)
Lemma hdr_tailg : forall (Q : machine_state -> Prop) (X1 XH : deflate_state)
    (z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 : word) (mB : mem),
  XH = hdr_fin (if ds_strstart X1 =? 0 then X1 else put_adler X1) ->
  0 <= ds_strstart X1 < 2^31 -> 0 <= ds_pending X1 -> ds_pending X1 + 4 <= 65536 -> ds_lit_bufsize X1 = 16384 ->
  0 <= cs_adler (ds_strm X1) < 2^64 -> 0 <= cs_avail_out (ds_strm X1) < 2^31 ->
  fp_ok XH -> ds_status (flush_pending XH) = 113 -> 0 <= ds_pending (flush_pending XH) < 2^64 ->
  Box (length (cs_out_rev (ds_strm (flush_pending XH))) <= length rest0)%nat ->
  (ds_pending (flush_pending XH) <> 0 -> DKL L flush rest0 lo r F fc me Q (flush_pending XH)) ->
  (ds_pending (flush_pending XH) = 0 -> DK L flush rest0 lo r F fc me Q 0x18068 (flush_pending XH)) ->
  DINV L rest0 lo r me X1 mB ->
  evt usegs Q (MS (deflR L flush r z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31)
                  F (wz 0x17440) fc None mB (seg_rom usegs)).
Proof.
  intros until mB. intros EH RSS RP0 RP4 LBS RAD RAO FPOK STF RPF ROOMF KL K90 (DR1 & DOUT1 & ROOM1 & (j0 & FR) & STK & MU & WM & MI1).
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp. apply box in SP16.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -64)) = bv_unsigned (r_sp r) + -64) by (apply unsigned_lit; lia).
  unfold deflR. unfold defl_frame in FR. unfold defl_W in MU.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_Ab L, dl_Ab L + 65536)] mB) as MUf. pose proof (wmono_refl usegs mB) as WMf.
  (* [comment removed for export] *)
  assert (C_F7C : forall (s3 : deflate_state) (w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 : word) (mm : mem),
    XH = hdr_fin s3 -> ds_lit_bufsize s3 = 16384 -> 0 <= cs_avail_out (ds_strm s3) < 2^31 ->
    DINV L rest0 lo r me s3 mm ->
    evt usegs Q (MS (deflR L flush r w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31)
                    F (wz 0x17468) fc None mm (seg_rom usegs))).
  { clear FR STK MU WM MUf WMf DOUT1 ROOM1 DR1 MI1 EH.
    intros s3 w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 mm EH3 LBS3 RAO3 (DR3 & DOUT3 & ROOM3 & (j03 & FR3) & STK3 & MU3 & WM3 & MI3).
    destruct DR3 as [ZS3 ST3]. destruct ST3 as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS3 LAY3].
    open_zs ZS3. open_A GA.
    unfold deflR. unfold defl_frame in FR3. unfold defl_W in MU3. unfold hdr_fin in EH3.
    do 3 zs. zstep.
    remember (wz (bv_unsigned (r_sp r) + -64)) as spw eqn:Espw.
    pose proof (munch_refl [(lo, bv_unsigned spw); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + 212)] mm) as MUf. pose proof (wmono_refl usegs mm) as WMf.
    call (adler32_null_spec lo 0 0).
    1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact MI3. } 1:{ rewrite ESP. exact STK3. } 1:{ rewrite ESP. unfold ADLER32_FRAME. lia. }
    lazymatch goal with H : stk usegs _ lo (bv_unsigned spw) |- _ => rewrite ESP in H; rename H into STKA end.
    lazymatch goal with H : mem_inv usegs _ |- _ => rename H into MIA end.
    subst spw.
    do 5 zs.
    name_mem mC. tr_groups MUf WMf.
    assert (DRH : DREP mC L XH).
    { rewrite EH3. split.
      - dsred. do 4 eexists. unfold zs_call_cells, zs_priv_cells, adler32_init. cbn [app]. dsred. close_cells ZS3.
      - constructor; [do 5 eexists; unfold dsA_cells, BUSY_STATE; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                     | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS3 | exact LAY3]. }
    assert (DOH : dout mC L rest0 (ds_strm XH)).
    { rewrite EH3. dsred. apply (dout_munch _ mm mC L rest0 _ DOUT3 ROOM3 MUf WMf); cbn [disjoint_from]; slia. }
    clear ZS3 GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend MUf WMf.
    call (flush_pending_spec HTFB L XH rest0 (zlength inp) lo).
    1:{ exact DRH. } 1:{ exact DOH. } 1:{ exact MIA. } 1:{ rewrite ESP. exact STKA. } 1:{ rewrite ESP. lia. } 1:{ unfold dlay_below. rewrite ESP. lia. }
    1:{ exact IO. } 1:{ exact FPOK. } 1:{ rewrite EH3. dsred. rewrite LBS3. reflexivity. } 1:{ rewrite EH3. dsred. exact RAO3. }
    1:{ exact (unbox _ ROOMF). } 1:{ reflexivity. }
    name_mem mD.
    lazymatch goal with H : stk usegs mD _ _ |- _ => rewrite ?ESP in H; rename H into STKF end.
    lazymatch goal with H : DREP mD L _ |- _ => rename H into DRF end.
    lazymatch goal with H : dout mD L _ _ |- _ => rename H into DOF end.
    lazymatch goal with H : mem_inv usegs mD |- _ => rename H into MIF end.
    assert (DIF : DINV L rest0 lo r me (flush_pending XH) mD).
    { split; [exact DRF|]. split; [exact DOF|]. split; [exact ROOMF|]. split; [eexists; exact FR3|]. split; [exact STKF|]. split; [exact MU3|]. split; [exact WM3| exact MIF]. }
    destruct DRF as [_ STF']. destruct STF' as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. open_A GA.
    assert (RSTF : - 2^31 <= ds_status (flush_pending XH) < 2^31) by lia.
    zs. zstep. if_cases KP; zify_cond KP; rewrite ?unsigned_lit in KP by lia.
    - unfold DKL, DK, Z_DEFL_LF, deflR in KL. eapply (KL ltac:(lia)). exact DIF.
    - zs. rewrite STF. zs.
      zs. zstep. closed_br. zs. zstep. closed_br. zs. zstep. closed_br. zs. zstep. closed_br. zstep.
      unfold DK, deflR in K90. eapply (K90 ltac:(lia)). exact DIF. }
  pose proof DR1 as DR1'. destruct DR1' as [ZS1 ST1]. destruct ST1 as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. open_A GA. open_zs ZS1.
  assert (RSS1 : - 2^31 <= ds_strstart X1 < 2^31) by lia.
  destruct (Z.eq_dec (ds_strstart X1) 0) as [SS0|SSN].
  - (* [comment removed for export] *)
    replace (ds_strstart X1 =? 0) with true in EH by (symmetry; apply Z.eqb_eq; exact SS0). cbv iota in EH.
    zs. rewrite SS0. zstep. if_cases KS; zify_cond KS; rewrite ?unsigned_lit in KS by lia; [| exfalso; lia]. clear KS GA ZS1.
    eapply (C_F7C X1); [exact EH| exact LBS| exact RAO|].
    split; [exact DR1|]. split; [exact DOUT1|]. split; [exact ROOM1|]. split; [eexists; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| exact MI1].
  - (* [comment removed for export] *)
    replace (ds_strstart X1 =? 0) with false in EH by (symmetry; apply Z.eqb_neq; exact SSN). cbv iota in EH.
    zs. zstep. if_cases KS; zify_cond KS; rewrite ?unsigned_lit in KS by lia; [exfalso; lia|]. clear KS.
    (* [comment removed for export] *)
    zs. zstep. zstep. zs. zstep. clear GA ZS1.
    call (putShortMSB_spec L X1 (wrap32 (Z.shiftr (cs_adler (ds_strm X1)) 16)) (bv_swrap 32 (Z.shiftr (cs_adler (ds_strm X1)) 16 + 0)) lo).
    1:{ exact DR1. } 1:{ exact MI1. } 1:{ unfold dlay_below. rewrite ESP. lia. } 1:{ rewrite ESP. lia. } 1:{ lia. } 1:{ lia. }
    1:{ apply wrap32_range. } 1:{ rewrite swrap32_mod32, Z.add_0_r, wrap32_mod. reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
    name_mem mB2.
    lazymatch goal with H : DREP mB2 L _ |- _ => rename H into DR2 end.
    lazymatch goal with H : mem_inv usegs mB2 |- _ => rename H into MI2 end.
    remember (putShortMSB X1 (wrap32 (Z.shiftr (cs_adler (ds_strm X1)) 16))) as X2 eqn:EX2.
    destruct (psm_facts X1 (wrap32 (Z.shiftr (cs_adler (ds_strm X1)) 16))) as (S2 & P2 & T2 & B2). rewrite <- EX2 in S2, P2, T2, B2.
    pose proof DR2 as DR2'. destruct DR2' as [ZS2 _]. open_zs ZS2. rewrite T2 in ZS2.
    (* [comment removed for export] *)
    rd_lo2 ZS2 96%nat. zstep. zs. zstep. unfold zx16. clear ZS2 RD.
    call (putShortMSB_spec L X2 (Z.land (cs_adler (ds_strm X1)) 65535) (bv_unsigned (wz (cs_adler (ds_strm X1))) mod 2^16) lo).
    1:{ exact DR2. } 1:{ exact MI2. } 1:{ unfold dlay_below. rewrite ESP. lia. } 1:{ rewrite ESP. lia. } 1:{ lia. } 1:{ lia. }
    1:{ change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound (cs_adler (ds_strm X1)) (2^16) ltac:(lia)). lia. }
    1:{ rewrite unsigned_lit by lia. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
        apply Z.mod_small. pose proof (Z.mod_pos_bound (cs_adler (ds_strm X1)) (2^16) ltac:(lia)). lia. }
    1:{ reflexivity. } 1:{ reflexivity. }
    name_mem mB3.
    lazymatch goal with H : DREP mB3 L _ |- _ => rename H into DR3 end.
    lazymatch goal with H : mem_inv usegs mB3 |- _ => rename H into MI3 end.
    remember (putShortMSB X2 (Z.land (cs_adler (ds_strm X1)) 65535)) as X3 eqn:EX3.
    destruct (psm_facts X2 (Z.land (cs_adler (ds_strm X1)) 65535)) as (S3 & P3 & T3 & B3). rewrite <- EX3 in S3, P3, T3, B3.
    assert (EQ3 : X3 = put_adler X1) by (rewrite EX3, EX2; unfold put_adler; reflexivity).
    eapply (C_F7C X3); [rewrite EH, <- EQ3; reflexivity| rewrite B3, B2; exact LBS| rewrite T3, T2; exact RAO|].
    split; [exact DR3|]. split; [rewrite T3, T2; apply (dout_munch _ mB mB3 L rest0 _ DOUT1 ROOM1 MUf WMf); cbn [disjoint_from]; slia|].
    split; [rewrite T3, T2; exact ROOM1|]. split; [eexists; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| exact MI3].
Qed.

(* [comment removed for export] *)
Lemma defl_hdrg : forall (Q : machine_state -> Prop) (X : deflate_state),
  ds_wrap X = 1 -> ds_w_bits X = 15 -> 0 <= ds_level X <= 9 -> 0 <= ds_strategy X <= 1 ->
  0 <= ds_strstart X < 2^31 -> 0 <= ds_pending X -> ds_pending X + 6 <= 65536 -> ds_lit_bufsize X = 16384 ->
  0 <= cs_adler (ds_strm X) < 2^64 -> 0 <= cs_avail_out (ds_strm X) < 2^31 ->
  fp_ok (zhdr_st X) -> ds_status (flush_pending (zhdr_st X)) = 113 -> 0 <= ds_pending (flush_pending (zhdr_st X)) < 2^64 ->
  Box (length (cs_out_rev (ds_strm (flush_pending (zhdr_st X)))) <= length rest0)%nat ->
  (ds_pending (flush_pending (zhdr_st X)) <> 0 -> DKL L flush rest0 lo r F fc me Q (flush_pending (zhdr_st X))) ->
  (ds_pending (flush_pending (zhdr_st X)) = 0 -> DK L flush rest0 lo r F fc me Q 0x18068 (flush_pending (zhdr_st X))) ->
  DKS L flush rest0 lo r F fc me Q 0x173b0 X.
Proof.
  intros Q X WR WB LV SG RSS RP0 RP6 LBS RAD RAO FPOK STF RPF ROOMF KL K90.
  unfold DKS. intros until m'. intros (DR & DOUT & ROOM & (j0 & FR) & STK & MU & WM & MI).
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp. apply box in SP16.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (zhdr_eqgU X WB SG) as EH.
  pose proof DR as DR0.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -64)) = bv_unsigned (r_sp r) + -64) by (apply unsigned_lit; lia).
  unfold deflR. unfold defl_frame in FR. unfold defl_W in MU.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_Ab L, dl_Ab L + 65536)] m') as MUf. pose proof (wmono_refl usegs m') as WMf.
  assert (RW : - 2^31 <= ds_wrap X < 2^31) by lia. assert (RWB : - 2^31 <= ds_w_bits X < 2^31) by lia.
  assert (RLV : - 2^31 <= ds_level X < 2^31) by lia. assert (RSG : - 2^31 <= ds_strategy X < 2^31) by lia.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (CALLK : forall (h : Z) (X1 : deflate_state) (v5 v6 v7 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 : word),
    X1 = putShortMSB X h -> zhdr_st X = hdr_fin (if ds_strstart X =? 0 then X1 else put_adler X1) -> 0 <= h < 2^32 ->
    evt usegs Q (MS (deflR L flush r (wz 0x17440) v5 v6 v7 (wz (dl_As L)) (wz h) v12 v13 v14 v15 v16 v17 v28 v29 v30 v31)
                    F (wz Z_PUTSHORTMSB) fc None m' (seg_rom usegs))).
  { intros h X1 v5 v6 v7 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 EX1 EHX Rh4. unfold deflR. clear GA.
    call (putShortMSB_spec L X h h lo).
    1:{ exact DR0. } 1:{ exact MI. } 1:{ unfold dlay_below. rewrite ESP. lia. } 1:{ rewrite ESP. lia. } 1:{ lia. } 1:{ lia. } 1:{ exact Rh4. }
    1:{ apply Z.mod_small. exact Rh4. } 1:{ reflexivity. } 1:{ reflexivity. }
    name_mem mB.
    lazymatch goal with H : DREP mB L _ |- _ => rename H into DR1 end.
    lazymatch goal with H : mem_inv usegs mB |- _ => rename H into MI1 end.
    destruct (psm_facts X h) as (S1 & P1 & T1 & B1). rewrite <- EX1 in S1, P1, T1, B1, DR1.
    eapply (hdr_tailg Q X1 (zhdr_st X));
      [ rewrite S1; exact EHX
      | rewrite S1; lia | lia | lia | rewrite B1; exact LBS | rewrite T1; exact RAD | rewrite T1; exact RAO
      | exact FPOK | exact STF | exact RPF | exact ROOMF | exact KL | exact K90 |].
    split; [exact DR1|]. split; [rewrite T1; apply (dout_munch _ m' mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|].
    split; [rewrite T1; exact ROOM|]. split; [eexists; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| exact MI1]. }
  unfold deflR in CALLK.
  (* [comment removed for export] *)
  assert (JN : forall (c : Z) (v12 : word), c = 64 * hflags X ->
    evt usegs Q (MS (deflR L flush r y1 y5 y6 y7 (wz 30720) (wz c) v12 (wz 1) y14 y15 y16 y17 y28 y29 y30 y31)
                    F (wz 0x173e8) fc None m' (seg_rom usegs))).
  { intros c v12 Ec. unfold deflR.
    destruct (Z.eq_dec (ds_strstart X) 0) as [SS0|SSN].
    - replace (ds_strstart X =? 0) with true in EH by (symmetry; apply Z.eqb_eq; exact SS0). cbv iota in EH.
      destruct (hflags_range X) as [E|[E|[E|E]]]; rewrite E in Ec, EH; subst c; cbn [Z.mul]; unfold hw0 in EH; cbn [Z.eqb Pos.eqb] in EH.
      all: (zstep; zs; rewrite SS0; do 3 zs; zstep; change (Z.b2z (0 <? 0)) with 0; do 14 zs; zs; zstep).
      all: (eapply CALLK; [ reflexivity | replace (ds_strstart X =? 0) with true by (symmetry; apply Z.eqb_eq; exact SS0); exact EH | lia ]).
    - replace (ds_strstart X =? 0) with false in EH by (symmetry; apply Z.eqb_neq; exact SSN). cbv iota in EH.
      destruct (hflags_range X) as [E|[E|[E|E]]]; rewrite E in Ec, EH; subst c; cbn [Z.mul]; unfold hw1 in EH; cbn [Z.eqb Pos.eqb] in EH.
      all: (zstep; zs; do 3 zs; zstep; replace (0 <? ds_strstart X) with true by (symmetry; apply Z.ltb_lt; lia); change (Z.b2z true) with 1; do 14 zs; zs; zstep).
      all: (eapply CALLK; [ reflexivity | replace (ds_strstart X =? 0) with false by (symmetry; apply Z.eqb_neq; exact SSN); exact EH | lia ]). }
  (* [comment removed for export] *)
  zs. zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia; [exfalso; lia|]. clear K1.
  zs. zs. zs. rewrite WB. zs. zs. zs. zs. zstep. if_cases KSG; zify_cond KSG; rewrite ?signed_wz, ?unsigned_lit in KSG by lia; try (exfalso; lia).
  zs. zs. zstep. if_cases KL2; zify_cond KL2; rewrite ?signed_wz, ?unsigned_lit in KL2 by lia.
  1: zs; zstep; if_cases KL6; zify_cond KL6; rewrite ?signed_wz, ?unsigned_lit in KL6 by lia.
  1: zstep; if_cases KE6; zify_cond KE6; rewrite ?signed_wz, ?unsigned_lit in KE6 by lia.
  (* [comment removed for export] *)
  1: zs; zstep. 2: zs; zstep. 3: zs; zstep. 4: zs.
  all: apply JN; unfold hflags;
       destruct (Z.ltb_spec (ds_level X) 2); try lia; destruct (Z.ltb_spec (ds_level X) 6); try lia; destruct (Z.eqb_spec (ds_level X) 6); lia.
Qed.
End HDRG.
