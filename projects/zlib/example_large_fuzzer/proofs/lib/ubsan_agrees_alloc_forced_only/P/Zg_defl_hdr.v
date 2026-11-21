(* [comment removed for export] *)


From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Z_defl_model Z_defl_kit Z_defl_arms Z_defl_put4 Z_flushpend Z_adler32.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate SendModel FillWinModel DeflateSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition hflags (X : deflate_state) : Z :=
  if ds_level X <? 2 then 0 else if ds_level X <? 6 then 1 else if ds_level X =? 6 then 2 else 3.
Definition hb0 (f : Z) : Z := if f =? 0 then 1 else if f =? 1 then 94 else if f =? 2 then 156 else 218.
Definition hb1 (f : Z) : Z := if f =? 0 then 63 else if f =? 1 then 125 else if f =? 2 then 187 else 249.

Lemma hflags_range : forall X, hflags X = 0 \/ hflags X = 1 \/ hflags X = 2 \/ hflags X = 3.
Proof. intros X. unfold hflags. destruct (_ <? 2); [tauto|]. destruct (_ <? 6); [tauto|]. destruct (_ =? 6); tauto. Qed.

Lemma zhdr_eqg : forall s, ds_w_bits s = 15 -> 0 <= ds_strategy s <= 1 ->
  zhdr_st s =
  (let s2 := put_byte (put_byte s 120) (if ds_strstart s =? 0 then hb0 (hflags s) else hb1 (hflags s)) in
   let s3 := if ds_strstart s =? 0 then s2 else put_adler s2 in
   set_status (set_strm s3 (cset_adler (ds_strm s3) adler32_init)) BUSY_STATE).
Proof.
  intros s WB SG. unfold zhdr_st. rewrite WB.
  replace (Z_HUFFMAN_ONLY <=? ds_strategy s) with false by (symmetry; apply Z.leb_gt; unfold Z_HUFFMAN_ONLY; lia). cbn [orb].
  replace (if ds_level s <? 2 then 0 else if ds_level s <? 6 then 1 else if ds_level s =? 6 then 2 else 3) with (hflags s) by reflexivity.
  destruct (hflags_range s) as [E|[E|[E|E]]]; rewrite E; cbv zeta;
    change (ds_strstart (putShortMSB s ?h)) with (ds_strstart s);
    destruct (ds_strstart s =? 0); cbn [negb]; cbv beta iota; unfold hb0, hb1; cbn [Z.eqb Pos.eqb];
    [ change (Z.lor (Z.shiftl (Z_DEFLATED + Z.shiftl (15 - 8) 4) 8) (Z.shiftl 0 6)) with 30720;
      change (30720 + (31 - 30720 mod 31)) with 30721; unfold putShortMSB; change (Z.shiftr 30721 8) with 120; change (Z.land 30721 255) with 1; reflexivity
    | change (Z.lor (Z.shiftl (Z_DEFLATED + Z.shiftl (15 - 8) 4) 8) (Z.shiftl 0 6)) with 30720;
      change (Z.lor 30720 PRESET_DICT + (31 - Z.lor 30720 PRESET_DICT mod 31)) with 30783; unfold put_adler; unfold putShortMSB at 5;
      change (Z.shiftr 30783 8) with 120; change (Z.land 30783 255) with 63; reflexivity
    | change (Z.lor (Z.shiftl (Z_DEFLATED + Z.shiftl (15 - 8) 4) 8) (Z.shiftl 1 6)) with 30784;
      change (30784 + (31 - 30784 mod 31)) with 30814; unfold putShortMSB; change (Z.shiftr 30814 8) with 120; change (Z.land 30814 255) with 94; reflexivity
    | change (Z.lor (Z.shiftl (Z_DEFLATED + Z.shiftl (15 - 8) 4) 8) (Z.shiftl 1 6)) with 30784;
      change (Z.lor 30784 PRESET_DICT + (31 - Z.lor 30784 PRESET_DICT mod 31)) with 30845; unfold put_adler; unfold putShortMSB at 5;
      change (Z.shiftr 30845 8) with 120; change (Z.land 30845 255) with 125; reflexivity
    | change (Z.lor (Z.shiftl (Z_DEFLATED + Z.shiftl (15 - 8) 4) 8) (Z.shiftl 2 6)) with 30848;
      change (30848 + (31 - 30848 mod 31)) with 30876; unfold putShortMSB; change (Z.shiftr 30876 8) with 120; change (Z.land 30876 255) with 156; reflexivity
    | change (Z.lor (Z.shiftl (Z_DEFLATED + Z.shiftl (15 - 8) 4) 8) (Z.shiftl 2 6)) with 30848;
      change (Z.lor 30848 PRESET_DICT + (31 - Z.lor 30848 PRESET_DICT mod 31)) with 30907; unfold put_adler; unfold putShortMSB at 5;
      change (Z.shiftr 30907 8) with 120; change (Z.land 30907 255) with 187; reflexivity
    | change (Z.lor (Z.shiftl (Z_DEFLATED + Z.shiftl (15 - 8) 4) 8) (Z.shiftl 3 6)) with 30912;
      change (30912 + (31 - 30912 mod 31)) with 30938; unfold putShortMSB; change (Z.shiftr 30938 8) with 120; change (Z.land 30938 255) with 218; reflexivity
    | change (Z.lor (Z.shiftl (Z_DEFLATED + Z.shiftl (15 - 8) 4) 8) (Z.shiftl 3 6)) with 30912;
      change (Z.lor 30912 PRESET_DICT + (31 - Z.lor 30912 PRESET_DICT mod 31)) with 30969; unfold put_adler; unfold putShortMSB at 5;
      change (Z.shiftr 30969 8) with 120; change (Z.land 30969 255) with 249; reflexivity ].
Qed.

Section HDRG.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : defl_ctx L inp rest0 lo r me.
Hypothesis HTFB : tr_flush_bits_stmt.

Lemma defl_hdrg : forall (Q : machine_state -> Prop) (X : deflate_state),
  ds_wrap X = 1 -> ds_w_bits X = 15 -> 0 <= ds_level X <= 9 -> 0 <= ds_strategy X <= 1 ->
  0 <= ds_strstart X < 2^31 -> 0 <= ds_pending X -> ds_pending X + 6 <= 65536 -> ds_lit_bufsize X = 16384 ->
  0 <= cs_adler (ds_strm X) < 2^64 -> 0 <= cs_avail_out (ds_strm X) < 2^31 ->
  fp_ok (zhdr_st X) -> ds_status (flush_pending (zhdr_st X)) = 113 -> 0 <= ds_pending (flush_pending (zhdr_st X)) < 2^64 ->
  Box (length (cs_out_rev (ds_strm (flush_pending (zhdr_st X)))) <= length rest0)%nat ->
  (ds_pending (flush_pending (zhdr_st X)) <> 0 -> DKL L flush rest0 lo r F fc me Q (flush_pending (zhdr_st X))) ->
  (ds_pending (flush_pending (zhdr_st X)) = 0 -> DK L flush rest0 lo r F fc me Q 0x17b9c (flush_pending (zhdr_st X))) ->
  DKH L flush rest0 lo r F fc me Q X.
Proof.
  intros Q X WR WB LV SG RSS RP0 RP6 LBS RAD RAO FPOK STF RPF ROOMF KL K90.
  unfold DKH. intros until m'. intros (DR & DOUT & ROOM & FR & STK & MU & WM & MI).
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp. apply box in SP16.
  pose proof (zhdr_eqg X WB SG) as EH. cbv zeta in EH.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_zs ZS. open_A GA. open_pend Gpend. pose proof (ln_pend _ LENS) as Lpend.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold deflR. unfold defl_frame in FR. unfold defl_W in MU.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_Ab L, dl_Ab L + 65536)] m') as MUf. pose proof (wmono_refl psegs m') as WMf.
  assert (RW : - 2^31 <= ds_wrap X < 2^31) by lia. assert (RWB : - 2^31 <= ds_w_bits X < 2^31) by lia.
  assert (RLV : - 2^31 <= ds_level X < 2^31) by lia. assert (RSG : - 2^31 <= ds_strategy X < 2^31) by lia.
  zs. zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia; [exfalso; lia|]. clear K1.
  zs. zs. zs. rewrite WB. zs. zs. zs. zs. zstep. if_cases KSG; zify_cond KSG; rewrite ?signed_wz in KSG by lia; [exfalso; lia|]. clear KSG.

  assert (C_D74 : forall (s3 : deflate_state) (z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z18 z19 z21 z22 z28 z29 z30 z31 : word) (mm : mem),
    zhdr_st X = set_status (set_strm s3 (cset_adler (ds_strm s3) adler32_init)) BUSY_STATE ->
    ds_lit_bufsize s3 = 16384 -> ds_strm s3 = ds_strm X ->
    DINV L rest0 lo r me s3 mm ->
    evt psegs Q (MS (deflR L flush r z1 z5 z6 z7 (wz (dl_S L)) z11 z12 z13 z14 z15 z16 z17 z18 z19 z21 z22 z28 z29 z30 z31)
                    F (wz 0x171d0) fc None mm (seg_rom psegs))).
  { clear GA Gpend ZS FR STK MU WM MUf WMf DOUT ROOM GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead LENS Lpend.
    intros s3 z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z18 z19 z21 z22 z28 z29 z30 z31 mm EH3 LBS3 ES3 (DR3 & DOUT3 & ROOM3 & FR3 & STK3 & MU3 & WM3 & MI3).
    destruct DR3 as [ZS3 ST3]. destruct ST3 as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS3 LAY3].
    open_zs ZS3. open_A GA.
    unfold deflR. unfold defl_frame in FR3. unfold defl_W in MU3.
    pose proof (munch_refl [(dl_S L, dl_S L + 112); (dl_As L, dl_As L + 212)] mm) as MUf. pose proof (wmono_refl psegs mm) as WMf.
    do 5 zs.
    call (adler32_null_spec).
    1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ eassumption. }
    do 5 zs.
    name_mem mC. tr_groups MUf WMf.
    assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -64)) = bv_unsigned (r_sp r) + -64) by (apply unsigned_lit; lia).
    assert (DRH : DREP mC L (zhdr_st X)).
    { rewrite EH3. split.
      - dsred. do 4 eexists. unfold zs_call_cells, zs_priv_cells, adler32_init. cbn [app]. dsred. close_cells ZS3.
      - constructor; [do 5 eexists; unfold dsA_cells, BUSY_STATE; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                     | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS3 | exact LAY3]. }
    assert (DOH : dout mC L rest0 (ds_strm (zhdr_st X))).
    { rewrite EH3. dsred. apply (dout_munch _ mm mC L rest0 _ DOUT3 ROOM3 MUf WMf); cbn [disjoint_from]; slia. }
    clear ZS3 GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend MUf WMf.
    call (flush_pending_spec HTFB L (zhdr_st X) rest0 (zlength inp) lo).
    1:{ exact DRH. } 1:{ exact DOH. } 1:{ eassumption. } 1:{ rewrite ESP. exact STK3. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
    1:{ exact IO. } 1:{ exact FPOK. } 1:{ rewrite EH3. dsred. rewrite LBS3. reflexivity. } 1:{ rewrite EH3. dsred. rewrite ES3. exact RAO. }
    1:{ exact (unbox _ ROOMF). } 1:{ reflexivity. }
    name_mem mD.
    lazymatch goal with H : stk psegs mD _ _ |- _ => rename H into STKF end. rewrite ESP in STKF.
    lazymatch goal with H : DREP mD L _ |- _ => rename H into DRF end.
    lazymatch goal with H : dout mD L _ _ |- _ => rename H into DOF end.
    assert (DIF : DINV L rest0 lo r me (flush_pending (zhdr_st X)) mD).
    { split; [exact DRF|]. split; [exact DOF|]. split; [exact ROOMF|]. split; [exact FR3|]. split; [exact STKF|]. split; [exact MU3|]. split; [exact WM3| eassumption]. }
    destruct DRF as [_ STF']. destruct STF' as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. open_A GA.
    assert (RSTF : - 2^31 <= ds_status (flush_pending (zhdr_st X)) < 2^31) by lia.
    zs. zstep. if_cases KP; zify_cond KP; rewrite ?unsigned_lit in KP by lia.
    - unfold DKL, deflR in KL. eapply (KL ltac:(lia)). exact DIF.
    - zs. rewrite STF. zs. zs.
      zs. zstep. closed_br. zs. zstep. closed_br. zs. zstep. closed_br. zs. zstep. closed_br. zs.
      unfold DK, deflR in K90. eapply (K90 ltac:(lia)). exact DIF. }

  assert (JN : forall (v14 : word),
    evt psegs Q (MS (deflR L flush r y1 y5 y6 y7 (wz (dl_S L)) (wz 30720) (wz (ds_pending X)) (wz (64 * hflags X)) v14 (wz 1) y16 y17 y18 y19 y21 y22 y28 y29 y30 y31)
                    F (wz 0x170d4) fc None m' (seg_rom psegs))).
  { intros v14. unfold deflR.
    destruct (Z.eq_dec (ds_strstart X) 0) as [SS0|SSN].
    - replace (ds_strstart X =? 0) with true in EH by (symmetry; apply Z.eqb_eq; exact SS0).
      destruct (hflags_range X) as [E|[E|[E|E]]]; rewrite E; cbn [Z.mul].
      all: do 5 zs.
      all: (rewrite SS0; do 6 zs; change (Z.b2z (0 <? 0)) with 0; zs).
      all: pb_store Gpend (ds_pending_buf X) 65536 (dl_Ab L) (ds_pending X) (wrap8 120) ltac:(vm_compute; reflexivity).
      all: do 18 zs.
      all: pb_store Gpend (arr_set (ds_pending_buf X) (ds_pending X) (wrap8 120)) 65536 (dl_Ab L) (ds_pending X + 1) (wrap8 (hb0 (hflags X))) ltac:(rewrite E; vm_compute; reflexivity).
      all: (zs; rewrite SS0; zstep; closed_br).
      all: (name_mem mB; tr_groups MUf WMf).
      all: (eapply (C_D74 (put_byte (put_byte X 120) (hb0 (hflags X)))); [exact EH| exact LBS| reflexivity|]).
      all: (split; [split; [ unfold put_byte; dsred; do 4 eexists; exact ZS
                           | unfold put_byte;
                             constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                                          | exact Gwin| exact Gprev| exact Ghead| unfold dpend; dsred; exact Gpend| close_lens_set LENS | exact LAY1] ]
                   | split; [unfold put_byte; dsred; apply (dout_munch _ m' mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|];
                     split; [unfold put_byte; dsred; exact ROOM|];
                     split; [exact FR|]; split; [exact STK|]; split; [exact MU|]; split; [exact WM| eassumption] ]).
    - replace (ds_strstart X =? 0) with false in EH by (symmetry; apply Z.eqb_neq; exact SSN).
      destruct (hflags_range X) as [E|[E|[E|E]]]; rewrite E; cbn [Z.mul].
      all: do 5 zs.
      all: (do 6 zs; replace (0 <? ds_strstart X) with true by (symmetry; apply Z.ltb_lt; lia); change (Z.b2z true) with 1; zs).
      all: pb_store Gpend (ds_pending_buf X) 65536 (dl_Ab L) (ds_pending X) (wrap8 120) ltac:(vm_compute; reflexivity).
      all: do 18 zs.
      all: pb_store Gpend (arr_set (ds_pending_buf X) (ds_pending X) (wrap8 120)) 65536 (dl_Ab L) (ds_pending X + 1) (wrap8 (hb1 (hflags X))) ltac:(rewrite E; vm_compute; reflexivity).
      all: (zs; zstep; if_cases KDI; zify_cond KDI; rewrite ?unsigned_lit in KDI by lia; [exfalso; lia|]; clear KDI).
      all: zs.
      all: (name_mem mB; tr_groups MUf WMf).
      all: (eapply (defl_put4 L flush inp rest0 lo r F fc me CTX Q (put_byte (put_byte X 120) (hb1 (hflags X))) 0x17160); [left; reflexivity| | | | |];
            [ split; [split; [ unfold put_byte; dsred; do 4 eexists; exact ZS
                             | unfold put_byte;
                               constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                                            | exact Gwin| exact Gprev| exact Ghead| unfold dpend; dsred; exact Gpend| close_lens_set LENS | exact LAY1] ]
                     | split; [unfold put_byte; dsred; apply (dout_munch _ m' mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|];
                       split; [unfold put_byte; dsred; exact ROOM|];
                       split; [exact FR|]; split; [exact STK|]; split; [exact MU|]; split; [exact WM| eassumption] ]
            | unfold put_byte; dsred; lia
            | unfold put_byte; dsred; lia
            | unfold put_byte; dsred; exact RAD
            | intros z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z18 z19 z21 z22 z28 z29 z30 z31 mm DI4;
              eapply (C_D74 (put_adler (put_byte (put_byte X 120) (hb1 (hflags X))))); [exact EH| unfold put_adler, putShortMSB, put_byte; dsred; exact LBS| reflexivity| exact DI4] ]). }

  zs. zs. zstep. if_cases KL2; zify_cond KL2; rewrite ?signed_wz in KL2 by lia.
  1: zs; zstep; if_cases KL6; zify_cond KL6; rewrite ?unsigned_lit in KL6 by lia.
  1: zstep; if_cases KE6; zify_cond KE6; rewrite ?unsigned_lit in KE6 by lia.

  1: zs; zs; zs. 2: zs; zs; zs; zs. 3: zs; zs. 4: zs.
  all: match goal with |- evt _ _ (MS (TNode (TNode _ _ (TNode _ _ (TNode _ (Some (wz ?c)) _))) None _) _ _ _ _ _ _) =>
         replace (wz c) with (wz (64 * hflags X))
           by (f_equal; unfold hflags;
               destruct (Z.ltb_spec (ds_level X) 2); [lia|]; destruct (Z.ltb_spec (ds_level X) 6); [lia|]; destruct (Z.eqb_spec (ds_level X) 6); lia)
       end.
  all: apply JN.
Qed.
End HDRG.
