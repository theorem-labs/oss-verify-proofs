(* [comment removed for export] *)


From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import InitMem Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_kit Z_tr_kit Z_tr_emit
     Zg_defl_iface Zg_sto_model Zg_sto_kit Zg_sto_head.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk SendModel FillWinModel TrSmallModel
     RefDeflFast1 RefDeflFastM RefDeflStored2 RefDeflStored5 RefDeflStored6 RefDeflStored7 RefDeflStored8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition Z_STO_COPY : Z := 0x182c0.

Lemma dlay_below_lower : forall L lo hi hi', dlay_below L lo hi -> hi' <= hi -> dlay_below L lo hi'.
Proof. intros L lo hi hi' H Hle. unfold dlay_below in *. lia. Qed.

Lemma patb0 : forall len, bv_unsigned (wz len) mod 2^8 = wrap8 len mod 2^8.
Proof. intros len. rewrite lo8_unsigned_wz. bits8. Qed.
Lemma patb1 : forall len, 0 <= len -> bv_unsigned (wz (Z.shiftr len 8)) mod 2^8 = wrap8 (Z.shiftr len 8) mod 2^8.
Proof. intros len H. rewrite lo8_unsigned_wz. bits8. Qed.
Lemma patb2 : forall len, 0 <= len -> bv_unsigned (wz (Z.lxor len 18446744073709551615)) mod 2^8 = wrap8 (Z.lnot len) mod 2^8.
Proof. intros len H. rewrite lo8_unsigned_wz. change 18446744073709551615 with (Z.ones 64). bits8. Qed.
Lemma patb3 : forall len, 0 <= len ->
  bv_unsigned (wz (Z.shiftr (Z.lxor len 18446744073709551615) 8)) mod 2^8 = wrap8 (Z.shiftr (wrap32 (Z.lnot len)) 8) mod 2^8.
Proof. intros len H. rewrite lo8_unsigned_wz. unfold wrap32. change 18446744073709551615 with (Z.ones 64). change 4294967295 with (Z.ones 32). bits8. Qed.

Lemma lastv_mach : forall flush len v, 0 <= flush <= 5 -> 0 <= len < 2^16 -> 0 <= v < 2^32 ->
  Z.b2z (Z.lor (Z.lxor flush 4) (Z.lxor len ((bv_swrap 32 v) mod 18446744073709551616)) <? 1) = (if (flush =? 4) && (len =? v) then 1 else 0).
Proof.
  intros flush len v Hf Hl Hv.
  set (u := bv_swrap 32 v mod 18446744073709551616).
  assert (Hu : 0 <= u /\ (u = len <-> v = len)).
  { subst u. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.div].
    change (4294967296 / 2) with 2147483648. change (2^32) with 4294967296 in Hv. change (2^16) with 65536 in Hl.
    Z.div_mod_to_equations. lia. }
  clearbody u. destruct Hu as [Hu0 Huv].
  assert (N1' : 0 <= Z.lxor flush 4) by (apply (proj2 (Z.lxor_nonneg flush 4)); lia).
  assert (N2' : 0 <= Z.lxor len u) by (apply (proj2 (Z.lxor_nonneg len u)); lia).
  assert (N3 : 0 <= Z.lor (Z.lxor flush 4) (Z.lxor len u)) by (apply (proj2 (Z.lor_nonneg _ _)); split; assumption).
  destruct (Z.ltb_spec (Z.lor (Z.lxor flush 4) (Z.lxor len u)) 1) as [LT|GE].
  - assert (E0 : Z.lor (Z.lxor flush 4) (Z.lxor len u) = 0) by lia.
    apply Z.lor_eq_0_iff in E0. destruct E0 as [E1 E2]. apply (proj1 (Z.lxor_eq_0_iff _ _)) in E1. apply (proj1 (Z.lxor_eq_0_iff _ _)) in E2.
    replace (flush =? 4) with true by (symmetry; apply Z.eqb_eq; exact E1).
    replace (len =? v) with true by (symmetry; apply Z.eqb_eq; symmetry; apply Huv; symmetry; exact E2). reflexivity.
  - destruct (Z.eqb_spec flush 4) as [EF|NF]; [|reflexivity]. destruct (Z.eqb_spec len v) as [EL|NL]; [|reflexivity].
    exfalso. rewrite EF in GE. assert (Eu : u = len) by (apply (proj2 Huv); symmetry; exact EL). rewrite Eu in GE.
    rewrite !Z.lxor_nilpotent in GE. change (Z.lor 0 0) with 0 in GE. lia.
Qed.

Ltac pb_store' ARR A idx v RNG := lazymatch type of ARR with u8arr _ _ _ (av8 ?a ?n) => pb_store ARR a n A idx v RNG end.

Ltac emit_close ZS GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY OUT ES Ek FR STK MU WM KL :=
  rewrite ES; split; [split|];
  [ eexists _, _, _, _; unfold zs_call_cells, zs_priv_cells; cbn [app]; unfold cs_emit; dsred;
    rewrite ?rev_append_rev, ?length_app, ?length_rev, ?arr_slice_length', <- ?Ek; close_cells ZS
  | constructor; [eexists _, _, _, _, _; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY]
  | split; [unfold dout; dsred; exact OUT|];
    split; [constructor; dsred; rewrite cs_emit_out_len, arr_slice_length', <- Ek; exact KL|];
    split; [eexists; exact FR|]; split; [exact STK|]; split; [exact MU|]; split; [exact WM| assumption] ].

Section EMIT.
Variables (L : dlay) (flush ai0 : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : sto_ctx L inp rest0 lo r me.
Hypothesis HFL : 0 <= flush <= 5.
Hypothesis HTSB : tr_stored_block_stmt.
Hypothesis HTFB : tr_flush_bits_stmt.

Definition KCOPY (Q : machine_state -> Prop) (X X4 : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y23 y28 y29 y30 y31 : word) (m' : mem),
    STOINV L flush ai0 1 rest0 lo r me X4 m' ->
    evt psegs Q (MS (stoR7 L r y1 y5 y6 y7 (wz (sb_len X)) y10 y11 y12 y13 y14 y15 y16 y17 (wz (sb_lastv X flush)) y19 y20
                        (wz (ds_strstart X - ds_block_start X)) (wz (ds_strstart X)) y23 (wz (ds_block_start X)) y28 y29 y30 y31)
                    F (wz Z_STO_COPY) fc None m' (seg_rom psegs)).

Variables (Q : machine_state -> Prop) (X : deflate_state).
Hypothesis RBV : 0 <= ds_bi_valid X <= 16.
Hypothesis RAO : 0 <= cs_avail_out (ds_strm X) < 2^31.
Hypothesis RAI : 0 <= cs_avail_in (ds_strm X) < 2^31.
Hypothesis RBS : 0 <= ds_block_start X <= ds_strstart X.
Hypothesis RSTR : ds_strstart X <= 65536.
Hypothesis LBS : ds_lit_bufsize X = 16384.
Hypothesis HH : sb_hdr X <= cs_avail_out (ds_strm X).
Hypothesis EOK : so_emit_ok X flush.
Hypothesis RM4 : Box (length (cs_out_rev (ds_strm (st_emit1 X flush))) <= length rest0)%nat.
Hypothesis KC : KCOPY Q X (st_emit1 X flush).

Lemma sto_emit : KEMIT L flush ai0 rest0 lo r F fc me Q X.
Proof using KC RM4 EOK HH LBS RSTR RBS RAI RAO HTFB HTSB HFL CTX inp.
  unfold KEMIT. intros until m'. intros INV.
  pose proof INV as (DR & DOUT & RM & (j0 & FR) & STK & MU & WM & MI). unfold sto_frame in FR. unfold Z_STO_EMIT, stoR, stoR7.
  pose proof (tc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_STORED_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY.
  pose proof (tc_bel _ _ _ _ _ _ CTX) as BEL. pose proof BEL as BEL'. below_open BEL'.
  pose proof (tc_io _ _ _ _ _ _ CTX) as IO. pose proof IO as IO'. io_open IO'.
  pose proof (sb_len_range X ltac:(lia) HH) as (RL1 & RL2 & RL3).

  destruct EOK as (BI0 & RP1 & FPOK). rewrite LBS in BI0, RP1, FPOK. change (16384 * 4) with 65536 in BI0, RP1, FPOK.
  remember (sb_lastv X flush) as last eqn:Elast.
  pose proof (sb_lastv_range X flush) as Rlast. rewrite <- Elast in Rlast.

  do 4 zstep.
  assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -160)) = bv_unsigned (r_sp r) + -160) by (apply unsigned_lit; lia).
  unfold sto_W, slow_W in MU.
  unfold dout in DOUT. pose proof (outv_length rest0 (ds_strm X) (unbox _ RM)) as OL. open_zs ZS.
  zstep. call (HTSB L X None 0 last lo).
  1:{ exact ST. } 1:{ exact MI. } 1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. eapply dlay_below_lower; [exact BEL| lia]. }
  1:{ exact BI0. } 1:{ lia. } 1:{ intros C; exfalso; apply C; reflexivity. } 1:{ exact I. } 1:{ lia. } 1:{ exact Rlast. }
  1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  name_mem m1. rewrite ESP in PC. rename PC into STK1. clear ST.

  assert (HX1 : exists X1, X1 = tr_stored_block X None 0 last) by (eexists; reflexivity). destruct HX1 as [X1 EX1].
  pose proof (sb_keep X None 0 last) as KK. cbv zeta in KK. rewrite <- EX1 in KK, RP1, FPOK, POST. destruct KK as (K1s & K1w & K1ws & K1hs & K1lbs & K1bs & K1str).
  open_DST POST. open_A GA. open_pend Gpend. pose proof (ln_pend _ LENS) as LNP.
  pose proof (munch_refl [(dl_Ab L, dl_Ab L + 65536)] m1) as MUf. pose proof (wmono_refl psegs m1) as WMf.

  zstep. zstep. zstep.
  pb_store' Gpend (dl_Ab L) (ds_pending X1 - 4) (wrap8 (sb_len X)) ltac:(apply patb0).
  zstep. zstep. zstep. zstep.
  pb_store' Gpend (dl_Ab L) (ds_pending X1 - 3) (wrap8 (Z.shiftr (sb_len X) 8)) ltac:(apply patb1; lia).
  zstep. zstep. zstep. zstep.
  pb_store' Gpend (dl_Ab L) (ds_pending X1 - 2) (wrap8 (Z.lnot (sb_len X))) ltac:(apply patb2; lia).
  zstep. zstep. zstep. zstep.
  pb_store' Gpend (dl_Ab L) (ds_pending X1 - 1) (wrap8 (Z.shiftr (wrap32 (Z.lnot (sb_len X))) 8)) ltac:(apply patb3; lia).
  name_mem mB.

  assert (EA4 : exists X2, X2 = sb_patch X1 (sb_len X)) by (eexists; reflexivity). destruct EA4 as [X2 EX2].
  pose proof (sb_patch_keep X1 (sb_len X)) as KK. rewrite <- EX2 in KK. destruct KK as (K2s & K2w & K2ws & K2hs & K2lbs & K2bs & K2str & K2p & K2wr & K2bv).
  rewrite <- EX2 in FPOK.
  tr_groups MUf WMf.
  assert (ST2 : DST mB L X2).
  { rewrite EX2. unfold sb_patch. cbv zeta.
    destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13].
    constructor; [exists hA1, hA2, hA3, hA4, hA5; exact GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact Gpend| | exact LAY].
    constructor; [exact l1| exact l2| exact l3| exact l4| exact l5| exact l6| exact l7| exact l8| exact l9| exact l10| exact l11| exact l12| ].
    dsred. rewrite !arr_len_set. exact LNP. }
  clear GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend MUf WMf LAY0 LENS LNP.

  destruct FPOK as [BI2 FPK]. cbv zeta in FPK. destruct FPK as (RP3 & RP3' & RPB3 & RPO3 & RPOL3 & RTO3).
  zstep. zstep. zstep. zstep. clear GA. call (HTFB L X2).
  1:{ exact ST2. } 1:{ assumption. } 1:{ exact BI2. } 1:{ exact RPB3. } 1:{ reflexivity. }
  name_mem mC. clear ST2.
  assert (HX3 : exists X3, X3 = tr_flush_bits X2) by (eexists; reflexivity). destruct HX3 as [X3 EX3].
  pose proof (bits_keep X2) as KK. cbv zeta in KK. rewrite <- EX3 in KK, RP3, RP3', RPB3, RPO3, RPOL3, RTO3, POST.
  destruct KK as (K3s & K3w & K3ws & K3hs & K3lbs & K3bs & K3str & K3wr & K3po).
  assert (ES : ds_strm X3 = ds_strm X) by (rewrite K3s, K2s; exact K1s).

  assert (EF : st_emit1 X flush = (if fp_len X3 =? 0 then X3 else fp_tail X3 (fp_len X3))).
  { unfold st_emit1. rewrite <- Elast, <- EX1, <- EX2, flush_pending_eq. cbv zeta. rewrite <- EX3. reflexivity. }
  rewrite EF in RM4. unfold KCOPY in KC. rewrite EF in KC. clear EF.
  assert (EL : fp_len X3 = if cs_avail_out (ds_strm X) <? ds_pending X3 then cs_avail_out (ds_strm X) else ds_pending X3).
  { unfold fp_len. rewrite ES, wrap32_id by lia. reflexivity. }
  revert RM4 KC RPOL3 EL. generalize (fp_len X3) as flen. intros flen RM4 KC RPOL3 EL.
  open_DST POST. open_A GA.
  pose proof (munch_refl [(dl_S L, dl_S L + 112); (dl_As L, dl_As L + 212); (dl_NO L, dl_NO L + Z.of_nat (length rest0))] mC) as MUf.
  pose proof (wmono_refl psegs mC) as WMf.
  zs. zs. zstep.
  assert (FL : 0 <= flen /\ flen <= cs_avail_out (ds_strm X) /\ flen <= ds_pending X3) by (destruct (Z.ltb_spec (cs_avail_out (ds_strm X)) (ds_pending X3)); lia).

  eapply (evt_cut psegs (fun ms' => ms' = _)).
  { if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
    - replace (cs_avail_out (ds_strm X) <? ds_pending X3) with false in EL by (symmetry; apply Z.ltb_ge; lia).
      replace (wz (ds_pending X3)) with (wz flen) by (f_equal; lia). apply evt_done. reflexivity.
    - zstep. apply evt_done. replace flen with (cs_avail_out (ds_strm X)) by (rewrite EL; destruct (Z.ltb_spec (cs_avail_out (ds_strm X)) (ds_pending X3)); lia).
      reflexivity. }
  intros ms' ->. clear EL.
  zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia.
  -
    replace (flen =? 0) with true in KC, RM4 by (symmetry; apply Z.eqb_eq; lia).
    subst last. eapply KC. split; [split|].
    + exists zp1, zp2, zp3, zresv. rewrite ES. exact ZS.
    + constructor; [eexists _, _, _, _, _; exact GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                   | exact Gwin| exact Gprev| exact Ghead| exact Gpend| exact LENS| exact LAY].
    + split; [unfold dout; rewrite ES; exact DOUT|]. split; [exact RM4|]. split; [eexists; exact FR|]. split; [exact STK1|].
      split; [exact MU|]. split; [exact WM| exact MI].
  -
    replace (flen =? 0) with false in KC, RM4 by (symmetry; apply Z.eqb_neq; lia).
    open_pend Gpend. pose proof (ln_pend _ LENS) as LNP.
    do 4 zstep. rewrite ?Z.mod_small by lia.
    remember (length (cs_out_rev (ds_strm X))) as k eqn:Ek.
    assert (KL : (k + Z.to_nat flen <= length rest0)%nat).
    { pose proof (unbox _ RM4) as R4. unfold fp_tail in R4. cbv zeta in R4. rewrite ES in R4.
      destruct (ds_pending X3 - flen =? 0); dsred in R4; rewrite cs_emit_out_len, arr_slice_length', <- Ek in R4; lia. }
    pose proof (u8arr_sub_bytes _ (dl_Ab L) _ (Z.to_nat (ds_pending_out X3)) (Z.to_nat flen) Gpend ltac:(rewrite av8_length; lia)) as SRC.
    rewrite av8_slice in SRC by lia. rewrite Z2Nat.id in SRC by lia.
    assert (LSRC : length (map (Z_to_bv 8) (arr_slice (ds_pending_buf X3) (ds_pending_out X3) flen)) = Z.to_nat flen)
      by (rewrite length_map; apply arr_slice_length').
    destruct (u8arr_split3 _ (dl_NO L) _ k (Z.to_nat flen) DOUT ltac:(rewrite OL; lia)) as (O1 & O2 & O3). clear DOUT.
    assert (LO1 : length (firstn k (outv rest0 (ds_strm X))) = k) by (rewrite length_firstn, OL; lia).
    assert (LO3 : length (skipn (k + Z.to_nat flen) (outv rest0 (ds_strm X))) = (length rest0 - (k + Z.to_nat flen))%nat) by (rewrite length_skipn, OL; lia).
    call (memcpy_Z (dl_NO L + Z.of_nat k) (dl_Ab L + ds_pending_out X3) flen).
    1:{ exact SRC. } 1:{ exact LSRC. } 1:{ exact O2. } 1:{ zsep. } 1:{ eassumption. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
    pose proof (u8arr_join3k _ (dl_NO L) _ _ _ k (Z.to_nat flen) LO1 O1 PC O3) as OUT.
    fold (zb8 (arr_slice (ds_pending_buf X3) (ds_pending_out X3) flen)) in OUT.
    rewrite <- (arr_slice_length' (ds_pending_buf X3) (ds_pending_out X3) flen) in OUT. rewrite Ek in OUT.
    rewrite <- outv_emit in OUT by (rewrite <- Ek, arr_slice_length'; exact KL).
    assert (OL' : length (outv rest0 (cs_emit (ds_strm X) (arr_slice (ds_pending_buf X3) (ds_pending_out X3) flen))) = length rest0).
    { apply outv_length. rewrite cs_emit_out_len, arr_slice_length', <- Ek. lia. }
    clear O1 O3 PC POST SRC LSRC LO1 LO3.
    do 16 zs.
    if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
    +
      tr_groups MUf WMf. subst last. eapply KC.
      unfold fp_tail. cbv zeta. replace (ds_pending X3 - flen =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      emit_close ZS GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY OUT ES Ek FR STK1 MU WM KL.
    +
      do 2 zs. tr_groups MUf WMf. subst last. eapply KC.
      unfold fp_tail. cbv zeta. replace (ds_pending X3 - flen =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
      emit_close ZS GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY OUT ES Ek FR STK1 MU WM KL.
Qed.
End EMIT.
