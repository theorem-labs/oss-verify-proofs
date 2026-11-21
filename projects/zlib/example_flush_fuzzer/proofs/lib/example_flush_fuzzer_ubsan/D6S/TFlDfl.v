(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.World Require Import Src_zlib_example_flush_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Frame Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require RefMemcpyLib.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout ZSLayout RomRead TreesRod FillWinMem TreeMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees Deflate HarnessKit HarnessFacts HarnessSmallFacts RefDeflatePost.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6 DS6 Callee6 CalleeKits6 TreesRod6 DeflBlkApi6 DeflSlow6_1 Defl6_M Defl6Api DeflInst6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import ZlibStmtBase ExSmallIface FlLibStmt FlLibIface.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.
#[local] Abbreviation RSX := Src_zlib_example_flush_fuzzer_repro.M.loaded_segments.

Lemma ret_ok_ra : forall ra, ra_ok ra -> ret_ok (Z_to_bv 64 ra).
Proof. intros ra [H1 H2]. apply ret_ok_even. change (Z_to_bv 64 ra) with (zw ra). rewrite u_zw_small by lia. exact H2. Qed.

Lemma holds_cells : forall m a zs, 0 <= a -> a + zlength zs <= 2 ^ 64 ->
  holds RSX m a zs -> cells s6_segs m a 1 1 (zlength zs) (fun i => nth (Z.to_nat i) zs 0).
Proof.
  intros m a zs Ha Hl H i Hi. unfold holds in H. unfold cell.
  pose proof (rdn_sub s6_segs (Z.to_nat i) (length zs) (Z_to_bv 64 a) m _ 1 H ltac:(unfold zlength in Hi; lia)) as R.
  replace (zw (a + 1 * i)) with (Z_to_bv 64 a + nat_to_word (Z.to_nat i))%bv.
  2:{ change (Z_to_bv 64 a) with (zw a). rewrite <- zw_add_nat. f_equal. lia. }
  rewrite R. f_equal. rewrite skipn_map, firstn_map.
  rewrite (skipn_nth zs (Z.to_nat i) 0) by (unfold zlength in Hi; lia). reflexivity.
Qed.

Lemma cells_holds : forall m a zs, 0 <= a -> a + zlength zs <= 2 ^ 64 ->
  cells s6_segs m a 1 1 (zlength zs) (fun i => nth (Z.to_nat i) zs 0) -> holds RSX m a zs.
Proof.
  intros m a zs Ha. unfold holds, cells, cell. unfold s6_segs. change (zw) with (Z_to_bv 64). revert a Ha.
  induction zs as [|z zs IH]; intros a Ha Hl H; [reflexivity|].
  cbn [length rdn map]. unfold zlength in *. cbn [length] in Hl, H.
  pose proof (H 0 ltac:(lia)) as H0. rewrite Z.mul_0_r, Z.add_0_r in H0. cbn [rdn Z_to_le_bytes Z.to_nat nth] in H0.
  destruct (match m (Z_to_bv 64 a) with Some b => Some b | None => seg_rom RSX (Z_to_bv 64 a) end) as [b|]; [| discriminate].
  injection H0 as <-.
  specialize (IH (a + 1) ltac:(lia) ltac:(lia)).
  replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
  2:{ change (Z_to_bv 64 (a + 1)) with (zw (a + Z.of_nat 1)). rewrite zw_add_nat. reflexivity. }
  rewrite IH; [reflexivity|].
  intros i Hi. specialize (H (i + 1) ltac:(lia)). replace (a + 1 + 1 * i) with (a + 1 * (i + 1)) by lia.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) in H by lia. cbn [nth] in H. exact H.
Qed.

Lemma rdn_mapped_ex : forall n m a, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall x : word, a <= bv_unsigned x < a + Z.of_nat n -> m x <> None) ->
  exists bs, rdn s6_segs m (Z_to_bv 64 a) n = Some bs /\ length bs = n.
Proof.
  induction n as [|n IH]; intros m a Ha Hn Hm; [exists []; split; reflexivity|].
  cbn [rdn]. destruct (m (Z_to_bv 64 a)) as [b|] eqn:Eb.
  2:{ exfalso. apply (Hm (Z_to_bv 64 a)); [| exact Eb]. change (Z_to_bv 64 a) with (zw a). rewrite u_zw_small by lia. lia. }
  destruct (IH m (a + 1) ltac:(lia) ltac:(lia) ltac:(intros x Hx; apply Hm; lia)) as (bs & E & L).
  replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
  2:{ change (Z_to_bv 64 (a + 1)) with (zw (a + Z.of_nat 1)). rewrite zw_add_nat. reflexivity. }
  rewrite E. exists (b :: bs). split; [reflexivity | cbn; lia].
Qed.

Lemma mapped_cell8_ex : forall m a, 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall x : word, a <= bv_unsigned x < a + 8 -> m x <> None) ->
  exists v, 0 <= v < 2 ^ 64 /\ cell s6_segs m a 8 v.
Proof.
  intros m a Ha H8 Hm.
  destruct (rdn_mapped_ex 8 m a Ha H8 Hm) as (bs & E & L).
  exists (bytes_le_to_Z bs). split.
  - pose proof (RefMemcpyLib.lez_bound_len bs 8 L) as R. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R. exact R.
  - unfold cell. change (zw a) with (Z_to_bv 64 a). rewrite E, <- L. rewrite InflMem.Z_to_le_bytes_bytes_le. reflexivity.
Qed.

Lemma find_segment_offimg : forall z, (z + 1 <= FL_RO_LO \/ FL_IMG_TOP <= z) -> find_segment RSX z 1 = None.
Proof.
  intros z Hz. unfold FL_RO_LO, FL_IMG_TOP in Hz.
  unfold Src_zlib_example_flush_fuzzer_repro.M.loaded_segments, Src_zlib_example_flush_fuzzer_repro_loaded_segments.
  cbn -[Z.leb Z.add Z.of_N].
  cbn [Z.of_N seg_base seg_size Src_zlib_example_flush_fuzzer_repro_segment_000 Src_zlib_example_flush_fuzzer_repro_segment_001
       Src_zlib_example_flush_fuzzer_repro_segment_002 Src_zlib_example_flush_fuzzer_repro_segment_003].
  destruct Hz as [Hz|Hz];
  repeat match goal with |- context [(?a <=? ?zz) && (?zz + 1 <=? ?b)] =>
    let E := fresh in
    first [ assert (E : (a <=? zz) = false) by (apply Z.leb_gt; lia); rewrite E; cbn [andb]
          | assert (E : (zz + 1 <=? b) = false) by (apply Z.leb_gt; lia); rewrite E, Bool.andb_false_r ] end;
  reflexivity.
Qed.

Lemma store_ok_offimg_mapped : forall m a n, 0 <= a -> 0 <= n -> a + n <= 2 ^ 64 ->
  (a + n <= FL_RO_LO \/ FL_IMG_TOP <= a) ->
  store_ok RSX m (Z_to_bv 64 a) (Z.to_nat n) = true -> mapped m a n.
Proof.
  intros m a n Ha Hn Han Hoff SO x Hx.
  pose proof (store_ok_all RSX m (Z.to_nat n) (Z_to_bv 64 a)) as A.
  change (Z_to_bv 64 a) with (zw a) in A. rewrite u_zw_small in A by lia. rewrite Z2Nat.id in A by lia.
  specialize (A Han SO x Hx). unfold wview in A.
  destruct (m x) as [b|] eqn:Em; [discriminate|].
  rewrite find_segment_offimg in A; [exact A|]. unfold FL_RO_LO, FL_IMG_TOP in *. lia.
Qed.

Lemma arr_get_of_list : forall l i, 0 <= i < zlength l -> arr_get (arr_of_list l) i = nth (Z.to_nat i) l 0.
Proof.
  intros l i Hi. unfold arr_of_list, parr_of_list. rewrite (arr_get_upd l _ 0 i 0).
  unfold arr_inb. rewrite arr_len_make.
  replace (0 <=? i) with true by (symmetry; apply Z.leb_le; lia).
  replace (i <? 0 + zlength l) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (i <? zlength l) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb]. rewrite Z.sub_0_r. reflexivity.
Qed.

Lemma dsafe_avail_out : forall s zc f, DSAFE6 (set_strm s (cstrm_of_call zc)) f -> 0 < zc_avail_out zc < 2 ^ 31.
Proof. intros s zc f (_ & (DL & _)). destruct DL as (_ & _ & H & _). rewrite DeflateSetters.strm_set_strm in H. exact H. Qed.
Lemma dpost_facts : forall s zc f, FL_DPOST (set_strm s (cstrm_of_call zc)) f ->
  let X := fst (deflate_core (set_strm s (cstrm_of_call zc)) f) in
  0 <= snd (deflate_core (set_strm s (cstrm_of_call zc)) f) <= 1 /\ 0 <= cs_next_in (ds_strm X) /\ 0 <= cs_avail_in (ds_strm X)
  /\ cs_next_in (ds_strm X) + cs_avail_in (ds_strm X) = zlength (zc_input zc).
Proof.
  intros s zc f ([A1 A2] & B & C & D). cbv zeta. rewrite DeflateSetters.strm_set_strm in D. cbn [cstrm_of_call cs_next_in cs_avail_in] in D.
  rewrite Z.add_0_l in D. repeat split; assumption.
Qed.

Theorem L_DFL6_ok : forall (regs : bvmap 5 word) (mem : word -> option byte) (q : dptrs) (s : deflate_state) (zc : ZCall) (f : Z)
                  (sp ra inp outp zcl fa ff : Z),
    let ds := set_strm s (cstrm_of_call zc) in
    let X  := fst (deflate_core ds f) in let rc := snd (deflate_core ds f) in
    let nout := Z.of_nat (length (cs_out_rev (ds_strm X))) in
    getr regs 10 = Z_to_bv 64 (dp_strm q) -> getr regs 11 = Z_to_bv 64 f -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = Z_to_bv 64 ra ->
    ra_ok ra -> sp mod 16 = 0 -> zcl + FL_FRA <= sp -> sp <= 2 ^ 47 -> FL_IMG_TOP <= zcl ->
    blocks_ok mem zcl (dblocks q) -> img_clear mem ->
    0 < dp_strm q -> dp_strm q + 112 <= 2 ^ 63 -> dp_strm q mod 8 = 0 -> 0 < inp -> 0 < outp ->
    store_ok RSX mem (Z_to_bv 64 (sp - FL_FRA)) (Z.to_nat FL_FRA) = true ->
    store_ok RSX mem (Z_to_bv 64 (dp_strm q)) 112%nat = true ->
    store_ok RSX mem (Z_to_bv 64 outp) (Z.to_nat (zc_avail_out zc)) = true ->
    all_apart ((sp - FL_FRA, FL_FRA) :: (dp_strm q, 112) :: (outp, zc_avail_out zc) :: (inp, zlength (zc_input zc)) :: dblocks q) ->
    (forall a n, In (a, n) ((sp - FL_FRA, FL_FRA) :: (dp_strm q, 112) :: (outp, zc_avail_out zc) :: dblocks q) -> a + n <= FL_RO_LO \/ FL_IMG_TOP <= a) ->
    inp + zlength (zc_input zc) < 2 ^ 63 -> outp + zc_avail_out zc < 2 ^ 63 ->
    FL_DREP mem q s -> holds RSX mem inp (zc_input zc) ->
    zs_cells FL_MSGA mem (dp_strm q) inp (zlength (zc_input zc)) outp (zc_avail_out zc) (zc_strm zc) (dp_s q) fa ff ->
    fa = FL_ZCALLOC -> ff = FL_ZCFREE ->
    FL_DSAFE ds f ->
    exists (regs' : bvmap 5 word) (mem' : word -> option byte),
      msteps RSX (mkst regs (Z_to_bv 64 FL_A_DEFLATE) mem (seg_rom RSX)) (mkst regs' (Z_to_bv 64 ra) mem' (seg_rom RSX))
      /\ frame_mod mem mem' ((Z_to_bv 64 (sp - FL_FRA), FL_FRA) :: (Z_to_bv 64 (dp_strm q), 112) :: (Z_to_bv 64 outp, nout) :: wz (dblocks q))
      /\ getr regs' 10 = Z_to_bv 64 rc /\ 0 <= rc <= 1 /\ getr regs' 2 = Z_to_bv 64 sp /\ rkeep regs regs' FL_KEEP
      /\ FL_DREP mem' q X
      /\ 0 <= nout <= zc_avail_out zc /\ 0 <= cs_next_in (ds_strm X) <= zlength (zc_input zc)
      /\ zs_cells FL_MSGA mem' (dp_strm q) (inp + cs_next_in (ds_strm X)) (zlength (zc_input zc) - cs_next_in (ds_strm X))
                      (outp + nout) (zc_avail_out zc - nout)
                      (zr_strm (zret_of_cs (ds_strm X) rc)) (dp_s q) fa ff
      /\ holds RSX mem' outp (cs_output (ds_strm X)).
Proof.
  intros regs mem q s zc f sp ra inp outp zcl fa ff. cbv zeta.
  intros R10 R11 R2 R1 RA SP16 ZCL SP47 TOP BOK IC S0 S63 S8 I0 O0 SOf SOs SOo AP IMG BI BO DREP HIN ZS FA FF SAFE.
  pose proof (proj2 (proj2 SAFE)) as DPOST.
  set (cs := cstrm_of_call zc) in *. set (ds := set_strm s cs) in *.
  set (X := fst (deflate_core ds f)) in *. set (rc := snd (deflate_core ds f)) in *.
  set (nout := Z.of_nat (length (cs_out_rev (ds_strm X)))) in *.
  set (strm := dp_strm q) in *. set (S := dp_s q) in *.
  set (p := fl_dsp q).
  pose proof (zlength_nonneg (zc_input zc)) as LEN0.
  unfold blocks_ok, dblocks in BOK.
  apply Forall_cons_iff in BOK as [BS BOK]. apply Forall_cons_iff in BOK as [BW BOK]. apply Forall_cons_iff in BOK as [BP BOK].
  apply Forall_cons_iff in BOK as [BH BOK]. apply Forall_cons_iff in BOK as [BB _]. cbn [fst snd] in BS, BW, BP, BH, BB.
  unfold blk_okz, FL_DSTATE_N, FL_DBLK_N, FL_IMG_TOP in BS, BW, BP, BH, BB. fold S in BS.
  destruct BS as (AS16 & S1 & SZ & SIM & SOS). destruct BW as (AW16 & W1 & WZ & WIM & SOW). destruct BP as (AP16 & P1 & PZ & PIM & SOP).
  destruct BH as (AH16 & H1 & HZ & HIM & SOH). destruct BB as (AB16 & B1 & BZ & BIM & SOB).
  unfold FL_FRA, FL_IMG_TOP, FL_RO_LO in *.
  pose proof (FL_DREP_strm mem q s cs DREP) as DREP'. fold ds in DREP'.
  destruct DREP' as (Dsc & Dar & Dtl & Dw & Dp & Dh & Db & DSZ & DRG).
  destruct DSZ as (Zws & Zhs & Zlbs & Lw & Lp & Lh & Lb).
  destruct DRG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10). unfold FL_DSTATE_N, FL_DBLK_N in G2, G4, G6, G8, G10. fold S in G1, G2.
  assert (Ecs : ds_strm ds = cs) by (subst ds; apply DeflateSetters.strm_set_strm).
  unfold zs_cells, izs_cells in ZS. fold strm in ZS.
  destruct ZS as ((Zni & Zai & Zti & Zno & Zao & Zto & Zmsg & Zst & Zza & Zzf & Zop & Zad) & Zdt).
  assert (MS : mapped mem strm 112).
  { apply store_ok_offimg_mapped; [lia | lia | lia | | exact SOs]. apply (IMG strm 112). cbn. tauto. }
  destruct (mapped_cell8_ex mem (strm + 104) ltac:(lia) ltac:(lia) ltac:(intros x Hx; apply MS; lia)) as (resv & RESV & Zrs).
  set (zp := ZSP inp outp fa ff 0 resv FL_MSGA).
  assert (HZI : zsl_input s6_segs mem zp (ds_strm ds)).
  { rewrite Ecs. unfold zsl_input. cbn [zp zp_in]. subst cs. cbn [cstrm_of_call cs_input]. rewrite arr_len_of_list.
    intros i Hi.
    rewrite arr_get_of_list by exact Hi. exact (holds_cells mem inp (zc_input zc) ltac:(lia) ltac:(lia) HIN i Hi). }
  assert (HZR : ZR6 mem S p zp ds).
  { unfold ZR6. split; [exact Dsc|]. split; [exact Dar|]. split; [exact Dtl|]. split; [exact Dw|]. split; [exact Dp|]. split; [exact Dh|]. split; [exact Db|].
    split; [| split; [exact HZI|]].
    - rewrite Ecs. unfold zsl_scalars, zsl_vals. cbn [fields zsl_layout zp zp_in zp_out zp_msg zp_zalloc zp_zfree zp_opaque zp_reserved p fl_dsp p_strm].
      subst cs. cbn [cstrm_of_call cs_next_in cs_avail_in cs_total_in cs_out_rev cs_avail_out cs_total_out cs_msg cs_data_type cs_adler length Z.of_nat].
      rewrite !Z.add_0_r. fold strm.
      repeat match goal with |- _ /\ _ => split end; first [assumption | exact I]. 
    - rewrite Ecs. unfold zsl_outA. cbn [zp zp_out]. subst cs. cbn [cstrm_of_call cs_out_rev length Z.of_nat]. intros j Hj. lia. }
  assert (Ein : arr_len (cs_input (ds_strm ds)) = zlength (zc_input zc)) by (rewrite Ecs; subst cs; cbn [cstrm_of_call cs_input]; apply arr_len_of_list).
  assert (Eout : Z.of_nat (length (cs_out_rev (ds_strm ds))) + cs_avail_out (ds_strm ds) = zc_avail_out zc) by (rewrite Ecs; subst cs; reflexivity).
  pose proof (zlength_nonneg (zc_input zc)) as LI0.
  pose proof (dsafe_avail_out s zc f (proj1 SAFE)) as AO0.
  assert (MF : mapped mem (sp - 1024) 1024) by (apply store_ok_offimg_mapped; [lia | lia | lia | apply (IMG (sp - 1024) 1024); cbn; tauto | exact SOf]).
  assert (MO : mapped mem outp (zc_avail_out zc)) by (apply store_ok_offimg_mapped; [lia | lia | lia | apply (IMG outp (zc_avail_out zc)); cbn; tauto | exact SOo]).
  assert (MSB : mapped mem S 5968) by (apply store_ok_offimg_mapped; [lia | lia | lia | unfold FL_RO_LO, FL_IMG_TOP; exact SIM | exact SOS]).
  assert (MW : mapped mem (dp_wnd q) 65536) by (apply store_ok_offimg_mapped; [lia | lia | lia | unfold FL_RO_LO, FL_IMG_TOP; exact WIM | exact SOW]).
  assert (MP : mapped mem (dp_prv q) 65536) by (apply store_ok_offimg_mapped; [lia | lia | lia | unfold FL_RO_LO, FL_IMG_TOP; exact PIM | exact SOP]).
  assert (MH : mapped mem (dp_hd q) 65536) by (apply store_ok_offimg_mapped; [lia | lia | lia | unfold FL_RO_LO, FL_IMG_TOP; exact HIM | exact SOH]).
  assert (MB : mapped mem (dp_pb q) 65536) by (apply store_ok_offimg_mapped; [lia | lia | lia | unfold FL_RO_LO, FL_IMG_TOP; exact BIM | exact SOB]).
  pose proof (IMG (sp - 1024) 1024 ltac:(cbn; tauto)) as J1. pose proof (IMG strm 112 ltac:(cbn; tauto)) as J2.
  pose proof (IMG outp (zc_avail_out zc) ltac:(cbn; tauto)) as J3.
  clear SOf SOo SOS SOW SOP SOH SOB.
  assert (HZRH : ZRH6 DEFL_K6 mem S sp p zp ds).
  { constructor.
    - unfold DEFL_K6. clear - ZCL SP47 TOP. lia.
    - unfold zr_regions, DEFL_K6, ds6_SIZE, zsl_SIZE. rewrite Zws, Zhs, Zlbs, Ein, Eout.
      cbn [zp zp_in zp_out p fl_dsp p_window p_prev p_head p_pending_buf p_strm]. fold strm S.
      clear SIM WIM PIM HIM BIM J1 J2 J3 IMG AP.
      repeat constructor; cbn [fst snd]; lia.
    - rewrite Ein. cbn [zp zp_in]. clear - BI LI0 I0. lia.
    - cbn [p fl_dsp p_window]. clear - W1. lia.
    - cbn [p fl_dsp p_head]. clear - H1 AH16. pose proof (Z.mod_pos_bound (dp_hd q) 16). lia.
    - cbn [p fl_dsp p_prev]. clear - P1 AP16. pose proof (Z.mod_pos_bound (dp_prv q) 16). lia.
    - unfold ZRF, DEFL_K6, ds6_SIZE, zsl_SIZE. rewrite Zws, Zhs, Zlbs, Eout.
      cbn [zp zp_out p fl_dsp p_window p_prev p_head p_pending_buf p_strm]. fold strm S.
      clear SIM WIM PIM HIM BIM J1 J2 J3 IMG AP.
      repeat constructor; cbn [fst snd]; intros y Hy; first [apply MF; lia | apply MSB; lia | apply MW; lia | apply MP; lia | apply MH; lia | apply MB; lia | apply MS; lia | apply MO; lia].
    - unfold zr_regions, DEFL_K6, ds6_SIZE, zsl_SIZE. rewrite Zws, Zhs, Zlbs, Ein, Eout.
      cbn [zp zp_in zp_out p fl_dsp p_window p_prev p_head p_pending_buf p_strm]. fold strm S.
      cbn [apart_all apart_from]. unfold FillWinMem.apart. cbn [fst snd].
      clear SIM WIM PIM HIM BIM J1 J2 J3 IMG.
      unfold dblocks in AP. cbn [all_apart apart_from_all] in AP. unfold ExSmallIface.apart in AP. fold S in AP. unfold FL_DSTATE_N, FL_DBLK_N in AP.
      destruct AP as ((A_FT & A_FO & A_FI & A_FS & A_FW & A_FP & A_FH & A_FB & _) & (A_TO & A_TI & A_TS & A_TW & A_TP & A_TH & A_TB & _) & (A_OI & A_OS & A_OW & A_OP & A_OH & A_OB & _)
                   & (A_IS & A_IW & A_IP & A_IH & A_IB & _) & (A_SW & A_SP & A_SH & A_SB & _) & (A_WP & A_WH & A_WB & _) & (A_PH & A_PB & _) & (A_HB & _) & _).
      repeat split;
        [ clear - A_FS | clear - A_FW | clear - A_FP | clear - A_FH | clear - A_FB | clear - A_FT | clear - A_FO | clear - A_FI
        | clear - A_SW | clear - A_SP | clear - A_SH | clear - A_SB | clear - A_TS | clear - A_OS | clear - A_IS
        | clear - A_WP | clear - A_WH | clear - A_WB | clear - A_TW | clear - A_OW | clear - A_IW
        | clear - A_PH | clear - A_PB | clear - A_TP | clear - A_OP | clear - A_IP
        | clear - A_HB | clear - A_TH | clear - A_OH | clear - A_IH
        | clear - A_TB | clear - A_OB | clear - A_IB
        | clear - A_TO | clear - A_TI
        | clear - A_OI ]; lia.
    - unfold rod6, trees_rod_clear6, trees_rod_clear, got6_clear, rom_clear. cbn [tr_lo tr_hi tr_sdesc R6].
      clear - IC. unfold img_clear, FL_RO_LO, FL_RO_HI in IC. repeat split; intros x Hx; rewrite <- (Z_to_bv_bv_unsigned 64 x); apply IC; lia.
    - unfold ZRF, DEFL_K6, ds6_SIZE, zsl_SIZE, IMG6_LO, IMG6_HI. rewrite Zws, Zhs, Zlbs, Eout.
      cbn [zp zp_out p fl_dsp p_window p_prev p_head p_pending_buf p_strm in_franges]. fold strm S.
      clear - J1 J2 J3 SIM WIM PIM HIM BIM. intros x Hx Hi. lia.
    - cbn [zp zp_out]. clear - O0. lia. }
  assert (HDP : DPTRS S p zp).
  { constructor; cbn [p fl_dsp p_strm zp zp_in zp_zalloc zp_zfree].
    - clear - S1. lia.
    - clear - S0. lia.
    - clear - I0. lia.
    - rewrite FA. unfold FL_ZCALLOC. clear. lia.
    - rewrite FF. unfold FL_ZCFREE. clear. lia. }
  assert (HROM : ROM6 mem).
  { unfold ROM6, S6AdlerBase.img_ok, S6AdlerBase.RO_LO, S6AdlerBase.RO_HI. clear - IC. unfold img_clear, FL_RO_LO, FL_RO_HI in IC. intros i Hi. apply IC. lia. }
  assert (HRC : rom_clear mem 0x10000 0x293d8).
  { clear - IC. unfold img_clear, FL_RO_LO, FL_RO_HI in IC. intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply IC. lia. }
  pose proof (ret_ok_ra ra RA) as HRET.
  pose proof (@deflate_run6_S6 fx) as DR. unfold deflate_run6 in DR.
  specialize (DR mem S p zp ds f (Z_to_bv 64 ra) sp regs HZRH HRC HDP HRET HZR HROM (proj1 SAFE) R10 R11 R2 R1).
  destruct DR as (R' & m' & RUN & ZR' & X10 & X2 & XREG & AG & ROD & ROM' & GR & LZK).
  exists R', m'.
  fold X in ZR', AG, LZK, X10. fold rc in X10. fold nout in AG.
  pose proof (dpost_facts s zc f DPOST) as DPF. cbv zeta in DPF. fold cs ds in DPF. fold X rc in DPF.
  destruct DPF as (RC01 & NI0 & AI0 & NAI).
  destruct LZK as (Kws & Khs & Klbs & Kwl & Kpl & Khl & Kbl & Kin & Kout & Kao & Kol).
  rewrite Eout in Kout. fold nout in Kout, Kol.
  assert (NOUT : 0 <= nout <= zc_avail_out zc) by (clear - Kout Kao Kol; subst nout; lia).
  split; [exact RUN|].
  split.
  {
    split; [| exact GR].
    intros a Hout. apply AG. intros Hin.
    unfold ZRFo, DEFL_K6, ds6_SIZE, zsl_SIZE in Hin. rewrite Zws, Zhs, Zlbs in Hin.
    cbn [zp zp_out p fl_dsp p_window p_prev p_head p_pending_buf p_strm in_franges] in Hin. fold strm S in Hin.
    unfold dblocks, FL_DSTATE_N, FL_DBLK_N in Hout. cbn [outside wz map fst snd] in Hout. unfold in_rng in Hout. fold S in Hout.
    change (Z_to_bv 64) with zw in Hout. rewrite !u_zw_small in Hout by (clear - ZCL TOP SP47 S0 S63 O0 BO G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 AO0; lia).
    clear - Hin Hout NOUT ZCL TOP. lia. }
  split; [exact X10|].
  split; [exact RC01|].
  split; [exact X2|].
  split.
  { intros r Hr. apply XREG. cbn in Hr.
    repeat (destruct Hr as [Hr|Hr]; [subst r; reflexivity|]). destruct Hr. }
  split.
  {
    destruct ZR' as (Ysc & Yar & Ytl & Yw & Yp & Yh & Yb & Yzs & Yzi & Yzo).
    destruct DREP as (_ & _ & _ & _ & _ & _ & _ & _ & DRG0).
    split; [exact Ysc|]. split; [exact Yar|]. split; [exact Ytl|]. split; [exact Yw|]. split; [exact Yp|]. split; [exact Yh|]. split; [exact Yb|].
    split; [| exact DRG0].
    unfold DSIZES. rewrite Kws, Khs, Klbs, Kwl, Kpl, Khl, Kbl, Zws, Zhs, Zlbs. repeat split; reflexivity. }
  split; [exact NOUT|].
  split; [clear - NI0 AI0 NAI; lia|].
  destruct ZR' as (Ysc & Yar & Ytl & Yw & Yp & Yh & Yb & Yzs & Yzi & Yzo).
  split.
  {
    unfold zsl_scalars, zsl_vals in Yzs. cbn [fields zsl_layout zp zp_in zp_out zp_msg zp_zalloc zp_zfree zp_opaque zp_reserved p fl_dsp p_strm] in Yzs.
    fold strm nout in Yzs.
    destruct Yzs as (C0 & C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C88 & C96 & C104 & _).
    replace (zlength (zc_input zc) - cs_next_in (ds_strm X)) with (cs_avail_in (ds_strm X)) by (clear - NAI; lia).
    replace (zc_avail_out zc - nout) with (cs_avail_out (ds_strm X)) by (clear - Kout; lia).
    unfold zs_cells, izs_cells. cbn [zr_strm zret_of_cs zstrm_of_cs zs_total_in zs_total_out zs_msg zs_adler zs_data_type].
    rewrite Z.add_0_r in C0.
    repeat match goal with |- _ /\ _ => split end; assumption. }
  apply cells_holds; [clear - O0; lia | | ].
  - rewrite RefDeflatePost.zlength_cs_output. unfold zlength. fold nout. clear - BO NOUT O0. lia.
  - rewrite RefDeflatePost.zlength_cs_output. unfold zlength. fold nout. unfold zsl_outA in Yzo. cbn [zp zp_out] in Yzo. fold nout in Yzo. exact Yzo.
Qed.
End FXG.
