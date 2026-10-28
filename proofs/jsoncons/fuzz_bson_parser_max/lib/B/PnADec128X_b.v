(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParSpecs PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PnASrcReadK_b PmAUarK_b PmAUar_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnDecFacts PnMemW. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnSpecsAXD_b PnADec128Defs_b PnADec128K_b PnADec128S_b PnADec128F_b PnADec128M_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnADec128Bv. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnADec128P7_b PnADec128Mid_b PnADec128XM_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNADX.
Import L5A. Import L5CA. Import L5SAR. Import PNADK.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation mem := (word -> option byte).

Lemma S_mono a b : a <= b -> S a <= S b.
Proof. intros H. unfold S. pose proof (Z.div_le_mono a b 8 ltac:(clear; lia) H). clear - H0. lia. Qed.

Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithHeap.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

(* [comment removed for export] *)
Lemma dg_memcpy E (X : dkc L ar HI E) axc (fx : FPState) Ra Mc modelc LKc Ac (d src n ra : Z) :
  dsg L ar HI E axc Mc modelc LKc Ac -> vfirst E <= d -> d + n <= vfirst E + 42 -> 0 < n <= 2 ^ 27 ->
  0x6722c8 <= src -> src + n <= 0x672300 -> L5.defined Mc src n ->
  getr Ra (reg 10) = Z_to_bv 64 d -> getr Ra (reg 11) = Z_to_bv 64 src -> getr Ra (reg 12) = Z_to_bv 64 n -> getr Ra (reg 4) = Z_to_bv 64 (hl_tp L) ->
  getr Ra (reg 1) = Z_to_bv 64 ra -> ra mod 2 = 0 -> 0 <= ra < 2 ^ 64 -> getr Ra (reg 2) = Z_to_bv 64 (vsp E - 256) ->
  (forall Rb Mb modelb, regs_preserved Ra Rb -> dsg L ar HI E axc Mb modelb LKc Ac ->
     (L5KA.zeros_at Mc (PNADD.SH (vF E) + 4) 18 -> L5KA.zeros_at Mb (PNADD.SH (vF E) + 4) 18) ->
     srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx Rb ra Mb modelb) (vK E)) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx Ra 0x77c94 Mc modelc) (vK E).
Proof.
  intros ST Hd1 Hd2 Hn Hs1 Hs2 SDEF Ra10 Ra11 Ra12 Ra4 Ra1 Hra Hra' Ra2 KC.
  pose proof ST as (BI & DF & AF & _). pose proof BI as (HHc & AMc & _ & _ & _ & ASTKc & _). cbn [app] in HHc.
  pose proof (c_G L ar HI E X) as G'. destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *. unfold PNADK.SCR in *.
  dgeom L ar HI E X.
  destruct (c_BLK L ar HI E X) as (Bq & Bm & HB & HB1 & HB2).
  pose proof (HAJ.aior_memcpy _ _ _ _ _ HIok) as MS. unfold amemcpy_spec, amemcpy_spec_at, amem_pre, amem_post in MS.
  rewrite (L5A.aly_segs L C LYa), (L5A.aly_memcpy L C LYa), (L5A.aly_scr_mem L C LYa), (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in MS.
  assert (U2 : bv_unsigned (getr Ra 2%bv) = vsp E - 256) by (rewrite L5K.rl2, Ra2; apply L5.unsigned_lit; clear - SR; lia).
  destruct (PMASRK.rdn_of_defR Mc (Z.to_nat n) src ltac:(clear - Hs1; lia) ltac:(rewrite Z2Nat.id by (clear - Hn; lia); clear - Hs2; lia)) as (bs & RDN).
  { intros i Hi. rewrite Z2Nat.id in Hi by (clear - Hn; lia). apply SDEF. exact Hi. }
  unfold PMSPA.cfg. apply (MS fx Ra Mc modelc (vLB E) (PNADK.FF' E) LKc (vcr E) Ac d src n bs (vK E)); clear MS.
  - split; [exact HHc|]. split; [exact (proj1 AMc)|]. split; [exact (proj2 AMc)|].
    split; [rewrite L5K.rl10; exact Ra10|]. split; [rewrite L5K.rl12; exact Ra12|]. split; [clear - Hn; lia|].
    split; [rewrite L5K.rl4; exact Ra4|]. split; [rewrite L5K.rl1, Ra1; apply Hoare.ret_ok_even; rewrite L5.unsigned_lit by exact Hra'; exact Hra|].
    split. { rewrite U2. apply (L5SAR.astack_ok_of_astk L ar C LYa Mc Mc (vsp E) 18432 256 2560 ASTKc (fun x Hx => Hx)); [clear; lia| clear; lia| clear; lia|].
             replace (vsp E - 256) with (vsp E + (-16) * 16) by (clear; lia). rewrite Z_mod_plus_full. clear - GS32.
             pose proof (Z.div_mod (vsp E) 32 ltac:(lia)) as D. rewrite GS32, Z.add_0_r in D. rewrite D. replace (32 * (vsp E / 32)) with ((2 * (vsp E / 32)) * 16) by lia. apply Z_mod_mult. }
    split; [intros a Ha; apply AF; clear - Ha Hd1 Hd2; lia|].
    split. { intros i Hi. rewrite U2. apply (L5SAR.block_client L ar _ (PNADK.FF' E) _ _ Bq Bm); [exact HB|]. clear - Hi Hd1 Hd2 HB1 HB2; lia. }
    split. { intros i m Hi Hm. pose proof (L5C.writable_of_defined RSEGS Mc (vfirst E) 42 DF ltac:(clear - GF1; lia) ltac:(clear - GF1; lia)) as WR.
             replace (d + i) with (vfirst E + (d - vfirst E + i)) by (clear; lia). apply WR; clear - Hi Hm Hd1 Hd2; lia. }
    split; [exact (c_K0 L ar HI E X)|]. apply (L5SAR.app_rng_block L ar C HI HIok _ _ _ _ _ _ _ Bq Bm d n HHc HB); [clear - Hd1 HB1; lia| clear - Hd2 HB2; lia].
  - rewrite L5K.rl11. exact Ra11.
  - intros a Ha. left.
    destruct (aic_img_shadow _ _ _ _ _ ICok _ _ _ _ _ _ _ HHc src n) as (Z0 & _).
    + rewrite (L5A.aly_img_lo L C LYa). clear - Hs1; lia.
    + rewrite (L5A.aly_img_hi L C LYa). clear - Hs2; lia.
    + clear - Hn; lia.
    + rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; clear - Hs1 Hs2; lia|]). apply Forall_nil.
    + apply Z0. unfold in_shadow_of. split; apply S_mono; clear - Ha; lia.
  - clear - Hs1 Hs2; lia.
  - apply (L5SAR.app_rng_img ar); [clear - GSPT; lia| clear - Hs1; lia| clear - Hs2; lia].
  - intros i Hi. left. clear - Hi Hs1 Hs2; lia.
  - exact RDN.
  - intros _. destruct GFI as [Y|Y]; [right; clear - Y Hs2 Hd1; lia| left; clear - Y Hs1 Hd2; lia].
  - intros Rb Mb modelb Rb10 RPb BYTES PRES SDEFb RTb MIb HHb. rewrite U2 in PRES, SDEFb. rewrite L5K.rl1, Ra1.
    assert (AMb : L5CA.amodel_ok Ac modelb) by (split; [rewrite (L5LZ.model_rt_halted _ _ RTb); exact (proj1 AMc)| exact MIb]).
    destruct (PNADK.dg_memcall L ar C HI LY HIok E X axc Mc modelc LKc Ac Mb modelb (fun a => d <= a < d + n) ST HHb AMb RTb PRES SDEFb) as (STb & ZSb).
    + intros a Ha. destruct (BYTES (a - d) ltac:(clear - Ha; lia)) as (v & _ & Bv). unfold byte_at in Bv. replace (d + (a - d)) with a in Bv by (clear; lia). rewrite Bv. discriminate.
    + intros a. destruct (L5SAR.rng_dec a d (d + n)) as [Y|Y]; [left; exact Y| right; exact Y].
    + intros a Ha. right. clear - Ha Hd1 Hd2; lia.
    + exact (KC Rb Mb modelb RPb STb ZSb).
Qed.

Lemma keeps_cs (R R' : bvmap 5 word) : regs_preserved R R' -> PNADXM.keeps R R'.
Proof. intros RP j Hj. apply (L5SAR.cs_of_preserved R R' j RP). revert j Hj. apply (L5K.incl_b PNADXM.KB). vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma to_end (E : dve) (X : dkc L ar HI E) (fx1 fx2 : FPState) R1 R2 (pc1 : Z) Mc modelc LKc Ac (M2v : mem) (q : Z) :
  dst L ar HI E Mc modelc LKc Ac ->
  msteps RSEGS (st fx1 R1 pc1 (mrestrict (ahid Ac modelc) Mc)) (st fx2 R2 0xb46b0 M2v) ->
  mem_grows (mrestrict (ahid Ac modelc) Mc) M2v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + 1) -> M2v (Z_to_bv 64 a) = mrestrict (ahid Ac modelc) Mc (Z_to_bv 64 a)) ->
  vfirst E <= q <= vfirst E + 40 -> PNADD.stE (vR E) (vsp E) (vF E) q 0 R2 ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx1 R1 pc1 Mc modelc) (vK E).
Proof.
  intros ST MS MG FZ Hq SE.
  apply (PNADK.dk_piece L ar C HI LY HIok E X fx1 fx2 R1 R2 pc1 0xb46b0 Mc modelc LKc Ac M2v (fun a => q <= a < q + 1) ST MS MG FZ).
  { intros a Wa. unfold Wmid. do 5 right. clear - Wa Hq. lia. }
  intros M3 model3 ST3 HID3 VIS3.
  apply (PNADM.out_to_end L ar C HI LY HIok E X fx2 R2 M3 model3 LKc Ac q 0 ST3).
  unfold PNADD.out_post. split; [exact SE|]. split; [exact (proj1 (dmem_of L ar C HI LY HIok E X M3 model3 LKc Ac ST3))|].
  split; [clear - Hq; lia| left; reflexivity].
Qed.

Theorem special_ok : out_stmt L ar HI -> PNADM.special_stmt L ar HI.
Proof.
  intros OUT E X fx Rc Mc modelc LKc Ac sigma hi lo ST Hs Hhi Hlo VP SX.
  dgeom L ar HI E X.
  pose proof (dmem_of L ar C HI LY HIok E X Mc modelc LKc Ac ST) as DM. unfold dmem, PNADD.MIA, PNST.sso_lit in DM.
  destruct DM as ((MWS & MWF & MFW & _ & _ & _ & _ & _ & _ & _ & _ & MZF6 & _) & _ & MIMG0 & _ & _ & _ & (MSI1 & _) & (MSN1 & _)).
  unfold PNADD.SH, PNADD.SBv in MZF6.
  destruct (gmem_of L ar C HI LY HIok E X _ Mc modelc LKc Ac (dsg_of_dst L ar HI E _ _ _ _ ST)) as (((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M176 & _) & _) & _).
  destruct SX as (((Q2 & Q3 & Q4 & Q8 & Q9 & Q23 & Q26 & Q27) & Q19 & Q20 & Q30) & Q18 & Q11 & Q10 & Q13).
  change (2 ^ 32) with 4294967296 in Q13.
  assert (RFc : PNADXM.RF (vR E) (vsp E) (vF E) Rc) by (unfold PNADXM.RF, PNADD.RBA; repeat split; assumption).
  pose proof (PNADXM.fork (vR E) (vsp E) (vF E) (vfirst E) sigma) as FK. L5SAR.feed FK ltac:(assumption).
  destruct (FK fx Rc _ hi lo RFc Q18 Q20 Q30 Q11 Q10 Q13 Hhi Hlo MWS) as (fx1 & R1 & pc1 & MS1 & K1 & B18 & B20 & B30 & B11 & B10 & B13 & [-> | [-> | ->]]); clear FK.
  - (* [comment removed for export] *)
    pose proof (PNADXM.RF_keeps _ _ _ Rc R1 RFc K1) as RF1.
    pose proof (PNADXM.nan_call (vR E) (vsp E) (vF E) (vfirst E) sigma) as NC. L5SAR.feed NC ltac:(assumption).
    destruct (NC fx1 R1 _ RF1 B18 B20 B30 MWS MSN1 M176) as (fx2 & R2 & MS2 & K2 & A1 & A10 & A11 & A12 & A18 & A20 & A21); clear NC.
    apply (PNADK.dk_piece L ar C HI LY HIok E X fx fx2 Rc R2 _ _ Mc modelc LKc Ac _ (fun _ => False) ST (msteps_trans _ _ _ _ MS1 MS2) (fun a Ha => Ha) (fun a _ _ => eq_refl) (fun a Wa => False_ind _ Wa)).
    intros M3 model3 ST3 HID3 VIS3.
    pose proof ST3 as (_ & _ & _ & _ & _ & _ & ERR3 & _ & _ & ZSIG3). pose proof ERR3 as (_ & DEC & _). rewrite bax_dec_add in DEC.
    cbn [PNST.bdec_ok PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj PMA.AN NADDR_A] in DEC. destruct DEC as (_ & _ & _ & (_ & SN2)).
    pose proof (PNADXM.RF_keeps _ _ _ R1 R2 RF1 K2) as RF2. pose proof RF2 as ((T2 & T3 & T4 & _) & _).
    match type of A11 with getr _ _ = Z_to_bv 64 ?src => match type of A1 with getr _ _ = Z_to_bv 64 ?ra => apply (dg_memcpy E X _ fx2 R2 M3 model3 LKc Ac (vfirst E) src 3 ra (dsg_of_dst L ar HI E _ _ _ _ ST3) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) SN2 A10 A11 A12) end end.
    { rewrite T4. exact (c_Rtp L ar HI E X). } { exact A1. } { reflexivity. } { clear; lia. } { exact T2. }
    intros R4 M4 model4 RP4 ST4 ZS4.
    assert (DST4 : dst L ar HI E M4 model4 LKc Ac) by (apply (PNADK.dst_of_dsg L ar HI E _ _ _ _ ST4); exact (ZS4 ZSIG3)).
    pose proof (PNADXM.RF_keeps _ _ _ R2 R4 RF2 (keeps_cs R2 R4 RP4)) as RF4.
    assert (C18 : getr R4 (reg 18) = getr R2 (reg 18)) by (apply (L5SAR.cs_of_preserved R2 R4 18%nat RP4); apply L5K.In_of_mem; vm_compute; reflexivity). rewrite A18 in C18.
    assert (C20 : getr R4 (reg 20) = getr R2 (reg 20)) by (apply (L5SAR.cs_of_preserved R2 R4 20%nat RP4); apply L5K.In_of_mem; vm_compute; reflexivity). rewrite A20 in C20.
    assert (C21 : getr R4 (reg 21) = getr R2 (reg 21)) by (apply (L5SAR.cs_of_preserved R2 R4 21%nat RP4); apply L5K.In_of_mem; vm_compute; reflexivity). rewrite A21 in C21.
    pose proof (dmem_of L ar C HI LY HIok E X M4 model4 LKc Ac DST4) as DM4. unfold dmem, PNADD.MIA, PNST.sso_lit in DM4.
    destruct DM4 as ((NWS & NWF & _ & _ & _ & _ & _ & _ & _ & _ & _ & NZF6 & _) & _ & _ & _ & _ & _ & _ & (NSN1 & _)).
    unfold PNADD.SH, PNADD.SBv in NZF6.
    pose proof (PNADXM.nan_tail (vR E) (vsp E) (vF E) (vfirst E) sigma) as NT. L5SAR.feed NT ltac:(assumption).
    destruct (NT fx2 R4 _ RF4 C18 C20 C21 NWS NSN1 NWF NZF6) as (fx5 & R5 & M5 & MS5 & MG5 & FZ5 & SE5); clear NT.
    exact (to_end E X fx2 fx5 R4 R5 _ M4 model4 LKc Ac M5 (vfirst E + 3) DST4 MS5 MG5 FZ5 ltac:(clear; lia) SE5).
  - (* [comment removed for export] *)
    pose proof (PNADXM.RF_keeps _ _ _ Rc R1 RFc K1) as RF1.
    pose proof (PNADXM.inf_call (vR E) (vsp E) (vF E) (vfirst E) sigma) as NC. L5SAR.feed NC ltac:(assumption).
    destruct (NC fx1 R1 _ RF1 B18 B20 B30 MWS MSI1 M176) as (fx2 & R2 & MS2 & K2 & A1 & A10 & A11 & A12 & A18 & A20); clear NC.
    apply (PNADK.dk_piece L ar C HI LY HIok E X fx fx2 Rc R2 _ _ Mc modelc LKc Ac _ (fun _ => False) ST (msteps_trans _ _ _ _ MS1 MS2) (fun a Ha => Ha) (fun a _ _ => eq_refl) (fun a Wa => False_ind _ Wa)).
    intros M3 model3 ST3 HID3 VIS3.
    pose proof ST3 as (_ & _ & _ & _ & _ & _ & ERR3 & _ & _ & ZSIG3). pose proof ERR3 as (_ & DEC & _). rewrite bax_dec_add in DEC.
    cbn [PNST.bdec_ok PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj PMA.AN NADDR_A] in DEC. destruct DEC as (_ & _ & (_ & SI2) & _).
    pose proof (PNADXM.RF_keeps _ _ _ R1 R2 RF1 K2) as RF2. pose proof RF2 as ((T2 & T3 & T4 & _) & _).
    match type of A11 with getr _ _ = Z_to_bv 64 ?src => match type of A1 with getr _ _ = Z_to_bv 64 ?ra => apply (dg_memcpy E X _ fx2 R2 M3 model3 LKc Ac (vfirst E + sigma) src 8 ra (dsg_of_dst L ar HI E _ _ _ _ ST3) ltac:(clear - Hs; lia) ltac:(clear - Hs; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) SI2 A10 A11 A12) end end.
    { rewrite T4. exact (c_Rtp L ar HI E X). } { exact A1. } { reflexivity. } { clear; lia. } { exact T2. }
    intros R4 M4 model4 RP4 ST4 ZS4.
    assert (DST4 : dst L ar HI E M4 model4 LKc Ac) by (apply (PNADK.dst_of_dsg L ar HI E _ _ _ _ ST4); exact (ZS4 ZSIG3)).
    pose proof (PNADXM.RF_keeps _ _ _ R2 R4 RF2 (keeps_cs R2 R4 RP4)) as RF4.
    assert (C18 : getr R4 (reg 18) = getr R2 (reg 18)) by (apply (L5SAR.cs_of_preserved R2 R4 18%nat RP4); apply L5K.In_of_mem; vm_compute; reflexivity). rewrite A18 in C18.
    assert (C20 : getr R4 (reg 20) = getr R2 (reg 20)) by (apply (L5SAR.cs_of_preserved R2 R4 20%nat RP4); apply L5K.In_of_mem; vm_compute; reflexivity). rewrite A20 in C20.
    pose proof (dmem_of L ar C HI LY HIok E X M4 model4 LKc Ac DST4) as DM4. unfold dmem, PNADD.MIA, PNST.sso_lit in DM4.
    destruct DM4 as ((NWS & NWF & _ & _ & _ & _ & _ & _ & _ & _ & _ & NZF6 & _) & _ & _ & _ & _ & _ & (NSI1 & _) & _).
    unfold PNADD.SH, PNADD.SBv in NZF6.
    pose proof (PNADXM.inf_tail (vR E) (vsp E) (vF E) (vfirst E) sigma) as NT. L5SAR.feed NT ltac:(assumption).
    destruct (NT fx2 R4 _ RF4 C18 C20 NWS NSI1 NWF NZF6) as (fx5 & R5 & M5 & MS5 & MG5 & FZ5 & SE5); clear NT.
    exact (to_end E X fx2 fx5 R4 R5 _ M4 model4 LKc Ac M5 (vfirst E + sigma + 8) DST4 MS5 MG5 FZ5 ltac:(clear - Hs; lia) SE5).
  - (* [comment removed for export] *)
    pose proof (PNADXM.RF_keeps _ _ _ Rc R1 RFc K1) as RF1.
    pose proof (PNADXM.noncanon (vR E) (vsp E) (vF E) (vfirst E) sigma) as NC. L5SAR.feed NC ltac:(assumption).
    destruct (NC fx1 R1 _ hi lo RF1 B18 B20 B30 B11 B10 B13 Hhi Hlo MWS MFW MIMG0) as (fx2 & R2 & M2 & MS2 & MG2 & FZ2 & SP & CZ); clear NC.
    apply (PNADK.dk_piece L ar C HI LY HIok E X fx fx2 Rc R2 _ _ Mc modelc LKc Ac M2 (fun a => vsp E - 240 <= a < vsp E - 176 \/ vsp E - 168 <= a < vsp E - 160 \/ vsp E - 136 <= a < vsp E - 120 \/ vF E + 32 <= a < vF E + 36) ST (msteps_trans _ _ _ _ MS1 MS2) MG2 FZ2).
    { intros a Wa. unfold Wmid. destruct Wa as [Y|[Y|[Y|Y]]]; [left| right; left| right; right; left| do 3 right; left]; clear - Y; lia. }
    intros M3 model3 ST3 HID3 VIS3.
    pose proof (dmem_of L ar C HI LY HIok E X M3 model3 LKc Ac ST3) as (MIA3 & _). rewrite HID3, VIS3 in MIA3.
    apply (OUT E X fx2 R2 M3 model3 LKc Ac sigma (Z.land (hi / 4294967296 / 32768) 16383) 0 1 ST3).
    + rewrite HID3, VIS3. unfold PNADD.out_pre. split; [exact SP|]. split; [exact MIA3|].
      split. { intros i Hi. exists 0. replace i with 0 by (clear - Hi; lia). split; [exact CZ| clear; lia]. }
      split; [exact Hs|]. split; [exact (PNADMID.e14_range _)|]. split; [clear; lia|]. split; [clear; lia| clear; lia].
    + intros fx9 R9 M9 model9 LK9 A9 ptr ec ST9 OP9. exact (PNADM.out_to_end L ar C HI LY HIok E X fx9 R9 M9 model9 LK9 A9 ptr ec ST9 OP9).
Qed.

End WithHeap.
End SCFG_1.
End PNADX.
