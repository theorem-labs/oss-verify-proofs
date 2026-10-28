(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParSpecs PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PmAUarK_b PmAUar_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnDecFacts. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnSpecsAXD_b PnADec128Defs_b PnADec128K_b PnADec128P1_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNADE.
Import L5A. Import L5CA. Import L5SAR. Import PNADK.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation mem := (word -> option byte).

(* [comment removed for export] *)
Definition rgd (E : dve) (R : bvmap 5 word) : Prop :=
  PNADD.RBA (vR E) (vsp E) (vF E) R /\ getr R (reg 19) = Z_to_bv 64 PNADD.SBv /\ getr R (reg 20) = Z_to_bv 64 (vfirst E)
  /\ getr R (reg 24) = Z_to_bv 64 (vvp E).

(* [comment removed for export] *)
Lemma up48 first x : first mod 8 = 0 -> x mod 8 = 0 -> first + 42 <= x -> first + 48 <= x.
Proof.
  intros F8 X8 H. pose proof (Z.div_mod first 8 ltac:(lia)) as D1. pose proof (Z.div_mod x 8 ltac:(lia)) as D2. rewrite F8 in D1. rewrite X8 in D2. lia.
Qed.
Lemma mod32_8 x : x mod 32 = 0 -> x mod 8 = 0.
Proof. intros H. pose proof (Z.div_mod x 32 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D. replace (32 * (x / 32)) with ((4 * (x / 32)) * 8) by lia. apply Z_mod_mult. Qed.
Lemma mod16_8 x : x mod 16 = 0 -> x mod 8 = 0.
Proof. intros H. pose proof (Z.div_mod x 16 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D. replace (16 * (x / 16)) with ((2 * (x / 16)) * 8) by lia. apply Z_mod_mult. Qed.

Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithHeap.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

(* [comment removed for export] *)
Lemma berr_keep LB FF sp scr W M M' ax :
  L5SAR.ek L ar LB FF sp scr W M M' -> (forall a, 65536 <= a < 6905856 -> L5.outside W a) ->
  PNSTA.berr_okA RSEGS PMA.AD PMA.AAD PMA.AN M ax -> PNSTA.berr_okA RSEGS PMA.AD PMA.AAD PMA.AN M' ax.
Proof.
  intros EK OUT ERR. apply (PNSTA.berr_okA_frame RSEGS PMA.AD PMA.AAD PMA.AN PMA.addrs_wf_B M M'); [| exact ERR].
  intros a Ha D. apply EK. split; [exact Ha|]. pose proof (PNADK.depA_img a D) as DI. split; [| apply OUT; exact DI].
  unfold aclient, aclient_g. right; right; left.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia| exact (PMA.ly_static L C LY a D)].
Qed.

(* [comment removed for export] *)
Definition at_guards : Prop :=
  forall (E : dve), dkc L ar HI E ->
  forall (fx : FPState) (Rc : bvmap 5 word) (Mc : mem) (modelc : Model) (LKc : list fframe) (Ac : list (Z * Z)),
    dsg L ar HI E (vax E) Mc modelc LKc Ac -> rgd E Rc ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx Rc 0xb3fac Mc modelc) (vK E).

Theorem entry : at_guards -> @PNSAXD.dec128_spec SCFG_P RSEGS PMA.AD PMA.AN PMA.AAD L ar HI.
Proof.
  intros GUARDS. unfold PNSAXD.dec128_spec.
  intros fx R M model K LB FF LK Aw cr first vp sp r ax HH AM K0 ENT FRM FRS SP32 A10 A11 A12 BLK DF VS1 VS2 DV ACV F8 ACF V8 BASE ERR KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 3) with 18432 in *.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12.
  destruct BLK as (Bq & Bm & HB & HB1 & HB2).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG. unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP, FSCEIL, FSIMG.
  destruct (WB _ HB) as ((BB0 & BBI & BB16 & BBn & BBC & BBA) & _ & _ & _ & _ & _ & BFS). cbn [fst snd] in *.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in BBI. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in BBA.
  pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF LK cr Aw M model HH BASE) as (VM0 & VM1 & VM2).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 18432 256 HH ASTK ltac:(clear; lia)) as (SL128 & SH128 & SWR).
  (* [comment removed for export] *)
  assert (VR1 : 0x696000 <= vp) by (clear - VS1 SL128 SLO SPT; lia).
  assert (VR3 : vp + 16 <= 2 ^ 47) by (clear - VS2 SPT; lia).
  assert (VBIG : 0x7fff7000 + 17592186048512 <= vp \/ vp + 16 <= 0x7fff7000) by (left; clear - VS1 SL128 SLO SPT; lia).
  assert (VCLg : forall sp' scr', sp' <= sp -> forall i, 0 <= i < 16 -> aclient L ar LB FF sp' scr' (vp + i)).
  { intros sp' scr' Hsp i Hi. apply (L5SAR.stack_client L ar LB FF sp' scr' (vp + i)); [clear - Hi VS1 VS2 SLO SPT; lia| clear - Hi VS1 Hsp; lia]. }
  pose proof (VCLg sp 18432 ltac:(clear; lia)) as VCL.
  assert (VSCL : forall i, 0 <= i < 16 / 8 -> aclient L ar LB FF sp 18432 (vp / 8 + SB + i)).
  { change (16 / 8) with 2. intros i Hi. apply (L5SAR.stk_shadow_client L ar LB FF sp 18432 (vp / 8 + SB + i)); [| clear - SPT; lia]. revert i Hi.
    intros i Hi. unfold in_shadow_of, S. pose proof (Z.div_le_mono (ahl_ceil ar) vp 8 ltac:(clear; lia) ltac:(clear - VS1 SLO; lia)) as Q1.
    pose proof (Z.div_le_mono (vp + 8) (ahl_ceil ar + (ar_sptop ar - ahl_ceil ar) - 1) 8 ltac:(clear; lia) ltac:(clear - VS2; lia)) as Q2.
    replace (vp + 8) with (vp + 1 * 8) in Q2 by (clear; lia). rewrite Z.div_add in Q2 by (clear; lia). clear - Hi Q1 Q2. lia. }
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (_ & VISs & _).
  assert (IMGC : L5.img_clear MV 1249280 1282048) by (intros i Hi; apply VM0; clear - Hi; lia).
  assert (QA : 0 <= sp < 2 ^ 64 /\ 0 <= first < 2 ^ 64 /\ 0 <= vp < 2 ^ 64 /\ 140735332487296 <= sp <= 140737488355328)
    by (clear - SL128 SHI SPT BB0 HB1 HB2 BBA VR1 VR3; lia).
  destruct QA as (QAs & QAf & QAv & QS).
  LeanFeed.pfeed P (PNADP1.adkA_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => first | 34%nat => vp | _ => 0 end)) ltac:(first [assumption | unfold PNADP1.aligned; assumption]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T12 & T19 & T20 & T22 & T24 & T27
                 & C104 & C96 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8 & C256 & C176).
  unfold PMSPA.cfg. change (PNL.pn_dec128 PMA.AN) with 0xb3e24.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xb3e24 R1 0x5df30 M1v (fun a => sp - 256 <= a < sp - 256 + 256) K HH AM MS1 MG1).
  { intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. split; [|intros X; clear - X Wa QS; lia]. unfold aclientw, aclient_g. right; left. split; [clear - Wa SL128 SHI SPT; lia| intros X; clear - X; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
  assert (NCS0 : forall a, sp - 256 <= a < sp -> ~ aclient L ar LB FF sp 18432 a).
  { intros a Xa Hc. destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 18432 a HH SPT Hc) as [Y|Y].
    - clear - Xa Y; lia.
    - clear - Xa Y SL128; lia. }
  assert (EK01 : L5SAR.ek L ar LB FF sp 18432 [] M M1).
  { apply (L5SAR.ek_piece L ar LB FF sp 18432 [] M M1 (fun a => sp - 256 <= a < sp - 256 + 256) FR1). intros a Ha Hc _ X. apply (NCS0 a); [clear - X; lia| exact Hc]. }
  assert (DK01 : L5SAR.dk L ar LB FF sp 18432 M M1) by (apply L5SAR.dk_grows; exact MGM1).
  assert (SV1 : forall a v, sp - 256 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
  { intros a v Ha1 Ha2 X. apply (proj1 (L5A.u64_at_vis H M1 a v (VISs a 8 ltac:(clear - Ha1 SL128 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL128 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))).
    rewrite VIS1. exact X. }
  assert (U1 : bv_unsigned (getr R (reg 1)) = r) by (rewrite Rra; apply L5.unsigned_lit; clear - Hr1; lia).
  rewrite U1 in C8.
  assert (OWN1 : own sp R r M1).
  { unfold own, PNADD.saves. repeat split; (apply SV1; [clear; lia| clear; lia| assumption]). }
  assert (C176m : L5.u64_at RSEGS M1 (sp - 176) (first + 42)) by (apply SV1; [clear; lia| clear; lia|]; rewrite L5.unsigned_lit in C176 by (clear - QAf HB2 BBA; lia); exact C176).
  clear C104 C96 C88 C80 C72 C64 C56 C48 C40 C32 C24 C16 C8 SV1.
  (* [comment removed for export] *)
  assert (FRk3 : ff_room 3 FF LK) by (apply (PMAUAR.ff_room_ofB PNRA.FCB 3 FF LK 3 FRM); [clear; lia| right; right; left; reflexivity]).
  change 0x5df30 with (PMA.SM_PC 3).
  apply (PMAUAR.uar_sm L ar C HI LY HIok 3 LB [] FF LK cr Aw sp 18432 (sp - 256) (sp - 104) sp (ocell sp) (own sp R r)
           fx1 R1 M M1 model model1 K 0xb3e9c ltac:(right; right; left; reflexivity) HH HH1 AM1 K0 ASTK MGM1 EK01 DK01).
  { rewrite L5K.rl2. exact T2. }
  { rewrite L5K.rl4. rewrite (KS1 4%nat) by inl. rewrite <- L5K.rl4. exact Rtp. }
  { rewrite L5K.rl1. exact T1. }
  { reflexivity. }
  { clear; lia. }
  { replace (sp - 256) with (sp + (-16) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { clear; lia. } { clear; lia. } { clear; lia. } { clear; lia. }
  { intros a Ha. exact Ha. }
  { intros Ma Mb OW AG. apply (own_agree sp R r Ma Mb ltac:(clear - SL128 SPT; lia) ltac:(clear - SHI SPT; lia) OW AG). }
  { exact FRk3. }
  { intros f Hf. specialize (FRS f Hf). clear - FRS; lia. }
  intros R2 M2 model2 F fl LK2 G G10 RP2 AM2 MRT2 ASTK2 EK02 DK02 EK12 DK12 AGF FW FSHW FSHZ FLC FLW FDEF VF VSH VFL APART.
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *. change (512 - 8) with 504 in *. cbn [app] in *.
  pose proof G as G'. destruct G' as [_ _ _ _ _ _ _ GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *. cbn [app] in GHH2.
  assert (HH2 : ri_inv HI LB ((F, 3, sp - 256 + 32) :: FF) LK2 cr Aw M2 (vml_of model2)) by exact GHH2.
  set (FF' := (F, 3, sp - 256 + 32) :: FF) in *.
  set (H2 := ahid Aw model2) in *. set (MV2 := mrestrict H2 M2) in *.
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 sp 18432 256 HH2 ASTK2 ltac:(clear; lia)) as (_ & _ & SWR2).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LK2 cr Aw M2 model2 HH2) as (_ & VISs2 & _).
  (* [comment removed for export] *)
  assert (CLF : forall i, 0 <= i < 42 -> aclient L ar LB FF 0 0 (first + i)).
  { intros i Hi. apply (L5SAR.block_client L ar LB FF 0 0 Bq Bm); [exact HB| clear - Hi HB1 HB2; lia]. }
  destruct (APART first 42 0 0 CLF ltac:(clear; lia)) as (ApF & ApSF & ApFL).
  destruct (APART vp 16 0 0 ltac:(intros i Hi; apply (VCLg 0 0 ltac:(clear - QS; lia) i Hi)) ltac:(clear; lia)) as (AvF & AvSF & AvFL).
  assert (BVAP : Bq + Bm <= vp \/ vp + 16 <= Bq) by (left; clear - BBC VS1 SLO; lia).
  assert (F8' : F mod 8 = 0) by (apply mod32_8; exact GF32).
  assert (GEOM : PNADD.geom sp first vp F fl).
  { unfold PNADD.geom.
    assert (X1 : 140735332483456 <= sp <= 140737488355328) by (clear - QS; lia).
    assert (X2 : 4096 <= first <= 140737488355280).
    { pose proof (up48 first 140737488355328 F8 ltac:(reflexivity) ltac:(clear - HB2 BBA; lia)) as Y. clear - Y BB0 HB1. lia. }
    assert (X3 : 2147446784 + 17592186048512 <= first \/ first + 48 <= 2147446784).
    { destruct BBA as (_ & [Y|Y] & _); [right; apply (up48 first 2147446784 F8 ltac:(reflexivity)); clear - Y HB2; lia| left; clear - Y HB1; lia]. }
    assert (X4 : sp - 256 + 256 <= first \/ first + 48 <= sp - 256) by (right; clear - BBC HB2 SL128; lia).
    assert (X5 : 65536 + 6840320 <= first \/ first + 48 <= 65536).
    { destruct BBI as [Y|Y]; [right; apply (up48 first 65536 F8 ltac:(reflexivity)); clear - Y HB2; lia| left; clear - Y HB1; lia]. }
    assert (X6 : 6905856 <= vp <= 140737488355312) by (clear - VR1 VR3; lia).
    assert (X7 : 2147446784 + 17592186048512 <= vp \/ vp + 16 <= 2147446784) by (clear - VBIG; lia).
    assert (X8 : sp - 256 + 256 <= vp \/ vp + 16 <= sp - 256) by (left; clear - VS1; lia).
    assert (X9 : first + 48 <= vp \/ vp + 16 <= first).
    { destruct BVAP as [Y|Y]; [left; apply (up48 first vp F8 V8); clear - Y HB2; lia| right; clear - Y HB1; lia]. }
    assert (X10 : 4096 <= F <= 140737488354816) by (clear - GFR; lia).
    assert (X11 : 2147446784 + 17592186048512 <= F \/ F + 512 <= 2147446784) by (clear - GFBIG; lia).
    assert (X12 : sp - 256 + 256 <= F \/ F + 512 <= sp - 256) by (right; clear - GFCEIL SL128; lia).
    assert (X13 : 65536 + 6840320 <= F \/ F + 512 <= 65536) by (left; clear - GFR; lia).
    assert (X14 : first + 48 <= F \/ F + 512 <= first).
    { destruct ApF as [Y|Y]; [left; apply (up48 first F F8 F8'); exact Y| right; exact Y]. }
    assert (X15 : vp + 16 <= F \/ F + 512 <= vp) by exact AvF.
    assert (X16 : 4096 <= fl <= 140737488355327) by (clear - GFLR; lia).
    assert (X17 : 2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784) by (clear - GFLBIG; lia).
    assert (X18 : F + 512 <= fl \/ fl + 1 <= F) by (clear - GFLA; lia).
    assert (X19 : sp - 256 + 256 <= fl \/ fl + 1 <= sp - 256) by (right; clear - GFLR SL128; lia).
    repeat split; first [ assumption | exact SP32 | exact F8 | exact V8 | exact GF32 | (clear - X1; lia) | (clear - X2; lia) | (clear - X6; lia) | (clear - X10; lia) | (clear - X16; lia) ]. }
  (* [comment removed for export] *)
  assert (R2c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (reg j) = getr R1 (reg j)).
  { intros j Hj. apply (L5SAR.cs_of_preserved R1 R2 j RP2 Hj). }
  assert (B2R : getr R2 (reg 2) = Z_to_bv 64 (sp - 256)) by (rewrite (R2c 2%nat) by inl; exact T2).
  assert (B8R : getr R2 (reg 8) = Z_to_bv 64 sp) by (rewrite (R2c 8%nat) by inl; exact T8).
  assert (B9R : getr R2 (reg 9) = Z_to_bv 64 (sp - 256)) by (rewrite (R2c 9%nat) by inl; exact T9).
  assert (B20R : getr R2 (reg 20) = Z_to_bv 64 first) by (rewrite (R2c 20%nat) by inl; exact T20).
  pose proof T19 as B19R. rewrite <- (R2c 19%nat) in B19R by inl.
  assert (B24R : getr R2 (reg 24) = Z_to_bv 64 vp) by (rewrite (R2c 24%nat) by inl; exact T24).
  assert (B10R : getr R2 (reg 10) = Z_to_bv 64 F) by (rewrite <- L5K.rl10; exact G10).
  assert (FLCv : L5.u64_at RSEGS MV2 (F + 504) fl) by (replace (F + 504) with (F + 512 - 8) by (clear; lia); exact FLC).
  assert (Q0 : 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64) by (clear - GFR GFLR; lia).
  destruct Q0 as (Q0f & Q0g).
  pose proof GEOM as (GS1 & GS32 & GF1 & GFA8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  assert (Q9 : (65536 + 6840320 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 64 <= 65536)) by (left; clear - GFR; pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)); lia).
  assert (Q10 : (65536 + 6840320 <= fl \/ fl + 1 <= 65536)) by (left; clear - GFLR; lia).
  LeanFeed.pfeed P (PNADP1.adkB1_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 33%nat => first | 34%nat => vp | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNADP1.aligned; assumption]).
  destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y18 & Y19 & Y23 & Y26 & Y27
                 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPC & HDESC & HMAG & D24 & SAVF).
  set (W3 := fun a => (sp - 144 <= a < sp - 144 + 8) \/ (F <= a < F + 24) \/ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 40)).
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF' LK2 cr Aw M2 model2 fx1 fx3 R2 0xb3e9c R3 0xb3fac M3v W3 K HH2 AM2 MS3 MG3).
  { intros a Ha Hn. apply FRZ3; [exact Ha| intros X; apply Hn; left; clear - X; lia| intros X; apply Hn; right; left; clear - X; lia
                    | intros X; apply Hn; right; right; clear - X; lia]. }
  { intros a Ha Wa. split.
    - destruct Wa as [X|[X|X]].
      + unfold aclientw, aclient_g. right; left. split; [clear - X SL128 SHI SPT; lia| intros Y; clear - Y; lia].
      + apply (L5SAR.fframe_client L ar LB FF' 0 0 F 3 (sp - 256 + 32)); [left; reflexivity| change (ff_bytes 3) with 512; clear - X; lia].
      + apply (L5SAR.fframe_shadow_client L ar LB FF' 0 0 F 3 (sp - 256 + 32)); [left; reflexivity|]. change (ff_bytes 3) with 512.
        unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - X; lia.
    - destruct Wa as [X|[X|X]]; [clear - X QS; lia| clear - X GFFI; lia| clear - X GFR; pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)); lia]. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3. change (mrestrict H2 M3 = M3v) in VIS3.
  assert (EK23 : L5SAR.ek L ar LB FF sp 18432 [] M2 M3).
  { apply (L5SAR.ek_piece L ar LB FF sp 18432 [] M2 M3 W3 FR3). intros a Ha Hc _ X. destruct X as [X|[X|X]].
    - apply (NCS0 a); [clear - X; lia| exact Hc].
    - destruct (APART a 1 sp 18432 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (Y & _). clear - X Y; lia.
    - destruct (APART a 1 sp 18432 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (_ & Y & _). unfold SB in Y. clear - X Y; lia. }
  pose proof (L5SAR.ek_trans L ar LB FF sp 18432 [] M M2 M3 EK02 EK23) as EK03.
  assert (OWN3 : own sp R r M3).
  { apply (own_agree sp R r M1 M3 ltac:(clear - SL128 SPT; lia) ltac:(clear - SHI SPT; lia) OWN1). intros a Ha. unfold ocell in Ha.
    rewrite FR3; [apply AGF; clear - Ha; lia| clear - Ha SL128 SHI SPT; lia|].
    intros [X|[X|X]]; [clear - X Ha; lia| clear - X Ha GFFS; lia| clear - X Ha GFR QS; pose proof (Z.div_le_upper_bound F 8 17592186044416 ltac:(lia) ltac:(lia)); lia]. }
  set (E := DVE R r sp first vp ax LB FF LK Aw cr model M K F fl LK2 M2 model2).
  assert (BI3 : PMAUK.binv L ar HI M model LB FF LK Aw sp 18432 (sp - 256) (own sp R r) F 3 (W E) [] M3 model3 LK2 cr Aw).
  { unfold PMAUK.binv. cbn [app]. split; [exact HH3|]. split; [exact AM3|].
    split; [eapply L5LZ.model_rt_trans; [exact MRT1| eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3]]|].
    split; [apply incl_refl|]. split; [exact GLKI2|]. split; [exact (L5SAR.astk_grows ar M2 M3 sp 18432 ASTK2 MGM3)|].
    split; [apply (L5SAR.ek_W L ar LB FF sp 18432 (W E) [] M M3 EK03); intros a _ r0 []|].
    split; [apply (L5SAR.dk_trans L ar LB FF sp 18432 M M2 M3 DK02); apply L5SAR.dk_grows; exact MGM3|].
    split; [exact OWN3|].
    change (ff_bytes 3 / 8) with 64. apply (L5.defined_grows M2 M3 _ _ MGM3).
    apply (proj1 (L5A.defined_vis H2 M2 (F / 8 + SB) 64 VSH)). intros i Hi. pose proof (FSHZ i Hi) as Z0. unfold MV2 in Z0. rewrite Z0. discriminate. }
  (* [comment removed for export] *)
  assert (DK03 : L5SAR.dk L ar LB FF sp 18432 M M3) by (apply (L5SAR.dk_trans L ar LB FF sp 18432 M M2 M3 DK02); apply L5SAR.dk_grows; exact MGM3).
  assert (DF3 : L5.defined M3 first 42).
  { apply (PMASK.defined_dk L ar LB FF sp 18432 M M3 first 42 DK03); [| clear - QAf; lia| clear - GF1; lia| exact DF].
    intros i Hi. apply (L5SAR.block_client L ar LB FF sp 18432 Bq Bm); [exact HB| clear - Hi HB1 HB2; lia]. }
  assert (DV3 : L5.defined M3 vp 16).
  { apply (PMASK.defined_dk L ar LB FF sp 18432 M M3 vp 16 DK03); [| clear - QAv; lia| clear - GV1; lia| exact DV].
    intros i Hi. replace i with (vp + (i - vp)) by (clear; lia). apply VCL. clear - Hi; lia. }
  assert (AGS : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 18432 a -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hc. apply EK03. split; [exact Ha|]. split; [exact Hc| intros r0 []]. }
  assert (AF3 : PMSPA.accA M3 first 48).
  { apply (aacc_agree M M3 _ _); [| exact ACF]. intros a Ha. pose proof (S_rng first 48 a F8 ltac:(clear; lia) Ha) as SR. change ((48 + 7) / 8) with 6 in SR.
    apply AGS; [clear - SR GF1; pose proof (Z.div_pos first 8 ltac:(lia) ltac:(lia)); pose proof (Z.div_le_upper_bound first 8 17592186044416 ltac:(lia) ltac:(lia)); lia|].
    unfold aclient, aclient_g. do 6 right. exists (Bq, Bm). split; [exact HB|]. cbn [fst snd]. unfold in_shadow_of.
    pose proof (sh6_in_blk first Bq Bm (S a - (first / 8 + 2147450880)) F8 ltac:(clear - BB0; lia) HB1 HB2 ltac:(clear - SR; lia)) as X. unfold S, SB in *. clear - X. lia. }
  assert (AV3 : PMSPA.accA M3 vp 16).
  { apply (aacc_agree M M3 _ _); [| exact ACV]. intros a Ha. pose proof (S_rng vp 16 a V8 ltac:(clear; lia) Ha) as SR. change ((16 + 7) / 8) with 2 in SR.
    apply AGS; [clear - SR GV1; pose proof (Z.div_pos vp 8 ltac:(lia) ltac:(lia)); pose proof (Z.div_le_upper_bound vp 8 17592186044416 ltac:(lia) ltac:(lia)); lia|].
    change (16 / 8) with 2 in VSCL. replace (S a) with (vp / 8 + SB + (S a - (vp / 8 + SB))) by (clear; lia). apply VSCL. unfold SB. clear - SR. lia. }
  assert (BASE3 : PMSTA.base_okA RSEGS PMA.AD M3) by (apply (PMASK.base_keep L ar C LY LB FF sp 18432 [] M M3 EK03); [intros a _ r0 []| exact BASE]).
  assert (ERR3 : PNSTA.berr_okA RSEGS PMA.AD PMA.AAD PMA.AN M3 ax) by (apply (berr_keep LB FF sp 18432 [] M M3 ax EK03); [intros a _ r0 []| exact ERR]).
  assert (CF128 : L5.u64_at RSEGS M3 (sp - 144) F).
  { apply (proj1 (L5A.u64_at_vis H2 M3 (sp - 144) F (VISs2 (sp - 144) 8 ltac:(clear - SL128 SPT; lia) ltac:(clear - SHI SPT; lia)) ltac:(clear - SL128 SPT; lia) ltac:(clear - SHI SPT; lia))).
    rewrite VIS3. exact SAVF. }
  assert (CF176 : L5.u64_at RSEGS M3 (sp - 176) (first + 42)).
  { apply (L5C.u64_at_agree RSEGS M1 M3); [| clear - SL128 SPT; lia| clear - SHI SPT; lia| exact C176m]. intros i Hi.
    rewrite FR3; [apply AGF; clear - Hi; lia| clear - Hi SL128 SHI SPT; lia|].
  intros [X|[X|X]]; [clear - X Hi; lia| clear - X Hi GFFS; lia| clear - X Hi GFR QS; pose proof (Z.div_le_upper_bound F 8 17592186044416 ltac:(lia) ltac:(lia)); lia]. }
  assert (XC : dkc L ar HI E).
  { constructor; cbn [vR vr vsp vfirst vvp vax vLB vFF vLK vAw vcr vmodel vM vK vF vfl vLK2 vM2 vmodel2 E]; unfold PNADK.SCR;
      first [ exact GEOM | exact G | exact HH | exact K0 | exact Rra | exact RAok | exact Rsp | exact Rgp | exact Rtp | exact ASTK | exact STKSH | exact FRM | exact FRS | exact (conj VS1 VS2) | idtac ].
    - exists Bq, Bm. split; [exact HB|]. split; [exact HB1| exact HB2].
    - unfold PNADK.kont. cbn [vR vr vsp vfirst vvp vax vLB vFF vLK vAw vcr vmodel vM vK vF vfl vLK2 vM2 vmodel2 E]. unfold PNADK.SCR, PNADK.W. cbn [vfirst vax E]. exact KONT. }
  apply (GUARDS E XC fx3 R3 M3 model3 LK2 Aw).
  - unfold PNADK.dsg. cbn [vR vr vsp vfirst vvp vax vLB vFF vLK vAw vcr vmodel vM vK vF vfl vLK2 vM2 vmodel2 E]. unfold PNADK.SCR.
    split; [exact BI3|]. split; [exact DF3|]. split; [exact AF3|]. split; [exact DV3|]. split; [exact AV3|]. split; [exact BASE3|]. split; [exact ERR3|]. split; [exact CF128| exact CF176].
  - unfold rgd, PNADD.RBA, PNADD.SH, PNADD.SBv. cbn [vR vr vsp vfirst vvp vF E].
    assert (R1c : forall j, In j [3; 4]%nat -> getr R1 (reg j) = getr R (reg j)).
    { intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b [3; 4]%nat). vm_compute. reflexivity. }
    assert (K3 : forall j, In j [2; 3; 4; 8; 9; 20; 24]%nat -> getr R3 (reg j) = getr R2 (reg j)).
    { intros j Hj. apply KS3. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 20; 24]%nat). vm_compute. reflexivity. }
    split.
    { split; [rewrite (K3 2%nat) by inl; exact B2R|].
      split; [rewrite (K3 3%nat) by inl; rewrite (R2c 3%nat) by inl; apply R1c; inl|].
      split; [rewrite (K3 4%nat) by inl; rewrite (R2c 4%nat) by inl; apply R1c; inl|].
      split; [rewrite (K3 8%nat) by inl; exact B8R|]. split; [rewrite (K3 9%nat) by inl; exact B9R|].
      split; [exact Y23|]. split; [exact Y26| exact Y27]. }
    split; [exact Y19|]. split; [rewrite (K3 20%nat) by inl; exact B20R| rewrite (K3 24%nat) by inl; exact B24R].
Qed.

End WithHeap.
End SCFG_1.
End PNADE.
