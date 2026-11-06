(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA LibIface AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreA L5CoreSpecsA L5StepAR L5CoreBR L5ADetailHR PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAa PmModelFactsA PmStepA PmStep PmParStep PmParKit PmASrcKit PmAParKit PmAReset1 PmAUarK PmAUar PmARtvP.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmARtv () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmARtv.PMARTV."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAa.PMA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1cons"; "1false"; "1nat"; "1nil"; "1option"; "2and"; "2eq"; "3Z"; "0E"; "0H"; "0HI"; "0L"; "4bvmap"; "0M"; "0M1"]; ["0M1'"; "0R"; "5mrestrict"; "6ocell"; "6own"; "7make_ec_spec"; "7read_value_spec"; "7rtv_spec"; "7src_read_spec"; "8getr"; "8regupd"; "0SCFG_P"; "9In"; ":le"; ":lt"; ":of_nat"]; [":pow"; ":sub"; "0a"; "0ar"; "0k"; ";Z_to_bv"; ";bv"; "0v"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia.
Module PMARTV.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition own (E : Z) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
L5.u64_at RSEGS M (E - 8) (bv_unsigned (getr R (reg 1))) /\ L5.u64_at RSEGS M (E - 16) (bv_unsigned (getr R (reg 8)))
/\ L5.u64_at RSEGS M (E - 24) (bv_unsigned (getr R (reg 9))) /\ L5.u64_at RSEGS M (E - 32) (bv_unsigned (getr R (reg 18)))
/\ L5.u64_at RSEGS M (E - 40) (bv_unsigned (getr R (reg 19))) /\ L5.u64_at RSEGS M (E - 48) (bv_unsigned (getr R (reg 20)))
/\ L5.u64_at RSEGS M (E - 56) (bv_unsigned (getr R (reg 21))) /\ L5.u64_at RSEGS M (E - 64) (bv_unsigned (getr R (reg 22)))
/\ L5.u64_at RSEGS M (E - 72) (bv_unsigned (getr R (reg 23))) /\ L5.u64_at RSEGS M (E - 80) (bv_unsigned (getr R (reg 24)))
/\ L5.u64_at RSEGS M (E - 88) (bv_unsigned (getr R (reg 25))).
Definition ocell (E : Z) (a : Z) : Prop := E - 88 <= a < E.
Lemma own_agree : ltac2:(TCodec.tc2 tcn__PmARtv "QD'8&=y5'Q6yR0%211%5241'5y8%611%311p061pRB72&Mz&Q1r4+RH%3221%6251r5&Q0+2+R0%3221%<251&Dr6%2318<&Cr8r1%3221'7&Q5r2%22Q01%:11r7%113%73N31p091pR6Q:1%A3=5Gp021p0A1p0E1p0L1pQ2Q41pQ0Q61pQ4Q<1pDQC1").
Proof. intros E R M1 M1'.
intros H0 H1 (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) AG. unfold own, ocell in *.
repeat split; (eapply L5C.u64_at_agree; [ | | | eassumption]; [intros j Hj; apply AG; lia | lia | lia]).
Qed.
Lemma own_vis : ltac2:(TCodec.tc2 tcn__PmARtv "QJ'8&=y5'Q6yR0%211%5241'0pRB31'5y8%811%311p081'6&M&Q1r5+RH%3221r1%6221&N%1236%:231'7r4&Q5r2%22I1%411(2%73I21p091pR6Q21z%E21Ar6&Q0+2+R0%3221%K251&Dr7%2318Cr8&B%12;O%63351p051p091p0@1p0C1pNQ91pFQ?1pQ4QB1pDQI1").
Proof. intros E R H M.
intros HV H0 H1 O. apply (own_agree E R M (mrestrict H M) H0 H1 O). intros a Ha. unfold ocell in Ha.
apply mrestrict_visible. apply HV. exact Ha.
Qed.
Lemma reg12_other : ltac2:(TCodec.tc2 tcn__PmARtv "R0&=y5'Q6yR0%211%5241'3&Lr1(1u2u3u4u8u9uBuCuDuEuFuGuHuIuJuK(4%11D%B3E31%C3F51%D3G71%E3H91%F3I;1%G3J=1%H3K?1%I3LA1%J3MC1%K3NE1%L3OG1%M3Q0I1%N3Q1K1%O3Q2M1%Q03Q3O1%Q33Q4Q21'7&I&Jr4&Q5&Ou<%211%42QB1r3%83721r2%711%92QG1%=241%>2<2%@3QG21p0B1pR:QG1pR@QJ1pQ4QJ1").
Proof. intros R v k.
intros Hk. assert (Hk' : k <> 12%nat /\ (k < 32)%nat) by (repeat (destruct Hk as [<-|Hk]; [split; lia|]); destruct Hk).
apply PMPX.regupd_other_idx; lia.
Qed.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.
Theorem rtv_ok : ltac2:(TCodec.tc2 tcn__PmARtv "?&HvKv<vQ3v;%544321&E%146543&F%148765&G%14:987p031p061p091").
Proof.
intros SR MKE RV. unfold PMA.rtv_spec, PMSPA.rtv_spec, PMSPA.run_spec, PMSPA.run_spec_r.
intros fx R M model K LBX FF LK Aw cr sp r fb cat s str sm e HH AM K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 9) with 30720 in *. change (30720 / 8) with 3840 in STKSH.
pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
destruct ARGS as (A10 & A11 & A12).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12.
pose proof RPRE as (PA & IA & VIS & VREF & BASE & ERR & TBOK).
pose proof FOK as ((rs & Hfb) & Fal).
pose proof (PMAPAR.op_vis L ar C HI LY HIok _ FF LK cr Aw M model fb _ s HH FOK PA) as ((O1 & O8 & ONSH) & Zop & Z32 & Z20 & OWR & OCE & OVIS & AOP & Eop).
pose proof (PMASK.iss_vis L ar C HI LY HIok _ FF LK cr Aw M model fb str sm sp 30720 HH FOK IA ASTK) as ((I1 & I8 & INSH) & Zis & IWR & ICE & IVIS & AOI & IOS).
pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF LK cr Aw M model HH BASE) as (VM0 & VM1 & VM2).
pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 30720 96 HH ASTK ltac:(lia)) as (SL96 & SH96 & SWR).
pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY _ FF LK cr Aw M model 0x130290 1 HH ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as ZOT.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & STOP & _).
pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 4) with 1024 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, F1, F2.
set (op := PMSPA.o_p PMA.AD fb) in *. set (ov := PMSPA.o_v PMA.AD fb) in *. set (oec := PMSPA.o_ec PMA.AD fb) in *. set (ois := PMSPA.o_is PMA.AD fb) in *.
assert (Eoec : oec = fb + 992) by reflexivity. assert (Eois : ois = fb + 96) by reflexivity. assert (Eov : ov = fb + 432) by reflexivity.
set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
assert (AOF : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> PMSPA.aobjA FF a n).
{ intros a n X1 X2. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. lia. }
pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (_ & VISs & _).
cfeed P (PMARTP.artA_conc fx R MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | _ => 0 end)) ltac:(first [assumption | unfold PMARTP.aligned; assumption | clear - SL96 SHI SPT; lia | clear - O1; lia | clear - O1 Eop Eov; lia | clear - O1 Eop Eoec; lia]).
destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & _ & _ & T19 & T20 & T21 & T25
& C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8 & C96).
unfold PMSPA.cfg. cbn [pa_rtv PMA.AD ADDR_A].
apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xad164 R1 0x5d22c M1v (fun a => sp - 96 <= a < sp - 96 + 96) K HH AM MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
{ intros a Ha Wa. split; [|intros X; lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
set (LB := PM.parser_own s ++ LBX) in *.
assert (INCX : incl LBX LB) by (unfold LB; apply incl_appr; apply incl_refl).
assert (NCS0 : forall a, sp - 96 <= a < sp -> ~ aclient L ar LB FF sp 30720 a).
{ intros a Xa Hc. destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 30720 a HH SPT Hc) as [Y|Y].
- clear - Xa Y; lia.
- clear - Xa Y SL96; lia. }
assert (EK01f : L5SAR.ek L ar LB FF sp 30720 [] M M1).
{ apply (L5SAR.ek_piece L ar LB FF sp 30720 [] M M1 (fun a => sp - 96 <= a < sp - 96 + 96) FR1). intros a Ha Hc _ X. apply (NCS0 a); [clear - X; lia| exact Hc]. }
assert (DK01f : L5SAR.dk L ar LB FF sp 30720 M M1) by (apply L5SAR.dk_grows; exact MGM1).
pose proof (PMKA.ek_sublb L ar LB LBX FF sp 30720 [] M M1 INCX EK01f) as EK01.
pose proof (PMKA.dk_sublb L ar LB LBX FF sp 30720 M M1 INCX DK01f) as DK01.
assert (SV1 : forall a v, sp - 96 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
{ intros a v Ha1 Ha2 X. apply (proj1 (L5A.u64_at_vis H M1 a v (VISs a 8 ltac:(clear - Ha1 SL96 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL96 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))).
rewrite VIS1. exact X. }
assert (OWN1 : own sp R M1).
{ unfold own. split; [apply SV1; [clear; lia| clear; lia| exact C8]|]. split; [apply SV1; [clear; lia| clear; lia| exact C16]|].
split; [apply SV1; [clear; lia| clear; lia| exact C24]|]. split; [apply SV1; [clear; lia| clear; lia| exact C32]|].
split; [apply SV1; [clear; lia| clear; lia| exact C40]|]. split; [apply SV1; [clear; lia| clear; lia| exact C48]|].
split; [apply SV1; [clear; lia| clear; lia| exact C56]|]. split; [apply SV1; [clear; lia| clear; lia| exact C64]|].
split; [apply SV1; [clear; lia| clear; lia| exact C72]|]. split; [apply SV1; [clear; lia| clear; lia| exact C80]|].
apply SV1; [clear; lia| clear; lia| exact C88]. }
clear C88 C80 C72 C64 C56 C48 C40 C32 C24 C16 C8 C96 SV1.
assert (FRk0 : ff_room 0 FF LK) by (apply (PMAUAR.ff_room_of 9 FF LK 0 FRM); [clear; lia| left; reflexivity]).
change 0x5d22c with (PMA.SM_PC 0).
apply (PMAUAR.uar_sm L ar C HI LY HIok 0 LBX (PM.parser_own s) FF LK cr Aw sp 30720 (sp - 96) (sp - 88) sp (ocell sp) (own sp R)
fx1 R1 M M1 model model1 K 0xad1d4 ltac:(left; reflexivity) HH HH1 AM1 K0 ASTK MGM1 EK01 DK01).
{ rewrite L5K.rl2. exact T2. }
{ rewrite L5K.rl4. rewrite (KS1 4%nat) by inl. rewrite <- L5K.rl4. exact Rtp. }
{ rewrite L5K.rl1. exact T1. }
{ reflexivity. }
{ clear; lia. }
{ replace (sp - 96) with (sp + (-6) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
{ clear; lia. } { clear; lia. } { clear; lia. } { clear; lia. }
{ intros a Ha. exact Ha. }
{ intros Ma Mb OW AG. apply (own_agree sp R Ma Mb ltac:(clear - SL96 SPT; lia) ltac:(clear - SHI SPT; lia) OW AG). }
{ exact FRk0. }
{ intros f Hf. specialize (FRS f Hf). clear - FRS; lia. }
intros R2 M2 model2 F fl LK2 G G10 RP2 AM2 MRT2 ASTK2 EK02 DK02 EK12f DK12f AGF FW FSHW FSHZ FLC FLW FDEF VF VSH VFL APART.
change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *. change (64 - 8) with 56 in *.
pose proof G as G'. destruct G' as [_ _ _ _ _ _ _ GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
change (ff_bytes 0) with 64 in *.
pose proof (L5SAR.ek_trans L ar LB FF sp 30720 [] M M1 M2 EK01f EK12f) as EK02f.
pose proof (L5SAR.dk_trans L ar LB FF sp 30720 M M1 M2 DK01f DK12f) as DK02f.
pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
assert (PA2 : PM.parser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA M2 op ois s).
{ apply (PMKA.parser_keepA RSEGS PMA.AD L ar LB FF sp 30720 [] M M2 EK02f PMKA.wapp_nil FRB BRB _ _ _ AOP); [| intros i _ r0 []| intros i _ r0 []| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact PA].
unfold LB. apply incl_appl, incl_refl. }
assert (IA2 : PM.iss_at RSEGS PMA.AD PMSPA.accA M2 ois str sm).
{ apply (PMKA.iss_keepA RSEGS PMA.AD L ar LB FF sp 30720 [] M M2 EK02f PMKA.wapp_nil FRB BRB ois str sm AOI); [| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA].
unfold LB. apply incl_appr. exact INCS. }
assert (BASE2 : PMSTA.base_okA RSEGS PMA.AD M2) by (apply (PMASK.base_keep L ar C LY LB FF sp 30720 [] M M2 EK02f); [intros a _ r0 []| exact BASE]).
assert (HH2 : ri_inv HI LB ((F, 0, sp - 96 + 32) :: FF) LK2 cr Aw M2 (vml_of model2)) by exact GHH2.
pose proof (PMAPAR.op_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 fb _ s HH2 (PMAUAR.frame_okA_push FF fb F 0 (sp - 96 + 32) FOK) PA2)
as ((_ & _ & _) & Zop2 & Z322 & Z202 & OWR2 & _ & OVIS2 & _ & _).
set (FF' := (F, 0, sp - 96 + 32) :: FF) in *.
assert (FOK' : PMSPA.frame_okA FF' fb) by exact (PMAUAR.frame_okA_push FF fb F 0 (sp - 96 + 32) FOK).
set (H2 := ahid Aw model2) in *. set (MV2 := mrestrict H2 M2) in *.
pose proof (PMASK.mach_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 HH2 BASE2) as (W0 & W1 & W2).
pose proof (PMASK.stk_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 sp 30720 96 HH2 ASTK2 ltac:(lia)) as (_ & _ & SWR2).
pose proof (PMASK.iss_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 fb str sm sp 30720 HH2 FOK' IA2 ASTK2) as ((_ & _ & _) & Zis2 & IWR2 & _ & IVIS2 & _ & _).
pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY _ _ LK2 cr Aw M2 model2 0x130290 1 HH2 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as ZOT2.
pose proof PA2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PSRC2 & _). pose proof PSRC2 as (PS240 & _).
assert (U264 : L5.u64_at RSEGS MV2 (op + 264) ois).
{ replace (op + 264) with (op + 24 + 240) by (clear; lia).
apply (proj2 (L5A.u64_at_vis H2 M2 _ ois (OVIS2 (op + 24 + 240) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia))). exact PS240. }
pose proof IA2 as (IS0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IOSB & _). pose proof IOSB as (_ & IST & _ & _ & _ & _ & _ & _ & STV).
assert (UIS0 : L5.u64_at RSEGS MV2 ois 1245864) by (apply (proj2 (L5A.u64_at_vis H2 M2 ois _ (IVIS2 ois 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - I1; lia) ltac:(clear - I1; lia))); exact IS0).
assert (UIST : L5.u32_at RSEGS MV2 (ois + 152) (PM.sm_st sm)).
{ replace (ois + 152) with (ois + 120 + 32) by (clear; lia).
apply (proj2 (L5A.u32_at_vis H2 M2 _ _ (IVIS2 (ois + 120 + 32) 4 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - I1; lia) ltac:(clear - I1; lia))). exact IST. }
assert (CLfb : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> 0 < n -> forall i, 0 <= i < n -> aclient L ar LB FF 0 0 (a + i)).
{ intros a n X1 X2 X3 i Hi. unfold aclient, aclient_g. do 3 right; left. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
change (ff_bytes 4) with 1024. split; [clear - X1 X2 Hi; lia| intros Y; clear - X1 X2 Hi Y; lia]. }
destruct (APART op 384 0 0 (CLfb op 384 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (ApF & ApSF & ApFL).
destruct (APART ois 272 0 0 (CLfb ois 272 ltac:(clear - Eois; lia) ltac:(clear - Eois; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (AiF & AiSF & AiFL).
assert (CLsh : forall a n, fb / 8 + SB <= a -> a + n <= fb / 8 + SB + 128 -> 0 < n -> forall i, 0 <= i < n -> aclient L ar LB FF 0 0 (a + i)).
{ intros a n X1 X2 X3 i Hi. unfold aclient, aclient_g. do 5 right; left. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
change (ff_bytes 4) with 1024. unfold in_shadow_of, S. unfold SB in *.
assert (D1 : (fb + 1024 - 1) / 8 = fb / 8 + 127).
{ pose proof (Z.div_mod fb 1024 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
replace (1024 * (fb / 1024) + 1024 - 1) with (7 + (128 * (fb / 1024) + 127) * 8) by (clear; lia). rewrite Z.div_add by lia.
replace (1024 * (fb / 1024)) with ((128 * (fb / 1024)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
rewrite D1. clear - X1 X2 Hi. lia. }
assert (SHop : op / 8 + SB = fb / 8 + SB + 58).
{ rewrite Eop. pose proof (Z.div_mod fb 1024 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
replace (1024 * (fb / 1024) + 464) with ((128 * (fb / 1024) + 58) * 8) by (clear; lia). rewrite Z.div_mul by lia.
replace (1024 * (fb / 1024)) with ((128 * (fb / 1024)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
assert (SHis : ois / 8 + SB = fb / 8 + SB + 12).
{ rewrite Eois. pose proof (Z.div_mod fb 1024 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
replace (1024 * (fb / 1024) + 96) with ((128 * (fb / 1024) + 12) * 8) by (clear; lia). rewrite Z.div_mul by lia.
replace (1024 * (fb / 1024)) with ((128 * (fb / 1024)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
destruct (APART (op / 8 + SB) 48 0 0 (CLsh (op / 8 + SB) 48 ltac:(clear - SHop; lia) ltac:(clear - SHop; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (_ & AsopSF & _).
destruct (APART (ois / 8 + SB) 34 0 0 (CLsh (ois / 8 + SB) 34 ltac:(clear - SHis; lia) ltac:(clear - SHis; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (_ & AsisSF & _).
assert (R2c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (reg j) = getr R1 (reg j)).
{ intros j Hj. apply (L5SAR.cs_of_preserved R1 R2 j RP2 Hj). }
assert (B2R : getr R2 (reg 2) = Z_to_bv 64 (sp - 96)) by (rewrite (R2c 2%nat) by inl; exact T2).
assert (B8R : getr R2 (reg 8) = Z_to_bv 64 sp) by (rewrite (R2c 8%nat) by inl; exact T8).
assert (B9R : getr R2 (reg 9) = Z_to_bv 64 (sp - 96)) by (rewrite (R2c 9%nat) by inl; exact T9).
assert (B19R : getr R2 (reg 19) = Z_to_bv 64 oec) by (rewrite (R2c 19%nat) by inl; exact T19).
assert (B20R : getr R2 (reg 20) = Z_to_bv 64 op) by (rewrite (R2c 20%nat) by inl; exact T20).
assert (B21R : getr R2 (reg 21) = Z_to_bv 64 ov) by (rewrite (R2c 21%nat) by inl; exact T21).
assert (B25R : getr R2 (reg 25) = Z_to_bv 64 2147450880) by (rewrite (R2c 25%nat) by inl; exact T25).
assert (B10R : getr R2 (reg 10) = Z_to_bv 64 F) by (rewrite <- L5K.rl10; exact G10).
assert (FLCv : L5.u64_at RSEGS MV2 (F + 56) fl) by (replace (F + 56) with (F + 64 - 8) by (clear; lia); exact FLC).
assert (Q0 : 0 <= sp < 2 ^ 64 /\ 0 <= op < 2 ^ 64 /\ 0 <= ov < 2 ^ 64 /\ 0 <= oec < 2 ^ 64 /\ 0 <= ois < 2 ^ 64 /\ 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64)
by (clear - SL96 SHI SPT O1 Eop Eov Eoec Eois GFR GFLR; lia).
destruct Q0 as (Q0a & Q0b & Q0c & Q0d & Q0e & Q0f & Q0g).
assert (Q1 : 140735332487264 <= sp <= 140737488355328) by (clear - SL96 SHI SPT; lia).
assert (Q2 : (sp - 96) + 96 <= op \/ op + 384 <= (sp - 96)) by (clear - OCE SL96; lia).
assert (Q3 : 6885376 <= F <= 140737488355264) by (clear - GFR; lia).
assert (Q4 : (sp - 96) + 96 <= F \/ F + 64 <= (sp - 96)) by (clear - GFCEIL SL96; lia).
assert (Q5 : (sp - 96) + 96 <= fl \/ fl + 1 <= (sp - 96)) by (clear - GFLR SL96; lia).
assert (Q6 : (sp - 96) + 96 <= ois \/ ois + 272 <= (sp - 96)) by (clear - ICE SL96; lia).
assert (Q7 : 4096 <= fl <= 140737488355327) by (clear - GFLR; lia).
assert (Q8 : F + 64 <= 65536 \/ 65536 + 1196032 <= F) by (clear - GFR; lia).
assert (Q9 : ((F / 8) + 2147450880) + 8 <= 2147606610 \/ 2147606610 + 1 <= ((F / 8) + 2147450880)).
{ clear - GFR GF8. unfold SB in *. assert (F / 8 >= 844264) by (apply Z.le_ge; apply Z.div_le_lower_bound; lia). lia. }
assert (Q10 : op + 384 <= ois \/ ois + 272 <= op) by (clear - Eop Eois; lia).
unfold SB in AsopSF, AsisSF, ApSF, AiSF.
assert (PB : exists (fx3 : FPState) R3 M3v, mem_grows MV2 M3v
/\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 96 <= i < sp - 96 + 8) -> ~ (F <= i < F + 24) -> ~ (F / 8 + 2147450880 <= i < F / 8 + 2147450880 + 8) ->
M3v (Z_to_bv 64 i) = MV2 (Z_to_bv 64 i))
/\ msteps RSEGS (L5A.st fx1 R2 0xad1d4 MV2) (L5A.st fx3 R3 0xaf334 M3v)
/\ (forall x, In x [2; 3; 4; 8; 9; 19; 20; 21; 25; 26; 27]%nat -> getr R3 (reg x) = getr R2 (reg x))
/\ getr R3 (reg 1) = Z_to_bv 64 709348 /\ getr R3 (reg 10) = Z_to_bv 64 (op + 24) /\ getr R3 (reg 11) = Z_to_bv 64 (F + 32)
/\ getr R3 (reg 12) = Z_to_bv 64 1 /\ getr R3 (reg 18) = Z_to_bv 64 F /\ getr R3 (reg 22) = Z_to_bv 64 (F + 32)
/\ getr R3 (reg 23) = Z_to_bv 64 F /\ getr R3 (reg 24) = Z_to_bv 64 ((F / 8) + 2147450880)
/\ L5.u8_at RSEGS M3v ((F / 8) + 2147450884) 1 /\ L5.defined M3v (F + 24) 40).
{ destruct STV as [STE|STE]; rewrite STE in UIST.
- cfeed P (PMARTP.artB0_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 45%nat => ois
| 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMARTP.aligned; assumption]).
destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & Y12 & _ & _ & Y18 & Y22 & Y23 & Y24 & Y4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & YD).
exists fx3, R3, M3v. split; [exact MG3|]. split; [intros i Hi N1 N2 N3; apply FRZ3; [exact Hi| intros X; apply N1; clear - X; lia| intros X; apply N2; clear - X; lia| intros X; apply N3; clear - X; lia]|].
split; [exact MS3|]. split; [intros x Hx; apply KS3; revert x Hx; apply (L5K.incl_b [2; 3; 4; 8; 9; 19; 20; 21; 25; 26; 27]%nat); vm_compute; reflexivity|].
repeat (split; [assumption|]). exact YD.
- cfeed P (PMARTP.artB2_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 45%nat => ois
| 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMARTP.aligned; assumption]).
destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & Y12 & _ & _ & Y18 & Y22 & Y23 & Y24 & Y4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & YD).
exists fx3, R3, M3v. split; [exact MG3|]. split; [intros i Hi N1 N2 N3; apply FRZ3; [exact Hi| intros X; apply N1; clear - X; lia| intros X; apply N2; clear - X; lia| intros X; apply N3; clear - X; lia]|].
split; [exact MS3|]. split; [intros x Hx; apply KS3; revert x Hx; apply (L5K.incl_b [2; 3; 4; 8; 9; 19; 20; 21; 25; 26; 27]%nat); vm_compute; reflexivity|].
repeat (split; [assumption|]). exact YD. }
destruct PB as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & Y12 & Y18 & Y22 & Y23 & Y24 & Y4 & YD).
set (W3 := fun a => (sp - 96 <= a < sp - 96 + 8) \/ (F <= a < F + 24) \/ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 8)).
apply (L5SAR.apiece L ar C HI LYa HIok LB FF' LK2 cr Aw M2 model2 fx1 fx3 R2 0xad1d4 R3 0xaf334 M3v W3 K HH2 AM2 MS3 MG3).
{ intros a Ha Hn. apply FRZ3; [exact Ha| intros X; apply Hn; left; exact X| intros X; apply Hn; right; left; exact X| intros X; apply Hn; right; right; exact X]. }
{ intros a Ha Wa. split.
- destruct Wa as [X|[X|X]].
+ unfold aclientw, aclient_g. right; left. split; [clear - X SL96 SHI SPT; lia| intros Y; clear - Y; lia].
+ apply (L5SAR.fframe_client L ar LB FF' 0 0 F 0 (sp - 96 + 32)); [left; reflexivity| change (ff_bytes 0) with 64; clear - X; lia].
+ apply (L5SAR.fframe_shadow_client L ar LB FF' 0 0 F 0 (sp - 96 + 32)); [left; reflexivity|]. change (ff_bytes 0) with 64.
unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - X; lia.
- destruct Wa as [X|[X|X]]; clear - X GFR SL96 SPT; lia. }
intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3. change (mrestrict H2 M3 = M3v) in VIS3.
assert (Y4' : L5.u8_at RSEGS M3 ((F / 8) + 2147450884) 1).
{ apply (proj1 (L5A.u8_at_vis H2 M3 ((F / 8) + 2147450884) 1 (L5A.avis_sub H2 (F / 8 + SB) 8 ((F / 8) + 2147450884) 1 VSH ltac:(unfold SB; clear; lia) ltac:(unfold SB; clear; lia))
ltac:(clear - Q0f GFR; lia) ltac:(clear - GFR; lia))).
rewrite VIS3. exact Y4. }
assert (YD' : L5.defined M3 (F + 24) 40).
{ apply (proj1 (L5A.defined_vis H2 M3 (F + 24) 40 (L5A.avis_sub H2 F 64 (F + 24) 40 VF ltac:(clear; lia) ltac:(clear; lia)))). rewrite VIS3. exact YD. }
assert (EK23f : L5SAR.ek L ar LB FF sp 30720 [] M2 M3).
{ apply (L5SAR.ek_piece L ar LB FF sp 30720 [] M2 M3 W3 FR3). intros a Ha Hc _ X. destruct X as [X|[X|X]].
- apply (NCS0 a); [clear - X; lia| exact Hc].
- destruct (APART a 1 sp 30720 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (Y & _). clear - X Y; lia.
- destruct (APART a 1 sp 30720 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (_ & Y & _). unfold SB in Y. clear - X Y; lia. }
pose proof (L5SAR.ek_trans L ar LB FF sp 30720 [] M M2 M3 EK02f EK23f) as EK03f.
assert (OWN3 : own sp R M3).
{ apply (own_agree sp R M1 M3 ltac:(clear - SL96 SPT; lia) ltac:(clear - SHI SPT; lia) OWN1). intros a Ha. unfold ocell in Ha.
rewrite FR3; [apply AGF; clear - Ha; lia| clear - Ha SL96 SHI SPT; lia| intros [X|[X|X]]; clear - X Ha GFCEIL GFR SL96 SPT; unfold SB in *; lia]. }
assert (WAPPR : PMKA.wapp (PMSPA.W_run PMA.AD fb)).
{ unfold PMSPA.W_run, PMSPA.W_srcf, PMSPA.err_W, PMSPA.o_src, PMSPA.o_is, PMSPA.o_tb, PMSPA.o_vec, PMSPA.o_ec, PMSPA.o_p.
cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMA.AD ADDR_A].
pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
repeat apply PMKA.wapp_cons; [..| apply PMKA.wapp_nil]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia. }
set (WR := PMSPA.W_run PMA.AD fb) in *.
assert (BI3 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 30720 (sp - 96) (own sp R) F 0 WR (PM.parser_own s) M3 model3 LK2 cr Aw).
{ unfold PMAUK.binv. split; [exact HH3|]. split; [exact AM3|].
split; [eapply L5LZ.model_rt_trans; [exact MRT1| eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3]]|].
split; [apply incl_refl|]. split; [exact GLKI2|]. split; [exact (L5SAR.astk_grows ar M2 M3 sp 30720 ASTK2 MGM3)|].
split; [apply (L5SAR.ek_W L ar LBX FF sp 30720 WR [] M M3 (PMKA.ek_sublb L ar LB LBX FF sp 30720 [] M M3 INCX EK03f)); intros a _ r0 []|].
split; [apply (L5SAR.dk_trans L ar LBX FF sp 30720 M M2 M3 DK02); apply L5SAR.dk_grows; exact MGM3|].
split; [exact OWN3|].
change (ff_bytes 0 / 8) with 8. apply (L5.defined_grows M2 M3 _ _ MGM3).
apply (proj1 (L5A.defined_vis H2 M2 (F / 8 + SB) 8 VSH)). intros i Hi. pose proof (FSHZ i Hi) as Z0. unfold MV2 in Z0. rewrite Z0. discriminate. }
assert (SZK : forall Mc lo g, L5SAR.ek L ar LBX FF sp 30720 WR M Mc -> sp - 30720 <= lo -> lo + 8 * g <= sp -> lo mod 8 = 0 -> 0 <= g -> shadow_zero Mc lo g).
{ intros Mc lo g EKc H1' H2' H3' H4'. apply (PMKA.stksh_keepA L ar LBX FF sp 30720 WR M Mc EKc WAPPR lo g); [clear - H1' SLO SPT; lia| clear - H1' SLO; lia| clear - H2' SHI SPT; lia| exact H3'| exact H4'|].
apply (PMKA.shadow_zero_sub M (sp - 30720) 3840); [| exact H3'| exact H1'| clear - H2'; lia| exact H4'| exact STKSH].
apply PMKA.mod16_8'. replace (sp - 30720) with (sp + (-1920) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
assert (ASTK3 : L5CA.astk ar M3 sp 30720) by exact (L5SAR.astk_grows ar M2 M3 sp 30720 ASTK2 MGM3).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH3) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDF3 & _).
unfold PMA.src_read_spec, PMSPA.src_read_spec, PMSPA.src_spec in SR.
apply (SR fx3 R3 M3 model3 K LBX FF' LK2 Aw cr (sp - 96) 0xad2e4 fb s str sm [(F + 32, 1)] HH3 AM3 K0).
{ split; [rewrite L5K.rl1; exact Y1|]. split; [split; [clear; lia| reflexivity]|]. split; [rewrite L5K.rl2; rewrite (KS3 2%nat) by inl; exact B2R|].
split; [rewrite L5K.rl3; rewrite (KS3 3%nat) by inl; rewrite (R2c 3%nat) by inl; rewrite (KS1 3%nat) by inl; rewrite <- L5K.rl3; exact Rgp|].
split; [rewrite L5K.rl4; rewrite (KS3 4%nat) by inl; rewrite (R2c 4%nat) by inl; rewrite (KS1 4%nat) by inl; rewrite <- L5K.rl4; exact Rtp|].
change (PMSPA.pm_scr 4) with 20480. change (20480 / 8) with 2560.
split; [apply (L5SAR.astk_sub ar M3 M3 sp 30720 96 20480 ASTK3 (mem_grows_refl M3)); [clear; lia| clear; lia| clear; lia| replace (sp - 96) with (sp + (-6) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
apply SZK; [exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 BI3)))))))| clear; lia| clear; lia| | clear; lia].
apply PMKA.mod16_8'. replace (sp - 96 - 20480) with (sp + (-1286) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
{ apply (PMAUAR.ffroomA_push 9 4 FF LK LK2 _ FRM GLKI2); [exact NDF3| clear; lia]. }
{ apply (PMAUAR.ffrsA_push FF sp (sp - 96) F 0 (sp - 96 + 32) FRS); clear; lia. }
{ exact FOK'. }
{ unfold PMSPA.o_src. fold op. exact Y10. }
{ exists (F + 32), 1. split; [exact Y11|]. split; [exact Y12|]. split; [unfold PM.CHUNK; clear; lia|].
left. split; [exists (F, 0, sp - 96 + 32); split; [left; reflexivity| cbn [ff_addr ff_class fst snd]; change (ff_bytes 0) with 64; clear; lia]|].
split; [clear; lia|]. split; [apply (L5.defined_sub M3 (F + 24) 40); [exact YD'| clear; lia| clear; lia]|].
split; [|split; [change (PMSPA.o_is PMA.AD fb) with ois; clear - AiF; change (ff_bytes 0) with 64 in AiF; lia
| change (PMSPA.o_p PMA.AD fb) with op; clear - ApF; change (ff_bytes 0) with 64 in ApF; lia]].
intros a Ha. assert (Ea : a = F + 32) by (clear - Ha; lia). subst a. right. exists 1. split; [| split; [clear; lia|]].
- unfold byte_at, S. replace ((F + 32) / 8 + SB) with (F / 8 + 2147450884) by (clear - GF8; unfold SB; lia).
apply (L5ADHR.byte_of_u8 M3 _ 1 Y4'); [right| ]; clear - GFR; lia.
- replace (F + 32) with (F + 4 * 8) by (clear; lia). rewrite Z_mod_plus_full. rewrite <- (proj1 GF8). rewrite Z_mod_mult. clear; lia. }
{ exists (F + 32), 1. split; [exact Y11|]. split; [exact Y12|]. split; [clear - Q0f GFR; lia|]. split; [clear; lia| reflexivity]. }
{ apply (PMKA.parser_keepA RSEGS PMA.AD L ar LB FF sp 30720 [] M M3 EK03f PMKA.wapp_nil FRB BRB _ _ _ AOP); [| intros i _ r0 []| intros i _ r0 []| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact PA].
unfold LB. apply incl_appl, incl_refl. }
{ apply (PMKA.iss_keepA RSEGS PMA.AD L ar LB FF sp 30720 [] M M3 EK03f PMKA.wapp_nil FRB BRB ois str sm AOI); [| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA].
unfold LB. apply incl_appr. exact INCS. }
{ apply (PMASK.base_keep L ar C LY LB FF sp 30720 [] M M3 EK03f); [intros a _ r0 []| exact BASE]. }
{ exact INCS. }
intros fx4 R4 M4 model4 LK4 Aw4 src4 sm4 RP4 PA4 IA4 STEP4 RES4 HP4 MRT4 INCLK4 INCAw4 AM4 HH4.
change (PMSPA.pm_scr 4) with 20480 in HP4.
assert (Iq : In (PM.sr_qc (PM.p_src s), PM.CHUNK) (PM.parser_own s)) by (unfold PM.parser_own, PM.src_own; left; reflexivity).
assert (IqL : In (PM.sr_qc (PM.p_src s), PM.CHUNK) LB) by (unfold LB; apply in_or_app; left; exact Iq).
pose proof (WB _ IqL) as ((Bq0 & _ & _ & _ & Bq4 & Bq5) & _). cbn [fst snd] in Bq0, Bq4, Bq5. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI, PM.CHUNK in Bq5, Bq4.
destruct Bq5 as (_ & Bq5 & _).
pose proof (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ _ _ HH IqL) as Bqi. unfold PM.CHUNK in Bqi.
set (qc := PM.sr_qc (PM.p_src s)) in *.
set (Wc := PMSPA.W_src PMA.AD fb (PM.p_src s) ++ [(F + 32, 1)]) in HP4.
assert (WcR : forall rr a, In rr Wc -> L5.in_rng rr a ->
(op + 280 <= a < op + 320) \/ (ois + 40 <= a < ois + 48) \/ (ois + 152 <= a < ois + 156) \/ (qc <= a < qc + 16384) \/ a = F + 32).
{ intros rr a Hin Hr. unfold Wc, PMSPA.W_src, PMSPA.W_srcf, PMSPA.o_src, PMSPA.o_is, PMSPA.o_p in Hin. cbn [app pa_off_p pa_off_is PMA.AD ADDR_A] in Hin.
unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hr; unfold PM.CHUNK in Hr; clear - Hr Eop Eois;
[left|right;left|right;right;left|right;right;right;left|right;right;right;right]; lia. }
assert (BI4 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 30720 (sp - 96) (own sp R) F 0 WR (PM.parser_own s) M4 model4 LK4 cr Aw4).
{ apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 30720 (sp - 96) (sp - 88) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PM.parser_own s) G
WR WR (PM.parser_own s) (PM.parser_own s) (PM.parser_own s) M3 model3 LK2 cr Aw M4 model4 LK4 cr Aw4 20480 Wc BI3 HP4 HH4 AM4 MRT4 INCAw4 INCLK4);
[clear; lia| clear; lia| | | intros a X; exact X].
- intros rr a Hin Hr. change (ff_bytes 0 / 8) with 8. unfold ocell, SB.
pose proof GFR as (GF1 & GF2 & _). assert (D1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
assert (D2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; clear - GF2; lia).
destruct (WcR rr a Hin Hr) as [X|[X|[X|[X|X]]]]; (split; [clear - X OCE ICE Bq4 GFCEIL SL96 Eop Eois GF2; lia|]).
+ destruct ONSH as [Y|Y]; clear - X Y D1 D2; lia.
+ destruct INSH as [Y|Y]; clear - X Y D1 D2; lia.
+ destruct INSH as [Y|Y]; clear - X Y D1 D2; lia.
+ destruct Bq5 as [Y|Y]; clear - X Y D1 D2; lia.
+ subst a. destruct GFBIG as [Y|Y]; clear - Y D1 D2; lia.
- intros a Hc Ho rr Hin Hr. destruct (WcR rr a Hin Hr) as [X|[X|[X|[X|X]]]].
+ apply (Ho (PMSPA.o_src PMA.AD fb + 256, 40)); [unfold WR, PMSPA.W_run, PMSPA.W_srcf; right; left; reflexivity| unfold L5.in_rng, PMSPA.o_src; fold op; cbn [fst snd]; clear - X; lia].
+ apply (Ho (PMSPA.o_is PMA.AD fb + 40, 8)); [unfold WR, PMSPA.W_run, PMSPA.W_srcf; right; right; left; reflexivity| unfold L5.in_rng; fold ois; cbn [fst snd]; clear - X; lia].
+ apply (Ho (PMSPA.o_is PMA.AD fb + 152, 4)); [unfold WR, PMSPA.W_run, PMSPA.W_srcf; right; right; right; left; reflexivity| unfold L5.in_rng; fold ois; cbn [fst snd]; clear - X; lia].
+ exact (PMARS1.own_not_aclient L ar C HI HIok (PM.parser_own s) LBX FF LK cr Aw M _ qc 16384 a sp 30720 HH Iq X Hc).
+ subst a. apply (GNCF (F + 32)); [left; clear; lia| exact Hc]. }
pose proof (L5SAR.ek_callee L ar LB [] FF [(F, 0, sp - 96 + 32)] sp 30720 (sp - 96) 20480 Wc Wc M3 M4 HP4 ltac:(clear; lia) ltac:(clear; lia) (fun a _ X => X)) as EK34.
assert (EC3 : PMSPA.ec_at RSEGS M3 oec 0 cat).
{ apply (PMKA.ec_keepA RSEGS L ar LB FF sp 30720 [] M M3 EK03f PMKA.wapp_nil FRB oec 0 cat (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia))); [intros i _ r0 []| exact EC0]. }
assert (OUTc : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> (a + n <= op + 280 \/ op + 320 <= a) -> (a + n <= ois + 40 \/ ois + 48 <= a) ->
(a + n <= ois + 152 \/ ois + 156 <= a) -> forall i, a <= i < a + n -> L5.outside Wc i).
{ intros a n X1 X2 X3 X4 X5 i Hi rr Hin Hr. destruct (WcR rr i Hin Hr) as [Y|[Y|[Y|[Y|Y]]]]; [clear - Hi Y X3; lia| clear - Hi Y X4; lia| clear - Hi Y X5; lia| |].
- destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ qc 16384 a n HH IqL (AOF a n X1 X2)) as [Z|Z]; clear - Hi Y Z; lia.
- subst i. destruct (APART a n 0 0 (CLfb a n X1 X2 ltac:(clear - Hi; lia)) ltac:(clear - Hi; lia)) as (Z & _). clear - Hi Z; lia. }
assert (WAPPc : PMKA.wapp Wc).
{ intros rr Hin. unfold Wc, PMSPA.W_src, PMSPA.W_srcf, PMSPA.o_src, PMSPA.o_is, PMSPA.o_p in Hin. cbn [app pa_off_p pa_off_is PMA.AD ADDR_A] in Hin.
unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd]; unfold PM.CHUNK.
- destruct ONSH as [Y|Y]; clear - Y Eop; lia.
- destruct INSH as [Y|Y]; clear - Y Eois; lia.
- destruct INSH as [Y|Y]; clear - Y Eois; lia.
- destruct Bq5 as [Y|Y]; clear - Y; lia.
- destruct GFBIG as [Y|Y]; clear - Y; lia. }
pose proof (PMKA.ec_keepA RSEGS L ar LB FF sp 30720 Wc M3 M4 EK34 WAPPc FRB oec 0 cat (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia))
(OUTc oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia) ltac:(clear - Eop Eoec; lia) ltac:(clear - Eois Eoec; lia) ltac:(clear - Eois Eoec; lia)) EC3) as EC4.
destruct RES4 as (p' & k' & d & Yp & Yk & Hp' & Hk' & Yd & Hd & CONS & DEFd & RM1 & RM0).
assert (Ek : k' = 1).
{ rewrite L5K.rl12 in Yk. rewrite Y12 in Yk. apply (f_equal bv_unsigned) in Yk. unfold PM.CHUNK in Hk'. rewrite !L5.unsigned_lit in Yk by (clear - Hk'; lia). clear - Yk; lia. }
assert (Ep : p' = F + 32).
{ rewrite L5K.rl11 in Yp. rewrite Y11 in Yp. apply (f_equal bv_unsigned) in Yp. rewrite !L5.unsigned_lit in Yp by (clear - Hp' Q0f GFR; lia). clear - Yp; lia. }
subst k' p'. rewrite L5K.rl10 in Yd.
assert (R4c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R4 (reg j) = getr R3 (reg j))
by (intros j Hj; exact (L5SAR.cs_of_preserved R3 R4 j RP4 Hj)).
assert (G2' : getr R4 (reg 2) = Z_to_bv 64 (sp - 96)) by (rewrite (R4c 2%nat) by inl; rewrite (KS3 2%nat) by inl; exact B2R).
assert (G8' : getr R4 (reg 8) = Z_to_bv 64 sp) by (rewrite (R4c 8%nat) by inl; rewrite (KS3 8%nat) by inl; exact B8R).
assert (G9' : getr R4 (reg 9) = Z_to_bv 64 (sp - 96)) by (rewrite (R4c 9%nat) by inl; rewrite (KS3 9%nat) by inl; exact B9R).
assert (G18' : getr R4 (reg 18) = Z_to_bv 64 F) by (rewrite (R4c 18%nat) by inl; exact Y18).
assert (G19' : getr R4 (reg 19) = Z_to_bv 64 oec) by (rewrite (R4c 19%nat) by inl; rewrite (KS3 19%nat) by inl; exact B19R).
assert (G20' : getr R4 (reg 20) = Z_to_bv 64 op) by (rewrite (R4c 20%nat) by inl; rewrite (KS3 20%nat) by inl; exact B20R).
assert (G21' : getr R4 (reg 21) = Z_to_bv 64 ov) by (rewrite (R4c 21%nat) by inl; rewrite (KS3 21%nat) by inl; exact B21R).
assert (G22' : getr R4 (reg 22) = Z_to_bv 64 (F + 32)) by (rewrite (R4c 22%nat) by inl; exact Y22).
assert (G23' : getr R4 (reg 23) = Z_to_bv 64 F) by (rewrite (R4c 23%nat) by inl; exact Y23).
assert (G24' : getr R4 (reg 24) = Z_to_bv 64 ((F / 8) + 2147450880)) by (rewrite (R4c 24%nat) by inl; exact Y24).
assert (G25' : getr R4 (reg 25) = Z_to_bv 64 2147450880) by (rewrite (R4c 25%nat) by inl; rewrite (KS3 25%nat) by inl; exact B25R).
assert (G34' : forall j, In j [3; 4; 26; 27]%nat -> getr R4 (reg j) = getr R (reg j)).
{ intros j Hj. rewrite (R4c j) by (revert j Hj; apply (L5K.incl_b [3; 4; 26; 27]%nat); vm_compute; reflexivity).
rewrite (KS3 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 26; 27]%nat); vm_compute; reflexivity).
rewrite (R2c j) by (revert j Hj; apply (L5K.incl_b [3; 4; 26; 27]%nat); vm_compute; reflexivity).
apply KS1. revert j Hj. apply (L5K.incl_b [3; 4; 26; 27]%nat). vm_compute. reflexivity. }
assert (QC4 : PM.sr_qc src4 = qc) by (destruct STEP4 as (X & _); exact X).
destruct (Z.eq_dec d 0) as [D0|D1'].
-
rewrite D0 in Yd.
set (s4 := PMSPA.with_src s src4) in *.
assert (EOWN : PM.parser_own s4 = PM.parser_own s) by (unfold s4, PMSPA.with_src, PM.parser_own, PM.src_own; cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]; rewrite QC4; reflexivity).
set (H4 := ahid Aw4 model4) in *. set (MV4 := mrestrict H4 M4) in *.
cfeed P (PMARTP.artE0_conc fx4 R4 MV4 (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | _ => 0 end)) ltac:(first [assumption]).
destruct P as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Z1 & Z10 & Z11).
assert (E5 : M5v = MV4) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ5; exact Ha). subst M5v.
apply (L5SAR.apiece_ro L ar C HI LYa HIok LB FF' LK4 cr Aw4 M4 model4 fx4 fx5 R4 0xad2e4 R5 0xae974 MV4 K HH4 AM4 MS5 (fun x Hx => Hx) (fun a Ha => eq_refl)).
intros M5 model5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5.
assert (E5 : M5 = M4) by (apply L5SAR.mem_eq_of_agree; exact FR5). subst M5.
pose proof (PMAUK.binv_model L ar HI M model LBX FF LK Aw sp 30720 (sp - 96) (own sp R) F 0 WR (PM.parser_own s) M4 model4 LK4 cr Aw4 model5 BI4 HH5 AM5 MRT5) as BI5.
assert (R5c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R5 (reg j) = getr R4 (reg j)).
{ intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
assert (EK04 : L5SAR.ek L ar LB FF sp 30720 Wc M M4) by exact (L5SAR.ek_trans L ar LB FF sp 30720 Wc M M3 M4 (L5SAR.ek_W L ar LB FF sp 30720 Wc [] M M3 EK03f (fun a _ r0 H0 => match H0 with end)) EK34).
assert (BASE4 : PMSTA.base_okA RSEGS PMA.AD M4).
{ apply (PMASK.base_keep L ar C LY LB FF sp 30720 Wc M M4 EK04); [| exact BASE].
intros a Ha rr Hin Hr. destruct (WcR rr a Hin Hr) as [X|[X|[X|[X|X]]]]; [clear - Ha X O1; lia| clear - Ha X I1; lia| clear - Ha X I1; lia| destruct Bqi as [Y|Y]; clear - Ha X Y; lia| clear - Ha X GFR; lia]. }
assert (ERR4 : PMSTA.err_okA RSEGS PMA.AD PMA.AAD M4 e).
{ apply (PMKA.err_okA_keep RSEGS PMA.AD PMA.AAD L ar LB FF sp 30720 Wc M M4 EK04 e PMA.addrs_wf_A); [| exact ERR].
intros a D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
split; [exact (PMA.ly_static L C LY a D)|]. intros rr Hin Hr. destruct (WcR rr a Hin Hr) as [X|[X|[X|[X|X]]]];
[clear - DI X O1; lia| clear - DI X I1; lia| clear - DI X I1; lia| destruct Bqi as [Y|Y]; clear - DI X Y; lia| clear - DI X GFR; lia]. }
unfold PMA.make_ec_spec, PMSPA.make_ec_spec in MKE.
pose proof EC4 as (_ & _ & ECD4 & ECA4).
apply (MKE fx5 R5 M4 model5 K LB FF' LK4 Aw4 cr oec 1 (sp - 96) 0xad334 e HH5 AM5 K0).
{ split; [rewrite L5K.rl1; exact Z1|]. split; [split; [clear; lia| reflexivity]|]. split; [rewrite L5K.rl2; rewrite (R5c 2%nat) by inl; exact G2'|].
split; [rewrite L5K.rl3; rewrite (R5c 3%nat) by inl; rewrite (G34' 3%nat) by inl; rewrite <- L5K.rl3; exact Rgp|].
split; [rewrite L5K.rl4; rewrite (R5c 4%nat) by inl; rewrite (G34' 4%nat) by inl; rewrite <- L5K.rl4; exact Rtp|].
change (PMSPA.pm_scr 1) with 14336. change (14336 / 8) with 1792.
pose proof BI4 as (_ & _ & _ & _ & _ & ASTK4 & EKb4 & _).
split; [apply (L5SAR.astk_sub ar M4 M4 sp 30720 96 14336 ASTK4 (mem_grows_refl M4)); [clear; lia| clear; lia| clear; lia| replace (sp - 96) with (sp + (-6) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
apply SZK; [exact EKb4| clear; lia| clear; lia| | clear; lia].
apply PMKA.mod16_8'. replace (sp - 96 - 14336) with (sp + (-902) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
{ pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH5) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDF5 & _).
apply (PMAUAR.ffroomA_push 9 1 FF LK LK4 _ FRM (fun x Hx => GLKI2 x (INCLK4 x Hx))); [exact NDF5| clear; lia]. }
{ apply (PMAUAR.ffrsA_push FF sp (sp - 96) F 0 (sp - 96 + 32) FRS); clear; lia. }
{ rewrite L5K.rl10. exact Z10. }
{ rewrite L5K.rl11. exact Z11. }
{ clear; lia. }
{ apply PMAUAR.aobjA_push. apply AOF; clear - Eoec; lia. }
{ rewrite Eoec. pose proof (Z.div_mod fb 1024 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
replace (1024 * (fb / 1024) + 992) with ((128 * (fb / 1024) + 124) * 8) by (clear; lia). apply Z_mod_mult. }
{ exact ECD4. }
{ exact ECA4. }
{ exact BASE4. }
{ exact ERR4. }
intros fx6 R6 M6 model6 LK6 Aw6 RP6 EC6 ERR6 HP6 MRT6 INCLK6 INCAw6 AM6 HH6.
change (PMSPA.pm_scr 1) with 14336 in HP6.
set (Wc6 := (oec, 16) :: (if e then [] else PMSPA.err_W PMA.AD)) in HP6.
assert (Wc6R : forall rr a, In rr Wc6 -> L5.in_rng rr a -> (oec <= a < oec + 16) \/ (0x66d380 <= a < 0x68f0f4)).
{ intros rr a Hin Hr. unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [left; exact Hr|]. right. destruct e; [destruct Hin|].
unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr; lia. }
assert (BI6 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 30720 (sp - 96) (own sp R) F 0 WR (PM.parser_own s) M6 model6 LK6 cr Aw6).
{ apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 30720 (sp - 96) (sp - 88) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PM.parser_own s) G
WR WR (PM.parser_own s) (PM.parser_own s) (PM.parser_own s) M4 model5 LK4 cr Aw4 M6 model6 LK6 cr Aw6 14336 Wc6 BI5 HP6 HH6 AM6 MRT6 INCAw6 INCLK6);
[clear; lia| clear; lia| | | intros a X; exact X].
- intros rr a Hin Hr. change (ff_bytes 0 / 8) with 8. unfold ocell, SB.
pose proof GFR as (GF1 & GF2 & _). assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
assert (DF2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; clear - GF2; lia).
pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
destruct (Wc6R rr a Hin Hr) as [X|X]; (split; [clear - X OCE SL96 SPT Eop Eoec F2 FSCEIL; lia|]).
+ destruct FA1 as [Y|Y]; clear - X Y DF1 DF2 F1 F2 Eoec; lia.
+ clear - X DF1; lia.
- intros a Hc Ho rr Hin Hr. destruct (Wc6R rr a Hin Hr) as [X|X].
+ apply (Ho (PMSPA.o_ec PMA.AD fb, 16)); [unfold WR, PMSPA.W_run, PMSPA.W_srcf, PMSPA.err_W; cbn [app]; do 6 right; left; reflexivity| unfold L5.in_rng; fold oec; cbn [fst snd]; clear - X; lia].
+ unfold WR, PMSPA.W_run, PMSPA.W_srcf, PMSPA.err_W in Ho. cbn [app pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Ho.
assert (X' : (0x66d380 <= a < 0x68f0f4)) by exact X. unfold Wc6, PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin.
destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr X' Eoec O1 Eop; lia|].
destruct e; [destruct Hin|]. destruct Hin as [<-|[<-|[]]].
* apply (Ho _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))))); exact Hr.
* apply (Ho _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))))); exact Hr. }
pose proof (L5SAR.ek_callee L ar LB [] FF [(F, 0, sp - 96 + 32)] sp 30720 (sp - 96) 14336 Wc6 Wc6 M4 M6 HP6 ltac:(clear; lia) ltac:(clear; lia) (fun a _ X => X)) as EK46.
assert (WAPP6 : PMKA.wapp Wc6).
{ intros rr Hin. unfold Wc6 in Hin. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct Hin as [<-|Hin]; cbn [fst snd].
- pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1. destruct FA1 as [Y|Y]; clear - Y F1 F2 Eoec; lia.
- destruct e; [destruct Hin|]. unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd]; clear; lia. }
assert (OUT6 : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> (a + n <= oec \/ oec + 16 <= a) -> forall i, a <= i < a + n -> L5.outside Wc6 i).
{ intros a n X1 X2 X3 i Hi rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y|Y]; [clear - Hi Y X3; lia| clear - Hi Y X1 Eop O1; lia]. }
assert (OUTB6 : forall q m, In (q, m) LB -> forall i, q <= i < q + m -> L5.outside Wc6 i).
{ intros q m Hq i Hi rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y|Y].
- destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m oec 16 HH Hq (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia))) as [Z|Z]; clear - Hi Y Z; lia.
- pose proof (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ q m HH Hq) as Z. destruct Z as [Z|Z]; clear - Hi Y Z; lia. }
assert (PA6 : PM.parser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA M6 op ois s4).
{ apply (PMKA.parser_keepA RSEGS PMA.AD L ar LB FF sp 30720 Wc6 M4 M6 EK46 WAPP6 FRB BRB _ _ _ AOP); [| | | | | exact PA4].
- rewrite EOWN. unfold LB. apply incl_appl, incl_refl.
- apply OUT6; clear - Eop Eoec; lia.
- unfold s4, PMSPA.with_src, PMKA.blk_out. cbn [PM.p_src]. rewrite QC4. apply (OUTB6 qc 16384). exact IqL.
- unfold s4, PMSPA.with_src, PMKA.blk_out. cbn [PM.p_b PM.p_k]. apply (OUTB6 (PM.p_b s) (32 * 2 ^ PM.p_k s)). unfold LB. apply in_or_app; left. unfold PM.parser_own, PM.vec_own. right; left; reflexivity.
- unfold s4, PMSPA.with_src, PMKA.blk_out. cbn [PM.p_tb]. intros c0 n0 p0 E0. apply (OUTB6 p0 c0). unfold LB. apply in_or_app; left. unfold PM.parser_own, PM.vs_own. rewrite E0. right; right; left; reflexivity. }
assert (IA6 : PM.iss_at RSEGS PMA.AD PMSPA.accA M6 ois str sm4).
{ apply (PMKA.iss_keepA RSEGS PMA.AD L ar LB FF sp 30720 Wc6 M4 M6 EK46 WAPP6 FRB BRB ois str sm4 AOI); [| | | exact IA4].
- unfold LB. apply incl_appr. exact INCS.
- apply OUT6; clear - Eois Eoec; lia.
- intros c0 n0 p0 E0. unfold PMKA.blk_out. apply (OUTB6 p0 c0). unfold LB. apply in_or_app; right. apply INCS. rewrite E0. left; reflexivity. }
assert (BASE6 : PMSTA.base_okA RSEGS PMA.AD M6).
{ apply (PMAPAR.base_keepW L ar C LY LB FF sp 30720 Wc6 M4 M6 EK46); [| | | | exact BASE4].
- intros a Ha rr Hin Hr. destruct (Wc6R rr a Hin Hr) as [X|X]; [clear - Ha X Eoec O1 Eop; lia|].
unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Ha Eoec Eop O1; lia|]. destruct e; [destruct Hin|].
unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr Ha; lia.
- intros a Ha rr Hin Hr. unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Ha Eoec Eop O1; lia|]. destruct e; [destruct Hin|].
unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr Ha; lia.
- intros rr Hin Hr. unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Eoec Eop O1; lia|]. destruct e; [destruct Hin|].
unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr; lia.
- intros a Ha rr Hin Hr. unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Ha Eoec Eop O1; lia|]. destruct e; [destruct Hin|].
unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr Ha; lia. }
set (H6 := ahid Aw6 model6) in *. set (MV6 := mrestrict H6 M6) in *.
destruct (PMAUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 30720 (sp - 96) (sp - 88) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PM.parser_own s) G
WR (PM.parser_own s) M6 model6 LK6 cr Aw6 BI6) as ((WS6 & _ & _ & _ & _) & OWN6 & (FD6 & FW6 & FSW6 & FLC6 & FLW6) & (FLCc6 & FLV6 & VF6 & VS6 & VSH6)).
change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *. replace (sp - (sp - 96)) with 96 in WS6 by (clear; lia).
replace (F + 64 - 8) with (F + 56) in FLC6 by (clear; lia).
assert (HH6' : ri_inv HI (PM.parser_own s4 ++ LBX) FF' LK6 cr Aw6 M6 (vml_of model6)) by (rewrite EOWN; exact HH6).
pose proof (PMAPAR.op_vis L ar C HI LY HIok _ _ LK6 cr Aw6 M6 model6 fb _ s4 HH6' FOK' PA6) as ((_ & _ & _) & Zop6 & Z326 & Z206 & OWR6 & _ & OVIS6 & _ & _).
assert (R6c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R6 (reg j) = getr R4 (reg j)).
{ intros j Hj. rewrite (L5SAR.cs_of_preserved R5 R6 j RP6 Hj). exact (R5c j Hj). }
pose proof OWN6 as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88).
pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8.
pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18.
pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19. pose proof (bv_unsigned_in_range 64 (getr R (reg 20))) as B20.
pose proof (bv_unsigned_in_range 64 (getr R (reg 21))) as B21. pose proof (bv_unsigned_in_range 64 (getr R (reg 22))) as B22.
pose proof (bv_unsigned_in_range 64 (getr R (reg 23))) as B23. pose proof (bv_unsigned_in_range 64 (getr R (reg 24))) as B24.
pose proof (bv_unsigned_in_range 64 (getr R (reg 25))) as B25. change (bv_modulus 64) with (2 ^ 64) in *.
cfeed P (PMARTP.artZ_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl
| 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9))
| 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20))
| 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23))
| 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | _ => 0 end)) ltac:(first [assumption | (rewrite R6c by inl; assumption) | unfold PMARTP.aligned; assumption]).
destruct P as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & E1 & E2 & E8 & E9 & _ & _ & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & FL0
& _ & _ & _ & _ & _ & _ & _ & _ & _ & MO0 & _).
assert (R7ra : getr R7 (reg 1) = Z_to_bv 64 r) by (rewrite E1, Z_to_bv_bv_unsigned; exact Rra).
pose proof (PMK.ret_to RSEGS fx7 R7 M7v 0xad3e8 (ltac:(oW' 0xad3e8%Z)) r (ltac:(oF' 0xad3e8%Z)) eq_refl (ltac:(oD' 0xad3e8%Z)) R7ra Hr1 Hr2) as MSr.
apply (PMAUK.retire_coreW L ar C HI LYa HIok M model LBX FF LK Aw sp 30720 (sp - 96) (sp - 88) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PM.parser_own s) G
WR (PM.parser_own s) M6 model6 LK6 cr Aw6 (fun a => op + 8 <= a < op + 9) fx6 fx7 R6 0xad334 R7 r M7v K BI6).
{ intros a X. split.
- apply (L5SAR.fframe_client L ar (PM.parser_own s ++ LBX) FF' 0 0 fb 4 rs); [right; exact Hfb| change (ff_bytes 4) with 1024; clear - X Eop; lia].
- intros O. apply (O (PMSPA.o_p PMA.AD fb + 8, 8)); [left; reflexivity| unfold L5.in_rng; fold op; cbn [fst snd]; clear - X; lia]. }
{ intros a. destruct (L5SAR.rng_dec a (op + 8) (op + 9)) as [X|X]; [left; exact X| right; exact X]. }
{ exact (msteps_trans _ _ _ _ MS7 MSr). }
{ exact MG7. }
{ intros a Ha Nw. unfold PMAUK.WretX, PMAUK.Wret in Nw. change (ff_bytes 0) with 64 in Nw.
apply FRZ7; [exact Ha| intros X; apply Nw; right; clear - X; lia| intros X; apply Nw; left; left; left; clear - X; lia
| intros X; apply Nw; left; left; right; unfold SB; clear - X; lia| intros X; apply Nw; left; right; clear - X; lia]. }
{ exact FL0. }
intros Mf modelf FZf MGf VISf AHf MRTf AMf HHf. change (mrestrict H6 Mf = M7v) in VISf.
assert (EKf : L5SAR.ek L ar (PM.parser_own s4 ++ LBX) FF 0 0 [(op + 8, 1)] M6 Mf).
{ apply (PMAUAR.wret_ek L ar C HI LY HIok LBX FF LK Aw sp 30720 (sp - 96) (sp - 88) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PM.parser_own s)
(PM.parser_own s4 ++ LBX) LK6 cr Aw6 M6 Mf _ [(op + 8, 1)] (fun a => op + 8 <= a < op + 9) G HH6').
- intros a X O. apply (O (op + 8, 1)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X; lia].
- exact FZf. }
pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH6') as BRB6.
assert (MO0f : L5.u8_at RSEGS Mf (op + 8) 0).
{ apply (proj1 (L5A.u8_at_vis H6 Mf (op + 8) 0 (OVIS6 (op + 8) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia))). rewrite VISf. exact MO0. }
pose proof BI6 as (_ & _ & _ & INCA6 & INCL6 & _ & EKb6 & _).
assert (OUT8 : forall a n, (a + n <= op + 8 \/ op + 9 <= a) -> forall i, a <= i < a + n -> L5.outside [(op + 8, 1)] i).
{ intros a n X3 i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hi Hr X3. lia. }
assert (OUTB8 : forall q m, In (q, m) (PM.parser_own s4 ++ LBX) -> forall i, q <= i < q + m -> L5.outside [(op + 8, 1)] i).
{ intros q m Hq i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr.
destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m op 384 HH6' Hq (PMAUAR.aobjA_push FF op 384 _ AOP)) as [Z|Z]; clear - Hi Hr Z; lia. }
assert (VIS6 : PMSPA.visitor_at RSEGS PMA.AD M6 ov).
{ apply (PMKA.visitor_keepA RSEGS PMA.AD L ar LBX FF sp 30720 WR M M6 EKb6 WAPPR FRB ov (AOF ov 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia))); [| exact VIS].
intros i Hi rr Hin Hr.
unfold WR, PMSPA.W_run, PMSPA.W_srcf, PMSPA.err_W, PMSPA.o_src, PMSPA.o_is, PMSPA.o_tb, PMSPA.o_vec, PMSPA.o_ec, PMSPA.o_p in Hin.
cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. unfold L5.in_rng in Hr.
repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; clear - Hi Hr Eov Eop O1; lia|]). destruct Hin. }
assert (VREF6 : L5.u64_at RSEGS M6 (op + 384) ov).
{ apply (PMKA.u64_keepA RSEGS L ar LBX FF sp 30720 WR M M6 EKb6 WAPPR FRB (op + 384) ov (AOF (op + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [| exact VREF].
intros i Hi rr Hin Hr. unfold WR, PMSPA.W_run, PMSPA.W_srcf, PMSPA.err_W, PMSPA.o_src, PMSPA.o_is, PMSPA.o_tb, PMSPA.o_vec, PMSPA.o_ec, PMSPA.o_p in Hin.
cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. unfold L5.in_rng in Hr.
repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; clear - Hi Hr Eop O1; lia|]). destruct Hin. }
assert (WAPP8 : PMKA.wapp [(op + 8, 1)]).
{ apply PMKA.wapp_cons; [| apply PMKA.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct ONSH as [Y|Y]; [right| left]; clear - Y; lia. }
assert (Ivb : In (PM.p_b s4, 32 * 2 ^ PM.p_k s4) (PM.parser_own s4 ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.vec_own; right; left; reflexivity).
assert (Iqc : In (PM.sr_qc (PM.p_src s4), PM.CHUNK) (PM.parser_own s4 ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
apply (KONT fx7 R7 Mf modelf LK6 Aw6 (PMPK.set_more s4 0) sm4 true cr).
-- apply L5SAR.preserved_by_index. intros j Hj. pose proof Hj as Hj'. unfold L5SAR.cs_all in Hj.
repeat (destruct Hj as [<-|Hj]; [first [ rewrite E2; exact (eq_sym Rsp) | rewrite E8; apply Z_to_bv_bv_unsigned | rewrite E9; apply Z_to_bv_bv_unsigned
| rewrite E18; apply Z_to_bv_bv_unsigned | rewrite E19; apply Z_to_bv_bv_unsigned | rewrite E20; apply Z_to_bv_bv_unsigned
| rewrite E21; apply Z_to_bv_bv_unsigned | rewrite E22; apply Z_to_bv_bv_unsigned | rewrite E23; apply Z_to_bv_bv_unsigned
| rewrite E24; apply Z_to_bv_bv_unsigned | rewrite E25; apply Z_to_bv_bv_unsigned
| rewrite (KS7 _) by inl; rewrite (R6c _) by inl; apply G34'; inl ] |]).
destruct Hj.
-- unfold PMSPA.run_post, PMSPA.run_pre.
split; [split; [| split; [| split; [| split; [| split; [| split]]]]]|].
++ destruct (BRB6 _ Iqc) as (Xq1 & Xq2). destruct (BRB6 _ Ivb) as (Xb1 & Xb2). cbn [fst snd] in Xq1, Xq2, Xb1, Xb2.
apply (PMAPAR.parser_more_updA M6 Mf op ois s4 0 PA6).
** clear - O1; lia.
** clear - O1; lia.
** apply (PMKA.agA_obj L ar _ FF 0 0 _ M6 Mf EKf WAPP8 FRB op 8 (AOF op 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))).
apply OUT8. clear; lia.
** apply (PMKA.agA_obj L ar _ FF 0 0 _ M6 Mf EKf WAPP8 FRB (op + 9) 375 (AOF (op + 9) 375 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))).
apply OUT8. clear; lia.
** exact (PMKA.agsh_obj L ar _ FF 0 0 _ M6 Mf EKf WAPP8 FRB op 384 AOP).
** pose proof PA6 as (_ & PD6 & _). apply (L5.defined_grows M6 Mf _ _ MGf PD6).
** exact MO0f.
** left; reflexivity.
** exact Xq1.
** clear - Xq2; lia.
** apply (PMKA.agA_blk L ar _ FF 0 0 _ M6 Mf EKf WAPP8 BRB6 _ _ Iqc).
apply OUTB8. exact Iqc.
** exact Xb1.
** clear - Xb2; lia.
** apply (PMKA.agA_blk L ar _ FF 0 0 _ M6 Mf EKf WAPP8 BRB6 _ _ Ivb).
apply OUTB8. exact Ivb.
** intros c0 n0 p0 E0. assert (Ip : In (p0, c0) (PM.parser_own s4 ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.vs_own; rewrite E0; right; right; left; reflexivity).
apply (PMKA.agA_blk L ar _ FF 0 0 _ M6 Mf EKf WAPP8 BRB6 _ _ Ip).
apply OUTB8. exact Ip.
++ apply (PMKA.iss_keepA RSEGS PMA.AD L ar _ FF 0 0 _ M6 Mf EKf WAPP8 FRB BRB6 ois str sm4 AOI); [| | | exact IA6].
** apply incl_appr. exact INCS.
** apply OUT8. clear - Eop Eois; lia.
** intros c0 n0 p0 E0. unfold PMKA.blk_out. apply (OUTB8 p0 c0). apply in_or_app; right. apply INCS. rewrite E0. left; reflexivity.
++ apply (PMKA.visitor_keepA RSEGS PMA.AD L ar _ FF 0 0 _ M6 Mf EKf WAPP8 FRB _ (AOF ov 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia))); [| exact VIS6].
apply OUT8. clear - Eop Eov; lia.
++ apply (PMKA.u64_keepA RSEGS L ar _ FF 0 0 _ M6 Mf EKf WAPP8 FRB (op + 384) _ (AOF (op + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [| exact VREF6].
apply OUT8. clear; lia.
++ apply (PMASK.base_keep L ar C LY _ FF 0 0 _ M6 Mf EKf); [| exact BASE6]. intros a Ha rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Ha Hr O1; lia.
++ apply (PMKA.err_okA_keep RSEGS PMA.AD PMA.AAD L ar _ FF 0 0 _ M6 Mf EKf true PMA.addrs_wf_A); [| exact ERR6].
intros a D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
split; [exact (PMA.ly_static L C LY a D)|]. intros rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - DI Hr O1; lia.
++ unfold PMPK.set_more, s4, PMSPA.with_src. cbn [PM.p_tb PM.p_tg]. exact TBOK.
++ split; [unfold PMPK.set_more, s4, PMSPA.with_src; cbn [PM.p_src]; exact STEP4|].
split; [intros _; reflexivity|]. left. exists 1. split; [clear; lia|]. split; [| split; [reflexivity| reflexivity]].
apply (PMKA.ec_keepA RSEGS L ar _ FF 0 0 _ M6 Mf EKf WAPP8 FRB _ 1 _ (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia))); [| exact EC6].
apply OUT8. clear - Eop Eoec; lia.
-- exact AHf.
-- unfold PMSPA.credit_keep. unfold PMPK.set_more, s4, PMSPA.with_src, PM.pot_parser. cbn [PM.p_k PM.p_tb PM.p_tg]. clear; lia.
-- exact MRTf.
-- exact INCL6.
-- exact INCA6.
-- exact AMf.
-- unfold PMPK.set_more. change (PM.parser_own (PM.PST 0 (PM.p_done s4) (PM.p_depth s4) (PM.p_src s4) (PM.p_tb s4) (PM.p_tg s4) (PM.p_b s4) (PM.p_k s4) (PM.p_stk s4)))
with (PM.parser_own s4). rewrite EOWN. exact HHf.
-
assert (D1 : d = 1) by (clear - Hd D1'; lia). rewrite D1 in Yd, Hd, CONS, DEFd, RM0. clear D1'.
set (H4 := ahid Aw4 model4) in *. set (MV4 := mrestrict H4 M4) in *.
pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LK4 cr Aw4 M4 model4 HH4) as (_ & VIS4 & _ & VFS4 & _).
cfeed P (PMARTP.artC_conc fx4 R4 MV4 (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | _ => 0 end)) ltac:(first [assumption]).
destruct P as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5).
assert (E5 : M5v = MV4) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ5; exact Ha). subst M5v.
assert (DV4 : L5.defined MV4 (F + 32) 1).
{ apply (proj2 (L5A.defined_vis H4 M4 (F + 32) 1 (VFS4 (F + 32) 1 ltac:(clear - GFS1; lia) ltac:(clear - GFS2; lia)))). exact DEFd. }
destruct (PMPX.lbu_run RSEGS fx5 R5 MV4 0xad2e8 (ltac:(oW' 0xad2e8%Z)) 12%bv 22%bv 0%bv (F + 32) (ltac:(oF' 0xad2e8%Z)) eq_refl (ltac:(oD' 0xad2e8%Z))) as (t & Ht & U8t & MSt).
{ intros E0. apply (f_equal bv_unsigned) in E0. vm_compute in E0. discriminate E0. }
{ clear; lia. } { clear; lia. }
{ rewrite L5K.rl22. rewrite (KS5 22%nat) by inl. exact G22'. }
{ clear - Q0f GFR; lia. }
{ change (bv_signed (0%bv : bv 12)) with 0. clear - Q0f GFR; lia. }
{ change (bv_signed (0%bv : bv 12)) with 0. rewrite Z.add_0_r. exact DV4. }
change (0xad2e8 + 4) with 0xad2ec in MSt. rewrite L5K.rl12 in MSt.
set (R5' := regupd R5 (reg 12) (Z_to_bv 64 t)) in MSt.
assert (R5o : forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R5' (reg k) = getr R4 (reg k)).
{ intros k Hk. unfold R5'. rewrite (reg12_other R5 _ k Hk). apply KS5. revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
assert (R512 : getr R5' (reg 12) = Z_to_bv 64 t) by (unfold R5'; apply PMPX.regupd_same_idx; lia).
cfeed P (PMARTP.artD_conc fx5 R5' MV4 (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 49%nat => t | _ => 0 end)) ltac:(first [assumption | (rewrite R5o by inl; assumption) | clear - Ht; lia]).
destruct P as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & MS6 & KS6 & Z1 & Z10 & Z11 & Z13).
assert (E6 : M6v = MV4) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ6; exact Ha). subst M6v.
apply (L5SAR.apiece_ro L ar C HI LYa HIok LB FF' LK4 cr Aw4 M4 model4 fx4 fx6 R4 0xad2e4 R6 0xad5dc MV4 K HH4 AM4).
{ eapply msteps_trans; [exact MS5| eapply msteps_trans; [exact MSt| exact MS6]]. }
{ intros x Hx. exact Hx. }
{ intros a Ha. reflexivity. }
intros M5 model5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5.
assert (E5 : M5 = M4) by (apply L5SAR.mem_eq_of_agree; exact FR5). subst M5.
pose proof (PMAUK.binv_model L ar HI M model LBX FF LK Aw sp 30720 (sp - 96) (own sp R) F 0 WR (PM.parser_own s) M4 model4 LK4 cr Aw4 model5 BI4 HH5 AM5 MRT5) as BI5.
assert (R6c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R6 (reg j) = getr R4 (reg j)).
{ intros j Hj. rewrite (KS6 j) by (revert j Hj; apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat); vm_compute; reflexivity).
exact (R5o j Hj). }
set (s4 := PMSPA.with_src s src4) in *.
assert (EOWN : PM.parser_own s4 = PM.parser_own s) by (unfold s4, PMSPA.with_src, PM.parser_own, PM.src_own; cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]; rewrite QC4; reflexivity).
assert (EK04 : L5SAR.ek L ar LB FF sp 30720 Wc M M4) by exact (L5SAR.ek_trans L ar LB FF sp 30720 Wc M M3 M4 (L5SAR.ek_W L ar LB FF sp 30720 Wc [] M M3 EK03f (fun a _ r0 H0 => match H0 with end)) EK34).
unfold PMA.read_value_spec, PMSPA.read_value_spec, PMSPA.run_spec, PMSPA.run_spec_r in RV.
apply (RV fx6 R6 M4 model5 K LBX FF' LK4 Aw4 cr (sp - 96) 0xad2fc fb cat s4 str sm4 e).
{ rewrite EOWN. exact HH5. }
{ exact AM5. }
{ exact K0. }
{ split; [rewrite L5K.rl1; exact Z1|]. split; [split; [clear; lia| reflexivity]|]. split; [rewrite L5K.rl2; rewrite (R6c 2%nat) by inl; exact G2'|].
split; [rewrite L5K.rl3; rewrite (R6c 3%nat) by inl; rewrite (G34' 3%nat) by inl; rewrite <- L5K.rl3; exact Rgp|].
split; [rewrite L5K.rl4; rewrite (R6c 4%nat) by inl; rewrite (G34' 4%nat) by inl; rewrite <- L5K.rl4; exact Rtp|].
change (PMSPA.pm_scr 8) with 28672. change (28672 / 8) with 3584.
pose proof BI4 as (_ & _ & _ & _ & _ & ASTK4 & EKb4 & _).
split; [apply (L5SAR.astk_sub ar M4 M4 sp 30720 96 28672 ASTK4 (mem_grows_refl M4)); [clear; lia| clear; lia| clear; lia| replace (sp - 96) with (sp + (-6) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
apply SZK; [exact EKb4| clear; lia| clear; lia| | clear; lia].
apply PMKA.mod16_8'. replace (sp - 96 - 28672) with (sp + (-1798) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
{ pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH5) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDF5 & _).
apply (PMAUAR.ffroomA_push 9 8 FF LK LK4 _ FRM (fun x Hx => GLKI2 x (INCLK4 x Hx))); [exact NDF5| clear; lia]. }
{ apply (PMAUAR.ffrsA_push FF sp (sp - 96) F 0 (sp - 96 + 32) FRS); clear; lia. }
{ exact FOK'. }
{ replace (sp - 96) with (sp + (-3) * 32) by (clear; lia). rewrite Z_mod_plus_full. exact SP32. }
{ split; [rewrite L5K.rl10; exact Z10|]. split; [rewrite L5K.rl11; exact Z11|]. split; [rewrite L5K.rl13; exact Z13|].
exists t. split; [exact Ht|]. rewrite L5K.rl12. rewrite (KS6 12%nat) by inl. exact R512. }
{ pose proof BI4 as (_ & _ & _ & _ & _ & _ & EKb4 & _).
unfold PMSPA.run_pre. split; [exact PA4|]. split; [exact IA4|].
split; [apply (PMKA.visitor_keepA RSEGS PMA.AD L ar LBX FF sp 30720 WR M M4 EKb4 WAPPR FRB ov (AOF ov 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia))); [| exact VIS]|].
{ intros i Hi rr Hin Hr. unfold WR, PMSPA.W_run, PMSPA.W_srcf, PMSPA.err_W, PMSPA.o_src, PMSPA.o_is, PMSPA.o_tb, PMSPA.o_vec, PMSPA.o_ec, PMSPA.o_p in Hin.
cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. unfold L5.in_rng in Hr.
repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; clear - Hi Hr Eov Eop O1; lia|]). destruct Hin. }
split; [apply (PMKA.u64_keepA RSEGS L ar LBX FF sp 30720 WR M M4 EKb4 WAPPR FRB (op + 384) ov (AOF (op + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [| exact VREF]|].
{ intros i Hi rr Hin Hr. unfold WR, PMSPA.W_run, PMSPA.W_srcf, PMSPA.err_W, PMSPA.o_src, PMSPA.o_is, PMSPA.o_tb, PMSPA.o_vec, PMSPA.o_ec, PMSPA.o_p in Hin.
cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. unfold L5.in_rng in Hr.
repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; clear - Hi Hr Eop O1; lia|]). destruct Hin. }
split; [apply (PMASK.base_keep L ar C LY LB FF sp 30720 Wc M M4 EK04); [| exact BASE]|].
{ intros a Ha rr Hin Hr. destruct (WcR rr a Hin Hr) as [X|[X|[X|[X|X]]]]; [clear - Ha X O1; lia| clear - Ha X I1; lia| clear - Ha X I1; lia| destruct Bqi as [Y|Y]; clear - Ha X Y; lia| clear - Ha X GFR; lia]. }
split; [apply (PMKA.err_okA_keep RSEGS PMA.AD PMA.AAD L ar LB FF sp 30720 Wc M M4 EK04 e PMA.addrs_wf_A); [| exact ERR]|].
{ intros a D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
split; [exact (PMA.ly_static L C LY a D)|]. intros rr Hin Hr. destruct (WcR rr a Hin Hr) as [X|[X|[X|[X|X]]]];
[clear - DI X O1; lia| clear - DI X I1; lia| clear - DI X I1; lia| destruct Bqi as [Y|Y]; clear - DI X Y; lia| clear - DI X GFR; lia]. }
exact TBOK. }
{ exact INCS. }
{ unfold s4, PMSPA.with_src. unfold PM.inv in *. cbn [PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_tb PM.p_tg] in *. exact INV. }
{ exact EC4. }
{ unfold s4, PMSPA.with_src. cbn [PM.p_src]. destruct STEP4 as (_ & _ & _ & _ & U4). clear - U4 UNR. lia. }
{ unfold s4, PMSPA.with_src, PM.pot_parser. cbn [PM.p_k PM.p_tb PM.p_tg]. exact CRED. }
intros fx7 R7 M7 model7 LK7 Aw7 s7 sm7 e7 cr7 RP7 RPOST7 HP7 CK7 MRT7 INCLK7 INCAw7 AM7 HH7.
change (PMSPA.pm_scr 8) with 28672 in HP7.
assert (WRR : forall rr a, In rr WR -> L5.in_rng rr a -> (fb + 32 <= a < fb + 1016) \/ (0x66d380 <= a < 0x68f0f4)).
{ intros rr a Hin Hr. unfold WR, PMSPA.W_run, PMSPA.W_srcf, PMSPA.err_W, PMSPA.o_src, PMSPA.o_is, PMSPA.o_tb, PMSPA.o_vec, PMSPA.o_ec, PMSPA.o_p in Hin.
cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. unfold L5.in_rng in Hr.
repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; clear - Hr; lia|]). destruct Hin. }
assert (BI7 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 30720 (sp - 96) (own sp R) F 0 WR (PM.parser_own s7) M7 model7 LK7 cr7 Aw7).
{ apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 30720 (sp - 96) (sp - 88) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PM.parser_own s) G
WR WR (PM.parser_own s) [] (PM.parser_own s7) M4 model5 LK4 cr Aw4 M7 model7 LK7 cr7 Aw7 28672 WR BI5 HP7 HH7 AM7 MRT7 INCAw7 INCLK7);
[clear; lia| clear; lia| | intros a _ X; exact X| intros a X; exact X].
intros rr a Hin Hr. change (ff_bytes 0 / 8) with 8. unfold ocell, SB.
pose proof GFR as (GF1 & GF2 & _). assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
assert (DF2 : F / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; clear - GF2; lia).
pose proof FSAPP as (FA0 & FA1 & FA2).
destruct (WRR rr a Hin Hr) as [X|X]; (split; [clear - X OCE SL96 SPT Eop F2 FSCEIL; lia|]).
- unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1. destruct FA1 as [Y|Y]; clear - X Y DF1 DF2 F1 F2; lia.
- clear - X DF1; lia. }
set (H7 := ahid Aw7 model7) in *. set (MV7 := mrestrict H7 M7) in *.
destruct (PMAUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 30720 (sp - 96) (sp - 88) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PM.parser_own s) G
WR (PM.parser_own s7) M7 model7 LK7 cr7 Aw7 BI7) as ((WS7 & _ & _ & _ & _) & OWN7 & (FD7 & FW7 & FSW7 & FLC7 & FLW7) & (FLCc7 & FLV7 & VF7 & VS7 & VSH7)).
change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *. replace (sp - (sp - 96)) with 96 in WS7 by (clear; lia).
replace (F + 64 - 8) with (F + 56) in FLC7 by (clear; lia).
assert (R7c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R7 (reg j) = getr R4 (reg j)).
{ intros j Hj. rewrite (L5SAR.cs_of_preserved R6 R7 j RP7 Hj). exact (R6c j Hj). }
pose proof OWN7 as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88).
pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8.
pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18.
pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19. pose proof (bv_unsigned_in_range 64 (getr R (reg 20))) as B20.
pose proof (bv_unsigned_in_range 64 (getr R (reg 21))) as B21. pose proof (bv_unsigned_in_range 64 (getr R (reg 22))) as B22.
pose proof (bv_unsigned_in_range 64 (getr R (reg 23))) as B23. pose proof (bv_unsigned_in_range 64 (getr R (reg 24))) as B24.
pose proof (bv_unsigned_in_range 64 (getr R (reg 25))) as B25. change (bv_modulus 64) with (2 ^ 64) in *.
cfeed P (PMARTP.artE_conc fx7 R7 MV7 (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl
| 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9))
| 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20))
| 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23))
| 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | _ => 0 end)) ltac:(first [assumption | (rewrite R7c by inl; assumption) | unfold PMARTP.aligned; assumption]).
destruct P as (fx8 & R8 & M8v & MG8 & _ & FRZ8 & MS8 & KS8 & E1 & E2 & E8 & E9 & _ & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & FL0 & _).
assert (R8ra : getr R8 (reg 1) = Z_to_bv 64 r) by (rewrite E1, Z_to_bv_bv_unsigned; exact Rra).
pose proof (PMK.ret_to RSEGS fx8 R8 M8v 0xad3e8 (ltac:(oW' 0xad3e8%Z)) r (ltac:(oF' 0xad3e8%Z)) eq_refl (ltac:(oD' 0xad3e8%Z)) R8ra Hr1 Hr2) as MSr.
apply (PMAUK.retire_core L ar C HI LYa HIok M model LBX FF LK Aw sp 30720 (sp - 96) (sp - 88) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PM.parser_own s) G
WR (PM.parser_own s7) M7 model7 LK7 cr7 Aw7 fx7 fx8 R7 0xad2fc R8 r M8v K BI7 (msteps_trans _ _ _ _ MS8 MSr) MG8).
{ intros a Ha Nw. unfold PMAUK.Wret in Nw. change (ff_bytes 0) with 64 in Nw. apply FRZ8; [exact Ha| intros X; apply Nw; left; left; clear - X; lia
| intros X; apply Nw; left; right; unfold SB; clear - X; lia| intros X; apply Nw; right; clear - X; lia]. }
{ exact FL0. }
intros Mf modelf FZf AHf MRTf AMf HHf.
assert (EKf : L5SAR.ek L ar (PM.parser_own s7 ++ LBX) FF 0 0 [] M7 Mf).
{ apply (PMAUAR.wret_ek L ar C HI LY HIok LBX FF LK Aw sp 30720 (sp - 96) (sp - 88) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PM.parser_own s)
(PM.parser_own s7 ++ LBX) LK7 cr7 Aw7 M7 Mf _ [] (fun _ => False) G HH7 (fun a X => match X with end)).
intros a Ha N. apply FZf; [exact Ha| intros X; apply N; left; exact X]. }
pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH7) as BRB7.
destruct RPOST7 as ((PA7 & IA7 & VIS7 & VREF7 & BASE7 & ERR7 & TB7) & STEP7 & EE7 & ALT7).
pose proof BI7 as (_ & _ & _ & INCA7 & INCL7 & _).
apply (KONT fx8 R8 Mf modelf LK7 Aw7 s7 sm7 e7 cr7).
-- apply L5SAR.preserved_by_index. intros j Hj. pose proof Hj as Hj'. unfold L5SAR.cs_all in Hj.
repeat (destruct Hj as [<-|Hj]; [first [ rewrite E2; exact (eq_sym Rsp) | rewrite E8; apply Z_to_bv_bv_unsigned | rewrite E9; apply Z_to_bv_bv_unsigned
| rewrite E18; apply Z_to_bv_bv_unsigned | rewrite E19; apply Z_to_bv_bv_unsigned | rewrite E20; apply Z_to_bv_bv_unsigned
| rewrite E21; apply Z_to_bv_bv_unsigned | rewrite E22; apply Z_to_bv_bv_unsigned | rewrite E23; apply Z_to_bv_bv_unsigned
| rewrite E24; apply Z_to_bv_bv_unsigned | rewrite E25; apply Z_to_bv_bv_unsigned
| rewrite (KS8 _) by inl; rewrite (R7c _) by inl; apply G34'; inl ] |]).
destruct Hj.
-- unfold PMSPA.run_post, PMSPA.run_pre.
split; [split; [| split; [| split; [| split; [| split; [| split]]]]]|].
++ apply (PMKA.parser_keepA RSEGS PMA.AD L ar (PM.parser_own s7 ++ LBX) FF 0 0 [] M7 Mf EKf PMKA.wapp_nil FRB BRB7 _ _ _ AOP); [| intros i _ r0 []| intros i _ r0 []| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact PA7].
apply incl_appl, incl_refl.
++ apply (PMKA.iss_keepA RSEGS PMA.AD L ar (PM.parser_own s7 ++ LBX) FF 0 0 [] M7 Mf EKf PMKA.wapp_nil FRB BRB7 _ str sm7 AOI); [| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA7].
apply incl_appr. exact INCS.
++ apply (PMKA.visitor_keepA RSEGS PMA.AD L ar (PM.parser_own s7 ++ LBX) FF 0 0 [] M7 Mf EKf PMKA.wapp_nil FRB _ (AOF ov 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia))); [intros i _ r0 []| exact VIS7].
++ apply (PMKA.u64_keepA RSEGS L ar (PM.parser_own s7 ++ LBX) FF 0 0 [] M7 Mf EKf PMKA.wapp_nil FRB (op + 384) _ (AOF (op + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [intros i _ r0 []| exact VREF7].
++ apply (PMASK.base_keep L ar C LY (PM.parser_own s7 ++ LBX) FF 0 0 [] M7 Mf EKf); [intros a _ r0 []| exact BASE7].
++ apply (PMKA.err_okA_keep RSEGS PMA.AD PMA.AAD L ar (PM.parser_own s7 ++ LBX) FF 0 0 [] M7 Mf EKf e7 PMA.addrs_wf_A); [| exact ERR7].
intros a D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
split; [exact (PMA.ly_static L C LY a D)| intros r0 []].
++ exact TB7.
++ split; [apply (PMAPAR.src_step_transA (PM.p_src s) src4 (PM.p_src s7) sm sm4 sm7 STEP4); exact STEP7|].
split; [exact EE7|].
destruct ALT7 as [(v & Hv & EC7 & MO7 & E7)|(EC7 & INV7 & PROG7)].
** left. exists v. split; [exact Hv|]. split; [|split; [exact MO7| exact E7]].
apply (PMKA.ec_keepA RSEGS L ar (PM.parser_own s7 ++ LBX) FF 0 0 [] M7 Mf EKf PMKA.wapp_nil FRB _ v _ (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia))); [intros i _ r0 []| exact EC7].
** right. split; [apply (PMKA.ec_keepA RSEGS L ar (PM.parser_own s7 ++ LBX) FF 0 0 [] M7 Mf EKf PMKA.wapp_nil FRB _ 0 _ (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia))); [intros i _ r0 []| exact EC7]|].
split; [exact INV7|].
unfold PMSPA.prog_value_strict. unfold PMSPA.prog_value, PMSPA.push_rel in PROG7. unfold PMSPA.consumed in CONS.
destruct STEP7 as (_ & _ & _ & _ & U7). unfold s4, PMSPA.with_src in PROG7, U7. cbn [PM.p_stk PM.p_src] in PROG7, U7.
split; [unfold PMSPA.push_rel; destruct PROG7 as [X|(c & X1 & X2 & X3 & X4 & X5)]; [left; exact X| right; exists c; split; [exact X1|]; split; [exact X2|]; split; [exact X3|]; split; [exact X4|]]|].
{ intros Y. specialize (X5 Y). clear - X5 CONS. lia. }
clear - U7 CONS. lia.
-- exact AHf.
-- unfold s4, PMSPA.with_src in CK7. exact CK7.
-- exact MRTf.
-- exact INCL7.
-- exact INCA7.
-- exact AMf.
-- exact HHf.
Qed.
End WithHeap.
End PMARTV.
