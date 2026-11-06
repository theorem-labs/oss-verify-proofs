(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIfaceAJx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface
AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA L5DefsAB0
L5CoreAB0 L5CoreSpecsAB0 L5StepARB0 L5CoreBRB0 L5ADetailHRB0 PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA PmSpecsA PmSpecsAX PmSpecsAb
PmModelFactsA PmStepAB0 PmStep PmParStep PmBSrcKit PmBParKit PmBUarK PmBUar PmParKit2 PmBParseD PmBParseP1.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBParseE () := ([""; "Corelib.Init.Datatypes."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBParseD.PMBLPD."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "stdpp.bitvector.definitions."], [["0Aw"; "1bool"; "1list"; "1option"; "1prod"; "2Z"; "0F"; "0FF"; "0HI"; "0K"; "0L"; "0LBX"; "0LK"; "0LK2"; "3Model"; "4bvmap"]; ["0M"; "0M1"; "0M2"; "0R"; "0R1"; "5credit"; "6fframe"; "7SCFG"; "8aframe"; "8alinv"; "8apctx"; "9pst"; "9strm"; "9vstr"; ":cfg"; ";FPState"]; ["<TSet"; "=srealizes"; ">loaded_segments"; "0SCFG_P"; "0ar"; "0cat"; "0cr"; "0e"; "0fb"; "0fl"; "0fx"; "0fx1"; "0model"; "0model1"; "0model2"; "0r"]; ["0s"; "0sm"; "0sp"; "?bv"; "0str"]]).
Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].
Module PMBLPE.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMB.ly_as0 L C LY.
Lemma parse_entry : ltac2:(TCodec.tc2 tcn__PmBParseE "S9'O&?y5'QCyR0%211%5241'3y8%611%311p061'>&Q0'2'4'5%2211%411&F%611&E'K'M'L'1&JvQ3v:vQ4v8r>rAr@r?r=r<r;r:r9r8r7r6r5r4r3r2r1%FEEDCBA@?>=<;:987654321&HrGrFrErCrB%6BKJI54321GFEHA<;:98&IrLrKrJrHrD%6LQ2Q1Q05432<;:19NMLOKJHA@?F:LKJ1'Q1&Q2&G%11Q7&N+edcH%265JI1HG%74641;p091pRLQL1pQ4QN1pQ:R41pRHR;1p0E1pRNR11pQ6R31pLQK1pRDR01p>R11+edT8%@6CFN1MQC%E4DB1QCp041p0Q61pR@QN1pS4R01pS:R21pS2R41pR<R;1pRBR<1pS0R=1pS6R>1pR>R:1p2R>1pJR=1p@R>1pHRA1pDRG1pRJRI1pQ2RK1pQ8S11pRFS81").
Proof. intros fx R M model K LBX FF LK Aw cr sp r fb cat s str sm e.
intros CTX KLOOP. pose proof CTX as CTX0.
destruct CTX as (HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & UNR & CRED & KONT).
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 10) with 32768 in *. change (32768 / 8) with 4096 in STKSH.
pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
destruct ARGS as (A10 & A11 & A12).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12.
pose proof RPRE as (PA & IA & VIS & VREF & BASE & ERR & TBOK).
pose proof FOK as ((rs & Hfb) & Fal).
pose proof (PMBPAR.op_vis L ar C HI LY HIok _ FF LK cr Aw M model fb _ s HH FOK PA) as ((O1 & O8 & ONSH) & Zop & Z32 & Z20 & OWR & OCE & OVIS & AOP & Eop).
pose proof (PMBPAR.ov_vis L ar C HI LY HIok _ FF LK cr Aw M model fb HH FOK VIS) as ((V1 & V8 & VNSH) & Zov & VWR & VCE & VVT & AOV & Eov).
pose proof (PMBPAR.oec_vis L ar C HI LY HIok _ FF LK cr Aw M model fb 0 cat HH FOK EC0) as ((E1 & E8 & ENSH) & Zoec & EWR & ECE & EV0 & AOE & Eoec).
pose proof (PMBSK.mach_vis L ar C HI LY HIok _ FF LK cr Aw M model HH BASE) as (VM0 & VM1 & VM2).
pose proof (PMBSK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 32768 288 HH ASTK ltac:(lia)) as (SL288 & SH288 & SWR).
pose proof (PMBSK.img_shz_vis L ar C HI LY IL ICok ILY _ FF LK cr Aw M model 0x12e760 16 HH ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as ZVT.
cbn in ZVT.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & STOP & _).
pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 4) with 1024 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, F1, F2.
set (op := PMSPA.o_p PMB.AD fb) in *. set (ov := PMSPA.o_v PMB.AD fb) in *. set (oec := PMSPA.o_ec PMB.AD fb) in *. set (ois := PMSPA.o_is PMB.AD fb) in *.
assert (Eois : ois = fb + 96) by reflexivity.
set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
assert (AOF : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> PMSPA.aobjA FF a n).
{ intros a n X1 X2. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. lia. }
pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (_ & VISs & _).
assert (Q1 : 140735332487456 <= sp <= 140737488355328) by (clear - SLO SHI SPT; lia).
assert (Q2 : (sp - 288) + 288 <= op \/ op + 384 <= (sp - 288)) by (clear - OCE SL288; lia).
assert (Q3 : (sp - 288) + 288 <= ov \/ ov + 8 <= (sp - 288)) by (clear - VCE SL288; lia).
assert (Q4 : (sp - 288) + 288 <= oec \/ oec + 16 <= (sp - 288)) by (clear - ECE SL288; lia).
assert (Q5 : op + 384 <= ov \/ ov + 8 <= op) by (clear - Eop Eov; lia).
assert (Q6 : oec + 16 <= ov \/ ov + 8 <= oec) by (clear - Eoec Eov; lia).
assert (Q7 : op + 384 <= oec \/ oec + 16 <= op) by (clear - Eop Eoec; lia).
assert (Q0 : 0 <= sp < 2 ^ 64 /\ 0 <= op < 2 ^ 64 /\ 0 <= ov < 2 ^ 64 /\ 0 <= oec < 2 ^ 64) by (clear - Q1 O1 V1 E1; lia).
destruct Q0 as (Q0a & Q0b & Q0c & Q0d).
cfeed P (PMBLPP1.blpA_conc fx R MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | _ => 0 end)) ltac:(first [assumption | unfold PMBLPP1.aligned; assumption]).
destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T12 & T19 & T27
& C152 & C144 & C104 & C96 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8 & C288).
unfold PMSPA.cfg.
apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xad088 R1 0x5d670 M1v (fun a => sp - 288 <= a < sp - 288 + 288) K HH AM MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
{ intros a Ha Wa. split; [|intros X; clear - Wa X SL288 SPT; lia]. unfold aclientw, aclient_g. right; left. split; [clear - Wa SL288 SH288; lia| intros X; clear - X; lia]. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
set (LB := PM.parser_own s ++ LBX) in *.
assert (INCX : incl LBX LB) by (unfold LB; apply incl_appr; apply incl_refl).
assert (NCS0 : forall a, sp - 288 <= a < sp -> ~ aclient L ar LB FF sp 32768 a).
{ intros a Xa Hc. destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 32768 a HH SPT Hc) as [Y|Y].
- clear - Xa Y; lia.
- clear - Xa Y SL288; lia. }
assert (EK01f : L5SAR.ek L ar LB FF sp 32768 [] M M1).
{ apply (L5SAR.ek_piece L ar LB FF sp 32768 [] M M1 (fun a => sp - 288 <= a < sp - 288 + 288) FR1). intros a Ha Hc _ X. apply (NCS0 a); [clear - X; lia| exact Hc]. }
assert (DK01f : L5SAR.dk L ar LB FF sp 32768 M M1) by (apply L5SAR.dk_grows; exact MGM1).
pose proof (PMKB.ek_sublb L ar LB LBX FF sp 32768 [] M M1 INCX EK01f) as EK01.
pose proof (PMKB.dk_sublb L ar LB LBX FF sp 32768 M M1 INCX DK01f) as DK01.
assert (SV1 : forall a v, sp - 288 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
{ intros a v Ha1 Ha2 X. apply (proj1 (L5A.u64_at_vis H M1 a v (VISs a 8 ltac:(clear - Ha1 SL288 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL288 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))).
rewrite VIS1. exact X. }
assert (OWN1 : PMBLPD.own sp R M1).
{ unfold PMBLPD.own. split; [apply SV1; [clear; lia| clear; lia| exact C8]|]. split; [apply SV1; [clear; lia| clear; lia| exact C16]|].
split; [apply SV1; [clear; lia| clear; lia| exact C24]|]. split; [apply SV1; [clear; lia| clear; lia| exact C32]|].
split; [apply SV1; [clear; lia| clear; lia| exact C40]|]. split; [apply SV1; [clear; lia| clear; lia| exact C48]|].
split; [apply SV1; [clear; lia| clear; lia| exact C56]|]. split; [apply SV1; [clear; lia| clear; lia| exact C64]|].
split; [apply SV1; [clear; lia| clear; lia| exact C72]|]. split; [apply SV1; [clear; lia| clear; lia| exact C80]|].
split; [apply SV1; [clear; lia| clear; lia| exact C88]|]. split; [apply SV1; [clear; lia| clear; lia| exact C96]|].
apply SV1; [clear; lia| clear; lia| exact C104]. }
assert (C144' : L5.u64_at RSEGS M1 (sp - 144) ov) by (apply SV1; [clear; lia| clear; lia| exact C144]).
assert (C152' : L5.u64_at RSEGS M1 (sp - 152) op) by (apply SV1; [clear; lia| clear; lia| exact C152]).
clear C104 C96 C88 C80 C72 C64 C56 C48 C40 C32 C24 C16 C8 C288 C152 SV1.
assert (FRk1 : ff_room 1 FF LK) by (apply (PMBUAR.ff_room_of 10 FF LK 1 FRM); [clear; lia| right; left; reflexivity]).
change 0x5d670 with (PMB.SM_PC 1).
apply (PMBUAR.uar_sm L ar C HI LY HIok 1 LBX (PM.parser_own s) FF LK cr Aw sp 32768 (sp - 288) (sp - 104) sp (PMBLPD.ocell sp) (PMBLPD.own sp R)
fx1 R1 M M1 model model1 K 708864 ltac:(right; left; reflexivity) HH HH1 AM1 K0 ASTK MGM1 EK01 DK01).
{ rewrite L5K.rl2. exact T2. }
{ rewrite L5K.rl4. rewrite (KS1 4%nat) by inl. rewrite <- L5K.rl4. exact Rtp. }
{ rewrite L5K.rl1. exact T1. }
{ reflexivity. }
{ clear; lia. }
{ replace (sp - 288) with (sp + (-18) * 16) by (clear; lia). rewrite Z_mod_plus_full. apply PMKB.mod16_8' in SP32 || idtac.
assert (X : sp mod 16 = 0) by (apply Z.mod_divide in SP32; [|lia]; destruct SP32 as (q & ->); replace (q * 32) with ((q * 2) * 16) by lia; apply Z.mod_mul; lia). exact X. }
{ clear; lia. } { clear; lia. } { clear; lia. } { clear; lia. }
{ intros a Ha. exact Ha. }
{ intros Ma Mb OW AG. apply (PMBLPD.own_agree sp R Ma Mb ltac:(clear - SL288 SPT; lia) ltac:(clear - SHI SPT; lia) OW AG). }
{ exact FRk1. }
{ intros f Hf. specialize (FRS f Hf). clear - FRS; lia. }
intros R2 M2 model2 F fl LK2 G G10 RP2 AM2 MRT2 ASTK2 EK02 DK02 EK12f DK12f AGF FW FSHW FSHZ FLC FLW FDEF VF VSH VFL APART.
change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *. change (128 - 8) with 120 in *.
pose proof G as G'. destruct G' as [_ _ _ _ _ _ _ GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
change (ff_bytes 1) with 128 in *.
pose proof (L5SAR.ek_trans L ar LB FF sp 32768 [] M M1 M2 EK01f EK12f) as EK02f.
pose proof (L5SAR.dk_trans L ar LB FF sp 32768 M M1 M2 DK01f DK12f) as DK02f.
pose proof (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
assert (PA2 : PM.parser_at RSEGS PMB.AD PMSPA.accA PMSPA.annA M2 op ois s).
{ apply (PMKB.parser_keepA RSEGS PMB.AD L ar LB FF sp 32768 [] M M2 EK02f PMKB.wapp_nil FRB BRB _ _ _ AOP); [| intros i _ r0 []| intros i _ r0 []| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact PA].
unfold LB. apply incl_appl, incl_refl. }
assert (VIS2 : PMSPA.visitor_at RSEGS PMB.AD M2 ov).
{ apply (PMKB.visitor_keepA RSEGS PMB.AD L ar LB FF sp 32768 [] M M2 EK02f PMKB.wapp_nil FRB ov AOV); [intros i _ r0 []| exact VIS]. }
assert (EC2 : PMSPA.ec_at RSEGS M2 oec 0 cat).
{ apply (PMKB.ec_keepA RSEGS L ar LB FF sp 32768 [] M M2 EK02f PMKB.wapp_nil FRB oec 0 cat AOE); [intros i _ r0 []| exact EC0]. }
assert (BASE2 : PMSTA.base_okA RSEGS PMB.AD M2) by (apply (PMBSK.base_keep L ar C LY LB FF sp 32768 [] M M2 EK02f); [intros a _ r0 []| exact BASE]).
assert (HH2 : ri_inv HI LB ((F, 1, sp - 288 + 32) :: FF) LK2 cr Aw M2 (vml_of model2)) by exact GHH2.
set (FF' := (F, 1, sp - 288 + 32) :: FF) in *.
assert (FOK' : PMSPA.frame_okA FF' fb) by exact (PMBUAR.frame_okA_push FF fb F 1 (sp - 288 + 32) FOK).
pose proof (PMBPAR.op_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 fb _ s HH2 FOK' PA2) as ((_ & _ & _) & Zop2 & Z322 & Z202 & OWR2 & _ & OVIS2 & _ & _).
pose proof (PMBPAR.ov_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 fb HH2 FOK' VIS2) as ((_ & _ & _) & Zov2 & VWR2 & _ & VVT2 & _ & _).
pose proof (PMBPAR.oec_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 fb 0 cat HH2 FOK' EC2) as ((_ & _ & _) & Zoec2 & EWR2 & _ & _ & _ & _).
set (H2 := ahid Aw model2) in *. set (MV2 := mrestrict H2 M2) in *.
fold op ov oec MV2 in Zop2, Z322, Z202, OWR2, OVIS2, Zov2, VWR2, VVT2, Zoec2, EWR2.
pose proof (PMBSK.mach_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 HH2 BASE2) as (W0 & W1 & W2).
pose proof (PMBSK.stk_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 sp 32768 288 HH2 ASTK2 ltac:(lia)) as (_ & _ & SWR2).
pose proof (PMBSK.img_shz_vis L ar C HI LY IL ICok ILY _ _ LK2 cr Aw M2 model2 0x12e760 16 HH2 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as ZVT2.
cbn in ZVT2. fold MV2 in W0, W1, W2, SWR2, ZVT2.
assert (CLfb : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> 0 < n -> forall i, 0 <= i < n -> aclient L ar LB FF 0 0 (a + i)).
{ intros a n X1 X2 X3 i Hi. unfold aclient, aclient_g. do 3 right; left. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
change (ff_bytes 4) with 1024. split; [clear - X1 X2 Hi; lia| intros Y; clear - X1 X2 Hi Y; lia]. }
destruct (APART op 384 0 0 (CLfb op 384 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (ApF & ApSF & ApFL).
destruct (APART ov 8 0 0 (CLfb ov 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (AvF & AvSF & AvFL).
destruct (APART oec 16 0 0 (CLfb oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (DjF & DjSF & DjFL).
assert (CLsh : forall a n, fb / 8 + SB <= a -> a + n <= fb / 8 + SB + 128 -> 0 < n -> forall i, 0 <= i < n -> aclient L ar LB FF 0 0 (a + i)).
{ intros a n X1 X2 X3 i Hi. unfold aclient, aclient_g. do 5 right; left. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
change (ff_bytes 4) with 1024. unfold in_shadow_of, S. unfold SB in *.
assert (D1 : (fb + 1024 - 1) / 8 = fb / 8 + 127).
{ pose proof (Z.div_mod fb 1024 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
replace (1024 * (fb / 1024) + 1024 - 1) with (7 + (128 * (fb / 1024) + 127) * 8) by (clear; lia). rewrite Z.div_add by lia.
replace (1024 * (fb / 1024)) with ((128 * (fb / 1024)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
rewrite D1. clear - X1 X2 Hi. lia. }
assert (SHD : forall o k, o = fb + 8 * k -> o / 8 + SB = fb / 8 + SB + k).
{ intros o k ->. pose proof (Z.div_mod fb 1024 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
replace (1024 * (fb / 1024) + 8 * k) with ((128 * (fb / 1024) + k) * 8) by (clear; lia). rewrite Z.div_mul by lia.
replace (1024 * (fb / 1024)) with ((128 * (fb / 1024)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
assert (SHop : op / 8 + SB = fb / 8 + SB + 58) by (apply SHD; clear - Eop; lia).
assert (SHov : ov / 8 + SB = fb / 8 + SB + 54) by (apply SHD; clear - Eov; lia).
assert (SHoe : oec / 8 + SB = fb / 8 + SB + 124) by (apply SHD; clear - Eoec; lia).
destruct (APART (op / 8 + SB) 48 0 0 (CLsh (op / 8 + SB) 48 ltac:(clear - SHop; lia) ltac:(clear - SHop; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (_ & AsopSF & _).
destruct (APART (ov / 8 + SB) 1 0 0 (CLsh (ov / 8 + SB) 1 ltac:(clear - SHov; lia) ltac:(clear - SHov; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (_ & AsovSF & _).
destruct (APART (oec / 8 + SB) 2 0 0 (CLsh (oec / 8 + SB) 2 ltac:(clear - SHoe; lia) ltac:(clear - SHoe; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (_ & AsoeSF & _).
unfold SB in AsopSF, AsovSF, AsoeSF.
assert (R2c : forall j, In j L5SAR.cs_all -> getr R2 (reg j) = getr R1 (reg j)) by (intros j Hj; apply (L5SAR.cs_of_preserved R1 R2 j RP2 Hj)).
assert (B2R : getr R2 (reg 2) = Z_to_bv 64 (sp - 288)) by (rewrite (R2c 2%nat) by inl; exact T2).
assert (B8R : getr R2 (reg 8) = Z_to_bv 64 sp) by (rewrite (R2c 8%nat) by inl; exact T8).
assert (B9R : getr R2 (reg 9) = Z_to_bv 64 (sp - 288)) by (rewrite (R2c 9%nat) by inl; exact T9).
assert (B19R : getr R2 (reg 19) = Z_to_bv 64 oec) by (rewrite (R2c 19%nat) by inl; exact T19).
assert (B27R : getr R2 (reg 27) = Z_to_bv 64 2147450880) by (rewrite (R2c 27%nat) by inl; exact T27).
assert (B10R : getr R2 (reg 10) = Z_to_bv 64 F) by (rewrite <- L5K.rl10; exact G10).
pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LK2 cr Aw M2 model2 HH2) as (_ & VISs2 & _).
assert (SV2 : forall a v, sp - 288 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1 a v -> L5.u64_at RSEGS MV2 a v).
{ intros a v Ha1 Ha2 X. apply (proj2 (L5A.u64_at_vis H2 M2 a v (VISs2 a 8 ltac:(clear - Ha1 SL288 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL288 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))).
apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply AGF; clear - Ha1 Ha2 Hi; lia| clear - Ha1 SL288 SPT; lia| clear - Ha2 SHI SPT; lia| exact X]. }
pose proof OWN1 as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96 & S104).
assert (S8' : L5.u64_at RSEGS MV2 (sp - 8) (bv_unsigned (getr R (reg 1)))) by (apply SV2; [clear; lia| clear; lia| exact S8]). assert (S16' : L5.u64_at RSEGS MV2 (sp - 16) (bv_unsigned (getr R (reg 8)))) by (apply SV2; [clear; lia| clear; lia| exact S16]).
assert (S24' : L5.u64_at RSEGS MV2 (sp - 24) (bv_unsigned (getr R (reg 9)))) by (apply SV2; [clear; lia| clear; lia| exact S24]). assert (S32' : L5.u64_at RSEGS MV2 (sp - 32) (bv_unsigned (getr R (reg 18)))) by (apply SV2; [clear; lia| clear; lia| exact S32]).
assert (S40' : L5.u64_at RSEGS MV2 (sp - 40) (bv_unsigned (getr R (reg 19)))) by (apply SV2; [clear; lia| clear; lia| exact S40]). assert (S48' : L5.u64_at RSEGS MV2 (sp - 48) (bv_unsigned (getr R (reg 20)))) by (apply SV2; [clear; lia| clear; lia| exact S48]).
assert (S56' : L5.u64_at RSEGS MV2 (sp - 56) (bv_unsigned (getr R (reg 21)))) by (apply SV2; [clear; lia| clear; lia| exact S56]). assert (S64' : L5.u64_at RSEGS MV2 (sp - 64) (bv_unsigned (getr R (reg 22)))) by (apply SV2; [clear; lia| clear; lia| exact S64]).
assert (S72' : L5.u64_at RSEGS MV2 (sp - 72) (bv_unsigned (getr R (reg 23)))) by (apply SV2; [clear; lia| clear; lia| exact S72]). assert (S80' : L5.u64_at RSEGS MV2 (sp - 80) (bv_unsigned (getr R (reg 24)))) by (apply SV2; [clear; lia| clear; lia| exact S80]).
assert (S88' : L5.u64_at RSEGS MV2 (sp - 88) (bv_unsigned (getr R (reg 25)))) by (apply SV2; [clear; lia| clear; lia| exact S88]). assert (S96' : L5.u64_at RSEGS MV2 (sp - 96) (bv_unsigned (getr R (reg 26)))) by (apply SV2; [clear; lia| clear; lia| exact S96]).
assert (S104' : L5.u64_at RSEGS MV2 (sp - 104) (bv_unsigned (getr R (reg 27)))) by (apply SV2; [clear; lia| clear; lia| exact S104]). assert (S144' : L5.u64_at RSEGS MV2 (sp - 144) ov) by (apply SV2; [clear; lia| clear; lia| exact C144']).
assert (S152' : L5.u64_at RSEGS MV2 (sp - 152) op) by (apply SV2; [clear; lia| clear; lia| exact C152']).
pose proof PA2 as (_ & _ & _ & _ & PD9 & _). pose proof INV as (_ & ID0 & _).
assert (D9 : L5.u8_at RSEGS MV2 (op + 9) 0).
{ rewrite ID0 in PD9. apply (proj2 (L5A.u8_at_vis H2 M2 (op + 9) 0 ltac:(apply OVIS2; lia) ltac:(lia) ltac:(lia))). exact PD9. }
pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8.
pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18.
pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19. pose proof (bv_unsigned_in_range 64 (getr R (reg 20))) as B20.
pose proof (bv_unsigned_in_range 64 (getr R (reg 21))) as B21. pose proof (bv_unsigned_in_range 64 (getr R (reg 22))) as B22.
pose proof (bv_unsigned_in_range 64 (getr R (reg 23))) as B23. pose proof (bv_unsigned_in_range 64 (getr R (reg 24))) as B24.
pose proof (bv_unsigned_in_range 64 (getr R (reg 25))) as B25. pose proof (bv_unsigned_in_range 64 (getr R (reg 26))) as B26.
pose proof (bv_unsigned_in_range 64 (getr R (reg 27))) as B27.
change (bv_modulus 64) with (2 ^ 64) in B1, B8, B9, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27.
assert (QF1 : 6893568 <= F <= 140737488355200) by (clear - GFR; lia).
assert (QF2 : 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64) by (clear - GFR GFLR; lia). destruct QF2 as (QF2a & QF2b).
assert (QF3 : 4096 <= fl <= 140737488355327) by (clear - GFLR; lia).
assert (QF4 : (sp - 288) + 288 <= F \/ F + 128 <= (sp - 288)) by (clear - GFCEIL SL288; lia).
assert (QF5 : (sp - 288) + 288 <= fl \/ fl + 1 <= (sp - 288)) by (clear - GFLR SL288; lia).
assert (QF6 : F + 128 <= 65536 \/ 65536 + 1204224 <= F) by (clear - GFR; lia).
assert (QF7 : ((F / 8) + 2147450880) + 16 <= 2147605740 \/ 2147605740 + 16 <= ((F / 8) + 2147450880)).
{ clear - GFR. assert (F / 8 >= 845384) by (apply Z.le_ge; apply Z.div_le_lower_bound; lia). lia. }
assert (FLC' : L5.u64_at RSEGS MV2 (F + 120) fl) by (replace (F + 120) with (F + 128 - 8) by (clear; lia); exact FLC).
cfeed P (PMBLPP1.blpB_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl
| 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9))
| 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20))
| 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23))
| 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26))
| 76%nat => bv_unsigned (getr R (reg 27)) | _ => 0 end)) ltac:(first [assumption | unfold PMBLPP1.aligned; assumption]).
destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y16 & Y17 & Y18 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26
& U224 & U200 & U216 & U208 & U192 & U256 & U160 & U240 & U176 & U248 & U168 & U264 & U112 & U184 & U136 & ZS11 & ZS10 & ZS9 & ZS8 & ZS7 & ZS6
& ZS5 & ZS4 & ZS3 & ZS2 & ZS1 & ZS0 & HD16 & HD8 & HD0 & U232 & DF24 & ZSH
& X8 & X16 & X24 & X32 & X40 & X48 & X56 & X64 & X72 & X80 & X88 & X96 & X104 & X144 & X152).
set (W3 := fun a => (sp - 288 <= a < sp - 288 + 288) \/ (F <= a < F + 24) \/ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 16)).
apply (L5SAR.apiece L ar C HI LYa HIok LB FF' LK2 cr Aw M2 model2 fx1 fx3 R2 0xad100 R3 0xad278 M3v W3 K HH2 AM2 MS3 MG3).
{ intros a Ha Hn. apply FRZ3; [exact Ha| intros X; apply Hn; left; exact X| intros X; apply Hn; right; left; clear - X; lia| intros X; apply Hn; right; right; clear - X; lia]. }
{ intros a Ha Wa. split.
- destruct Wa as [X|[X|X]].
+ unfold aclientw, aclient_g. right; left. split; [clear - X SL288 SHI SPT; lia| intros Y; clear - Y; lia].
+ apply (L5SAR.fframe_client L ar LB FF' 0 0 F 1 (sp - 288 + 32)); [left; reflexivity| change (ff_bytes 1) with 128; clear - X; lia].
+ apply (L5SAR.fframe_shadow_client L ar LB FF' 0 0 F 1 (sp - 288 + 32)); [left; reflexivity|]. change (ff_bytes 1) with 128.
unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - X; lia.
- destruct Wa as [X|[X|X]]; clear - X GFR SL288 SPT; lia. }
intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3. change (mrestrict H2 M3 = M3v) in VIS3.
assert (EK23f : L5SAR.ek L ar LB FF sp 32768 [] M2 M3).
{ apply (L5SAR.ek_piece L ar LB FF sp 32768 [] M2 M3 W3 FR3). intros a Ha Hc _ X. destruct X as [X|[X|X]].
- apply (NCS0 a); [clear - X; lia| exact Hc].
- destruct (APART a 1 sp 32768 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (Y & _). clear - X Y; lia.
- destruct (APART a 1 sp 32768 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (_ & Y & _). unfold SB in Y. clear - X Y; lia. }
pose proof (L5SAR.ek_trans L ar LB FF sp 32768 [] M M2 M3 EK02f EK23f) as EK03f.
pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LK2 cr Aw M3 model3 HH3) as (_ & VISs3 & _).
assert (TS3 : forall a v, sp - 288 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M3 a v).
{ intros a v Ha1 Ha2 X. rewrite <- VIS3 in X.
apply (proj1 (L5A.u64_at_vis H2 M3 a v (VISs2 a 8 ltac:(clear - Ha1 SL288 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL288 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))).
exact X. }
assert (OWN3 : PMBLPD.own sp R M3).
{ unfold PMBLPD.own. split; [apply TS3; [clear; lia| clear; lia| exact X8]|]. split; [apply TS3; [clear; lia| clear; lia| exact X16]|].
split; [apply TS3; [clear; lia| clear; lia| exact X24]|]. split; [apply TS3; [clear; lia| clear; lia| exact X32]|].
split; [apply TS3; [clear; lia| clear; lia| exact X40]|]. split; [apply TS3; [clear; lia| clear; lia| exact X48]|].
split; [apply TS3; [clear; lia| clear; lia| exact X56]|]. split; [apply TS3; [clear; lia| clear; lia| exact X64]|].
split; [apply TS3; [clear; lia| clear; lia| exact X72]|]. split; [apply TS3; [clear; lia| clear; lia| exact X80]|].
split; [apply TS3; [clear; lia| clear; lia| exact X88]|]. split; [apply TS3; [clear; lia| clear; lia| exact X96]|].
apply TS3; [clear; lia| clear; lia| exact X104]. }
assert (WAPPR : PMKB.wapp (PMSPA.W_run PMB.AD fb)).
{ unfold PMSPA.W_run, PMSPA.W_srcf, PMSPA.err_W, PMSPA.o_src, PMSPA.o_is, PMSPA.o_tb, PMSPA.o_vec, PMSPA.o_ec, PMSPA.o_p.
cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMB.AD ADDR_B].
pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
repeat apply PMKB.wapp_cons; [..| apply PMKB.wapp_nil]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia. }
set (WR := PMSPA.W_run PMB.AD fb) in *.
assert (BI3 : PMBUK.binv L ar HI M model LBX FF LK Aw sp (PMSPA.pm_scr 10) (sp - 288) (PMBLPD.own sp R) F 1 WR (PM.parser_own s) M3 model3 LK2 cr Aw).
{ change (PMSPA.pm_scr 10) with 32768. unfold PMBUK.binv. split; [exact HH3|]. split; [exact AM3|].
split; [eapply L5LZ.model_rt_trans; [exact MRT1| eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3]]|].
split; [apply incl_refl|]. split; [exact GLKI2|]. split; [exact (L5SAR.astk_grows ar M2 M3 sp 32768 ASTK2 MGM3)|].
split; [apply (L5SAR.ek_W L ar LBX FF sp 32768 WR [] M M3 (PMKB.ek_sublb L ar LB LBX FF sp 32768 [] M M3 INCX EK03f)); intros a _ r0 []|].
split; [apply (L5SAR.dk_trans L ar LBX FF sp 32768 M M2 M3 DK02); apply L5SAR.dk_grows; exact MGM3|].
split; [exact OWN3|].
change (ff_bytes 1 / 8) with 16. apply (L5.defined_grows M2 M3 _ _ MGM3).
apply (proj1 (L5A.defined_vis H2 M2 (F / 8 + SB) 16 VSH)). intros i Hi. pose proof (FSHZ i Hi) as Z0. unfold MV2 in Z0. rewrite Z0. discriminate. }
assert (PA3 : PM.parser_at RSEGS PMB.AD PMSPA.accA PMSPA.annA M3 op ois s).
{ apply (PMKB.parser_keepA RSEGS PMB.AD L ar LB FF sp 32768 [] M M3 EK03f PMKB.wapp_nil FRB BRB _ _ _ AOP); [| intros i _ r0 []| intros i _ r0 []| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact PA].
unfold LB. apply incl_appl, incl_refl. }
assert (IA3 : PM.iss_at RSEGS PMB.AD PMSPA.accA M3 ois str sm).
{ apply (PMKB.iss_keepA RSEGS PMB.AD L ar LB FF sp 32768 [] M M3 EK03f PMKB.wapp_nil FRB BRB ois str sm (AOF ois 272 ltac:(clear - Eois; lia) ltac:(clear - Eois; lia)));
[| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA].
unfold LB. apply incl_appr. exact INCS. }
assert (VIS3' : PMSPA.visitor_at RSEGS PMB.AD M3 ov).
{ apply (PMKB.visitor_keepA RSEGS PMB.AD L ar LB FF sp 32768 [] M M3 EK03f PMKB.wapp_nil FRB ov AOV); [intros i _ r0 []| exact VIS]. }
assert (VREF3 : L5.u64_at RSEGS M3 (op + 384) ov).
{ apply (PMKB.u64_keepA RSEGS L ar LB FF sp 32768 [] M M3 EK03f PMKB.wapp_nil FRB (op + 384) ov (AOF (op + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [intros i _ r0 []| exact VREF]. }
assert (BASE3 : PMSTA.base_okA RSEGS PMB.AD M3) by (apply (PMBSK.base_keep L ar C LY LB FF sp 32768 [] M M3 EK03f); [intros a _ r0 []| exact BASE]).
assert (ERR3 : PMSTA.err_okA RSEGS PMB.AD PMB.AAD M3 e).
{ apply (PMKB.err_okA_keep RSEGS PMB.AD PMB.AAD L ar LB FF sp 32768 [] M M3 EK03f e PMB.addrs_wf_A); [| exact ERR].
intros a D. pose proof (PMBSK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
split; [exact (PMB.ly_static L C LY a D)| intros r0 []]. }
assert (EC3 : PMSPA.ec_at RSEGS M3 oec 0 cat).
{ apply (PMKB.ec_keepA RSEGS L ar LB FF sp 32768 [] M M3 EK03f PMKB.wapp_nil FRB oec 0 cat AOE); [intros i _ r0 []| exact EC0]. }
assert (KS3' : forall x, In x [2; 3; 4; 8; 9; 19; 27]%nat -> getr R3 (reg x) = getr R2 (reg x)).
{ intros x Hx. apply KS3. revert x Hx. apply (L5K.incl_b [2; 3; 4; 8; 9; 19; 27]%nat). vm_compute. reflexivity. }
apply (KLOOP F fl LK2 M2 model2 G fx3 R3 M3 model3).
unfold PMBLPD.alinv, PMBLPD.lregs, PMBLPD.lmem. fold op oec ov.
split; [|split; [exact INV| split; [exact EC3| split; [exact BI3|]]]].
- split; [rewrite (KS3' 2%nat) by inl; exact B2R|]. split; [rewrite (KS3' 8%nat) by inl; exact B8R|]. split; [rewrite (KS3' 9%nat) by inl; exact B9R|].
split; [exact Y18|]. split; [rewrite (KS3' 19%nat) by inl; exact B19R|]. split; [exact Y20|]. split; [exact Y21|].
split; [exact Y22|]. split; [exact Y23|]. split; [exact Y24|]. split; [exact Y25|]. split; [exact Y26|]. split; [rewrite (KS3' 27%nat) by inl; exact B27R|].
split; [rewrite (KS3' 3%nat) by inl; rewrite (R2c 3%nat) by inl; apply KS1; inl|].
rewrite (KS3' 4%nat) by inl; rewrite (R2c 4%nat) by inl; apply KS1; inl.
- split; [unfold PMSPA.run_pre; split; [exact PA3|]; split; [exact IA3|]; split; [exact VIS3'|]; split; [exact VREF3|]; split; [exact BASE3|]; split; [exact ERR3| exact TBOK]|].
split.
+ unfold PMBLPD.lspill.
split; [apply TS3; [clear; lia| clear; lia| exact U264]|]. split; [apply TS3; [clear; lia| clear; lia| exact U256]|].
split; [apply TS3; [clear; lia| clear; lia| exact U248]|]. split; [apply TS3; [clear; lia| clear; lia| exact U240]|].
split; [apply TS3; [clear; lia| clear; lia| exact U232]|]. split; [apply TS3; [clear; lia| clear; lia| exact U224]|].
split; [apply TS3; [clear; lia| clear; lia| exact U216]|]. split; [apply TS3; [clear; lia| clear; lia| exact U208]|].
split; [apply TS3; [clear; lia| clear; lia| exact U200]|]. split; [apply TS3; [clear; lia| clear; lia| exact U192]|].
split; [apply TS3; [clear; lia| clear; lia| exact U184]|]. split; [apply TS3; [clear; lia| clear; lia| exact U176]|].
split; [apply TS3; [clear; lia| clear; lia| exact U168]|]. split; [apply TS3; [clear; lia| clear; lia| exact U160]|].
split; [apply TS3; [clear; lia| clear; lia| exact X152]|]. split; [apply TS3; [clear; lia| clear; lia| exact X144]|].
split; [apply TS3; [clear; lia| clear; lia| exact U136]|]. apply TS3; [clear; lia| clear; lia| exact U112].
+ split; [unfold PMSPA.src_step, PM.unread; split; [reflexivity|]; split; [reflexivity|]; split; [clear; lia|]; split; [intros X; exact X| clear; lia]|].
split; [intros X; exact X|]. unfold PMSPA.credit_keep. clear; lia.
Qed.
End WithHeap.
End PMBLPE.
