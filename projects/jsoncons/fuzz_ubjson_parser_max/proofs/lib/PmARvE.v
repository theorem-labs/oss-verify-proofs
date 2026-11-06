(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA LibIface
AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreA L5CoreSpecsA L5StepAR L5CoreBR L5ADetailHR
PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAa
PmModelFactsA PmStepA PmStep PmParStep PmParKit PmASrcKit PmAParKit PmAReset1 PmAUarK PmAUar PmARdValP1 PmARvK.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMARVE.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithHeap.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.
Definition at_disp : Prop :=
forall (E : PMARVK.rve), PMARVK.rvc L ar HI E ->
forall (fx : FPState) (Rc : bvmap 5 word) (Mc : word -> option byte) (modelc : Model) (LKc : list fframe) (crc : credit) (Ac : list (Z * Z)) (t : Z),
PMARVK.rvst L ar HI E Rc Mc modelc LKc crc Ac (PMARVK.vs0 E) (PMARVK.vsm0 E) (PMARVK.ve0 E) 0 (PMARVK.vcat E) ->
0 <= t < 256 -> getr Rc (reg 23) = Z_to_bv 64 t -> getr Rc (reg 12) = Z_to_bv 64 99 ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx Rc 0xad76c Mc modelc) (PMARVK.vK E).
Theorem rv_entry : at_disp -> PMA.read_value_spec L ar HI.
Proof.
intros DISP. unfold PMA.read_value_spec, PMSPA.read_value_spec, PMSPA.run_spec, PMSPA.run_spec_r.
intros fx R M model K LBX FF LK Aw cr sp r fb cat s str sm e HH AM K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT.
pose proof ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 8) with 28672 in *. change (28672 / 8) with 3584 in STKSH.
pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
destruct ARGS as (A10 & A11 & A13 & (t & Ht & A12)).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11.
rewrite L5K.rl12 in A12. rewrite L5K.rl13 in A13.
pose proof RPRE as (PA & IA & VIS & VREF & BASE & ERR & TBOK).
pose proof FOK as ((rs & Hfb) & Fal).
pose proof (PMAPAR.op_vis L ar C HI LY HIok _ FF LK cr Aw M model fb _ s HH FOK PA) as ((O1 & O8 & ONSH) & Zop & Z32 & Z20 & OWR & OCE & OVIS & AOP & Eop).
pose proof (PMAPAR.oec_vis L ar C HI LY HIok _ FF LK cr Aw M model fb 0 cat HH FOK EC0) as ((Q1 & Q8 & QNSH) & Zoec & QWR & QCE & QU & AOQ & Eoec).
pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF LK cr Aw M model HH BASE) as (VM0 & VM1 & VM2).
pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 28672 128 HH ASTK ltac:(lia)) as (SL128 & SH128 & SWR).
pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (_ & VISs & VIMG & _).
assert (RMS : L5.u64_at RSEGS (mrestrict (ahid Aw model) M) 1263176 1199536).
{ pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
pose proof (L5A.statics_facts L C M LYa ST) as (_ & _ & _ & RM & _).
apply (proj2 (L5A.u64_at_vis _ M 1263176 1199536 (VIMG 1263176 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact RM. }
set (op := PMSPA.o_p PMA.AD fb) in *. set (ov := PMSPA.o_v PMA.AD fb) in *. set (oec := PMSPA.o_ec PMA.AD fb) in *. set (ois := PMSPA.o_is PMA.AD fb) in *.
assert (Eois : ois = fb + 96) by reflexivity. assert (Eov : ov = fb + 432) by reflexivity.
set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
cfeed P (PMARVP1.arvA_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => t | 36%nat => op | 37%nat => ov | 38%nat => oec | _ => 0 end)) ltac:(first [assumption | unfold PMARVP1.aligned; assumption | clear - SL128 SHI SPT; lia | clear - O1; lia | clear - Q1; lia
| clear - O1 Eop Eoec; lia | clear - O1 Eop Eov; lia | clear - Ht; lia | clear - OCE SL128; lia | clear - QCE SL128; lia]).
destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T12 & T20 & T21 & T22 & T23 & T26
& C104 & C96 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8 & C128).
unfold PMSPA.cfg. cbn [pa_read_value PMA.AD ADDR_A].
apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xad5dc R1 0x5d6cc M1v (fun a => sp - 128 <= a < sp - 128 + 128) K HH AM MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
{ intros a Ha Wa. split; [|intros X; lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
set (LB := PM.parser_own s ++ LBX) in *.
assert (INCX : incl LBX LB) by (unfold LB; apply incl_appr; apply incl_refl).
assert (NCS0 : forall a, sp - 128 <= a < sp -> ~ aclient L ar LB FF sp 28672 a).
{ intros a Xa Hc. destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 28672 a HH SPT Hc) as [Y|Y].
- clear - Xa Y; lia.
- clear - Xa Y SL128; lia. }
assert (EK01f : L5SAR.ek L ar LB FF sp 28672 [] M M1).
{ apply (L5SAR.ek_piece L ar LB FF sp 28672 [] M M1 (fun a => sp - 128 <= a < sp - 128 + 128) FR1). intros a Ha Hc _ X. apply (NCS0 a); [clear - X; lia| exact Hc]. }
assert (DK01f : L5SAR.dk L ar LB FF sp 28672 M M1) by (apply L5SAR.dk_grows; exact MGM1).
pose proof (PMKA.ek_sublb L ar LB LBX FF sp 28672 [] M M1 INCX EK01f) as EK01.
pose proof (PMKA.dk_sublb L ar LB LBX FF sp 28672 M M1 INCX DK01f) as DK01.
assert (SV1 : forall a v, sp - 128 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
{ intros a v Ha1 Ha2 X. apply (proj1 (L5A.u64_at_vis H M1 a v (VISs a 8 ltac:(clear - Ha1 SL128 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL128 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))).
rewrite VIS1. exact X. }
assert (OWN1 : PMARVK.own sp R M1).
{ unfold PMARVK.own. repeat split; (apply SV1; [clear; lia| clear; lia| assumption]). }
clear C104 C96 C88 C80 C72 C64 C56 C48 C40 C32 C24 C16 C8 SV1.
assert (FRk3 : ff_room 3 FF LK) by (apply (PMAUAR.ff_room_of 8 FF LK 3 FRM); [clear; lia| cbn; tauto]).
change 0x5d6cc with (PMA.SM_PC 3).
apply (PMAUAR.uar_sm L ar C HI LY HIok 3 LBX (PM.parser_own s) FF LK cr Aw sp 28672 (sp - 128) (sp - 104) sp (PMARVK.ocell sp) (PMARVK.own sp R)
fx1 R1 M M1 model model1 K 0xad658 ltac:(cbn; tauto) HH HH1 AM1 K0 ASTK MGM1 EK01 DK01).
{ rewrite L5K.rl2. exact T2. }
{ rewrite L5K.rl4. rewrite (KS1 4%nat) by inl. rewrite <- L5K.rl4. exact Rtp. }
{ rewrite L5K.rl1. exact T1. }
{ reflexivity. }
{ clear; lia. }
{ replace (sp - 128) with (sp + (-8) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
{ clear; lia. } { clear; lia. } { clear; lia. } { clear; lia. }
{ intros a Ha. exact Ha. }
{ intros Ma Mb OW AG. apply (PMARVK.own_agree sp R Ma Mb ltac:(clear - SL128 SPT; lia) ltac:(clear - SHI SPT; lia) OW AG). }
{ exact FRk3. }
{ intros f Hf. specialize (FRS f Hf). clear - FRS; lia. }
intros R2 M2 model2 F fl LK2 G G10 RP2 AM2 MRT2 ASTK2 EK02 DK02 EK12f DK12f AGF FW FSHW FSHZ FLC FLW FDEF VF VSH VFL APART.
change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *. change (512 - 8) with 504 in *.
pose proof G as G'. destruct G' as [_ _ _ _ _ _ _ GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
pose proof (L5SAR.ek_trans L ar LB FF sp 28672 [] M M1 M2 EK01f EK12f) as EK02f.
pose proof (L5SAR.dk_trans L ar LB FF sp 28672 M M1 M2 DK01f DK12f) as DK02f.
pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
assert (AOF : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> PMSPA.aobjA FF a n).
{ intros a n X1 X2. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. lia. }
assert (PA2 : PM.parser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA M2 op ois s).
{ apply (PMKA.parser_keepA RSEGS PMA.AD L ar LB FF sp 28672 [] M M2 EK02f PMKA.wapp_nil FRB BRB _ _ _ AOP); [| intros i _ r0 []| intros i _ r0 []| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact PA].
unfold LB. apply incl_appl, incl_refl. }
assert (AOI : PMSPA.aobjA FF ois 272) by (apply AOF; clear - Eois; lia).
assert (IA2 : PM.iss_at RSEGS PMA.AD PMSPA.accA M2 ois str sm).
{ apply (PMKA.iss_keepA RSEGS PMA.AD L ar LB FF sp 28672 [] M M2 EK02f PMKA.wapp_nil FRB BRB ois str sm AOI); [| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA].
unfold LB. apply incl_appr. exact INCS. }
assert (BASE2 : PMSTA.base_okA RSEGS PMA.AD M2) by (apply (PMASK.base_keep L ar C LY LB FF sp 28672 [] M M2 EK02f); [intros a _ r0 []| exact BASE]).
assert (VIS2 : PMSPA.visitor_at RSEGS PMA.AD M2 ov).
{ apply (PMKA.visitor_keepA RSEGS PMA.AD L ar LB FF sp 28672 [] M M2 EK02f PMKA.wapp_nil FRB ov (AOF ov 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia))); [intros i _ r0 []| exact VIS]. }
assert (VREF2 : L5.u64_at RSEGS M2 (op + 384) ov).
{ apply (PMKA.u64_keepA RSEGS L ar LB FF sp 28672 [] M M2 EK02f PMKA.wapp_nil FRB (op + 384) ov (AOF (op + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [intros i _ r0 []| exact VREF]. }
assert (ERR2 : PMSTA.err_okA RSEGS PMA.AD PMA.AAD M2 e).
{ apply (PMKA.err_okA_keep RSEGS PMA.AD PMA.AAD L ar LB FF sp 28672 [] M M2 EK02f e PMA.addrs_wf_A); [| exact ERR].
intros a D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
split; [exact (PMA.ly_static L C LY a D)| intros r0 []]. }
assert (EC2 : PMSPA.ec_at RSEGS M2 oec 0 cat).
{ apply (PMKA.ec_keepA RSEGS L ar LB FF sp 28672 [] M M2 EK02f PMKA.wapp_nil FRB oec 0 cat AOQ); [intros i _ r0 []| exact EC0]. }
assert (HH2 : ri_inv HI LB ((F, 3, sp - 128 + 32) :: FF) LK2 cr Aw M2 (vml_of model2)) by exact GHH2.
set (FF' := (F, 3, sp - 128 + 32) :: FF) in *.
assert (FOK' : PMSPA.frame_okA FF' fb) by exact (PMAUAR.frame_okA_push FF fb F 3 (sp - 128 + 32) FOK).
pose proof (PMAPAR.op_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 fb _ s HH2 FOK' PA2) as ((_ & _ & _) & Zop2 & Z322 & Z202 & OWR2 & _ & OVIS2 & _ & _).
pose proof (PMAPAR.oec_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 fb 0 cat HH2 FOK' EC2) as ((_ & _ & _) & Zoec2 & QWR2 & _ & QU2 & _ & _).
set (H2 := ahid Aw model2) in *. set (MV2 := mrestrict H2 M2) in *.
pose proof (PMASK.mach_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 HH2 BASE2) as (W0 & W1 & W2).
pose proof (PMASK.stk_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 sp 28672 128 HH2 ASTK2 ltac:(lia)) as (_ & _ & SWR2).
pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LK2 cr Aw M2 model2 HH2) as (_ & VISs2 & VIMG2 & _).
assert (RMS2 : L5.u64_at RSEGS MV2 1263176 1199536).
{ pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
pose proof (L5A.statics_facts L C M2 LYa ST) as (_ & _ & _ & RM & _).
apply (proj2 (L5A.u64_at_vis _ M2 1263176 1199536 (VIMG2 1263176 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact RM. }
assert (OWN2 : PMARVK.own sp R M2).
{ apply (PMARVK.own_agree sp R M1 M2 ltac:(clear - SL128 SPT; lia) ltac:(clear - SHI SPT; lia) OWN1). intros a Ha. unfold PMARVK.ocell in Ha. apply AGF. clear - Ha; lia. }
assert (SVV : forall a v, sp - 128 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M2 a v -> L5.u64_at RSEGS MV2 a v).
{ intros a v Ha1 Ha2 X. apply (proj2 (L5A.u64_at_vis H2 M2 a v (VISs2 a 8 ltac:(clear - Ha1 SL128 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL128 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))). exact X. }
pose proof OWN2 as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96 & S104).
apply SVV in S8; [|clear; lia|clear; lia]. apply SVV in S16; [|clear; lia|clear; lia]. apply SVV in S24; [|clear; lia|clear; lia]. apply SVV in S32; [|clear; lia|clear; lia].
apply SVV in S40; [|clear; lia|clear; lia]. apply SVV in S48; [|clear; lia|clear; lia]. apply SVV in S56; [|clear; lia|clear; lia]. apply SVV in S64; [|clear; lia|clear; lia].
apply SVV in S72; [|clear; lia|clear; lia]. apply SVV in S80; [|clear; lia|clear; lia]. apply SVV in S88; [|clear; lia|clear; lia]. apply SVV in S96; [|clear; lia|clear; lia].
apply SVV in S104; [|clear; lia|clear; lia].
assert (CLfb : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> 0 < n -> forall i, 0 <= i < n -> aclient L ar LB FF 0 0 (a + i)).
{ intros a n X1 X2 X3 i Hi. unfold aclient, aclient_g. do 3 right; left. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
change (ff_bytes 4) with 1024. split; [clear - X1 X2 Hi; lia| intros Y; clear - X1 X2 Hi Y; lia]. }
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
assert (SHoec : oec / 8 + SB = fb / 8 + SB + 124).
{ rewrite Eoec. pose proof (Z.div_mod fb 1024 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
replace (1024 * (fb / 1024) + 992) with ((128 * (fb / 1024) + 124) * 8) by (clear; lia). rewrite Z.div_mul by lia.
replace (1024 * (fb / 1024)) with ((128 * (fb / 1024)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
destruct (APART op 384 0 0 (CLfb op 384 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (ApF & ApSF & ApFL).
destruct (APART oec 16 0 0 (CLfb oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (AqF & AqSF & AqFL).
destruct (APART (op / 8 + SB) 48 0 0 (CLsh (op / 8 + SB) 48 ltac:(clear - SHop; lia) ltac:(clear - SHop; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (_ & AsopSF & _).
destruct (APART (oec / 8 + SB) 2 0 0 (CLsh (oec / 8 + SB) 2 ltac:(clear - SHoec; lia) ltac:(clear - SHoec; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (_ & AsqSF & _).
pose proof (PMAPAR.ov_vis L ar C HI LY HIok _ FF LK cr Aw M model fb HH FOK VIS) as ((V1 & V8 & VNSH) & _ & _ & VCE & _ & AOV & _).
destruct (APART ov 8 0 0 (CLfb ov 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (AvF & AvSF & AvFL).
assert (SHov : ov / 8 + SB = fb / 8 + SB + 54).
{ rewrite Eov. pose proof (Z.div_mod fb 1024 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
replace (1024 * (fb / 1024) + 432) with ((128 * (fb / 1024) + 54) * 8) by (clear; lia). rewrite Z.div_mul by lia.
replace (1024 * (fb / 1024)) with ((128 * (fb / 1024)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
destruct (APART (ov / 8 + SB) 1 0 0 (CLsh (ov / 8 + SB) 1 ltac:(clear - SHov; lia) ltac:(clear - SHov; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (_ & AsvSF & _).
unfold SB in AsopSF, AsqSF, ApSF, AqSF, AsvSF.
assert (R2c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (reg j) = getr R1 (reg j)).
{ intros j Hj. apply (L5SAR.cs_of_preserved R1 R2 j RP2 Hj). }
assert (B2R : getr R2 (reg 2) = Z_to_bv 64 (sp - 128)) by (rewrite (R2c 2%nat) by inl; exact T2).
assert (B8R : getr R2 (reg 8) = Z_to_bv 64 sp) by (rewrite (R2c 8%nat) by inl; exact T8).
assert (B9R : getr R2 (reg 9) = Z_to_bv 64 (sp - 128)) by (rewrite (R2c 9%nat) by inl; exact T9).
assert (B20R : getr R2 (reg 20) = Z_to_bv 64 op) by (rewrite (R2c 20%nat) by inl; exact T20).
assert (B21R : getr R2 (reg 21) = Z_to_bv 64 oec) by (rewrite (R2c 21%nat) by inl; exact T21).
assert (B22R : getr R2 (reg 22) = Z_to_bv 64 ov) by (rewrite (R2c 22%nat) by inl; exact T22).
assert (B23R : getr R2 (reg 23) = Z_to_bv 64 t) by (rewrite (R2c 23%nat) by inl; exact T23).
assert (B26R : getr R2 (reg 26) = Z_to_bv 64 2147450880) by (rewrite (R2c 26%nat) by inl; exact T26).
assert (B10R : getr R2 (reg 10) = Z_to_bv 64 F) by (rewrite <- L5K.rl10; exact G10).
assert (FLCv : L5.u64_at RSEGS MV2 (F + 504) fl) by (replace (F + 504) with (F + 512 - 8) by (clear; lia); exact FLC).
pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8.
pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18.
pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19. pose proof (bv_unsigned_in_range 64 (getr R (reg 20))) as B20.
pose proof (bv_unsigned_in_range 64 (getr R (reg 21))) as B21. pose proof (bv_unsigned_in_range 64 (getr R (reg 22))) as B22.
pose proof (bv_unsigned_in_range 64 (getr R (reg 23))) as B23. pose proof (bv_unsigned_in_range 64 (getr R (reg 24))) as B24.
pose proof (bv_unsigned_in_range 64 (getr R (reg 25))) as B25. pose proof (bv_unsigned_in_range 64 (getr R (reg 26))) as B26.
pose proof (bv_unsigned_in_range 64 (getr R (reg 27))) as B27. change (bv_modulus 64) with (2 ^ 64) in *.
assert (Q0 : 0 <= sp < 2 ^ 64 /\ 0 <= op < 2 ^ 64 /\ 0 <= ov < 2 ^ 64 /\ 0 <= oec < 2 ^ 64 /\ 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64 /\ 0 <= t < 2 ^ 64)
by (clear - SL128 SHI SPT O1 Eop Eov Eoec GFR GFLR Ht; lia).
destruct Q0 as (Q0a & Q0b & Q0c & Q0d & Q0f & Q0g & Q0h).
assert (Y1 : 140735332487296 <= sp <= 140737488355328) by (clear - SL128 SHI SPT; lia).
assert (Y2 : (sp - 128) + 128 <= op \/ op + 384 <= (sp - 128)) by (clear - OCE SL128; lia).
assert (Y2b : (sp - 128) + 128 <= oec \/ oec + 16 <= (sp - 128)) by (clear - QCE SL128; lia).
assert (Y3 : 6885376 <= F <= 140737488354816) by (clear - GFR; lia).
assert (Y4 : (sp - 128) + 128 <= F \/ F + 512 <= (sp - 128)) by (clear - GFCEIL SL128; lia).
assert (Y5 : (sp - 128) + 128 <= fl \/ fl + 1 <= (sp - 128)) by (clear - GFLR SL128; lia).
assert (Y7 : 4096 <= fl <= 140737488355327) by (clear - GFLR; lia).
assert (Y8 : F + 512 <= 65536 \/ 65536 + 1196032 <= F) by (clear - GFR; lia).
assert (Y9 : ((F / 8) + 2147450880) + 64 <= 1263176 \/ 1263176 + 8 <= ((F / 8) + 2147450880)).
{ clear - GFR GF8. right. assert (F / 8 >= 844264) by (apply Z.le_ge; apply Z.div_le_lower_bound; lia). lia. }
assert (Y10 : op + 384 <= oec \/ oec + 16 <= op) by (clear - Eop Eoec; lia).
assert (Y11 : (op + 384 <= F \/ F + 512 <= op)) by exact ApF.
assert (Y12 : (op + 384 <= fl \/ fl + 1 <= op)) by exact ApFL.
assert (Y13 : (((op / 8) + 2147450880) + 48 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 64 <= ((op / 8) + 2147450880))) by exact AsopSF.
assert (Y14 : (oec + 16 <= F \/ F + 512 <= oec)) by exact AqF.
assert (Y15 : (oec + 16 <= fl \/ fl + 1 <= oec)) by exact AqFL.
assert (Y16 : (((oec / 8) + 2147450880) + 2 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 64 <= ((oec / 8) + 2147450880))) by exact AsqSF.
cfeed P (PMARVP1.arvB_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 33%nat => t | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl
| 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9))
| 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20))
| 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23))
| 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26))
| 76%nat => bv_unsigned (getr R (reg 27)) | _ => 0 end)) ltac:(first [assumption | unfold PMARVP1.aligned; assumption | clear - Y1 ; lia]).
destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & X10 & X11 & X12 & X13 & X14 & X18 & X19 & X27 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H16 & H8 & H0 & S112 & DEF24 & Z24 & T8v & T16v & T24v & T32v & T40v & T48v & T56v & T64v & T72v & T80v & T88v & T96v & T104v).
set (W3 := fun a => (sp - 128 <= a < sp - 128 + 128) \/ (F <= a < F + 24) \/ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 64)).
apply (L5SAR.apiece L ar C HI LYa HIok LB FF' LK2 cr Aw M2 model2 fx1 fx3 R2 0xad658 R3 0xad76c M3v W3 K HH2 AM2 MS3 MG3).
{ intros a Ha Hn. apply FRZ3; [exact Ha| intros X; apply Hn; left; exact X| intros X; apply Hn; right; left; clear - X; lia| intros X; apply Hn; right; right; clear - X; lia]. }
{ intros a Ha Wa. split.
- destruct Wa as [X|[X|X]].
+ unfold aclientw, aclient_g. right; left. split; [clear - X SL128 SHI SPT; lia| intros Y; clear - Y; lia].
+ apply (L5SAR.fframe_client L ar LB FF' 0 0 F 3 (sp - 128 + 32)); [left; reflexivity| change (ff_bytes 3) with 512; clear - X; lia].
+ apply (L5SAR.fframe_shadow_client L ar LB FF' 0 0 F 3 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 3) with 512.
unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - X; lia.
- destruct Wa as [X|[X|X]]; clear - X GFR SL128 SPT; lia. }
intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3. change (mrestrict H2 M3 = M3v) in VIS3.
assert (EK23f : L5SAR.ek L ar LB FF sp 28672 [] M2 M3).
{ apply (L5SAR.ek_piece L ar LB FF sp 28672 [] M2 M3 W3 FR3). intros a Ha Hc _ X. destruct X as [X|[X|X]].
- apply (NCS0 a); [clear - X; lia| exact Hc].
- destruct (APART a 1 sp 28672 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (Y & _). clear - X Y; lia.
- destruct (APART a 1 sp 28672 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (_ & Y & _). unfold SB in Y. clear - X Y; lia. }
pose proof (L5SAR.ek_trans L ar LB FF sp 28672 [] M M2 M3 EK02f EK23f) as EK03f.
assert (SV3 : forall a v, sp - 128 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M3 a v).
{ intros a v Ha1 Ha2 X. apply (proj1 (L5A.u64_at_vis H2 M3 a v (VISs2 a 8 ltac:(clear - Ha1 SL128 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL128 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))).
rewrite VIS3. exact X. }
assert (OWN3 : PMARVK.own sp R M3).
{ unfold PMARVK.own. repeat split; (apply SV3; [clear; lia| clear; lia| assumption]). }
assert (WAPPR : PMKA.wapp (PMSPA.W_run PMA.AD fb)).
{ pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 4) with 1024 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, F1, F2.
unfold PMSPA.W_run, PMSPA.W_srcf, PMSPA.err_W, PMSPA.o_src, PMSPA.o_is, PMSPA.o_tb, PMSPA.o_vec, PMSPA.o_ec, PMSPA.o_p.
cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMA.AD ADDR_A].
pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
repeat apply PMKA.wapp_cons; [..| apply PMKA.wapp_nil]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia. }
assert (BI3 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 28672 (sp - 128) (PMARVK.own sp R) F 3 (PMSPA.W_run PMA.AD fb) (PM.parser_own s) M3 model3 LK2 cr Aw).
{ unfold PMAUK.binv. split; [exact HH3|]. split; [exact AM3|].
split; [eapply L5LZ.model_rt_trans; [exact MRT1| eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3]]|].
split; [apply incl_refl|]. split; [exact GLKI2|]. split; [exact (L5SAR.astk_grows ar M2 M3 sp 28672 ASTK2 MGM3)|].
split; [apply (L5SAR.ek_W L ar LBX FF sp 28672 (PMSPA.W_run PMA.AD fb) [] M M3 (PMKA.ek_sublb L ar LB LBX FF sp 28672 [] M M3 INCX EK03f)); intros a _ r0 []|].
split; [apply (L5SAR.dk_trans L ar LBX FF sp 28672 M M2 M3 DK02); apply L5SAR.dk_grows; exact MGM3|].
split; [exact OWN3|].
change (ff_bytes 3 / 8) with 64. apply (L5.defined_grows M2 M3 _ _ MGM3).
apply (proj1 (L5A.defined_vis H2 M2 (F / 8 + SB) 64 VSH)). intros i Hi. pose proof (FSHZ i Hi) as Z0. unfold MV2 in Z0. rewrite Z0. discriminate. }
assert (PA3 : PM.parser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA M3 op ois s).
{ apply (PMKA.parser_keepA RSEGS PMA.AD L ar LB FF sp 28672 [] M M3 EK03f PMKA.wapp_nil FRB BRB _ _ _ AOP); [| intros i _ r0 []| intros i _ r0 []| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact PA].
unfold LB. apply incl_appl, incl_refl. }
assert (IA3 : PM.iss_at RSEGS PMA.AD PMSPA.accA M3 ois str sm).
{ apply (PMKA.iss_keepA RSEGS PMA.AD L ar LB FF sp 28672 [] M M3 EK03f PMKA.wapp_nil FRB BRB ois str sm AOI); [| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA].
unfold LB. apply incl_appr. exact INCS. }
assert (BASE3 : PMSTA.base_okA RSEGS PMA.AD M3) by (apply (PMASK.base_keep L ar C LY LB FF sp 28672 [] M M3 EK03f); [intros a _ r0 []| exact BASE]).
assert (VIS3o : PMSPA.visitor_at RSEGS PMA.AD M3 ov).
{ apply (PMKA.visitor_keepA RSEGS PMA.AD L ar LB FF sp 28672 [] M M3 EK03f PMKA.wapp_nil FRB ov (AOF ov 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia))); [intros i _ r0 []| exact VIS]. }
assert (VREF3 : L5.u64_at RSEGS M3 (op + 384) ov).
{ apply (PMKA.u64_keepA RSEGS L ar LB FF sp 28672 [] M M3 EK03f PMKA.wapp_nil FRB (op + 384) ov (AOF (op + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [intros i _ r0 []| exact VREF]. }
assert (ERR3 : PMSTA.err_okA RSEGS PMA.AD PMA.AAD M3 e).
{ apply (PMKA.err_okA_keep RSEGS PMA.AD PMA.AAD L ar LB FF sp 28672 [] M M3 EK03f e PMA.addrs_wf_A); [| exact ERR].
intros a D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
split; [exact (PMA.ly_static L C LY a D)| intros r0 []]. }
assert (EC3 : PMSPA.ec_at RSEGS M3 oec 0 cat).
{ apply (PMKA.ec_keepA RSEGS L ar LB FF sp 28672 [] M M3 EK03f PMKA.wapp_nil FRB oec 0 cat AOQ); [intros i _ r0 []| exact EC0]. }
set (E := PMARVK.RVE R r sp fb cat s str sm e LBX FF LK Aw cr model M K F fl LK2 M2 model2).
assert (XAR : PMARVK.rvar E).
{ unfold PMARVK.rvar, PMARVK.op, PMARVK.oec, PMARVK.ov. cbn [PMARVK.vsp PMARVK.vF PMARVK.vfl PMARVK.vfb E]. fold op oec ov.
assert (Yv1 : (sp - 128) + 128 <= ov \/ ov + 8 <= (sp - 128)) by (clear - VCE SL128; lia).
assert (Yv2 : op + 384 <= ov \/ ov + 8 <= op) by (clear - Eop Eov; lia).
assert (Yv3 : oec + 16 <= ov \/ ov + 8 <= oec) by (clear - Eoec Eov; lia).
assert (Yv4 : F + 512 <= ov \/ ov + 8 <= F) by (clear - AvF; lia).
assert (Yv5 : fl + 1 <= ov \/ ov + 8 <= fl) by (clear - AvFL; lia).
assert (Yv6 : ((F / 8) + 2147450880) + 64 <= 2147604776 \/ 2147604776 + 16 <= ((F / 8) + 2147450880)).
{ clear - GFR. right. assert (F / 8 >= 844368) by (apply Z.le_ge; apply Z.div_le_lower_bound; lia). lia. }
assert (Yv7 : ((F / 8) + 2147450880) + 64 <= ((ov / 8) + 2147450880) \/ ((ov / 8) + 2147450880) + 1 <= ((F / 8) + 2147450880)) by (clear - AsvSF; lia).
assert (Yv8 : 6885376 <= ov <= 140737488355320) by (clear - V1; lia).
assert (YF1 : 2147446784 + 17592186048512 <= F \/ F + 512 <= 2147446784) by (clear - GFBIG; lia).
assert (YF2 : 2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784) by (clear - GFLBIG; lia).
assert (YF3 : F + 512 <= fl \/ fl + 1 <= F) by (clear - GFLA; lia).
repeat split; first [ assumption | exact GF32 | (clear - Y1; lia) | (clear - O1; lia) | (clear - Q1; lia) | (clear - Y3; lia) | (clear - Y7; lia) | (clear - V1; lia) ]. }
assert (XC : PMARVK.rvc L ar HI E).
{ constructor; [exact XAR|..]; cbn [PMARVK.vR PMARVK.vr PMARVK.vsp PMARVK.vfb PMARVK.vcat PMARVK.vs0 PMARVK.vstr PMARVK.vsm0 PMARVK.ve0 PMARVK.vLBX PMARVK.vFF PMARVK.vLK
PMARVK.vAw PMARVK.vcr PMARVK.vmodel PMARVK.vM PMARVK.vK PMARVK.vF PMARVK.vfl PMARVK.vLK2 PMARVK.vM2 PMARVK.vmodel2 E]; unfold PMARVK.SCR;
first [ exact G | exact HH | exact K0 | exact Rra | exact RAok | exact Rsp | exact Rgp | exact Rtp | exact ASTK | exact STKSH | exact FRM | exact FRS
| exact FOK | exact SP32 | exact INCS | exact UNR | exact CRED | exact INV | idtac ].
unfold PMARVK.kont. exact KONT. }
apply (DISP E XC fx3 R3 M3 model3 LK2 cr Aw t).
- unfold PMARVK.rvst. cbn [PMARVK.vR PMARVK.vr PMARVK.vsp PMARVK.vfb PMARVK.vcat PMARVK.vs0 PMARVK.vstr PMARVK.vsm0 PMARVK.ve0 PMARVK.vLBX PMARVK.vFF PMARVK.vLK
PMARVK.vAw PMARVK.vcr PMARVK.vmodel PMARVK.vM PMARVK.vK PMARVK.vF PMARVK.vfl PMARVK.vLK2 PMARVK.vM2 PMARVK.vmodel2 E].
unfold PMARVK.WR, PMARVK.SCR. split; [exact BI3|].
split.
{ unfold PMARVK.mid, PMARVK.op, PMARVK.oec, PMARVK.ov. cbn [PMARVK.vR PMARVK.vsp PMARVK.vfb PMARVK.vF E]. fold op oec ov.
split; [rewrite (KS3 2%nat) by inl; exact B2R|]. split; [rewrite (KS3 8%nat) by inl; exact B8R|]. split; [rewrite (KS3 9%nat) by inl; exact B9R|].
split; [exact X18|]. split; [exact X19|]. split; [rewrite (KS3 20%nat) by inl; exact B20R|]. split; [rewrite (KS3 21%nat) by inl; exact B21R|].
split; [rewrite (KS3 22%nat) by inl; exact B22R|]. split; [rewrite (KS3 26%nat) by inl; exact B26R|]. split; [exact X27|].
split; [rewrite (KS3 3%nat) by inl; rewrite (R2c 3%nat) by inl; apply KS1; inl|].
rewrite (KS3 4%nat) by inl; rewrite (R2c 4%nat) by inl; apply KS1; inl. }
split; [unfold PMSPA.run_pre; fold op ois ov; split; [exact PA3|]; split; [exact IA3|]; split; [exact VIS3o|]; split; [exact VREF3|]; split; [exact BASE3|];
split; [exact ERR3| exact TBOK]|].
split; [unfold PMSPA.src_step; split; [reflexivity|]; split; [reflexivity|]; split; [clear; lia|]; split; [intros X; exact X| clear; lia]|].
split; [intros X; exact X|].
split; [unfold PMSPA.credit_keep; clear; lia|].
unfold PMARVK.oec. exact EC3.
- exact Ht.
- rewrite (KS3 23%nat) by inl. exact B23R.
- exact X12.
Qed.
End WithHeap.
End SCFG_1.
End PMARVE.
