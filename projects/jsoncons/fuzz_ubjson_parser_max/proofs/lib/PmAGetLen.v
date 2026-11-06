(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA LibIface AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreA L5CoreSpecsA L5StepAR L5CoreBR L5ADetailHR PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAa PmModelFactsA PmStepA PmStep PmParStep PmParKit PmASrcKit PmAParKit PmAReset1 PmAUarK PmAUar PmAGlP1 PmAGlP2 PmAGlP3 PmAGlP4 PmAGlP5 PmAGetLenK.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia.
Module PMAGLN.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Import PMAGLK.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.
Theorem get_length_ok : PMA.src_read_spec L ar HI -> PMA.make_ec_spec L ar HI -> PMA.get_length_spec L ar HI.
Proof.
intros SR MKE. unfold PMA.get_length_spec, PMSPA.get_length_spec, PMSPA.run_spec_rd.
intros d Hd fx R M model K LBX FF LK Aw cr sp r fb cat s str sm e HH AM K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 5) with 22528 in *. change (22528 / 8) with 2816 in STKSH.
pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
destruct ARGS as (A10 & A11).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11.
pose proof RPRE as (PA & IA & VIS & VREF & BASE & ERR & TBOK).
pose proof FOK as ((rs & Hfb) & Fal).
pose proof (PMAPAR.op_vis L ar C HI LY HIok _ FF LK cr Aw M model fb _ s HH FOK PA) as ((O1 & O8 & ONSH) & Zop & Z32 & Z20 & OWR & OCE & OVIS & AOP & Eop).
pose proof (PMASK.iss_vis L ar C HI LY HIok _ FF LK cr Aw M model fb str sm sp 22528 HH FOK IA ASTK) as ((I1 & I8 & INSH) & Zis & IWR & ICE & IVIS & AOI & IOS).
pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF LK cr Aw M model HH BASE) as (VM0 & VM1 & VM2).
pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 22528 128 HH ASTK ltac:(lia)) as (SL128 & SH128 & SWR).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & STOP & _).
pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 4) with 1024 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, F1, F2.
set (op := PMSPA.o_p PMA.AD fb) in *. set (ov := PMSPA.o_v PMA.AD fb) in *. set (oec := PMSPA.o_ec PMA.AD fb) in *. set (ois := PMSPA.o_is PMA.AD fb) in *.
assert (Eoec : oec = fb + 992) by reflexivity. assert (Eois : ois = fb + 96) by reflexivity. assert (Eov : ov = fb + 432) by reflexivity.
assert (FB0 : 6885376 <= fb) by (clear - O1 Eop Fal; lia).
set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
assert (AOF : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> PMSPA.aobjA FF a n).
{ intros a n X1 X2. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. lia. }
pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (_ & VISs & _).
cfeed P (PMAGL1.aglA_conc fx R MV (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | _ => 0 end)) ltac:(first [assumption | unfold PMAGL1.aligned; assumption | clear - SL128 SHI SPT; lia | clear - O1; lia | clear - O1 Eop Eoec; lia]).
destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & _ & _ & T19 & T20 & T26
& C96 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8 & C128).
unfold PMSPA.cfg. cbn [pa_get_length PMA.AD ADDR_A].
apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xafe2c R1 0x5d530 M1v (fun a => sp - 128 <= a < sp - 128 + 128) K HH AM MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
{ intros a Ha Wa. split; [|intros X; lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
set (LB := PM.parser_own s ++ LBX) in *.
assert (INCX : incl LBX LB) by (unfold LB; apply incl_appr; apply incl_refl).
assert (NCS0 : forall a, sp - 128 <= a < sp -> ~ aclient L ar LB FF sp 22528 a).
{ intros a Xa Hc. destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 22528 a HH SPT Hc) as [Y|Y].
- clear - Xa Y; lia.
- clear - Xa Y SL128; lia. }
assert (EK01f : L5SAR.ek L ar LB FF sp 22528 [] M M1).
{ apply (L5SAR.ek_piece L ar LB FF sp 22528 [] M M1 (fun a => sp - 128 <= a < sp - 128 + 128) FR1). intros a Ha Hc _ X. apply (NCS0 a); [clear - X; lia| exact Hc]. }
assert (DK01f : L5SAR.dk L ar LB FF sp 22528 M M1) by (apply L5SAR.dk_grows; exact MGM1).
pose proof (PMKA.ek_sublb L ar LB LBX FF sp 22528 [] M M1 INCX EK01f) as EK01.
pose proof (PMKA.dk_sublb L ar LB LBX FF sp 22528 M M1 INCX DK01f) as DK01.
assert (SV1 : forall a v, sp - 128 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
{ intros a v Ha1 Ha2 X. apply (proj1 (L5A.u64_at_vis H M1 a v (VISs a 8 ltac:(clear - Ha1 SL128 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL128 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))).
rewrite VIS1. exact X. }
assert (OWN1 : own sp R M1).
{ unfold own. split; [apply SV1; [clear; lia| clear; lia| exact C8]|]. split; [apply SV1; [clear; lia| clear; lia| exact C16]|].
split; [apply SV1; [clear; lia| clear; lia| exact C24]|]. split; [apply SV1; [clear; lia| clear; lia| exact C32]|].
split; [apply SV1; [clear; lia| clear; lia| exact C40]|]. split; [apply SV1; [clear; lia| clear; lia| exact C48]|].
split; [apply SV1; [clear; lia| clear; lia| exact C56]|]. split; [apply SV1; [clear; lia| clear; lia| exact C64]|].
split; [apply SV1; [clear; lia| clear; lia| exact C72]|]. split; [apply SV1; [clear; lia| clear; lia| exact C80]|].
split; [apply SV1; [clear; lia| clear; lia| exact C88]|]. apply SV1; [clear; lia| clear; lia| exact C96]. }
clear C96 C88 C80 C72 C64 C56 C48 C40 C32 C24 C16 C8 C128 SV1.
assert (FRk2 : ff_room 2 FF LK) by (apply (PMAUAR.ff_room_of 5 FF LK 2 FRM); [clear; lia| right; right; left; reflexivity]).
change 0x5d530 with (PMA.SM_PC 2).
apply (PMAUAR.uar_sm L ar C HI LY HIok 2 LBX (PM.parser_own s) FF LK cr Aw sp 22528 (sp - 128) (sp - 96) sp (ocell sp) (own sp R)
fx1 R1 M M1 model model1 K 0xafe9c ltac:(right; right; left; reflexivity) HH HH1 AM1 K0 ASTK MGM1 EK01 DK01).
{ rewrite L5K.rl2. exact T2. }
{ rewrite L5K.rl4. rewrite (KS1 4%nat) by inl. rewrite <- L5K.rl4. exact Rtp. }
{ rewrite L5K.rl1. exact T1. }
{ reflexivity. }
{ clear; lia. }
{ replace (sp - 128) with (sp + (-8) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
{ clear; lia. } { clear; lia. } { clear; lia. } { clear; lia. }
{ intros a Ha. exact Ha. }
{ intros Ma Mb OW AG. apply (own_agree sp R Ma Mb ltac:(clear - SL128 SPT; lia) ltac:(clear - SHI SPT; lia) OW AG). }
{ exact FRk2. }
{ intros f Hf. specialize (FRS f Hf). clear - FRS; lia. }
intros R2 M2 model2 F fl LK2 G G10 RP2 AM2 MRT2 ASTK2 EK02 DK02 EK12f DK12f AGF FW FSHW FSHZ FLC FLW FDEF VF VSH VFL APART.
change (ff_bytes 2) with 256 in *. change (256 / 8) with 32 in *.
pose proof G as G'. destruct G' as [_ _ _ _ _ _ _ GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
change (ff_bytes 2) with 256 in *. change (256 / 8) with 32 in *.
pose proof (L5SAR.ek_trans L ar LB FF sp 22528 [] M M1 M2 EK01f EK12f) as EK02f.
pose proof (L5SAR.dk_trans L ar LB FF sp 22528 M M1 M2 DK01f DK12f) as DK02f.
pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
assert (HH2 : ri_inv HI LB ((F, 2, sp - 128 + 32) :: FF) LK2 cr Aw M2 (vml_of model2)) by exact GHH2.
set (FF' := (F, 2, sp - 128 + 32) :: FF) in *.
assert (FOK' : PMSPA.frame_okA FF' fb) by exact (PMAUAR.frame_okA_push FF fb F 2 (sp - 128 + 32) FOK).
set (H2 := ahid Aw model2) in *. set (MV2 := mrestrict H2 M2) in *.
pose proof (PMASK.stk_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 sp 22528 128 HH2 ASTK2 ltac:(lia)) as (_ & _ & SWR2).
assert (R2c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (reg j) = getr R1 (reg j)).
{ intros j Hj. apply (L5SAR.cs_of_preserved R1 R2 j RP2 Hj). }
assert (B2R : getr R2 (reg 2) = Z_to_bv 64 (sp - 128)) by (rewrite (R2c 2%nat) by inl; exact T2).
assert (B8R : getr R2 (reg 8) = Z_to_bv 64 sp) by (rewrite (R2c 8%nat) by inl; exact T8).
assert (B9R : getr R2 (reg 9) = Z_to_bv 64 (sp - 128)) by (rewrite (R2c 9%nat) by inl; exact T9).
assert (B19R : getr R2 (reg 19) = Z_to_bv 64 op) by (rewrite (R2c 19%nat) by inl; exact T19).
assert (B20R : getr R2 (reg 20) = Z_to_bv 64 oec) by (rewrite (R2c 20%nat) by inl; exact T20).
assert (B26R : getr R2 (reg 26) = Z_to_bv 64 2147450880) by (rewrite (R2c 26%nat) by inl; exact T26).
assert (B10R : getr R2 (reg 10) = Z_to_bv 64 F) by (rewrite <- L5K.rl10; exact G10).
assert (FLCv : L5.u64_at RSEGS MV2 (F + 248) fl) by (replace (F + 248) with (F + 256 - 8) by (clear; lia); exact FLC).
assert (Q0 : 0 <= sp < 2 ^ 64 /\ 0 <= op < 2 ^ 64 /\ 0 <= ov < 2 ^ 64 /\ 0 <= oec < 2 ^ 64 /\ 0 <= ois < 2 ^ 64 /\ 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64)
by (clear - SL128 SHI SPT O1 Eop Eov Eoec Eois GFR GFLR; lia).
destruct Q0 as (Q0a & Q0b & Q0c & Q0d & Q0e & Q0f & Q0g).
assert (Q1 : 140735332487296 <= sp <= 140737488355328) by (clear - SL128 SHI SPT; lia).
assert (Q3 : 6885376 <= F <= 140737488355072) by (clear - GFR; lia).
assert (Q4 : (sp - 128) + 128 <= F \/ F + 256 <= (sp - 128)) by (clear - GFCEIL SL128; lia).
assert (Q5 : (sp - 128) + 128 <= fl \/ fl + 1 <= (sp - 128)) by (clear - GFLR SL128; lia).
assert (Q7 : 4096 <= fl <= 140737488355327) by (clear - GFLR; lia).
cfeed P (PMAGL1.aglB_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMAGL1.aligned; assumption]).
destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & Y12 & _ & _ & _ & Y18 & Y21 & Y22 & Y24 & Y25
& _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Y4 & _ & _ & _ & _ & _ & _ & _ & _ & YD & _).
set (W3 := fun a => (sp - 104 <= a < sp - 104 + 8) \/ (F <= a < F + 24) \/ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 20)).
apply (L5SAR.apiece L ar C HI LYa HIok LB FF' LK2 cr Aw M2 model2 fx1 fx3 R2 0xafe9c R3 0xaf334 M3v W3 K HH2 AM2 MS3 MG3).
{ intros a Ha Nn. apply FRZ3; [exact Ha| intros X; apply Nn; left; clear - X; lia| intros X; apply Nn; right; left; clear - X; lia| intros X; apply Nn; right; right; clear - X; lia]. }
{ intros a Ha Wa. split.
- destruct Wa as [X|[X|X]].
+ unfold aclientw, aclient_g. right; left. split; [clear - X SL128 SHI SPT; lia| intros Y; clear - Y; lia].
+ apply (L5SAR.fframe_client L ar LB FF' 0 0 F 2 (sp - 128 + 32)); [left; reflexivity| change (ff_bytes 2) with 256; clear - X; lia].
+ apply (L5SAR.fframe_shadow_client L ar LB FF' 0 0 F 2 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 2) with 256.
unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - X; lia.
- destruct Wa as [X|[X|X]]; clear - X GFR SL128 SPT; lia. }
intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3. change (mrestrict H2 M3 = M3v) in VIS3.
assert (EK23f : L5SAR.ek L ar LB FF sp 22528 [] M2 M3).
{ apply (L5SAR.ek_piece L ar LB FF sp 22528 [] M2 M3 W3 FR3). intros a Ha Hc _ X. destruct X as [X|[X|X]].
- apply (NCS0 a); [clear - X; lia| exact Hc].
- destruct (APART a 1 sp 22528 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (Y & _). clear - X Y; lia.
- destruct (APART a 1 sp 22528 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (_ & Y & _). unfold SB in Y. clear - X Y; lia. }
pose proof (L5SAR.ek_trans L ar LB FF sp 22528 [] M M2 M3 EK02f EK23f) as EK03f.
assert (OWN3 : own sp R M3).
{ apply (own_agree sp R M1 M3 ltac:(clear - SL128 SPT; lia) ltac:(clear - SHI SPT; lia) OWN1). intros a Ha. unfold ocell in Ha.
rewrite FR3; [apply AGF; clear - Ha; lia| clear - Ha SL128 SHI SPT; lia| intros [X|[X|X]]; clear - X Ha GFCEIL GFR SL128 SPT; unfold SB in *; lia]. }
assert (WAPPR : PMKA.wapp (PMSPA.W_run PMA.AD fb)).
{ unfold PMSPA.W_run, PMSPA.W_srcf, PMSPA.err_W, PMSPA.o_src, PMSPA.o_is, PMSPA.o_tb, PMSPA.o_vec, PMSPA.o_ec, PMSPA.o_p.
cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMA.AD ADDR_A].
pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
repeat apply PMKA.wapp_cons; [..| apply PMKA.wapp_nil]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia. }
set (WR := PMSPA.W_run PMA.AD fb) in *.
assert (BI3 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PM.parser_own s) M3 model3 LK2 cr Aw).
{ unfold PMAUK.binv. split; [exact HH3|]. split; [exact AM3|].
split; [eapply L5LZ.model_rt_trans; [exact MRT1| eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3]]|].
split; [apply incl_refl|]. split; [exact GLKI2|]. split; [exact (L5SAR.astk_grows ar M2 M3 sp 22528 ASTK2 MGM3)|].
split; [apply (L5SAR.ek_W L ar LBX FF sp 22528 WR [] M M3 (PMKA.ek_sublb L ar LB LBX FF sp 22528 [] M M3 INCX EK03f)); intros a _ r0 []|].
split; [apply (L5SAR.dk_trans L ar LBX FF sp 22528 M M2 M3 DK02); apply L5SAR.dk_grows; exact MGM3|].
split; [exact OWN3|].
change (ff_bytes 2 / 8) with 32. apply (L5.defined_grows M2 M3 _ _ MGM3).
apply (proj1 (L5A.defined_vis H2 M2 (F / 8 + SB) 32 VSH)). intros i Hi. pose proof (FSHZ i Hi) as Z0. unfold MV2 in Z0. rewrite Z0. discriminate. }
assert (SZK : forall Mc lo g, L5SAR.ek L ar LBX FF sp 22528 WR M Mc -> sp - 22528 <= lo -> lo + 8 * g <= sp -> lo mod 8 = 0 -> 0 <= g -> shadow_zero Mc lo g).
{ intros Mc lo g EKc H1' H2' H3' H4'. apply (PMKA.stksh_keepA L ar LBX FF sp 22528 WR M Mc EKc WAPPR lo g); [clear - H1' SLO SPT; lia| clear - H1' SLO; lia| clear - H2' SHI SPT; lia| exact H3'| exact H4'|].
apply (PMKA.shadow_zero_sub M (sp - 22528) 2816); [| exact H3'| exact H1'| clear - H2'; lia| exact H4'| exact STKSH].
apply PMKA.mod16_8'. replace (sp - 22528) with (sp + (-1408) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
assert (ASTK3 : L5CA.astk ar M3 sp 22528) by exact (L5SAR.astk_grows ar M2 M3 sp 22528 ASTK2 MGM3).
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
destruct (APART (op / 8 + SB) 48 0 0 (CLsh (op / 8 + SB) 48 ltac:(clear - SHop; lia) ltac:(clear - SHop; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (_ & AsopSF & _).
unfold SB in ApSF, AsopSF.
assert (R1c : forall j, In j [3; 4; 21; 22; 23; 24; 25; 27]%nat -> getr R1 (reg j) = getr R (reg j)).
{ intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b [3; 4; 21; 22; 23; 24; 25; 27]%nat). vm_compute. reflexivity. }
pose (SP := fun Mc : word -> option byte => PMSPA.visitor_at RSEGS PMA.AD Mc ov /\ L5.u64_at RSEGS Mc (op + 384) ov /\ PMSTA.base_okA RSEGS PMA.AD Mc
/\ PMSTA.err_okA RSEGS PMA.AD PMA.AAD Mc e /\ PMSPA.ec_at RSEGS Mc oec 0 cat).
assert (SPK : forall Ma Mb sp0 scr0 W, L5SAR.ek L ar LB FF sp0 scr0 W Ma Mb -> PMKA.wapp W ->
(forall i, (ov <= i < ov + 8 \/ op + 384 <= i < op + 392 \/ oec <= i < oec + 16 \/ 65536 <= i < 6885376) -> L5.outside W i) -> SP Ma -> SP Mb).
{ intros Ma Mb sp0 scr0 W EK WA OUT (V1 & V2 & V3 & V4 & V5). split; [|split; [|split; [|split]]].
- apply (PMKA.visitor_keepA RSEGS PMA.AD L ar LB FF sp0 scr0 W Ma Mb EK WA FRB ov (AOF ov 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia))); [| exact V1].
intros i Hi. apply OUT. left. clear - Hi; lia.
- apply (PMKA.u64_keepA RSEGS L ar LB FF sp0 scr0 W Ma Mb EK WA FRB (op + 384) ov (AOF (op + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [| exact V2].
intros i Hi. apply OUT. right; left. clear - Hi; lia.
- apply (PMASK.base_keep L ar C LY LB FF sp0 scr0 W Ma Mb EK); [| exact V3]. intros a Ha. apply OUT. do 3 right. exact Ha.
- apply (PMKA.err_okA_keep RSEGS PMA.AD PMA.AAD L ar LB FF sp0 scr0 W Ma Mb EK e PMA.addrs_wf_A); [| exact V4].
intros a D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
split; [exact (PMA.ly_static L C LY a D)|]. apply OUT. do 3 right. clear - DI; lia.
- apply (PMKA.ec_keepA RSEGS L ar LB FF sp0 scr0 W Ma Mb EK WA FRB oec 0 cat (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia))); [| exact V5].
intros i Hi. apply OUT. right; right; left. clear - Hi; lia. }
assert (SP3 : SP M3).
{ apply (SPK M M3 sp 22528 [] EK03f PMKA.wapp_nil); [intros i _ r0 []|]. split; [exact VIS| split; [exact VREF| split; [exact BASE| split; [exact ERR| exact EC0]]]]. }
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH3) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDF3 & _).
assert (Iq : In (PM.sr_qc (PM.p_src s), PM.CHUNK) (PM.parser_own s)) by (unfold PM.parser_own, PM.src_own; left; reflexivity).
assert (IqL : In (PM.sr_qc (PM.p_src s), PM.CHUNK) LB) by (unfold LB; apply in_or_app; left; exact Iq).
pose proof (WB _ IqL) as ((Bq0 & _ & _ & _ & Bq4 & Bq5) & _). cbn [fst snd] in Bq0, Bq4, Bq5. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI, PM.CHUNK in Bq5, Bq4.
destruct Bq5 as (_ & Bq5 & _).
pose proof (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ _ _ HH IqL) as Bqi. unfold PM.CHUNK in Bqi.
set (qc := PM.sr_qc (PM.p_src s)) in *.
assert (RD : forall (pcr off k v : Z) (fx3 : FPState) (R3 : bvmap 5 word) (M3 : word -> option byte) (model3 : Model) (LK3 : list fframe) (Aw3 : list (Z * Z))
(src3 : PM.srcst) (sm3 : PM.strm),
L5.ra_ok pcr ->
PMAUK.binv L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PM.parser_own s) M3 model3 LK3 cr Aw3 ->
PM.sr_qc src3 = qc ->
PM.parser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA M3 op ois (PMSPA.with_src s src3) -> PM.iss_at RSEGS PMA.AD PMSPA.accA M3 ois str sm3 -> SP M3 ->
PMSPA.src_step (PM.p_src s) src3 sm sm3 ->
getr R3 (reg 1) = Z_to_bv 64 pcr -> getr R3 (reg 2) = Z_to_bv 64 (sp - 128) -> (forall j, In j [3; 4]%nat -> getr R3 (reg j) = getr R (reg j)) ->
getr R3 (reg 10) = Z_to_bv 64 (op + 24) -> getr R3 (reg 11) = Z_to_bv 64 (F + off) -> getr R3 (reg 12) = Z_to_bv 64 k ->
32 <= off -> off + k <= 248 -> off mod 8 = 0 -> ((k = 8 /\ v = 0) \/ (1 <= k <= 7 /\ v = k)) ->
L5.u8_at RSEGS M3 (F / 8 + off / 8 + 2147450880) v -> L5.defined M3 (F + off) k ->
(forall (fx4 : FPState) (R4 : bvmap 5 word) (M4 : word -> option byte) (model4 : Model) (LK4 : list fframe) (Aw4 : list (Z * Z)) (src4 : PM.srcst) (sm4 : PM.strm) (dd : Z),
PMAUK.binv L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PM.parser_own s) M4 model4 LK4 cr Aw4 ->
regs_preserved R3 R4 -> getr R4 (reg 10) = Z_to_bv 64 dd -> 0 <= dd <= k -> PMSPA.consumed src3 src4 sm3 sm4 = dd ->
L5.defined M4 (F + off) dd -> (1 <= PM.sr_rem src3 -> 1 <= dd) -> (dd = 0 -> PM.sr_rem src4 = 0 /\ PM.sm_st sm4 = 2) ->
PM.sr_qc src4 = qc ->
PM.parser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA M4 op ois (PMSPA.with_src s src4) -> PM.iss_at RSEGS PMA.AD PMSPA.accA M4 ois str sm4 -> SP M4 ->
PMSPA.src_step (PM.p_src s) src4 sm sm4 ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx4 R4 pcr M4 model4) K) ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx3 R3 0xaf334 M3 model3) K).
{ intros pcr off k v fx3' R3' M3' model3' LK3' Aw3' src3 sm3 RApc BI QC3 PA3 IA3 SP3' ST3 J1 J2 J34 J10 J11 J12 Ho1 Ho2 Ho3 Hkv U8 DEFk KR.
pose proof BI as (HH3' & AM3' & _ & _ & INCL3' & ASTK3' & EKb3' & _).
assert (EOWN3 : PM.parser_own (PMSPA.with_src s src3) = PM.parser_own s)
by (unfold PMSPA.with_src, PM.parser_own, PM.src_own; cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]; rewrite QC3; reflexivity).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH3') as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDF3' & _).
pose proof SP3' as (_ & _ & BASE3' & _).
unfold PMA.src_read_spec, PMSPA.src_read_spec, PMSPA.src_spec in SR.
unfold PMSPA.cfg. cbn [pa_src_read PMA.AD ADDR_A] in SR.
apply (SR fx3' R3' M3' model3' K LBX FF' LK3' Aw3' cr (sp - 128) pcr fb (PMSPA.with_src s src3) str sm3 [(F + off, k)]).
{ rewrite EOWN3. exact HH3'. }
{ exact AM3'. }
{ exact K0. }
{ split; [rewrite L5K.rl1; exact J1|]. split; [exact RApc|]. split; [rewrite L5K.rl2; exact J2|].
split; [rewrite L5K.rl3; rewrite (J34 3%nat) by inl; rewrite <- L5K.rl3; exact Rgp|].
split; [rewrite L5K.rl4; rewrite (J34 4%nat) by inl; rewrite <- L5K.rl4; exact Rtp|].
change (PMSPA.pm_scr 4) with 20480. change (20480 / 8) with 2560.
split; [apply (L5SAR.astk_sub ar M3' M3' sp 22528 128 20480 ASTK3' (mem_grows_refl M3')); [clear; lia| clear; lia| clear; lia| replace (sp - 128) with (sp + (-8) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
apply SZK; [exact EKb3'| clear; lia| clear; lia| | clear; lia].
apply PMKA.mod16_8'. replace (sp - 128 - 20480) with (sp + (-1288) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
{ apply (PMAUAR.ffroomA_push 5 4 FF LK LK3' _ FRM INCL3'); [exact NDF3'| clear; lia]. }
{ apply (PMAUAR.ffrsA_push FF sp (sp - 128) F 2 (sp - 128 + 32) FRS); clear; lia. }
{ exact FOK'. }
{ rewrite L5K.rl10. unfold PMSPA.o_src. fold op. exact J10. }
{ exists (F + off), k. split; [rewrite L5K.rl11; exact J11|]. split; [rewrite L5K.rl12; exact J12|]. split; [unfold PM.CHUNK; destruct Hkv as [(X & _)|(X & _)]; clear - X; lia|].
left. split; [exists (F, 2, sp - 128 + 32); split; [left; reflexivity| cbn [ff_addr ff_class fst snd]; change (ff_bytes 2) with 256; destruct Hkv as [(X & _)|(X & _)]; clear - X Ho1 Ho2; lia]|].
split; [destruct Hkv as [(X & _)|(X & _)]; clear - X; lia|]. split; [exact DEFk|].
split; [|split; [change (PMSPA.o_is PMA.AD fb) with ois; clear - AiF Ho1 Ho2 Hkv; change (ff_bytes 2) with 256 in AiF; destruct Hkv as [(X & _)|(X & _)]; lia
| change (PMSPA.o_p PMA.AD fb) with op; clear - ApF Ho1 Ho2 Hkv; change (ff_bytes 2) with 256 in ApF; destruct Hkv as [(X & _)|(X & _)]; lia]].
apply (aacc_local M3' F off k v (proj1 GF8) Ho3 ltac:(clear - Ho1; lia) ltac:(clear - Q3; lia) Hkv).
pose proof GFR as (_ & GF2' & _). assert (DF : F / 8 <= 17592186044384) by (apply Z.div_le_upper_bound; clear - GF2'; lia).
assert (DF0 : 0 <= F / 8) by (apply Z.div_pos; clear - Q3; lia). assert (DO : off / 8 <= 31) by (apply Z.div_le_upper_bound; [lia|]; clear - Ho2 Hkv; destruct Hkv as [(X & _)|(X & _)]; lia).
assert (DO0 : 0 <= off / 8) by (apply Z.div_pos; clear - Ho1; lia).
apply (L5ADHR.byte_of_u8 M3' _ v U8); [right| ]; clear - DF DF0 DO DO0; lia. }
{ exists (F + off), k. split; [rewrite L5K.rl11; exact J11|]. split; [rewrite L5K.rl12; exact J12|]. split; [clear - Q3 Ho1 Ho2 Hkv; destruct Hkv as [(X & _)|(X & _)]; lia|].
split; [destruct Hkv as [(X & _)|(X & _)]; clear - X; lia| reflexivity]. }
{ exact PA3. }
{ exact IA3. }
{ exact BASE3'. }
{ exact INCS. }
intros fx4 R4 M4 model4 LK4 Aw4 src4 sm4 RP4 PA4 IA4 STEP4 RES4 HP4 MRT4 INCLK4 INCAw4 AM4 HH4.
change (PMSPA.pm_scr 4) with 20480 in HP4. rewrite EOWN3 in HP4, HH4. cbn [PMSPA.with_src PM.p_src] in HP4, STEP4.
set (Wc := PMSPA.W_src PMA.AD fb src3 ++ [(F + off, k)]) in HP4.
assert (WcR : forall rr a, In rr Wc -> L5.in_rng rr a ->
(op + 280 <= a < op + 320) \/ (ois + 40 <= a < ois + 48) \/ (ois + 152 <= a < ois + 156) \/ (qc <= a < qc + 16384) \/ (F + off <= a < F + off + k)).
{ intros rr a Hin Hr. unfold Wc, PMSPA.W_src, PMSPA.W_srcf, PMSPA.o_src, PMSPA.o_is, PMSPA.o_p in Hin. cbn [app pa_off_p pa_off_is PMA.AD ADDR_A] in Hin.
rewrite QC3 in Hin. unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hr; unfold PM.CHUNK in Hr; clear - Hr Eop Eois;
[left|right;left|right;right;left|right;right;right;left|right;right;right;right]; lia. }
assert (BI4 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PM.parser_own s) M4 model4 LK4 cr Aw4).
{ apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 22528 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 2 LK2 M2 model2 cr (PM.parser_own s) G
WR WR (PM.parser_own s) (PM.parser_own s) (PM.parser_own s) M3' model3' LK3' cr Aw3' M4 model4 LK4 cr Aw4 20480 Wc BI HP4 HH4 AM4 MRT4 INCAw4 INCLK4);
[clear; lia| clear; lia| | | intros a X; exact X].
- intros rr a Hin Hr. change (ff_bytes 2 / 8) with 32. unfold ocell, SB.
pose proof GFR as (GF1 & GF2 & _). assert (D1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
assert (D2 : F / 8 <= 17592186044384) by (apply Z.div_le_upper_bound; clear - GF2; lia).
destruct (WcR rr a Hin Hr) as [X|[X|[X|[X|X]]]]; (split; [clear - X OCE ICE Bq4 GFCEIL SL128 Eop Eois GF2 Ho1 Ho2 Hkv; destruct Hkv as [(Y & _)|(Y & _)]; lia|]).
+ destruct ONSH as [Y|Y]; clear - X Y D1 D2; lia.
+ destruct INSH as [Y|Y]; clear - X Y D1 D2; lia.
+ destruct INSH as [Y|Y]; clear - X Y D1 D2; lia.
+ destruct Bq5 as [Y|Y]; clear - X Y D1 D2; lia.
+ destruct GFBIG as [Y|Y]; clear - X Y D1 D2 Ho1 Ho2 Hkv; destruct Hkv as [(Z & _)|(Z & _)]; lia.
- intros a Hc Ho rr Hin Hr. destruct (WcR rr a Hin Hr) as [X|[X|[X|[X|X]]]].
+ apply (Ho (PMSPA.o_src PMA.AD fb + 256, 40)); [unfold WR, PMSPA.W_run, PMSPA.W_srcf; right; left; reflexivity| unfold L5.in_rng, PMSPA.o_src; fold op; cbn [fst snd]; clear - X; lia].
+ apply (Ho (PMSPA.o_is PMA.AD fb + 40, 8)); [unfold WR, PMSPA.W_run, PMSPA.W_srcf; right; right; left; reflexivity| unfold L5.in_rng; fold ois; cbn [fst snd]; clear - X; lia].
+ apply (Ho (PMSPA.o_is PMA.AD fb + 152, 4)); [unfold WR, PMSPA.W_run, PMSPA.W_srcf; right; right; right; left; reflexivity| unfold L5.in_rng; fold ois; cbn [fst snd]; clear - X; lia].
+ exact (PMARS1.own_not_aclient L ar C HI HIok (PM.parser_own s) LBX FF LK cr Aw M _ qc 16384 a sp 22528 HH Iq X Hc).
+ apply (GNCF a); [left; clear - X Ho1 Ho2 Hkv; destruct Hkv as [(Y & _)|(Y & _)]; lia| exact Hc]. }
pose proof (L5SAR.ek_callee L ar LB [] FF [(F, 2, sp - 128 + 32)] sp 22528 (sp - 128) 20480 Wc Wc M3' M4 HP4 ltac:(clear; lia) ltac:(clear; lia) (fun a _ X => X)) as EK34.
assert (WAPPc : PMKA.wapp Wc).
{ intros rr Hin. unfold Wc, PMSPA.W_src, PMSPA.W_srcf, PMSPA.o_src, PMSPA.o_is, PMSPA.o_p in Hin. cbn [app pa_off_p pa_off_is PMA.AD ADDR_A] in Hin.
rewrite QC3 in Hin. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd]; unfold PM.CHUNK.
- destruct ONSH as [Y|Y]; clear - Y Eop; lia.
- destruct INSH as [Y|Y]; clear - Y Eois; lia.
- destruct INSH as [Y|Y]; clear - Y Eois; lia.
- destruct Bq5 as [Y|Y]; clear - Y; lia.
- destruct GFBIG as [Y|Y]; destruct Hkv as [(Z & _)|(Z & _)]; clear - Y Z Ho1 Ho2; lia. }
assert (SP4 : SP M4).
{ apply (SPK M3' M4 sp 22528 Wc EK34 WAPPc); [| exact SP3'].
intros i Hi rr Hin Hr. destruct (WcR rr i Hin Hr) as [Y|[Y|[Y|[Y|Y]]]].
- destruct Hi as [X|[X|[X|X]]]; clear - X Y Eop Eov Eoec Eois FB0; lia.
- destruct Hi as [X|[X|[X|X]]]; clear - X Y Eop Eov Eoec Eois FB0; lia.
- destruct Hi as [X|[X|[X|X]]]; clear - X Y Eop Eov Eoec Eois FB0; lia.
- destruct Hi as [X|[X|[X|X]]].
+ destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ qc 16384 ov 8 HH IqL (AOF ov 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia))) as [Z|Z]; clear - X Y Z; lia.
+ destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ qc 16384 (op + 384) 8 HH IqL (AOF (op + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))) as [Z|Z]; clear - X Y Z; lia.
+ destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ qc 16384 oec 16 HH IqL (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia))) as [Z|Z]; clear - X Y Z; lia.
+ clear - X Y Bqi; lia.
- destruct Hi as [X|[X|[X|X]]].
+ destruct (APART ov 8 0 0 (CLfb ov 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (Z & _). clear - X Y Z Ho1 Ho2 Hkv; destruct Hkv as [(W & _)|(W & _)]; lia.
+ destruct (APART (op + 384) 8 0 0 (CLfb (op + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (Z & _). clear - X Y Z Ho1 Ho2 Hkv; destruct Hkv as [(W & _)|(W & _)]; lia.
+ destruct (APART oec 16 0 0 (CLfb oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (Z & _). clear - X Y Z Ho1 Ho2 Hkv; destruct Hkv as [(W & _)|(W & _)]; lia.
+ clear - X Y Q3 Ho1; lia. }
destruct RES4 as (p' & k' & dd & Yp & Yk & Hp' & Hk' & Yd & Hdd & CONS & DEFd & RM1 & RM0).
assert (Ek : k' = k).
{ rewrite L5K.rl12 in Yk. rewrite J12 in Yk. apply (f_equal bv_unsigned) in Yk. unfold PM.CHUNK in Hk'. rewrite !L5.unsigned_lit in Yk by (clear - Hk' Hkv; destruct Hkv as [(X & _)|(X & _)]; lia). clear - Yk; lia. }
assert (Ep : p' = F + off).
{ rewrite L5K.rl11 in Yp. rewrite J11 in Yp. apply (f_equal bv_unsigned) in Yp. rewrite !L5.unsigned_lit in Yp by (clear - Hp' Q3 Ho1 Ho2 Hkv; destruct Hkv as [(X & _)|(X & _)]; lia). clear - Yp; lia. }
subst k' p'. rewrite L5K.rl10 in Yd.
assert (QC4 : PM.sr_qc src4 = qc) by (destruct STEP4 as (X & _); rewrite X; exact QC3).
apply (KR fx4 R4 M4 model4 LK4 Aw4 src4 sm4 dd BI4 RP4 Yd Hdd CONS DEFd RM1 RM0 QC4 PA4 IA4 SP4 (PMAPAR.src_step_transA _ _ _ _ _ _ ST3 STEP4)). }
assert (ERRP : forall (pcz v : Z) (fx5 : FPState) (R5 : bvmap 5 word) (M5 : word -> option byte) (model5 : Model) (LK5 : list fframe) (Aw5 : list (Z * Z))
(src5 : PM.srcst) (sm5 : PM.strm),
zrun pcz -> L5.ra_ok pcz -> 1 <= v <= 64 ->
PMAUK.binv L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PM.parser_own s) M5 model5 LK5 cr Aw5 ->
PM.sr_qc src5 = qc ->
PM.parser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA M5 op ois (PMSPA.with_src s src5) -> PM.iss_at RSEGS PMA.AD PMSPA.accA M5 ois str sm5 -> SP M5 ->
PMSPA.src_step (PM.p_src s) src5 sm sm5 ->
getr R5 (reg 1) = Z_to_bv 64 pcz -> getr R5 (reg 10) = Z_to_bv 64 oec -> getr R5 (reg 11) = Z_to_bv 64 v ->
getr R5 (reg 2) = Z_to_bv 64 (sp - 128) -> getr R5 (reg 8) = Z_to_bv 64 sp -> getr R5 (reg 9) = Z_to_bv 64 (sp - 128) ->
getr R5 (reg 18) = Z_to_bv 64 F -> getr R5 (reg 19) = Z_to_bv 64 op -> getr R5 (reg 20) = Z_to_bv 64 oec -> getr R5 (reg 21) = Z_to_bv 64 (op + 24) ->
getr R5 (reg 24) = Z_to_bv 64 ((F / 8) + 2147450880) -> getr R5 (reg 25) = Z_to_bv 64 F -> getr R5 (reg 26) = Z_to_bv 64 2147450880 ->
(forall j, In j [3; 4; 27]%nat -> getr R5 (reg j) = getr R (reg j)) ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx5 R5 0xae974 M5 model5) K).
{ intros pcz v fx5 R5 M5 model5 LK5 Aw5 src5 sm5 ZR RApc Hv BI5 QC5 PA5 IA5 SP5 ST5 J1 J10 J11 J2 J8 J9 J18 J19 J20 J21 J24 J25 J26 J34.
set (s5 := PMSPA.with_src s src5) in *.
assert (EOWN5 : PM.parser_own s5 = PM.parser_own s)
by (unfold s5, PMSPA.with_src, PM.parser_own, PM.src_own; cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]; rewrite QC5; reflexivity).
rewrite <- EOWN5 in BI5.
destruct SP5 as (VIS5 & VREF5 & BASE5 & ERR5 & EC5).
pose proof BI5 as (HH5 & AM5 & _ & _ & _ & ASTK5 & EKb5 & _).
pose proof EC5 as (_ & _ & ECD5 & ECA5).
pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH5) as BRB5.
unfold PMA.make_ec_spec, PMSPA.make_ec_spec in MKE.
unfold PMSPA.cfg. cbn [pa_make_ec PMA.AD ADDR_A] in MKE.
apply (MKE fx5 R5 M5 model5 K (PM.parser_own s5 ++ LBX) FF' LK5 Aw5 cr oec v (sp - 128) pcz e HH5 AM5 K0).
{ split; [rewrite L5K.rl1; exact J1|]. split; [exact RApc|]. split; [rewrite L5K.rl2; exact J2|].
split; [rewrite L5K.rl3; rewrite (J34 3%nat) by inl; rewrite <- L5K.rl3; exact Rgp|].
split; [rewrite L5K.rl4; rewrite (J34 4%nat) by inl; rewrite <- L5K.rl4; exact Rtp|].
change (PMSPA.pm_scr 1) with 14336. change (14336 / 8) with 1792.
split; [apply (L5SAR.astk_sub ar M5 M5 sp 22528 128 14336 ASTK5 (mem_grows_refl M5)); [clear; lia| clear; lia| clear; lia| replace (sp - 128) with (sp + (-8) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
apply SZK; [exact EKb5| clear; lia| clear; lia| | clear; lia].
apply PMKA.mod16_8'. replace (sp - 128 - 14336) with (sp + (-904) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
{ pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH5) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDF5 & _).
pose proof BI5 as (_ & _ & _ & _ & INCL5 & _).
apply (PMAUAR.ffroomA_push 5 1 FF LK LK5 _ FRM INCL5); [exact NDF5| clear; lia]. }
{ apply (PMAUAR.ffrsA_push FF sp (sp - 128) F 2 (sp - 128 + 32) FRS); clear; lia. }
{ rewrite L5K.rl10. exact J10. }
{ rewrite L5K.rl11. exact J11. }
{ exact Hv. }
{ apply PMAUAR.aobjA_push. apply AOF; clear - Eoec; lia. }
{ rewrite Eoec. pose proof (Z.div_mod fb 1024 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
replace (1024 * (fb / 1024) + 992) with ((128 * (fb / 1024) + 124) * 8) by (clear; lia). apply Z_mod_mult. }
{ exact ECD5. }
{ exact ECA5. }
{ exact BASE5. }
{ exact ERR5. }
intros fx6 R6 M6 model6 LK6 Aw6 RP6 EC6 ERR6 HP6 MRT6 INCLK6 INCAw6 AM6 HH6.
change (PMSPA.pm_scr 1) with 14336 in HP6.
set (Wc6 := (oec, 16) :: (if e then [] else PMSPA.err_W PMA.AD)) in HP6.
assert (Wc6R : forall rr a, In rr Wc6 -> L5.in_rng rr a -> (oec <= a < oec + 16) \/ (0x66d380 <= a < 0x68f0f4)).
{ intros rr a Hin Hr. unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [left; exact Hr|]. right. destruct e; [destruct Hin|].
unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr; lia. }
assert (BI6 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PM.parser_own s5) M6 model6 LK6 cr Aw6).
{ apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 22528 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 2 LK2 M2 model2 cr (PM.parser_own s) G
WR WR (PM.parser_own s5) (PM.parser_own s5) (PM.parser_own s5) M5 model5 LK5 cr Aw5 M6 model6 LK6 cr Aw6 14336 Wc6 BI5 HP6 HH6 AM6 MRT6 INCAw6 INCLK6);
[clear; lia| clear; lia| | | intros a X; exact X].
- intros rr a Hin Hr. change (ff_bytes 2 / 8) with 32. unfold ocell, SB.
pose proof GFR as (GF1 & GF2 & _). assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
assert (DF2 : F / 8 <= 17592186044384) by (apply Z.div_le_upper_bound; clear - GF2; lia).
pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
destruct (Wc6R rr a Hin Hr) as [X|X]; (split; [clear - X OCE SL128 SPT Eop Eoec F2 FSCEIL; lia|]).
+ destruct FA1 as [Y|Y]; clear - X Y DF1 DF2 F1 F2 Eoec; lia.
+ clear - X DF1; lia.
- intros a Hc Ho rr Hin Hr. destruct (Wc6R rr a Hin Hr) as [X|X].
+ apply (Ho (PMSPA.o_ec PMA.AD fb, 16)); [unfold WR, PMSPA.W_run, PMSPA.W_srcf, PMSPA.err_W; cbn [app]; do 6 right; left; reflexivity| unfold L5.in_rng; fold oec; cbn [fst snd]; clear - X; lia].
+ unfold WR, PMSPA.W_run, PMSPA.W_srcf, PMSPA.err_W in Ho. cbn [app pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Ho.
unfold Wc6, PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin.
destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr X Eoec O1 Eop; lia|].
destruct e; [destruct Hin|]. destruct Hin as [<-|[<-|[]]].
* apply (Ho _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))))); exact Hr.
* apply (Ho _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))))); exact Hr. }
pose proof (L5SAR.ek_callee L ar (PM.parser_own s5 ++ LBX) [] FF [(F, 2, sp - 128 + 32)] sp 22528 (sp - 128) 14336 Wc6 Wc6 M5 M6 HP6 ltac:(clear; lia) ltac:(clear; lia) (fun a _ X => X)) as EK56.
assert (WAPP6 : PMKA.wapp Wc6).
{ intros rr Hin. unfold Wc6 in Hin. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct Hin as [<-|Hin]; cbn [fst snd].
- pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1. destruct FA1 as [Y|Y]; clear - Y F1 F2 Eoec; lia.
- destruct e; [destruct Hin|]. unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd]; clear; lia. }
assert (OUT6 : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> (a + n <= oec \/ oec + 16 <= a) -> forall i, a <= i < a + n -> L5.outside Wc6 i).
{ intros a n X1 X2 X3 i Hi rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y|Y]; [clear - Hi Y X3; lia| clear - Hi Y X1 Eop O1; lia]. }
assert (OUTB6 : forall q m, In (q, m) (PM.parser_own s5 ++ LBX) -> forall i, q <= i < q + m -> L5.outside Wc6 i).
{ intros q m Hq i Hi rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y|Y].
- destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m oec 16 HH5 Hq (PMAUAR.aobjA_push FF oec 16 _ (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia)))) as [Z|Z]; clear - Hi Y Z; lia.
- pose proof (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ q m HH5 Hq) as Z. destruct Z as [Z|Z]; clear - Hi Y Z; lia. }
assert (PA6 : PM.parser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA M6 op ois s5).
{ apply (PMKA.parser_keepA RSEGS PMA.AD L ar (PM.parser_own s5 ++ LBX) FF sp 22528 Wc6 M5 M6 EK56 WAPP6 FRB BRB5 _ _ _ AOP); [| | | | | exact PA5].
- apply incl_appl, incl_refl.
- apply OUT6; clear - Eop Eoec; lia.
- unfold PMKA.blk_out. apply OUTB6. apply in_or_app; left. unfold PM.parser_own, PM.src_own; left; reflexivity.
- unfold PMKA.blk_out. apply OUTB6. apply in_or_app; left. unfold PM.parser_own, PM.vec_own. right; left; reflexivity.
- intros c0' n0 p0 E0. unfold PMKA.blk_out. apply OUTB6. apply in_or_app; left. unfold PM.parser_own, PM.vs_own. rewrite E0. right; right; left; reflexivity. }
assert (IA6 : PM.iss_at RSEGS PMA.AD PMSPA.accA M6 ois str sm5).
{ apply (PMKA.iss_keepA RSEGS PMA.AD L ar (PM.parser_own s5 ++ LBX) FF sp 22528 Wc6 M5 M6 EK56 WAPP6 FRB BRB5 ois str sm5 AOI); [| | | exact IA5].
- apply incl_appr. exact INCS.
- apply OUT6; clear - Eois Eoec; lia.
- intros c0' n0 p0 E0. unfold PMKA.blk_out. apply OUTB6. apply in_or_app; right. apply INCS. rewrite E0. left; reflexivity. }
assert (VIS6 : PMSPA.visitor_at RSEGS PMA.AD M6 ov).
{ apply (PMKA.visitor_keepA RSEGS PMA.AD L ar (PM.parser_own s5 ++ LBX) FF sp 22528 Wc6 M5 M6 EK56 WAPP6 FRB ov (AOF ov 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia))); [| exact VIS5].
apply OUT6; clear - Eov Eoec; lia. }
assert (VREF6 : L5.u64_at RSEGS M6 (op + 384) ov).
{ apply (PMKA.u64_keepA RSEGS L ar (PM.parser_own s5 ++ LBX) FF sp 22528 Wc6 M5 M6 EK56 WAPP6 FRB (op + 384) ov (AOF (op + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [| exact VREF5].
apply OUT6; clear - Eop Eoec; lia. }
assert (BASE6 : PMSTA.base_okA RSEGS PMA.AD M6).
{ apply (PMAPAR.base_keepW L ar C LY (PM.parser_own s5 ++ LBX) FF sp 22528 Wc6 M5 M6 EK56); [| | | | exact BASE5].
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
destruct (PMAUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 22528 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 2 LK2 M2 model2 cr (PM.parser_own s) G
WR (PM.parser_own s5) M6 model6 LK6 cr Aw6 BI6) as ((WS6 & _ & _ & _ & _) & OWN6 & (FD6 & FW6 & FSW6 & FLC6 & FLW6) & (FLCc6 & FLV6 & VF6 & VS6 & VSH6)).
change (ff_bytes 2) with 256 in *. change (256 / 8) with 32 in *. replace (sp - (sp - 128)) with 128 in WS6 by (clear; lia).
replace (F + 256 - 8) with (F + 248) in FLC6 by (clear; lia).
pose proof (PMAPAR.op_vis L ar C HI LY HIok _ _ LK6 cr Aw6 M6 model6 fb _ s5 HH6 FOK' PA6) as ((_ & _ & _) & Zop6 & Z326 & Z206 & OWR6 & _ & OVIS6 & _ & _).
assert (R6c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R6 (reg j) = getr R5 (reg j)).
{ intros j Hj. exact (L5SAR.cs_of_preserved R5 R6 j RP6 Hj). }
pose proof OWN6 as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96).
pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8.
pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18.
pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19. pose proof (bv_unsigned_in_range 64 (getr R (reg 20))) as B20.
pose proof (bv_unsigned_in_range 64 (getr R (reg 21))) as B21. pose proof (bv_unsigned_in_range 64 (getr R (reg 22))) as B22.
pose proof (bv_unsigned_in_range 64 (getr R (reg 23))) as B23. pose proof (bv_unsigned_in_range 64 (getr R (reg 24))) as B24.
pose proof (bv_unsigned_in_range 64 (getr R (reg 25))) as B25. pose proof (bv_unsigned_in_range 64 (getr R (reg 26))) as B26.
change (bv_modulus 64) with (2 ^ 64) in *.
pose proof GFR as (GF1 & GF2 & _). pose proof GFLR as (GL1 & GL2 & GL3 & GL4).
destruct (ZR fx6 R6 R MV6 sp op oec F fl) as (fx7 & R7 & M7v & MG7 & FRZ7 & MS7 & K347 & REG7 & E72 & FL0 & MO0);
first [assumption | (rewrite R6c by inl; assumption) | clear - SL128 SHI SPT; lia | clear - O1; lia | clear - GF1 GF2; lia
| clear - GL1 GL2; lia | clear - OCE SL128; lia | clear - GFCEIL SL128; lia | clear - GL4 SL128; lia | clear - Eop Eov Eoec O1; lia
| (replace (sp mod 32) with 0 by (symmetry; exact SP32); reflexivity) | exact SP32 | exact O8 | exact GF32 | idtac].
assert (R7ra : getr R7 (reg 1) = Z_to_bv 64 r) by (rewrite (REG7 1%nat) by inl; exact Rra).
pose proof (PMK.ret_to RSEGS fx7 R7 M7v 0xb02e8 (ltac:(oW' 0xb02e8%Z)) r (ltac:(oF' 0xb02e8%Z)) eq_refl (ltac:(oD' 0xb02e8%Z)) R7ra Hr1 Hr2) as MSr.
apply (PMAUK.retire_coreW L ar C HI LYa HIok M model LBX FF LK Aw sp 22528 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 2 LK2 M2 model2 cr (PM.parser_own s) G
WR (PM.parser_own s5) M6 model6 LK6 cr Aw6 (fun a => op + 8 <= a < op + 9) fx6 fx7 R6 pcz R7 r M7v K BI6).
{ intros a X. split.
- apply (L5SAR.fframe_client L ar (PM.parser_own s5 ++ LBX) FF' 0 0 fb 4 rs); [right; exact Hfb| change (ff_bytes 4) with 1024; clear - X Eop; lia].
- intros O. apply (O (PMSPA.o_p PMA.AD fb + 8, 8)); [left; reflexivity| unfold L5.in_rng; fold op; cbn [fst snd]; clear - X; lia]. }
{ intros a. destruct (L5SAR.rng_dec a (op + 8) (op + 9)) as [X|X]; [left; exact X| right; exact X]. }
{ exact (msteps_trans _ _ _ _ MS7 MSr). }
{ exact MG7. }
{ intros a Ha Nw. unfold PMAUK.WretX, PMAUK.Wret in Nw. change (ff_bytes 2) with 256 in Nw. change (256 / 8) with 32 in Nw.
apply FRZ7; [exact Ha| intros X; apply Nw; right; clear - X; lia| intros X; apply Nw; left; left; left; clear - X; lia
| intros X; apply Nw; left; left; right; unfold SB; clear - X; lia| intros X; apply Nw; left; right; clear - X; lia]. }
{ exact FL0. }
intros Mf modelf FZf MGf VISf AHf MRTf AMf HHf. change (mrestrict H6 Mf = M7v) in VISf.
assert (EKf : L5SAR.ek L ar (PM.parser_own s5 ++ LBX) FF 0 0 [(op + 8, 1)] M6 Mf).
{ apply (PMAUAR.wret_ek L ar C HI LY HIok LBX FF LK Aw sp 22528 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 2 LK2 M2 model2 cr (PM.parser_own s)
(PM.parser_own s5 ++ LBX) LK6 cr Aw6 M6 Mf _ [(op + 8, 1)] (fun a => op + 8 <= a < op + 9) G HH6).
- intros a X O. apply (O (op + 8, 1)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X; lia].
- exact FZf. }
pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH6) as BRB6.
assert (MO0f : L5.u8_at RSEGS Mf (op + 8) 0).
{ apply (proj1 (L5A.u8_at_vis H6 Mf (op + 8) 0 (OVIS6 (op + 8) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia))). rewrite VISf. exact MO0. }
pose proof BI6 as (_ & _ & _ & INCA6 & INCL6 & _).
assert (OUT8 : forall a n, (a + n <= op + 8 \/ op + 9 <= a) -> forall i, a <= i < a + n -> L5.outside [(op + 8, 1)] i).
{ intros a n X3 i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hi Hr X3. lia. }
assert (OUTB8 : forall q m, In (q, m) (PM.parser_own s5 ++ LBX) -> forall i, q <= i < q + m -> L5.outside [(op + 8, 1)] i).
{ intros q m Hq i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr.
destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m op 384 HH6 Hq (PMAUAR.aobjA_push FF op 384 _ AOP)) as [Z|Z]; clear - Hi Hr Z; lia. }
assert (WAPP8 : PMKA.wapp [(op + 8, 1)]).
{ apply PMKA.wapp_cons; [| apply PMKA.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct ONSH as [Y|Y]; [right| left]; clear - Y; lia. }
assert (Ivb : In (PM.p_b s5, 32 * 2 ^ PM.p_k s5) (PM.parser_own s5 ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.vec_own; right; left; reflexivity).
assert (Iqc : In (PM.sr_qc (PM.p_src s5), PM.CHUNK) (PM.parser_own s5 ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
apply (KONT fx7 R7 Mf modelf LK6 Aw6 (PMPK.set_more s5 0) sm5 true cr).
- apply L5SAR.preserved_by_index. intros j Hj. pose proof Hj as Hj'. unfold L5SAR.cs_all in Hj.
repeat (destruct Hj as [<-|Hj]; [first [ rewrite E72; exact (eq_sym Rsp) | apply REG7; inl
| rewrite (K347 _) by inl; rewrite (R6c _) by inl; apply J34; inl ] |]).
destruct Hj.
- unfold PMSPA.run_post_d, PMSPA.run_pre.
split; [split; [| split; [| split; [| split; [| split; [| split]]]]]|].
+ destruct (BRB6 _ Iqc) as (Xq1 & Xq2). destruct (BRB6 _ Ivb) as (Xb1 & Xb2). cbn [fst snd] in Xq1, Xq2, Xb1, Xb2.
apply (PMAPAR.parser_more_updA M6 Mf op ois s5 0 PA6).
* clear - O1; lia.
* clear - O1; lia.
* apply (PMKA.agA_obj L ar _ FF 0 0 _ M6 Mf EKf WAPP8 FRB op 8 (AOF op 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))). apply OUT8. clear; lia.
* apply (PMKA.agA_obj L ar _ FF 0 0 _ M6 Mf EKf WAPP8 FRB (op + 9) 375 (AOF (op + 9) 375 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))). apply OUT8. clear; lia.
* exact (PMKA.agsh_obj L ar _ FF 0 0 _ M6 Mf EKf WAPP8 FRB op 384 AOP).
* pose proof PA6 as (_ & PD6 & _). apply (L5.defined_grows M6 Mf _ _ MGf PD6).
* exact MO0f.
* left; reflexivity.
* exact Xq1.
* clear - Xq2; lia.
* apply (PMKA.agA_blk L ar _ FF 0 0 _ M6 Mf EKf WAPP8 BRB6 _ _ Iqc). apply OUTB8. exact Iqc.
* exact Xb1.
* clear - Xb2; lia.
* apply (PMKA.agA_blk L ar _ FF 0 0 _ M6 Mf EKf WAPP8 BRB6 _ _ Ivb). apply OUTB8. exact Ivb.
* intros c0' n0 p0 E0. assert (Ip : In (p0, c0') (PM.parser_own s5 ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.vs_own; rewrite E0; right; right; left; reflexivity).
apply (PMKA.agA_blk L ar _ FF 0 0 _ M6 Mf EKf WAPP8 BRB6 _ _ Ip). apply OUTB8. exact Ip.
+ apply (PMKA.iss_keepA RSEGS PMA.AD L ar _ FF 0 0 _ M6 Mf EKf WAPP8 FRB BRB6 ois str sm5 AOI); [| | | exact IA6].
* apply incl_appr. exact INCS.
* apply OUT8. clear - Eop Eois; lia.
* intros c0' n0 p0 E0. unfold PMKA.blk_out. apply (OUTB8 p0 c0'). apply in_or_app; right. apply INCS. rewrite E0. left; reflexivity.
+ apply (PMKA.visitor_keepA RSEGS PMA.AD L ar _ FF 0 0 _ M6 Mf EKf WAPP8 FRB _ (AOF ov 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia))); [| exact VIS6].
apply OUT8. clear - Eop Eov; lia.
+ apply (PMKA.u64_keepA RSEGS L ar _ FF 0 0 _ M6 Mf EKf WAPP8 FRB (op + 384) _ (AOF (op + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [| exact VREF6].
apply OUT8. clear; lia.
+ apply (PMASK.base_keep L ar C LY _ FF 0 0 _ M6 Mf EKf); [| exact BASE6]. intros a Ha rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Ha Hr O1; lia.
+ apply (PMKA.err_okA_keep RSEGS PMA.AD PMA.AAD L ar _ FF 0 0 _ M6 Mf EKf true PMA.addrs_wf_A); [| exact ERR6].
intros a D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
split; [exact (PMA.ly_static L C LY a D)|]. intros rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - DI Hr O1; lia.
+ unfold PMPK.set_more. cbn [PM.p_tb PM.p_tg]. exact TBOK.
+ split; [exact ST5|].
split; [intros _; reflexivity|]. left. exists v. split; [exact Hv|]. split; [| split; [reflexivity| reflexivity]].
apply (PMKA.ec_keepA RSEGS L ar _ FF 0 0 _ M6 Mf EKf WAPP8 FRB _ v _ (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia))); [| exact EC6].
apply OUT8. clear - Eop Eoec; lia.
- exact AHf.
- unfold PMSPA.credit_keep. change (PM.pot_parser (PMSPA.HV L ar) (PMPK.set_more s5 0)) with (PM.pot_parser (PMSPA.HV L ar) s). split; lia.
- exact MRTf.
- exact INCL6.
- exact INCA6.
- exact AMf.
- unfold PMPK.set_more. change (PM.parser_own (PM.PST 0 (PM.p_done s5) (PM.p_depth s5) (PM.p_src s5) (PM.p_tb s5) (PM.p_tg s5) (PM.p_b s5) (PM.p_k s5) (PM.p_stk s5)))
with (PM.parser_own s5). exact HHf. }
assert (OKP : forall (pc0 : Z) (X : bvmap 5 word -> (word -> option byte) -> Z -> Prop) (fx5 : FPState) (R5 : bvmap 5 word) (M5 : word -> option byte) (model5 : Model)
(LK5 : list fframe) (Aw5 : list (Z * Z)) (src5 : PM.srcst) (sm5 : PM.strm),
orun pc0 X -> X R5 (mrestrict (ahid Aw5 model5) M5) F ->
PMAUK.binv L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PM.parser_own s) M5 model5 LK5 cr Aw5 ->
PM.sr_qc src5 = qc ->
PM.parser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA M5 op ois (PMSPA.with_src s src5) -> PM.iss_at RSEGS PMA.AD PMSPA.accA M5 ois str sm5 -> SP M5 ->
PMSPA.src_step (PM.p_src s) src5 sm sm5 -> PM.unread src5 sm5 < PM.unread (PM.p_src s) sm ->
getr R5 (reg 2) = Z_to_bv 64 (sp - 128) -> getr R5 (reg 8) = Z_to_bv 64 sp -> getr R5 (reg 9) = Z_to_bv 64 (sp - 128) ->
getr R5 (reg 18) = Z_to_bv 64 F -> getr R5 (reg 19) = Z_to_bv 64 op -> getr R5 (reg 20) = Z_to_bv 64 oec -> getr R5 (reg 21) = Z_to_bv 64 (op + 24) ->
getr R5 (reg 24) = Z_to_bv 64 ((F / 8) + 2147450880) -> getr R5 (reg 25) = Z_to_bv 64 F -> getr R5 (reg 26) = Z_to_bv 64 2147450880 ->
(forall j, In j [3; 4; 27]%nat -> getr R5 (reg j) = getr R (reg j)) ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx5 R5 pc0 M5 model5) K).
{ intros pc0 X fx5 R5 M5 model5 LK5 Aw5 src5 sm5 ORUN XR BI5 QC5 PA5 IA5 SP5 ST5 UNR5 J2 J8 J9 J18 J19 J20 J21 J24 J25 J26 J34.
set (s5 := PMSPA.with_src s src5) in *.
assert (EOWN5 : PM.parser_own s5 = PM.parser_own s)
by (unfold s5, PMSPA.with_src, PM.parser_own, PM.src_own; cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]; rewrite QC5; reflexivity).
rewrite <- EOWN5 in BI5.
destruct SP5 as (VIS5 & VREF5 & BASE5 & ERR5 & EC5).
pose proof BI5 as (HH5 & AM5 & _ & INCA5 & INCL5 & _).
pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH5) as BRB5.
set (H5 := ahid Aw5 model5) in *. set (MV5 := mrestrict H5 M5) in *.
destruct (PMAUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 22528 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 2 LK2 M2 model2 cr (PM.parser_own s) G
WR (PM.parser_own s5) M5 model5 LK5 cr Aw5 BI5) as ((WS5 & _ & _ & _ & _) & OWN5 & (FD5 & FW5 & FSW5 & FLC5 & FLW5) & (FLCc5 & FLV5 & VF5 & VS5 & VSH5)).
change (ff_bytes 2) with 256 in *. change (256 / 8) with 32 in *. replace (sp - (sp - 128)) with 128 in WS5 by (clear; lia).
replace (F + 256 - 8) with (F + 248) in FLC5 by (clear; lia).
pose proof GFR as (GF1 & GF2 & _). pose proof GFLR as (GL1 & GL2 & GL3 & GL4).
destruct (ORUN fx5 R5 R MV5 sp op oec F fl XR) as (fx6 & R6 & M6v & MG6 & FRZ6 & MS6 & K346 & REG6 & E62 & FL0);
first [assumption | clear - SL128 SHI SPT; lia | clear - O1; lia | clear - GF1 GF2; lia
| clear - GL1 GL2; lia | clear - GFCEIL SL128; lia | clear - GL4 SL128; lia
| (replace (sp mod 32) with 0 by (symmetry; exact SP32); reflexivity) | exact SP32 | exact GF32 | idtac].
assert (R6ra : getr R6 (reg 1) = Z_to_bv 64 r) by (rewrite (REG6 1%nat) by inl; exact Rra).
pose proof (PMK.ret_to RSEGS fx6 R6 M6v 0xb02e8 (ltac:(oW' 0xb02e8%Z)) r (ltac:(oF' 0xb02e8%Z)) eq_refl (ltac:(oD' 0xb02e8%Z)) R6ra Hr1 Hr2) as MSr.
apply (PMAUK.retire_core L ar C HI LYa HIok M model LBX FF LK Aw sp 22528 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 2 LK2 M2 model2 cr (PM.parser_own s) G
WR (PM.parser_own s5) M5 model5 LK5 cr Aw5 fx5 fx6 R5 pc0 R6 r M6v K BI5 (msteps_trans _ _ _ _ MS6 MSr) MG6).
{ intros a Ha Nw. unfold PMAUK.Wret in Nw. change (ff_bytes 2) with 256 in Nw. change (256 / 8) with 32 in Nw.
apply FRZ6; [exact Ha| intros Y; apply Nw; left; left; clear - Y; lia| intros Y; apply Nw; left; right; unfold SB; clear - Y; lia| intros Y; apply Nw; right; clear - Y; lia]. }
{ exact FL0. }
intros Mf modelf FZf AHf MRTf AMf HHf.
assert (EKf : L5SAR.ek L ar (PM.parser_own s5 ++ LBX) FF 0 0 [] M5 Mf).
{ apply (PMAUAR.wret_ek L ar C HI LY HIok LBX FF LK Aw sp 22528 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 2 LK2 M2 model2 cr (PM.parser_own s)
(PM.parser_own s5 ++ LBX) LK5 cr Aw5 M5 Mf _ [] (fun _ => False) G HH5 (fun a Y => match Y with end)).
intros a Ha N. apply FZf; [exact Ha| intros Y; apply N; left; exact Y]. }
apply (KONT fx6 R6 Mf modelf LK5 Aw5 s5 sm5 e cr).
- apply L5SAR.preserved_by_index. intros j Hj. pose proof Hj as Hj'. unfold L5SAR.cs_all in Hj.
repeat (destruct Hj as [<-|Hj]; [first [ rewrite E62; exact (eq_sym Rsp) | apply REG6; inl | rewrite (K346 _) by inl; apply J34; inl ] |]).
destruct Hj.
- unfold PMSPA.run_post_d, PMSPA.run_pre.
split; [split; [| split; [| split; [| split; [| split; [| split]]]]]|].
+ apply (PMKA.parser_keepA RSEGS PMA.AD L ar (PM.parser_own s5 ++ LBX) FF 0 0 [] M5 Mf EKf PMKA.wapp_nil FRB BRB5 _ _ _ AOP); [| intros i _ r0 []| intros i _ r0 []| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact PA5].
apply incl_appl, incl_refl.
+ apply (PMKA.iss_keepA RSEGS PMA.AD L ar (PM.parser_own s5 ++ LBX) FF 0 0 [] M5 Mf EKf PMKA.wapp_nil FRB BRB5 _ str sm5 AOI); [| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA5].
apply incl_appr. exact INCS.
+ apply (PMKA.visitor_keepA RSEGS PMA.AD L ar (PM.parser_own s5 ++ LBX) FF 0 0 [] M5 Mf EKf PMKA.wapp_nil FRB _ (AOF ov 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia))); [intros i _ r0 []| exact VIS5].
+ apply (PMKA.u64_keepA RSEGS L ar (PM.parser_own s5 ++ LBX) FF 0 0 [] M5 Mf EKf PMKA.wapp_nil FRB (op + 384) _ (AOF (op + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [intros i _ r0 []| exact VREF5].
+ apply (PMASK.base_keep L ar C LY (PM.parser_own s5 ++ LBX) FF 0 0 [] M5 Mf EKf); [intros a _ r0 []| exact BASE5].
+ apply (PMKA.err_okA_keep RSEGS PMA.AD PMA.AAD L ar (PM.parser_own s5 ++ LBX) FF 0 0 [] M5 Mf EKf e PMA.addrs_wf_A); [| exact ERR5].
intros a D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
split; [exact (PMA.ly_static L C LY a D)| intros r0 []].
+ exact TBOK.
+ split; [exact ST5|]. split; [intros Y; exact Y|]. right.
split; [apply (PMKA.ec_keepA RSEGS L ar (PM.parser_own s5 ++ LBX) FF 0 0 [] M5 Mf EKf PMKA.wapp_nil FRB oec 0 cat (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia))); [intros i _ r0 []| exact EC5]|].
split; [exact INV|].
split; [reflexivity|]. split; [exact UNR5|].
exists (bv_unsigned (getr R6 (reg 10))). split; [pose proof (bv_unsigned_in_range 64 (getr R6 (reg 10))) as B10; change (bv_modulus 64) with (2 ^ 64) in B10; exact B10|].
rewrite L5K.rl10. symmetry. apply Z_to_bv_bv_unsigned.
- exact AHf.
- unfold PMSPA.credit_keep. change (PM.pot_parser (PMSPA.HV L ar) s5) with (PM.pot_parser (PMSPA.HV L ar) s). split; lia.
- exact MRTf.
- exact INCL5.
- exact INCA5.
- exact AMf.
- exact HHf. }
assert (PK : forall (Ma Mb : word -> option byte) (Wp : Z -> Prop) (src0 : PM.srcst) (sm0 : PM.strm),
(forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) ->
(forall a, Wp a -> (sp - 128 <= a < sp) \/ (F <= a < F + 256) \/ (F / 8 + SB <= a < F / 8 + SB + 32)) ->
PM.sr_qc src0 = qc ->
PM.parser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA Ma op ois (PMSPA.with_src s src0) -> PM.iss_at RSEGS PMA.AD PMSPA.accA Ma ois str sm0 -> SP Ma ->
PM.parser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA Mb op ois (PMSPA.with_src s src0) /\ PM.iss_at RSEGS PMA.AD PMSPA.accA Mb ois str sm0 /\ SP Mb).
{ intros Ma Mb Wp src0 sm0 FRm WPm QC0 PAm IAm SPm.
assert (EK : L5SAR.ek L ar LB FF sp 22528 [] Ma Mb).
{ apply (L5SAR.ek_piece L ar LB FF sp 22528 [] Ma Mb Wp FRm). intros a Ha Hc _ X. destruct (WPm a X) as [Y|[Y|Y]].
- apply (NCS0 a); [exact Y| exact Hc].
- destruct (APART a 1 sp 22528 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (Z & _). clear - Y Z; lia.
- destruct (APART a 1 sp 22528 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (_ & Z & _). unfold SB in Y, Z. clear - Y Z; lia. }
assert (EOWN0 : PM.parser_own (PMSPA.with_src s src0) = PM.parser_own s)
by (unfold PMSPA.with_src, PM.parser_own, PM.src_own; cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]; rewrite QC0; reflexivity).
split; [|split].
- apply (PMKA.parser_keepA RSEGS PMA.AD L ar LB FF sp 22528 [] Ma Mb EK PMKA.wapp_nil FRB BRB _ _ _ AOP);
[rewrite EOWN0; unfold LB; apply incl_appl, incl_refl| intros i _ r0 []| intros i _ r0 []| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact PAm].
- apply (PMKA.iss_keepA RSEGS PMA.AD L ar LB FF sp 22528 [] Ma Mb EK PMKA.wapp_nil FRB BRB ois str sm0 AOI); [unfold LB; apply incl_appr; exact INCS| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IAm].
- apply (SPK Ma Mb sp 22528 [] EK PMKA.wapp_nil); [intros i _ r0 []| exact SPm]. }
assert (WSID : PMSPA.with_src s (PM.p_src s) = s) by (clear; destruct s; reflexivity).
assert (PA3 : PM.parser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA M3 op ois (PMSPA.with_src s (PM.p_src s))).
{ rewrite WSID. apply (PMKA.parser_keepA RSEGS PMA.AD L ar LB FF sp 22528 [] M M3 EK03f PMKA.wapp_nil FRB BRB _ _ _ AOP);
[unfold LB; apply incl_appl, incl_refl| intros i _ r0 []| intros i _ r0 []| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact PA]. }
assert (IA3 : PM.iss_at RSEGS PMA.AD PMSPA.accA M3 ois str sm).
{ apply (PMKA.iss_keepA RSEGS PMA.AD L ar LB FF sp 22528 [] M M3 EK03f PMKA.wapp_nil FRB BRB ois str sm AOI); [unfold LB; apply incl_appr; exact INCS| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA]. }
assert (STR : PMSPA.src_step (PM.p_src s) (PM.p_src s) sm sm) by (unfold PMSPA.src_step; split; [reflexivity| split; [reflexivity| split; [clear; lia| split; [intros X; exact X| clear; lia]]]]).
assert (R3c : forall j, In j [3; 4; 27]%nat -> getr R3 (reg j) = getr R (reg j)).
{ intros j Hj. rewrite (KS3 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity).
rewrite (R2c j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity). apply R1c. revert j Hj. apply (L5K.incl_b [3; 4; 27]%nat). vm_compute. reflexivity. }
assert (Y4m : L5.u8_at RSEGS M3 (F / 8 + 32 / 8 + 2147450880) 1).
{ change (32 / 8) with 4. replace (F / 8 + 4 + 2147450880) with (F / 8 + 2147450884) by (clear; lia).
apply (proj1 (L5A.u8_at_vis H2 M3 ((F / 8) + 2147450884) 1 (L5A.avis_sub H2 (F / 8 + SB) 32 ((F / 8) + 2147450884) 1 VSH ltac:(unfold SB; clear; lia) ltac:(unfold SB; clear; lia))
ltac:(clear - Q0f GFR; lia) ltac:(clear - GFR; lia))).
rewrite VIS3. exact Y4. }
assert (YDm : L5.defined M3 (F + 24) 232).
{ apply (proj1 (L5A.defined_vis H2 M3 (F + 24) 232 (L5A.avis_sub H2 F 256 (F + 24) 232 VF ltac:(clear; lia) ltac:(clear; lia)))). rewrite VIS3. exact YD. }
apply (RD 0xaff78 32 1 1 fx3 R3 M3 model3 LK2 Aw (PM.p_src s) sm ltac:(split; [clear; lia| reflexivity]) BI3 eq_refl PA3 IA3 SP3 STR).
{ exact Y1. } { rewrite (KS3 2%nat) by inl. exact B2R. } { intros j Hj. apply R3c. revert j Hj. apply (L5K.incl_b [3; 4]%nat). vm_compute. reflexivity. }
{ exact Y10. } { exact Y11. } { exact Y12. }
{ clear; lia. } { clear; lia. } { reflexivity. } { right; split; [clear; lia| reflexivity]. }
{ exact Y4m. }
{ apply (L5.defined_sub M3 (F + 24) 232); [exact YDm| clear; lia| clear; lia]. }
intros fx4 R4 M4 model4 LK4 Aw4 src4 sm4 dd BI4 RP4 Yd Hdd CONS DEFd RM1 RM0 QC4 PA4 IA4 SP4 ST4.
assert (R4c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R4 (reg j) = getr R3 (reg j))
by (intros j Hj; exact (L5SAR.cs_of_preserved R3 R4 j RP4 Hj)).
assert (G2' : getr R4 (reg 2) = Z_to_bv 64 (sp - 128)) by (rewrite (R4c 2%nat) by inl; rewrite (KS3 2%nat) by inl; exact B2R).
assert (G8' : getr R4 (reg 8) = Z_to_bv 64 sp) by (rewrite (R4c 8%nat) by inl; rewrite (KS3 8%nat) by inl; exact B8R).
assert (G9' : getr R4 (reg 9) = Z_to_bv 64 (sp - 128)) by (rewrite (R4c 9%nat) by inl; rewrite (KS3 9%nat) by inl; exact B9R).
assert (G18' : getr R4 (reg 18) = Z_to_bv 64 F) by (rewrite (R4c 18%nat) by inl; exact Y18).
assert (G19' : getr R4 (reg 19) = Z_to_bv 64 op) by (rewrite (R4c 19%nat) by inl; rewrite (KS3 19%nat) by inl; exact B19R).
assert (G20' : getr R4 (reg 20) = Z_to_bv 64 oec) by (rewrite (R4c 20%nat) by inl; rewrite (KS3 20%nat) by inl; exact B20R).
assert (G21' : getr R4 (reg 21) = Z_to_bv 64 (op + 24)) by (rewrite (R4c 21%nat) by inl; exact Y21).
assert (G22' : getr R4 (reg 22) = Z_to_bv 64 (F + 32)) by (rewrite (R4c 22%nat) by inl; exact Y22).
assert (G24' : getr R4 (reg 24) = Z_to_bv 64 ((F / 8) + 2147450880)) by (rewrite (R4c 24%nat) by inl; exact Y24).
assert (G25' : getr R4 (reg 25) = Z_to_bv 64 F) by (rewrite (R4c 25%nat) by inl; exact Y25).
assert (G26' : getr R4 (reg 26) = Z_to_bv 64 2147450880) by (rewrite (R4c 26%nat) by inl; rewrite (KS3 26%nat) by inl; exact B26R).
assert (G34' : forall j, In j [3; 4; 27]%nat -> getr R4 (reg j) = getr R (reg j)).
{ intros j Hj. rewrite (R4c j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity). apply R3c. exact Hj. }
clear R4c.
set (H4 := ahid Aw4 model4) in *. set (MV4 := mrestrict H4 M4) in *.
destruct (Z.eq_dec dd 0) as [D0|D0].
-
clear CONS. subst dd.
cfeed P (PMAGL1.aglE0_conc fx4 R4 MV4 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption]).
destruct P as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Z1 & Z10 & Z11).
assert (E5 : M5v = MV4) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ5; exact Ha). subst M5v.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK4 cr Aw4 M4 model4 fx4 fx5 R4 0xaff78 R5 0xae974 MV4 K (proj1 BI4) (proj1 (proj2 BI4)) MS5 (fun x Hx => Hx) (fun a Ha => eq_refl)).
intros M5 model5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5.
assert (E5 : M5 = M4) by (apply L5SAR.mem_eq_of_agree; exact FR5). subst M5.
pose proof (PMAUK.binv_model L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PM.parser_own s) M4 model4 LK4 cr Aw4 model5 BI4 HH5 AM5 MRT5) as BI5.
apply (ERRP 0xb000c 1 fx5 R5 M4 model5 LK4 Aw4 src4 sm4 zT_run ltac:(split; [clear; lia| reflexivity]) ltac:(clear; lia) BI5 QC4 PA4 IA4 SP4 ST4).
all: first [ exact Z1 | exact Z10 | exact Z11 | (rewrite (KS5 _) by inl; assumption)
| (intros j Hj; rewrite (KS5 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity); apply G34'; exact Hj) ].
-
assert (D1 : dd = 1) by (clear - Hdd D0; lia). clear D0. rewrite D1 in Yd, CONS, DEFd. clear Hdd RM0.
assert (UN4 : PM.unread src4 sm4 < PM.unread (PM.p_src s) sm) by (unfold PMSPA.consumed in CONS; clear - CONS; lia).
cfeed P (PMAGL1.aglB1_conc fx4 R4 MV4 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption]).
destruct P as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5).
assert (E5 : M5v = MV4) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ5; exact Ha). subst M5v.
pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LK4 cr Aw4 M4 model4 (proj1 BI4)) as (_ & _ & _ & VFS4 & _).
assert (DV4 : L5.defined MV4 (F + 32) 1).
{ apply (proj2 (L5A.defined_vis H4 M4 (F + 32) 1 (VFS4 (F + 32) 1 ltac:(clear - GFS1; lia) ltac:(clear - GFS2; lia)))). exact DEFd. }
destruct (PMPX.lbu_run RSEGS fx5 R5 MV4 0xaff7c (ltac:(oW' 0xaff7c%Z)) 10%bv 22%bv 0%bv (F + 32) (ltac:(oF' 0xaff7c%Z)) eq_refl (ltac:(oD' 0xaff7c%Z))) as (b & Hb & U8b & MSb).
{ intros E0. apply (f_equal bv_unsigned) in E0. vm_compute in E0. discriminate E0. }
{ clear; lia. } { clear; lia. }
{ rewrite L5K.rl22. rewrite (KS5 22%nat) by inl. exact G22'. }
{ clear - Q0f GFR; lia. }
{ change (bv_signed (0%bv : bv 12)) with 0. clear - Q0f GFR; lia. }
{ change (bv_signed (0%bv : bv 12)) with 0. rewrite Z.add_0_r. exact DV4. }
change (0xaff7c + 4) with 0xaff80 in MSb. rewrite L5K.rl10 in MSb.
set (R5' := regupd R5 (reg 10) (Z_to_bv 64 b)) in MSb.
assert (R5o : forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R5' (reg k) = getr R4 (reg k)).
{ intros k Hk. unfold R5'. rewrite PMPX.regupd_other_idx.
- apply KS5. revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat). vm_compute. reflexivity.
- intros E. subst k. cbn in Hk. repeat (destruct Hk as [Hk|Hk]; [discriminate Hk|]). destruct Hk.
- cbn in Hk. repeat (destruct Hk as [<-|Hk]; [lia|]). destruct Hk.
- lia. }
assert (R510 : getr R5' (reg 10) = Z_to_bv 64 b) by (unfold R5'; apply PMPX.regupd_same_idx; lia).
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK4 cr Aw4 M4 model4 fx4 fx5 R4 0xaff78 R5' 0xaff80 MV4 K (proj1 BI4) (proj1 (proj2 BI4))).
{ eapply msteps_trans; [exact MS5| exact MSb]. }
{ intros x Hx. exact Hx. }
{ intros a Ha. reflexivity. }
intros M5 model5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5.
assert (E5 : M5 = M4) by (apply L5SAR.mem_eq_of_agree; exact FR5). subst M5.
pose proof (PMAUK.binv_model L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PM.parser_own s) M4 model4 LK4 cr Aw4 model5 BI4 HH5 AM5 MRT5) as BI5.
assert (K52 : getr R5' (reg 2) = Z_to_bv 64 (sp - 128)) by (rewrite (R5o 2%nat) by inl; exact G2').
assert (K58 : getr R5' (reg 8) = Z_to_bv 64 sp) by (rewrite (R5o 8%nat) by inl; exact G8').
assert (K59 : getr R5' (reg 9) = Z_to_bv 64 (sp - 128)) by (rewrite (R5o 9%nat) by inl; exact G9').
assert (K518 : getr R5' (reg 18) = Z_to_bv 64 F) by (rewrite (R5o 18%nat) by inl; exact G18').
assert (K519 : getr R5' (reg 19) = Z_to_bv 64 op) by (rewrite (R5o 19%nat) by inl; exact G19').
assert (K520 : getr R5' (reg 20) = Z_to_bv 64 oec) by (rewrite (R5o 20%nat) by inl; exact G20').
assert (K521 : getr R5' (reg 21) = Z_to_bv 64 (op + 24)) by (rewrite (R5o 21%nat) by inl; exact G21').
assert (K524 : getr R5' (reg 24) = Z_to_bv 64 ((F / 8) + 2147450880)) by (rewrite (R5o 24%nat) by inl; exact G24').
assert (K525 : getr R5' (reg 25) = Z_to_bv 64 F) by (rewrite (R5o 25%nat) by inl; exact G25').
assert (K526 : getr R5' (reg 26) = Z_to_bv 64 2147450880) by (rewrite (R5o 26%nat) by inl; exact G26').
assert (K534 : forall j, In j [3; 4; 27]%nat -> getr R5' (reg j) = getr R (reg j)).
{ intros j Hj. rewrite (R5o j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity). apply G34'. exact Hj. }
clear R5o KS5 G2' G8' G9' G18' G19' G20' G21' G22' G24' G25' G26' G34'.
clearbody R5'.
set (H5 := ahid Aw4 model5) in *. set (MV5 := mrestrict H5 M4) in *.
destruct (PMAUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 22528 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 2 LK2 M2 model2 cr (PM.parser_own s) G
WR (PM.parser_own s) M4 model5 LK4 cr Aw4 BI5) as ((WS5 & _ & _ & _ & _) & OWN5 & (FD5 & FW5 & FSW5 & FLC5 & FLW5) & (FLCc5 & FLV5 & VF5 & VS5 & VSH5)).
change (ff_bytes 2) with 256 in *. change (256 / 8) with 32 in *. replace (F + 256 - 8) with (F + 248) in FLC5 by (clear; lia).
assert (HB64 : 0 <= b < 2 ^ 64) by (clear - Hb; lia).
destruct (Z.eq_dec b 105) as [Bti|Bti].
{
subst b.
cfeed P (PMAGL1.aglTi_conc fx5 R5' MV5 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMAGL1.aligned; assumption]).
destruct P as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & MS6 & KS6 & A61 & A610 & A611 & A612 & A622 & A623 & C60).
set (W6 := fun a => F / 8 + 2147450886 <= a < F / 8 + 2147450886 + 1).
apply (L5SAR.apiece L ar C HI LYa HIok _ FF' LK4 cr Aw4 M4 model5 fx5 fx6 R5' 0xaff80 R6 0xaf334 M6v W6 K (proj1 BI5) (proj1 (proj2 BI5)) MS6 MG6).
{ intros a Ha Nn. apply FRZ6; [exact Ha| intros X; apply Nn; unfold W6; clear - X; lia]. }
{ intros a Ha Wa. unfold W6 in Wa. split.
- apply (L5SAR.fframe_shadow_client L ar _ FF' 0 0 F 2 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 2) with 256.
unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - Wa; lia.
- assert (DF0 : 0 <= F / 8) by (apply Z.div_pos; clear - Q3; lia). clear - Wa DF0; lia. }
intros M6 model6 HH6 AM6 MRT6 HID6 VIS6 MGM6 FR6 VV6. change (mrestrict H5 M6 = M6v) in VIS6.
assert (BI6 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PM.parser_own s) M6 model6 LK4 cr Aw4).
{ apply (PMAUK.binv_piece L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 2 LK2 M2 model2 cr (PM.parser_own s) G
WR (PM.parser_own s) M4 model5 LK4 cr Aw4 M6 model6 W6 BI5 HH6 AM6 MRT6 MGM6 FR6).
intros a Wa. right; right. change (ff_bytes 2 / 8) with 32. unfold W6 in Wa. unfold SB. clear - Wa; lia. }
destruct (PK M4 M6 W6 src4 sm4 FR6 ltac:(intros a Wa; right; right; unfold W6 in Wa; unfold SB; clear - Wa; lia) QC4 PA4 IA4 SP4) as (PA6 & IA6 & SP6).
assert (U86 : L5.u8_at RSEGS M6 (F / 8 + 48 / 8 + 2147450880) 1).
{ change (48 / 8) with 6. replace (F / 8 + 6 + 2147450880) with (F / 8 + 2147450886) by (clear; lia).
apply (proj1 (L5A.u8_at_vis H5 M6 (F / 8 + 2147450886) 1 (L5A.avis_sub H5 (F / 8 + SB) 32 (F / 8 + 2147450886) 1 VSH5 ltac:(unfold SB; clear; lia) ltac:(unfold SB; clear; lia))
ltac:(clear - Q0f GFR; lia) ltac:(clear - GFR; lia))).
rewrite VIS6. exact C60. }
assert (DEF6 : L5.defined M6 (F + 48) 1).
{ apply (L5.defined_grows M4 M6 _ _ MGM6). apply (proj1 (L5A.defined_vis H5 M4 (F + 48) 1 (L5A.avis_sub H5 F 256 (F + 48) 1 VF5 ltac:(clear; lia) ltac:(clear; lia)))).
apply (L5.defined_sub MV5 F 256); [exact FD5| clear; lia| clear; lia]. }
apply (RD 0xaffbc 48 1 1 fx6 R6 M6 model6 LK4 Aw4 src4 sm4 ltac:(split; [clear; lia| reflexivity]) BI6 QC4 PA6 IA6 SP6 ST4).
{ exact A61. } { rewrite (KS6 2%nat) by inl. exact K52. }
{ intros j Hj. rewrite (KS6 j) by (revert j Hj; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity). apply K534. revert j Hj. apply (L5K.incl_b [3; 4]%nat). vm_compute. reflexivity. }
{ exact A610. } { exact A611. } { exact A612. }
{ clear; lia. } { clear; lia. } { reflexivity. } { right; split; [clear; lia| reflexivity]. }
{ exact U86. } { exact DEF6. }
intros fx7 R7 M7 model7 LK7 Aw7 src7 sm7 dd7 BI7 RP7 Yd7 Hdd7 CONS7 DEFd7 RM17 RM07 QC7 PA7 IA7 SP7 ST7.
assert (R7c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R7 (reg j) = getr R6 (reg j))
by (intros j Hj; exact (L5SAR.cs_of_preserved R6 R7 j RP7 Hj)).
assert (K72 : getr R7 (reg 2) = Z_to_bv 64 (sp - 128)) by (rewrite (R7c 2%nat) by inl; rewrite (KS6 2%nat) by inl; exact K52).
assert (K78 : getr R7 (reg 8) = Z_to_bv 64 sp) by (rewrite (R7c 8%nat) by inl; rewrite (KS6 8%nat) by inl; exact K58).
assert (K79 : getr R7 (reg 9) = Z_to_bv 64 (sp - 128)) by (rewrite (R7c 9%nat) by inl; rewrite (KS6 9%nat) by inl; exact K59).
assert (K718 : getr R7 (reg 18) = Z_to_bv 64 F) by (rewrite (R7c 18%nat) by inl; rewrite (KS6 18%nat) by inl; exact K518).
assert (K719 : getr R7 (reg 19) = Z_to_bv 64 op) by (rewrite (R7c 19%nat) by inl; rewrite (KS6 19%nat) by inl; exact K519).
assert (K720 : getr R7 (reg 20) = Z_to_bv 64 oec) by (rewrite (R7c 20%nat) by inl; rewrite (KS6 20%nat) by inl; exact K520).
assert (K721 : getr R7 (reg 21) = Z_to_bv 64 (op + 24)) by (rewrite (R7c 21%nat) by inl; rewrite (KS6 21%nat) by inl; exact K521).
assert (K724 : getr R7 (reg 24) = Z_to_bv 64 ((F / 8) + 2147450880)) by (rewrite (R7c 24%nat) by inl; rewrite (KS6 24%nat) by inl; exact K524).
assert (K725 : getr R7 (reg 25) = Z_to_bv 64 F) by (rewrite (R7c 25%nat) by inl; rewrite (KS6 25%nat) by inl; exact K525).
assert (K726 : getr R7 (reg 26) = Z_to_bv 64 2147450880) by (rewrite (R7c 26%nat) by inl; rewrite (KS6 26%nat) by inl; exact K526).
assert (K722 : getr R7 (reg 22) = Z_to_bv 64 1) by (rewrite (R7c 22%nat) by inl; exact A622).
assert (K723 : getr R7 (reg 23) = Z_to_bv 64 (F + 48)) by (rewrite (R7c 23%nat) by inl; exact A623).
assert (K734 : forall j, In j [3; 4; 27]%nat -> getr R7 (reg j) = getr R (reg j)).
{ intros j Hj. rewrite (R7c j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity).
rewrite (KS6 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity). apply K534. exact Hj. }
clear R7c.
assert (UN7 : PM.unread src7 sm7 < PM.unread (PM.p_src s) sm) by (unfold PMSPA.consumed in CONS7; clear - CONS7 UN4 Hdd7; lia).
set (H7 := ahid Aw7 model7) in *. set (MV7 := mrestrict H7 M7) in *.
destruct (PMAUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 22528 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 2 LK2 M2 model2 cr (PM.parser_own s) G
WR (PM.parser_own s) M7 model7 LK7 cr Aw7 BI7) as ((WS7 & _ & _ & _ & _) & OWN7 & (FD7 & FW7 & FSW7 & FLC7 & FLW7) & (FLCc7 & FLV7 & VF7 & VS7 & VSH7)).
change (ff_bytes 2) with 256 in *. change (256 / 8) with 32 in *. replace (F + 256 - 8) with (F + 248) in FLC7 by (clear; lia).
destruct (Z.eq_dec dd7 1) as [D7|D7].
-
clear CONS7. subst dd7.
assert (DV7 : L5.defined MV7 (F + 48) 1).
{ apply (proj2 (L5A.defined_vis H7 M7 (F + 48) 1 (L5A.avis_sub H7 F 256 (F + 48) 1 VF7 ltac:(clear; lia) ltac:(clear; lia)))). exact DEFd7. }
cfeed P (PMAGL2.aglVi_conc fx7 R7 MV7 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMAGL2.aligned; assumption]).
destruct P as (fx8 & R8 & M8v & MG8 & _ & FRZ8 & MS8 & KS8).
assert (E8 : M8v = MV7) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ8; exact Ha). subst M8v.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK7 cr Aw7 M7 model7 fx7 fx8 R7 0xaffbc R8 0xaffc4 MV7 K (proj1 BI7) (proj1 (proj2 BI7)) MS8 (fun x Hx => Hx) (fun a Ha => eq_refl)).
intros M8 model8 HH8 AM8 MRT8 HID8 VIS8 MGM8 FR8.
assert (E8 : M8 = M7) by (apply L5SAR.mem_eq_of_agree; exact FR8). subst M8.
pose proof (PMAUK.binv_model L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PM.parser_own s) M7 model7 LK7 cr Aw7 model8 BI7 HH8 AM8 MRT8) as BI8.
pose proof (bv_unsigned_in_range 64 (getr R8 (reg 10))) as B810. change (bv_modulus 64) with (2 ^ 64) in B810.
assert (K810 : getr R8 (reg 10) = Z_to_bv 64 (bv_unsigned (getr R8 (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
destruct (Z_lt_dec (bv_unsigned (getr R8 (reg 10))) 9223372036854775808) as [Vp|Vn].
+ apply (OKP 0xaffc4 (XS (fun _ => 1) (fun F => F + 48)) fx8 R8 M7 model8 LK7 Aw7 src7 sm7 si_run).
{ exists (bv_unsigned (getr R8 (reg 10))). split; [clear - B810 Vp; lia|]. split; [exact K810|].
split; [rewrite (KS8 22%nat) by inl; exact K722| rewrite (KS8 23%nat) by inl; exact K723]. }
all: first [exact BI8 | exact QC7 | exact PA7 | exact IA7 | exact SP7 | exact ST7 | exact UN7 | (rewrite (KS8 _) by inl; assumption)
| (intros j Hj; rewrite (KS8 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity); apply K734; exact Hj) ].
+ assert (VN : 9223372036854775808 <= bv_unsigned (getr R8 (reg 10)) <= 18446744073709551615) by (clear - B810 Vn; lia).
set (H8 := ahid Aw7 model8) in *. set (MV8 := mrestrict H8 M7) in *.
cfeed P (PMAGL4.aglSiN_conc fx8 R8 MV8 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl
| 49%nat => bv_unsigned (getr R8 (reg 10)) | _ => 0 end)) ltac:(first [assumption | (rewrite (KS8 _) by inl; assumption)]).
destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & Z1 & Z10 & Z11 & _).
assert (E9 : M9v = MV8) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ9; exact Ha). subst M9v.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK7 cr Aw7 M7 model8 fx8 fx9 R8 0xaffc4 R9 0xae974 MV8 K (proj1 BI8) (proj1 (proj2 BI8)) MS9 (fun x Hx => Hx) (fun a Ha => eq_refl)).
intros M9 model9 HH9 AM9 MRT9 HID9 VIS9 MGM9 FR9.
assert (E9 : M9 = M7) by (apply L5SAR.mem_eq_of_agree; exact FR9). subst M9.
pose proof (PMAUK.binv_model L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PM.parser_own s) M7 model8 LK7 cr Aw7 model9 BI8 HH9 AM9 MRT9) as BI9.
apply (ERRP 0xaffd8 4 fx9 R9 M7 model9 LK7 Aw7 src7 sm7 zi_run ltac:(split; [clear; lia| reflexivity]) ltac:(clear; lia) BI9 QC7 PA7 IA7 SP7 ST7).
all: first [ exact Z1 | exact Z10 | exact Z11 | (rewrite (KS9 _) by inl; rewrite (KS8 _) by inl; assumption)
| (intros j Hj; rewrite (KS9 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity);
rewrite (KS8 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity); apply K734; exact Hj) ].
-
assert (D70 : dd7 = 0) by (clear - Hdd7 D7; lia). clear CONS7. subst dd7.
cfeed P (PMAGL2.aglNi_conc fx7 R7 MV7 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => 0 | _ => 0 end)) ltac:(first [assumption]).
destruct P as (fx8 & R8 & M8v & MG8 & _ & FRZ8 & MS8 & KS8 & Z1 & Z10 & Z11).
assert (E8 : M8v = MV7) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ8; exact Ha). subst M8v.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK7 cr Aw7 M7 model7 fx7 fx8 R7 0xaffbc R8 0xae974 MV7 K (proj1 BI7) (proj1 (proj2 BI7)) MS8 (fun x Hx => Hx) (fun a Ha => eq_refl)).
intros M8 model8 HH8 AM8 MRT8 HID8 VIS8 MGM8 FR8.
assert (E8 : M8 = M7) by (apply L5SAR.mem_eq_of_agree; exact FR8). subst M8.
pose proof (PMAUK.binv_model L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PM.parser_own s) M7 model7 LK7 cr Aw7 model8 BI7 HH8 AM8 MRT8) as BI8.
apply (ERRP 0xaffd8 1 fx8 R8 M7 model8 LK7 Aw7 src7 sm7 zi_run ltac:(split; [clear; lia| reflexivity]) ltac:(clear; lia) BI8 QC7 PA7 IA7 SP7 ST7).
all: first [ exact Z1 | exact Z10 | exact Z11 | (rewrite (KS8 _) by inl; assumption)
| (intros j Hj; rewrite (KS8 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity); apply K734; exact Hj) ]. }
destruct (Z.eq_dec b 85) as [BtU|BtU].
{
subst b.
cfeed P (PMAGL1.aglTU_conc fx5 R5' MV5 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMAGL1.aligned; assumption]).
destruct P as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & MS6 & KS6 & A61 & A610 & A611 & A612 & A622 & C60).
set (W6 := fun a => F / 8 + 2147450888 <= a < F / 8 + 2147450888 + 1).
apply (L5SAR.apiece L ar C HI LYa HIok _ FF' LK4 cr Aw4 M4 model5 fx5 fx6 R5' 0xaff80 R6 0xaf334 M6v W6 K (proj1 BI5) (proj1 (proj2 BI5)) MS6 MG6).
{ intros a Ha Nn. apply FRZ6; [exact Ha| intros X; apply Nn; unfold W6; clear - X; lia]. }
{ intros a Ha Wa. unfold W6 in Wa. split.
- apply (L5SAR.fframe_shadow_client L ar _ FF' 0 0 F 2 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 2) with 256.
unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - Wa; lia.
- assert (DF0 : 0 <= F / 8) by (apply Z.div_pos; clear - Q3; lia). clear - Wa DF0; lia. }
intros M6 model6 HH6 AM6 MRT6 HID6 VIS6 MGM6 FR6 VV6. change (mrestrict H5 M6 = M6v) in VIS6.
assert (BI6 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PM.parser_own s) M6 model6 LK4 cr Aw4).
{ apply (PMAUK.binv_piece L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 2 LK2 M2 model2 cr (PM.parser_own s) G
WR (PM.parser_own s) M4 model5 LK4 cr Aw4 M6 model6 W6 BI5 HH6 AM6 MRT6 MGM6 FR6).
intros a Wa. right; right. change (ff_bytes 2 / 8) with 32. unfold W6 in Wa. unfold SB. clear - Wa; lia. }
destruct (PK M4 M6 W6 src4 sm4 FR6 ltac:(intros a Wa; right; right; unfold W6 in Wa; unfold SB; clear - Wa; lia) QC4 PA4 IA4 SP4) as (PA6 & IA6 & SP6).
assert (U86 : L5.u8_at RSEGS M6 (F / 8 + 64 / 8 + 2147450880) 1).
{ change (64 / 8) with 8. replace (F / 8 + 8 + 2147450880) with (F / 8 + 2147450888) by (clear; lia).
apply (proj1 (L5A.u8_at_vis H5 M6 (F / 8 + 2147450888) 1 (L5A.avis_sub H5 (F / 8 + SB) 32 (F / 8 + 2147450888) 1 VSH5 ltac:(unfold SB; clear; lia) ltac:(unfold SB; clear; lia))
ltac:(clear - Q0f GFR; lia) ltac:(clear - GFR; lia))).
rewrite VIS6. exact C60. }
assert (DEF6 : L5.defined M6 (F + 64) 1).
{ apply (L5.defined_grows M4 M6 _ _ MGM6). apply (proj1 (L5A.defined_vis H5 M4 (F + 64) 1 (L5A.avis_sub H5 F 256 (F + 64) 1 VF5 ltac:(clear; lia) ltac:(clear; lia)))).
apply (L5.defined_sub MV5 F 256); [exact FD5| clear; lia| clear; lia]. }
apply (RD 0xb00f0 64 1 1 fx6 R6 M6 model6 LK4 Aw4 src4 sm4 ltac:(split; [clear; lia| reflexivity]) BI6 QC4 PA6 IA6 SP6 ST4).
{ exact A61. } { rewrite (KS6 2%nat) by inl. exact K52. }
{ intros j Hj. rewrite (KS6 j) by (revert j Hj; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity). apply K534. revert j Hj. apply (L5K.incl_b [3; 4]%nat). vm_compute. reflexivity. }
{ exact A610. } { exact A611. } { exact A612. }
{ clear; lia. } { clear; lia. } { reflexivity. } { right; split; [clear; lia| reflexivity]. }
{ exact U86. } { exact DEF6. }
intros fx7 R7 M7 model7 LK7 Aw7 src7 sm7 dd7 BI7 RP7 Yd7 Hdd7 CONS7 DEFd7 RM17 RM07 QC7 PA7 IA7 SP7 ST7.
assert (R7c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R7 (reg j) = getr R6 (reg j))
by (intros j Hj; exact (L5SAR.cs_of_preserved R6 R7 j RP7 Hj)).
assert (K72 : getr R7 (reg 2) = Z_to_bv 64 (sp - 128)) by (rewrite (R7c 2%nat) by inl; rewrite (KS6 2%nat) by inl; exact K52).
assert (K78 : getr R7 (reg 8) = Z_to_bv 64 sp) by (rewrite (R7c 8%nat) by inl; rewrite (KS6 8%nat) by inl; exact K58).
assert (K79 : getr R7 (reg 9) = Z_to_bv 64 (sp - 128)) by (rewrite (R7c 9%nat) by inl; rewrite (KS6 9%nat) by inl; exact K59).
assert (K718 : getr R7 (reg 18) = Z_to_bv 64 F) by (rewrite (R7c 18%nat) by inl; rewrite (KS6 18%nat) by inl; exact K518).
assert (K719 : getr R7 (reg 19) = Z_to_bv 64 op) by (rewrite (R7c 19%nat) by inl; rewrite (KS6 19%nat) by inl; exact K519).
assert (K720 : getr R7 (reg 20) = Z_to_bv 64 oec) by (rewrite (R7c 20%nat) by inl; rewrite (KS6 20%nat) by inl; exact K520).
assert (K721 : getr R7 (reg 21) = Z_to_bv 64 (op + 24)) by (rewrite (R7c 21%nat) by inl; rewrite (KS6 21%nat) by inl; exact K521).
assert (K724 : getr R7 (reg 24) = Z_to_bv 64 ((F / 8) + 2147450880)) by (rewrite (R7c 24%nat) by inl; rewrite (KS6 24%nat) by inl; exact K524).
assert (K725 : getr R7 (reg 25) = Z_to_bv 64 F) by (rewrite (R7c 25%nat) by inl; rewrite (KS6 25%nat) by inl; exact K525).
assert (K726 : getr R7 (reg 26) = Z_to_bv 64 2147450880) by (rewrite (R7c 26%nat) by inl; rewrite (KS6 26%nat) by inl; exact K526).
assert (K722 : getr R7 (reg 22) = Z_to_bv 64 (F + 64)) by (rewrite (R7c 22%nat) by inl; exact A622).
assert (K734 : forall j, In j [3; 4; 27]%nat -> getr R7 (reg j) = getr R (reg j)).
{ intros j Hj. rewrite (R7c j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity).
rewrite (KS6 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity). apply K534. exact Hj. }
clear R7c.
assert (UN7 : PM.unread src7 sm7 < PM.unread (PM.p_src s) sm) by (unfold PMSPA.consumed in CONS7; clear - CONS7 UN4 Hdd7; lia).
set (H7 := ahid Aw7 model7) in *. set (MV7 := mrestrict H7 M7) in *.
destruct (PMAUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 22528 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 2 LK2 M2 model2 cr (PM.parser_own s) G
WR (PM.parser_own s) M7 model7 LK7 cr Aw7 BI7) as ((WS7 & _ & _ & _ & _) & OWN7 & (FD7 & FW7 & FSW7 & FLC7 & FLW7) & (FLCc7 & FLV7 & VF7 & VS7 & VSH7)).
change (ff_bytes 2) with 256 in *. change (256 / 8) with 32 in *. replace (F + 256 - 8) with (F + 248) in FLC7 by (clear; lia).
destruct (Z.eq_dec dd7 1) as [D7|D7].
-
clear CONS7. subst dd7.
assert (DV7 : L5.defined MV7 (F + 64) 1).
{ apply (proj2 (L5A.defined_vis H7 M7 (F + 64) 1 (L5A.avis_sub H7 F 256 (F + 64) 1 VF7 ltac:(clear; lia) ltac:(clear; lia)))). exact DEFd7. }
apply (OKP 0xb00f0 XVU fx7 R7 M7 model7 LK7 Aw7 src7 sm7 vu_run).
{ split; [exact Yd7| split; [exact K722| exact DV7]]. }
all: first [exact BI7 | exact QC7 | exact PA7 | exact IA7 | exact SP7 | exact ST7 | exact UN7 | assumption].
-
assert (D70 : dd7 = 0) by (clear - Hdd7 D7; lia). clear CONS7. subst dd7.
cfeed P (PMAGL2.aglNU_conc fx7 R7 MV7 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => 0 | _ => 0 end)) ltac:(first [assumption]).
destruct P as (fx8 & R8 & M8v & MG8 & _ & FRZ8 & MS8 & KS8 & Z1 & Z10 & Z11).
assert (E8 : M8v = MV7) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ8; exact Ha). subst M8v.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK7 cr Aw7 M7 model7 fx7 fx8 R7 0xb00f0 R8 0xae974 MV7 K (proj1 BI7) (proj1 (proj2 BI7)) MS8 (fun x Hx => Hx) (fun a Ha => eq_refl)).
intros M8 model8 HH8 AM8 MRT8 HID8 VIS8 MGM8 FR8.
assert (E8 : M8 = M7) by (apply L5SAR.mem_eq_of_agree; exact FR8). subst M8.
pose proof (PMAUK.binv_model L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PM.parser_own s) M7 model7 LK7 cr Aw7 model8 BI7 HH8 AM8 MRT8) as BI8.
apply (ERRP 0xb036c 1 fx8 R8 M7 model8 LK7 Aw7 src7 sm7 zU_run ltac:(split; [clear; lia| reflexivity]) ltac:(clear; lia) BI8 QC7 PA7 IA7 SP7 ST7).
all: first [ exact Z1 | exact Z10 | exact Z11 | (rewrite (KS8 _) by inl; assumption)
| (intros j Hj; rewrite (KS8 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity); apply K734; exact Hj) ]. }
destruct (Z.eq_dec b 108) as [Btl|Btl].
{
subst b.
cfeed P (PMAGL1.aglTl_conc fx5 R5' MV5 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMAGL1.aligned; assumption]).
destruct P as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & MS6 & KS6 & A61 & A610 & A611 & A612 & A622 & A623 & C60).
set (W6 := fun a => F / 8 + 2147450892 <= a < F / 8 + 2147450892 + 1).
apply (L5SAR.apiece L ar C HI LYa HIok _ FF' LK4 cr Aw4 M4 model5 fx5 fx6 R5' 0xaff80 R6 0xaf334 M6v W6 K (proj1 BI5) (proj1 (proj2 BI5)) MS6 MG6).
{ intros a Ha Nn. apply FRZ6; [exact Ha| intros X; apply Nn; unfold W6; clear - X; lia]. }
{ intros a Ha Wa. unfold W6 in Wa. split.
- apply (L5SAR.fframe_shadow_client L ar _ FF' 0 0 F 2 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 2) with 256.
unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - Wa; lia.
- assert (DF0 : 0 <= F / 8) by (apply Z.div_pos; clear - Q3; lia). clear - Wa DF0; lia. }
intros M6 model6 HH6 AM6 MRT6 HID6 VIS6 MGM6 FR6 VV6. change (mrestrict H5 M6 = M6v) in VIS6.
assert (BI6 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PM.parser_own s) M6 model6 LK4 cr Aw4).
{ apply (PMAUK.binv_piece L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 2 LK2 M2 model2 cr (PM.parser_own s) G
WR (PM.parser_own s) M4 model5 LK4 cr Aw4 M6 model6 W6 BI5 HH6 AM6 MRT6 MGM6 FR6).
intros a Wa. right; right. change (ff_bytes 2 / 8) with 32. unfold W6 in Wa. unfold SB. clear - Wa; lia. }
destruct (PK M4 M6 W6 src4 sm4 FR6 ltac:(intros a Wa; right; right; unfold W6 in Wa; unfold SB; clear - Wa; lia) QC4 PA4 IA4 SP4) as (PA6 & IA6 & SP6).
assert (U86 : L5.u8_at RSEGS M6 (F / 8 + 96 / 8 + 2147450880) 4).
{ change (96 / 8) with 12. replace (F / 8 + 12 + 2147450880) with (F / 8 + 2147450892) by (clear; lia).
apply (proj1 (L5A.u8_at_vis H5 M6 (F / 8 + 2147450892) 4 (L5A.avis_sub H5 (F / 8 + SB) 32 (F / 8 + 2147450892) 1 VSH5 ltac:(unfold SB; clear; lia) ltac:(unfold SB; clear; lia))
ltac:(clear - Q0f GFR; lia) ltac:(clear - GFR; lia))).
rewrite VIS6. exact C60. }
assert (DEF6 : L5.defined M6 (F + 96) 4).
{ apply (L5.defined_grows M4 M6 _ _ MGM6). apply (proj1 (L5A.defined_vis H5 M4 (F + 96) 4 (L5A.avis_sub H5 F 256 (F + 96) 4 VF5 ltac:(clear; lia) ltac:(clear; lia)))).
apply (L5.defined_sub MV5 F 256); [exact FD5| clear; lia| clear; lia]. }
apply (RD 0xb0118 96 4 4 fx6 R6 M6 model6 LK4 Aw4 src4 sm4 ltac:(split; [clear; lia| reflexivity]) BI6 QC4 PA6 IA6 SP6 ST4).
{ exact A61. } { rewrite (KS6 2%nat) by inl. exact K52. }
{ intros j Hj. rewrite (KS6 j) by (revert j Hj; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity). apply K534. revert j Hj. apply (L5K.incl_b [3; 4]%nat). vm_compute. reflexivity. }
{ exact A610. } { exact A611. } { exact A612. }
{ clear; lia. } { clear; lia. } { reflexivity. } { right; split; [clear; lia| reflexivity]. }
{ exact U86. } { exact DEF6. }
intros fx7 R7 M7 model7 LK7 Aw7 src7 sm7 dd7 BI7 RP7 Yd7 Hdd7 CONS7 DEFd7 RM17 RM07 QC7 PA7 IA7 SP7 ST7.
assert (R7c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R7 (reg j) = getr R6 (reg j))
by (intros j Hj; exact (L5SAR.cs_of_preserved R6 R7 j RP7 Hj)).
assert (K72 : getr R7 (reg 2) = Z_to_bv 64 (sp - 128)) by (rewrite (R7c 2%nat) by inl; rewrite (KS6 2%nat) by inl; exact K52).
assert (K78 : getr R7 (reg 8) = Z_to_bv 64 sp) by (rewrite (R7c 8%nat) by inl; rewrite (KS6 8%nat) by inl; exact K58).
assert (K79 : getr R7 (reg 9) = Z_to_bv 64 (sp - 128)) by (rewrite (R7c 9%nat) by inl; rewrite (KS6 9%nat) by inl; exact K59).
assert (K718 : getr R7 (reg 18) = Z_to_bv 64 F) by (rewrite (R7c 18%nat) by inl; rewrite (KS6 18%nat) by inl; exact K518).
assert (K719 : getr R7 (reg 19) = Z_to_bv 64 op) by (rewrite (R7c 19%nat) by inl; rewrite (KS6 19%nat) by inl; exact K519).
assert (K720 : getr R7 (reg 20) = Z_to_bv 64 oec) by (rewrite (R7c 20%nat) by inl; rewrite (KS6 20%nat) by inl; exact K520).
assert (K721 : getr R7 (reg 21) = Z_to_bv 64 (op + 24)) by (rewrite (R7c 21%nat) by inl; rewrite (KS6 21%nat) by inl; exact K521).
assert (K724 : getr R7 (reg 24) = Z_to_bv 64 ((F / 8) + 2147450880)) by (rewrite (R7c 24%nat) by inl; rewrite (KS6 24%nat) by inl; exact K524).
assert (K725 : getr R7 (reg 25) = Z_to_bv 64 F) by (rewrite (R7c 25%nat) by inl; rewrite (KS6 25%nat) by inl; exact K525).
assert (K726 : getr R7 (reg 26) = Z_to_bv 64 2147450880) by (rewrite (R7c 26%nat) by inl; rewrite (KS6 26%nat) by inl; exact K526).
assert (K722 : getr R7 (reg 22) = Z_to_bv 64 4) by (rewrite (R7c 22%nat) by inl; exact A622).
assert (K723 : getr R7 (reg 23) = Z_to_bv 64 (F + 96)) by (rewrite (R7c 23%nat) by inl; exact A623).
assert (K734 : forall j, In j [3; 4; 27]%nat -> getr R7 (reg j) = getr R (reg j)).
{ intros j Hj. rewrite (R7c j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity).
rewrite (KS6 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity). apply K534. exact Hj. }
clear R7c.
assert (UN7 : PM.unread src7 sm7 < PM.unread (PM.p_src s) sm) by (unfold PMSPA.consumed in CONS7; clear - CONS7 UN4 Hdd7; lia).
set (H7 := ahid Aw7 model7) in *. set (MV7 := mrestrict H7 M7) in *.
destruct (PMAUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 22528 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 2 LK2 M2 model2 cr (PM.parser_own s) G
WR (PM.parser_own s) M7 model7 LK7 cr Aw7 BI7) as ((WS7 & _ & _ & _ & _) & OWN7 & (FD7 & FW7 & FSW7 & FLC7 & FLW7) & (FLCc7 & FLV7 & VF7 & VS7 & VSH7)).
change (ff_bytes 2) with 256 in *. change (256 / 8) with 32 in *. replace (F + 256 - 8) with (F + 248) in FLC7 by (clear; lia).
destruct (Z.eq_dec dd7 4) as [D7|D7].
-
clear CONS7. subst dd7.
assert (DV7 : L5.defined MV7 (F + 96) 4).
{ apply (proj2 (L5A.defined_vis H7 M7 (F + 96) 4 (L5A.avis_sub H7 F 256 (F + 96) 4 VF7 ltac:(clear; lia) ltac:(clear; lia)))). exact DEFd7. }
cfeed P (PMAGL2.aglVl_conc fx7 R7 MV7 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMAGL2.aligned; assumption]).
destruct P as (fx8 & R8 & M8v & MG8 & _ & FRZ8 & MS8 & KS8).
assert (E8 : M8v = MV7) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ8; exact Ha). subst M8v.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK7 cr Aw7 M7 model7 fx7 fx8 R7 0xb0118 R8 0xb014c MV7 K (proj1 BI7) (proj1 (proj2 BI7)) MS8 (fun x Hx => Hx) (fun a Ha => eq_refl)).
intros M8 model8 HH8 AM8 MRT8 HID8 VIS8 MGM8 FR8.
assert (E8 : M8 = M7) by (apply L5SAR.mem_eq_of_agree; exact FR8). subst M8.
pose proof (PMAUK.binv_model L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PM.parser_own s) M7 model7 LK7 cr Aw7 model8 BI7 HH8 AM8 MRT8) as BI8.
pose proof (bv_unsigned_in_range 64 (getr R8 (reg 10))) as B810. change (bv_modulus 64) with (2 ^ 64) in B810.
assert (K810 : getr R8 (reg 10) = Z_to_bv 64 (bv_unsigned (getr R8 (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
destruct (Z_lt_dec (bv_unsigned (getr R8 (reg 10))) 9223372036854775808) as [Vp|Vn].
+ apply (OKP 0xb014c (XS (fun _ => 4) (fun F => F + 96)) fx8 R8 M7 model8 LK7 Aw7 src7 sm7 sl_run).
{ exists (bv_unsigned (getr R8 (reg 10))). split; [clear - B810 Vp; lia|]. split; [exact K810|].
split; [rewrite (KS8 22%nat) by inl; exact K722| rewrite (KS8 23%nat) by inl; exact K723]. }
all: first [exact BI8 | exact QC7 | exact PA7 | exact IA7 | exact SP7 | exact ST7 | exact UN7 | (rewrite (KS8 _) by inl; assumption)
| (intros j Hj; rewrite (KS8 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity); apply K734; exact Hj) ].
+ assert (VN : 9223372036854775808 <= bv_unsigned (getr R8 (reg 10)) <= 18446744073709551615) by (clear - B810 Vn; lia).
set (H8 := ahid Aw7 model8) in *. set (MV8 := mrestrict H8 M7) in *.
cfeed P (PMAGL4.aglSlN_conc fx8 R8 MV8 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl
| 49%nat => bv_unsigned (getr R8 (reg 10)) | _ => 0 end)) ltac:(first [assumption | (rewrite (KS8 _) by inl; assumption)]).
destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & Z1 & Z10 & Z11).
assert (E9 : M9v = MV8) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ9; exact Ha). subst M9v.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK7 cr Aw7 M7 model8 fx8 fx9 R8 0xb014c R9 0xae974 MV8 K (proj1 BI8) (proj1 (proj2 BI8)) MS9 (fun x Hx => Hx) (fun a Ha => eq_refl)).
intros M9 model9 HH9 AM9 MRT9 HID9 VIS9 MGM9 FR9.
assert (E9 : M9 = M7) by (apply L5SAR.mem_eq_of_agree; exact FR9). subst M9.
pose proof (PMAUK.binv_model L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PM.parser_own s) M7 model8 LK7 cr Aw7 model9 BI8 HH9 AM9 MRT9) as BI9.
apply (ERRP 0xb02fc 4 fx9 R9 M7 model9 LK7 Aw7 src7 sm7 zl_run ltac:(split; [clear; lia| reflexivity]) ltac:(clear; lia) BI9 QC7 PA7 IA7 SP7 ST7).
all: first [ exact Z1 | exact Z10 | exact Z11 | (rewrite (KS9 _) by inl; rewrite (KS8 _) by inl; assumption)
| (intros j Hj; rewrite (KS9 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity);
rewrite (KS8 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity); apply K734; exact Hj) ].
-
assert (D7r : 0 <= dd7 <= 3) by (clear - Hdd7 D7; lia). assert (D7b : 0 <= dd7 < 2 ^ 64) by (clear - Hdd7; lia).
cfeed P (PMAGL2.aglNl_conc fx7 R7 MV7 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => dd7 | _ => 0 end)) ltac:(first [assumption]).
destruct P as (fx8 & R8 & M8v & MG8 & _ & FRZ8 & MS8 & KS8 & Z1 & Z10 & Z11 & _).
assert (E8 : M8v = MV7) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ8; exact Ha). subst M8v.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK7 cr Aw7 M7 model7 fx7 fx8 R7 0xb0118 R8 0xae974 MV7 K (proj1 BI7) (proj1 (proj2 BI7)) MS8 (fun x Hx => Hx) (fun a Ha => eq_refl)).
intros M8 model8 HH8 AM8 MRT8 HID8 VIS8 MGM8 FR8.
assert (E8 : M8 = M7) by (apply L5SAR.mem_eq_of_agree; exact FR8). subst M8.
pose proof (PMAUK.binv_model L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PM.parser_own s) M7 model7 LK7 cr Aw7 model8 BI7 HH8 AM8 MRT8) as BI8.
apply (ERRP 0xb02fc 1 fx8 R8 M7 model8 LK7 Aw7 src7 sm7 zl_run ltac:(split; [clear; lia| reflexivity]) ltac:(clear; lia) BI8 QC7 PA7 IA7 SP7 ST7).
all: first [ exact Z1 | exact Z10 | exact Z11 | (rewrite (KS8 _) by inl; assumption)
| (intros j Hj; rewrite (KS8 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity); apply K734; exact Hj) ]. }
destruct (Z.eq_dec b 73) as [BtI|BtI].
{
subst b.
cfeed P (PMAGL1.aglTI_conc fx5 R5' MV5 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMAGL1.aligned; assumption]).
destruct P as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & MS6 & KS6 & A61 & A610 & A611 & A612 & A622 & A623 & C60).
set (W6 := fun a => F / 8 + 2147450890 <= a < F / 8 + 2147450890 + 1).
apply (L5SAR.apiece L ar C HI LYa HIok _ FF' LK4 cr Aw4 M4 model5 fx5 fx6 R5' 0xaff80 R6 0xaf334 M6v W6 K (proj1 BI5) (proj1 (proj2 BI5)) MS6 MG6).
{ intros a Ha Nn. apply FRZ6; [exact Ha| intros X; apply Nn; unfold W6; clear - X; lia]. }
{ intros a Ha Wa. unfold W6 in Wa. split.
- apply (L5SAR.fframe_shadow_client L ar _ FF' 0 0 F 2 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 2) with 256.
unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - Wa; lia.
- assert (DF0 : 0 <= F / 8) by (apply Z.div_pos; clear - Q3; lia). clear - Wa DF0; lia. }
intros M6 model6 HH6 AM6 MRT6 HID6 VIS6 MGM6 FR6 VV6. change (mrestrict H5 M6 = M6v) in VIS6.
assert (BI6 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PM.parser_own s) M6 model6 LK4 cr Aw4).
{ apply (PMAUK.binv_piece L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 2 LK2 M2 model2 cr (PM.parser_own s) G
WR (PM.parser_own s) M4 model5 LK4 cr Aw4 M6 model6 W6 BI5 HH6 AM6 MRT6 MGM6 FR6).
intros a Wa. right; right. change (ff_bytes 2 / 8) with 32. unfold W6 in Wa. unfold SB. clear - Wa; lia. }
destruct (PK M4 M6 W6 src4 sm4 FR6 ltac:(intros a Wa; right; right; unfold W6 in Wa; unfold SB; clear - Wa; lia) QC4 PA4 IA4 SP4) as (PA6 & IA6 & SP6).
assert (U86 : L5.u8_at RSEGS M6 (F / 8 + 80 / 8 + 2147450880) 2).
{ change (80 / 8) with 10. replace (F / 8 + 10 + 2147450880) with (F / 8 + 2147450890) by (clear; lia).
apply (proj1 (L5A.u8_at_vis H5 M6 (F / 8 + 2147450890) 2 (L5A.avis_sub H5 (F / 8 + SB) 32 (F / 8 + 2147450890) 1 VSH5 ltac:(unfold SB; clear; lia) ltac:(unfold SB; clear; lia))
ltac:(clear - Q0f GFR; lia) ltac:(clear - GFR; lia))).
rewrite VIS6. exact C60. }
assert (DEF6 : L5.defined M6 (F + 80) 2).
{ apply (L5.defined_grows M4 M6 _ _ MGM6). apply (proj1 (L5A.defined_vis H5 M4 (F + 80) 2 (L5A.avis_sub H5 F 256 (F + 80) 2 VF5 ltac:(clear; lia) ltac:(clear; lia)))).
apply (L5.defined_sub MV5 F 256); [exact FD5| clear; lia| clear; lia]. }
apply (RD 0xb0170 80 2 2 fx6 R6 M6 model6 LK4 Aw4 src4 sm4 ltac:(split; [clear; lia| reflexivity]) BI6 QC4 PA6 IA6 SP6 ST4).
{ exact A61. } { rewrite (KS6 2%nat) by inl. exact K52. }
{ intros j Hj. rewrite (KS6 j) by (revert j Hj; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity). apply K534. revert j Hj. apply (L5K.incl_b [3; 4]%nat). vm_compute. reflexivity. }
{ exact A610. } { exact A611. } { exact A612. }
{ clear; lia. } { clear; lia. } { reflexivity. } { right; split; [clear; lia| reflexivity]. }
{ exact U86. } { exact DEF6. }
intros fx7 R7 M7 model7 LK7 Aw7 src7 sm7 dd7 BI7 RP7 Yd7 Hdd7 CONS7 DEFd7 RM17 RM07 QC7 PA7 IA7 SP7 ST7.
assert (R7c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R7 (reg j) = getr R6 (reg j))
by (intros j Hj; exact (L5SAR.cs_of_preserved R6 R7 j RP7 Hj)).
assert (K72 : getr R7 (reg 2) = Z_to_bv 64 (sp - 128)) by (rewrite (R7c 2%nat) by inl; rewrite (KS6 2%nat) by inl; exact K52).
assert (K78 : getr R7 (reg 8) = Z_to_bv 64 sp) by (rewrite (R7c 8%nat) by inl; rewrite (KS6 8%nat) by inl; exact K58).
assert (K79 : getr R7 (reg 9) = Z_to_bv 64 (sp - 128)) by (rewrite (R7c 9%nat) by inl; rewrite (KS6 9%nat) by inl; exact K59).
assert (K718 : getr R7 (reg 18) = Z_to_bv 64 F) by (rewrite (R7c 18%nat) by inl; rewrite (KS6 18%nat) by inl; exact K518).
assert (K719 : getr R7 (reg 19) = Z_to_bv 64 op) by (rewrite (R7c 19%nat) by inl; rewrite (KS6 19%nat) by inl; exact K519).
assert (K720 : getr R7 (reg 20) = Z_to_bv 64 oec) by (rewrite (R7c 20%nat) by inl; rewrite (KS6 20%nat) by inl; exact K520).
assert (K721 : getr R7 (reg 21) = Z_to_bv 64 (op + 24)) by (rewrite (R7c 21%nat) by inl; rewrite (KS6 21%nat) by inl; exact K521).
assert (K724 : getr R7 (reg 24) = Z_to_bv 64 ((F / 8) + 2147450880)) by (rewrite (R7c 24%nat) by inl; rewrite (KS6 24%nat) by inl; exact K524).
assert (K725 : getr R7 (reg 25) = Z_to_bv 64 F) by (rewrite (R7c 25%nat) by inl; rewrite (KS6 25%nat) by inl; exact K525).
assert (K726 : getr R7 (reg 26) = Z_to_bv 64 2147450880) by (rewrite (R7c 26%nat) by inl; rewrite (KS6 26%nat) by inl; exact K526).
assert (K722 : getr R7 (reg 22) = Z_to_bv 64 (F + 80)) by (rewrite (R7c 22%nat) by inl; exact A622).
assert (K723 : getr R7 (reg 23) = Z_to_bv 64 2) by (rewrite (R7c 23%nat) by inl; exact A623).
assert (K734 : forall j, In j [3; 4; 27]%nat -> getr R7 (reg j) = getr R (reg j)).
{ intros j Hj. rewrite (R7c j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity).
rewrite (KS6 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity). apply K534. exact Hj. }
clear R7c.
assert (UN7 : PM.unread src7 sm7 < PM.unread (PM.p_src s) sm) by (unfold PMSPA.consumed in CONS7; clear - CONS7 UN4 Hdd7; lia).
set (H7 := ahid Aw7 model7) in *. set (MV7 := mrestrict H7 M7) in *.
destruct (PMAUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 22528 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 2 LK2 M2 model2 cr (PM.parser_own s) G
WR (PM.parser_own s) M7 model7 LK7 cr Aw7 BI7) as ((WS7 & _ & _ & _ & _) & OWN7 & (FD7 & FW7 & FSW7 & FLC7 & FLW7) & (FLCc7 & FLV7 & VF7 & VS7 & VSH7)).
change (ff_bytes 2) with 256 in *. change (256 / 8) with 32 in *. replace (F + 256 - 8) with (F + 248) in FLC7 by (clear; lia).
destruct (Z.eq_dec dd7 2) as [D7|D7].
-
clear CONS7. subst dd7.
assert (DV7 : L5.defined MV7 (F + 80) 2).
{ apply (proj2 (L5A.defined_vis H7 M7 (F + 80) 2 (L5A.avis_sub H7 F 256 (F + 80) 2 VF7 ltac:(clear; lia) ltac:(clear; lia)))). exact DEFd7. }
cfeed P (PMAGL2.aglVI_conc fx7 R7 MV7 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMAGL2.aligned; assumption]).
destruct P as (fx8 & R8 & M8v & MG8 & _ & FRZ8 & MS8 & KS8).
assert (E8 : M8v = MV7) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ8; exact Ha). subst M8v.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK7 cr Aw7 M7 model7 fx7 fx8 R7 0xb0170 R8 0xb0184 MV7 K (proj1 BI7) (proj1 (proj2 BI7)) MS8 (fun x Hx => Hx) (fun a Ha => eq_refl)).
intros M8 model8 HH8 AM8 MRT8 HID8 VIS8 MGM8 FR8.
assert (E8 : M8 = M7) by (apply L5SAR.mem_eq_of_agree; exact FR8). subst M8.
pose proof (PMAUK.binv_model L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PM.parser_own s) M7 model7 LK7 cr Aw7 model8 BI7 HH8 AM8 MRT8) as BI8.
pose proof (bv_unsigned_in_range 64 (getr R8 (reg 10))) as B810. change (bv_modulus 64) with (2 ^ 64) in B810.
assert (K810 : getr R8 (reg 10) = Z_to_bv 64 (bv_unsigned (getr R8 (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
destruct (Z_lt_dec (bv_unsigned (getr R8 (reg 10))) 9223372036854775808) as [Vp|Vn].
+ apply (OKP 0xb0184 (XS (fun F => F + 80) (fun _ => 2)) fx8 R8 M7 model8 LK7 Aw7 src7 sm7 sI_run).
{ exists (bv_unsigned (getr R8 (reg 10))). split; [clear - B810 Vp; lia|]. split; [exact K810|].
split; [rewrite (KS8 22%nat) by inl; exact K722| rewrite (KS8 23%nat) by inl; exact K723]. }
all: first [exact BI8 | exact QC7 | exact PA7 | exact IA7 | exact SP7 | exact ST7 | exact UN7 | (rewrite (KS8 _) by inl; assumption)
| (intros j Hj; rewrite (KS8 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity); apply K734; exact Hj) ].
+ assert (VN : 9223372036854775808 <= bv_unsigned (getr R8 (reg 10)) <= 18446744073709551615) by (clear - B810 Vn; lia).
set (H8 := ahid Aw7 model8) in *. set (MV8 := mrestrict H8 M7) in *.
cfeed P (PMAGL4.aglSIN_conc fx8 R8 MV8 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl
| 49%nat => bv_unsigned (getr R8 (reg 10)) | _ => 0 end)) ltac:(first [assumption | (rewrite (KS8 _) by inl; assumption)]).
destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & Z1 & Z10 & Z11).
assert (E9 : M9v = MV8) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ9; exact Ha). subst M9v.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK7 cr Aw7 M7 model8 fx8 fx9 R8 0xb0184 R9 0xae974 MV8 K (proj1 BI8) (proj1 (proj2 BI8)) MS9 (fun x Hx => Hx) (fun a Ha => eq_refl)).
intros M9 model9 HH9 AM9 MRT9 HID9 VIS9 MGM9 FR9.
assert (E9 : M9 = M7) by (apply L5SAR.mem_eq_of_agree; exact FR9). subst M9.
pose proof (PMAUK.binv_model L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PM.parser_own s) M7 model8 LK7 cr Aw7 model9 BI8 HH9 AM9 MRT9) as BI9.
apply (ERRP 0xb03a0 4 fx9 R9 M7 model9 LK7 Aw7 src7 sm7 zI_run ltac:(split; [clear; lia| reflexivity]) ltac:(clear; lia) BI9 QC7 PA7 IA7 SP7 ST7).
all: first [ exact Z1 | exact Z10 | exact Z11 | (rewrite (KS9 _) by inl; rewrite (KS8 _) by inl; assumption)
| (intros j Hj; rewrite (KS9 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity);
rewrite (KS8 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity); apply K734; exact Hj) ].
-
assert (D7r : 0 <= dd7 <= 1) by (clear - Hdd7 D7; lia). assert (D7b : 0 <= dd7 < 2 ^ 64) by (clear - Hdd7; lia).
cfeed P (PMAGL2.aglNI_conc fx7 R7 MV7 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => dd7 | _ => 0 end)) ltac:(first [assumption]).
destruct P as (fx8 & R8 & M8v & MG8 & _ & FRZ8 & MS8 & KS8 & Z1 & Z10 & Z11).
assert (E8 : M8v = MV7) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ8; exact Ha). subst M8v.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK7 cr Aw7 M7 model7 fx7 fx8 R7 0xb0170 R8 0xae974 MV7 K (proj1 BI7) (proj1 (proj2 BI7)) MS8 (fun x Hx => Hx) (fun a Ha => eq_refl)).
intros M8 model8 HH8 AM8 MRT8 HID8 VIS8 MGM8 FR8.
assert (E8 : M8 = M7) by (apply L5SAR.mem_eq_of_agree; exact FR8). subst M8.
pose proof (PMAUK.binv_model L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PM.parser_own s) M7 model7 LK7 cr Aw7 model8 BI7 HH8 AM8 MRT8) as BI8.
apply (ERRP 0xb03a0 1 fx8 R8 M7 model8 LK7 Aw7 src7 sm7 zI_run ltac:(split; [clear; lia| reflexivity]) ltac:(clear; lia) BI8 QC7 PA7 IA7 SP7 ST7).
all: first [ exact Z1 | exact Z10 | exact Z11 | (rewrite (KS8 _) by inl; assumption)
| (intros j Hj; rewrite (KS8 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity); apply K734; exact Hj) ]. }
destruct (Z.eq_dec b 76) as [BtL|BtL].
{
subst b.
cfeed P (PMAGL1.aglTL_conc fx5 R5' MV5 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMAGL1.aligned; assumption]).
destruct P as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & MS6 & KS6 & A61 & A610 & A611 & A612 & A622 & A623 & C60).
set (W6 := fun a => F / 8 + 2147450894 <= a < F / 8 + 2147450894 + 1).
apply (L5SAR.apiece L ar C HI LYa HIok _ FF' LK4 cr Aw4 M4 model5 fx5 fx6 R5' 0xaff80 R6 0xaf334 M6v W6 K (proj1 BI5) (proj1 (proj2 BI5)) MS6 MG6).
{ intros a Ha Nn. apply FRZ6; [exact Ha| intros X; apply Nn; unfold W6; clear - X; lia]. }
{ intros a Ha Wa. unfold W6 in Wa. split.
- apply (L5SAR.fframe_shadow_client L ar _ FF' 0 0 F 2 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 2) with 256.
unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - Wa; lia.
- assert (DF0 : 0 <= F / 8) by (apply Z.div_pos; clear - Q3; lia). clear - Wa DF0; lia. }
intros M6 model6 HH6 AM6 MRT6 HID6 VIS6 MGM6 FR6 VV6. change (mrestrict H5 M6 = M6v) in VIS6.
assert (BI6 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PM.parser_own s) M6 model6 LK4 cr Aw4).
{ apply (PMAUK.binv_piece L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 2 LK2 M2 model2 cr (PM.parser_own s) G
WR (PM.parser_own s) M4 model5 LK4 cr Aw4 M6 model6 W6 BI5 HH6 AM6 MRT6 MGM6 FR6).
intros a Wa. right; right. change (ff_bytes 2 / 8) with 32. unfold W6 in Wa. unfold SB. clear - Wa; lia. }
destruct (PK M4 M6 W6 src4 sm4 FR6 ltac:(intros a Wa; right; right; unfold W6 in Wa; unfold SB; clear - Wa; lia) QC4 PA4 IA4 SP4) as (PA6 & IA6 & SP6).
assert (U86 : L5.u8_at RSEGS M6 (F / 8 + 112 / 8 + 2147450880) 0).
{ change (112 / 8) with 14. replace (F / 8 + 14 + 2147450880) with (F / 8 + 2147450894) by (clear; lia).
apply (proj1 (L5A.u8_at_vis H5 M6 (F / 8 + 2147450894) 0 (L5A.avis_sub H5 (F / 8 + SB) 32 (F / 8 + 2147450894) 1 VSH5 ltac:(unfold SB; clear; lia) ltac:(unfold SB; clear; lia))
ltac:(clear - Q0f GFR; lia) ltac:(clear - GFR; lia))).
rewrite VIS6. exact C60. }
assert (DEF6 : L5.defined M6 (F + 112) 8).
{ apply (L5.defined_grows M4 M6 _ _ MGM6). apply (proj1 (L5A.defined_vis H5 M4 (F + 112) 8 (L5A.avis_sub H5 F 256 (F + 112) 8 VF5 ltac:(clear; lia) ltac:(clear; lia)))).
apply (L5.defined_sub MV5 F 256); [exact FD5| clear; lia| clear; lia]. }
apply (RD 0xb005c 112 8 0 fx6 R6 M6 model6 LK4 Aw4 src4 sm4 ltac:(split; [clear; lia| reflexivity]) BI6 QC4 PA6 IA6 SP6 ST4).
{ exact A61. } { rewrite (KS6 2%nat) by inl. exact K52. }
{ intros j Hj. rewrite (KS6 j) by (revert j Hj; apply (L5K.incl_b [3; 4]%nat); vm_compute; reflexivity). apply K534. revert j Hj. apply (L5K.incl_b [3; 4]%nat). vm_compute. reflexivity. }
{ exact A610. } { exact A611. } { exact A612. }
{ clear; lia. } { clear; lia. } { reflexivity. } { left; split; reflexivity. }
{ exact U86. } { exact DEF6. }
intros fx7 R7 M7 model7 LK7 Aw7 src7 sm7 dd7 BI7 RP7 Yd7 Hdd7 CONS7 DEFd7 RM17 RM07 QC7 PA7 IA7 SP7 ST7.
assert (R7c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R7 (reg j) = getr R6 (reg j))
by (intros j Hj; exact (L5SAR.cs_of_preserved R6 R7 j RP7 Hj)).
assert (K72 : getr R7 (reg 2) = Z_to_bv 64 (sp - 128)) by (rewrite (R7c 2%nat) by inl; rewrite (KS6 2%nat) by inl; exact K52).
assert (K78 : getr R7 (reg 8) = Z_to_bv 64 sp) by (rewrite (R7c 8%nat) by inl; rewrite (KS6 8%nat) by inl; exact K58).
assert (K79 : getr R7 (reg 9) = Z_to_bv 64 (sp - 128)) by (rewrite (R7c 9%nat) by inl; rewrite (KS6 9%nat) by inl; exact K59).
assert (K718 : getr R7 (reg 18) = Z_to_bv 64 F) by (rewrite (R7c 18%nat) by inl; rewrite (KS6 18%nat) by inl; exact K518).
assert (K719 : getr R7 (reg 19) = Z_to_bv 64 op) by (rewrite (R7c 19%nat) by inl; rewrite (KS6 19%nat) by inl; exact K519).
assert (K720 : getr R7 (reg 20) = Z_to_bv 64 oec) by (rewrite (R7c 20%nat) by inl; rewrite (KS6 20%nat) by inl; exact K520).
assert (K721 : getr R7 (reg 21) = Z_to_bv 64 (op + 24)) by (rewrite (R7c 21%nat) by inl; rewrite (KS6 21%nat) by inl; exact K521).
assert (K724 : getr R7 (reg 24) = Z_to_bv 64 ((F / 8) + 2147450880)) by (rewrite (R7c 24%nat) by inl; rewrite (KS6 24%nat) by inl; exact K524).
assert (K725 : getr R7 (reg 25) = Z_to_bv 64 F) by (rewrite (R7c 25%nat) by inl; rewrite (KS6 25%nat) by inl; exact K525).
assert (K726 : getr R7 (reg 26) = Z_to_bv 64 2147450880) by (rewrite (R7c 26%nat) by inl; rewrite (KS6 26%nat) by inl; exact K526).
assert (K722 : getr R7 (reg 22) = Z_to_bv 64 (F + 112)) by (rewrite (R7c 22%nat) by inl; exact A622).
assert (K723 : getr R7 (reg 23) = Z_to_bv 64 8) by (rewrite (R7c 23%nat) by inl; exact A623).
assert (K734 : forall j, In j [3; 4; 27]%nat -> getr R7 (reg j) = getr R (reg j)).
{ intros j Hj. rewrite (R7c j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity).
rewrite (KS6 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity). apply K534. exact Hj. }
clear R7c.
assert (UN7 : PM.unread src7 sm7 < PM.unread (PM.p_src s) sm) by (unfold PMSPA.consumed in CONS7; clear - CONS7 UN4 Hdd7; lia).
set (H7 := ahid Aw7 model7) in *. set (MV7 := mrestrict H7 M7) in *.
destruct (PMAUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 22528 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 2 LK2 M2 model2 cr (PM.parser_own s) G
WR (PM.parser_own s) M7 model7 LK7 cr Aw7 BI7) as ((WS7 & _ & _ & _ & _) & OWN7 & (FD7 & FW7 & FSW7 & FLC7 & FLW7) & (FLCc7 & FLV7 & VF7 & VS7 & VSH7)).
change (ff_bytes 2) with 256 in *. change (256 / 8) with 32 in *. replace (F + 256 - 8) with (F + 248) in FLC7 by (clear; lia).
destruct (Z.eq_dec dd7 8) as [D7|D7].
-
clear CONS7. subst dd7.
assert (DV7 : L5.defined MV7 (F + 112) 8).
{ apply (proj2 (L5A.defined_vis H7 M7 (F + 112) 8 (L5A.avis_sub H7 F 256 (F + 112) 8 VF7 ltac:(clear; lia) ltac:(clear; lia)))). exact DEFd7. }
cfeed P (PMAGL2.aglVL_conc fx7 R7 MV7 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMAGL2.aligned; assumption]).
destruct P as (fx8 & R8 & M8v & MG8 & _ & FRZ8 & MS8 & KS8).
assert (E8 : M8v = MV7) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ8; exact Ha). subst M8v.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK7 cr Aw7 M7 model7 fx7 fx8 R7 0xb005c R8 0xb00c8 MV7 K (proj1 BI7) (proj1 (proj2 BI7)) MS8 (fun x Hx => Hx) (fun a Ha => eq_refl)).
intros M8 model8 HH8 AM8 MRT8 HID8 VIS8 MGM8 FR8.
assert (E8 : M8 = M7) by (apply L5SAR.mem_eq_of_agree; exact FR8). subst M8.
pose proof (PMAUK.binv_model L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PM.parser_own s) M7 model7 LK7 cr Aw7 model8 BI7 HH8 AM8 MRT8) as BI8.
pose proof (bv_unsigned_in_range 64 (getr R8 (reg 10))) as B810. change (bv_modulus 64) with (2 ^ 64) in B810.
assert (K810 : getr R8 (reg 10) = Z_to_bv 64 (bv_unsigned (getr R8 (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
destruct (Z_lt_dec (bv_unsigned (getr R8 (reg 10))) 9223372036854775808) as [Vp|Vn].
+ apply (OKP 0xb00c8 (XS (fun F => F + 112) (fun _ => 8)) fx8 R8 M7 model8 LK7 Aw7 src7 sm7 sL_run).
{ exists (bv_unsigned (getr R8 (reg 10))). split; [clear - B810 Vp; lia|]. split; [exact K810|].
split; [rewrite (KS8 22%nat) by inl; exact K722| rewrite (KS8 23%nat) by inl; exact K723]. }
all: first [exact BI8 | exact QC7 | exact PA7 | exact IA7 | exact SP7 | exact ST7 | exact UN7 | (rewrite (KS8 _) by inl; assumption)
| (intros j Hj; rewrite (KS8 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity); apply K734; exact Hj) ].
+ assert (VN : 9223372036854775808 <= bv_unsigned (getr R8 (reg 10)) <= 18446744073709551615) by (clear - B810 Vn; lia).
set (H8 := ahid Aw7 model8) in *. set (MV8 := mrestrict H8 M7) in *.
cfeed P (PMAGL4.aglSLN_conc fx8 R8 MV8 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl
| 49%nat => bv_unsigned (getr R8 (reg 10)) | _ => 0 end)) ltac:(first [assumption | (rewrite (KS8 _) by inl; assumption)]).
destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & Z1 & Z10 & Z11).
assert (E9 : M9v = MV8) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ9; exact Ha). subst M9v.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK7 cr Aw7 M7 model8 fx8 fx9 R8 0xb00c8 R9 0xae974 MV8 K (proj1 BI8) (proj1 (proj2 BI8)) MS9 (fun x Hx => Hx) (fun a Ha => eq_refl)).
intros M9 model9 HH9 AM9 MRT9 HID9 VIS9 MGM9 FR9.
assert (E9 : M9 = M7) by (apply L5SAR.mem_eq_of_agree; exact FR9). subst M9.
pose proof (PMAUK.binv_model L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PM.parser_own s) M7 model8 LK7 cr Aw7 model9 BI8 HH9 AM9 MRT9) as BI9.
apply (ERRP 0xb0338 4 fx9 R9 M7 model9 LK7 Aw7 src7 sm7 zL_run ltac:(split; [clear; lia| reflexivity]) ltac:(clear; lia) BI9 QC7 PA7 IA7 SP7 ST7).
all: first [ exact Z1 | exact Z10 | exact Z11 | (rewrite (KS9 _) by inl; rewrite (KS8 _) by inl; assumption)
| (intros j Hj; rewrite (KS9 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity);
rewrite (KS8 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity); apply K734; exact Hj) ].
-
assert (D7r : 0 <= dd7 <= 7) by (clear - Hdd7 D7; lia). assert (D7b : 0 <= dd7 < 2 ^ 64) by (clear - Hdd7; lia).
cfeed P (PMAGL2.aglNL_conc fx7 R7 MV7 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => dd7 | _ => 0 end)) ltac:(first [assumption]).
destruct P as (fx8 & R8 & M8v & MG8 & _ & FRZ8 & MS8 & KS8 & Z1 & Z10 & Z11).
assert (E8 : M8v = MV7) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ8; exact Ha). subst M8v.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK7 cr Aw7 M7 model7 fx7 fx8 R7 0xb005c R8 0xae974 MV7 K (proj1 BI7) (proj1 (proj2 BI7)) MS8 (fun x Hx => Hx) (fun a Ha => eq_refl)).
intros M8 model8 HH8 AM8 MRT8 HID8 VIS8 MGM8 FR8.
assert (E8 : M8 = M7) by (apply L5SAR.mem_eq_of_agree; exact FR8). subst M8.
pose proof (PMAUK.binv_model L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PM.parser_own s) M7 model7 LK7 cr Aw7 model8 BI7 HH8 AM8 MRT8) as BI8.
apply (ERRP 0xb0338 1 fx8 R8 M7 model8 LK7 Aw7 src7 sm7 zL_run ltac:(split; [clear; lia| reflexivity]) ltac:(clear; lia) BI8 QC7 PA7 IA7 SP7 ST7).
all: first [ exact Z1 | exact Z10 | exact Z11 | (rewrite (KS8 _) by inl; assumption)
| (intros j Hj; rewrite (KS8 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity); apply K734; exact Hj) ]. }
assert (CASES : (0 <= b <= 72) \/ (74 <= b <= 75) \/ (77 <= b <= 84) \/ (86 <= b <= 104) \/ (106 <= b <= 107) \/ (109 <= b <= 255)) by (clear - Hb Bti BtU Btl BtI BtL; lia).
destruct CASES as [Bc|[Bc|[Bc|[Bc|[Bc|Bc]]]]].
+ cfeed P (PMAGL1.aglTd1_conc fx5 R5' MV5 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => b | _ => 0 end)) ltac:(first [assumption]).
destruct P as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & MS6 & KS6 & Z1 & Z10 & Z11).
assert (E6 : M6v = MV5) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ6; exact Ha). subst M6v.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK4 cr Aw4 M4 model5 fx5 fx6 R5' 0xaff80 R6 0xae974 MV5 K (proj1 BI5) (proj1 (proj2 BI5)) MS6 (fun x Hx => Hx) (fun a Ha => eq_refl)).
intros M6 model6 HH6 AM6 MRT6 HID6 VIS6 MGM6 FR6.
assert (E6 : M6 = M4) by (apply L5SAR.mem_eq_of_agree; exact FR6). subst M6.
pose proof (PMAUK.binv_model L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PM.parser_own s) M4 model5 LK4 cr Aw4 model6 BI5 HH6 AM6 MRT6) as BI6.
apply (ERRP 0xb019c 5 fx6 R6 M4 model6 LK4 Aw4 src4 sm4 zD_run ltac:(split; [clear; lia| reflexivity]) ltac:(clear; lia) BI6 QC4 PA4 IA4 SP4 ST4).
all: first [ exact Z1 | exact Z10 | exact Z11 | (rewrite (KS6 _) by inl; assumption)
| (intros j Hj; rewrite (KS6 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity); apply K534; exact Hj) ].
+ cfeed P (PMAGL1.aglTd2_conc fx5 R5' MV5 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => b | _ => 0 end)) ltac:(first [assumption]).
destruct P as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & MS6 & KS6 & Z1 & Z10 & Z11).
assert (E6 : M6v = MV5) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ6; exact Ha). subst M6v.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK4 cr Aw4 M4 model5 fx5 fx6 R5' 0xaff80 R6 0xae974 MV5 K (proj1 BI5) (proj1 (proj2 BI5)) MS6 (fun x Hx => Hx) (fun a Ha => eq_refl)).
intros M6 model6 HH6 AM6 MRT6 HID6 VIS6 MGM6 FR6.
assert (E6 : M6 = M4) by (apply L5SAR.mem_eq_of_agree; exact FR6). subst M6.
pose proof (PMAUK.binv_model L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PM.parser_own s) M4 model5 LK4 cr Aw4 model6 BI5 HH6 AM6 MRT6) as BI6.
apply (ERRP 0xb019c 5 fx6 R6 M4 model6 LK4 Aw4 src4 sm4 zD_run ltac:(split; [clear; lia| reflexivity]) ltac:(clear; lia) BI6 QC4 PA4 IA4 SP4 ST4).
all: first [ exact Z1 | exact Z10 | exact Z11 | (rewrite (KS6 _) by inl; assumption)
| (intros j Hj; rewrite (KS6 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity); apply K534; exact Hj) ].
+ cfeed P (PMAGL1.aglTd3_conc fx5 R5' MV5 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => b | _ => 0 end)) ltac:(first [assumption]).
destruct P as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & MS6 & KS6 & Z1 & Z10 & Z11).
assert (E6 : M6v = MV5) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ6; exact Ha). subst M6v.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK4 cr Aw4 M4 model5 fx5 fx6 R5' 0xaff80 R6 0xae974 MV5 K (proj1 BI5) (proj1 (proj2 BI5)) MS6 (fun x Hx => Hx) (fun a Ha => eq_refl)).
intros M6 model6 HH6 AM6 MRT6 HID6 VIS6 MGM6 FR6.
assert (E6 : M6 = M4) by (apply L5SAR.mem_eq_of_agree; exact FR6). subst M6.
pose proof (PMAUK.binv_model L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PM.parser_own s) M4 model5 LK4 cr Aw4 model6 BI5 HH6 AM6 MRT6) as BI6.
apply (ERRP 0xb019c 5 fx6 R6 M4 model6 LK4 Aw4 src4 sm4 zD_run ltac:(split; [clear; lia| reflexivity]) ltac:(clear; lia) BI6 QC4 PA4 IA4 SP4 ST4).
all: first [ exact Z1 | exact Z10 | exact Z11 | (rewrite (KS6 _) by inl; assumption)
| (intros j Hj; rewrite (KS6 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity); apply K534; exact Hj) ].
+ cfeed P (PMAGL2.aglTd4_conc fx5 R5' MV5 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => b | _ => 0 end)) ltac:(first [assumption]).
destruct P as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & MS6 & KS6 & Z1 & Z10 & Z11).
assert (E6 : M6v = MV5) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ6; exact Ha). subst M6v.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK4 cr Aw4 M4 model5 fx5 fx6 R5' 0xaff80 R6 0xae974 MV5 K (proj1 BI5) (proj1 (proj2 BI5)) MS6 (fun x Hx => Hx) (fun a Ha => eq_refl)).
intros M6 model6 HH6 AM6 MRT6 HID6 VIS6 MGM6 FR6.
assert (E6 : M6 = M4) by (apply L5SAR.mem_eq_of_agree; exact FR6). subst M6.
pose proof (PMAUK.binv_model L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PM.parser_own s) M4 model5 LK4 cr Aw4 model6 BI5 HH6 AM6 MRT6) as BI6.
apply (ERRP 0xb019c 5 fx6 R6 M4 model6 LK4 Aw4 src4 sm4 zD_run ltac:(split; [clear; lia| reflexivity]) ltac:(clear; lia) BI6 QC4 PA4 IA4 SP4 ST4).
all: first [ exact Z1 | exact Z10 | exact Z11 | (rewrite (KS6 _) by inl; assumption)
| (intros j Hj; rewrite (KS6 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity); apply K534; exact Hj) ].
+ cfeed P (PMAGL2.aglTd5_conc fx5 R5' MV5 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => b | _ => 0 end)) ltac:(first [assumption]).
destruct P as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & MS6 & KS6 & Z1 & Z10 & Z11).
assert (E6 : M6v = MV5) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ6; exact Ha). subst M6v.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK4 cr Aw4 M4 model5 fx5 fx6 R5' 0xaff80 R6 0xae974 MV5 K (proj1 BI5) (proj1 (proj2 BI5)) MS6 (fun x Hx => Hx) (fun a Ha => eq_refl)).
intros M6 model6 HH6 AM6 MRT6 HID6 VIS6 MGM6 FR6.
assert (E6 : M6 = M4) by (apply L5SAR.mem_eq_of_agree; exact FR6). subst M6.
pose proof (PMAUK.binv_model L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PM.parser_own s) M4 model5 LK4 cr Aw4 model6 BI5 HH6 AM6 MRT6) as BI6.
apply (ERRP 0xb019c 5 fx6 R6 M4 model6 LK4 Aw4 src4 sm4 zD_run ltac:(split; [clear; lia| reflexivity]) ltac:(clear; lia) BI6 QC4 PA4 IA4 SP4 ST4).
all: first [ exact Z1 | exact Z10 | exact Z11 | (rewrite (KS6 _) by inl; assumption)
| (intros j Hj; rewrite (KS6 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity); apply K534; exact Hj) ].
+ cfeed P (PMAGL2.aglTd6_conc fx5 R5' MV5 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => b | _ => 0 end)) ltac:(first [assumption]).
destruct P as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & MS6 & KS6 & Z1 & Z10 & Z11).
assert (E6 : M6v = MV5) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ6; exact Ha). subst M6v.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK4 cr Aw4 M4 model5 fx5 fx6 R5' 0xaff80 R6 0xae974 MV5 K (proj1 BI5) (proj1 (proj2 BI5)) MS6 (fun x Hx => Hx) (fun a Ha => eq_refl)).
intros M6 model6 HH6 AM6 MRT6 HID6 VIS6 MGM6 FR6.
assert (E6 : M6 = M4) by (apply L5SAR.mem_eq_of_agree; exact FR6). subst M6.
pose proof (PMAUK.binv_model L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PM.parser_own s) M4 model5 LK4 cr Aw4 model6 BI5 HH6 AM6 MRT6) as BI6.
apply (ERRP 0xb019c 5 fx6 R6 M4 model6 LK4 Aw4 src4 sm4 zD_run ltac:(split; [clear; lia| reflexivity]) ltac:(clear; lia) BI6 QC4 PA4 IA4 SP4 ST4).
all: first [ exact Z1 | exact Z10 | exact Z11 | (rewrite (KS6 _) by inl; assumption)
| (intros j Hj; rewrite (KS6 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity); apply K534; exact Hj) ].
Qed.
End WithHeap.
End PMAGLN.
