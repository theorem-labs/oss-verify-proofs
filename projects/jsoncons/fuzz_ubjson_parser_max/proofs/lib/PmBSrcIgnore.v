(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0 LibIface AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0 L5CoreSpecsAB0 L5StepARB0 L5CoreBRB0 L5ADetailHRB0 PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAb PmModelFactsA PmStepAB0 PmStep PmParStep PmParKit PmBSrcKit PmBParKit PmBReset1 PmBUarK PmBUar PmBSrcUar PmBIgnP1 PmBIgnP2.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia.
Module PMBSIG.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Ltac pdestr PP := repeat match type of PP with _ /\ _ => let H := fresh "Q" in destruct PP as (H & PP) end.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMB.ly_as0 L C LY.
Theorem ignore_ok : PMB.fill_buffer_spec L ar HI -> PMB.ignore_spec L ar HI.
Proof.
intros FB. unfold PMB.ignore_spec, PMSPA.ignore_spec, PMSPA.src_spec.
intros fx R M model K LBX FF LK Aw cr sp r fb s str sm Wextra HH AM K0 ENT FRM FRS FOK A10 A11 WX PA IA BASE INCS KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
unfold PMSPA.no_W in WX. subst Wextra. rewrite app_nil_r in KONT. unfold PMSPA.ignore_args in A11.
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5SAR.r11 in A11.
change (PMSPA.pm_scr 4) with 20480 in *. change (20480 / 8) with 2560 in STKSH. pose proof RAok as (Hr1 & Hr2).
pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
set (LB := PM.parser_own s ++ LBX) in *.
pose proof (PMBSK.src_vis L ar C HI LY HIok LB FF LK cr Aw M model fb (PMSPA.o_is PMB.AD fb) s sp 20480 HH FOK PA ASTK)
as ((O1 & O8 & OBIG) & OZ & OW & OCE & OAV & AO & OFS1 & OFS2).
set (os := PMSPA.o_src PMB.AD fb) in *. set (ois := PMSPA.o_is PMB.AD fb) in *.
pose proof (PMBSK.mach_vis L ar C HI LY HIok LB FF LK cr Aw M model HH BASE) as (V0 & V1 & V2).
pose proof (PMBSK.stk_vis L ar C HI LY HIok LB FF LK cr Aw M model sp 20480 208 HH ASTK ltac:(lia)) as (SL208 & SH208 & V3).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & STOP & _).
pose proof FOK as ((rs & Hfb) & Fal).
pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 4) with 1024 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, F1, F2.
destruct s as [mo dn dp src tb tg vb vk stk]. destruct src as [qc de rem]. destruct sm as [g eg st].
cbn [PM.p_src PM.sr_qc PM.sr_de PM.sr_rem PM.sm_g PM.sm_eg PM.sm_st] in *.
pose proof PA as (_ & PDEF & _ & _ & _ & _ & _ & _ & _ & PSRC & _).
destruct PSRC as (S240 & S248 & SD256 & S264 & S272 & S280 & S288 & G1 & G2 & G3 & G16 & DCH & ACH & ACC240).
cbn [PM.p_src PM.sr_qc PM.sr_de PM.sr_rem] in *. unfold PM.CHUNK in *.
fold os in S240, S248, SD256, S264, S272, S280, S288.
set (s := PM.PST mo dn dp (PM.SRC qc de rem) tb tg vb vk stk) in *.
assert (QIN : In (qc, 16384) LB) by (unfold LB, s, PM.parser_own, PM.src_own; cbn; left; reflexivity).
destruct (WB _ QIN) as ((Q0 & _ & _ & _ & Q4 & Q5) & _). cbn [fst snd] in Q0, Q4, Q5.
set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
assert (BOWN : incl (PM.parser_own s) LB) by (unfold LB; apply incl_appl, incl_refl).
assert (SOWN : incl (PM.vs_own str) LB) by (unfold LB; apply incl_appr; exact INCS).
pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (_ & VISs & _).
assert (V3' : L5.writable RSEGS MV (sp - 192) 192) by (apply (L5.writable_sub RSEGS MV (sp - 208) 208); [exact V3| lia| lia]).
cfeed P (PMBIGP1.bigA_conc fx R MV (fun j => match j with 2%nat => sp | 36%nat => os | _ => 0 end)) ltac:(first [assumption | unfold PMBIGP1.aligned; assumption | clear - SL208 SHI SPT; lia | clear - O1; lia]).
destruct P as (fxa & Ra & Mav & MGa & _ & FRZa & MSa & KSa & T2 & T8 & C104 & C96 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8 & C192).
set (X := (sp - 192) - (sp - 192) mod 32) in *.
assert (HX : sp - 208 <= X <= sp - 192 /\ X mod 32 = 0 /\ X mod 16 = 0).
{ unfold X. pose proof (Z.mod_pos_bound (sp - 192) 32 ltac:(lia)) as B.
assert (E16 : (sp - 192) mod 32 = 0 \/ (sp - 192) mod 32 = 16).
{ assert (S16 : (sp - 192) mod 16 = 0) by (replace (sp - 192) with (sp + (-12) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
pose proof (Z.div_mod (sp - 192) 32 ltac:(lia)) as D. pose proof (Z.div_mod (sp - 192) 16 ltac:(lia)) as D2. lia. }
split; [lia|]. split.
- rewrite Zminus_mod. rewrite Z.mod_mod by lia. rewrite Z.sub_diag. reflexivity.
- destruct E16 as [E|E]; rewrite E; replace (sp - 192 - 0) with (sp + (-12) * 16) || replace (sp - 192 - 16) with (sp + (-13) * 16); try lia;
rewrite Z_mod_plus_full; exact A16. }
destruct HX as (HX1 & HX32 & HX16).
destruct (PMBSU.andi_sp Ra (sp - 192) (Z_to_bv 12 4064) ltac:(lia) eq_refl T2) as (T2' & TO).
pose proof (PMBSU.andi_to fxa Ra Mav 0xafb34 (ltac:(oW' 0xafb34%Z)) _ _ _ (ltac:(oF' 0xafb34%Z)) eq_refl (ltac:(oD' 0xafb34%Z)) eq_refl ltac:(lia) ltac:(lia)) as MSA.
set (Rat := regupd Ra 2%bv (v_andi (getr Ra 2%bv) (bv_signed (Z_to_bv 12 4064 : bv 12)))) in MSA, T2', TO.
fold X in T2'.
assert (U8 : getr Rat (reg 8) = Z_to_bv 64 sp) by (rewrite (TO 8%nat) by lia; exact T8).
assert (U10 : getr Rat (reg 10) = Z_to_bv 64 os) by (rewrite (TO 10%nat) by lia; rewrite (KSa 10%nat) by inl; exact A10).
assert (U11 : getr Rat (reg 11) = Z_to_bv 64 1) by (rewrite (TO 11%nat) by lia; rewrite (KSa 11%nat) by inl; rewrite <- L5SAR.r11; exact A11).
assert (WXa : L5.writable RSEGS Mav X 96).
{ apply (L5.writable_grows RSEGS MV Mav X 96 MGa). apply (L5.writable_sub RSEGS MV (sp - 208) 208); [exact V3| lia| lia]. }
assert (VMa : L5.img_clear Mav 65536 1269760 /\ L5.u64_at RSEGS Mav 1296952 2147450880 /\ L5.u32_at RSEGS Mav 1296960 1).
{ assert (AG1 : forall i, 0 <= i < 1296968 -> Mav (Z_to_bv 64 i) = MV (Z_to_bv 64 i)) by (intros i Hi; apply FRZa; [lia| clear - Hi SL208 SHI SPT; lia]).
split; [intros i Hi; rewrite AG1 by lia; apply V0; exact Hi|].
split; [apply (L5C.u64_at_agree RSEGS MV Mav); [intros i Hi; rewrite AG1 by lia; reflexivity| lia| lia| exact V1]|].
apply (PMF.u32_at_agree RSEGS MV Mav); [intros i Hi; rewrite AG1 by lia; reflexivity| lia| lia| exact V2]. }
destruct VMa as (VMa0 & VMa1 & VMa2).
cfeed P (PMBIGP1.bigA2_conc fxa Rat Mav (fun j => match j with 2%nat => sp | 36%nat => os | 50%nat => X | _ => 0 end)) ltac:(first [assumption | unfold PMBIGP1.aligned; assumption | clear - SL208 SHI SPT HX1; lia | clear - O1; lia | clear - HX1 SL208 SHI SPT; lia]).
destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1b & T9b & T10b & _ & _ & T17b & T19b & T23b & C56X).
assert (MS01 : msteps RSEGS (L5A.st fx R 0xafaf4 MV) (L5A.st fx1 R1 0x5d670 M1v))
by (eapply msteps_trans; [exact MSa| eapply msteps_trans; [exact MSA| exact MS1]]).
assert (MG01 : mem_grows MV M1v) by (intros x Hx; apply MG1; apply MGa; exact Hx).
assert (SVa : forall a v, sp - 104 <= a -> a + 8 <= sp -> L5.u64_at RSEGS Mav a v -> L5.u64_at RSEGS M1v a v).
{ intros a v Ha1 Ha2 Y. apply (L5C.u64_at_agree RSEGS Mav M1v); [intros i Hi; apply FRZ1; [clear - Hi Ha1 Ha2 SL208 SHI SPT; lia| clear - Hi Ha1 Ha2 HX1; lia]| clear - Ha1 SL208 SPT; lia| clear - Ha2 SHI SPT; lia| exact Y]. }
unfold PMSPA.cfg. cbn [pa_ignore PMB.AD ADDR_B].
apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xafaf4 R1 0x5d670 M1v (fun a => X <= a < sp) K HH AM MS01 MG01).
{ intros a Ha N. rewrite FRZ1 by (first [exact Ha| intros Y; apply N; clear - Y HX1; lia]). apply FRZa; [exact Ha| intros Y; apply N; clear - Y HX1; lia]. }
{ intros a Ha Wa. split; [|intros Y; clear - Wa Y SL208 SPT HX1; lia]. unfold aclientw, aclient_g. right; left. split; [clear - Wa SL208 SHI SPT HX1; lia| intros Y; clear - Y; lia]. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
assert (NCS0 : forall a, X <= a < sp -> ~ aclient L ar LB FF sp 20480 a).
{ intros a Xa Hc. destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 20480 a HH SPT Hc) as [Y|Y].
- clear - Xa Y HX1; lia.
- clear - Xa Y SL208 HX1; lia. }
assert (EK01 : L5SAR.ek L ar LB FF sp 20480 [] M M1).
{ apply (L5SAR.ek_piece L ar LB FF sp 20480 [] M M1 (fun a => X <= a < sp) FR1). intros a Ha Hc _ Y. apply (NCS0 a); [exact Y| exact Hc]. }
assert (DK01 : L5SAR.dk L ar LB FF sp 20480 M M1) by (apply L5SAR.dk_grows; exact MGM1).
assert (SV1 : forall a v, sp - 104 <= a -> a + 8 <= sp -> L5.u64_at RSEGS Mav a v -> L5.u64_at RSEGS M1 a v).
{ intros a v Ha1 Ha2 Y. apply (proj1 (L5A.u64_at_vis H M1 a v (VISs a 8 ltac:(clear - Ha1 SL208 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL208 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))).
rewrite VIS1. apply SVa; assumption. }
assert (OWN1 : PMBSU.own13 sp R M1).
{ unfold PMBSU.own13. split; [apply SV1; [clear; lia| clear; lia| exact C8]|]. split; [apply SV1; [clear; lia| clear; lia| exact C16]|].
split; [apply SV1; [clear; lia| clear; lia| exact C24]|]. split; [apply SV1; [clear; lia| clear; lia| exact C32]|].
split; [apply SV1; [clear; lia| clear; lia| exact C40]|]. split; [apply SV1; [clear; lia| clear; lia| exact C48]|].
split; [apply SV1; [clear; lia| clear; lia| exact C56]|]. split; [apply SV1; [clear; lia| clear; lia| exact C64]|].
split; [apply SV1; [clear; lia| clear; lia| exact C72]|]. split; [apply SV1; [clear; lia| clear; lia| exact C80]|].
split; [apply SV1; [clear; lia| clear; lia| exact C88]|]. split; [apply SV1; [clear; lia| clear; lia| exact C96]|].
apply SV1; [clear; lia| clear; lia| exact C104]. }
assert (C56' : L5.u64_at RSEGS M1 (X + 56) 2147450880).
{ apply (proj1 (L5A.u64_at_vis H M1 (X + 56) _ (VISs (X + 56) 8 ltac:(clear - HX1 SL208 SPT; lia) ltac:(clear - HX1 SHI SPT; lia)) ltac:(clear - HX1 SL208 SPT; lia) ltac:(clear - HX1 SHI SPT; lia))).
rewrite VIS1. exact C56X. }
clear C104 C96 C88 C80 C72 C64 C56 C48 C40 C32 C24 C16 C8 C192 SV1 SVa.
assert (FRk1 : ff_room 1 FF LK) by (apply (PMBUAR.ff_room_of 4 FF LK 1 FRM); [clear; lia| right; left; reflexivity]).
change 0x5d670 with (PMB.SM_PC 1).
apply (PMBUAR.uar_sm L ar C HI LY HIok 1 LB [] FF LK cr Aw sp 20480 X (sp - 104) sp (PMBSU.ocell13 sp) (PMBSU.own13 sp R)
fx1 R1 M M1 model model1 K 0xafb6c ltac:(right; left; reflexivity) HH HH1 AM1 K0 ASTK MGM1 EK01 DK01).
{ rewrite L5K.rl2. rewrite (KS1 2%nat) by inl. exact T2'. }
{ rewrite L5K.rl4. rewrite (KS1 4%nat) by inl. rewrite (TO 4%nat) by lia. rewrite (KSa 4%nat) by inl. rewrite <- L5K.rl4. exact Rtp. }
{ rewrite L5K.rl1. exact T1b. }
{ reflexivity. }
{ clear; lia. }
{ exact HX16. }
{ clear - HX1; lia. } { clear - HX1; lia. } { clear; lia. } { clear; lia. }
{ intros a Ha. exact Ha. }
{ intros Ma Mb OWa AGa. apply (PMBSU.own13_agree sp R Ma Mb ltac:(clear - SL208 SPT; lia) ltac:(clear - SHI SPT; lia) OWa AGa). }
{ exact FRk1. }
{ intros f Hf. specialize (FRS f Hf). clear - FRS; lia. }
intros R2 M2 model2 F fl LK2 G G10 RP2 AM2 MRT2 ASTK2 EK02 DK02 EK12f DK12f AGF FW FSHW FSHZ FLC FLW FDEF VF VSH VFL APART.
change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *. change (128 - 8) with 120 in *.
pose proof G as G'. destruct G' as [_ _ _ _ _ _ _ GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
change (ff_bytes 1) with 128 in *.
pose proof (L5SAR.ek_trans L ar LB FF sp 20480 [] M M1 M2 EK01 EK12f) as EK02f.
pose proof (L5SAR.dk_trans L ar LB FF sp 20480 M M1 M2 DK01 DK12f) as DK02f.
pose proof (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
pose proof (PMBPAR.op_vis L ar C HI LY HIok _ FF LK cr Aw M model fb _ s HH FOK PA) as (_ & _ & _ & _ & _ & _ & _ & AOP & Eop).
pose proof (PMBSK.iss_vis L ar C HI LY HIok _ FF LK cr Aw M model fb str _ sp 20480 HH FOK IA ASTK) as ((I1 & I8 & INSH) & _ & _ & ICE & _ & AOI & _).
fold ois in I1, I8, INSH, ICE, AOI.
assert (PA2 : PM.parser_at RSEGS PMB.AD PMSPA.accA PMSPA.annA M2 (PMSPA.o_p PMB.AD fb) ois s).
{ apply (PMKB.parser_keepA RSEGS PMB.AD L ar LB FF sp 20480 [] M M2 EK02f PMKB.wapp_nil FRB BRB _ _ _ AOP);
[exact BOWN| intros i _ r0 []| intros i _ r0 []| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact PA]. }
assert (IA2 : PM.iss_at RSEGS PMB.AD PMSPA.accA M2 ois str (PM.STRM g eg st)).
{ apply (PMKB.iss_keepA RSEGS PMB.AD L ar LB FF sp 20480 [] M M2 EK02f PMKB.wapp_nil FRB BRB ois str _ AOI); [exact SOWN| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA]. }
assert (BASE2 : PMSTA.base_okA RSEGS PMB.AD M2) by (apply (PMBSK.base_keep L ar C LY LB FF sp 20480 [] M M2 EK02f); [intros a _ r0 []| exact BASE]).
assert (HH2 : ri_inv HI LB ((F, 1, X + 32) :: FF) LK2 cr Aw M2 (vml_of model2)) by exact GHH2.
set (FF' := (F, 1, X + 32) :: FF) in *.
assert (FOK' : PMSPA.frame_okA FF' fb) by exact (PMBUAR.frame_okA_push FF fb F 1 (X + 32) FOK).
set (H2 := ahid Aw model2) in *. set (MV2 := mrestrict H2 M2) in *.
pose proof (PMBSK.src_vis L ar C HI LY HIok LB FF' LK2 cr Aw M2 model2 fb ois s sp 20480 HH2 FOK' PA2 ASTK2)
as ((_ & _ & _) & OZ2 & OW2 & _ & OAV2 & AO2 & _ & _). fold os MV2 in OZ2, OW2, OAV2, AO2.
pose proof (PMBSK.mach_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 HH2 BASE2) as (W0 & W1 & W2). fold MV2 in W0, W1, W2.
pose proof (PMBSK.stk_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 sp 20480 208 HH2 ASTK2 ltac:(lia)) as (_ & _ & SWR2). fold MV2 in SWR2.
pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LK2 cr Aw M2 model2 HH2) as (_ & VISs2 & _).
assert (CLos : forall i, 0 <= i < 296 -> aclient L ar ([] ++ LB) FF 0 0 (os + i)).
{ intros i Hi. destruct AO as (f & Hf & X1 & X2). unfold aclient, aclient_g. do 3 right; left. exists f. split; [exact Hf|]. clear - X1 X2 Hi; lia. }
destruct (APART os 296 0 0 CLos ltac:(clear; lia)) as (AoF & AoSF & AoFL).
assert (CLsh : forall i, 0 <= i < 37 -> aclient L ar ([] ++ LB) FF 0 0 (os / 8 + SB + i)).
{ intros i Hi. destruct AO as (f & Hf & X1 & X2). unfold aclient, aclient_g. do 5 right; left. exists f. split; [exact Hf|].
unfold in_shadow_of, S.
assert (D1 : ff_addr f / 8 <= os / 8) by (apply Z.div_le_mono; clear - X1; lia).
assert (D2 : (os + i * 8) / 8 = os / 8 + i) by (apply Z.div_add; clear; lia).
assert (D3 : (os + i * 8) / 8 <= (ff_addr f + ff_bytes (ff_class f) - 1) / 8) by (apply Z.div_le_mono; clear - X2 Hi; lia).
clear - D1 D2 D3 Hi. lia. }
destruct (APART (os / 8 + SB) 37 0 0 CLsh ltac:(clear; lia)) as (_ & AsoSF & _).
unfold SB in AsoSF.
assert (QQ0 : 0 <= sp < 2 ^ 64 /\ 0 <= os < 2 ^ 64 /\ 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64 /\ 0 <= X < 2 ^ 64 /\ 0 <= qc < 2 ^ 64)
by (clear - SL208 SHI SPT O1 GFR GFLR HX1 Q0 Q4; lia).
destruct QQ0 as (Q0a & Q0b & Q0c & Q0d & Q0e & Q0f).
assert (QX : 140735332487168 <= X <= 140737488355136) by (clear - SL208 SHI SPT HX1; lia).
assert (QXa : X mod 32 = 0) by exact HX32.
assert (QXo : X + 96 <= os \/ os + 296 <= X) by (clear - OCE SL208 HX1; lia).
assert (QXF : X + 96 <= F \/ F + 128 <= X) by (clear - GFCEIL SL208 HX1; lia).
assert (QXfl : X + 96 <= fl \/ fl + 1 <= X) by (clear - GFLR SL208 HX1; lia).
assert (QFR : 6893568 <= F <= 140737488355200) by (clear - GFR; lia).
assert (QFI : F + 128 <= 65536 \/ 65536 + 1204224 <= F) by (clear - GFR; lia).
assert (QFL : 4096 <= fl <= 140737488355327) by (clear - GFLR; lia).
assert (QoF : os + 296 <= F \/ F + 128 <= os) by exact AoF.
assert (QoFL : os + 296 <= fl \/ fl + 1 <= os) by exact AoFL.
assert (QoSF : ((os / 8) + 2147450880) + 37 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 16 <= ((os / 8) + 2147450880)) by exact AsoSF.
assert (FLCv : L5.u64_at RSEGS MV2 (F + 120) fl) by (replace (F + 120) with (F + 128 - 8) by (clear; lia); exact FLC).
assert (SV2 : forall a v, X <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1 a v -> L5.u64_at RSEGS MV2 a v).
{ intros a v Ha1 Ha2 Y. apply (proj2 (L5A.u64_at_vis H2 M2 a v (VISs2 a 8 ltac:(clear - Ha1 SL208 SPT HX1; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL208 SPT HX1; lia) ltac:(clear - Ha2 SHI SPT; lia))).
apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply AGF; clear - Ha1 Ha2 Hi; lia| clear - Ha1 SL208 SPT HX1; lia| clear - Ha2 SHI SPT; lia| exact Y]. }
assert (C56v : L5.u64_at RSEGS MV2 (X + 56) 2147450880) by (apply SV2; [clear; lia| clear - HX1; lia| exact C56']).
assert (WX2 : L5.writable RSEGS MV2 X 96) by (apply (L5.writable_sub RSEGS MV2 (sp - 208) 208); [exact SWR2| clear - HX1; lia| clear - HX1; lia]).
pose proof PA2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PSRC2 & _).
destruct PSRC2 as (_ & _ & SD2 & S264b & S272b & S280b & S288b & _ & _ & _ & _ & _ & _ & _). cbn [PM.p_src s PM.sr_qc PM.sr_de PM.sr_rem] in SD2, S264b, S272b, S280b, S288b.
fold os in SD2, S264b, S272b, S280b, S288b. unfold PM.CHUNK in S272b.
assert (VS264 : L5.u64_at RSEGS MV2 (os + 264) qc) by (apply (proj2 (L5A.u64_at_vis _ M2 (os + 264) qc ltac:(apply OAV2; clear; lia) ltac:(clear - O1; lia) ltac:(clear - O1; lia))); exact S264b).
assert (VS272 : L5.u64_at RSEGS MV2 (os + 272) 16384) by (apply (proj2 (L5A.u64_at_vis _ M2 (os + 272) _ ltac:(apply OAV2; clear; lia) ltac:(clear - O1; lia) ltac:(clear - O1; lia))); exact S272b).
assert (VS280 : L5.u64_at RSEGS MV2 (os + 280) de) by (apply (proj2 (L5A.u64_at_vis _ M2 (os + 280) de ltac:(apply OAV2; clear; lia) ltac:(clear - O1; lia) ltac:(clear - O1; lia))); exact S280b).
assert (VS288 : L5.u64_at RSEGS MV2 (os + 288) rem) by (apply (proj2 (L5A.u64_at_vis _ M2 (os + 288) rem ltac:(apply OAV2; clear; lia) ltac:(clear - O1; lia) ltac:(clear - O1; lia))); exact S288b).
assert (VD256 : L5.defined MV2 (os + 256) 8) by (apply (proj2 (L5A.defined_vis _ M2 (os + 256) 8 ltac:(apply OAV2; clear; lia))); exact SD2).
assert (R2c : forall j, In j L5SAR.cs_all -> getr R2 (reg j) = getr R1 (reg j)) by (intros j Hj; apply (L5SAR.cs_of_preserved R1 R2 j RP2 Hj)).
assert (B2R : getr R2 (reg 2) = Z_to_bv 64 X) by (rewrite (R2c 2%nat) by inl; rewrite (KS1 2%nat) by inl; exact T2').
assert (B8R : getr R2 (reg 8) = Z_to_bv 64 sp) by (rewrite (R2c 8%nat) by inl; rewrite (KS1 8%nat) by inl; exact U8).
assert (B9R : getr R2 (reg 9) = Z_to_bv 64 X) by (rewrite (R2c 9%nat) by inl; exact T9b).
assert (B19R : getr R2 (reg 19) = Z_to_bv 64 os) by (rewrite (R2c 19%nat) by inl; exact T19b).
assert (B23R : getr R2 (reg 23) = Z_to_bv 64 1) by (rewrite (R2c 23%nat) by inl; exact T23b).
assert (B10R : getr R2 (reg 10) = Z_to_bv 64 F) by (rewrite <- L5K.rl10; exact G10).
assert (B34 : forall j, In j [3; 4]%nat -> getr R2 (reg j) = getr R (reg j)).
{ intros j Hj. rewrite (R2c j) by (destruct Hj as [<-|[<-|[]]]; inl). rewrite (KS1 j) by (destruct Hj as [<-|[<-|[]]]; inl).
rewrite (TO j) by (destruct Hj as [<-|[<-|[]]]; lia). apply KSa. destruct Hj as [<-|[<-|[]]]; inl. }
set (WS := PMSPA.W_src PMB.AD fb (PM.p_src s)) in *.
assert (EXITP : forall (fx7 : FPState) R7 M7 model7 LK7 Aw7 (src7 : PM.srcst) (sm7 : PM.strm),
PMBUK.binv L ar HI M model LB FF LK Aw sp 20480 X (PMBSU.own13 sp R) F 1 WS [] M7 model7 LK7 cr Aw7 ->
getr R7 (reg 2) = Z_to_bv 64 X -> getr R7 (reg 8) = Z_to_bv 64 sp -> getr R7 (reg 9) = Z_to_bv 64 X ->
getr R7 (reg 26) = Z_to_bv 64 ((F / 8) + 2147450880) ->
getr R7 (reg 3) = getr R (reg 3) -> getr R7 (reg 4) = getr R (reg 4) ->
L5.u64_at RSEGS M7 (X + 8) F -> L5.u64_at RSEGS M7 (X + 16) F ->
PM.parser_at RSEGS PMB.AD PMSPA.accA PMSPA.annA M7 (PMSPA.o_p PMB.AD fb) ois (PMSPA.with_src s src7) ->
PM.iss_at RSEGS PMB.AD PMSPA.accA M7 ois str sm7 ->
PMSPA.src_step (PM.p_src s) src7 (PM.STRM g eg st) sm7 ->
PMSPA.ignore_res R R M7 (PM.p_src s) src7 (PM.STRM g eg st) sm7 ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx7 R7 0xafe04 M7 model7) K).
{ intros fx7 R7 M7 model7 LK7 Aw7 src7 sm7 BI7 G72 G78 G79 G726 G73 G74 S8 S16 PA7 IA7 STEP7 RES7.
set (H7 := ahid Aw7 model7) in *. set (MV7 := mrestrict H7 M7) in *.
destruct (PMBUK.vis_facts L ar C HI LYa HIok M model LB FF LK Aw sp 20480 X (sp - 104) sp (PMBSU.ocell13 sp) (PMBSU.own13 sp R) F fl 1 LK2 M2 model2 cr [] G
WS [] M7 model7 LK7 cr Aw7 BI7) as ((WS7 & _ & _ & _ & _) & OWN7 & (FD7 & FW7 & FSW7 & FLC7 & FLW7) & (FLCc7 & FLV7 & VF7 & VS7 & VSH7)).
change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *. fold H7 MV7 in WS7, OWN7, FD7, FW7, FSW7, FLC7, FLW7.
replace (F + 128 - 8) with (F + 120) in FLC7 by (clear; lia).
assert (WSE7 : L5.writable RSEGS MV7 (sp - 192) 192) by (apply (L5.writable_sub RSEGS MV7 X (sp - X)); [exact WS7| clear - HX1; lia| clear; lia]).
assert (WSX7 : L5.writable RSEGS MV7 X 96) by (apply (L5.writable_sub RSEGS MV7 X (sp - X)); [exact WS7| clear; lia| clear - HX1; lia]).
assert (S8v : L5.u64_at RSEGS MV7 (X + 8) F).
{ apply (proj2 (L5A.u64_at_vis H7 M7 (X + 8) F (L5A.avis_sub H7 X (sp - X) (X + 8) 8 VS7 ltac:(clear; lia) ltac:(clear - HX1; lia)) ltac:(clear - Q0e; lia) ltac:(clear - QX; lia))). exact S8. }
assert (S16v : L5.u64_at RSEGS MV7 (X + 16) F).
{ apply (proj2 (L5A.u64_at_vis H7 M7 (X + 16) F (L5A.avis_sub H7 X (sp - X) (X + 16) 8 VS7 ltac:(clear; lia) ltac:(clear - HX1; lia)) ltac:(clear - Q0e; lia) ltac:(clear - QX; lia))). exact S16. }
pose proof OWN7 as (Y8 & Y16 & Y24 & Y32 & Y40 & Y48 & Y56 & Y64 & Y72 & Y80 & Y88 & Y96 & Y104).
pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8.
pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18.
pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19. pose proof (bv_unsigned_in_range 64 (getr R (reg 20))) as B20.
pose proof (bv_unsigned_in_range 64 (getr R (reg 21))) as B21. pose proof (bv_unsigned_in_range 64 (getr R (reg 22))) as B22.
pose proof (bv_unsigned_in_range 64 (getr R (reg 23))) as B23. pose proof (bv_unsigned_in_range 64 (getr R (reg 24))) as B24.
pose proof (bv_unsigned_in_range 64 (getr R (reg 25))) as B25. pose proof (bv_unsigned_in_range 64 (getr R (reg 26))) as B26.
pose proof (bv_unsigned_in_range 64 (getr R (reg 27))) as B27.
change (bv_modulus 64) with (2 ^ 64) in B1, B8, B9, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27.
assert (QsF : (sp - 104) + 104 <= F \/ F + 128 <= (sp - 104)) by (clear - GFCEIL SL208; lia).
assert (QsFL : (sp - 104) + 104 <= fl \/ fl + 1 <= (sp - 104)) by (clear - GFLR SL208; lia).
assert (QsSF : (sp - 104) + 104 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 16 <= (sp - 104)).
{ right. pose proof GFR as (GF1 & GF2 & _). assert (D2 : F / 8 <= 17592186044400) by (apply Z.div_le_upper_bound; clear - GF2; lia). clear - D2 SL208 SPT; lia. }
cfeed P (PMBIGP2.bigR_conc fx7 R7 MV7 (fun j => match j with 2%nat => sp | 36%nat => os | 47%nat => F | 48%nat => fl | 50%nat => X
| 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9))
| 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20))
| 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23))
| 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26))
| 76%nat => bv_unsigned (getr R (reg 27)) | _ => 0 end)) ltac:(first [assumption | unfold PMBIGP2.aligned; assumption | clear - SL208 SHI SPT; lia]).
destruct P as (fx8 & R8 & M8v & MG8 & _ & FRZ8 & MS8 & KS8 & E1 & E2 & E8 & E9 & _ & _ & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & FL0 & _).
assert (R8ra : getr R8 (reg 1) = Z_to_bv 64 r) by (rewrite E1, Z_to_bv_bv_unsigned; exact Rra).
pose proof (PMK.ret_to RSEGS fx8 R8 M8v 0xafed8 (ltac:(oW' 0xafed8%Z)) r (ltac:(oF' 0xafed8%Z)) eq_refl (ltac:(oD' 0xafed8%Z)) R8ra Hr1 Hr2) as MSr.
apply (PMBUK.retire_core L ar C HI LYa HIok M model LB FF LK Aw sp 20480 X (sp - 104) sp (PMBSU.ocell13 sp) (PMBSU.own13 sp R) F fl 1 LK2 M2 model2 cr [] G
WS [] M7 model7 LK7 cr Aw7 fx7 fx8 R7 0xafe04 R8 r M8v K BI7 (msteps_trans _ _ _ _ MS8 MSr) MG8).
{ intros a Ha Nw. unfold PMBUK.Wret in Nw. change (ff_bytes 1) with 128 in Nw. change (128 / 8) with 16 in Nw.
apply FRZ8; [exact Ha| intros Y; apply Nw; left; left; clear - Y; lia| intros Y; apply Nw; left; right; unfold SB; clear - Y; lia| intros Y; apply Nw; right; clear - Y; lia]. }
{ exact FL0. }
intros Mf modelf FZf AHf MRTf AMf HHf.
pose proof BI7 as (HH7 & _ & _ & INCA7 & INCL7 & _).
assert (EKf : L5SAR.ek L ar LB FF 0 0 [] M7 Mf).
{ apply (PMBUAR.wret_ek L ar C HI LY HIok LB FF LK Aw sp 20480 X (sp - 104) sp (PMBSU.ocell13 sp) (PMBSU.own13 sp R) F fl 1 LK2 M2 model2 cr []
LB LK7 cr Aw7 M7 Mf _ [] (fun _ => False) G HH7 (fun a Y => match Y with end)).
intros a Ha N. apply FZf; [exact Ha| intros Y; apply N; left; exact Y]. }
pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH7) as BRB7.
assert (QC7 : PM.sr_qc src7 = qc) by (destruct STEP7 as (Y & _); exact Y).
apply (KONT fx8 R8 Mf modelf LK7 Aw7 src7 sm7).
- apply L5SAR.preserved_by_index. intros j Hj. pose proof Hj as Hj'. unfold L5SAR.cs_all in Hj.
repeat (destruct Hj as [<-|Hj]; [first [ rewrite E2; exact (eq_sym Rsp) | rewrite E8; apply Z_to_bv_bv_unsigned | rewrite E9; apply Z_to_bv_bv_unsigned
| rewrite E18; apply Z_to_bv_bv_unsigned | rewrite E19; apply Z_to_bv_bv_unsigned | rewrite E20; apply Z_to_bv_bv_unsigned
| rewrite E21; apply Z_to_bv_bv_unsigned | rewrite E22; apply Z_to_bv_bv_unsigned | rewrite E23; apply Z_to_bv_bv_unsigned
| rewrite E24; apply Z_to_bv_bv_unsigned | rewrite E25; apply Z_to_bv_bv_unsigned | rewrite E26; apply Z_to_bv_bv_unsigned
| rewrite E27; apply Z_to_bv_bv_unsigned
| rewrite (KS8 _) by inl; first [exact G73 | exact G74] ] |]).
destruct Hj.
- apply (PMKB.parser_keepA RSEGS PMB.AD L ar LB FF 0 0 [] M7 Mf EKf PMKB.wapp_nil FRB BRB7 _ _ _ AOP); [| intros i _ r0 []| intros i _ r0 []| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact PA7].
unfold PMSPA.with_src. destruct src7 as [qc7 de7 rem7]. cbn [PM.sr_qc] in QC7. subst qc7. exact BOWN.
- apply (PMKB.iss_keepA RSEGS PMB.AD L ar LB FF 0 0 [] M7 Mf EKf PMKB.wapp_nil FRB BRB7 ois str sm7 AOI); [exact SOWN| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA7].
- exact STEP7.
- exact RES7.
- exact AHf.
- exact MRTf.
- exact INCL7.
- exact INCA7.
- exact AMf.
- exact HHf. }
assert (APT : forall q m, In (q, m) LB -> q + m <= os \/ os + 296 <= q).
{ intros q m Hq. exact (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m os 296 HH Hq AO). }
assert (WSW : PMKB.wapp [(os + 256, 40)]).
{ apply PMKB.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct OBIG as [Y|Y]; [right; clear - Y; lia| left; clear - Y; lia]| apply PMKB.wapp_nil]. }
assert (OUTIS : forall i, ois <= i < ois + 272 -> L5.outside [(os + 256, 40)] i).
{ intros i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. unfold ois, os, PMSPA.o_is, PMSPA.o_src, PMSPA.o_p in *. cbn [pa_off_is pa_off_p PMB.AD ADDR_B] in *. clear - Hi. lia. }
assert (OUTBLK : forall c0 n0 p0, str = PM.VLong c0 n0 p0 -> forall i, p0 <= i < p0 + c0 -> L5.outside [(os + 256, 40)] i).
{ intros c0 n0 p0 E i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. assert (TIN : In (p0, c0) LB) by (apply SOWN; rewrite E; left; reflexivity).
destruct (APT p0 c0 TIN) as [Y|Y]; clear - Y Hi; lia. }
set (W3 := fun a => (X <= a < X + 88) \/ (F <= a < F + 24) \/ (F + 32 <= a < F + 40) \/ ((F / 8) + 2147450880 <= a < (F / 8) + 2147450880 + 16) \/ (os + 256 <= a < os + 296)).
assert (W3ok : forall a, 0 <= a < 2 ^ 64 -> W3 a -> aclientw L ar LB FF' 0 0 a /\ ~ (0x10000 <= a < 0x693000)).
{ intros a Ha Wa. split.
- destruct Wa as [Y|[Y|[Y|[Y|Y]]]].
+ unfold aclientw, aclient_g. right; left. split; [clear - Y SL208 SHI SPT HX1; lia| intros Z1; clear - Z1; lia].
+ apply (L5SAR.fframe_client L ar LB FF' 0 0 F 1 (X + 32)); [left; reflexivity| change (ff_bytes 1) with 128; clear - Y; lia].
+ apply (L5SAR.fframe_client L ar LB FF' 0 0 F 1 (X + 32)); [left; reflexivity| change (ff_bytes 1) with 128; clear - Y; lia].
+ apply (L5SAR.fframe_shadow_client L ar LB FF' 0 0 F 1 (X + 32)); [left; reflexivity|]. change (ff_bytes 1) with 128.
unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - Y; lia.
+ unfold aclientw, aclient_g. do 3 right; left. destruct AO as (f & Hf & Y1 & Y2). exists f. split; [right; exact Hf|]. clear - Y Y1 Y2; lia.
- pose proof GFR as (GF1 & GF2 & _). assert (D1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
destruct Wa as [Y|[Y|[Y|[Y|Y]]]]; clear - Y GFR D1 SL208 SPT HX1 O1; lia. }
assert (EKW3 : forall Ma Mb, (forall a, 0 <= a < 2 ^ 64 -> ~ W3 a -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) -> L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] Ma Mb).
{ intros Ma Mb FZ. apply (L5SAR.ek_piece L ar LB FF sp 20480 [(os + 256, 40)] Ma Mb W3 FZ). intros a Ha Hc Ho Wa.
destruct Wa as [Y|[Y|[Y|[Y|Y]]]].
- apply (NCS0 a); [clear - Y HX1; lia| exact Hc].
- apply (GNCF a); [left; change (ff_bytes 1) with 128; clear - Y; lia| exact Hc].
- apply (GNCF a); [left; change (ff_bytes 1) with 128; clear - Y; lia| exact Hc].
- apply (GNCF a); [right; change (ff_bytes 1) with 128; unfold S; rewrite (proj1 (proj2 GF8)); unfold SB; clear - Y; lia| exact Hc].
- apply (Ho (os + 256, 40)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Y; lia]. }
assert (BEXIT : forall (fx3 : FPState) R3 M3v de' rem',
msteps RSEGS (L5A.st fx1 R2 0xafb6c MV2) (L5A.st fx3 R3 0xafe04 M3v) -> mem_grows MV2 M3v ->
(forall i, 0 <= i < 2 ^ 64 -> ~ W3 i -> M3v (Z_to_bv 64 i) = MV2 (Z_to_bv 64 i)) ->
getr R3 (reg 2) = Z_to_bv 64 X -> getr R3 (reg 8) = Z_to_bv 64 sp -> getr R3 (reg 9) = Z_to_bv 64 X ->
getr R3 (reg 26) = Z_to_bv 64 ((F / 8) + 2147450880) -> getr R3 (reg 3) = getr R2 (reg 3) -> getr R3 (reg 4) = getr R2 (reg 4) ->
L5.u64_at RSEGS M3v (X + 8) F -> L5.u64_at RSEGS M3v (X + 16) F ->
L5.u64_at RSEGS M3v (os + 264) qc -> L5.u64_at RSEGS M3v (os + 272) 16384 -> L5.u64_at RSEGS M3v (os + 280) de' -> L5.u64_at RSEGS M3v (os + 288) rem' ->
qc <= de' -> 0 <= rem' -> de' + rem' <= qc + 16384 ->
PMSPA.src_step (PM.p_src s) (PM.SRC qc de' rem') (PM.STRM g eg st) (PM.STRM g eg st) ->
PMSPA.ignore_res R R M (PM.p_src s) (PM.SRC qc de' rem') (PM.STRM g eg st) (PM.STRM g eg st) ->
srealizes RSEGS SCFG (@L5A.cfg fx1 R2 0xafb6c M2 model2) K).
{ intros fx3 R3 M3v de' rem' MS3 MG3 FRZ3 Y2 Y8 Y9 Y26 Y3 Y4 YX8 YX16 Y264 Y272 Y280 Y288 Hd1 Hd2 Hd3 STEP RES.
apply (L5SAR.apiece L ar C HI LYa HIok LB FF' LK2 cr Aw M2 model2 fx1 fx3 R2 0xafb6c R3 0xafe04 M3v W3 K HH2 AM2 MS3 MG3 FRZ3 W3ok).
intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3. change (mrestrict H2 M3 = M3v) in VIS3.
assert (EK23 : L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M2 M3) by exact (EKW3 M2 M3 FR3).
assert (EK03 : L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M M3).
{ apply (L5SAR.ek_trans L ar LB FF sp 20480 _ M M2 M3); [| exact EK23].
apply (L5SAR.ek_W L ar LB FF sp 20480 _ [] M M2 EK02f). intros a _ r0 []. }
assert (TO3 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M3 a v).
{ intros a v Ha Hb Y. rewrite <- VIS3 in Y. apply (proj1 (L5A.u64_at_vis _ M3 a v ltac:(apply OAV2; clear - Ha Hb; lia) ltac:(clear - Ha O1; lia) ltac:(clear - Hb O1; lia))). exact Y. }
assert (TX3 : forall a v, X <= a -> a + 8 <= X + 96 -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M3 a v).
{ intros a v Ha Hb Y. rewrite <- VIS3 in Y.
apply (proj1 (L5A.u64_at_vis _ M3 a v (VISs2 a 8 ltac:(clear - Ha SL208 SPT HX1; lia) ltac:(clear - Hb QX; lia)) ltac:(clear - Ha Q0e; lia) ltac:(clear - Hb QX; lia))). exact Y. }
assert (PA3 : PM.parser_at RSEGS PMB.AD PMSPA.accA PMSPA.annA M3 (PMSPA.o_p PMB.AD fb) ois (PMSPA.with_src s (PM.SRC qc de' rem'))).
{ apply (PMBSU.src_piece_parserB L ar LB FF fb ois s de' rem' sp 20480 M2 M3 FRB BRB APT WSW FOK BOWN EK23 MGM3 PA2);
cbn [PM.p_src s PM.sr_qc]; unfold PM.CHUNK; [apply TO3; [clear; lia| clear; lia| assumption]..| assumption| assumption| assumption]. }
assert (IA3 : PM.iss_at RSEGS PMB.AD PMSPA.accA M3 ois str (PM.STRM g eg st)).
{ apply (PMKB.iss_keepA RSEGS PMB.AD L ar LB FF sp 20480 _ M2 M3 EK23 WSW FRB BRB ois str _ AOI); [exact SOWN| exact OUTIS| exact OUTBLK| exact IA2]. }
assert (BI3 : PMBUK.binv L ar HI M model LB FF LK Aw sp 20480 X (PMBSU.own13 sp R) F 1 WS [] M3 model3 LK2 cr Aw).
{ unfold PMBUK.binv. split; [exact HH3|]. split; [exact AM3|].
split; [eapply L5LZ.model_rt_trans; [exact MRT1| eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3]]|].
split; [apply incl_refl|]. split; [exact GLKI2|]. split; [exact (L5SAR.astk_grows ar M2 M3 sp 20480 ASTK2 MGM3)|].
split.
{ apply (L5SAR.ek_trans L ar LB FF sp 20480 WS M M2 M3).
- apply (L5SAR.ek_W L ar LB FF sp 20480 WS [] M M2 EK02f). intros a _ r0 [].
- apply (L5SAR.ek_W L ar LB FF sp 20480 WS [(os + 256, 40)] M2 M3 EK23). intros a Ho r0 [<-|[]] Y. apply (Ho (os + 256, 40)); [left; reflexivity| exact Y]. }
split; [apply (L5SAR.dk_trans L ar LB FF sp 20480 M M2 M3 DK02f); apply L5SAR.dk_grows; exact MGM3|].
split.
{ apply (PMBSU.own13_agree sp R M1 M3 ltac:(clear - SL208 SPT; lia) ltac:(clear - SHI SPT; lia) OWN1). intros a Ha. unfold PMBSU.ocell13 in Ha.
rewrite FR3; [apply AGF; clear - Ha HX1; lia| clear - Ha SL208 SHI SPT; lia|].
pose proof GFR as (GF1 & GF2 & _). assert (D2 : F / 8 <= 17592186044400) by (apply Z.div_le_upper_bound; clear - GF2; lia).
intros [Y|[Y|[Y|[Y|Y]]]]; clear - Y Ha HX1 GFCEIL SL208 SPT OCE D2; lia. }
change (ff_bytes 1 / 8) with 16. apply (L5.defined_grows M2 M3 _ _ MGM3).
apply (proj1 (L5A.defined_vis H2 M2 (F / 8 + SB) 16 VSH)). intros i Hi. pose proof (FSHZ i Hi) as Z0. unfold MV2 in Z0. rewrite Z0. discriminate. }
apply (EXITP fx3 R3 M3 model3 LK2 Aw (PM.SRC qc de' rem') (PM.STRM g eg st) BI3 Y2 Y8 Y9 Y26).
- rewrite Y3. rewrite (B34 3%nat) by (left; reflexivity). reflexivity.
- rewrite Y4. rewrite (B34 4%nat) by (right; left; reflexivity). reflexivity.
- apply TX3; [clear; lia| clear; lia| exact YX8].
- apply TX3; [clear; lia| clear; lia| exact YX16].
- exact PA3.
- exact IA3.
- exact STEP.
- exact RES. }
assert (QDE : 4096 <= de <= 140737488338944) by (clear - G1 G2 G3 Q0 Q4 SL208 SHI SPT; unfold PM.CHUNK in *; lia).
assert (QDE2 : 0 <= de < 2 ^ 64) by (clear - QDE; lia).
assert (QREM : 0 <= rem < 2 ^ 64) by (clear - G1 G2 G3 QDE; unfold PM.CHUNK in *; lia).
assert (TRANS : forall (Ma Mb : word -> option byte), (forall i, 0 <= i < 2 ^ 64 -> ~ W3 i -> Mb (Z_to_bv 64 i) = Ma (Z_to_bv 64 i)) ->
(forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ W3 i) -> forall i, a <= i < a + n -> Mb (Z_to_bv 64 i) = Ma (Z_to_bv 64 i))).
{ intros Ma Mb FZ a n H0 H1 NW i Hi. apply FZ; [clear - H0 H1 Hi; lia| apply NW; exact Hi]. }
pose proof GFR as (GF1 & GF2 & _). assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
assert (DF2 : F / 8 <= 17592186044400) by (apply Z.div_le_upper_bound; clear - GF2; lia).
destruct (Z_le_gt_dec 2 rem) as [REM2|REM1].
{
cfeed P (PMBIGP1.bigB1b_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 33%nat => rem | 34%nat => qc | 35%nat => de | 36%nat => os
| 47%nat => F | 48%nat => fl | 50%nat => X | _ => 0 end)) ltac:(first [assumption | unfold PMBIGP1.aligned; assumption | clear - REM2 S288 Q0 Q4 G1 G2 G3; unfold PM.CHUNK in *; lia]).
destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Z5 & Z10 & Z11 & Z12 & Z13 & Z14 & Z15 & Z16 & Z17 & Z18 & Z20 & Z21 & Z22 & Z25 & Z26
& ZX16 & ZX8 & ZX80 & ZF32 & SH11 & SH10 & SH9 & SH8 & SH3 & SH2 & SH1 & SH0 & SH7 & SH6 & SH5 & SH4 & HD16 & HD8 & HD0 & ZX56
& Z264 & Z272 & ZD256 & Z280 & Z288 & ZD24 & ZD40 & ZZ12).
assert (FZ3' : forall i, 0 <= i < 2 ^ 64 -> ~ W3 i -> M3v (Z_to_bv 64 i) = MV2 (Z_to_bv 64 i)).
{ intros i Hi N. apply FRZ3; [exact Hi|..]; intros Y; apply N; unfold W3; clear - Y; lia. }
pose proof (TRANS MV2 M3v FZ3') as TR3.
assert (T3img : L5.img_clear M3v 65536 1269760).
{ intros i Hi. rewrite (TR3 65536 1204224 ltac:(clear; lia) ltac:(clear; lia)) by (first [clear - Hi; lia | intros j Hj; unfold W3; clear - Hj DF1 DF2 QX QFR O1; lia]). apply W0; exact Hi. }
assert (T3sb : L5.u64_at RSEGS M3v 1296952 2147450880).
{ apply (L5C.u64_at_agree RSEGS MV2 M3v); [intros i Hi; apply (TR3 1296952 8); [clear; lia| clear; lia| intros j Hj; unfold W3; clear - Hj DF1 DF2 QX QFR O1; lia| exact Hi]| clear; lia| clear; lia| exact W1]. }
assert (T3uar : L5.u32_at RSEGS M3v 1296960 1).
{ apply (PMF.u32_at_agree RSEGS MV2 M3v); [intros i Hi; apply (TR3 1296960 4); [clear; lia| clear; lia| intros j Hj; unfold W3; clear - Hj DF1 DF2 QX QFR O1; lia| exact Hi]| clear; lia| clear; lia| exact W2]. }
assert (T3oz : L5KA.zeros_at M3v (((os + 8) / 8) + 2147450880) 36).
{ apply (L5KA.zeros_at_agree1 MV2 M3v); [| exact OZ2]. intros i Hi. apply (TR3 (((os + 8) / 8) + 2147450880) 36); [| | | exact Hi].
- pose proof (Z.div_pos (os + 8) 8 ltac:(clear - O1; lia) ltac:(clear; lia)). clear - H0; lia.
- assert ((os + 8) / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; clear - O1; lia). clear - H0; lia.
- intros j Hj. assert (E8 : (os + 8) / 8 = os / 8 + 1) by (rewrite <- (Z.div_add os 1 8) by lia; f_equal; lia). rewrite E8 in Hj.
assert (D3 : os / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; clear - O1; lia).
assert (D4 : 0 <= os / 8) by (apply Z.div_pos; clear - O1; lia).
unfold W3. destruct QoSF as [Y|Y]; destruct GFBIG as [Y2|Y2]; destruct OBIG as [Y3|Y3]; clear - Hj Y Y2 Y3 D3 D4 QX QFR O1 DF1 DF2; lia. }
assert (T3fl : L5.u64_at RSEGS M3v (F + 120) fl).
{ apply (L5C.u64_at_agree RSEGS MV2 M3v); [intros i Hi; apply (TR3 (F + 120) 8); [clear - QFR; lia| clear - QFR; lia| intros j Hj; unfold W3; destruct GFBIG as [Y2|Y2]; clear - Hj Y2 DF1 DF2 QX QFR QXF QoF; lia| exact Hi]| clear - QFR; lia| clear - QFR; lia| exact FLCv]. }
assert (T3z32 : L5KA.zeros_at M3v (((F + 32) / 8) + 2147450880) 1).
{ replace ((F + 32) / 8) with (F / 8 + 4) by (rewrite <- (Z.div_add F 4 8) by lia; f_equal; lia).
intros i Hi. replace i with 0 by (clear - Hi; lia). rewrite Z.add_0_r. replace (F / 8 + 4 + 2147450880) with ((F / 8) + 2147450884) by (clear; lia).
apply (L5ADHR.byte_of_u8 M3v _ 0 SH4); [right| ]; clear - DF1 DF2; lia. }
assert (T3wX : L5.writable RSEGS M3v X 96) by exact (L5.writable_grows RSEGS MV2 M3v X 96 MG3 WX2).
assert (T3wo : L5.writable RSEGS M3v os 296) by exact (L5.writable_grows RSEGS MV2 M3v os 296 MG3 OW2).
assert (T3dF : L5.defined M3v F 128) by exact (L5.defined_grows MV2 M3v F 128 MG3 FDEF).
assert (T3wF : L5.writable RSEGS M3v F 128) by exact (L5.writable_grows RSEGS MV2 M3v F 128 MG3 FW).
assert (T3wS : L5.writable RSEGS M3v ((F / 8) + 2147450880) 16) by exact (L5.writable_grows RSEGS MV2 M3v _ 16 MG3 FSHW).
assert (T3wl : L5.writable RSEGS M3v fl 1) by exact (L5.writable_grows RSEGS MV2 M3v fl 1 MG3 FLW).
assert (Y2 : getr R3 (reg 2) = Z_to_bv 64 X) by (rewrite (KS3 2%nat) by inl; exact B2R).
assert (Y8 : getr R3 (reg 8) = Z_to_bv 64 sp) by (rewrite (KS3 8%nat) by inl; exact B8R).
assert (Y9 : getr R3 (reg 9) = Z_to_bv 64 X) by (rewrite (KS3 9%nat) by inl; exact B9R).
assert (Y19 : getr R3 (reg 19) = Z_to_bv 64 os) by (rewrite (KS3 19%nat) by inl; exact B19R).
assert (Y23 : getr R3 (reg 23) = Z_to_bv 64 1) by (rewrite (KS3 23%nat) by inl; exact B23R).
cfeed P (PMBIGP1.bigB1b2_conc fx3 R3 M3v (fun j => match j with 2%nat => sp | 33%nat => rem | 34%nat => qc | 35%nat => de | 36%nat => os
| 47%nat => F | 48%nat => fl | 50%nat => X | _ => 0 end)) ltac:(first [assumption | unfold PMBIGP1.aligned; assumption | clear - REM2 S288 Q0 Q4 G1 G2 G3; unfold PM.CHUNK in *; lia]).
destruct P as (fx4 & R4 & M4v & MG4 & _ & FRZ4 & MS4 & KS4 & _ & _ & _ & _ & _ & U288 & U280 & U264 & U272).
apply (BEXIT fx4 R4 M4v (de + 1) (rem - 1)).
- eapply msteps_trans; [exact MS3| exact MS4].
- intros x Hx. apply MG4. apply MG3. exact Hx.
- intros i Hi N. rewrite FRZ4 by (first [exact Hi| intros Y; apply N; unfold W3; clear - Y; lia]). apply FZ3'; [exact Hi| exact N].
- rewrite (KS4 2%nat) by inl. exact Y2.
- rewrite (KS4 8%nat) by inl. exact Y8.
- rewrite (KS4 9%nat) by inl. exact Y9.
- rewrite (KS4 26%nat) by inl. exact Z26.
- rewrite (KS4 3%nat) by inl. rewrite (KS3 3%nat) by inl. reflexivity.
- rewrite (KS4 4%nat) by inl. rewrite (KS3 4%nat) by inl. reflexivity.
- apply (L5C.u64_at_agree RSEGS M3v M4v); [intros i Hi; apply FRZ4; [clear - Hi QX; lia| clear - Hi QXo; lia]| clear - QX; lia| clear - QX; lia| exact ZX8].
- apply (L5C.u64_at_agree RSEGS M3v M4v); [intros i Hi; apply FRZ4; [clear - Hi QX; lia| clear - Hi QXo; lia]| clear - QX; lia| clear - QX; lia| exact ZX16].
- exact U264.
- exact U272.
- exact U280.
- exact U288.
- clear - G1; lia.
- clear - REM2; lia.
- clear - G3; unfold PM.CHUNK in *; lia.
- unfold PMSPA.src_step, PM.unread. cbn. lia.
- unfold PMSPA.ignore_res, PMSPA.consumed, PM.unread. cbn. split; [left; lia| intros _; lia]. }
destruct (Z.eq_dec rem 1) as [REQ1|REM0].
{
pose proof (PMBIGP1.bigB1a_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 34%nat => qc | 35%nat => de | 36%nat => os
| 47%nat => F | 48%nat => fl | 50%nat => X | _ => 0 end)) as P.
cbn beta iota in P. rewrite REQ1 in VS288.
L5SAR.feed P ltac:(first [assumption | unfold PMBIGP1.aligned; assumption]).
destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Y26 & _ & Y288 & Y280 & YX16 & YX8 & _
& _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Y264 & Y272 & _ & _ & _).
apply (BEXIT fx3 R3 M3v (de + 1) 0 MS3 MG3).
- intros i Hi N. apply FRZ3; [exact Hi|..]; intros Y; apply N; unfold W3; clear - Y; lia.
- rewrite (KS3 2%nat) by inl. exact B2R.
- rewrite (KS3 8%nat) by inl. exact B8R.
- rewrite (KS3 9%nat) by inl. exact B9R.
- exact Y26.
- rewrite (KS3 3%nat) by inl. reflexivity.
- rewrite (KS3 4%nat) by inl. reflexivity.
- exact YX8.
- exact YX16.
- exact Y264.
- exact Y272.
- exact Y280.
- exact Y288.
- clear - G1; lia.
- clear; lia.
- clear - G3 REQ1; unfold PM.CHUNK in *; lia.
- unfold PMSPA.src_step, PM.unread. cbn. lia.
- unfold PMSPA.ignore_res, PMSPA.consumed, PM.unread. cbn. split; [left; lia| intros _; lia]. }
assert (REMZ : rem = 0) by (clear - REM1 REM0 G2; lia).
rewrite REMZ in VS288.
cfeed P (PMBIGP1.bigB0_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 34%nat => qc | 35%nat => de | 36%nat => os
| 47%nat => F | 48%nat => fl | 50%nat => X | _ => 0 end)) ltac:(first [assumption | unfold PMBIGP1.aligned; assumption]).
destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y5 & Y10 & Y11 & Y12 & _ & _ & _ & _ & Y17 & Y18 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27
& Y280 & YX24 & YX32 & YX40 & YX0 & YX48 & YX16 & YX8 & YX80 & YF32 & SH11 & SH10 & SH9 & SH8 & SH3 & SH2 & SH1 & SH0 & SH7 & SH6 & SH5 & SH4
& HD16 & HD8 & HD0 & YX56 & Y264 & Y272 & YD256 & Y288 & YD24 & YD40 & YZ12).
apply (L5SAR.apiece L ar C HI LYa HIok LB FF' LK2 cr Aw M2 model2 fx1 fx3 R2 0xafb6c R3 0xb0e58 M3v W3 K HH2 AM2 MS3 MG3).
{ intros i Hi N. apply FRZ3; [exact Hi|..]; intros Y; apply N; unfold W3; clear - Y; lia. }
{ exact W3ok. }
intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3. change (mrestrict H2 M3 = M3v) in VIS3.
assert (EK23 : L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M2 M3) by exact (EKW3 M2 M3 FR3).
assert (TO3 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M3 a v).
{ intros a v Ha Hb Y. rewrite <- VIS3 in Y. apply (proj1 (L5A.u64_at_vis _ M3 a v ltac:(apply OAV2; clear - Ha Hb; lia) ltac:(clear - Ha O1; lia) ltac:(clear - Hb O1; lia))). exact Y. }
assert (TX3 : forall a v, X <= a -> a + 8 <= X + 96 -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M3 a v).
{ intros a v Ha Hb Y. rewrite <- VIS3 in Y.
apply (proj1 (L5A.u64_at_vis _ M3 a v (VISs2 a 8 ltac:(clear - Ha SL208 SPT HX1; lia) ltac:(clear - Hb QX; lia)) ltac:(clear - Ha Q0e; lia) ltac:(clear - Hb QX; lia))). exact Y. }
assert (TF3 : forall a v, F <= a -> a + 8 <= F + 128 -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M3 a v).
{ intros a v Ha Hb Y. rewrite <- VIS3 in Y.
apply (proj1 (L5A.u64_at_vis _ M3 a v (L5A.avis_sub H2 F 128 a 8 VF ltac:(clear - Ha; lia) ltac:(clear - Hb; lia)) ltac:(clear - Ha Q0c; lia) ltac:(clear - Hb QFR; lia))). exact Y. }
assert (TS3 : forall a v, F / 8 + SB <= a -> a + 1 <= F / 8 + SB + 16 -> L5.u8_at RSEGS M3v a v -> L5.u8_at RSEGS M3 a v).
{ intros a v Ha Hb Y. rewrite <- VIS3 in Y. unfold SB in Ha, Hb.
apply (proj1 (L5A.u8_at_vis _ M3 a v (L5A.avis_sub H2 (F / 8 + SB) 16 a 1 VSH ltac:(unfold SB; clear - Ha; lia) ltac:(unfold SB; clear - Hb; lia)) ltac:(clear - Ha DF1; lia) ltac:(clear - Hb DF2; lia))). exact Y. }
set (s1 := PMSPA.with_src s (PM.SRC qc qc 0)) in *.
assert (PA3 : PM.parser_at RSEGS PMB.AD PMSPA.accA PMSPA.annA M3 (PMSPA.o_p PMB.AD fb) ois s1).
{ apply (PMBSU.src_piece_parserB L ar LB FF fb ois s qc 0 sp 20480 M2 M3 FRB BRB APT WSW FOK BOWN EK23 MGM3 PA2);
cbn [PM.p_src s PM.sr_qc]; unfold PM.CHUNK; [apply TO3; [clear; lia| clear; lia| assumption]..| clear; lia| clear; lia| clear; lia]. }
assert (IA3 : PM.iss_at RSEGS PMB.AD PMSPA.accA M3 ois str (PM.STRM g eg st)).
{ apply (PMKB.iss_keepA RSEGS PMB.AD L ar LB FF sp 20480 _ M2 M3 EK23 WSW FRB BRB ois str _ AOI); [exact SOWN| exact OUTIS| exact OUTBLK| exact IA2]. }
assert (BASE3 : PMSTA.base_okA RSEGS PMB.AD M3).
{ apply (PMBSK.base_keep L ar C LY LB FF sp 20480 _ M2 M3 EK23); [| exact BASE2].
intros a Ha r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. clear - Ha O1. lia. }
assert (BI3 : PMBUK.binv L ar HI M model LB FF LK Aw sp 20480 X (PMBSU.own13 sp R) F 1 WS [] M3 model3 LK2 cr Aw).
{ unfold PMBUK.binv. split; [exact HH3|]. split; [exact AM3|].
split; [eapply L5LZ.model_rt_trans; [exact MRT1| eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3]]|].
split; [apply incl_refl|]. split; [exact GLKI2|]. split; [exact (L5SAR.astk_grows ar M2 M3 sp 20480 ASTK2 MGM3)|].
split.
{ apply (L5SAR.ek_trans L ar LB FF sp 20480 WS M M2 M3).
- apply (L5SAR.ek_W L ar LB FF sp 20480 WS [] M M2 EK02f). intros a _ r0 [].
- apply (L5SAR.ek_W L ar LB FF sp 20480 WS [(os + 256, 40)] M2 M3 EK23). intros a Ho r0 [<-|[]] Y. apply (Ho (os + 256, 40)); [left; reflexivity| exact Y]. }
split; [apply (L5SAR.dk_trans L ar LB FF sp 20480 M M2 M3 DK02f); apply L5SAR.dk_grows; exact MGM3|].
split.
{ apply (PMBSU.own13_agree sp R M1 M3 ltac:(clear - SL208 SPT; lia) ltac:(clear - SHI SPT; lia) OWN1). intros a Ha. unfold PMBSU.ocell13 in Ha.
rewrite FR3; [apply AGF; clear - Ha HX1; lia| clear - Ha SL208 SHI SPT; lia|].
intros [Y|[Y|[Y|[Y|Y]]]]; clear - Y Ha HX1 GFCEIL SL208 SPT OCE DF2; lia. }
change (ff_bytes 1 / 8) with 16. apply (L5.defined_grows M2 M3 _ _ MGM3).
apply (proj1 (L5A.defined_vis H2 M2 (F / 8 + SB) 16 VSH)). intros i Hi. pose proof (FSHZ i Hi) as Z0. unfold MV2 in Z0. rewrite Z0. discriminate. }
assert (WAPPS : PMKB.wapp WS).
{ unfold WS, PMSPA.W_src, PMSPA.W_srcf. cbn [app PM.p_src s PM.sr_qc].
fold os ois.
repeat apply PMKB.wapp_cons; [..| apply PMKB.wapp_nil]; cbn [fst snd]; unfold PM.CHUNK, BIGSHADOW_LO, BIGSHADOW_HI.
- destruct OBIG as [Y|Y]; [right; clear - Y; lia| left; clear - Y; lia].
- destruct INSH as [Y|Y]; [right; clear - Y; lia| left; clear - Y; lia].
- destruct INSH as [Y|Y]; [right; clear - Y; lia| left; clear - Y; lia].
- unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5. destruct Q5 as (_ & [Y|Y] & _); [left; clear - Y; lia| right; clear - Y; lia]. }
assert (STK3 : shadow_zero M3 (X - 18432) (18432 / 8)).
{ change (18432 / 8) with 2304.
assert (M8a : (sp - 20480) mod 8 = 0) by (apply PMKB.mod16_8'; replace (sp - 20480) with (sp + (-1280) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16).
assert (M8b : (X - 18432) mod 8 = 0) by (apply PMKB.mod16_8'; replace (X - 18432) with (X + (-1152) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact HX16).
pose proof BI3 as (_ & _ & _ & _ & _ & _ & EK3 & _).
apply (PMKB.stksh_keepA L ar LB FF sp 20480 WS M M3 EK3 WAPPS (X - 18432) 2304); [clear - HX1 SL208 SPT; lia| clear - HX1 SLO; lia| clear - HX1 SHI SPT; lia| exact M8b| clear; lia|].
apply (PMKB.shadow_zero_sub M (sp - 20480) 2560); [exact M8a| exact M8b| clear - HX1; lia| clear - HX1; lia| clear; lia| exact STKSH]. }
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH3) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDF3 & _).
unfold PMB.fill_buffer_spec, PMSPA.fill_buffer_spec, PMSPA.src_spec in FB.
apply (FB fx3 R3 M3 model3 K LBX FF' LK2 Aw cr X 0xafd54 fb s1 str (PM.STRM g eg st) [] HH3 AM3 K0).
{ split; [rewrite L5K.rl1; exact Y1|]. split; [split; [clear; lia| reflexivity]|]. split; [rewrite L5K.rl2; rewrite (KS3 2%nat) by inl; exact B2R|].
split; [rewrite L5K.rl3; rewrite (KS3 3%nat) by inl; rewrite (B34 3%nat) by (left; reflexivity); rewrite <- L5K.rl3; exact Rgp|].
split; [rewrite L5K.rl4; rewrite (KS3 4%nat) by inl; rewrite (B34 4%nat) by (right; left; reflexivity); rewrite <- L5K.rl4; exact Rtp|].
change (PMSPA.pm_scr 3) with 18432. split; [|exact STK3].
pose proof (L5SAR.astk_sub ar M3 M3 sp 20480 (sp - X) 18432 (L5SAR.astk_grows ar M2 M3 sp 20480 ASTK2 MGM3) (fun _ Y => Y)) as AS.
replace (sp - (sp - X)) with X in AS by (clear; lia). apply AS; [clear - HX1; lia| clear; lia| clear - HX1; lia| exact HX16]. }
{ apply (PMBUAR.ffroomA_push 4 3 FF LK LK2 _ FRM GLKI2); [exact NDF3| clear; lia]. }
{ apply (PMBUAR.ffrsA_push FF sp X F 1 (X + 32) FRS); clear - HX1; lia. }
{ exact FOK'. }
{ unfold PMSPA.o_src. fold os. exact Y10. }
{ split; [rewrite L5SAR.r11; exact Y11| rewrite L5SAR.r12; exact Y12]. }
{ reflexivity. }
{ exact PA3. }
{ exact IA3. }
{ exact BASE3. }
{ exact INCS. }
intros fx4 R4 M4 model4 LK4 Aw4 src4 sm4 RP4 PA4 IA4 STEP4 RES4 HP4 MRT4 INCLK4 INCAw4 AM4 HH4.
change (PMSPA.pm_scr 3) with 18432 in HP4. rewrite app_nil_r in HP4.
assert (BI4 : PMBUK.binv L ar HI M model LB FF LK Aw sp 20480 X (PMBSU.own13 sp R) F 1 WS [] M4 model4 LK4 cr Aw4).
{ apply (PMBUK.binv_callee L ar C HI HIok M model LB FF LK Aw sp 20480 X (sp - 104) sp (PMBSU.ocell13 sp) (PMBSU.own13 sp R) F fl 1 LK2 M2 model2 cr [] G
WS WS [] [] [] M3 model3 LK2 cr Aw M4 model4 LK4 cr Aw4 18432 WS BI3 HP4 HH4 AM4 MRT4 INCAw4 INCLK4); [clear; lia| clear - HX1; lia| | | intros a Y; exact Y].
- intros rr a Hin Hr. unfold WS, PMSPA.W_src, PMSPA.W_srcf in Hin. cbn [app PM.p_src s PM.sr_qc] in Hin. fold os ois in Hin.
unfold PMBSU.ocell13, SB. change (ff_bytes 1 / 8) with 16. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; unfold PM.CHUNK in Hr.
+ destruct OBIG as [Y|Y]; clear - Hr Y OCE SL208 SPT DF1 DF2; split; lia.
+ destruct INSH as [Y|Y]; clear - Hr Y ICE SL208 SPT DF1 DF2; split; lia.
+ destruct INSH as [Y|Y]; clear - Hr Y ICE SL208 SPT DF1 DF2; split; lia.
+ unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5. destruct Q5 as (_ & [Y|Y] & _); clear - Hr Y Q4 SL208 SPT DF1 DF2; split; lia.
- intros a _ Y. exact Y. }
destruct RES4 as (E4 & c & A10c & Hc & G4c & _ & _). subst src4. unfold PM.CHUNK in Hc.
rewrite L5K.rl10 in A10c.
assert (R4c : forall j, In j L5SAR.cs_all -> getr R4 (reg j) = getr R3 (reg j)) by (intros j Hj; exact (L5SAR.cs_of_preserved R3 R4 j RP4 Hj)).
set (H4 := ahid Aw4 model4) in *. set (MV4 := mrestrict H4 M4) in *.
destruct (PMBUK.vis_facts L ar C HI LYa HIok M model LB FF LK Aw sp 20480 X (sp - 104) sp (PMBSU.ocell13 sp) (PMBSU.own13 sp R) F fl 1 LK2 M2 model2 cr [] G
WS [] M4 model4 LK4 cr Aw4 BI4) as ((WS4 & _ & _ & _ & _) & _ & (FD4 & FW4 & FSW4 & FLC4 & FLW4) & (_ & _ & VF4 & VS4 & VSH4)).
change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *. fold H4 MV4 in WS4, FD4, FW4, FSW4, FLC4, FLW4.
replace (F + 128 - 8) with (F + 120) in FLC4 by (clear; lia).
assert (WX4 : L5.writable RSEGS MV4 X 96) by (apply (L5.writable_sub RSEGS MV4 X (sp - X)); [exact WS4| clear; lia| clear - HX1; lia]).
pose proof (L5SAR.ek_callee L ar LB [] FF' [] X 18432 X 18432 WS WS M3 M4 HP4 ltac:(clear; lia) ltac:(clear; lia) (fun a _ Y => Y)) as EK34.
pose proof (PMBSK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ qc 16384 HH QIN) as QIMG.
assert (BASE4 : PMSTA.base_okA RSEGS PMB.AD M4).
{ apply (PMBSK.base_keep L ar C LY LB FF' X 18432 WS M3 M4 EK34); [| exact BASE3].
intros a Ha r0 Hr. unfold WS, PMSPA.W_src, PMSPA.W_srcf in Hr. cbn [app PM.p_src s PM.sr_qc] in Hr. fold os ois in Hr. unfold L5.in_rng.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; unfold PM.CHUNK; destruct QIMG as [Y|Y]; clear - Ha O1 I1 Y; lia. }
assert (KEEP4 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF' X 18432 a -> L5.outside WS a -> M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
{ intros a Ha Hcl Ho. apply (proj1 HP4). split; [exact Ha| split; [exact Hcl| exact Ho]]. }
assert (OUTWS : forall a, (X <= a < sp \/ F <= a < F + 128 \/ F / 8 + SB <= a < F / 8 + SB + 16) -> L5.outside WS a).
{ intros a Ha r0 Hr. unfold WS, PMSPA.W_src, PMSPA.W_srcf in Hr. cbn [app PM.p_src s PM.sr_qc] in Hr. fold os ois in Hr. unfold L5.in_rng, SB in *.
pose proof (proj2 (APART qc 16384 0 0 ltac:(intros i Hi; left; exists (qc, 16384); split; [exact QIN| cbn [fst snd]; clear - Hi; lia]) ltac:(clear; lia))) as (AqSF & _).
pose proof (proj1 (APART qc 16384 0 0 ltac:(intros i Hi; left; exists (qc, 16384); split; [exact QIN| cbn [fst snd]; clear - Hi; lia]) ltac:(clear; lia))) as AqF.
destruct (APART ois 272 0 0 ltac:(intros i Hi; destruct AOI as (f & Hf & Z1 & Z2); unfold aclient, aclient_g; do 3 right; left; exists f; split; [exact Hf| clear - Z1 Z2 Hi; lia]) ltac:(clear; lia)) as (AiF & AiSF & _).
unfold SB in AqSF, AiSF.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; unfold PM.CHUNK.
- destruct OBIG as [Y|Y]; clear - Ha Y OCE SL208 SPT DF1 DF2 QoF HX1; lia.
- destruct INSH as [Y|Y]; clear - Ha Y ICE SL208 SPT DF1 DF2 AiF HX1; lia.
- destruct INSH as [Y|Y]; clear - Ha Y ICE SL208 SPT DF1 DF2 AiF HX1; lia.
- unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5. destruct Q5 as (_ & [Y|Y] & _); clear - Ha Y Q4 SL208 SPT DF1 DF2 AqF HX1; lia. }
assert (KX4 : forall a v, X <= a -> a + 8 <= X + 96 -> L5.u64_at RSEGS M3 a v -> L5.u64_at RSEGS MV4 a v).
{ intros a v Ha Hb Y.
apply (proj2 (L5A.u64_at_vis H4 M4 a v (L5A.avis_sub H4 X (sp - X) a 8 VS4 ltac:(clear - Ha; lia) ltac:(clear - Hb HX1; lia)) ltac:(clear - Ha Q0e; lia) ltac:(clear - Hb QX; lia))).
apply (L5C.u64_at_agree RSEGS M3 M4); [intros i Hi; apply KEEP4; [clear - Hi Ha Hb QX; lia| apply L5SAR.stack_client; [clear - Hi Ha Hb QX SL208 SHI SPT HX1; lia| clear - Hi Ha; lia]| apply OUTWS; clear - Hi Ha Hb HX1; lia]
| clear - Ha Q0e; lia| clear - Hb QX; lia| exact Y]. }
assert (KF4 : forall a v, F + 32 <= a -> a + 8 <= F + 40 -> L5.u64_at RSEGS M3 a v -> L5.u64_at RSEGS MV4 a v).
{ intros a v Ha Hb Y.
apply (proj2 (L5A.u64_at_vis H4 M4 a v (L5A.avis_sub H4 F 128 a 8 VF4 ltac:(clear - Ha; lia) ltac:(clear - Hb; lia)) ltac:(clear - Ha Q0c; lia) ltac:(clear - Hb QFR; lia))).
apply (L5C.u64_at_agree RSEGS M3 M4); [intros i Hi; apply KEEP4; [clear - Hi Ha Hb QFR; lia| apply (L5SAR.fframe_client L ar LB FF' X 18432 F 1 (X + 32)); [left; reflexivity| change (ff_bytes 1) with 128; clear - Hi Ha Hb; lia]| apply OUTWS; clear - Hi Ha Hb; lia]
| clear - Ha Q0c; lia| clear - Hb QFR; lia| exact Y]. }
assert (KS4 : forall a v, F / 8 + 2147450880 <= a -> a + 1 <= F / 8 + 2147450880 + 16 -> L5.u8_at RSEGS M3 a v -> L5.u8_at RSEGS MV4 a v).
{ intros a v Ha Hb Y.
apply (proj2 (L5A.u8_at_vis H4 M4 a v (L5A.avis_sub H4 (F / 8 + SB) 16 a 1 VSH4 ltac:(unfold SB; clear - Ha; lia) ltac:(unfold SB; clear - Hb; lia)) ltac:(clear - Ha DF1; lia) ltac:(clear - Hb DF2; lia))).
apply (L5C.u8_at_agree RSEGS M3 M4); [intros i Hi; apply KEEP4; [clear - Hi Ha Hb DF1 DF2; lia| apply (L5SAR.fframe_shadow_client L ar LB FF' X 18432 F 1 (X + 32)); [left; reflexivity| change (ff_bytes 1) with 128; unfold in_shadow_of, S; rewrite (proj1 (proj2 GF8)); unfold SB; clear - Hi Ha Hb; lia]
| apply OUTWS; unfold SB; clear - Hi Ha Hb; lia]| clear - Ha DF1; lia| clear - Hb DF2; lia| exact Y]. }
assert (U4x56 : L5.u64_at RSEGS MV4 (X + 56) 2147450880) by (apply KX4; [clear; lia| clear; lia| apply TX3; [clear; lia| clear; lia| exact YX56]]).
assert (U4x0 : L5.u64_at RSEGS MV4 X (os + 272)) by (replace X with (X + 0) at 1 by (clear; lia); apply KX4; [clear; lia| clear; lia| rewrite Z.add_0_r; apply TX3; [clear; lia| clear; lia| exact YX0]]).
assert (U4x8 : L5.u64_at RSEGS MV4 (X + 8) F) by (apply KX4; [clear; lia| clear; lia| apply TX3; [clear; lia| clear; lia| exact YX8]]).
assert (U4x16 : L5.u64_at RSEGS MV4 (X + 16) F) by (apply KX4; [clear; lia| clear; lia| apply TX3; [clear; lia| clear; lia| exact YX16]]).
assert (U4x24 : L5.u64_at RSEGS MV4 (X + 24) (((os + 256) / 8) + 2147450880)) by (apply KX4; [clear; lia| clear; lia| apply TX3; [clear; lia| clear; lia| exact YX24]]).
assert (U4x32 : L5.u64_at RSEGS MV4 (X + 32) (((os + 272) / 8) + 2147450880)) by (apply KX4; [clear; lia| clear; lia| apply TX3; [clear; lia| clear; lia| exact YX32]]).
assert (U4x40 : L5.u64_at RSEGS MV4 (X + 40) (((os + 264) / 8) + 2147450880)) by (apply KX4; [clear; lia| clear; lia| apply TX3; [clear; lia| clear; lia| exact YX40]]).
assert (U4x48 : L5.u64_at RSEGS MV4 (X + 48) (os + 264)) by (apply KX4; [clear; lia| clear; lia| apply TX3; [clear; lia| clear; lia| exact YX48]]).
assert (U4x80 : L5.u64_at RSEGS MV4 (X + 80) F) by (apply KX4; [clear; lia| clear; lia| apply TX3; [clear; lia| clear; lia| exact YX80]]).
assert (U4f32 : L5.u64_at RSEGS MV4 (F + 32) 1) by (apply KF4; [clear; lia| clear; lia| apply TF3; [clear; lia| clear; lia| exact YF32]]).
assert (U4s4 : L5.u8_at RSEGS MV4 ((F / 8) + 2147450884) 0) by (apply KS4; [clear; lia| clear; lia| apply TS3; [unfold SB; clear; lia| unfold SB; clear; lia| exact SH4]]).
assert (U4s8 : L5.u8_at RSEGS MV4 ((F / 8) + 2147450888) 248) by (apply KS4; [clear; lia| clear; lia| apply TS3; [unfold SB; clear; lia| unfold SB; clear; lia| exact SH8]]).
pose proof BI4 as (_ & _ & _ & _ & _ & ASTK4 & _).
pose proof (PMBSK.src_vis L ar C HI LY HIok LB FF' LK4 cr Aw4 M4 model4 fb ois s1 sp 20480 HH4 FOK' PA4 ASTK4)
as ((_ & _ & _) & OZ4 & OW4 & _ & OAV4 & _ & _ & _). fold os MV4 in OZ4, OW4, OAV4.
pose proof (PMBSK.mach_vis L ar C HI LY HIok _ _ LK4 cr Aw4 M4 model4 HH4 BASE4) as (W40 & W41 & W42). fold MV4 in W40, W41, W42.
pose proof PA4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PSRC4 & _).
destruct PSRC4 as (_ & _ & SD4 & S264c & S272c & S280c & S288c & _ & _ & _ & _ & _ & _ & _). cbn [PM.p_src s1 s PMSPA.with_src PM.sr_qc PM.sr_de PM.sr_rem] in SD4, S264c, S272c, S280c, S288c.
fold os in SD4, S264c, S272c, S280c, S288c. unfold PM.CHUNK in S272c.
assert (V4264 : L5.u64_at RSEGS MV4 (os + 264) qc) by (apply (proj2 (L5A.u64_at_vis _ M4 (os + 264) qc ltac:(apply OAV4; clear; lia) ltac:(clear - O1; lia) ltac:(clear - O1; lia))); exact S264c).
assert (V4272 : L5.u64_at RSEGS MV4 (os + 272) 16384) by (apply (proj2 (L5A.u64_at_vis _ M4 (os + 272) _ ltac:(apply OAV4; clear; lia) ltac:(clear - O1; lia) ltac:(clear - O1; lia))); exact S272c).
assert (V4280 : L5.u64_at RSEGS MV4 (os + 280) qc) by (apply (proj2 (L5A.u64_at_vis _ M4 (os + 280) qc ltac:(apply OAV4; clear; lia) ltac:(clear - O1; lia) ltac:(clear - O1; lia))); exact S280c).
assert (V4288 : L5.u64_at RSEGS MV4 (os + 288) 0) by (apply (proj2 (L5A.u64_at_vis _ M4 (os + 288) 0 ltac:(apply OAV4; clear; lia) ltac:(clear - O1; lia) ltac:(clear - O1; lia))); exact S288c).
assert (V4256 : L5.defined MV4 (os + 256) 8) by (apply (proj2 (L5A.defined_vis _ M4 (os + 256) 8 ltac:(apply OAV4; clear; lia))); exact SD4).
assert (G42 : getr R4 (reg 2) = Z_to_bv 64 X) by (rewrite (R4c 2%nat) by inl; rewrite (KS3 2%nat) by inl; exact B2R).
assert (G48 : getr R4 (reg 8) = Z_to_bv 64 sp) by (rewrite (R4c 8%nat) by inl; rewrite (KS3 8%nat) by inl; exact B8R).
assert (G49 : getr R4 (reg 9) = Z_to_bv 64 X) by (rewrite (R4c 9%nat) by inl; rewrite (KS3 9%nat) by inl; exact B9R).
assert (G418 : getr R4 (reg 18) = Z_to_bv 64 (F + 32)) by (rewrite (R4c 18%nat) by inl; exact Y18).
assert (G419 : getr R4 (reg 19) = Z_to_bv 64 os) by (rewrite (R4c 19%nat) by inl; rewrite (KS3 19%nat) by inl; exact B19R).
assert (G420 : getr R4 (reg 20) = Z_to_bv 64 (os + 288)) by (rewrite (R4c 20%nat) by inl; exact Y20).
assert (G421 : getr R4 (reg 21) = Z_to_bv 64 (os + 280)) by (rewrite (R4c 21%nat) by inl; exact Y21).
assert (G422 : getr R4 (reg 22) = Z_to_bv 64 (os + 256)) by (rewrite (R4c 22%nat) by inl; exact Y22).
assert (G423 : getr R4 (reg 23) = Z_to_bv 64 (((os + 280) / 8) + 2147450880)) by (rewrite (R4c 23%nat) by inl; exact Y23).
assert (G424 : getr R4 (reg 24) = Z_to_bv 64 (F + 64)) by (rewrite (R4c 24%nat) by inl; exact Y24).
assert (G425 : getr R4 (reg 25) = Z_to_bv 64 (((os + 288) / 8) + 2147450880)) by (rewrite (R4c 25%nat) by inl; exact Y25).
assert (G426 : getr R4 (reg 26) = Z_to_bv 64 ((F / 8) + 2147450880)) by (rewrite (R4c 26%nat) by inl; exact Y26).
assert (G427 : getr R4 (reg 27) = Z_to_bv 64 0) by (rewrite (R4c 27%nat) by inl; exact Y27).
assert (G434 : forall j, In j [3; 4]%nat -> getr R4 (reg j) = getr R (reg j)).
{ intros j Hj. rewrite (R4c j) by (destruct Hj as [<-|[<-|[]]]; inl). rewrite (KS3 j) by (destruct Hj as [<-|[<-|[]]]; inl). apply B34. exact Hj. }
assert (QC : 0 <= c < 2 ^ 64) by (clear - Hc; lia).
assert (QQC : 4096 <= qc <= 140737488338944) by (clear - Q0 Q4 SL208 SHI SPT; lia).
set (W5 := fun a => (F + 64 <= a < F + 72) \/ ((F / 8) + 2147450880 + 8 <= a < (F / 8) + 2147450880 + 9) \/ (os + 256 <= a < os + 296)).
assert (CEXIT : forall (fx5 : FPState) R5 M5v de' rem',
msteps RSEGS (L5A.st fx4 R4 0xafd54 MV4) (L5A.st fx5 R5 0xafe04 M5v) -> mem_grows MV4 M5v ->
(forall i, 0 <= i < 2 ^ 64 -> ~ W5 i -> M5v (Z_to_bv 64 i) = MV4 (Z_to_bv 64 i)) ->
getr R5 (reg 2) = Z_to_bv 64 X -> getr R5 (reg 8) = Z_to_bv 64 sp -> getr R5 (reg 9) = Z_to_bv 64 X ->
getr R5 (reg 26) = Z_to_bv 64 ((F / 8) + 2147450880) -> getr R5 (reg 3) = getr R4 (reg 3) -> getr R5 (reg 4) = getr R4 (reg 4) ->
L5.u64_at RSEGS M5v (os + 264) qc -> L5.u64_at RSEGS M5v (os + 272) 16384 -> L5.u64_at RSEGS M5v (os + 280) de' -> L5.u64_at RSEGS M5v (os + 288) rem' ->
qc <= de' -> 0 <= rem' -> de' + rem' <= qc + 16384 ->
PMSPA.src_step (PM.p_src s) (PM.SRC qc de' rem') (PM.STRM g eg st) sm4 ->
PMSPA.ignore_res R R M (PM.p_src s) (PM.SRC qc de' rem') (PM.STRM g eg st) sm4 ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx4 R4 0xafd54 M4 model4) K).
{ intros fx5 R5 M5v de' rem' MS5 MG5 FRZ5 Y52 Y58 Y59 Y526 Y53 Y54 Y5264 Y5272 Y5280 Y5288 Hd1 Hd2 Hd3 STEP RES. unfold PMSPA.cfg.
assert (W5ok : forall a, 0 <= a < 2 ^ 64 -> W5 a -> aclientw L ar LB FF' 0 0 a /\ ~ (0x10000 <= a < 0x693000)).
{ intros a Ha Wa. split.
- destruct Wa as [Y|[Y|Y]].
+ apply (L5SAR.fframe_client L ar LB FF' 0 0 F 1 (X + 32)); [left; reflexivity| change (ff_bytes 1) with 128; clear - Y; lia].
+ apply (L5SAR.fframe_shadow_client L ar LB FF' 0 0 F 1 (X + 32)); [left; reflexivity|]. change (ff_bytes 1) with 128.
unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - Y; lia.
+ unfold aclientw, aclient_g. do 3 right; left. destruct AO as (f & Hf & Z1 & Z2). exists f. split; [right; exact Hf|]. clear - Y Z1 Z2; lia.
- destruct Wa as [Y|[Y|Y]]; clear - Y GFR DF1 O1; lia. }
pose proof BI4 as (HH4b & _).
apply (L5SAR.apiece L ar C HI LYa HIok ([] ++ LB) FF' LK4 cr Aw4 M4 model4 fx4 fx5 R4 0xafd54 R5 0xafe04 M5v W5 K HH4b AM4 MS5 MG5 FRZ5 W5ok).
intros M5 model5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5 VV5. change (mrestrict H4 M5 = M5v) in VIS5.
assert (EK45 : L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M4 M5).
{ apply (L5SAR.ek_piece L ar LB FF sp 20480 [(os + 256, 40)] M4 M5 W5 FR5). intros a Ha Hcl Ho Wa.
destruct Wa as [Y|[Y|Y]].
- apply (GNCF a); [left; change (ff_bytes 1) with 128; clear - Y; lia| exact Hcl].
- apply (GNCF a); [right; change (ff_bytes 1) with 128; unfold S; rewrite (proj1 (proj2 GF8)); unfold SB; clear - Y; lia| exact Hcl].
- apply (Ho (os + 256, 40)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Y; lia]. }
assert (TO5 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M5v a v -> L5.u64_at RSEGS M5 a v).
{ intros a v Ha Hb Y. rewrite <- VIS5 in Y. apply (proj1 (L5A.u64_at_vis _ M5 a v ltac:(apply OAV4; clear - Ha Hb; lia) ltac:(clear - Ha O1; lia) ltac:(clear - Hb O1; lia))). exact Y. }
assert (PA5 : PM.parser_at RSEGS PMB.AD PMSPA.accA PMSPA.annA M5 (PMSPA.o_p PMB.AD fb) ois (PMSPA.with_src s (PM.SRC qc de' rem'))).
{ pose proof (PMBSU.src_piece_parserB L ar LB FF fb ois s1 de' rem' sp 20480 M4 M5 FRB BRB APT WSW FOK BOWN EK45 MGM5 PA4) as Z.
cbn [PM.p_src s1 s PMSPA.with_src PM.sr_qc] in Z. unfold PM.CHUNK in Z.
apply Z; [apply TO5; [clear; lia| clear; lia| assumption]..| assumption| assumption| assumption]. }
assert (IA5 : PM.iss_at RSEGS PMB.AD PMSPA.accA M5 ois str sm4).
{ apply (PMKB.iss_keepA RSEGS PMB.AD L ar LB FF sp 20480 _ M4 M5 EK45 WSW FRB BRB ois str _ AOI); [exact SOWN| exact OUTIS| exact OUTBLK| exact IA4]. }
assert (BI5 : PMBUK.binv L ar HI M model LB FF LK Aw sp 20480 X (PMBSU.own13 sp R) F 1 WS [] M5 model5 LK4 cr Aw4).
{ apply (PMBUK.binv_pieceW L ar HI M model LB FF LK Aw sp 20480 X (sp - 104) sp (PMBSU.ocell13 sp) (PMBSU.own13 sp R) F fl 1 LK2 M2 model2 cr [] G
WS [] M4 model4 LK4 cr Aw4 M5 model5 W5 BI4 HH5 AM5 MRT5 MGM5 FR5).
intros a Wa. change (ff_bytes 1) with 128. change (128 / 8) with 16. unfold PMBSU.ocell13, SB.
destruct Wa as [Y|[Y|Y]].
- split; [clear - Y GFCEIL SL208; lia| right; left; clear - Y; lia].
- split; [clear - Y DF2 SL208 SPT; lia| right; right; left; clear - Y; lia].
- split; [clear - Y OCE SL208; lia| right; right; right]. intros Ho. apply (Ho (os + 256, 40)); [unfold WS, PMSPA.W_src, PMSPA.W_srcf; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Y; lia]. }
assert (TX5 : forall a v, X <= a -> a + 8 <= X + 96 -> L5.u64_at RSEGS MV4 a v -> L5.u64_at RSEGS M5 a v).
{ intros a v Ha Hb Y. apply (proj1 (L5A.u64_at_vis H4 M5 a v (L5A.avis_sub H4 X (sp - X) a 8 VS4 ltac:(clear - Ha; lia) ltac:(clear - Hb HX1; lia)) ltac:(clear - Ha Q0e; lia) ltac:(clear - Hb QX; lia))).
rewrite VIS5. apply (L5C.u64_at_agree RSEGS MV4 M5v); [intros i Hi; apply FRZ5; [clear - Hi Ha Hb QX; lia| unfold W5; clear - Hi Ha Hb QXF QXo DF2 QX; lia]| clear - Ha Q0e; lia| clear - Hb QX; lia| exact Y]. }
apply (EXITP fx5 R5 M5 model5 LK4 Aw4 (PM.SRC qc de' rem') sm4 BI5 Y52 Y58 Y59 Y526).
- rewrite Y53. apply G434. left; reflexivity.
- rewrite Y54. apply G434. right; left; reflexivity.
- apply TX5; [clear; lia| clear; lia| exact U4x8].
- apply TX5; [clear; lia| clear; lia| exact U4x16].
- exact PA5.
- exact IA5.
- exact STEP.
- exact RES. }
destruct sm4 as [g4 eg4 st4]. cbn [PM.sm_g PM.sm_eg PM.sm_st] in G4c.
pose proof STEP4 as (_ & E4eg & E4g & E4st & _). cbn [PM.sm_g PM.sm_eg PM.sm_st] in E4eg, E4g, E4st.
assert (SS : forall de' rem', rem' + (eg4 - g4) <= 0 + (eg - g) -> qc <= de' ->
PMSPA.src_step (PM.p_src s) (PM.SRC qc de' rem') (PM.STRM g eg st) (PM.STRM g4 eg4 st4)).
{ intros de' rem' U Hq. unfold PMSPA.src_step, PM.unread. cbn [PM.p_src s PM.sr_qc PM.sr_rem PM.sm_g PM.sm_eg PM.sm_st].
rewrite REMZ. split; [reflexivity|]. split; [exact E4eg|]. split; [clear - E4g; lia|]. split; [exact E4st| clear - U; lia]. }
assert (RR : forall de' rem', rem' + (eg4 - g4) = 0 + (eg - g) \/ rem' + (eg4 - g4) = 0 + (eg - g) - 1 ->
PMSPA.ignore_res R R M (PM.p_src s) (PM.SRC qc de' rem') (PM.STRM g eg st) (PM.STRM g4 eg4 st4)).
{ intros de' rem' U. unfold PMSPA.ignore_res, PMSPA.consumed, PM.unread. cbn [PM.p_src s PM.sr_qc PM.sr_rem PM.sm_g PM.sm_eg PM.sm_st].
rewrite REMZ. split; [destruct U as [U|U]; [right| left]; clear - U; lia| intros Y; clear - Y; lia]. }
destruct (Z.eq_dec c 0) as [C0|CN0].
{
subst c.
cfeed P (PMBIGP2.bigC0_conc fx4 R4 MV4 (fun j => match j with 2%nat => sp | 34%nat => qc | 36%nat => os | 47%nat => F | 48%nat => fl | 50%nat => X | _ => 0 end)) ltac:(first [assumption | unfold PMBIGP2.aligned; assumption]).
destruct P as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & _ & _ & Z288 & Z264 & Z272 & _ & Z280).
apply (CEXIT fx5 R5 M5v qc 0 MS5 MG5).
- intros i Hi N. apply FRZ5; [exact Hi|..]; intros Y; apply N; unfold W5; clear - Y; lia.
- rewrite (KS5 2%nat) by inl. exact G42.
- rewrite (KS5 8%nat) by inl. exact G48.
- rewrite (KS5 9%nat) by inl. exact G49.
- rewrite (KS5 26%nat) by inl. exact G426.
- rewrite (KS5 3%nat) by inl. reflexivity.
- rewrite (KS5 4%nat) by inl. reflexivity.
- exact Z264. - exact Z272. - exact Z280. - exact Z288.
- clear; lia. - clear; lia. - clear; lia.
- apply SS; [rewrite G4c, E4eg; clear; lia| clear; lia].
- apply RR. left. rewrite G4c, E4eg. clear; lia. }
destruct (Z.eq_dec c 1) as [C1|CN1].
{
subst c.
cfeed P (PMBIGP2.bigC1a_conc fx4 R4 MV4 (fun j => match j with 2%nat => sp | 34%nat => qc | 36%nat => os | 47%nat => F | 48%nat => fl | 50%nat => X | _ => 0 end)) ltac:(first [assumption | unfold PMBIGP2.aligned; assumption]).
destruct P as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & _ & _ & _ & _ & _ & Z288 & Z280 & _ & _ & Z264 & Z272 & _ & _).
apply (CEXIT fx5 R5 M5v (qc + 1) 0 MS5 MG5).
- intros i Hi N. apply FRZ5; [exact Hi|..]; intros Y; apply N; unfold W5; clear - Y; lia.
- rewrite (KS5 2%nat) by inl. exact G42.
- rewrite (KS5 8%nat) by inl. exact G48.
- rewrite (KS5 9%nat) by inl. exact G49.
- rewrite (KS5 26%nat) by inl. exact G426.
- rewrite (KS5 3%nat) by inl. reflexivity.
- rewrite (KS5 4%nat) by inl. reflexivity.
- exact Z264. - exact Z272. - exact Z280. - exact Z288.
- clear; lia. - clear; lia. - clear; lia.
- apply SS; [rewrite G4c, E4eg; clear; lia| clear; lia].
- apply RR. right. rewrite G4c, E4eg. clear; lia. }
{
assert (C2 : 2 <= c <= 16384) by (clear - Hc CN0 CN1; lia).
cfeed P (PMBIGP2.bigC1b_conc fx4 R4 MV4 (fun j => match j with 2%nat => sp | 34%nat => qc | 36%nat => os | 47%nat => F | 48%nat => fl | 50%nat => X
| 51%nat => c | _ => 0 end)) ltac:(first [assumption | unfold PMBIGP2.aligned; assumption]).
destruct P as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Z11 & Z12 & Z13 & Z64 & ZS8 & Z288 & Z264 & Z272 & ZD256 & Z280 & _ & _).
assert (FZ5' : forall i, 0 <= i < 2 ^ 64 -> ~ W5 i -> M5v (Z_to_bv 64 i) = MV4 (Z_to_bv 64 i)).
{ intros i Hi N. apply FRZ5; [exact Hi|..]; intros Y; apply N; unfold W5; clear - Y; lia. }
assert (TR5 : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ W5 i) -> forall i, a <= i < a + n -> M5v (Z_to_bv 64 i) = MV4 (Z_to_bv 64 i)).
{ intros a n H0 H1 NW i Hi. apply FZ5'; [clear - H0 H1 Hi; lia| apply NW; exact Hi]. }
assert (T5img : L5.img_clear M5v 65536 1269760).
{ intros i Hi. rewrite (TR5 65536 1204224 ltac:(clear; lia) ltac:(clear; lia)) by (first [clear - Hi; lia | intros j Hj; unfold W5; clear - Hj DF1 DF2 QFR O1; lia]). apply W40; exact Hi. }
assert (T5sb : L5.u64_at RSEGS M5v 1296952 2147450880).
{ apply (L5C.u64_at_agree RSEGS MV4 M5v); [intros i Hi; apply (TR5 1296952 8); [clear; lia| clear; lia| intros j Hj; unfold W5; clear - Hj DF1 DF2 QFR O1; lia| exact Hi]| clear; lia| clear; lia| exact W41]. }
assert (T5uar : L5.u32_at RSEGS M5v 1296960 1).
{ apply (PMF.u32_at_agree RSEGS MV4 M5v); [intros i Hi; apply (TR5 1296960 4); [clear; lia| clear; lia| intros j Hj; unfold W5; clear - Hj DF1 DF2 QFR O1; lia| exact Hi]| clear; lia| clear; lia| exact W42]. }
assert (T5X : forall a v, X <= a -> a + 8 <= X + 96 -> L5.u64_at RSEGS MV4 a v -> L5.u64_at RSEGS M5v a v).
{ intros a v Ha Hb Y. apply (L5C.u64_at_agree RSEGS MV4 M5v); [intros i Hi; apply (TR5 a 8); [clear - Ha Q0e; lia| clear - Hb QX; lia| intros j Hj; unfold W5; clear - Hj Ha Hb QXF QXo DF2 QX; lia| exact Hi]
| clear - Ha Q0e; lia| clear - Hb QX; lia| exact Y]. }
assert (T5oz : L5KA.zeros_at M5v (((os + 8) / 8) + 2147450880) 36).
{ apply (L5KA.zeros_at_agree1 MV4 M5v); [| exact OZ4]. intros i Hi. apply (TR5 (((os + 8) / 8) + 2147450880) 36); [| | | exact Hi].
- pose proof (Z.div_pos (os + 8) 8 ltac:(clear - O1; lia) ltac:(clear; lia)). clear - H0; lia.
- assert ((os + 8) / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; clear - O1; lia). clear - H0; lia.
- intros j Hj. assert (E8 : (os + 8) / 8 = os / 8 + 1) by (rewrite <- (Z.div_add os 1 8) by lia; f_equal; lia). rewrite E8 in Hj.
assert (D3 : os / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; clear - O1; lia).
assert (D4 : 0 <= os / 8) by (apply Z.div_pos; clear - O1; lia).
unfold W5. destruct QoSF as [Y|Y]; destruct GFBIG as [Y2|Y2]; destruct OBIG as [Y3|Y3]; clear - Hj Y Y2 Y3 D3 D4 QFR O1 DF1 DF2; lia. }
assert (T5fl : L5.u64_at RSEGS M5v (F + 120) fl).
{ apply (L5C.u64_at_agree RSEGS MV4 M5v); [intros i Hi; apply (TR5 (F + 120) 8); [clear - QFR; lia| clear - QFR; lia| intros j Hj; unfold W5; destruct GFBIG as [Y2|Y2]; clear - Hj Y2 DF1 DF2 QFR QoF; lia| exact Hi]| clear - QFR; lia| clear - QFR; lia| exact FLC4]. }
assert (T5f32 : L5.u64_at RSEGS M5v (F + 32) 1).
{ apply (L5C.u64_at_agree RSEGS MV4 M5v); [intros i Hi; apply (TR5 (F + 32) 8); [clear - QFR; lia| clear - QFR; lia| intros j Hj; unfold W5; destruct GFBIG as [Y2|Y2]; clear - Hj Y2 DF1 DF2 QFR QoF; lia| exact Hi]| clear - QFR; lia| clear - QFR; lia| exact U4f32]. }
assert (T5z64 : L5KA.zeros_at M5v (((F + 64) / 8) + 2147450880) 1).
{ replace ((F + 64) / 8) with (F / 8 + 8) by (rewrite <- (Z.div_add F 8 8) by lia; f_equal; lia).
intros i Hi. replace i with 0 by (clear - Hi; lia). rewrite Z.add_0_r. replace (F / 8 + 8 + 2147450880) with ((F / 8) + 2147450888) by (clear; lia).
apply (L5ADHR.byte_of_u8 M5v _ 0 ZS8); [right| ]; clear - DF1 DF2; lia. }
assert (T5wX : L5.writable RSEGS M5v X 96) by exact (L5.writable_grows RSEGS MV4 M5v X 96 MG5 WX4).
assert (T5wo : L5.writable RSEGS M5v os 296) by exact (L5.writable_grows RSEGS MV4 M5v os 296 MG5 OW4).
assert (T5dF : L5.defined M5v F 128) by exact (L5.defined_grows MV4 M5v F 128 MG5 FD4).
assert (T5wF : L5.writable RSEGS M5v F 128) by exact (L5.writable_grows RSEGS MV4 M5v F 128 MG5 FW4).
assert (T5wS : L5.writable RSEGS M5v ((F / 8) + 2147450880) 16) by exact (L5.writable_grows RSEGS MV4 M5v _ 16 MG5 FSW4).
assert (T5wl : L5.writable RSEGS M5v fl 1) by exact (L5.writable_grows RSEGS MV4 M5v fl 1 MG5 FLW4).
assert (U5x56 : L5.u64_at RSEGS M5v (X + 56) 2147450880) by (apply T5X; [clear; lia| clear; lia| exact U4x56]).
assert (U5x0 : L5.u64_at RSEGS M5v X (os + 272)) by (replace X with (X + 0) at 1 by (clear; lia); apply T5X; [clear; lia| clear; lia| rewrite Z.add_0_r; exact U4x0]).
assert (U5x8 : L5.u64_at RSEGS M5v (X + 8) F) by (apply T5X; [clear; lia| clear; lia| exact U4x8]).
assert (U5x16 : L5.u64_at RSEGS M5v (X + 16) F) by (apply T5X; [clear; lia| clear; lia| exact U4x16]).
assert (U5x24 : L5.u64_at RSEGS M5v (X + 24) (((os + 256) / 8) + 2147450880)) by (apply T5X; [clear; lia| clear; lia| exact U4x24]).
assert (U5x32 : L5.u64_at RSEGS M5v (X + 32) (((os + 272) / 8) + 2147450880)) by (apply T5X; [clear; lia| clear; lia| exact U4x32]).
assert (U5x40 : L5.u64_at RSEGS M5v (X + 40) (((os + 264) / 8) + 2147450880)) by (apply T5X; [clear; lia| clear; lia| exact U4x40]).
assert (U5x48 : L5.u64_at RSEGS M5v (X + 48) (os + 264)) by (apply T5X; [clear; lia| clear; lia| exact U4x48]).
assert (U5x80 : L5.u64_at RSEGS M5v (X + 80) F) by (apply T5X; [clear; lia| clear; lia| exact U4x80]).
assert (G510 : getr R5 (reg 10) = Z_to_bv 64 c) by (rewrite (KS5 10%nat) by inl; exact A10c).
cfeed P (PMBIGP2.bigC1b2_conc fx5 R5 M5v (fun j => match j with 2%nat => sp | 34%nat => qc | 36%nat => os | 47%nat => F | 48%nat => fl | 50%nat => X
| 51%nat => c | _ => 0 end)) ltac:(first [assumption | unfold PMBIGP2.aligned; assumption | rewrite (KS5 _) by inl; assumption]).
destruct P as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & MS6 & KS6 & _ & _ & _ & _ & _ & _ & V6288 & V6280 & _ & V6264 & V6272 & _ & _).
apply (CEXIT fx6 R6 M6v (qc + 1) (c - 1)).
- eapply msteps_trans; [exact MS5| exact MS6].
- intros x Hx. apply MG6. apply MG5. exact Hx.
- intros i Hi N. rewrite FRZ6 by (first [exact Hi| intros Y; apply N; unfold W5; clear - Y; lia]). apply FZ5'; [exact Hi| exact N].
- rewrite (KS6 2%nat) by inl. rewrite (KS5 2%nat) by inl. exact G42.
- rewrite (KS6 8%nat) by inl. rewrite (KS5 8%nat) by inl. exact G48.
- rewrite (KS6 9%nat) by inl. rewrite (KS5 9%nat) by inl. exact G49.
- rewrite (KS6 26%nat) by inl. rewrite (KS5 26%nat) by inl. exact G426.
- rewrite (KS6 3%nat) by inl. rewrite (KS5 3%nat) by inl. reflexivity.
- rewrite (KS6 4%nat) by inl. rewrite (KS5 4%nat) by inl. reflexivity.
- exact V6264. - exact V6272. - exact V6280. - exact V6288.
- clear; lia. - clear - C2; lia. - clear - C2; lia.
- apply SS; [rewrite G4c, E4eg; clear; lia| clear; lia].
- apply RR. right. rewrite G4c, E4eg. clear; lia. }
Qed.
End WithHeap.
End PMBSIG.
