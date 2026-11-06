(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StreamSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreA L5StepAR PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAa PmModelFactsA PmStep PmStepA PmStepA2 PmCertKitG PmAErrP.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmAErr () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAa.PMA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StreamSim."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1option"; "1true"; "2and"; "2eq"; "3Z"; "0HI"; "0L"; "0M"; "4img_clear"; "4u32_at"; "4u64_at"; "4u8_at"; "4writable"; "5make_ec_spec"; "6wseg_ok"]; ["7loaded_segments"; "0SCFG_P"; "8add"; "8le"; "8lt"; "8pow"; "8to_nat"; "0a"; "0ar"; "0n"; "9Z_to_bv"; "9bv"; "9bv_unsigned"; "0v"; "0w"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia.
Module PMAERR.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Lemma writable_img : ltac2:(TCodec.tc2 tcn__PmAErr "Q@'KyR0%211'1y8%511%311p051'5'4'0&?&@&Jr2%22>1&Fr1%211%83741(2%<3;21&Czr3%3221&D%1243&Br5r4%3221&E+2+R0%3221%>251&=r7r6%34L21;p051p0?1p0B1p0G1pQDQ51pQ@Q61pBQ81").
Proof. intros M a n.
intros W Ha Hn Han d k Hd Hk. destruct k as [|k]. reflexivity.
eapply (store_ok_sub RSEGS M (Z_to_bv 64 a) _ (Z.to_nat n) (Datatypes.S k)).
- rewrite L5.unsigned_lit by lia. rewrite Z2Nat.id by lia. lia.
- apply store_ok_wseg. exact W.
- rewrite !L5.unsigned_lit by lia. lia.
- rewrite !L5.unsigned_lit by lia. rewrite Z2Nat.id by lia. lia.
Qed.
Lemma u32_of_u64 : ltac2:(TCodec.tc2 tcn__PmAErr "F'KyR0%211'1y8%511%311p051'5&;&@r3r2r1%544321&:r4%247165p041pQL;1pQ@<1pB>1").
Proof. intros M a v.
unfold L5.u64_at, L5.u32_at. intros H. rewrite (SeqExec.rdn_firstn RSEGS M 8%nat (Z_to_bv 64 a) _ 4%nat H) by lia. reflexivity.
Qed.
Lemma nl_u8 : ltac2:(TCodec.tc2 tcn__PmAErr "D'KyR0%211'1y8%511%311p051&9r1+ValPC+ValPD%43321&<&@r2z%443271p061pB<1").
Proof. intros M.
intros IC. unfold L5.u8_at. rewrite (PMCG.rdn_img RSEGS M 0x68f013 0x68f014 0x68f013 1 IC) by lia. vm_compute. reflexivity.
Qed.
Lemma bvu : ltac2:(TCodec.tc2 tcn__PmAErr "B'KyR0%211'3&Cz&Lr1%2271%5241&D&E+2+R0%3221%5271%=271pQN?1").
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as X. change (bv_modulus 64) with (2 ^ 64) in X. exact X. Qed.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT.
Let LYa := PMA.ly_as0 L C LY.
Theorem make_ec_ok : ltac2:(TCodec.tc2 tcn__PmAErr "6&>vAv7vHv6%544321").
Proof.
unfold PMA.make_ec_spec, PMSPA.make_ec_spec.
intros fx R M model K LB FF LK Aw cr o v sp r b HH AM K0 ENT FRM FRS A10 A11 VR AO O8 OD ACC BASE ERR KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
pose proof AM as (Mh & MI). pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11.
change (PMSPA.pm_scr 1) with 14336 in *.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model o 16 sp 14336 HH (PMKA.aobj_of_aobjA FF o 16 AO O8) ltac:(lia) ltac:(reflexivity))
as ((O1 & O2 & O3 & O4 & O5) & OBIG & ODEF & OVIS & OSHV & OCL & OSHCL).
pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
assert (HO : bv_unsigned (getr R (reg 10)) = o) by (rewrite A10; apply L5.unsigned_lit; lia).
assert (V0 : L5.img_clear MV 1228800 1261568) by (apply L5A.img_clear_mrestrict; exact GOT).
assert (V1 : L5.u64_at RSEGS MV 1289464 2147450880) by (apply (proj2 (L5A.u64_at_vis H M 1289464 2147450880 (VIMG 1289464 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
assert (V2 : L5.u32_at RSEGS MV 1289472 1) by (apply (proj2 (L5A.u32_at_vis H M 1289472 1 (VIMG 1289472 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
assert (V3 : L5.writable RSEGS MV (sp - 128) 128).
{ apply (proj2 (L5A.writable_vis H M (sp - 128) 128 (VIS (sp - 128) 128 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
apply (L5C.writable_of_defined RSEGS). apply (L5.defined_sub M (sp - 14336) 14336); [exact SDEF| lia| lia]. lia. lia. }
assert (VZ : L5KA.zeros_at MV ((o / 8) + 2147450880) 2).
{ pose proof (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model o 16 HH AO O8 ltac:(lia) ltac:(reflexivity) ACC) as X.
exact X. }
assert (VW : L5.writable RSEGS MV o 16).
{ apply (proj2 (L5A.writable_vis H M o 16 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
set (WE := (o, 16) :: (if b then [] else PMSPA.err_W PMA.AD)).
assert (WAPP : PMKA.wapp WE).
{ unfold WE. apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia|].
destruct b; [apply PMKA.wapp_nil|]. unfold PMSPA.err_W. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A].
apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO; lia|]. apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO; lia|]. apply PMKA.wapp_nil. }
assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47).
{ intros f Hf. destruct (WF f Hf) as (X1 & X2 & _). unfold app_mem, FS_BYTES in *. lia. }
destruct ERR as (EG & EA).
unfold PMSPA.cfg. cbn [pa_make_ec PMA.AD ADDR_A].
destruct b.
-
cbn iota in EG. cbn [pa_errcat_guard PMA.AD ADDR_A] in EG.
assert (VG : L5.u8_at RSEGS MV 6738816 1).
{ apply (proj2 (L5A.u8_at_vis H M 6738816 1 (VIMG 6738816 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact EG. }
cfeed P (PMAERP.aerA_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => v | _ => 0 end)) ltac:(first [assumption | exact Rsp | unfold PMAERP.aligned; lia | lia]).
destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & B11 & C8 & C0).
assert (R1ra : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by inl; exact Rra).
pose proof (PMK.ret_to RSEGS fx1 R1 M1v 0xaea00 (ltac:(oW' 0xaea00%Z)) r (ltac:(oF' 0xaea00%Z)) eq_refl (ltac:(oD' 0xaea00%Z)) R1ra ltac:(lia) Hr2) as MS2.
apply (PMKA2.apiece_img L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xae974 R1 r M1v
(fun a => sp - 32 <= a < sp - 32 + 32 \/ o + 0 <= a < o + 0 + 16) K HH AM).
{ eapply msteps_trans; [exact MS1| exact MS2]. }
{ exact MG1. }
{ intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
{ intros a Ha [Wa|Wa].
- split; [|intros X; pose proof (PMA.ly_ro L C LY a X); lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
- split; [|intros X; pose proof (PMA.ly_ro L C LY a X); lia]. unfold aclientw, aclient_g. do 3 right. left.
destruct AO as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. split; [lia| intros X; lia]. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
assert (EK : L5SAR.ek L ar LB FF sp 14336 WE M M1).
{ apply (L5SAR.ek_piece L ar LB FF sp 14336 WE M M1 (fun a => (sp - 32 <= a < sp - 32 + 32) \/ (o + 0 <= a < o + 0 + 16))).
{ intros a Ha N. apply FR1; [exact Ha| exact N]. }
intros a Ha Hc Ho [X|X].
- destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M (vml_of model) sp 14336 a HH SPT Hc) as [(Y1 & Y2)|Y]; [apply Y2; lia| exfalso; lia].
- apply (Ho (o, 16)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
assert (U1 : forall a v0, o <= a -> a + 8 <= o + 16 -> L5.u64_at RSEGS M1v a v0 -> L5.u64_at RSEGS M1 a v0).
{ intros a v0 Ha Hb X. rewrite <- VIS1 in X. exact (proj1 (L5A.u64_at_vis H M1 a v0 ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia)) X). }
apply (KONT fx1 R1 M1 model1 LK Aw).
+ apply L5SAR.preserved_by_index. intros k Hk. apply KS1. unfold L5SAR.cs_all in Hk. repeat (destruct Hk as [<-|Hk]; [inl|]). destruct Hk.
+ split; [apply u32_of_u64; apply (U1 o v ltac:(lia) ltac:(lia) C0)|].
split; [cbn [pa_errcat_obj PMA.AD ADDR_A]; apply (U1 (o + 8) _ ltac:(lia) ltac:(lia) C8)|].
split; [apply (L5.defined_grows M M1 _ _ MGM1); exact OD|].
apply (PMKA.acc_keepA' L ar LB FF sp 14336 WE M M1 EK WAPP FRB o 16 AO ACC).
+ split.
* cbn iota. cbn [pa_errcat_guard PMA.AD ADDR_A]. apply (L5C.u8_at_agree RSEGS M M1); [intros i Hi; apply FR1; lia | lia | lia | exact EG].
* apply (PMSTA.atexit_stA_agree RSEGS PMA.AD PMA.AAD PMA.addrs_wf_A M M1 true); [|exact EA].
intros i Hi. cbn [pa_atexit PMA.AD ADDR_A] in Hi. apply FR1; lia.
+ apply (L5SAR.ahpres_of L ar LB FF sp 14336 WE M M1 EK).
* intros i Hi. apply MGM1. apply SDEF. exact Hi.
* apply (L5SAR.dk_grows L ar LB FF sp 14336 M M1 MGM1).
+ exact MRT1.
+ intros x Hx. exact Hx.
+ intros x Hx. exact Hx.
+ exact AM1.
+ exact HH1.
-
cbn iota in EG, EA. cbn [pa_errcat_guard PMA.AD ADDR_A] in EG.
assert (V4 : L5.img_clear MV 6738816 6738818) by (apply L5A.img_clear_mrestrict; exact EG).
assert (V5 : L5.writable RSEGS MV 6738816 2) by (apply writable_img; [vm_compute; reflexivity| lia| lia| lia]).
cfeed P (PMAERP.aerB1_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => v | _ => 0 end)) ltac:(first [assumption | exact Rsp | unfold PMAERP.aligned; lia | lia]).
destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & R1ra & R1sp & R1s0 & R1s1 & R1a0 & R1a1 & R1a2 & R1s2 & G1 & S32 & S24 & S16 & S8).
apply (PMKA2.apiece_img L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xae974 R1 0x6d0c0 M1v
(fun a => sp - 32 <= a < sp - 32 + 32 \/ 0 + 6738816 <= a < 0 + 6738816 + 2) K HH AM MS1 MG1).
{ intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
{ intros a Ha [Wa|Wa].
- split; [|intros X; pose proof (PMA.ly_ro L C LY a X); lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
- split; [|apply (PMKA2.rt_ro_bss L C a LY); lia]. unfold aclientw, aclient_g. right; right; left.
rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|].
intros [X|X].
+ apply (PMA.ly_static L C LY a); [|exact X]. apply PMST.in_foot_errg. cbn [pa_errcat_guard PMA.AD ADDR_A]. lia.
+ pose proof (PMA.ly_ro L C LY a X). lia. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
pose proof AM1 as (Mh1 & MI1).
assert (EK01 : L5SAR.ek L ar LB FF sp 14336 WE M M1).
{ apply (L5SAR.ek_piece L ar LB FF sp 14336 WE M M1 (fun a => (sp - 32 <= a < sp - 32 + 32) \/ (0 + 6738816 <= a < 0 + 6738816 + 2))).
{ intros a Ha N. apply FR1; [exact Ha| exact N]. }
intros a Ha Hc Ho [X|X].
- destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M (vml_of model) sp 14336 a HH SPT Hc) as [(Y1 & Y2)|Y]; [apply Y2; lia| exfalso; lia].
- apply (Ho (6738816, 2)); [right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
pose proof (HAJ.aex_cxa_atexit _ _ _ _ _ EXT) as CXA.
unfold HAJ.cxa_atexit_spec in CXA.
cbn [PMA.EXT HAJ.ec_cxa_pc HAJ.ec_cxa_scr HAJ.ec_atexit HAJ.ec_f0 HAJ.ec_a0 HAJ.ec_f1 HAJ.ec_a1 HAJ.ec_atc HAJ.ec_nl
paa_cxa_atexit_icpt paa_atexit_f0 paa_atexit_a0 paa_at_cxa_atexit PMA.AAD AADDR_A pa_atexit pa_atexit_call pa_exit_guard pa_need_locks PMA.AD ADDR_A] in CXA.
rewrite (L5A.aly_segs L C LYa) in CXA.
assert (ATX1 : HAJ.atexit_cells RSEGS M1 0x68edd0 0x1138d0 0x96c0c 0x1138d0 0xa75d4 None).
{ pose proof (PMSTA.atexit_stA_agree RSEGS PMA.AD PMA.AAD PMA.addrs_wf_A M M1 false) as X.
unfold PMSTA.atexit_stA in X. cbn [pa_atexit paa_atexit_f0 paa_atexit_a0 pa_atexit_call pa_exit_guard PMA.AAD AADDR_A PMA.AD ADDR_A] in X.
apply X; [|exact EA]. intros i Hi. apply FR1; lia. }
assert (NL1 : L5.u8_at RSEGS M1 0x68f013 0).
{ destruct BASE as (_ & _ & NL & _). cbn [pa_need_locks PMA.AD ADDR_A] in NL.
apply (L5C.u8_at_agree RSEGS M M1); [intros i Hi; apply FR1; lia| lia| lia| exact NL]. }
assert (ASO : astack_ok L ar M1 1024 (sp - 32)).
{ apply (L5SAR.astack_ok_of_astk L ar C LYa M M1 sp 14336 32 1024 ASTK MGM1); [lia| lia| lia|].
replace (sp - 32) with (sp + (-2) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
apply (CXA fx1 R1 M1 model1 LB FF LK cr Aw K 852432 1273200 1262664); clear CXA.
{ exact HH1. }
{ exact Mh1. }
{ exact MI1. }
{ rewrite L5K.rl10. exact R1a0. }
{ rewrite L5K.rl11. exact R1a1. }
{ rewrite L5K.rl12. exact R1a2. }
{ exact ATX1. }
{ exact NL1. }
{ rewrite L5K.rl4. rewrite (KS1 4%nat) by inl. exact Rtp. }
{ rewrite L5K.rl1, R1ra. vm_compute. reflexivity. }
{ rewrite L5K.rl2, R1sp. rewrite L5.unsigned_lit by lia. exact ASO. }
{ exact K0. }
intros fx2 R2 M2 model2 Aw2 RP2 A02 ATX2 FRC2 DX2 SCR2 MRT2 INC2 MI2 HH2.
rewrite L5K.rl2, R1sp, L5.unsigned_lit in FRC2, SCR2 by lia.
rewrite L5K.rl1, R1ra.
assert (AM2 : L5CA.amodel_ok Aw2 model2) by (split; [rewrite (L5LZ.model_rt_halted model1 model2 MRT2); exact Mh1| exact MI2]).
assert (EK12 : L5SAR.ek L ar LB FF sp 14336 WE M1 M2).
{ apply (L5SAR.ek_mem L ar LB FF sp 14336 (sp - 32) 1024 (fun x => 0x68edd0 <= x < 0x68edd0 + 544) WE M1 M2); [| lia| lia|].
- intros a Ha Hc Hn. apply FRC2; [exact Ha| exact Hc| exact Hn].
- intros a Hc Ho X. apply (Ho (0x68edd0, 544)); [right; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
assert (EK02 : L5SAR.ek L ar LB FF sp 14336 WE M M2) by (apply (L5SAR.ek_trans L ar LB FF sp 14336 WE M M1 M2 EK01 EK12)).
assert (DK02 : L5SAR.dk L ar LB FF sp 14336 M M2).
{ intros a Ha Hc HM. destruct (L5SAR.rng_dec a 0x68edd0 (0x68edd0 + 544)) as [I|N].
- apply DX2; [exact I| apply MGM1; exact HM].
- destruct (L5SAR.rng_dec a (sp - 32 - 1024) (sp - 32)) as [J|NJ]; [apply SCR2; exact J|].
rewrite FRC2; [apply MGM1; exact HM| exact Ha| apply (L5SAR.aclient_narrow L ar LB FF sp 14336 (sp - 32) 1024 a Hc NJ)| exact N]. }
pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw2 M2 model2 HH2) as (HOFF2 & VIS2 & VIMG2 & VFS2 & VBLK2 & VBSH2 & VFSSH2 & VSTSH2).
set (H2 := ahid Aw2 model2) in *. set (MV2 := mrestrict H2 M2) in *.
pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw2 M2 model2 o 16 sp 14336 HH2 (PMKA.aobj_of_aobjA FF o 16 AO O8) ltac:(lia) ltac:(reflexivity))
as (_ & _ & ODEF2 & OVIS2 & _ & _ & _).
pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as ST2. rewrite (L5A.aly_segs L C LYa) in ST2.
pose proof (L5A.statics_facts L C M2 LYa ST2) as (GOT2 & CSB2 & CUAR2 & _).
assert (ACC2 : PMSPA.accA M2 o 16) by (apply (PMKA.acc_keepA' L ar LB FF sp 14336 WE M M2 EK02 WAPP FRB o 16 AO ACC)).
assert (Y0 : L5.img_clear MV2 1228800 1261568) by (apply L5A.img_clear_mrestrict; exact GOT2).
assert (Y1 : L5.u64_at RSEGS MV2 1289464 2147450880) by (apply (proj2 (L5A.u64_at_vis H2 M2 1289464 2147450880 (VIMG2 1289464 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB2).
assert (Y2 : L5.u32_at RSEGS MV2 1289472 1) by (apply (proj2 (L5A.u32_at_vis H2 M2 1289472 1 (VIMG2 1289472 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR2).
assert (SD2 : L5.defined M2 (sp - 14336) 14336).
{ intros i Hi. destruct (Z_lt_le_dec (sp - 14336 + i) (sp - 32 - 1024)) as [X|X]; [|destruct (Z_lt_le_dec (sp - 14336 + i) (sp - 32)) as [Y|Y]].
- rewrite FRC2; [apply MGM1; apply SDEF; exact Hi| lia| apply L5SAR.stack_client; lia| lia].
- apply SCR2. lia.
- rewrite FRC2; [apply MGM1; apply SDEF; exact Hi| lia| apply L5SAR.stack_client; lia| lia]. }
assert (Y3 : L5.writable RSEGS MV2 (sp - 128) 128).
{ apply (proj2 (L5A.writable_vis H2 M2 (sp - 128) 128 (VIS2 (sp - 128) 128 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
apply (L5C.writable_of_defined RSEGS). apply (L5.defined_sub M2 (sp - 14336) 14336); [exact SD2| lia| lia]. lia. lia. }
assert (YZ : L5KA.zeros_at MV2 ((o / 8) + 2147450880) 2).
{ pose proof (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw2 M2 model2 o 16 HH2 AO O8 ltac:(lia) ltac:(reflexivity) ACC2) as X. exact X. }
assert (YW : L5.writable RSEGS MV2 o 16).
{ apply (proj2 (L5A.writable_vis H2 M2 o 16 OVIS2 ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF2. lia. lia. }
assert (YG : L5.writable RSEGS MV2 6738816 2) by (apply writable_img; [vm_compute; reflexivity| lia| lia| lia]).
assert (SAVE : forall a v0, sp - 32 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v0 -> L5.u64_at RSEGS MV2 a v0).
{ intros a v0 Ha Hb X. rewrite <- VIS1 in X.
apply (proj1 (L5A.u64_at_vis H M1 a v0 (VIS a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))) in X.
apply (proj2 (L5A.u64_at_vis H2 M2 a v0 (VIS2 a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
apply (L5C.u64_at_agree RSEGS M1 M2); [|lia|lia|exact X].
intros i Hi. apply FRC2; [lia| apply L5SAR.stack_client; lia| lia]. }
pose proof (bvu (getr R (reg 8))) as Hs8. pose proof (bvu (getr R (reg 9))) as Hs9. pose proof (bvu (getr R (reg 18))) as Hs18.
assert (Y8 : L5.u64_at RSEGS MV2 (sp - 8) r).
{ apply SAVE; [lia| lia|]. rewrite Rra, L5.unsigned_lit in S8 by lia. exact S8. }
assert (Y16 : L5.u64_at RSEGS MV2 (sp - 16) (bv_unsigned (getr R (reg 8)))) by (apply SAVE; [lia| lia| exact S16]).
assert (Y24 : L5.u64_at RSEGS MV2 (sp - 24) (bv_unsigned (getr R (reg 9)))) by (apply SAVE; [lia| lia| exact S24]).
assert (Y32 : L5.u64_at RSEGS MV2 (sp - 32) (bv_unsigned (getr R (reg 18)))) by (apply SAVE; [lia| lia| exact S32]).
assert (R2sp : getr R2 (reg 2) = Z_to_bv 64 (sp - 32)) by (rewrite (L5SAR.cs_of_preserved R1 R2 2 RP2) by inl; exact R1sp).
assert (R2s0 : getr R2 (reg 8) = Z_to_bv 64 o) by (rewrite (L5SAR.cs_of_preserved R1 R2 8 RP2) by inl; exact R1s0).
assert (R2s1 : getr R2 (reg 9) = Z_to_bv 64 v) by (rewrite (L5SAR.cs_of_preserved R1 R2 9 RP2) by inl; exact R1s1).
assert (R2s2 : getr R2 (reg 18) = Z_to_bv 64 2147450880) by (rewrite (L5SAR.cs_of_preserved R1 R2 18 RP2) by inl; exact R1s2).
cfeed P (PMAERP.aerB2_conc fx2 R2 MV2 (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => v | 43%nat => r
| 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9))
| 46%nat => bv_unsigned (getr R (reg 18)) | _ => 0 end)) ltac:(first [assumption | unfold PMAERP.aligned; lia | lia]).
destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & R3ra & R3sp & R3s0 & R3s1 & R3a0 & R3a1 & R3s2 & D8 & D0 & GB1 & GB0).
pose proof (PMK.ret_to RSEGS fx3 R3 M3v 0xaea00 (ltac:(oW' 0xaea00%Z)) r (ltac:(oF' 0xaea00%Z)) eq_refl (ltac:(oD' 0xaea00%Z)) R3ra ltac:(lia) Hr2) as MS4.
apply (PMKA2.apiece_img L ar C HI LYa HIok LB FF LK cr Aw2 M2 model2 fx2 fx3 R2 0xaea34 R3 r M3v
(fun a => o + 0 <= a < o + 0 + 16 \/ 0 + 6738816 <= a < 0 + 6738816 + 2) K HH2 AM2).
{ eapply msteps_trans; [exact MS3| exact MS4]. }
{ exact MG3. }
{ intros a Ha N. apply FRZ3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
{ intros a Ha [Wa|Wa].
- split; [|intros X; pose proof (PMA.ly_ro L C LY a X); lia]. unfold aclientw, aclient_g. do 3 right. left.
destruct AO as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. split; [lia| intros X; lia].
- split; [|apply (PMKA2.rt_ro_bss L C a LY); lia]. unfold aclientw, aclient_g. right; right; left.
rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|].
intros [X|X].
+ apply (PMA.ly_static L C LY a); [|exact X]. apply PMST.in_foot_errg. cbn [pa_errcat_guard PMA.AD ADDR_A]. lia.
+ pose proof (PMA.ly_ro L C LY a X). lia. }
intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
assert (EK23 : L5SAR.ek L ar LB FF sp 14336 WE M2 M3).
{ apply (L5SAR.ek_piece L ar LB FF sp 14336 WE M2 M3 (fun a => (o + 0 <= a < o + 0 + 16) \/ (0 + 6738816 <= a < 0 + 6738816 + 2))).
{ intros a Ha N. apply FR3; [exact Ha| exact N]. }
intros a Ha Hc Ho [X|X].
- apply (Ho (o, 16)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
- apply (Ho (6738816, 2)); [right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
assert (EK03 : L5SAR.ek L ar LB FF sp 14336 WE M M3) by (apply (L5SAR.ek_trans L ar LB FF sp 14336 WE M M2 M3 EK02 EK23)).
assert (U3 : forall a v0, o <= a -> a + 8 <= o + 16 -> L5.u64_at RSEGS M3v a v0 -> L5.u64_at RSEGS M3 a v0).
{ intros a v0 Ha Hb X. rewrite <- VIS3 in X. exact (proj1 (L5A.u64_at_vis H2 M3 a v0 ltac:(eapply L5A.avis_sub; [exact OVIS2| lia| lia]) ltac:(lia) ltac:(lia)) X). }
assert (UG : forall a v0, 6738816 <= a < 6738818 -> L5.u8_at RSEGS M3v a v0 -> L5.u8_at RSEGS M3 a v0).
{ intros a v0 Ha X. rewrite <- VIS3 in X. exact (proj1 (L5A.u8_at_vis H2 M3 a v0 (VIMG2 a 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) X). }
apply (KONT fx3 R3 M3 model3 LK Aw2).
+ apply L5SAR.preserved_by_index. intros k Hk. unfold L5SAR.cs_all in Hk.
repeat (destruct Hk as [<-|Hk];
[first [ rewrite R3sp, Rsp; reflexivity
| rewrite R3s0, Z_to_bv_bv_unsigned; reflexivity
| rewrite R3s1, Z_to_bv_bv_unsigned; reflexivity
| rewrite R3s2, Z_to_bv_bv_unsigned; reflexivity
| rewrite (KS3 _) by inl; rewrite (L5SAR.cs_of_preserved R1 R2 _ RP2) by inl; apply KS1; inl ]|]).
destruct Hk.
+ split; [apply u32_of_u64; apply (U3 o v ltac:(lia) ltac:(lia) D0)|].
split; [cbn [pa_errcat_obj PMA.AD ADDR_A]; apply (U3 (o + 8) _ ltac:(lia) ltac:(lia) D8)|].
split; [apply (L5.defined_grows M2 M3 _ _ MGM3); exact ODEF2|].
apply (PMKA.acc_keepA' L ar LB FF sp 14336 WE M M3 EK03 WAPP FRB o 16 AO ACC).
+ split.
* cbn iota. cbn [pa_errcat_guard PMA.AD ADDR_A]. exact (UG 6738816 1 ltac:(lia) GB0).
* unfold PMSTA.atexit_stA. cbn [pa_atexit paa_atexit_f0 paa_atexit_a0 pa_atexit_call pa_exit_guard pa_errcat_dtor pa_errcat_obj paa_at_cxa_atexit PMA.AAD AADDR_A PMA.AD ADDR_A].
pose proof (PMSTA.atexit_stA_agree RSEGS PMA.AD PMA.AAD PMA.addrs_wf_A M2 M3 true) as X.
unfold PMSTA.atexit_stA in X.
cbn [pa_atexit paa_atexit_f0 paa_atexit_a0 pa_atexit_call pa_exit_guard pa_errcat_dtor pa_errcat_obj paa_at_cxa_atexit PMA.AAD AADDR_A PMA.AD ADDR_A] in X.
apply X; [|exact ATX2]. intros i Hi. apply FR3; lia.
+ apply (L5SAR.ahpres_of L ar LB FF sp 14336 WE M M3 EK03).
* intros i Hi. apply MGM3. apply SD2. exact Hi.
* apply (L5SAR.dk_trans L ar LB FF sp 14336 M M2 M3 DK02 (L5SAR.dk_grows L ar LB FF sp 14336 M2 M3 MGM3)).
+ apply (L5LZ.model_rt_trans model model2 model3); [|exact MRT3]. apply (L5LZ.model_rt_trans model model1 model2); [exact MRT1| exact MRT2].
+ intros x Hx. exact Hx.
+ exact INC2.
+ exact AM3.
+ exact HH3.
Qed.
End WithHeap.
End PMAERR.
