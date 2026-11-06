(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StreamSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0 L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0 L5StepARB0 PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAb PmSpecsAmc PmModelFactsA PmStep PmStepAB0 PmStepB2 XIcptAs0B0 PmBLocIslandP PmBLocP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan Require Import XIcptAB0 XIcptAs0KitB0.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBLoc () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5DefsAB0.L5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5KnA.L5KA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAb.PMB."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StreamSim."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Aw"; "0C"; "1bool"; "1list"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "2not"; "2or"; "3Z"; "0FF"; "0HI"; "0L"]; ["0LB"; "0LK"; "0M"; "4credit"; "5asc_cells"; "5cell_is"; "5fframe"; "5hl_rt_static"; "5ri_inv"; "5shadow_zero"; "5vml"; "6writable"; "7AS0_ALY_CELLS_D4"; "8zeros_at"; "9locale_ctor_spec"; "9locale_dtor_spec"]; [":wseg_ok"; ";loaded_segments"; "0SCFG_P"; "<In"; "=add"; "=div"; "=le"; "=lt"; "=modulo"; "=pow"; "=sub"; "=to_nat"; "0V"; "0a"; "0ar"; "0cr"]; ["0n"; "0sp"; ">Z_to_bv"; ">bv"; "0v"; "0w"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].
Module PMBLOC.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Lemma wseg_loc1 : ltac2:(TCodec.tc2 tcn__PmBLoc ">'9'2&Q0&Q1&QByR0+V]lgB%3221&Q;+QiN%211%93841(7%=3<21"). Proof. vm_compute. reflexivity. Qed.
Lemma wseg_loc2 : ltac2:(TCodec.tc2 tcn__PmBLoc ">'9'2&Q0&Q1&QByR0+V^PZH%3221&Q;+RH%211%93841(7%=3<21"). Proof. vm_compute. reflexivity. Qed.
Lemma writable_img : ltac2:(TCodec.tc2 tcn__PmBLoc "Q@'QCyR0%211'4y8%511%311p051'<'9'2&Q0&Q1&QBr2%22>1&Q;r1%211%83741(7%<3;21&Q6zr3%3221&Q7%1243&Q4r5r4%3221&Q9+2+R0%3221%>251&Kr7r6%34L21;p051p0?1p0B1p0G1pS2Q51pRLQ61pQ6Q81").
Proof. intros M a n.
intros W Ha Hn Han d k Hd Hk. destruct k as [|k]. reflexivity.
eapply (store_ok_sub RSEGS M (Z_to_bv 64 a) _ (Z.to_nat n) (Datatypes.S k)).
- rewrite L5.unsigned_lit by lia. rewrite Z2Nat.id by lia. lia.
- apply store_ok_wseg. exact W.
- rewrite !L5.unsigned_lit by lia. lia.
- rewrite !L5.unsigned_lit by lia. rewrite Z2Nat.id by lia. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma stack_zeros : ltac2:(TCodec.tc2 tcn__PmBLoc "Q6'QCyR0%211'4y8%511%311p051'<&Ir2&Q:r1+`P0%3221+RP0%73621'9&Q8+@%22:1z%53>21&Mr4&Q4&Q5r3+8%3221+Qoono`0%6221+`0%:3921p0<1p0C1pS4L1pQ6N1").
Proof. intros M sp.
intros SZ S16 i Hi. pose proof (SZ (1536 + i) ltac:(Lia.lia)) as X. unfold byte_at, S, SB in X.
replace (sp / 8 + 2147450368 + i) with ((sp - 16384) / 8 + 2147450880 + (1536 + i)) by Lia.lia. exact X.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis MCC : PMAMC.mcmp_cells_b C.
Let LYa := PMB.ly_as0 L C LY.
Lemma ccell : ltac2:(TCodec.tc2 tcn__PmBLoc "QG'3'6'<%2211%411&F%611&C'QCyR0%211'4y8%511%311p051&J&Hv>r:r9r8r7r6r5r4%9887654321&Q3%K2IJ(5r3%24MM61r2%44NO21&Dv1%211%:3941&E&Q1&Q;%11@%453DB1<p061p0B1pS:Q;1pS<Q<1pRLQ=1pRJQ01pQ6Q21p2Q>1pS0Q<1pQ4Q>1pLQ?1pQ2QB1").
Proof. intros LB FF LK cr Aw M V a w v.
intros HH Hin. pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & CS). rewrite (L5A.aly_segs L C LYa) in CS.
rewrite Forall_forall in CS. exact (CS (a, w, v) Hin).
Qed.
Lemma d4cell : ltac2:(TCodec.tc2 tcn__PmBLoc "QE'3'6'<%2211%411&F%611&C'QCyR0%211'4y8%511%311p051&J&Hv>r:r9r8r7r6r5r4%9887654321&Q3%K2IJ(5r3%24MM61r2%44NO21&L%83721&E&Q1&Q;%11>%453B@1:p061p0@1pS:Q91pS<Q:1pRLQ;1pRJN1pQ6Q01p2Q<1pS0Q:1pQ4Q<1pLQ=1pQ2Q@1").
Proof. intros LB FF LK cr Aw M V a w v. intros HH Hin. exact (ccell LB FF LK cr Aw M V a w v HH (L5A.aly_cells L C LYa _ Hin)). Qed.
Lemma loc_foot_static : ltac2:(TCodec.tc2 tcn__PmBLoc "I'<';'8&Q6+V]lgBr1%3221&Q7+V]na@%2241%8241+V^PZH%9217+V^P]@%7291%=231%?261&:&Gv?r2%3221%511p071pRLH1").
Proof. intros a.
intros Ha. apply (PMB.ly_static L C LY). unfold PMST.dep, pm_foot, pm_initc.
cbn [pa_errcat_guard pa_syscat_guard pa_loc_foot pa_atexit pa_canary pa_need_locks pa_locale_lock PMB.AD ADDR_A app].
left. destruct Ha as [Ha|Ha]; [exists (0x66f2f2, 0x66fa30)| exists (0x670158, 0x6701b0)]; split; cbn; [tauto| lia| tauto| lia].
Qed.
Theorem locale_ctor_ok : ltac2:(TCodec.tc2 tcn__PmBLoc "6&NvQ2v?vQ>v>%544321").
Proof.
unfold PMB.locale_ctor_spec, PMSPA.locale_ctor_spec.
intros fx R M model K LB FF LK Aw cr o sp r b HH AM K0 ENT FRM FRS A10 AO O8 ODEF BASE LOC KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
pose proof AM as (Mh & MI). pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl10 in A10.
change (PMSPA.pm_scr 2) with 16384 in *. change (16384 / 8) with 2048 in STKSH.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
assert (SPR : 0 <= sp < 2 ^ 64 /\ 140735332491264 <= sp <= 140737488355328) by (clear - SLO SHI SPT; lia).
pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
pose proof (PMKB.aobj_of_aobjA FF o 8 AO O8) as AOB.
pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model o 8 sp 16384 HH AOB ltac:(lia) ltac:(reflexivity))
as (OR & OBIG & ODEF' & OVIS & OVSH & OCL & OCLSH).
pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
assert (VU8 : forall x v0, 0x10000 <= x < 0x693000 -> L5.u8_at RSEGS M x v0 -> L5.u8_at RSEGS MV x v0).
{ intros x v0 Hx X. apply (proj2 (L5A.u8_at_vis H M x v0 (VIMG x 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
assert (VU32 : forall x v0, 0x10000 <= x -> x + 4 <= 0x693000 -> L5.u32_at RSEGS M x v0 -> L5.u32_at RSEGS MV x v0).
{ intros x v0 Hx Hx' X. apply (proj2 (L5A.u32_at_vis H M x v0 (VIMG x 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
assert (VU64 : forall x v0, 0x10000 <= x -> x + 8 <= 0x693000 -> L5.u64_at RSEGS M x v0 -> L5.u64_at RSEGS MV x v0).
{ intros x v0 Hx Hx' X. apply (proj2 (L5A.u64_at_vis H M x v0 (VIMG x 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
assert (OWv : L5.writable RSEGS MV o 8).
{ apply (proj2 (L5A.writable_vis H M o 8 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47).
{ intros f Hf. destruct (WF f Hf) as (X1 & X2 & _). unfold app_mem, FS_BYTES in *. lia. }
unfold PMSPA.cfg. cbn [pa_locale_ctor PMB.AD ADDR_A].
destruct b.
-
destruct LOC as (G & P0). cbn [pa_glocale pa_classic_imp PMB.AD ADDR_A] in G, P0.
assert (Gv : L5.u8_at RSEGS MV 6747376 1) by (apply VU8; [lia| exact G]).
assert (Pv : L5.u64_at RSEGS MV 6747368 6748416) by (apply VU64; [lia| lia| exact P0]).
assert (W32 : L5.writable RSEGS MV (sp - 32) 32).
{ apply (proj2 (L5A.writable_vis H M (sp - 32) 32 (VIS (sp - 32) 32 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
apply (L5SAR.astk_writable ar M sp 16384); [exact ASTK| lia| lia| lia]. }
assert (FRO : sp - 32 + 32 <= o \/ o + 8 <= sp - 32) by lia.
cfeed P (PMBLOCP.aliB_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx R MV (fun j => match j with 2%nat => sp | 33%nat => o | _ => 0 end)) ltac:(first [assumption | unfold PMBLOCP.aligned; lia | lia]).
destruct P as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & B10 & B11 & CO).
assert (R1ra : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by inl; exact Rra).
pose proof (PMK.ret_to RSEGS fx1 R1 M1v 0xfbda8 (ltac:(oW' 0xfbda8%Z)) r (ltac:(oF' 0xfbda8%Z)) eq_refl (ltac:(oD' 0xfbda8%Z)) R1ra ltac:(lia) Hr2) as MS2.
set (W1 := fun a => sp - 32 <= a < sp - 32 + 32 \/ o + 0 <= a < o + 0 + 8).
apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xfbd4c R1 r M1v W1 K HH AM).
{ eapply msteps_trans; [exact MS1| exact MS2]. }
{ exact MG1. }
{ intros a Ha N. apply FZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
{ intros a Ha [Wa|Wa].
- split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
- split; [apply (L5SAR.obj_client L ar LB FF 0 0 o 8 a AOB); lia| lia]. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
assert (EK : L5SAR.ek L ar LB FF sp 16384 [(o, 8)] M M1).
{ apply (L5SAR.ek_piece L ar LB FF sp 16384 [(o, 8)] M M1 W1 FR1). intros a Ha Hc Ho [X|X].
- destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M _ sp 16384 a HH SPT Hc) as [Z1|Z1]; lia.
- apply (Ho (o, 8)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. lia. }
apply (KONT fx1 R1 M1 model1 LK Aw).
+ apply L5SAR.preserved_by_index. intros k Hk. apply KS1. unfold L5SAR.cs_all in Hk. repeat (destruct Hk as [<-|Hk]; [inl|]). destruct Hk.
+ cbn [pa_classic_imp PMB.AD ADDR_A]. rewrite <- VIS1 in CO. exact (proj1 (L5A.u64_at_vis H M1 o 6748416 OVIS ltac:(lia) ltac:(lia)) CO).
+ cbn [PMST.loc_ok pa_glocale pa_classic_imp PMB.AD ADDR_A]. split.
* apply (L5C.u8_at_agree RSEGS M M1); [| lia| lia| exact G]. intros i Hi. apply FR1; [lia|]. intros [X|X]; lia.
* apply (L5C.u64_at_agree RSEGS M M1); [| lia| lia| exact P0]. intros i Hi. apply FR1; [lia|]. intros [X|X]; lia.
+ apply (L5SAR.ahpres_of L ar LB FF sp 16384 [(o, 8)] M M1 EK).
* intros i Hi. apply MGM1. apply SDEF. exact Hi.
* apply (L5SAR.dk_grows L ar LB FF sp 16384 M M1 MGM1).
+ exact MRT1.
+ intros x Hx. exact Hx.
+ intros x Hx. exact Hx.
+ exact AM1.
+ exact HH1.
-
cbn [PMST.loc_ok] in LOC. unfold PMST.img_clear_l in LOC. cbn [pa_loc_foot PMB.AD ADDR_A] in LOC.
assert (C1 : L5.img_clear M 6746866 6748720) by (apply (LOC (0x66f2f2, 0x66fa30)); cbn; auto).
assert (C2 : L5.img_clear M 6750552 6750640) by (apply (LOC (0x670158, 0x6701b0)); cbn; auto).
destruct BASE as (RO0 & (can & Hcan & CAN) & NL & LL). cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock PMB.AD ADDR_A] in RO0, CAN, NL, LL.
assert (V0 : L5.img_clear MV 65536 1269760) by (apply L5A.img_clear_mrestrict; exact RO0).
assert (V1 : L5.u64_at RSEGS MV 1296952 2147450880) by (apply VU64; [lia| lia| exact CSB]).
assert (V2 : L5.u32_at RSEGS MV 1296960 1) by (apply VU32; [lia| lia| exact CUAR]).
assert (VC1 : L5.img_clear MV 6746866 6748720) by (apply L5A.img_clear_mrestrict; exact C1).
assert (VC2 : L5.img_clear MV 6750552 6750640) by (apply L5A.img_clear_mrestrict; exact C2).
assert (WC1 : L5.writable RSEGS MV 6746866 1854).
{ apply (proj2 (L5A.writable_vis H M 6746866 1854 (VIMG 6746866 1854 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
exact (writable_img M 6746866 1854 wseg_loc1 ltac:(lia) ltac:(lia) ltac:(lia)). }
assert (WC2 : L5.writable RSEGS MV 6750552 88).
{ apply (proj2 (L5A.writable_vis H M 6750552 88 (VIMG 6750552 88 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
exact (writable_img M 6750552 88 wseg_loc2 ltac:(lia) ltac:(lia) ltac:(lia)). }
assert (VNL : L5.u8_at RSEGS MV 6884691 0) by (apply VU8; [lia| exact NL]).
assert (VLL : L5.u32_at RSEGS MV 6884912 0) by (apply VU32; [lia| lia| exact LL]).
assert (VCAN : L5.u64_at RSEGS MV 6884096 can) by (apply VU64; [lia| lia| exact CAN]).
assert (W4096 : L5.writable RSEGS MV (sp - 4096) 4096).
{ apply (proj2 (L5A.writable_vis H M (sp - 4096) 4096 (VIS (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
apply (L5SAR.astk_writable ar M sp 16384); [exact ASTK| lia| lia| lia]. }
assert (FRO : sp - 4096 + 4096 <= o \/ o + 8 <= sp - 4096) by lia.
assert (XC1 : L5.u64_at RSEGS MV 1262496 1296952) by (apply VU64; [lia| lia| exact (d4cell _ _ _ _ _ _ _ 1262496 8 1296952 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 4 right; left; reflexivity))]).
assert (XC2 : L5.u64_at RSEGS MV 1262504 1300264) by (apply VU64; [lia| lia| exact (d4cell _ _ _ _ _ _ _ 1262504 8 1300264 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 5 right; left; reflexivity))]).
assert (XC3 : L5.u64_at RSEGS MV 1300264 0) by (apply VU64; [lia| lia| exact (d4cell _ _ _ _ _ _ _ 1300264 8 0 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 6 right; left; reflexivity))]).
assert (XC4 : L5.u64_at RSEGS MV 1262512 1300272) by (apply VU64; [lia| lia| exact (d4cell _ _ _ _ _ _ _ 1262512 8 1300272 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 7 right; left; reflexivity))]).
assert (XC5 : L5.u64_at RSEGS MV 1300272 0) by (apply VU64; [lia| lia| exact (d4cell _ _ _ _ _ _ _ 1300272 8 0 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 8 right; left; reflexivity))]).
assert (XC6 : L5.u64_at RSEGS MV 1262520 1300256) by (apply VU64; [lia| lia| exact (d4cell _ _ _ _ _ _ _ 1262520 8 1300256 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 9 right; left; reflexivity))]).
assert (XC7 : L5.u64_at RSEGS MV 1300256 140737488355327) by (apply VU64; [lia| lia| exact (d4cell _ _ _ _ _ _ _ 1300256 8 140737488355327 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 10 right; left; reflexivity))]).
assert (XC8 : L5.u64_at RSEGS MV 1265416 1300249) by (apply VU64; [lia| lia| exact (d4cell _ _ _ _ _ _ _ 1265416 8 1300249 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 11 right; left; reflexivity))]).
assert (XC9 : L5.u8_at RSEGS MV 1300249 1) by (apply VU8; [lia| exact (d4cell _ _ _ _ _ _ _ 1300249 1 1 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 12 right; left; reflexivity))]).
assert (XC10 : L5.u64_at RSEGS MV 1270704 1207272) by (apply VU64; [lia| lia| exact (d4cell _ _ _ _ _ _ _ 1270704 8 1207272 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 2 right; left; reflexivity))]).
assert (XC11 : L5.u64_at RSEGS MV 1270696 1206244) by (apply VU64; [lia| lia| exact (d4cell _ _ _ _ _ _ _ 1270696 8 1206244 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 13 right; left; reflexivity))]).
destruct MCC as (MC1 & MC2 & MC3 & MC4).
assert (MX1 : L5.u8_at RSEGS MV 1300248 1) by (apply VU8; [lia| exact (ccell _ _ _ _ _ _ _ 1300248 1 1 HH MC1)]).
assert (MX2 : L5.u64_at RSEGS MV 1270232 1206196) by (apply VU64; [lia| lia| exact (ccell _ _ _ _ _ _ _ 1270232 8 1206196 HH MC2)]).
assert (MX3 : L5.u8_at RSEGS MV 1893990 1) by (apply VU8; [lia| exact (ccell _ _ _ _ _ _ _ 1893990 1 1 HH MC3)]).
assert (MX4 : L5.u8_at RSEGS MV 1893991 1) by (apply VU8; [lia| exact (ccell _ _ _ _ _ _ _ 1893991 1 1 HH MC4)]).
assert (IMGZ : forall lo n, 65536 <= lo -> lo + n <= 0x693000 -> 0 < n -> (lo + n <= 0x23160 \/ 0x23940 <= lo) -> (lo + n <= 0x12ebc0 \/ 0x12ec60 <= lo) ->
(lo + n <= 0x138ea0 \/ 0x139380 <= lo) -> forall a k, SB + lo / 8 <= a -> a + k <= SB + (lo + n - 1) / 8 + 1 -> L5KA.zeros_at MV a k).
{ intros lo n Hlo Hn Hn0 P1 P2 P3 a k Ha Hk.
destruct (aic_img_shadow _ _ _ _ _ ICok _ _ _ _ _ _ _ HH lo n) as (ZB & SA).
- rewrite (L5A.aly_img_lo L C LYa). lia. - rewrite (L5A.aly_img_hi L C LYa). lia. - lia.
- rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; clear - P1 P2 P3; lia|]). apply Forall_nil.
- intros i Hi. assert (AV : L5A.avis H (a + i) 1).
{ apply (L5A.avis_of_shadow_allowed Aw model lo n). exact SA. intros j Hj. unfold in_shadow_of, S, SB in *. lia. }
pose proof (ZB (a + i) ltac:(unfold in_shadow_of, S, SB in *; lia)) as Z1. unfold byte_at in Z1.
unfold MV. rewrite (AsanAcct.mrestrict_visible H M); [exact Z1|]. pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (SHZ1 : L5KA.zeros_at MV 2148294230 248) by (apply (IMGZ (6746866 - 64) (1854 + 128)); try unfold SB; lia).
assert (SHZ2 : L5KA.zeros_at MV 2148294691 27) by (apply (IMGZ (6750552 - 64) (88 + 128)); try unfold SB; lia).
assert (SHZ3 : L5KA.zeros_at MV 2147473032 77) by (apply (IMGZ 0x2b444 616); try unfold SB; lia).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
assert (STZ : L5KA.zeros_at MV (sp / 8 + 2147450368) 512).
{ intros i Hi. unfold MV. rewrite (AsanAcct.mrestrict_visible H M). apply (stack_zeros M sp STKSH A16). exact Hi.
assert (AV : L5A.avis H (sp / 8 + 2147450368 + i) 1).
{ apply (VSTSH (sp / 8 + 2147450368 + i) 1). intros j Hj. unfold in_shadow_of, S, SB.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
assert (CR : 0 <= can < 2 ^ 64) by exact Hcan.
cfeed P (PMBLIP.aliA_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx R MV (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => can | _ => 0 end)) ltac:(first [assumption | unfold PMBLIP.aligned; lia | lia]).
destruct P as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & B10 & B11 & CO & CG & CP).
assert (R1ra : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by inl; exact Rra).
pose proof (PMK.ret_to RSEGS fx1 R1 M1v 0xfbda8 (ltac:(oW' 0xfbda8%Z)) r (ltac:(oF' 0xfbda8%Z)) eq_refl (ltac:(oD' 0xfbda8%Z)) R1ra ltac:(lia) Hr2) as MS2.
set (W1 := fun a => (sp - 4096 <= a < sp - 4096 + 4096 \/ o + 0 <= a < o + 0 + 8) \/ (0 + 6746866 <= a < 0 + 6746866 + 1854 \/ 0 + 6750552 <= a < 0 + 6750552 + 88)).
apply (PMKB2.apiece_img L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xfbd4c R1 r M1v W1 K HH AM).
{ eapply msteps_trans; [exact MS1| exact MS2]. }
{ exact MG1. }
{ intros a Ha N. apply FZ1; [exact Ha| | | |]; intros X; apply N; [left; left|left; right|right; left|right; right]; exact X. }
{ intros a Ha [[Wa|Wa]|[Wa|Wa]].
- split; [|intros X; pose proof (PMB.ly_ro L C LY a X); lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
- split; [apply (L5SAR.obj_client L ar LB FF 0 0 o 8 a AOB); lia| apply (PMKB2.rt_ro_bss L C a LY); lia].
- split; [|apply (PMKB2.rt_ro_bss L C a LY); lia]. unfold aclientw, aclient_g. right; right; left.
split; [rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa); lia|]. intros [X|X]; [exact (loc_foot_static a ltac:(lia) X)| exact (PMKB2.rt_ro_bss L C a LY ltac:(lia) X)].
- split; [|apply (PMKB2.rt_ro_bss L C a LY); lia]. unfold aclientw, aclient_g. right; right; left.
split; [rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa); lia|]. intros [X|X]; [exact (loc_foot_static a ltac:(lia) X)| exact (PMKB2.rt_ro_bss L C a LY ltac:(lia) X)]. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
set (WL := (o, 8) :: PMSPA.loc_W PMB.AD).
assert (EK : L5SAR.ek L ar LB FF sp 16384 WL M M1).
{ apply (L5SAR.ek_piece L ar LB FF sp 16384 WL M M1 W1 FR1). intros a Ha Hc Ho [[X|X]|[X|X]].
- destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M _ sp 16384 a HH SPT Hc) as [Z1|Z1]; lia.
- apply (Ho (o, 8)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. lia.
- apply (Ho (0x66f2f2, 0x66fa30 - 0x66f2f2)). right; left; reflexivity. unfold L5.in_rng; cbn [fst snd]. lia.
- apply (Ho (0x670158, 0x6701b0 - 0x670158)). right; right; left; reflexivity. unfold L5.in_rng; cbn [fst snd]. lia. }
apply (KONT fx1 R1 M1 model1 LK Aw).
+ apply L5SAR.preserved_by_index. intros k Hk. apply KS1. unfold L5SAR.cs_all in Hk. repeat (destruct Hk as [<-|Hk]; [inl|]). destruct Hk.
+ cbn [pa_classic_imp PMB.AD ADDR_A]. rewrite <- VIS1 in CO. exact (proj1 (L5A.u64_at_vis H M1 o 6748416 OVIS ltac:(lia) ltac:(lia)) CO).
+ cbn [PMST.loc_ok pa_glocale pa_classic_imp PMB.AD ADDR_A]. rewrite <- VIS1 in CG, CP. split.
* exact (proj1 (L5A.u8_at_vis H M1 6747376 1 (VIMG 6747376 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) CG).
* exact (proj1 (L5A.u64_at_vis H M1 6747368 6748416 (VIMG 6747368 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) CP).
+ apply (L5SAR.ahpres_of L ar LB FF sp 16384 WL M M1 EK).
* intros i Hi. apply MGM1. apply SDEF. exact Hi.
* apply (L5SAR.dk_grows L ar LB FF sp 16384 M M1 MGM1).
+ exact MRT1.
+ intros x Hx. exact Hx.
+ intros x Hx. exact Hx.
+ exact AM1.
+ exact HH1.
Qed.
Theorem locale_dtor_ok : ltac2:(TCodec.tc2 tcn__PmBLoc "6&OvQ2v?vQ>v>%544321").
Proof.
unfold PMB.locale_dtor_spec, PMSPA.locale_dtor_spec.
intros fx R M model K LB FF LK Aw cr o sp r HH AM K0 ENT FRM FRS A10 AO CELL KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). pose proof RAok as (Hr1 & Hr2).
pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl10 in A10. cbn [pa_classic_imp PMB.AD ADDR_A] in CELL.
pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
destruct AO as (f & Hf & O1 & O2).
pose proof (WF f Hf) as (Y1 & Y2 & _ & Y4 & _).
rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG. unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in *.
assert (HB : 0 < ff_bytes (ff_class f) <= 1024).
{ clear - Y4. destruct Y4 as [E|[E|[E|[E|[E|[]]]]]]; rewrite <- E;
[change (ff_bytes 0) with 64 | change (ff_bytes 1) with 128 | change (ff_bytes 2) with 256 | change (ff_bytes 3) with 512 | change (ff_bytes 4) with 1024]; lia. }
assert (OR : 6893568 <= o <= 140737488355320) by (clear - O1 O2 Y1 Y2 FSIMG FSAPP HB; lia).
assert (OVIS : L5A.avis H o 8) by (apply VFS; clear - O1 O2 Y1 Y2 HB; lia).
assert (CV : L5.u64_at RSEGS MV o 6748416) by (apply (proj2 (L5A.u64_at_vis H M o 6748416 OVIS ltac:(lia) ltac:(lia))); exact CELL).
change (PMSPA.pm_scr 0) with 12288 in *.
assert (SPR : 0 <= sp < 2 ^ 64) by (clear - SLO SHI SPT; lia).
cfeed P (PMBLOCP.aliD_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx R MV (fun j => match j with 2%nat => sp | 33%nat => o | _ => 0 end)) ltac:(first [assumption | unfold PMBLOCP.aligned; lia | lia]).
destruct P as (fx1 & R1 & M1v & MG1 & FA1 & FZ1 & MS1 & KS1 & _).
assert (E1 : M1v = MV) by (apply L5SAR.mem_eq_of_agree; exact FZ1). subst M1v.
assert (R1ra : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by inl; exact Rra).
pose proof (PMK.ret_to RSEGS fx1 R1 MV 0xfbe44 (ltac:(oW' 0xfbe44%Z)) r (ltac:(oF' 0xfbe44%Z)) eq_refl (ltac:(oD' 0xfbe44%Z)) R1ra ltac:(lia) Hr2) as MS2.
unfold PMSPA.cfg. cbn [pa_locale_dtor PMB.AD ADDR_A].
apply (L5SAR.apiece_ro L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xfbe24 R1 r MV K HH AM (msteps_trans _ _ _ _ MS1 MS2) (fun x Hx => Hx) (fun a Ha => eq_refl)).
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
assert (E2 : M1 = M) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1.
apply (KONT fx1 R1 model1).
- apply L5SAR.preserved_by_index. intros k Hk. apply KS1. unfold L5SAR.cs_all in Hk. repeat (destruct Hk as [<-|Hk]; [inl|]). destruct Hk.
- exact MRT1.
- exact AM1.
- exact HH1.
Qed.
End Stage.
End PMBLOC.
