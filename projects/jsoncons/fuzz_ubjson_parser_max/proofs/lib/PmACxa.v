(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StreamSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreA L5StepAR PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAa PmModelFactsA PmStep PmStepA PmStepA2 PmACxaP.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmACxa () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceAJx.HAJ."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5DefsA.L5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAa.PMA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StreamSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreA.L5CA."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1Some"; "1bool"; "1false"; "1list"; "1option"; "1pair"; "1prod"; "1true"; "2I"; "2and"; "2eq"; "2not"; "3Z"; "0FF"]; ["0HI"; "0K"; "0L"; "0LB"; "0LK"; "4fetch_word"; "4is_ecall"; "4store_ok"; "5Model"; "6decode_any"; "7Jalr"; "7instr"; "8bvmap"; "0M"; "0M1"; "0M1v"]; ["0Mx"; "0R"; "0R1"; "9mrestrict"; "9segs_below_b"; ":msteps"; ";credit"; "<aclient"; "<aclientw"; "<ahid"; "<ar_sptop"; "<fframe"; "<hl_rt_ro"; "<hl_tp"; "<model_rt"; "<ri_inv"]; ["<vml"; "<vml_of"; "=cxa_atexit_spec"; "=ec_a0"; "=ec_a1"; "=ec_atc"; "=ec_atexit"; "=ec_cxa_pc"; "=ec_cxa_scr"; "=ec_f0"; "=ec_f1"; "=ec_nl"; ">ret_ok"; "@u32_at"; "@u64_at"; "@writable"]; ["?SCFG"; "Acfg"; "BEXT"; "CFPState"; "Cgetr"; "Cmkst"; "Cseg_rom"; "DTSet"; "Esrealizes"; "Fmem_grows"; "Gwseg_ok"; "Hamodel_ok"; "Iloaded_segments"; "0SCFG_P"; "Jadd"; "Jle"]; ["Jlt"; "Jof_nat"; "Jpow"; "Jto_nat"; "0V"; "0W"; "0a"; "0ar"; "0cr"; "0fx"; "0fx1"; "0model"; "0model1"; "0n"; "0pc"; "0pc1"]; ["0scr"; "0sp"; "KBV"; "KZ_to_bv"; "Kbv"; "Kbv_unsigned"; "0v"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia.
Module PMACXA.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).
Lemma writable_img : ltac2:(TCodec.tc2 tcn__PmACxa "Q@'S4yR0%211'6y8%511%311p051'>'<'3&R:&R<&S3r2%22>1&RCr1%211%83741(9%<3;21&R?zr3%3221&R@%1243&R>r5r4%3221&RB+2+R0%3221%>251&QOr7r6%34L21;p051p0?1p0B1p0G1pULQ51pU>Q61pQLQ81").
Proof. intros M a n.
intros W Ha Hn Han d k Hd Hk. destruct k as [|k]. reflexivity.
eapply (store_ok_sub RSEGS M (Z_to_bv 64 a) _ (Z.to_nat n) (Datatypes.S k)).
- rewrite L5.unsigned_lit by lia. rewrite Z2Nat.id by lia. lia.
- apply store_ok_wseg. exact W.
- rewrite !L5.unsigned_lit by lia. lia.
- rewrite !L5.unsigned_lit by lia. rewrite Z2Nat.id by lia. lia.
Qed.
Lemma segs_belowA : ltac2:(TCodec.tc2 tcn__PmACxa "8'<'3&Q4&R<+VbTP0%3221(9%73621").
Proof. vm_compute. reflexivity. Qed.
Lemma store_ok_defined : ltac2:(TCodec.tc2 tcn__PmACxa "Q='S4yR0%211'6y8%511%311p051'>';&R?+VbTP0r1%3221&R@&RB+2+R0%3221%5271%;271'<'3&G&R<r3&S3r2%22K1u1%746521(9%;3:21&=r4%92Q2:%211(1%11Q1%B3Q131%711p091p0F1pU>Q31pR2Q51").
Proof. intros Mx a.
intros Ha Hs. cbn [store_ok] in Hs. unfold wview in Hs.
destruct (Mx (Z_to_bv 64 a)) as [b|]; [discriminate|]. exfalso.
rewrite (find_segment1_none_above RSEGS 0x691000 (bv_unsigned (Z_to_bv 64 a)) segs_belowA) in Hs by (rewrite L5.unsigned_lit by lia; lia). discriminate.
Qed.
Lemma u64_norm : ltac2:(TCodec.tc2 tcn__PmACxa "I'S4yR0%211'6y8%511%311p051'>&QN&R<r3r2&S5&S3r1%22?1%42@1%948761r4%;4:198p031pV>>1pU>?1pQLA1").
Proof. intros M a v. unfold L5.u64_at. rewrite Z_to_bv_bv_unsigned. exact (fun X => X). Qed.
Lemma ret_rok : ltac2:(TCodec.tc2 tcn__PmACxa "RG'R3&Ly5'S4yR0%211%5241'6y8%611%311p061'>yQ0%;11'<%912&E&R<&S3r2%22A1%5241(2r1%22;1%;3:41'3&F%119(4%@3421'8'K%221F%L11&Ir3%211(7(J(S2z(:%33Q:21+1%53Q<13y<%73165%93531+4%<4BQ721%M2B1%Q63B?1&QL&R4r7&RAu1%211%Q92QJ1%6251%811'Q5&R5r9r8r6%QA2R01&R6%11QD%75653?1&S5%B27=%22R61%QH2R71%<5;:1D6%>3QK61p0@1p0J1p0QA1p0QG1pU<R41pUNR71pQLR91pR4R?1pUDRF1").
Proof. intros fx R M pc W.
intros HF HEC HD RO. rewrite Z_to_bv_bv_unsigned. eapply mst_step; [reflexivity | | apply mst_refl].
assert (D: decode_any W = Some (Jalr 0 (reg 1) (0%bv : bv 12), 4%Z)). { rewrite HD. repeat f_equal; apply bv_eq; reflexivity. }
rewrite (step_jalr_x0 RSEGS R _ M (seg_rom RSEGS) _ (reg 1) (0%bv : bv 12) (getr R (reg 1)) HF HEC D eq_refl).
change (bv_signed (0%bv : bv 12)) with 0. unfold Hoare.ret_ok in RO. rewrite RO. reflexivity.
Qed.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis FCTR : HAJ.rt_frame_ctr L ar HI.
Let LYa := PMA.ly_as0 L C LY.
Lemma apiece_ctr : ltac2:(TCodec.tc2 tcn__PmACxa "V6'5'8'>%2211%411&Q;%611&Q6'S4yR0%211'6y8%511%311p051'H'R3&Ly5%221:!p0D1&R7&Q?v@r@r?r>r=r<r;&QAr:%211%;8:9876541&R;%1286'Q5&R<&R5r9&S3r8%22Q31&Q3&Q9%12CA%321C&R6%11;%;5D:731r7r6%<2Q=1r5%@5G4216%C3B61&R9%=2Q0N%?21Q0%3218';&R?zr1%3221&R@&RB+2+R0%3221%5271%;271&=r2%Q111%311'<r3%Q62R71%Q@11rCrA%Q6221rB%Q93216%93R961p0;1p0@1pU>RH1%QB1@&R>&Q=vB%211+@%5221%Q321C+D%8251%Q22F1%Q8241%M11&Q8vRGrIrHr4%57?432Q=Q=1&Q<%12A3%Q611%QC241p0;1p0H1p0Q;1pU>SC1&QM%14R@R>FQGrGrFrE%RK1QJ%S48S3BA432QA1%RI24QB&Q>%125Q@'3p0SG1%RD2GF%RE2H:%QF3321%RG2K=%RI21RA%QI3SH1S=%R>2NRD%QG1QN%R011%S<1QKrM%11QM%R03T031p051p0R71pU>T?1rK%S5371RB(4%R73E21%SG1R;%M1R<%R:3T:21p041pU>T@1'R8&R0vR=%211&R1%15QFQ7Q6SOSG%64SJ31R<p081p0B1p0L1p0N1p0Q21p0Q81p0Q;1p0Q=1pUJTJ1pQNTL1%=5RITAT@RJRG%B4T6?1T4p031p0QH1p0QK1p0RG1p0SE1p0SJ1p0T?1p0TB1pQ4TO1pU<U11pR0U91pV0UG1pR6U61pUNUI1pR4U81pUFU<1pUDU=1pUHU?1pQLUA1p2UM1pUBUK1pQ:UM1pQ0UN1pQ8V11").
Proof. intros LB FF LK cr A M model fx fx1 R pc R1 pc1 M1v W K.
intros HH [Hh MI] MS MG FZ WC CT KONT.
pose proof (HAJ.aior_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (AWF & LZ).
pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr A M model HH) as (HOFF & _ & VIMG & _).
set (H := ahid A model) in *.
unfold L5A.cfg. eapply (L5LZ.cps_of_msteps_lazy RSEGS H A fx fx1 R _ M R1 _ M1v model K HOFF L5A.wx_nowrap (L5LZ.lazy_cover_ahid A model) AWF MI Hh MS).
intros model1 MI1 SBM1 HC1.
set (M1 := munrestrict H M M1v).
assert (M1vis : mrestrict H M1 = M1v). { apply L5LZ.mrestrict_of_munrestrict. exact HC1. }
assert (FRM1 : forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha Hn. unfold M1, munrestrict. destruct (H (Z_to_bv 64 a)) eqn:E. reflexivity. rewrite (FZ a Ha Hn). unfold mrestrict. rewrite E. reflexivity. }
assert (MGM1 : mem_grows M M1).
{ intros x Hx. unfold M1, munrestrict. destruct (H x) eqn:E. exact Hx. apply MG. unfold mrestrict. rewrite E. exact Hx. }
assert (VML : vml_of model1 = vml_of model). { unfold vml_of. rewrite (L5LZ.sbm_vmmaps _ _ SBM1), (L5LZ.sbm_lazy _ _ SBM1). reflexivity. }
pose proof (PMA.ly_tp L C LY) as TP. cbn [pa_tp PMA.AD ADDR_A] in TP.
apply (KONT M1 model1).
- rewrite VML. apply (FCTR LB FF LK cr A M M1 _ HH).
+ intros a Ha Hp Hc. apply FRM1. exact Ha. intros CW. destruct (WC a Ha CW Hc) as [C1 C2]. destruct Hp as [Hp|[Hp|Hp]].
* exact (Hp (aclientw_client _ _ _ _ _ _ _ C1)). * exact (C2 Hp).
* exact (L5SAR.aclientw_not_bshadow L ar C HI LYa HIok LB FF LK cr A M _ 0 0 a HH C1 Hp).
+ rewrite (L5A.aly_segs L C LYa). rewrite TP in *. change (L5.u32_at RSEGS M1 (6745472 + 16) 0).
apply (proj1 (L5A.u32_at_vis H M1 (6745472 + 16) 0 (VIMG (6745472 + 16) 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
rewrite M1vis. exact CT.
+ exact MGM1.
- split. exact (eq_trans (L5LZ.sbm_halted _ _ SBM1) Hh). exact MI1.
- apply L5LZ.sbm_model_rt. exact SBM1.
- apply L5LZ.sbm_ahid. exact SBM1.
- exact M1vis.
- exact MGM1.
- exact FRM1.
- intros a Ha. unfold M1. apply L5LZ.munrestrict_visible. exact Ha.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma ctr_not_client : ltac2:(TCodec.tc2 tcn__PmACxa "QM'5'8'>%2211%411&Q;%611&Q6'S4yR0%211'6y8%511%311p051&Q@&Q?v@r:r9r8r7r6r5r4%9887654321&R?+SoonPPPPP0&Q:vRG%211%5241';+V]k\@r3%9221&R@+V]k\D%2241%7241&=&Q7vBr=r<%473@21GFE%611p081p0A1p0H1pV@QA1pV2QB1pV4QC1pU:Q61pQLQ81p2QD1pUBQB1pQ:QD1pQ0QE1pQ8QH1").
Proof. intros LB FF LK cr A M V sp scr x.
intros HH SPT Hx Hc. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
pose proof (L5A.aly_img_lo L C LYa) as IL. pose proof (L5A.aly_img_hi L C LYa) as IH.
pose proof (PMA.ly_tp L C LY) as TP. cbn [pa_tp PMA.AD ADDR_A] in TP.
unfold app_mem, FS_BYTES in *.
destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
- destruct Hc as (b & Hb & X). pose proof (proj1 (WB b Hb)) as (_ & Y & _). lia.
- lia.
- apply (proj2 Hc). apply (PMA.ly_ctr_static L C LY). lia.
- destruct Hc as (f & Hf & X). pose proof (WF f Hf) as (Y1 & Y2 & _). lia.
- unfold in_shadow_of, S, SB in Hc. lia.
- destruct Hc as (f & Hf & X). pose proof (WF f Hf) as (Y1 & Y & _). unfold in_shadow_of, S, SB in X. lia.
- destruct Hc as (b & Hb & X). pose proof (proj1 (WB b Hb)) as (Y0 & _). unfold in_shadow_of, S, SB in X. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Theorem cxa_atexit_ok : ltac2:(TCodec.tc2 tcn__PmACxa "K&QBvBvRG&R0vR=%211v@&QG&R2%211&QH%113&QF%115&QI%117&QC%119&QJ%11;&QD%11=&QE%11?&QK%11A%J=IHEDA?=;97531").
Proof.
unfold HAJ.cxa_atexit_spec.
cbn [PMA.EXT HAJ.ec_cxa_pc HAJ.ec_cxa_scr HAJ.ec_atexit HAJ.ec_f0 HAJ.ec_a0 HAJ.ec_f1 HAJ.ec_a1 HAJ.ec_atc HAJ.ec_nl
paa_cxa_atexit_icpt paa_atexit_f0 paa_atexit_a0 paa_at_cxa_atexit PMA.AAD AADDR_A pa_atexit pa_atexit_call pa_exit_guard pa_need_locks PMA.AD ADDR_A].
cbv zeta.
intros fx R M model LB FF LK cr Aw K f a d HH Mh MI A10 A11 A12 ATX NL Rtp RET ASO K0 KONT.
rewrite (L5A.aly_segs L C LYa) in *.
pose proof (PMA.ly_tp L C LY) as TP. cbn [pa_tp PMA.AD ADDR_A] in TP.
set (sp := bv_unsigned (getr R 2%bv)) in *.
assert (Rsp : getr R (reg 2) = Z_to_bv 64 sp) by (unfold sp; rewrite L5K.rl2, Z_to_bv_bv_unsigned; reflexivity).
assert (Hsp : 0 <= sp < 2 ^ 64) by (unfold sp; pose proof (bv_unsigned_in_range 64 (getr R 2%bv)) as X; change (bv_modulus 64) with (2 ^ 64) in X; exact X).
destruct ASO as (S16 & SLO & SHI & SPT & SST & SUP). rewrite (L5A.aly_segs L C LYa) in SST.
rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12. rewrite L5K.rl4, TP in Rtp. rewrite L5K.rl1 in RET.
set (f' := bv_unsigned (getr R (reg 10))). set (a' := bv_unsigned (getr R (reg 11))). set (d' := bv_unsigned (getr R (reg 12))).
assert (R10 : getr R (reg 10) = Z_to_bv 64 f') by (unfold f'; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (R11 : getr R (reg 11) = Z_to_bv 64 a') by (unfold a'; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (R12 : getr R (reg 12) = Z_to_bv 64 d') by (unfold d'; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (Hf : 0 <= f' < 2 ^ 64) by (unfold f'; pose proof (bv_unsigned_in_range 64 (getr R (reg 10))) as X; change (bv_modulus 64) with (2 ^ 64) in X; exact X).
assert (Ha : 0 <= a' < 2 ^ 64) by (unfold a'; pose proof (bv_unsigned_in_range 64 (getr R (reg 11))) as X; change (bv_modulus 64) with (2 ^ 64) in X; exact X).
assert (Hd : 0 <= d' < 2 ^ 64) by (unfold d'; pose proof (bv_unsigned_in_range 64 (getr R (reg 12))) as X; change (bv_modulus 64) with (2 ^ 64) in X; exact X).
pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
destruct ST as (_ & CS). rewrite Forall_forall in CS.
assert (CINIT : L5.u8_at RSEGS M 0x13b9d8 1).
{ exact (CS (0x13b9d8, 1, 1) (L5A.aly_cells L C LYa _ ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 14 right; left; reflexivity))). }
destruct (PMA.ly_cxa_cells L C LY) as (IR & IC).
assert (CREAL : L5.u64_at RSEGS M 0x1345e8 0x113744) by exact (CS _ IR).
assert (CCTR : L5.u32_at RSEGS M 0x66ed90 0) by exact (CS _ IC).
destruct ATX as (AF & ALK & ASL & AHD & ANX & AF0 & AA0 & AF1 & AA1 & _).
assert (VU8 : forall x v0, 0x10000 <= x < 0x691000 -> L5.u8_at RSEGS M x v0 -> L5.u8_at RSEGS MV x v0).
{ intros x v0 Hx X. apply (proj2 (L5A.u8_at_vis H M x v0 (VIMG x 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
assert (VU32 : forall x v0, 0x10000 <= x -> x + 4 <= 0x691000 -> L5.u32_at RSEGS M x v0 -> L5.u32_at RSEGS MV x v0).
{ intros x v0 Hx Hx' X. apply (proj2 (L5A.u32_at_vis H M x v0 (VIMG x 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
assert (VU64 : forall x v0, 0x10000 <= x -> x + 8 <= 0x691000 -> L5.u64_at RSEGS M x v0 -> L5.u64_at RSEGS MV x v0).
{ intros x v0 Hx Hx' X. apply (proj2 (L5A.u64_at_vis H M x v0 (VIMG x 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
assert (V0 : L5.img_clear MV 1228800 1261568) by (apply L5A.img_clear_mrestrict; exact GOT).
assert (V1 : L5.u64_at RSEGS MV 1289464 2147450880) by (apply VU64; [lia| lia| exact CSB]).
assert (V2 : L5.u32_at RSEGS MV 1289472 1) by (apply VU32; [lia| lia| exact CUAR]).
assert (V3 : L5.writable RSEGS MV (sp - 1024) 1024).
{ apply (proj2 (L5A.writable_vis H M (sp - 1024) 1024 (VIS (sp - 1024) 1024 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
intros dd k Hdd Hkk. apply SST; lia. }
assert (V4 : L5.u32_at RSEGS MV 6745488 0) by (apply VU32; [lia| lia| exact CCTR]).
assert (V5 : L5.writable RSEGS MV 6745488 4) by (apply writable_img; [vm_compute; reflexivity| lia| lia| lia]).
assert (V6 : L5.u8_at RSEGS MV 1292760 1) by (apply VU8; [lia| exact CINIT]).
assert (V7 : L5.u64_at RSEGS MV 1263080 1128260) by (apply VU64; [lia| lia| exact CREAL]).
assert (V8 : L5.u8_at RSEGS MV 6876624 0) by (apply VU8; [lia| exact AF]).
assert (V9 : L5.u32_at RSEGS MV 6876628 0) by (apply VU32; [lia| lia| exact ALK]).
assert (V10 : L5.u32_at RSEGS MV 6876632 2) by (apply VU32; [lia| lia| exact ASL]).
assert (V11 : L5.u64_at RSEGS MV 6876640 6876648) by (apply VU64; [lia| lia| exact AHD]).
assert (V12 : L5.writable RSEGS MV 6876624 544) by (apply writable_img; [vm_compute; reflexivity| lia| lia| lia]).
assert (V13 : L5.u8_at RSEGS MV 6877203 0) by (apply VU8; [lia| exact NL]).
cfeed P (PMACXP.acxA_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => f' | 34%nat => a' | 35%nat => 0 | 36%nat => d' | _ => 0 end)) ltac:(first [assumption | unfold PMACXP.aligned; lia | lia]).
destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & R1a0 & R1a1 & R1a2 & R1a3 & CT1 & SL1 & A21 & F21 & A11' & F11).
assert (R1ra : getr R1 (reg 1) = getr R (reg 1)) by (apply KS1; inl).
rewrite <- R1ra in RET.
pose proof (ret_rok fx1 R1 M1v 0x6d140 (ltac:(oW' 0x6d140%Z)) (ltac:(oF' 0x6d140%Z)) eq_refl (ltac:(oD' 0x6d140%Z)) RET) as MS2. rewrite R1ra in MS2.
set (WX := fun x => (sp - 1024 <= x < sp - 1024 + 1024) \/ (0 + 6745488 <= x < 0 + 6745488 + 4) \/ (0 + 6876632 <= x < 0 + 6876632 + 4)
\/ (0 + 6876672 <= x < 0 + 6876672 + 16) \/ (0 + 6876928 <= x < 0 + 6876928 + 16)).
change (srealizes RSEGS SCFG (L5A.cfg (fx:=fx) R 0x6d0c0 M model) K).
apply (apiece_ctr LB FF LK cr Aw M model fx fx1 R 0x6d0c0 R1 (bv_unsigned (getr R (reg 1))) M1v WX K HH (conj Mh MI)).
{ eapply msteps_trans; [exact MS1| exact MS2]. }
{ exact MG1. }
{ intros x Hx N. unfold WX in N. apply FRZ1; [exact Hx| | | | |]; intros X; apply N; tauto. }
{ intros x Hx Wx Nc. rewrite TP in Nc. unfold WX in Wx. destruct Wx as [Wx|[Wx|Wx]].
- split; [|intros X; pose proof (PMA.ly_ro L C LY x X); lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
- exfalso. lia.
- split; [|apply (PMKA2.rt_ro_bss L C x LY); lia]. unfold aclientw, aclient_g. right; right; left.
rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|].
intros [X|X].
+ apply (PMA.ly_static L C LY x); [|exact X]. apply PMST.in_foot_atexit. cbn [pa_atexit PMA.AD ADDR_A]. lia.
+ pose proof (PMA.ly_ro L C LY x X). lia. }
{ rewrite TP. exact CT1. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
assert (FR1' : forall x, 6876624 <= x < 6876624 + 544 -> ~ WX x -> M1 (Z_to_bv 64 x) = M (Z_to_bv 64 x)) by (intros x Hx N; apply FR1; [lia| exact N]).
assert (W1 : forall x v0, 6876624 <= x -> x + 8 <= 6876624 + 544 -> L5.u64_at RSEGS M1v x v0 -> L5.u64_at RSEGS M1 x v0).
{ intros x v0 Hx Hx' X. rewrite <- VIS1 in X. exact (proj1 (L5A.u64_at_vis H M1 x v0 (VIMG x 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) X). }
unfold L5A.cfg. rewrite Z_to_bv_bv_unsigned. rewrite <- L5K.rl1.
pose proof AM1 as (Mh1 & MI1).
apply (KONT fx1 R1 M1 model1 Aw).
- apply L5SAR.preserved_by_index. intros k Hk. apply KS1. unfold L5SAR.cs_all in Hk. repeat (destruct Hk as [<-|Hk]; [inl|]). destruct Hk.
- rewrite L5K.rl10. exact R1a0.
- unfold HAJ.atexit_cells.
split; [apply (L5C.u8_at_agree RSEGS M M1); [intros i Hi; apply FR1'; [lia| unfold WX; lia] | lia | lia | exact AF]|].
split; [apply (PMF.u32_at_agree RSEGS M M1); [intros j Hj; apply FR1'; [lia| unfold WX; lia]| lia| lia| exact ALK]|].
split; [rewrite <- VIS1 in SL1; exact (proj1 (L5A.u32_at_vis H M1 6876632 4 (VIMG 6876632 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) SL1)|].
split; [apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1'; [lia| unfold WX; lia] | lia | lia | exact AHD]|].
split; [apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1'; [lia| unfold WX; lia] | lia | lia | exact ANX]|].
split; [apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1'; [lia| unfold WX; lia] | lia | lia | exact AF0]|].
split; [apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1'; [lia| unfold WX; lia] | lia | lia | exact AA0]|].
split; [apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1'; [lia| unfold WX; lia] | lia | lia | exact AF1]|].
split; [apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1'; [lia| unfold WX; lia] | lia | lia | exact AA1]|].
split; [apply u64_norm; rewrite <- A10; apply (W1 6876672); [lia| lia| exact F11]|].
split; [apply (W1 6876680); [lia| lia| exact F21]|].
split; [apply u64_norm; rewrite <- A11; apply (W1 6876928); [lia| lia| exact A11']|].
apply (W1 6876936); [lia| lia| exact A21].
- intros x Hx Hc Hn. apply FR1; [exact Hx|]. unfold WX. intros [X|[X|X]].
+ destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M (vml_of model) sp 1024 x HH SPT Hc) as [(Y1 & Y2)|Y]; [apply Y2; lia| lia].
+ exact (ctr_not_client LB FF LK cr Aw M (vml_of model) sp 1024 x HH ltac:(lia) ltac:(lia) Hc).
+ apply Hn. lia.
- intros x Hx HM. apply MGM1. exact HM.
- intros x Hx. apply MGM1. replace x with (sp - 1024 + (x - (sp - 1024))) by lia.
apply store_ok_defined; [lia|]. apply SST; lia.
- exact MRT1.
- intros x Hx. exact Hx.
- exact MI1.
- exact HH1.
Qed.
End WithHeap.
End PMACXA.
