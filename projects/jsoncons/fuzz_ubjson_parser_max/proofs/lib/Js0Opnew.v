(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Js0PlanKit AsanPlanCore BigLinkBase BigLinkGlue L5Defs L5Core L5CoreKit PmLayout PmLayoutS PmModel PmStatics PmSpecs PmSpecsS PmStep.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require Import LibSegJs_lcnew1 LibSegJs_lcnew2.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Js0Opnew () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3.AX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigLinkGlue.BG."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0Opnew.L5NEW.L5CS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0Opnew.L5NEW.P1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0Opnew.L5NEW.P2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0Opnew.L5NEW.SCFG_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsS.PMS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1bool"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "1true"; "2and"; "2eq"; "2ex"; "2not"; "3nth"; "4Z"; "0HI"; "0L"]; ["5ALU_ADD"; "6bvmap"; "0M"; "0M1"; "0M3"; "0R"; "0R1"; "0R3"; "7EAlu"; "7ELit"; "7EVar"; "7KAlign"; "7KRange"; "7KWord"; "7KWr"; "7SA"]; ["7expr"; "7kentry"; "8kept_ok"; "8u64_at"; "8writable"; "9msteps"; ":OPNEW"; ";cells"; ";kn0"; ";regs0"; ";regs_out"; "<kn0"; "<regs0"; "<regs_out"; "=KS1"; "=KS2"]; ["=MALLOC"; "=RET1"; "=RETI"; ">ra_ok"; "?opnew_spec"; "@FPState"; "@getr"; "@mkst"; "@seg_rom"; "Amem_grows"; "Bloaded_segments"; "0SCFG_P"; "CIn"; "Dadd"; "Dle"; "Dlt"]; ["Dmodulo"; "Dof_nat"; "Dpow"; "Dsub"; "0a"; "0fx"; "0fx'"; "0n"; "0r"; "0ra0"; "0s00"; "0sp"; "EZ_to_bv"; "Ebv"; "Ebv_unsigned"; "0x"]]).
Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastTauto.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Plain.
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc. Local Ltac tauto := L5FastTauto.ptauto0.
Module L5NEW.
Module L5CS.
Abbreviation RSEGS := PMS.RSEGS.
Definition HEAP_STACK : Z := 8224.
Definition OPNEW : Z := 0xae098.
Definition OPNEW_SCR : Z := 16 + HEAP_STACK.
Definition OPDEL : Z := 0x543fc.
Definition OPDEL_SIZED : Z := 0x54400.
Definition OPDEL_SCR : Z := HEAP_STACK.
Definition TP : Z := 0xc7c60.
End L5CS.
Lemma nth_error_single {A} (x y : A) i : nth_error [x] i = Some y -> y = x.
Proof. destruct i; simpl. congruence. destruct i; discriminate. Qed.
Import L5CS.
Module P1 := LibSegJs_lcnew1.
Module P2 := LibSegJs_lcnew2.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)).
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Definition MALLOC : Z := 0x9aab4.
Definition RET1 : Z := 0xae0b4.
Definition RETI : Z := 0xae0dc.
Definition KS1 : list nat := Eval vm_compute in (BG.kept_list 48 P1.regs0 P1.regs_out).
Lemma KS1_ok : ltac2:(TCodec.tc2 tcn__Js0Opnew ":'9'1&Q2uQ@&Q9&Q:&Q>%544321(7%93821"). Proof. vm_compute. reflexivity. Qed.
Definition KS2 : list nat := Eval vm_compute in (BG.kept_list 48 P2.regs0 P2.regs_out).
Lemma KS2_ok : ltac2:(TCodec.tc2 tcn__Js0Opnew ":'9'1&Q2uQ@&Q<&Q=&Q?%544321(7%93821"). Proof. vm_compute. reflexivity. Qed.
Lemma kn0_1 : ltac2:(TCodec.tc2 tcn__Js0Opnew "Q3'9'3'Q1%211&Q8(2(L(Ju2%211+SoomohPPP@+TPPPPPPPP0%63321(K+@%2261(N(O-@%22:1(I%117%6231u:%A11+1+TPPPP0%E3321(5%11K%I3L31%J3M91%K3NA1%L3OE1%Q23ON1").
Proof. vm_compute. reflexivity. Qed.
Lemma cells_1 : ltac2:(TCodec.tc2 tcn__Js0Opnew "J'9'3'Q1%211&Q7(2(M(O(Ju2%211-@%5221u8%611%93321-8%:271u1%;11%>3371(5%11D%B3E31%C3F91%I3FE1").
Proof. vm_compute. reflexivity. Qed.
Lemma r1_1 : ltac2:(TCodec.tc2 tcn__Js0Opnew "<'9'Q0&<u1&Q:(Iz%211%647541+ehUD%511%;3:31"). Proof. vm_compute. reflexivity. Qed.
Lemma r2_1 : ltac2:(TCodec.tc2 tcn__Js0Opnew "A'9'Q0&<u2&Q:(Iz%211%647541(H(@(J%119-@%911%63531%@3?81"). Proof. vm_compute. reflexivity. Qed.
Lemma r8_1 : ltac2:(TCodec.tc2 tcn__Js0Opnew "='9'Q0&<u8&Q:(Iz%211%647541(Ju:%211%<3;41"). Proof. vm_compute. reflexivity. Qed.
Lemma r10_1 : ltac2:(TCodec.tc2 tcn__Js0Opnew "<'9'Q0&<u:&Q:(Iz%211%647541(J%117%;3:31"). Proof. vm_compute. reflexivity. Qed.
Lemma kn0_2 : ltac2:(TCodec.tc2 tcn__Js0Opnew "Q?'9'3'Q1%211&Q;(2(L(Ju2%211+SoomohPPP@+TPPPPPPPP0%63321(K+@%2261(N(O-@%22:1(I%117%6231u:%A11+1+_oooooooooooO%E3321(M-8%=2E1u8uQ8%J11%63431uQ9%M11%93B61(5%11Q5%Q33Q631%Q43Q771%Q53Q8?1%Q63Q9E1%Q73Q:M1%Q83Q;Q11%Q>3Q;Q:1").
Proof. vm_compute. reflexivity. Qed.
Lemma r1_2 : ltac2:(TCodec.tc2 tcn__Js0Opnew "='9'Q0&<u1&Q=(Iz%211%647541(JuQ8%211%<3;41"). Proof. vm_compute. reflexivity. Qed.
Lemma r2_2 : ltac2:(TCodec.tc2 tcn__Js0Opnew "<'9'Q0&<u2&Q=(Iz%211%647541(J%117%;3:31"). Proof. vm_compute. reflexivity. Qed.
Lemma r8_2 : ltac2:(TCodec.tc2 tcn__Js0Opnew "='9'Q0&<u8&Q=(Iz%211%647541(JuQ9%211%<3;41"). Proof. vm_compute. reflexivity. Qed.
Lemma r10_2 : ltac2:(TCodec.tc2 tcn__Js0Opnew "<'9'Q0&<u:&Q=(Iz%211%647541(J%117%;3:31"). Proof. vm_compute. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_p1_run := (ltac2:(TCodec.tc2 tcn__Js0Opnew "U4'QE&Ay5'R=yR0%211%5241'6y8%611%311p061'='9&QFr4&R<&R1u:%211%42B1%7261r2%72C1%;3C31'8&QN+1r3%3221&R2+2+K%3221%8261%:261r6u2%E11%G2Q51%J241%I2Q5=%M3Q521&R0+@%22N1z%Q23Q321&QM+SoomohPPP0%2216r5%J221+Q?%H2G1%M2C1&Q4r9&R3r7%221@%5341A':'Q5&QJ&QGr?r>&Q6%QE2R11r=&QH%118%8576431&Q@%QK2R71r1%<5QAQG215%?3>51'4&QL&Q>%23361%R21QM%R42RB1%R72R61r@%R9213%R;3RC31p071pU0;1u1%R;11%R=2RK1%R@2R81&QA%R@2RL1%RD3RL31%RD2R<QKr;%Q:21QH%RE2S11%RI3S141u8%RG11%RI2S71%RL2RD1r<%RL2S81%S03S831%S02RHRJ%S23S:13&Q3+8%QH2?1&R>%S62QAG%22SA1%63Q:41%S92QD>%52SD1%93Q=E1&;%R12@R?%92SHQ@%S3221&QO%123D%S7231%711%S61S<%R11S=%SG3SJ21p041pT:T11&QI%12R2QL%S@231%SA2A1%SB2E1%SC2M1%SD2Q01%SE2Q81%SF2Q>1%SG2QF1%SH2R31qQ8T71%RE2T81qQ>T>1%RG2T?1qT>TF1%RI2TG1p0RK1p0S21p0S61p0S<1p0SB1p0SJ1p0T61pTHTC1pT@TD1pQ6TF1pQ<TL1pT<U31")) (only parsing).
Variable fx : ltac:(sec_ty2 constr:(SEC_T_p1_run) 0%nat 0%nat).
Variable R : ltac:(sec_ty2 constr:(SEC_T_p1_run) 1%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_p1_run) 2%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_p1_run) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_p1_run) 4%nat 0%nat).
Lemma p1_run : ltac:(sec_stmt2 constr:(SEC_T_p1_run) 5%nat 0%nat).
Proof.
intros H10 Hn H2 A16 SLO SHI WR.
set (Vf := fun k : nat => getr R (reg k)).
set (E := Env Vf (fun _ => [])).
assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; rewrite H2; apply BG.unsigned_lit; lia).
assert (U10: bv_unsigned (ev E 10) = n) by (cbv [E ev Vf]; rewrite H10; apply BG.unsigned_lit; lia).
assert (HR: regs_ok E P1.regs0 R).
{ apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl P1.regs0 nth edenot ev E Vf]. repeat split; reflexivity. }
assert (HK: know_ok RSEGS E M P1.kn0).
{ unfold know_ok. rewrite kn0_1.
apply Forall_cons. { eapply BG.kentry_KRange_var. exact U2. lia. }
apply Forall_cons. { eapply BG.kentry_KAlign_var. exact U2. lia. lia. }
apply Forall_cons. { eapply BG.kentry_KWr_var. exact U2. lia. lia. lia. exact WR. }
apply Forall_cons. { eapply BG.kentry_KRange_var. exact U10. lia. }
apply Forall_nil. }
destruct (P1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
apply nth_error_single in Hnth. subst ps0. change P1.NX0 with 48%nat in Hag.
assert (AG: forall k, (k < 48)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
assert (A2: bv_unsigned (ev E' 2) = sp) by (rewrite AG by lia; exact U2).
exists fx', R', M'. split. exact Hms.
split. { intros j Hj. apply (BG.kept_regs E E' R R' P1.regs0 P1.regs_out 48 KS1 KS1_ok HR Hag Hregs j Hj). }
split. { rewrite (BG.out_reg P1.regs_out E' R' 1 Hregs) by lia. rewrite r1_1. reflexivity. }
split. { rewrite (BG.out_reg P1.regs_out E' R' 2 Hregs) by lia. rewrite r2_1. cbn [edenot].
rewrite (BG.word_of_unsigned _ _ A2), BG.alu_add_lit. reflexivity. }
split. { rewrite (BG.out_reg P1.regs_out E' R' 8 Hregs) by lia. rewrite r8_1. cbn [edenot]. rewrite AG by lia. apply BG.word_of_unsigned. exact U10. }
split. { rewrite (BG.out_reg P1.regs_out E' R' 10 Hregs) by lia. rewrite r10_1. cbn [edenot]. rewrite AG by lia. apply BG.word_of_unsigned. exact U10. }
split. { eapply (BG.u64_of_KWord E' M' 2 (-8)). apply Hcells. change (SR.ps_cells P1.ps0) with P1.cells. rewrite cells_1. right; left; reflexivity. exact A2.
cbn [edenot]. rewrite AG by lia. reflexivity. }
split. { eapply (BG.u64_of_KWord E' M' 2 (-16)). apply Hcells. change (SR.ps_cells P1.ps0) with P1.cells. rewrite cells_1. left; reflexivity. exact A2.
cbn [edenot]. rewrite AG by lia. reflexivity. }
split. { intros a Ha. apply Hfr. unfold SGP.outside. change P1.F0 with [(EVar 2, -16, ELit 16)].
constructor. { unfold estart, elenZ. cbn [edenot a_base a_off]. rewrite A2. rewrite BG.unsigned_lit by lia. lia. } constructor. }
exact Hgr.
Qed.
End SE.
Lemma ret_ae08c : ltac2:(TCodec.tc2 tcn__Js0Opnew "QN'QE&Ay5'R=yR0%211%5241'6y8%611%311p061'='9&QFr3&R<&R1u1%211%42B1%7261r1%72C1%;3C31'8&QNzr2%3221&QO&R2+2+Q?%3221%5271%;271&R0%12G6%J3K1<'Q5&QJ&QGr7r6&QB%N2Q:1r5&QH%118%8576431r4%Q42Q@1%;5:9164%>3=41p0@1p0D1p0Q11pTBQ>1pQ6Q@1pQ<QF1pT<QM1").
Proof. intros fx R M r. intros H1 Hr He. apply (PMK.ret_to RSEGS fx R M RETI (ltac:(oW' 0xae0dc%Z)) r (ltac:(oF' 0xae0dc%Z)) eq_refl (ltac:(oD' 0xae0dc%Z)) H1 Hr He). Qed.
Section SE.
Local Abbreviation SEC_T_p2_run := (ltac2:(TCodec.tc2 tcn__Js0Opnew "U='QE&Ay5'R=yR0%211%5241'6y8%611%311p061'='9&QFr7&R<&R1u:%211%42B1%7261r5%72C1%;3C31'8&QN+1r6%3221&QO&R2+2+R0%3221%5271%;271r9u2%F11%H2Q61%K241&R3+@%22@1%M2Q91%Q13Q951&R0%12Q15z%Q53Q621&QM+SoomohPPP0%221:r8%M221+Q?%J2I1%Q02E1&Q4r<r:%D21C%4331D&Q3r=r;+8%J221%53418r>%M2;L%8321;%Q?2H=%Q<2>Q8%QB221%QO3R06@&QC%11=':'Q5&QJ&QGrHrG&QA%R62RB1rF&QH%118%8576431r3r2rA%R>2RJ1r1%>554217%A3@71'4&QL&Q?%23361r4%RF1;%RH2S61%RK231rI%RM213%RO3S731p081pU0<1u1%RO11%S12S?1%S42F1rC%S42S@1%S83S@31%S82JR>rD%S82SD1%S<3SD31u8%S:11%S<2SJ1%S?2Q11rB%S?2SK1%SC3SK31%SC2Q5S=rE%SC2SO1%SG3SO31%Q91Q6%QB1Q7%SJ3SM21pT:T31&QI%12QCQ;%SB231%SC281%SD2=1%SE2E1%SF2J1%SG2Q21%SH2Q@1qQ:T71%R42T81qQ@T>1%R62T?1qT>TF1%R82TG1p0R:1p0R=1p0R?1p0R@1p0RD1p0RH1p0RO1p0S51p0S91p0S?1p0SD1p0SO1p0T<1pTBTI1pTFTJ1pTDTK1pTHTL1p2TM1pQ6TO1pQ<U51pT<U<1")) (only parsing).
Variable fx : ltac:(sec_ty2 constr:(SEC_T_p2_run) 0%nat 0%nat).
Variable R : ltac:(sec_ty2 constr:(SEC_T_p2_run) 1%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_p2_run) 2%nat 0%nat).
Variable A : ltac:(sec_ty2 constr:(SEC_T_p2_run) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_p2_run) 4%nat 0%nat).
Variable ra0 : ltac:(sec_ty2 constr:(SEC_T_p2_run) 5%nat 0%nat).
Variable s00 : ltac:(sec_ty2 constr:(SEC_T_p2_run) 6%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_p2_run) 7%nat 0%nat).
Lemma p2_run : ltac:(sec_stmt2 constr:(SEC_T_p2_run) 8%nat 0%nat).
Proof.
intros H10 HA H2 A16 SLO SHI WR C8 C16 Hra0 Hs00 Er [Hr He].
set (Vf := fun k : nat => match k with 2%nat => Z_to_bv 64 sp | 40%nat => Z_to_bv 64 ra0 | 41%nat => Z_to_bv 64 s00 | _ => getr R (reg k) end).
set (E := Env Vf (fun _ => [])).
assert (U2: bv_unsigned (ev E 2) = sp) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
assert (U10: bv_unsigned (ev E 10) = A) by (cbv [E ev Vf]; rewrite H10; apply BG.unsigned_lit; lia).
assert (U40: bv_unsigned (ev E 40) = ra0) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
assert (U41: bv_unsigned (ev E 41) = s00) by (cbv [E ev Vf]; apply BG.unsigned_lit; lia).
assert (HR: regs_ok E P2.regs0 R).
{ apply BG.regs_ok_of_slots. reflexivity. cbv [BG.slots tl P2.regs0 nth edenot ev E Vf]. repeat split; try reflexivity.
rewrite BG.alu_add_lit. exact H2. }
assert (HK: know_ok RSEGS E M P2.kn0).
{ unfold know_ok. rewrite kn0_2.
apply Forall_cons. { eapply BG.kentry_KRange_var. exact U2. lia. }
apply Forall_cons. { eapply BG.kentry_KAlign_var. exact U2. lia. lia. }
apply Forall_cons. { eapply BG.kentry_KWr_var. exact U2. lia. lia. lia. exact WR. }
apply Forall_cons. { eapply BG.kentry_KRange_var. exact U10. lia. }
apply Forall_cons. { eapply BG.kentry_KWord_var. exact U2. exact U40. lia. lia. exact C8. }
apply Forall_cons. { eapply BG.kentry_KWord_var. exact U2. exact U41. lia. lia. exact C16. }
apply Forall_nil. }
destruct (P2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
apply nth_error_single in Hnth. subst ps0. change P2.NX0 with 48%nat in Hag.
assert (AG: forall k, (k < 48)%nat -> ev E' k = ev E k) by (intros k Hk; symmetry; apply (proj1 Hag k Hk)).
assert (MM: forall a : word, M' a = M a). { intros a. apply Hfr. constructor. }
assert (R1: getr R' (reg 1) = Z_to_bv 64 ra0).
{ rewrite (BG.out_reg P2.regs_out E' R' 1 Hregs) by lia. rewrite r1_2. cbn [edenot]. rewrite AG by lia. apply BG.word_of_unsigned. exact U40. }
exists fx', R', M'. split.
{ eapply msteps_trans. exact Hms. change (SR.ps_pc P2.ps0) with RETI. apply ret_ae08c. rewrite R1. subst ra0. reflexivity. exact Hr. exact He. }
split. { intros j Hj. apply (BG.kept_regs E E' R R' P2.regs0 P2.regs_out 48 KS2 KS2_ok HR Hag Hregs j Hj). }
split. exact R1.
split. { rewrite (BG.out_reg P2.regs_out E' R' 2 Hregs) by lia. rewrite r2_2. cbn [edenot]. rewrite AG by lia. apply BG.word_of_unsigned. exact U2. }
split. { rewrite (BG.out_reg P2.regs_out E' R' 8 Hregs) by lia. rewrite r8_2. cbn [edenot]. rewrite AG by lia. apply BG.word_of_unsigned. exact U41. }
split. { rewrite (BG.out_reg P2.regs_out E' R' 10 Hregs) by lia. rewrite r10_2. cbn [edenot]. rewrite AG by lia. apply BG.word_of_unsigned. exact U10. }
split. exact MM. exact Hgr.
Qed.
End SE.
Section WithHeap.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Theorem opnew_ok : ltac2:(TCodec.tc2 tcn__Js0Opnew "5&QDvQKv?v>%43321").
Proof.
unfold PMS.opnew_spec, PMSP.opnew_spec. change (pa_opnew PMS.AD) with OPNEW. change PMSP.OPNEW_SCR with OPNEW_SCR. intros fx R M model K LB cr n sp r HH (Mh & Ml & Mm) HK0 H10 Hn CR H1 RA H2 H4 STK KONT.
pose proof STK as (A16 & SLO & SHI & STOP & DEF). unfold OPNEW_SCR, HEAP_STACK in SLO, DEF.
pose proof RA as [Hr He].
assert (WR16: BG.writable M (sp - 16) 16).
{ change (L5.writable RSEGS M (sp - 16) 16). eapply L5.writable_sub. apply (L5C.writable_of_defined RSEGS). exact DEF. lia. lia. lia. lia. }
destruct (p1_run fx R M n sp H10 ltac:(lia) H2 A16 ltac:(lia) ltac:(lia) WR16)
as (fx1 & R1 & M1 & MS1 & K1 & R1_1 & R1_2 & R1_8 & R1_10 & C8 & C16 & FR1 & GR1).
unfold PMSP.cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
pose proof (hio_malloc L SCFG HI HIok) as HM. unfold malloc_spec in HM. rewrite (PMS.ly_segs L LY), (PMS.ly_malloc L LY) in HM.
change (Z_to_bv 64 MALLOC) with (Z_to_bv 64 0x9aab4).
eapply (HM fx1 R1 M1 model LB cr n K); clear HM.
-
eapply (L5C.hi_heap_client L SCFG HI LB cr M M1). exact HIok. exact HH.
+ exact (PMS.ly_ro L LY).
+ rewrite (PMS.ly_img_hi L LY). lia.
+ lia.
+ intros a Ha. destruct (Z_lt_le_dec a (sp - 16)) as [Hlt|Hge]. left. apply FR1. rewrite BG.unsigned_lit by lia. lia.
destruct (Z_lt_le_dec a sp) as [Hlt'|Hge']. right; left. lia. left. apply FR1. rewrite BG.unsigned_lit by lia. lia.
+ exact GR1.
- exact Mh. - exact Ml. - exact Mm.
- exact R1_10.
- lia.
- exact CR.
- rewrite (PMS.ly_tp L LY). rewrite <- H4. apply (K1 4%nat). cbn; tauto.
- rewrite L5K.rl1, R1_1. apply L5K.ret_ok_lit. split. unfold RET1. lia. reflexivity.
- rewrite L5K.rl2, R1_2, BG.unsigned_lit by lia. unfold stack_ok. rewrite (PMS.ly_stack L LY), (PMS.ly_segs L LY). unfold HEAP_STACK.
split. { replace (sp - 16) with (sp + (-1) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
split. lia. split. lia. split. lia.
assert (W1 : L5.writable RSEGS M1 (sp - 16 - 8224) 8224).
{ eapply L5.writable_grows. exact GR1. eapply L5.writable_sub. apply (L5C.writable_of_defined RSEGS M _ _ DEF); lia. lia. lia. }
intros d m Hd Hm. apply W1. lia. lia.
- exact HK0.
-
intros R2 M2 model2 A HA RP BR BA DEFA PRES MBV HH2.
rewrite L5K.rl1, R1_1.
pose proof BR as (BR0 & BR1 & BR2 & BR3 & BR4). rewrite (PMS.ly_img_lo L LY), (PMS.ly_img_hi L LY) in BR1.
rewrite L5K.rl2, R1_2, BG.unsigned_lit in PRES by lia. destruct PRES as [PRES SDEF]. rewrite (PMS.ly_stack L LY) in PRES, SDEF. unfold HEAP_STACK in PRES, SDEF.
assert (CL: forall a, sp - 16 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
{ intros a Ha. apply PRES. lia. right. left. lia. unfold in_errno. rewrite (PMS.ly_errno L LY). lia. }
assert (C8' : BG.u64_at M2 (sp - 8) (bv_unsigned (getr R (reg 1)))).
{ eapply (L5C.u64_at_agree RSEGS M1 M2). intros i Hi. apply CL. lia. lia. lia. exact C8. }
assert (C16' : BG.u64_at M2 (sp - 16) (bv_unsigned (getr R (reg 8)))).
{ eapply (L5C.u64_at_agree RSEGS M1 M2). intros i Hi. apply CL. lia. lia. lia. exact C16. }
assert (WR2 : BG.writable M2 (sp - 16) 16).
{ change (L5.writable RSEGS M2 (sp - 16) 16). eapply (L5C.writable_agree RSEGS M1 M2). intros i Hi. apply CL. lia. lia. lia.
eapply L5.writable_grows. exact GR1. exact WR16. }
pose proof (bv_unsigned_in_range _ (getr R (reg 1))) as RG1. pose proof (bv_unsigned_in_range _ (getr R (reg 8))) as RG8.
change (bv_modulus 64) with (2 ^ 64) in RG1, RG8.
assert (E1 : bv_unsigned (getr R (reg 1)) = r). { rewrite <- L5K.rl1, H1. apply BG.unsigned_lit. lia. }
destruct (p2_run fx1 R2 M2 A sp (bv_unsigned (getr R (reg 1))) (bv_unsigned (getr R (reg 8))) r
HA ltac:(lia) ltac:(rewrite <- L5K.rl2, (RP 2%bv ltac:(cbn; tauto)), L5K.rl2; exact R1_2) A16 ltac:(lia) ltac:(lia) WR2
C8' C16' ltac:(lia) ltac:(lia) E1 RA)
as (fx3 & R3 & M3 & MS3 & K3 & R3_1 & R3_2 & R3_8 & R3_10 & MM3 & GR3).
eapply (L5.cps_of_msteps RSEGS). { rewrite (L5C.halted_but_vm _ _ MBV). exact Mh. } { rewrite (L5C.lazy_but_vm _ _ MBV). exact Ml. }
exact MS3.
apply (KONT fx3 R3 M3 model2 A).
+ rewrite L5K.rl10. exact R3_10.
+
apply L5K.regs_preserved_by_index. intros i Hi.
cbn in Hi. destruct Hi as [<-|Hi]. { rewrite R3_2, <- H2, L5K.rl2. reflexivity. }
destruct Hi as [<-|Hi]. { rewrite (K3 3%nat) by (cbn; tauto). rewrite <- L5K.rl3, (RP 3%bv) by (cbn; tauto). rewrite L5K.rl3. apply (K1 3%nat). cbn; tauto. }
destruct Hi as [<-|Hi]. { rewrite (K3 4%nat) by (cbn; tauto). rewrite <- L5K.rl4, (RP 4%bv) by (cbn; tauto). rewrite L5K.rl4. apply (K1 4%nat). cbn; tauto. }
destruct Hi as [<-|Hi]. { rewrite R3_8. symmetry. apply BG.word_of_unsigned. reflexivity. }
assert (G: forall j, In j [9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (reg j) = getr R (reg j)).
{ intros j Hj.
assert (M2j: In j KS2) by (pose proof Hj as H'; L5K.inlist H').
assert (M1j: In j KS1) by (pose proof Hj as H'; L5K.inlist H').
assert (MCj: In j L5K.CS) by (pose proof Hj as H'; L5K.inlist H').
rewrite (K3 j M2j). rewrite (L5K.regs_preserved_index R1 R2 j RP MCj). apply (K1 j M1j). }
apply G. L5K.inlist Hi.
+
split. exact BR. split. exact BA. intros i Hi. rewrite (MM3 (Z_to_bv 64 (A + i))). apply DEFA. exact Hi.
+
split.
* intros a (Ha & CA & NE & _). rewrite (MM3 (Z_to_bv 64 a)).
destruct CA as [IB|[[S1 S2]|IM]].
-- rewrite PRES. apply FR1. rewrite BG.unsigned_lit by lia.
{ destruct IB as (b & Hb & Hin). pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M _ HH) b Hb) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _).
lia. }
lia. left. exact IB. exact NE.
-- unfold OPNEW_SCR, HEAP_STACK in S2. rewrite PRES. apply FR1. rewrite BG.unsigned_lit by lia. lia. lia.
right. left. split. exact S1. lia. exact NE.
-- rewrite PRES. apply FR1. rewrite BG.unsigned_lit by lia. rewrite (PMS.ly_img_hi L LY) in IM. lia. lia. right. right. exact IM. exact NE.
* split.
{ unfold OPNEW_SCR, HEAP_STACK. intros i Hi. rewrite (MM3 (Z_to_bv 64 _)).
destruct (Z_lt_le_dec (sp - (16 + 8224) + i) (sp - 16)) as [Hlt|Hge].
-- apply SDEF. lia.
-- rewrite CL by lia. apply GR1. apply DEF. lia. }
intros a Ha CA NE D0. rewrite (MM3 (Z_to_bv 64 a)). unfold OPNEW_SCR, HEAP_STACK in CA.
rewrite PRES; [apply GR1; exact D0 | lia | | exact NE].
eapply L5K.client_inner. exact CA. lia. lia.
+ exact MBV.
+ eapply (L5C.hi_heap_client L SCFG HI). exact HIok. exact HH2. exact (PMS.ly_ro L LY). rewrite (PMS.ly_img_hi L LY); lia. lia.
intros a Ha. left. apply MM3. exact GR3.
Qed.
End WithHeap.
End SCFG_1.
End L5NEW.
