(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceA LibIface AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA L5DefsA L5CoreA L5StepAR L5CoreBR L5ADetailHR L5AFrameKR HeapIfaceAJx PmLayout PmLayoutA PmModel PmModelFacts PmModelFactsA PmStatics PmStaticsA PmSpecsA PmSpecsAa PmStepA PmAReset1 PmAHarnessStmts PmAHarnessKit PmAHarnessKit2 PmAHarnessSK PmAHarnessP4 Ja0Sums AsanPlanCore AsanPlanSoundSums.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmAHarness11 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanCore.APC."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundSums.APSX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5DefsA.L5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmAHarnessStmts.PMHAS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5AFrameKR.L5AFKR."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreA.L5CA."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0Ac"; "0BX"; "1O"; "1app"; "1list"; "1nat"; "1option"; "1prod"; "2and"; "2eq"; "2ex"; "2not"; "3lt"; "4Z"; "0F"]; ["0FF"; "0HI"; "0K"; "0L"; "0LB"; "0LK"; "0LKc"; "5Model"; "6bvmap"; "0M"; "0M9v"; "0MV"; "0Mc"; "0Mf"; "0R"; "0R9"]; ["0Rc"; "0Rf"; "7caller_saved"; "8kept_ok"; "9msteps"; ":credit"; ":regs_preserved"; ";SB"; ";fframe"; ";model_rt"; ";ri_inv"; ";vml_of"; "=defined"; "=img_clear"; "=u32_at"; "=u64_at"]; ["=u8_at"; "=writable"; "<SCFG"; ">cfg"; "?U"; "?rinvH"; "?tfrk"; "@FPState"; "@getr"; "@mkst"; "@seg_rom"; "ATSet"; "Bsrealizes"; "Cmem_grows"; "DWret"; "Dbinv"]; ["Eahpres"; "Eamodel_ok"; "Floaded_segments"; "0SCFG_P"; "GIn"; "Hadd"; "Hdiv"; "Hle"; "Hlt"; "Hof_nat"; "Hpow"; "Hsub"; "0V2"; "0W"; "0a"; "0ar"]; ["0cls"; "0crc"; "0fl"; "0fx"; "0fx9"; "0fxf"; "0k"; "0model"; "0modelc"; "0modelf"; "0regs"; "0regs'"; "IZ_to_bv"; "Ibv"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module PMHA11.
Import L5A. Import L5CA. Import L5SAR. Import PMHAS.
Abbreviation RSEGS := Asan.M.loaded_segments.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac hsc := first [ asm | apply UR | apply U_to | rk | gmem | (arith_goal; first [asm | alia]) | assumption ].
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section Stage.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.
Variables (M : word -> option byte) (model : Model) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z)) (R : bvmap 5 word)
(V2 cls F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr : credit) (W : list L5.range).
Hypothesis G : L5AFKR.gctx L ar HI LB FF LK A (V2 + cls) 36864 (V2 - 128) (V2 - 128) (V2 + cls) (tocell (V2 + cls)) (tfrk (V2 + cls) R) F fl 4 LK2 M2 model2 cr.
Hypothesis CLS : cls = 0 \/ cls = 16.
Hypothesis V2R : 140735332487360 <= V2 <= 140737488355328.
Hypothesis V2S : V2 + cls <= 140737488355328.
Hypothesis V2A : V2 mod 32 = 0.
Hypothesis GP : getr R (reg 3) = Z_to_bv 64 (pa_gp PMA.AD).
Hypothesis TP : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis FFRS : forall f, In f FF -> V2 + cls + 32 <= ff_rs f.
Hypothesis ROOM : forall LKc, incl LKc LK -> NoDup (map ff_addr ((F, 4, V2 - 128 + 32) :: FF ++ LKc)) -> PMSPA.ffroomA 11 ((F, 4, V2 - 128 + 32) :: FF) LKc.
Hypothesis STKSH : shadow_zero M (V2 + cls - 36864) 4608.
Hypothesis WAPP : PMKA.wapp W.
Hypothesis RA : L5.ra_ok (U R 1).
Hypothesis G2R : getr R (reg 2) = Z_to_bv 64 (V2 + cls).
Local Notation Bv := (L5AFKR.binv L ar HI M model LB FF LK A (V2 + cls) 36864 (V2 - 128) (tfrk (V2 + cls) R) F 4).
Local Notation FF' := ((F, 4, V2 - 128 + 32) :: FF).
Ltac hsolve := first [ exact LY | exact HIok | eassumption | exact (or_introl eq_refl) | (split; reflexivity) | apply incl_refl
| (apply PMHAK2.wapart_cons; [cbn [fst snd]; lia| first [apply PMHAK2.wapart_nil | (apply PMHAK2.wapart_cons; [cbn [fst snd]; lia| apply PMHAK2.wapart_nil])]])
| (apply PMHAK2.wapart_nil) | lia ].
#[using="Type"] Lemma kept_reg : ltac2:(TCodec.tc2 tcn__PmAHarness11 "Q9&Hy5'RMyR0%211%5241'6&Q3r3r2%3221'9&=(3%2215uQ0%4271%6231&<&R4&Q2%23?=1%411':&QHr5&RL&R9r4%211%42M1%7261r6%9213%;3N31p0=1p0C1p0K1pU>Q01pUHQ21pUFQ31").
Proof. intros regs regs' k.
intros H Hk NI. apply H.
- intros E. apply (f_equal bv_unsigned) in E. rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 5) with 32 in E.
rewrite Z.mod_small in E by lia. change (bv_unsigned (0%bv : bv 5)) with 0 in E. lia.
- unfold AX2.ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. rewrite Nat2Z.id. exact NI.
Qed.
Lemma tail_run : ltac2:(TCodec.tc2 tcn__PmAHarness11 "UK'QG&Hy5'RMyR0%211%5241'7y8%611%311p061&QEvNr2vR<vR@v?%6554321':&QHr3&RL&R9uE%211%42H1%7261+_oooooooooooH%72I1%;3I31r4uF%:11%<2Q01%?241%A3O17r5uG%@11%B2Q61%E241+QVPg0%E2Q71%I3Q731r6uJ%H11%J2Q>1%M241%O3Q=1E&QA&R2&R;+T0%22Q81&R5%12Q:Q9%5213%847>41&Q=r7+QU`P0+QV`P0%43321&Q?r8+QW[WH+QoooPP0%44A321&Q>r9+QW[X0+1%44F321r:+QVab8+QTc]@%=4J321&QFr;%23HR41&Q<r<+QP0%332R41r=%Q44Q31R63r>&R6+8%22R:1&Q7%Q5221%Q;4Q:61Q8r?+oH%Q92R@1vRB%Q24Q?421r@%QB4QA13L';'9'Q4&QIrFrE+do_0%RG2S91rD&QJ%11QL%8576431&QDu1%22S71%RO2SA1r1%>5S2S9217%@3R471&QM%12<4'>&R7z%2218&R8&R:+2+R0%3221%52>1%N271&<&QN+4%24SHQ71SK%411%SE2T7SF%S=11rG%113%SL3T531p061p0<1pTNG1&Q@%14S0NQBG&Q6%12T9T8u:%T111%T32TG1%T62T<1%T52TGN%T93TG21%QF271%QG2:1%QH2=1%QI2Q61%QJ2Q91qQFTG1%QM2TH1qR0TN1%QO2TO1qU:U61%R12U71p0R31p0R61p0R<1p0RD1p0RG1p0RL1p0S01p0S51p0S;1p0SA1p0SG1p0T11p0T81p0TA1p0TH1p0U51pQHU=1pR2UC1pU8UJ1").
Proof. intros fx Rc MV.
intros RI X21 X22 X23 X26 WSv IMGC CSB CUAR RMS OWNv FDEFv FWv FSHWv FLCv FLWv.
pose proof G as G'. destruct G' as [HkG SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
change (ff_bytes 4) with 1024 in *. change (1024 / 8) with 128 in *.
pose proof RI as (X2 & X8 & X9 & X18 & X19 & X20 & X24 & X25 & X3 & X4 & X27).
assert (Q1 : 4096 <= F <= 140737488354304) by (clear - FR; lia).
assert (Q2 : 4096 <= fl <= 140737488355327) by (clear - FLR; lia).
assert (Q3 : V2 - 128 + 144 <= F \/ F + 1024 <= V2 - 128) by (clear - FCEIL SLO CLS; lia).
assert (Q4 : V2 - 128 + 144 <= fl \/ fl + 1 <= V2 - 128) by (clear - FLR SLO CLS; lia).
assert (Q5 : L5.writable RSEGS MV (V2 - 128) 128) by (eapply L5.writable_sub; [exact WSv| clear; lia| clear - CLS; lia]).
unfold HeapIfaceA.SB in FSHWv.
pose proof (PMAHP4.haO_conc fx Rc MV (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl | 58%nat => U Rc 1 | _ => 0 end)) as P.
cbn beta iota in P.
feed P ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
| exact FDEFv | exact FWv | exact FSHWv | exact FLWv | exact Q5 | exact FLCv | (unfold PMAHP4.aligned; exact V2A) ]).
destruct P as (fx1 & R1 & M1v & MG1 & oFR & oFZ & (oMS & oKS & oR1 & oR10 & oR11 & oQ)).
assert (AG1 : forall i, 0 <= i < 2 ^ 64 -> ~ (F / 8 + 2147450884 <= i < F / 8 + 2147450884 + 3) -> ~ (F <= i < F + 8) -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
{ intros i Hi N1 N2. apply oFZ; [exact Hi| intros X0; apply N1; clear - X0; lia| intros X0; apply N2; clear - X0; lia]. }
assert (AGI1 : forall i, 65536 <= i < 6885376 -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
{ intros i Hi. apply AG1; [clear - Hi; lia| clear - Hi FR; lia| clear - Hi FR; lia]. }
assert (IMGC1 : L5.img_clear M1v 1228800 1261568) by (intros i Hi; rewrite AGI1 by (clear - Hi; lia); apply IMGC; exact Hi).
assert (CSB1 : L5.u64_at RSEGS M1v 1289464 2147450880) by (eapply L5C.u64_at_agree; [intros i Hi; apply AGI1; clear - Hi; lia| clear; lia| clear; lia| exact CSB]).
assert (CUAR1 : L5.u32_at RSEGS M1v 1289472 1) by (apply (PMHAK.u32_agree MV M1v 1289472 1); [intros i Hi; apply AGI1; clear - Hi; lia| clear; lia| clear; lia| exact CUAR]).
assert (RMS1 : L5.u64_at RSEGS M1v 1263176 1199536) by (eapply L5C.u64_at_agree; [intros i Hi; apply AGI1; clear - Hi; lia| clear; lia| clear; lia| exact RMS]).
pose proof (PMAHP4.haQt_conc fx1 R1 M1v (fun j => match j with 2%nat => V2 - 128 | _ => 0 end)) as P. cbn beta iota in P.
assert (R12' : getr R1 (reg 2) = Z_to_bv 64 (V2 - 128)) by (rewrite (oKS 2%nat) by inl; exact X2).
feed P ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | exact IMGC1 | exact CSB1 | exact CUAR1 | exact RMS1 ]).
destruct P as (fx2 & R2 & M2v & _ & tFR & _ & (tMS & tKS & tR6 & tR11 & tR12)).
assert (E2 : M2v = M1v) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply tFR). subst M2v.
set (sh := F / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 128 <= 17594333495296).
{ subst sh. clear - FR. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono F (2 ^ 47 - 1024) 8 ltac:(lia) ltac:(lia)). change ((2 ^ 47 - 1024) / 8) with 17592186044288 in H0. lia. }
assert (FSHW1 : L5.writable RSEGS M1v sh 128) by (eapply L5.writable_grows; [exact MG1| exact FSHWv]).
destruct (as0_fill_spec_memset fx2 M1v (Z_to_bv 64 sh) (Z_to_bv 64 245) 128 R2 (Z_to_bv 64 687624)) as (R3 & MS3 & KO3 & _).
{ clear; lia. }
{ rewrite L5.unsigned_lit by (clear - SHR; lia). clear - SHR; lia. }
{ pose proof (FSHW1 0 128%nat ltac:(clear; lia) ltac:(clear; lia)) as X0. rewrite Z.add_0_r in X0. exact X0. }
{ rewrite L5.unsigned_lit by (clear; lia). unfold AX2.two64. clear; lia. }
{ apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (clear; lia). reflexivity. }
{ rewrite L5K.rl1, (tKS 1%nat) by inl. exact oR1. }
{ rewrite L5K.rl10, (tKS 10%nat) by inl. exact oR10. }
{ rewrite L5K.rl11. exact tR11. }
{ rewrite L5K.rl12, tR12. exact oR11. }
set (M3v := wbytes M1v (Z_to_bv 64 sh) (repeat (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 245))) (Z.to_nat 128))) in *.
assert (MG3 : mem_grows M1v M3v) by (apply wbytes_grows).
assert (AG3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sh <= a < sh + 128) -> M3v (Z_to_bv 64 a) = M1v (Z_to_bv 64 a)).
{ intros a Ha Hn. subst M3v. apply AX2S.wbytes_out. rewrite repeat_length, L5.unsigned_lit by (clear - SHR; lia). clear - SHR; lia.
rewrite repeat_length, !L5.unsigned_lit by (clear - SHR Ha; lia). clear - Hn. lia. }
assert (KP3 : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (reg j) = getr R1 (reg j)).
{ intros j Hj. rewrite (kept_reg R2 R3 j KO3). apply tKS. revert Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat PMAHP4.KS_haQt). vm_compute; reflexivity.
cbn [In] in Hj; clear - Hj; lia. cbn [In] in Hj. unfold APC.caller_saved. cbn [In]. clear - Hj. lia. }
assert (AGS : forall a, V2 - 128 <= a < V2 + cls -> M3v (Z_to_bv 64 a) = MV (Z_to_bv 64 a)).
{ intros a Ha. rewrite AG3; [| clear - Ha V2R CLS; lia| clear - Ha SHR V2R CLS; lia]. apply AG1; [clear - Ha V2R CLS; lia| | ].
- subst sh. unfold HeapIfaceA.SB in *. clear - Ha SHR V2R CLS FR. lia.
- clear - Ha Q3 CLS. lia. }
assert (OWN3 : tfrk (V2 + cls) R M3v).
{ apply (tfrk_agree (V2 + cls) R MV M3v ltac:(clear - V2R CLS; lia) ltac:(clear - V2S; lia) OWNv). intros a Ha. unfold tocell in Ha. apply AGS. clear - Ha CLS. lia. }
destruct OWN3 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12).
assert (FDEF3 : L5.defined M3v F 1024) by (eapply L5.defined_grows; [exact MG3| eapply L5.defined_grows; [exact MG1| exact FDEFv]]).
assert (FW3 : L5.writable RSEGS M3v F 1024) by (eapply L5.writable_grows; [exact MG3| eapply L5.writable_grows; [exact MG1| exact FWv]]).
assert (FSHW3 : L5.writable RSEGS M3v sh 128) by (eapply L5.writable_grows; [exact MG3| exact FSHW1]).
assert (FLW3 : L5.writable RSEGS M3v fl 1) by (eapply L5.writable_grows; [exact MG3| eapply L5.writable_grows; [exact MG1| exact FLWv]]).
assert (FLC3 : L5.u64_at RSEGS M3v (F + 1016) fl).
{ eapply L5C.u64_at_agree; [| clear - FR; lia| clear - FR; lia| exact FLCv]. intros i Hi. rewrite AG3; [| clear - Hi FR; lia| clear - Hi FR FBIG SHR; subst sh; lia].
apply AG1; [clear - Hi FR; lia| subst sh; clear - Hi FR FBIG; lia| clear - Hi; lia]. }
assert (WS3 : L5.writable RSEGS M3v (V2 - 128) (V2 + cls - (V2 - 128))) by (eapply L5.writable_grows; [exact MG3| eapply L5.writable_grows; [exact MG1| exact WSv]]).
assert (RI3 : rinvH R R3 V2 cls F).
{ apply (rinvH_keep R R1 R3 V2 cls F); [apply (rinvH_ks R Rc R1 V2 cls F PMAHP4.KS_haO RI oKS); vm_compute; reflexivity|].
intros k Hk. apply KP3. unfold HIDX in Hk. cbn [In] in Hk |- *. clear - Hk. tauto. }
pose proof RI3 as (Y2 & Y8 & Y9 & Y18 & Y19 & Y20 & Y24 & Y25 & Y3 & Y4 & Y27).
assert (Y21 : getr R3 (reg 21) = Z_to_bv 64 18446744073709551608) by (rewrite (KP3 21%nat) by inl; rewrite (oKS 21%nat) by inl; exact X21).
assert (Y22 : getr R3 (reg 22) = Z_to_bv 64 18446744073709551608) by (rewrite (KP3 22%nat) by inl; rewrite (oKS 22%nat) by inl; exact X22).
assert (Y23 : getr R3 (reg 23) = Z_to_bv 64 1245920) by (rewrite (KP3 23%nat) by inl; rewrite (oKS 23%nat) by inl; exact X23).
assert (Y26 : getr R3 (reg 26) = Z_to_bv 64 18446744073709551608) by (rewrite (KP3 26%nat) by inl; rewrite (oKS 26%nat) by inl; exact X26).
assert (V0R : forall k, 0 <= U R k < 2 ^ 64) by (intros k; apply UR).
assert (Q5b : L5.writable RSEGS M3v (V2 - 128) 128) by (eapply L5.writable_sub; [exact WS3| clear; lia| clear - CLS; lia]).
assert (EPI : exists (fx9 : FPState) R9 M9v, msteps RSEGS (st fx2 R3 0xa7e08 M3v) (st fx9 R9 0xa7e54 M9v) /\ mem_grows M3v M9v
/\ (forall a, 0 <= a < 2 ^ 64 -> ~ (fl <= a < fl + 1) -> M9v (Z_to_bv 64 a) = M3v (Z_to_bv 64 a))
/\ L5.u8_at RSEGS M9v fl 0 /\ getr R9 (reg 1) = Z_to_bv 64 (U R 1) /\ getr R9 (reg 2) = Z_to_bv 64 (V2 + cls) /\ getr R9 (reg 10) = Z_to_bv 64 0
/\ (forall k, In k [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%nat -> getr R9 (reg k) = Z_to_bv 64 (U R k))
/\ (forall k, In k [3; 4; 27]%nat -> getr R9 (reg k) = getr R3 (reg k))).
{ destruct CLS as [E0|E0]; subst cls.
- rewrite Z.add_0_r in *.
pose proof (PMAHP4.haR0_conc fx2 R3 M3v (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl
| 42%nat => U R 1 | 43%nat => U R 8 | 44%nat => U R 9 | 45%nat => U R 18 | 46%nat => U R 19 | 47%nat => U R 20 | 48%nat => U R 21
| 49%nat => U R 22 | 50%nat => U R 23 | 51%nat => U R 24 | 52%nat => U R 25 | 53%nat => U R 26 | 58%nat => U R3 1 | _ => 0 end)) as P.
cbn beta iota in P.
feed P ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
| exact FDEF3 | exact FW3 | exact FSHW3 | exact FLW3 | exact Q5b | exact FLC3 | (unfold PMAHP4.aligned; exact V2A) ]).
destruct P as (fx9 & R9 & M9v & MG9 & eFR & eFZ & (eMS & eKS & eR1 & eR2 & eR8 & eR9 & eR10 & eR18 & eR19 & eR20 & eR21 & eR22 & eR23 & eR24 & eR25 & eR26 & eFL0)).
exists fx9, R9, M9v. split; [exact eMS|]. split; [exact MG9|]. split; [intros a Ha Hn; apply eFZ; [exact Ha| intros X0; apply Hn; clear - X0; lia]|].
split; [exact eFL0|]. split; [exact eR1|]. split; [exact eR2|]. split; [exact eR10|]. split.
+ intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [assumption|]). destruct Hk.
+ intros k Hk. apply eKS. revert k Hk. apply (L5K.incl_b [3; 4; 27]%nat PMAHP4.KS_haR0). vm_compute; reflexivity.
- pose proof (PMAHP4.haR16_conc fx2 R3 M3v (fun j => match j with 2%nat => V2 | 40%nat => F | 41%nat => fl
| 42%nat => U R 1 | 43%nat => U R 8 | 44%nat => U R 9 | 45%nat => U R 18 | 46%nat => U R 19 | 47%nat => U R 20 | 48%nat => U R 21
| 49%nat => U R 22 | 50%nat => U R 23 | 51%nat => U R 24 | 52%nat => U R 25 | 53%nat => U R 26 | 58%nat => U R3 1 | _ => 0 end)) as P.
cbn beta iota in P.
assert (W144 : L5.writable RSEGS M3v (V2 - 128) 144) by (eapply L5.writable_sub; [exact WS3| clear; lia| clear; lia]).
replace (V2 + 16 - 8) with (V2 + 8) in C1 by lia. replace (V2 + 16 - 16) with V2 in C2 by lia.
feed P ltac:(first [ asm | apply UR | apply U_to | (clear - V2R; lia) | (clear - V2R V2S; lia) | (clear - FR; lia) | (clear - FLR; lia) | exact F32
| exact FDEF3 | exact FW3 | exact FSHW3 | exact FLW3 | exact W144 | exact FLC3 | (unfold PMAHP4.aligned; exact V2A)
| (match goal with H : L5.u64_at RSEGS M3v ?a ?v |- L5.u64_at RSEGS M3v ?b ?v => replace b with a by lia; exact H end) ]).
destruct P as (fx9 & R9 & M9v & MG9 & eFR & eFZ & (eMS & eKS & eR1 & eR2 & eR8 & eR9 & eR10 & eR18 & eR19 & eR20 & eR21 & eR22 & eR23 & eR24 & eR25 & eR26 & eFL0)).
exists fx9, R9, M9v. split; [exact eMS|]. split; [exact MG9|]. split; [intros a Ha Hn; apply eFZ; [exact Ha| intros X0; apply Hn; clear - X0; lia]|].
split; [exact eFL0|]. split; [exact eR1|]. split; [exact eR2|]. split; [exact eR10|]. split.
+ intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [assumption|]). destruct Hk.
+ intros k Hk. apply eKS. revert k Hk. apply (L5K.incl_b [3; 4; 27]%nat PMAHP4.KS_haR16). vm_compute; reflexivity. }
destruct EPI as (fx9 & R9 & M9v & eMS & MG9 & eFZ & eFL0 & eR1 & eR2 & eR10 & eRS & eRK).
pose proof (ret_to fx9 R9 M9v 0xa7e54 (ltac:(oW' 0xa7e54%Z)) (U R 1) (ltac:(oF' 0xa7e54%Z)) eq_refl (ltac:(oD' 0xa7e54%Z)) eR1 (proj1 RA) (proj2 RA)) as RET.
exists fx9, R9, M9v. split. { eapply msteps_trans. exact oMS. eapply msteps_trans. exact tMS. eapply msteps_trans. exact MS3. eapply msteps_trans. exact eMS. exact RET. }
split. { eapply mem_grows_trans. exact MG1. eapply mem_grows_trans. exact MG3. exact MG9. }
split. { intros a Ha Hw. unfold L5AFKR.Wret in Hw. change (ff_bytes 4 / 8) with 128 in Hw. rewrite eFZ; [| exact Ha| clear - Hw; lia].
rewrite AG3; [| exact Ha| subst sh; unfold HeapIfaceA.SB in Hw; clear - Hw; lia]. apply AG1; [exact Ha| | clear - Hw; lia].
subst sh. unfold HeapIfaceA.SB in Hw. clear - Hw. lia. }
split. exact eFL0.
split; [| exact eR10].
apply preserved_by_index. intros j Hj. unfold cs_all in Hj. cbn [In] in Hj.
destruct Hj as [<-|Hj]. { rewrite eR2. symmetry. exact G2R. }
destruct Hj as [<-|Hj]. { rewrite (eRK 3%nat) by inl. exact Y3. }
destruct Hj as [<-|Hj]. { rewrite (eRK 4%nat) by inl. exact Y4. }
do 11 (destruct Hj as [<-|Hj]; [rewrite eRS by inl; symmetry; apply U_to|]).
destruct Hj as [<-|[]]. rewrite (eRK 27%nat) by inl. exact Y27.
Qed.
Lemma harness_tail : ltac2:(TCodec.tc2 tcn__PmAHarness11 "UH'QG&Hy5'RMyR0%211%5241'7y8%611%311p061'G'5'8'>%2211%411&Q8%611&Q5&QK&QOvCvR?vAvIvRGvDv@vEv0&R5vR<vR@%3221+QTP0&R;+T0%2261&QFvN%2271v?+4vR=r5r7r6r4r3r2%NFMLKJIHGFEA@=:987654321&QEr9%25>1FE<':&QHr:&RL&R9uE%211%42QM1%7261+_oooooooooooH%72QN1%;3QN31r;uF%:11%<2R51%?241%A3R417r<uG%@11%B2R;1%E241+QVPg0%E2R<1%I3R<31r=uJ%H11%J2RC1%M241%O3RB1EpUNRCR>&Q6%12QAQ8u:%Q011%Q22RK1%Q52Q=1z%Q52RL1%Q93RL31'9&R7r1%2261&R8&R:+2+R0%3221%5271%:271&<&QNvRB%24R51R4QM%411%QG2S>R0%R411rF%113%QN3S<31p061p0<1pTNS:1&R0%19S4S3RORNRHRGR>S1R=&Q9%12S2R?&R1rA%221R@&Q:&4rE%23SD1S8rDrCrBr8&Q;%11RK%:8SB7S>65431'QL&R2&QBvR3%211&QC&QDu1%22S;1%45RARK1RO=%:4961?p0<1p0H1p0L1p0O1p0Q21p0QK1p0R31pUDTB1pQLR71pR4TJ1pU<U11r@r?+do_0r>%E54321RD%K4JG1Op071p0RB1p0RI1p0S21p0S91p0SF1p0SJ1pQ6TJ1p4TO1pU4TM1pQ>TO1p6U21pUBU81pQJU:1pR2U@1pU8UG1").
Proof. intros fx Rc Mc modelc BX LKc crc Ac K.
intros BI RI X21 X22 X23 X26 KF.
destruct (L5AFKR.vis_facts L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W BX Mc modelc LKc crc Ac BI)
as ((WSv & IMGC & CSB & CUAR & RMS) & OWNv & (FDEFv & FWv & FSHWv & FLCv & FLWv) & _).
change (ff_bytes 4) with 1024 in *. change (1024 / 8) with 128 in *. replace (F + 1024 - 8) with (F + 1016) in FLCv by lia.
destruct (tail_run fx Rc _ RI X21 X22 X23 X26 WSv IMGC CSB CUAR RMS OWNv FDEFv FWv FSHWv FLCv FLWv) as (fx9 & R9 & M9v & MS9 & MG9 & FZ9 & FL9 & RP9 & A09).
apply (L5AFKR.retire_core L ar C HI LYa HIok M model LB FF LK A _ _ _ _ _ _ _ F fl 4 LK2 M2 model2 cr G W BX Mc modelc LKc crc Ac fx fx9 Rc 0xa7de0 R9 (U R 1) M9v K BI MS9 MG9 FZ9 FL9).
intros Mf modelf FRMf AHf RTf AMf HHf. apply (KF fx9 R9 Mf modelf RP9 A09 FRMf AHf RTf AMf HHf).
Qed.
End Stage.
End SCFG_1.
End PMHA11.
