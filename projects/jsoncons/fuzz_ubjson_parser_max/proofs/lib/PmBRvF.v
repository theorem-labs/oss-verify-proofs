(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0 LibIface AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0 L5CoreSpecsAB0 L5StepARB0 L5CoreBRB0 L5ADetailHRB0 PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAb PmModelFactsA PmStepAB0 PmStep PmParStep PmParKit PmBSrcKit PmBParKit PmBReset1 PmBUarK PmBUar PmBRvK PmBHarnessP4 PmBRdValP8 Jb0Sums AsanPlanCore AsanPlanSoundSums.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBRvF () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanCore.APC."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundSums.APSX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBRvK.PMBRVK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayout."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Ac"; "1O"; "1bool"; "1list"; "1nat"; "1option"; "1prod"; "1true"; "2and"; "2eq"; "2not"; "2or"; "3lt"; "4Z"; "0E"; "0HI"]; ["0L"; "0LKc"; "5Model"; "6bvmap"; "0M1v"; "0Mc"; "0R1"; "0Rc"; "7mrestrict"; "8caller_saved"; "9kept_ok"; ":msteps"; ";credit"; "<ahid"; "<fframe"; ">u8_at"]; ["=SCFG"; "?mid"; "?op"; "?rvc"; "?rve"; "?rvst"; "?vF"; "?vK"; "?vcat"; "?vs0"; "?vsm0"; "@pa_errcat_obj"; "AADDR_B"; "Binv"; "Bpst"; "Bstrm"]; ["Ccfg"; "Cprog_value"; "DFPState"; "Dgetr"; "Dmkst"; "Dseg_rom"; "Esrealizes"; "Fmem_grows"; "Gloaded_segments"; "0SCFG_P"; "HIn"; "Iadd"; "Idiv"; "Ile"; "Ilt"; "Iof_nat"]; ["Ipow"; "0X"; "0a"; "0ar"; "0c"; "0crc"; "0e"; "0fx"; "0fx1"; "0k"; "0m"; "0modelc"; "0pc"; "0regs"; "0regs'"; "0s"]; ["0sm"; "JZ_to_bv"; "Jbv"; "0v"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia.
Module PMBRVF.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Lemma kept_reg : ltac2:(TCodec.tc2 tcn__PmBRvF "Q9&Cy5'RByR0%211%5241'4&Jr3r2%3221'8&<(1%2215uQ0%4271%6231&:&QJ&I%23?=1%411'9&QCr5&RA&QOr4%211%42M1%7261r6%9213%;3N31p0=1p0C1p0K1pTDQ01pTNQ21pTLQ31").
Proof. intros regs regs' k.
intros H Hk NI. apply H.
- intros E. apply (f_equal bv_unsigned) in E. rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 5) with 32 in E.
rewrite Z.mod_small in E by lia. change (bv_unsigned (0%bv : bv 5)) with 0 in E. lia.
- unfold AX2.ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. rewrite Nat2Z.id. exact NI.
Qed.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithHeap.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMB.ly_as0 L C LY.
Lemma rv_fin : ltac2:(TCodec.tc2 tcn__PmBRvF "W='Q4'Q3vQIv@vR3v?r1%6554321'QB&Cy5'RByR0%211%5241'='5y8%711%311p071'B'3&N%211&L'6%12<<%611'Q>'Q?'2&Q5rCr@r>r=r<r;r:r9r8r7r6r5%=?Q:Q9Q8<;:987654321'K&QH&QDrBrA&RA%12Q8B&H&M%12ADr?%4221&QE%11<%<5;:831r4r3+_\d4%=2QD1r2%B554217%E3D71&QG%?2Q0=%A21Q4%3219'8&QMz%221R5&QN&R0+2+R0%3221%52R;1%:271&:&Q6rH%211%>21F&QK+8%2241%?2J1%D251%:11&QLrI%<11%3218+QoooPP0%;221%K21Q6%=22F%J2Q81%O231%E11&Q2rJ%211%D21C%Q421Q@+9%G241%Q42QC1%Q9241%O11'9%R12S8R8%R=11rE%R12R61rF%R43215%73S751p091p0D1p0Q01p0Q<1pT6S@1&OrG%I11%Q;21Q:%44RERH1RK';%C3SGRNQL+1%E3SIS01%4231&QC&QOu1%211%RK2T41%52S61+el^@%RN2T51%O3T531u:%911%S22T;1%<2S>1%R31Q=%QJ21QO%R121QG%S72T>1%Q83T>51u;%B11%S;2TD1%E2SH1%S=2TDRA%Q>3TD21&Q1rL%221SN%RL2NT3%RM2T4RG%RO221&Q;&Q<%211%QH3TLSC1%QI3TMT9S2(7%QK3T?SL1%S7231%S8251%S92:1%QO3U3T@S8&Q8rM%211%R33U7SN1%R43U8TDQ@&Q=%11TH&QA&Q9%118&Q:%11:%543TN1T>%SH271%SI2:1%SJ2<1%SK2A1%QO2C1'QF&Q0%11V5&Q@rK%26TKQ71S0S;SE&Q7rN%211%94TO741p0;1p0Q<1p0Q@1p0QG1p0R11p0R;1p0RA1p0RG1p0T@1p0TE1p0U<1pQ:V61pQ>V=1pTBVD1pTFV>1pT:V?1pU8V@1pT>V11pU2V31pU0V51p2V71pT<V;1pQ4V=1pTHVA1pQ<VC1pTJVI1pQ@VK1pT@W21pT4W41pNW<1").
Proof. intros E X fx Rc pc Mc modelc LKc crc Ac s sm e v c m fx1 R1 M1v.
intros ST MS1 MG1 FZ1 MO1 Hm R1ra R1a0 R1a1 MID1 OUT.
pose proof (PMBRVK.rvmem_of L ar C HI LY HIok E X _ _ _ _ _ _ _ _ _ _ _ ST) as MEM.
pose proof (PMBRVK.c_AR L ar HI E X) as AR.
pose proof X as [_ XG XHH XK0 XRra XRA XRsp XRgp XRtp XASTK XSTKSH XFRM XFRS XFOK XSP32 XINCS XUNR XCRED XINV XKONT].
destruct ST as (BI & MID & RPRE & STEP & EE & CK & EC).
destruct E as [R r sp fb cat s0 str sm0 e0 LBX FF LK Aw cr model M K F fl LK2 M2 model2].
unfold PMBRVK.rvmem, PMBRVK.rvar, PMBRVK.op, PMBRVK.oec, PMBRVK.ov, PMBRVK.mid, PMBRVK.WR, PMBRVK.SCR, PMBRVK.kont in *.
cbn [PMBRVK.vR PMBRVK.vr PMBRVK.vsp PMBRVK.vfb PMBRVK.vcat PMBRVK.vs0 PMBRVK.vstr PMBRVK.vsm0 PMBRVK.ve0 PMBRVK.vLBX PMBRVK.vFF PMBRVK.vLK
PMBRVK.vAw PMBRVK.vcr PMBRVK.vmodel PMBRVK.vM PMBRVK.vK PMBRVK.vF PMBRVK.vfl PMBRVK.vLK2 PMBRVK.vM2 PMBRVK.vmodel2] in *.
set (op := PMSPA.o_p PMB.AD fb) in *. set (ov := PMSPA.o_v PMB.AD fb) in *. set (oec := PMSPA.o_ec PMB.AD fb) in *. set (ois := PMSPA.o_is PMB.AD fb) in *.
destruct MEM as (IMG0 & CSB0 & CUAR0 & RMS0 & WS0 & Zop0 & Z320 & Z200 & OWR0 & Zoec0 & QWR0 & QU0 & FD0 & FW0 & FSW0 & FLC0 & FLW0 & OWN0).
destruct AR as ((ARsp1 & ARsp2) & (ARop1 & ARop2 & ARop3 & ARop4) & (ARq1 & ARq2 & ARq3 & ARq4 & ARq5)
& (ARF1 & ARF2 & ARF3 & ARF4 & ARF5 & ARF6 & ARF7 & ARF8 & ARF9 & ARF10 & ARF11 & ARF12 & ARF13 & ARF14 & ARF15 & ARF16)
& (ARv1 & ARv2 & ARv3 & ARv4 & ARv5 & ARv6 & ARv7 & ARv8 & ARv9 & ARv10)).
pose proof XG as G'. destruct G' as [GHk GSPT GSLO GSHI GSPC GOCR GOWNAG GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
set (MV := mrestrict (ahid Ac modelc) Mc) in *.
set (sh := F / 8 + 2147450880) in *.
assert (SHR : 2148296192 <= sh /\ sh + 64 <= 17594333495296).
{ subst sh. clear - ARF1. assert (F / 8 >= 845384) by (apply Z.le_ge; apply Z.div_le_lower_bound; lia).
assert (F / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; lia). lia. }
assert (AG1 : forall a, 0 <= a < 2 ^ 64 -> (a < F \/ F + 8 <= a) -> (a < sh \/ sh + 64 <= a) -> (a < op + 8 \/ op + 9 <= a) -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a)).
{ intros a Ha X1 X2 X3. apply FZ1; [exact Ha| clear - X1; lia| subst sh; clear - X2; lia| clear - X3; lia]. }
assert (AGI1 : forall i, 65536 <= i < 6893568 -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
{ intros i Hi. apply AG1; [clear - Hi; lia| clear - Hi ARF1; lia| clear - Hi SHR; lia| clear - Hi ARop1; lia]. }
assert (IMG1 : L5.img_clear M1v 65536 1269760) by (intros i Hi; rewrite AGI1 by (clear - Hi; lia); apply IMG0; exact Hi).
assert (IMGC1 : L5.img_clear M1v 1232896 1269760) by (intros i Hi; apply IMG1; clear - Hi; lia).
assert (CSB1 : L5.u64_at RSEGS M1v 1296952 2147450880) by (eapply L5C.u64_at_agree; [intros i Hi; apply AGI1; clear - Hi; lia| clear; lia| clear; lia| exact CSB0]).
assert (CUAR1 : L5.u32_at RSEGS M1v 1296960 1) by (apply (PMF.u32_at_agree RSEGS MV M1v); [intros i Hi; apply AGI1; clear - Hi; lia| clear; lia| clear; lia| exact CUAR0]).
assert (RMS1 : L5.u64_at RSEGS M1v 1270704 1207272) by (eapply L5C.u64_at_agree; [intros i Hi; apply AGI1; clear - Hi; lia| clear; lia| clear; lia| exact RMS0]).
pose proof MID1 as (Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q26 & Q27 & Q3 & Q4).
cfeed P (PMBHP4.haQt_conc fx1 R1 M1v (fun j => match j with 2%nat => sp - 128 | _ => 0 end)) ltac:(first [ assumption | (clear - ARsp1; lia) ]).
destruct P as (fx2 & R2 & M2v & _ & tFR & _ & (tMS & tKS & tR6 & tR11 & tR12)).
assert (E2 : M2v = M1v) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply tFR). subst M2v.
assert (FSHW1 : L5.writable RSEGS M1v sh 64) by (eapply L5.writable_grows; [exact MG1| exact FSW0]).
destruct (as0_fill_spec_memset fx2 M1v (Z_to_bv 64 sh) (Z_to_bv 64 245) 64 R2 (Z_to_bv 64 717264)) as (R3 & MS3 & KO3 & _).
{ clear; lia. }
{ rewrite L5.unsigned_lit by (clear - SHR; lia). clear - SHR; lia. }
{ pose proof (FSHW1 0 64%nat ltac:(clear; lia) ltac:(clear; lia)) as X0. rewrite Z.add_0_r in X0. exact X0. }
{ rewrite L5.unsigned_lit by (clear; lia). unfold AX2.two64. clear; lia. }
{ apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (clear; lia). reflexivity. }
{ rewrite L5K.rl1, (tKS 1%nat) by inl. exact R1ra. }
{ rewrite L5K.rl10, (tKS 10%nat) by inl. exact R1a0. }
{ rewrite L5K.rl11. exact tR11. }
{ rewrite L5K.rl12, tR12. exact R1a1. }
set (M3v := wbytes M1v (Z_to_bv 64 sh) (repeat (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 245))) (Z.to_nat 64))) in *.
assert (MG3 : mem_grows M1v M3v) by (apply wbytes_grows).
assert (AG3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sh <= a < sh + 64) -> M3v (Z_to_bv 64 a) = M1v (Z_to_bv 64 a)).
{ intros a Ha Hn. subst M3v. apply AX2S.wbytes_out. rewrite repeat_length, L5.unsigned_lit by (clear - SHR; lia). clear - SHR; lia.
rewrite repeat_length, !L5.unsigned_lit by (clear - SHR Ha; lia). clear - Hn. lia. }
assert (KP3 : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (reg j) = getr R1 (reg j)).
{ intros j Hj. rewrite (kept_reg R2 R3 j KO3). apply tKS. revert Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat PMBHP4.KS_haQt). vm_compute; reflexivity.
cbn [In] in Hj; clear - Hj; lia. cbn [In] in Hj. unfold APC.caller_saved. cbn [In]. clear - Hj. lia. }
assert (AGM3 : forall a, 0 <= a < 2 ^ 64 -> (a < F \/ F + 8 <= a) -> (a < sh \/ sh + 64 <= a) -> (a < op + 8 \/ op + 9 <= a) -> M3v (Z_to_bv 64 a) = MV (Z_to_bv 64 a)).
{ intros a Ha X1 X2 X3. rewrite AG3; [apply AG1; assumption| exact Ha| clear - X2; lia]. }
assert (MG13 : mem_grows MV M3v) by (intros x Hx; apply MG3; apply MG1; exact Hx).
assert (IMG3 : L5.img_clear M3v 65536 1269760) by (intros i Hi; rewrite AGM3 by (clear - Hi ARF1 SHR ARop1; lia); apply IMG0; exact Hi).
assert (CSB3 : L5.u64_at RSEGS M3v 1296952 2147450880) by (eapply L5C.u64_at_agree; [intros i Hi; apply AGM3; clear - Hi ARF1 SHR ARop1; lia| clear; lia| clear; lia| exact CSB0]).
assert (CUAR3 : L5.u32_at RSEGS M3v 1296960 1) by (apply (PMF.u32_at_agree RSEGS MV M3v); [intros i Hi; apply AGM3; clear - Hi ARF1 SHR ARop1; lia| clear; lia| clear; lia| exact CUAR0]).
assert (RMS3 : L5.u64_at RSEGS M3v 1270704 1207272) by (eapply L5C.u64_at_agree; [intros i Hi; apply AGM3; clear - Hi ARF1 SHR ARop1; lia| clear; lia| clear; lia| exact RMS0]).
assert (WS3 : L5.writable RSEGS M3v (sp - 128) 128) by (eapply L5.writable_grows; [exact MG13| exact WS0]).
assert (Zop3 : L5KA.zeros_at M3v ((op / 8) + 2147450880) 3) by (intros j Hj; rewrite AGM3 by (clear - Hj ARop1 ARop3 ARF1 ARF3 ARF11 SHR; subst sh; lia); apply Zop0; exact Hj).
assert (Z323 : L5KA.zeros_at M3v (((op + 32) / 8) + 2147450880) 44).
{ intros j Hj. assert ((op + 32) / 8 = op / 8 + 4) by (clear; replace (op + 32) with (4 * 8 + op) by lia; rewrite Z.div_add_l by lia; lia).
rewrite AGM3 by (clear - Hj ARop1 ARop3 ARF1 ARF3 ARF11 SHR H; subst sh; lia). apply Z320; exact Hj. }
assert (Z203 : L5KA.zeros_at M3v (((op + 20) / 8) + 2147450880) 1).
{ intros j Hj. assert ((op + 20) / 8 = op / 8 + 2) by (clear - ARop2; pose proof (Z.div_mod op 8 ltac:(lia)); pose proof (Z.mod_pos_bound op 8 ltac:(lia)); rewrite ARop2 in *; lia).
rewrite AGM3 by (clear - Hj ARop1 ARop3 ARF1 ARF3 ARF11 SHR H; subst sh; lia). apply Z200; exact Hj. }
assert (OWR3 : L5.writable RSEGS M3v op 384) by (eapply L5.writable_grows; [exact MG13| exact OWR0]).
assert (Zoec3 : L5KA.zeros_at M3v ((oec / 8) + 2147450880) 2) by (intros j Hj; rewrite AGM3 by (clear - Hj ARq1 ARq3 ARF1 ARF3 ARF14 ARop1 ARop3 SHR; subst sh; lia); apply Zoec0; exact Hj).
assert (QWR3 : L5.writable RSEGS M3v oec 16) by (eapply L5.writable_grows; [exact MG13| exact QWR0]).
assert (FD3 : L5.defined M3v F 512) by (eapply L5.defined_grows; [exact MG13| exact FD0]).
assert (FW3 : L5.writable RSEGS M3v F 512) by (eapply L5.writable_grows; [exact MG13| exact FW0]).
assert (FSW3 : L5.writable RSEGS M3v sh 64) by (eapply L5.writable_grows; [exact MG13| exact FSW0]).
assert (FLC3 : L5.u64_at RSEGS M3v (F + 504) fl) by (eapply L5C.u64_at_agree; [intros i Hi; apply AGM3; clear - Hi ARF1 ARF3 ARF9 SHR; subst sh; lia| clear - ARF1; lia| clear - ARF1; lia| exact FLC0]).
assert (FLW3 : L5.writable RSEGS M3v fl 1) by (eapply L5.writable_grows; [exact MG13| exact FLW0]).
assert (OWN3 : PMBRVK.own sp R M3v).
{ apply (PMBRVK.own_agree sp R MV M3v ltac:(clear - ARsp1; lia) ltac:(clear - ARsp1; lia) OWN0). intros a Ha. unfold PMBRVK.ocell in Ha.
apply AGM3; clear - Ha ARsp1 ARF1 ARF7 ARop1 ARop4 SHR; subst sh; lia. }
pose proof OWN3 as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96 & S104).
pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8.
pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18.
pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19. pose proof (bv_unsigned_in_range 64 (getr R (reg 20))) as B20.
pose proof (bv_unsigned_in_range 64 (getr R (reg 21))) as B21. pose proof (bv_unsigned_in_range 64 (getr R (reg 22))) as B22.
pose proof (bv_unsigned_in_range 64 (getr R (reg 23))) as B23. pose proof (bv_unsigned_in_range 64 (getr R (reg 24))) as B24.
pose proof (bv_unsigned_in_range 64 (getr R (reg 25))) as B25. pose proof (bv_unsigned_in_range 64 (getr R (reg 26))) as B26.
pose proof (bv_unsigned_in_range 64 (getr R (reg 27))) as B27. change (bv_modulus 64) with (2 ^ 64) in *.
assert (Y2 : getr R3 (reg 2) = Z_to_bv 64 (sp - 128)) by (rewrite KP3 by inl; exact Q2).
assert (Y8 : getr R3 (reg 8) = Z_to_bv 64 sp) by (rewrite KP3 by inl; exact Q8).
assert (Y9 : getr R3 (reg 9) = Z_to_bv 64 (sp - 128)) by (rewrite KP3 by inl; exact Q9).
assert (Y18 : getr R3 (reg 18) = Z_to_bv 64 sh) by (rewrite KP3 by inl; exact Q18).
assert (Y19 : getr R3 (reg 19) = Z_to_bv 64 F) by (rewrite KP3 by inl; exact Q19).
assert (Y20 : getr R3 (reg 20) = Z_to_bv 64 op) by (rewrite KP3 by inl; exact Q20).
assert (Y21 : getr R3 (reg 21) = Z_to_bv 64 oec) by (rewrite KP3 by inl; exact Q21).
assert (Y22 : getr R3 (reg 22) = Z_to_bv 64 ov) by (rewrite KP3 by inl; exact Q22).
assert (Y26 : getr R3 (reg 27) = Z_to_bv 64 2147450880) by (rewrite KP3 by inl; exact Q26).
assert (Y27 : getr R3 (reg 26) = Z_to_bv 64 F) by (rewrite KP3 by inl; exact Q27).
cfeed P (PMBRVP8.arvR2_conc fx2 R3 M3v (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl
| 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9))
| 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20))
| 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23))
| 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26))
| 76%nat => bv_unsigned (getr R (reg 27)) | _ => 0 end)) ltac:(first [assumption | unfold PMBRVP8.aligned; assumption | (clear - ARsp1; lia) | (clear - ARop1; lia) | (clear - ARq1; lia) | (clear - ARF1; lia) | (clear - ARF4; lia) | (clear - ARv1; lia) ]).
destruct P as (fx4 & R4 & M4v & MG4 & _ & FRZ4 & MS4 & KS4 & E1 & E2 & E8 & E9 & E10 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & FL0).
pose proof XRA as (Hr1 & Hr2).
assert (R4ra : getr R4 (reg 1) = Z_to_bv 64 r) by (rewrite E1, Z_to_bv_bv_unsigned; exact XRra).
pose proof (PMK.ret_to RSEGS fx4 R4 M4v 0xaf2b8 (ltac:(oW' 0xaf2b8%Z)) r (ltac:(oF' 0xaf2b8%Z)) eq_refl (ltac:(oD' 0xaf2b8%Z)) R4ra Hr1 Hr2) as MSr.
assert (MSall : msteps RSEGS (L5SAR.st fx Rc pc MV) (L5SAR.st fx4 R4 r M4v)).
{ eapply msteps_trans; [exact MS1|]. eapply msteps_trans; [exact tMS|]. eapply msteps_trans; [exact MS3|]. eapply msteps_trans; [exact MS4| exact MSr]. }
assert (MGall : mem_grows MV M4v) by (intros x Hx; apply MG4; apply MG13; exact Hx).
pose proof XFOK as ((rs & Hfb) & Fal).
assert (Eop : op = fb + 464) by reflexivity.
apply (PMBUK.retire_coreW L ar C HI LYa HIok M model LBX FF LK Aw sp 28672 (sp - 128) (sp - 104) sp (PMBRVK.ocell sp) (PMBRVK.own sp R) F fl 3 LK2 M2 model2 cr
(PM.parser_own s0) XG (PMSPA.W_run PMB.AD fb) (PM.parser_own s) Mc modelc LKc crc Ac (fun a => op + 8 <= a < op + 9) fx fx4 Rc pc R4 r M4v K BI).
{ intros a Xa. split.
- apply (L5SAR.fframe_client L ar (PM.parser_own s ++ LBX) ((F, 3, sp - 128 + 32) :: FF) 0 0 fb 4 rs); [right; exact Hfb| change (ff_bytes 4) with 1024; clear - Xa Eop; lia].
- intros O. apply (O (PMSPA.o_p PMB.AD fb + 8, 8)); [left; reflexivity| unfold L5.in_rng; fold op; cbn [fst snd]; clear - Xa; lia]. }
{ intros a. destruct (L5SAR.rng_dec a (op + 8) (op + 9)) as [Xa|Xa]; [left; exact Xa| right; exact Xa]. }
{ exact MSall. }
{ exact MGall. }
{ intros a Ha Nw. unfold PMBUK.WretX, PMBUK.Wret in Nw. change (ff_bytes 3) with 512 in Nw. change (512 / 8) with 64 in Nw.
rewrite FRZ4; [| exact Ha| intros Xa; apply Nw; left; right; clear - Xa; lia].
apply AGM3; [exact Ha| | subst sh; unfold SB in Nw; clear - Nw; lia| clear - Nw; lia].
destruct (Z_lt_le_dec a F) as [Y|Y]; [left; exact Y| right]. destruct (Z_lt_le_dec a (F + 8)) as [Z|Z]; [exfalso; apply Nw; left; left; left; clear - Y Z; lia| exact Z]. }
{ exact FL0. }
intros Mf modelf FZf MGf VISf AHf MRTf AMf HHf.
pose proof BI as (HHc & AMc & MRTc & INCAc & INCLc & ASTKc & EKc & DKc & OWNc & DEFc).
assert (EKf : L5SAR.ek L ar (PM.parser_own s ++ LBX) FF 0 0 [(op + 8, 1)] Mc Mf).
{ apply (PMBUAR.wret_ek L ar C HI LY HIok LBX FF LK Aw sp 28672 (sp - 128) (sp - 104) sp (PMBRVK.ocell sp) (PMBRVK.own sp R) F fl 3 LK2 M2 model2 cr (PM.parser_own s0)
(PM.parser_own s ++ LBX) LKc crc Ac Mc Mf _ [(op + 8, 1)] (fun a => op + 8 <= a < op + 9) XG HHc).
- intros a Xa O. apply (O (op + 8, 1)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Xa; lia].
- exact FZf. }
pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHf) as BRBf.
pose proof (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ XHH) as FRB.
pose proof RPRE as (PA & IA & VIS & VREF & BASE & ERR & TBOK).
pose proof (PMBRVK.frame_okA' (PMBRVK.RVE R r sp fb cat s0 str sm0 e0 LBX FF LK Aw cr model M K F fl LK2 M2 model2) XFOK) as FOK'.
cbn [PMBRVK.FF' PMBRVK.vF PMBRVK.vsp PMBRVK.vFF PMBRVK.vfb] in FOK'.
pose proof (PMBPAR.op_vis L ar C HI LY HIok _ _ LKc crc Ac Mc modelc fb _ s HHc FOK' PA) as ((O1 & O8 & ONSH) & _ & _ & _ & _ & _ & OVIS & AOP & _).
assert (AOF : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> PMSPA.aobjA FF a n).
{ intros a n Xa1 Xa2. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. clear - Xa1 Xa2; lia. }
assert (AOP0 : PMSPA.aobjA FF op 384) by (apply AOF; clear - Eop; lia).
assert (Eois : ois = fb + 96) by reflexivity. assert (Eov : ov = fb + 432) by reflexivity. assert (Eoec : oec = fb + 992) by reflexivity.
assert (MO0f : L5.u8_at RSEGS Mf (op + 8) m).
{ apply (proj1 (L5A.u8_at_vis (ahid Ac modelc) Mf (op + 8) m (OVIS (op + 8) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia))).
rewrite VISf. apply (L5C.u8_at_agree RSEGS M1v M4v); [| clear - O1; lia| clear - O1; lia| exact MO1].
intros i Hi. rewrite FRZ4; [| clear - Hi O1; lia| clear - Hi ARF10; lia]. rewrite AG3; [reflexivity| clear - Hi O1; lia| clear - Hi ARop3 SHR; subst sh; lia]. }
assert (OUT8 : forall a n, (a + n <= op + 8 \/ op + 9 <= a) -> forall i, a <= i < a + n -> L5.outside [(op + 8, 1)] i).
{ intros a n X3 i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hi Hr X3. lia. }
assert (OUTB8 : forall q n, In (q, n) (PM.parser_own s ++ LBX) -> forall i, q <= i < q + n -> L5.outside [(op + 8, 1)] i).
{ intros q n Hq i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr.
destruct (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q n op 384 HHc Hq (PMBUAR.aobjA_push FF op 384 _ AOP0)) as [Z|Z]; clear - Hi Hr Z; lia. }
assert (WAPP8 : PMKB.wapp [(op + 8, 1)]).
{ apply PMKB.wapp_cons; [| apply PMKB.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct ONSH as [Yn|Yn]; [right| left]; clear - Yn; lia. }
assert (Ivb : In (PM.p_b s, 32 * 2 ^ PM.p_k s) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.vec_own; right; left; reflexivity).
assert (Iqc : In (PM.sr_qc (PM.p_src s), PM.CHUNK) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
assert (EOWN : PM.parser_own (PMPK.set_more s m) = PM.parser_own s) by (destruct s; reflexivity).
assert (EC_f : forall v0 c0, PMSPA.ec_at RSEGS Mc oec v0 c0 -> PMSPA.ec_at RSEGS Mf oec v0 c0).
{ intros v0 c0 X0. apply (PMKB.ec_keepA RSEGS L ar _ FF 0 0 _ Mc Mf EKf WAPP8 FRB _ v0 c0 (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia))); [| exact X0].
apply OUT8. clear - Eop Eoec; lia. }
apply (XKONT fx4 R4 Mf modelf LKc Ac (PMPK.set_more s m) sm e crc).
- apply L5SAR.preserved_by_index. intros j Hj. pose proof Hj as Hj'. unfold L5SAR.cs_all in Hj.
repeat (destruct Hj as [<-|Hj]; [first [ rewrite E2; exact (eq_sym XRsp) | rewrite E8; apply Z_to_bv_bv_unsigned | rewrite E9; apply Z_to_bv_bv_unsigned
| rewrite E18; apply Z_to_bv_bv_unsigned | rewrite E19; apply Z_to_bv_bv_unsigned | rewrite E20; apply Z_to_bv_bv_unsigned
| rewrite E21; apply Z_to_bv_bv_unsigned | rewrite E22; apply Z_to_bv_bv_unsigned | rewrite E23; apply Z_to_bv_bv_unsigned
| rewrite E24; apply Z_to_bv_bv_unsigned | rewrite E25; apply Z_to_bv_bv_unsigned | rewrite E26; apply Z_to_bv_bv_unsigned
| rewrite E27; apply Z_to_bv_bv_unsigned
| (rewrite (KS4 _) by inl; rewrite (KP3 _) by inl; first [exact Q3 | exact Q4]) ] |]).
destruct Hj.
- unfold PMSPA.run_post, PMSPA.run_pre.
split; [split; [| split; [| split; [| split; [| split; [| split]]]]]|].
+ destruct (BRBf _ Iqc) as (Xq1 & Xq2). destruct (BRBf _ Ivb) as (Xb1 & Xb2). cbn [fst snd] in Xq1, Xq2, Xb1, Xb2.
apply (PMBPAR.parser_more_updA Mc Mf op ois s m PA).
* clear - O1; lia.
* clear - O1; lia.
* apply (PMKB.agA_obj L ar _ FF 0 0 _ Mc Mf EKf WAPP8 FRB op 8 (AOF op 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))).
apply OUT8. clear; lia.
* apply (PMKB.agA_obj L ar _ FF 0 0 _ Mc Mf EKf WAPP8 FRB (op + 9) 375 (AOF (op + 9) 375 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))).
apply OUT8. clear; lia.
* exact (PMKB.agsh_obj L ar _ FF 0 0 _ Mc Mf EKf WAPP8 FRB op 384 AOP0).
* pose proof PA as (_ & PD & _). apply (L5.defined_grows Mc Mf _ _ MGf PD).
* exact MO0f.
* exact Hm.
* exact Xq1.
* clear - Xq2; lia.
* apply (PMKB.agA_blk L ar _ FF 0 0 _ Mc Mf EKf WAPP8 BRBf _ _ Iqc). apply OUTB8. exact Iqc.
* exact Xb1.
* clear - Xb2; lia.
* apply (PMKB.agA_blk L ar _ FF 0 0 _ Mc Mf EKf WAPP8 BRBf _ _ Ivb). apply OUTB8. exact Ivb.
* intros c0 n0 p0 E0. assert (Ip : In (p0, c0) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.vs_own; rewrite E0; right; right; left; reflexivity).
apply (PMKB.agA_blk L ar _ FF 0 0 _ Mc Mf EKf WAPP8 BRBf _ _ Ip). apply OUTB8. exact Ip.
+ apply (PMKB.iss_keepA RSEGS PMB.AD L ar _ FF 0 0 _ Mc Mf EKf WAPP8 FRB BRBf ois str sm (AOF ois 272 ltac:(clear - Eois; lia) ltac:(clear - Eois; lia))); [| | | exact IA].
* apply incl_appr. exact XINCS.
* apply OUT8. clear - Eop Eois; lia.
* intros c0 n0 p0 E0. unfold PMKB.blk_out. apply (OUTB8 p0 c0). apply in_or_app; right. apply XINCS. rewrite E0. left; reflexivity.
+ apply (PMKB.visitor_keepA RSEGS PMB.AD L ar _ FF 0 0 _ Mc Mf EKf WAPP8 FRB _ (AOF ov 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia))); [| exact VIS].
apply OUT8. clear - Eop Eov; lia.
+ apply (PMKB.u64_keepA RSEGS L ar _ FF 0 0 _ Mc Mf EKf WAPP8 FRB (op + 384) _ (AOF (op + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [| exact VREF].
apply OUT8. clear; lia.
+ apply (PMBSK.base_keep L ar C LY _ FF 0 0 _ Mc Mf EKf); [| exact BASE]. intros a Ha rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Ha Hr O1; lia.
+ apply (PMKB.err_okA_keep RSEGS PMB.AD PMB.AAD L ar _ FF 0 0 _ Mc Mf EKf e PMB.addrs_wf_A); [| exact ERR].
intros a D. pose proof (PMBSK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
split; [exact (PMB.ly_static L C LY a D)|]. intros rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - DI Hr O1; lia.
+ unfold PMPK.set_more. cbn [PM.p_tb PM.p_tg]. exact TBOK.
+ split; [unfold PMPK.set_more; cbn [PM.p_src]; exact STEP|].
split; [exact EE|].
destruct OUT as [(Hv & Ec & Em & Ee)|(Hv & Ec & Em & INVs & PRG)].
* left. exists v. split; [exact Hv|]. split; [subst c; apply EC_f; exact EC|]. split; [unfold PMPK.set_more; cbn [PM.p_more]; exact Em| exact Ee].
* right. split; [subst v c; apply EC_f; exact EC|]. split.
-- subst m. destruct s as [mo dn dp src tb tg vb vk stk]. pose proof INVs as (IM & _). cbn [PM.p_more] in IM. subst mo. exact INVs.
-- unfold PMSPA.prog_value, PMSPA.push_rel in *. unfold PMPK.set_more. cbn [PM.p_stk PM.p_src]. exact PRG.
- exact AHf.
- unfold PMSPA.credit_keep in *. unfold PMPK.set_more, PM.pot_parser in *. cbn [PM.p_k PM.p_tb PM.p_tg] in *. exact CK.
- exact MRTf.
- exact INCLc.
- exact INCAc.
- exact AMf.
- rewrite EOWN. exact HHf.
Qed.
End WithHeap.
End SCFG_1.
End PMBRVF.
