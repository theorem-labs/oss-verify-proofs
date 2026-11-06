(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0 LibIface
AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0 L5CoreSpecsAB0 L5StepARB0 L5CoreBRB0 L5ADetailHRB0
PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAb
PmModelFactsA PmStepAB0 PmStep PmParStep PmParKit PmBSrcKit PmBParKit PmBReset1 PmBUarK PmBUar PmBSrcRead1 PmBRvK PmBRvC.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBRvG () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBRvK.PMBRVK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayout."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAb.PMB."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Ac"; "0Ac'"; "1app"; "1bool"; "1list"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3Z"; "0E"]; ["0HI"; "0L"; "0LK'"; "0LKc"; "4Model"; "5bvmap"; "0M'"; "0Mc"; "0R'"; "0RS"; "0Rc"; "6credit"; "6regs_preserved"; "7FS_BYTES"; "7SB"; "7aacc"]; ["7ar_fs"; "7ff_bytes"; "7fframe"; "9defined"; "9in_rng"; "9ra_ok"; "9range"; "8SCFG"; ":WR"; ":ocell"; ":op"; ":rvc"; ":rve"; ":rvst"; ":vF"; ":vK"]; [":vLBX"; ":vfb"; ":vsp"; ";pa_errcat_obj"; "<AADDR_B"; "<ADDR_B"; "=inv"; "=p_more"; "=p_stk"; "=parser_own"; "=pst"; "=pstate"; "=strm"; ">cfg"; ">run_spec_r"; ">run_spec_rd"]; ["?read_span_spec"; "@FPState"; "@getr"; "Asrealizes"; "Bloaded_segments"; "0SCFG_P"; "0SP"; "CIn"; "Dadd"; "Ddiv"; "Dle"; "Dlt"; "Dof_nat"; "Dpow"; "Dsub"; "0X"]; ["0a"; "0ar"; "0args"; "0c"; "0c'"; "0cr'"; "0crc"; "0e"; "0e'"; "0fx"; "0fx'"; "0h"; "0len"; "0m"; "0model'"; "0modelc"]; ["0n"; "0pc"; "0prog"; "0ptr"; "0q"; "0ra"; "0rr"; "0s"; "0s'"; "0sm"; "0sm'"; "EZ_to_bv"; "Ebv"; "0v'"]]).
Local Ltac lia := L5FastLia.plia.
Module PMBRVG.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithHeap.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMB.ly_as0 L C LY.
Lemma wr_rng : ltac2:(TCodec.tc2 tcn__PmBRvG "Q5'Q<&Q6'>&R7r2&Q8r3%211%53741&Q4%1246'='9&R:&R8&QAr5%211+Q0%5221%721>&R;+oH%9261%32B1%=251+V]lV0%>21E+VbSaD%82G1%B231%D261p0F1p0I1pU2Q01pV>Q21pQ0Q41").
Proof. intros E.
intros rr a Hin Hr. unfold PMBRVK.WR, PMSPA.W_run, PMSPA.W_srcf, PMSPA.err_W, PMSPA.o_src, PMSPA.o_is, PMSPA.o_tb, PMSPA.o_vec, PMSPA.o_ec, PMSPA.o_p in Hin.
cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMB.AD ADDR_B] in Hin. unfold L5.in_rng in Hr.
repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; clear - Hr; lia|]). destruct Hin.
Qed.
Lemma wr_apart : ltac2:(TCodec.tc2 tcn__PmBRvG "QE'Q<'Q;vR5vAvRAv@r1%6554321&Q6'>&R7r2&Q8r4%211%53741&Q4r3%2217'9&<&Q9&QBr6%211%4218%611&R:&R8&R9&Q>%118+8%4221&N%7221%921C&R;&Q1+3%211%<219%>271%62J1%I281%I11%K2D1p0M1p0Q11pU2Q81pV>Q:1pU0Q<1pQ0QD1").
Proof. intros E X.
intros rr a Hin Hr.
pose proof (PMBRVK.c_FOK L ar HI E X) as ((rs & Hfb) & Fal).
pose proof (PMBRVK.c_G L ar HI E X) as G'.
destruct G' as [GHk GSPT GSLO GSHI GSPC GOCR GOWNAG GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *. unfold PMBRVK.SCR in GSLO.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ (PMBRVK.c_HH L ar HI E X)) as (WB0 & WF0 & FSAPP & FSCEIL & _).
pose proof (WF0 _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 4) with 1024 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, F1, F2.
assert (DF1 : 0 <= PMBRVK.vF E / 8) by (apply Z.div_pos; clear - GFR; lia).
assert (DF2 : PMBRVK.vF E / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; clear - GFR; lia).
pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
unfold PMBRVK.ocell, SB.
destruct (wr_rng E rr a Hin Hr) as [Xa|Xa]; (split; [clear - Xa F1 F2 FSCEIL GSLO GSPT; lia|]).
- destruct FA1 as [Y|Y]; clear - Xa Y DF1 DF2 F1 F2; lia.
- clear - Xa DF1; lia.
Qed.
Lemma rd0_r : ltac2:(TCodec.tc2 tcn__PmBRvG "Q8'>&Ey5'S<yR0%211%5241'QJ!p021p0:1p051'QLp015p021p081p091p0;1&QOvR5&R4&QE&QDvAvRAv@r4r3zr2r1%=<<;:987654321&QNr5%2;?>=<;:91875p041pV6C1pU6J1pUHQ61pV4Q71").
Proof. intros pc h args prog.
unfold PMSPA.run_spec_rd, PMSPA.run_spec_r.
intros SP fx R M model K LBX FF LK Aw cr sp r fb cat s str sm e HH AM K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC UNR CRED KONT.
apply (SP fx R M model K LBX FF LK Aw cr sp r fb cat s str sm e HH AM K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS (proj1 (PM.inv_d0 s) INV) EC UNR CRED).
intros fx' R' M' model' LK' Aw' s' sm' e' cr' RP POST. apply (KONT fx' R' M' model' LK' Aw' s' sm' e' cr' RP).
unfold PMSPA.run_post_d in POST. unfold PMSPA.run_post. rewrite <- PM.inv_d0 in POST. exact POST.
Qed.
Lemma rv_run : ltac2:(TCodec.tc2 tcn__PmBRvG "UC'>&Ey5'S<yR0%211%5241'QJ!p021p0:1p051'QLp015p021p081p091p0;1&QNvR5&R4&QE&QDvAvRAv@r4r3r2r1%<;;:987654321'Q<'Q;%15>:984'R1'5y8%Q211%311p0Q21'D'4&Q2%211&K'7%12Q>Q>%611'3&Q=r>r;r:r9r8r7r6r5z%:?Q4Q3Q298765432Q1Q01O':&R2r<&S;&R<u1%211%42R11%7261%62R1Q9%:3R121&Q5%11Q='9&R:rE%22B1+7%4231%6231r?&QArB%211%9341O&QF%11Q2rQ0%Q7?R1R0QO1Q5Q4Q3Q2QMQ1Q0OQNQLQK&LrN%221M'=+1%D21R4+R0%F2R61%H231&QC%11R>%Q83S4R91&QG%11Q@%Q;3S71Q=(8%Q=3QIQA1%Q1231%Q2271%Q32;1%QA3S=RCQCrF%QC3S?RD1%K1QJrQ4r=rIrH%4532QO1QN%Q=261%Q>281%Q?2;1%M2=1'R3&Q7%11S9&QM%16S:Q>R<@<R0&Q?rQ3%211%84S>641p0:1p0Q91p0Q=1pU:T61pVLT71pU<RL1pUBRI1pVFSN1pVBT41p4RM1pQ6S21pUNS61pQ>S81pQBT:1pUFS?1rCrJrAr@%I6T24R4321%H1R<%N4T4L21p081p0R41p0R71p0R=1p0RE1p0RH1p0S41pV<U01pU8U11pU@SB1pVDTG1pV@TM1p2SF1pU>SJ1pQ8SL1pV0T01pQ@T21pQFU41pUDT91pU0T;1pQ0T>1pT>T@1pV6TN1pU6U51pUHUA1pV4UB1").
Proof. intros pc h args prog SP E X fx Rc Mc modelc LKc crc Ac s sm e c ra.
intros ST R1 RA Hh ARGS INV KC.
pose proof ST as (BI & MID & RPRE & STEP & EE & CK & EC).
pose proof BI as (HHc & AMc & _).
pose proof (PMBRVK.c_G L ar HI E X) as XG.
unfold PMSPA.run_spec_r in SP.
apply (SP fx Rc Mc modelc (PMBRVK.vK E) (PMBRVK.vLBX E) (PMBRVK.FF' E) LKc Ac crc (PMBRVK.vsp E - 128) ra (PMBRVK.vfb E) c s (PMBRVK.vstr E) sm e
HHc AMc (PMBRVK.c_K0 L ar HI E X)).
- exact (PMBRVC.rv_entryA L ar C HI HIok E X _ _ _ _ _ _ _ _ _ _ _ ra h ST R1 RA Hh).
- exact (PMBRVC.rv_room L ar C HI HIok E X _ _ _ _ _ _ _ _ _ _ _ h ST ltac:(lia)).
- exact (PMBRVC.rv_frs L ar HI E X).
- exact (PMBRVK.frame_okA' E (PMBRVK.c_FOK L ar HI E X)).
- pose proof (PMBRVK.c_SP32 L ar HI E X) as SP32. replace (PMBRVK.vsp E - 128) with (PMBRVK.vsp E + (-4) * 32) by lia. rewrite Z_mod_plus_full. exact SP32.
- exact ARGS.
- exact RPRE.
- exact (PMBRVK.c_INCS L ar HI E X).
- exact INV.
- exact EC.
- pose proof STEP as (_ & _ & _ & _ & U). pose proof (PMBRVK.c_UNR L ar HI E X) as U0. lia.
- exact (PMBPAR.credit_le_keepA _ _ _ _ (PMBRVK.c_CRED L ar HI E X) CK).
- intros fx' R' M' model' LK' Aw' s' sm' e' cr' RP' POST' HP' CK' MRT' INCLK' INCA' AM' HH'.
assert (BI' : PMBUK.binv L ar HI (PMBRVK.vM E) (PMBRVK.vmodel E) (PMBRVK.vLBX E) (PMBRVK.vFF E) (PMBRVK.vLK E) (PMBRVK.vAw E) (PMBRVK.vsp E) PMBRVK.SCR
(PMBRVK.vsp E - 128) (PMBRVK.own (PMBRVK.vsp E) (PMBRVK.vR E)) (PMBRVK.vF E) 3 (PMBRVK.WR E) (PM.parser_own s') M' model' LK' cr' Aw').
{ apply (PMBUK.binv_callee L ar C HI HIok (PMBRVK.vM E) (PMBRVK.vmodel E) (PMBRVK.vLBX E) (PMBRVK.vFF E) (PMBRVK.vLK E) (PMBRVK.vAw E) (PMBRVK.vsp E) PMBRVK.SCR
(PMBRVK.vsp E - 128) (PMBRVK.vsp E - 104) (PMBRVK.vsp E) (PMBRVK.ocell (PMBRVK.vsp E)) (PMBRVK.own (PMBRVK.vsp E) (PMBRVK.vR E)) (PMBRVK.vF E) (PMBRVK.vfl E) 3
(PMBRVK.vLK2 E) (PMBRVK.vM2 E) (PMBRVK.vmodel2 E) (PMBRVK.vcr E) (PM.parser_own (PMBRVK.vs0 E)) XG
(PMBRVK.WR E) (PMBRVK.WR E) (PM.parser_own s) [] (PM.parser_own s') Mc modelc LKc crc Ac M' model' LK' cr' Aw' (PMSPA.pm_scr h) (PMBRVK.WR E)
BI HP' HH' AM' MRT' INCA' INCLK');
[unfold PMSPA.pm_scr; lia| unfold PMSPA.pm_scr, PMBRVK.SCR; lia| exact (wr_apart E X)| intros a _ Y; exact Y| intros a Y; exact Y]. }
destruct POST' as (RPRE' & STEP' & EE' & ALT').
assert (MID' : PMBRVK.mid E R').
{ apply (PMBRVK.mid_keep E Rc R' MID); intros kk Hkk; apply (L5SAR.cs_of_preserved Rc R' kk RP'); revert kk Hkk; PMBRVK.kin. }
assert (STEP2 : PMSPA.src_step (PM.p_src (PMBRVK.vs0 E)) (PM.p_src s') (PMBRVK.vsm0 E) sm') by exact (PMBPAR.src_step_transA _ _ _ _ _ _ STEP STEP').
assert (CK2 : PMSPA.credit_keep (PMBRVK.vcr E) cr' (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) (PMBRVK.vs0 E))) (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s')))
by exact (PMBPAR.credit_keep_transA _ _ _ _ _ _ CK CK').
destruct ALT' as [(v' & Hv & EC' & MO' & E')|(EC' & INV' & PRG')].
+ apply (KC fx' R' M' model' LK' Aw' s' sm' e' cr' v' (pa_errcat_obj PMB.AD)); [| exact RP'| left; split; [exact Hv| split; [reflexivity| split; [exact MO'| exact E']]]].
split; [exact BI'|]. split; [exact MID'|]. split; [exact RPRE'|]. split; [exact STEP2|]. split; [intros H0; exact (EE' (EE H0))|]. split; [exact CK2| exact EC'].
+ apply (KC fx' R' M' model' LK' Aw' s' sm' e' cr' 0 c); [| exact RP'| right; split; [reflexivity| split; [reflexivity| split; [exact INV'| exact PRG']]]].
split; [exact BI'|]. split; [exact MID'|]. split; [exact RPRE'|]. split; [exact STEP2|]. split; [intros H0; exact (EE' (EE H0))|]. split; [exact CK2| exact EC'].
Qed.
Lemma rv_rspan : ltac2:(TCodec.tc2 tcn__PmBRvG "X7&R0vR5vAvRAv@%544321'Q<'Q;r1%2587651'R1&Ey5'S<yR0%211%5241'5y8%611%311p061'D'4&Q2%211&K'7'>%2211%711'QJ'QL'3&Q=r?r<r;r:r9r8r7r6r5r4zr3%=?Q=Q<Q;<;:987654321':&R2r=&S;&R<u1%211%42Q;1%7261%62Q;;%:3Q;21&Q5%11@u:%:11%<2QC1%?2M1&R8&Q:rB%211+H%5221%D2QI1%H3QI81r@u;%G11%I2R01%L241%K2R0Q3%O3R021rAu<%N11%Q02R71%Q3241rD%D11+Z@%G221%Q62R;1%Q:3R;61'9&R:%12Q@QD&R;&R=+2+R0%3221%52QJ1%9271rQ1rFrE%R6?S6S5S43R2R1R0QOQJQNQMQL2QK1&LrO%221R6%QK2R8Q=%QJ2ROR1%QN3RO21%QN2QMQ3%R03S113%E2R4R6rG%G2R81%I231+J%G2F1%I2R=1&Q3%13RFRAR@&O%13QBRDRC'=%R=3S1RFR@&Q0%11SL%Q421RJ%R02RKRJ&M%R2241%Q8231%Q:251';&R7(6r2%24S>S>1T2&2&QI%11S:&Q@rQ;%211%63SD41%;3SE81%QG2:S?%RC2S@S?%RD2<T=%QJ221%QL241%QM261qULSM1%D2SN1qV:SO1%F2T01%Q12H1%Q22Q11%R32SBSJ%S@3T4SKSC%R32SDSM%Q6221%S22SASO+Q?%R62R51%R:231%SG3T;SESJ&R>&QBrQ=%211+T0%5221r>%RC221%S?22SN+\P0%:251%RG231%QH251%QI2>1'QK%U011&QH%11SFrQ5%311%T<3531&QFrQ6%211%31S;p021'R3&R4&Q7%11V4&QMrJrIrQ3rH%5684321RI&Q?rQ@%211%=4<:41p0?1p0E1p0M1p0Q=1p0QB1p0QF1p0QH1p0RL1p0RO1p0S21p0S61p0S;1p0S>1p0SB1p0SF1pV2V31pV8V41pU<V71pVFV21pVBV41p4V61pQ6V<1pUNV@1pQ>VB1pQBVH1pUFVO1+fWP8rC%Q66Q9T5TG21U9%Q11SK%Q<4Q;Q921p061p0T<1p0TG1p0U31p0U;1p0UH1p0UK1p0V71pUJVK1pV<VL1pU8VM1pU@VI1pVDVK1pV@VM1p2VO1pU>W41pQ8W61pV0W:1pQ@W<1pQFWB1pUDWI1pU0WK1pQ0WO1pQDX11").
Proof. intros RS E X fx Rc Mc modelc LKc crc Ac s sm e c ra len.
intros ST R1 RA R10 R11 R12 Hlen KC.
pose proof ST as (BI & MID & RPRE & STEP & EE & CK & EC).
pose proof BI as (HHc & AMc & _).
pose proof RPRE as (PA & IA & VIS & VREF & BASE & ERR & TBOK).
pose proof (PMBRVK.c_AR L ar HI E X) as AR. unfold PMBRVK.rvar in AR. cbn zeta in AR.
destruct AR as ((ARsp1 & ARsp2) & (ARop1 & ARop2 & ARop3 & ARop4) & (ARq1 & ARq2 & ARq3 & ARq4 & ARq5) & _ & _).
pose proof (PMBRVK.c_FOK L ar HI E X) as ((rs & Hfb) & Fal).
assert (AOF : forall a n, PMBRVK.vfb E + 32 <= a -> a + n <= PMBRVK.vfb E + 1016 -> PMSPA.aobjA (PMBRVK.vFF E) a n).
{ intros a n Xa1 Xa2. exists (PMBRVK.vfb E, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. clear - Xa1 Xa2; lia. }
assert (Eoec : PMBRVK.oec E = PMBRVK.vfb E + 992) by reflexivity. assert (Eop : PMBRVK.op E = PMBRVK.vfb E + 464) by reflexivity.
assert (Eois : PMBRVK.ois E = PMBRVK.vfb E + 96) by reflexivity. assert (Eov : PMBRVK.ov E = PMBRVK.vfb E + 432) by reflexivity.
pose proof (PMBRVK.c_G L ar HI E X) as XG.
pose proof XG as G'. destruct G' as [GHk GSPT GSLO GSHI GSPC GOCR GOWNAG GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *. unfold PMBRVK.SCR in GSLO.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ (PMBRVK.c_HH L ar HI E X)) as (WB0 & WF0 & FSAPP & FSCEIL & _).
pose proof (WF0 _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 4) with 1024 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, F1, F2.
assert (HK : 0 <= PM.p_k s <= 11) by (destruct PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & Hk & _) & _); exact Hk).
assert (CR : PMSPA.credit_le (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s)) crc) by exact (PMBPAR.credit_le_keepA _ _ _ _ (PMBRVK.c_CRED L ar HI E X) CK).
unfold PMB.read_span_spec, PMSPA.read_span_spec in RS.
apply (RS fx Rc Mc modelc (PMBRVK.vK E) (PMBRVK.vLBX E) (PMBRVK.FF' E) LKc Ac crc (PMBRVK.vsp E - 128) ra (PMBRVK.vfb E) len s (PMBRVK.vstr E) sm
HHc AMc (PMBRVK.c_K0 L ar HI E X)).
- exact (PMBRVC.rv_entryA L ar C HI HIok E X _ _ _ _ _ _ _ _ _ _ _ ra 6 ST R1 RA ltac:(lia)).
- exact (PMBRVC.rv_room L ar C HI HIok E X _ _ _ _ _ _ _ _ _ _ _ 6 ST ltac:(lia)).
- exact (PMBRVC.rv_frs L ar HI E X).
- exact (PMBRVK.frame_okA' E (PMBRVK.c_FOK L ar HI E X)).
- pose proof (PMBRVK.c_SP32 L ar HI E X) as SP32. replace (PMBRVK.vsp E - 128) with (PMBRVK.vsp E + (-4) * 32) by lia. rewrite Z_mod_plus_full. exact SP32.
- rewrite L5K.rl10. unfold PMSPA.o_src. exact R10.
- rewrite L5K.rl11. exact R11.
- rewrite L5K.rl12. unfold PMSPA.o_tb. exact R12.
- exact Hlen.
- exact PA.
- exact IA.
- exact BASE.
- exact TBOK.
- exact (PMBRVK.c_INCS L ar HI E X).
- pose proof STEP as (_ & _ & _ & _ & U). pose proof (PMBRVK.c_UNR L ar HI E X) as U0. lia.
- exact (PMBPAR.pot_text_le_parserA L ar C LY s crc HK CR).
- intros fx' R' M' model' LK' Aw' s' sm' cr' ptr n RP' Rptr Rn Hn Hn26 LOC' DEF' ACC' PA' IA' TB' MO' DO' DP' B' K' STK' STEP' HP' CK' MRT' INCLK' INCA' AM' HH'.
change (PMSPA.pm_scr 6) with 24576 in HP'.
set (Wc6 := PMSPA.W_srcf PMB.AD (PMBRVK.vfb E) ++ [(PMSPA.o_tb PMB.AD (PMBRVK.vfb E), 24)]) in HP'.
assert (INW6 : forall rr, In rr Wc6 -> In rr (PMBRVK.WR E)).
{ intros rr Hin. unfold PMBRVK.WR, PMSPA.W_run. cbn [app]. unfold Wc6 in Hin. apply in_app_or in Hin. destruct Hin as [Hin|[<-|[]]].
+ right. apply in_or_app. left. exact Hin.
+ right. apply in_or_app. right. left. reflexivity. }
assert (Wc6R : forall rr a, In rr Wc6 -> L5.in_rng rr a -> PMBRVK.vfb E + 32 <= a < PMBRVK.vfb E + 1016).
{ intros rr a Hin Hr. unfold Wc6, PMSPA.W_srcf, PMSPA.o_src, PMSPA.o_is, PMSPA.o_tb, PMSPA.o_p in Hin. cbn [app pa_off_p pa_off_is PMB.AD ADDR_B] in Hin.
unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; clear - Hr; lia. }
assert (BI' : PMBUK.binv L ar HI (PMBRVK.vM E) (PMBRVK.vmodel E) (PMBRVK.vLBX E) (PMBRVK.vFF E) (PMBRVK.vLK E) (PMBRVK.vAw E) (PMBRVK.vsp E) PMBRVK.SCR
(PMBRVK.vsp E - 128) (PMBRVK.own (PMBRVK.vsp E) (PMBRVK.vR E)) (PMBRVK.vF E) 3 (PMBRVK.WR E) (PM.parser_own s') M' model' LK' cr' Aw').
{ apply (PMBUK.binv_callee L ar C HI HIok (PMBRVK.vM E) (PMBRVK.vmodel E) (PMBRVK.vLBX E) (PMBRVK.vFF E) (PMBRVK.vLK E) (PMBRVK.vAw E) (PMBRVK.vsp E) PMBRVK.SCR
(PMBRVK.vsp E - 128) (PMBRVK.vsp E - 104) (PMBRVK.vsp E) (PMBRVK.ocell (PMBRVK.vsp E)) (PMBRVK.own (PMBRVK.vsp E) (PMBRVK.vR E)) (PMBRVK.vF E) (PMBRVK.vfl E) 3
(PMBRVK.vLK2 E) (PMBRVK.vM2 E) (PMBRVK.vmodel2 E) (PMBRVK.vcr E) (PM.parser_own (PMBRVK.vs0 E)) XG
(PMBRVK.WR E) (PMBRVK.WR E) (PM.parser_own s) [] (PM.parser_own s') Mc modelc LKc crc Ac M' model' LK' cr' Aw' 24576 Wc6
BI HP' HH' AM' MRT' INCA' INCLK');
[clear; lia| unfold PMBRVK.SCR; clear; lia| | | intros a Y; exact Y].
- intros rr a Hin Hr. exact (wr_apart E X rr a (INW6 rr Hin) Hr).
- intros a Hc Ho rr Hin Hr. exact (Ho rr (INW6 rr Hin) Hr). }
pose proof (L5SAR.ek_callee L ar (PMBRVK.vLBX E) [] (PMBRVK.vFF E) [(PMBRVK.vF E, 3, PMBRVK.vsp E - 128 + 32)] (PMBRVK.vsp E) 28672 (PMBRVK.vsp E - 128) 24576 Wc6 Wc6 Mc M' HP'
ltac:(clear; lia) ltac:(clear; lia) (fun a _ X0 => X0)) as EK46.
assert (WAPP6 : PMKB.wapp Wc6) by (intros rr Hin; apply (PMBRVC.wapp_WR L ar C HI HIok E X); apply INW6; exact Hin).
pose proof (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ (PMBRVK.c_HH L ar HI E X)) as FRB.
assert (OUTc6 : forall a n0, PMBRVK.vfb E + 32 <= a -> a + n0 <= PMBRVK.vfb E + 1016 -> (a + n0 <= PMBRVK.op E + 280 \/ PMBRVK.op E + 320 <= a)
-> (a + n0 <= PMBRVK.ois E + 40 \/ PMBRVK.ois E + 48 <= a) -> (a + n0 <= PMBRVK.ois E + 152 \/ PMBRVK.ois E + 156 <= a)
-> (a + n0 <= PMBRVK.op E + 336 \/ PMBRVK.op E + 360 <= a) -> forall i, a <= i < a + n0 -> L5.outside Wc6 i).
{ intros a n0 X1 X2 X3 X4 X5 X6 i Hi rr Hin Hr. unfold Wc6, PMSPA.W_srcf, PMSPA.o_src, PMSPA.o_is, PMSPA.o_tb, PMSPA.o_p in Hin. cbn [app pa_off_p pa_off_is PMB.AD ADDR_B] in Hin.
unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; clear - Hr Hi X3 X4 X5 X6 Eop Eois; lia. }
assert (FB0 : 6893568 <= PMBRVK.vfb E) by (clear - ARop1 Eop Fal; lia).
assert (VIS' : PMSPA.visitor_at RSEGS PMB.AD M' (PMBRVK.ov E)).
{ apply (PMKB.visitor_keepA RSEGS PMB.AD L ar (PMBRVK.vLBX E) (PMBRVK.vFF E) (PMBRVK.vsp E) 28672 Wc6 Mc M' EK46 WAPP6 FRB _ (AOF (PMBRVK.ov E) 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia))); [| exact VIS].
apply OUTc6; clear - Eov Eop Eois; lia. }
assert (VREF' : L5.u64_at RSEGS M' (PMBRVK.op E + 384) (PMBRVK.ov E)).
{ apply (PMKB.u64_keepA RSEGS L ar (PMBRVK.vLBX E) (PMBRVK.vFF E) (PMBRVK.vsp E) 28672 Wc6 Mc M' EK46 WAPP6 FRB (PMBRVK.op E + 384) _ (AOF (PMBRVK.op E + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [| exact VREF].
apply OUTc6; clear - Eop Eois; lia. }
assert (EC' : PMSPA.ec_at RSEGS M' (PMBRVK.oec E) 0 c).
{ apply (PMKB.ec_keepA RSEGS L ar (PMBRVK.vLBX E) (PMBRVK.vFF E) (PMBRVK.vsp E) 28672 Wc6 Mc M' EK46 WAPP6 FRB _ 0 c (AOF (PMBRVK.oec E) 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia))); [| exact EC].
apply OUTc6; clear - Eoec Eop Eois; lia. }
assert (BASE' : PMSTA.base_okA RSEGS PMB.AD M').
{ apply (PMBSK.base_keep L ar C LY (PMBRVK.vLBX E) (PMBRVK.vFF E) (PMBRVK.vsp E) 28672 Wc6 Mc M' EK46); [| exact BASE].
intros a Ha rr Hin Hr. pose proof (Wc6R rr a Hin Hr) as Y. clear - Ha Y FB0; lia. }
assert (ERR' : PMSTA.err_okA RSEGS PMB.AD PMB.AAD M' e).
{ apply (PMKB.err_okA_keep RSEGS PMB.AD PMB.AAD L ar (PMBRVK.vLBX E) (PMBRVK.vFF E) (PMBRVK.vsp E) 28672 Wc6 Mc M' EK46 e PMB.addrs_wf_A); [| exact ERR].
intros a D. pose proof (PMBSK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
split; [exact (PMB.ly_static L C LY a D)|]. intros rr Hin Hr. pose proof (Wc6R rr a Hin Hr) as Y. clear - DI Y FB0; lia. }
rewrite L5K.rl10 in Rptr. rewrite L5K.rl11 in Rn.
assert (PLOC : (ptr = 0 /\ n = 0) \/ (exists q m, In (q, m) (PM.parser_own s' ++ PMBRVK.vLBX E) /\ q <= ptr /\ ptr + n <= q + m /\ 4096 <= ptr /\ ptr + n <= ahl_ceil ar)
\/ (ar_fs ar <= ptr /\ ptr + n <= ar_fs ar + 11571200 /\ 4096 <= ptr)).
{ destruct LOC' as [Y|[(Bq & mq & Hin & X1 & X2)|(X1 & X2)]]; [left; exact Y| right; left| right; right].
- pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH') as (WB6 & _).
destruct (WB6 (Bq, mq) (in_or_app _ _ _ (or_introl Hin))) as ((Yb1 & _ & _ & _ & Yb5 & _) & _). cbn [fst snd] in Yb1, Yb5.
exists Bq, mq. split; [apply in_or_app; left; exact Hin|]. split; [exact X1|]. split; [exact X2|]. clear - X1 X2 Yb1 Yb5; lia.
- unfold PMSPA.o_tb in X1, X2. fold (PMBRVK.op E) in X1, X2. clear - X1 X2 F1 F2 Eop FB0; lia. }
assert (CEIL : ahl_ceil ar + 32768 <= PMBRVK.vsp E) by (clear - GSLO; lia).
apply (KC fx' R' M' model' LK' Aw' s' sm' cr' ptr n); [| exact RP'| exact Rptr| exact Rn| exact Hn| exact Hn26| exact DEF'| exact ACC'| | | | | | exact STK'|].
+ split; [exact BI'|].
split; [apply (PMBRVK.mid_keep E Rc R' MID); intros kk Hkk; apply (L5SAR.cs_of_preserved Rc R' kk RP'); revert kk Hkk; PMBRVK.kin|].
split; [split; [exact PA'|]; split; [exact IA'|]; split; [exact VIS'|]; split; [exact VREF'|]; split; [exact BASE'|]; split; [exact ERR'| exact TB']|].
split; [exact (PMBPAR.src_step_transA _ _ _ _ _ _ STEP STEP')|].
split; [exact EE|].
split; [exact (PMBPAR.credit_keep_transA _ _ _ _ _ _ CK (PMBPAR.credit_keep_textA L ar C LY s s' crc cr' CK' K'))| exact EC'].
+ destruct PLOC as [(_ & Y)|[(q & m & Hin & Y1 & Y2 & _)|(Y1 & Y2 & _)]]; [left; exact Y| right; right; exists q, m; split; [exact Hin| split; [exact Y1| exact Y2]]| right; left; unfold FS_BYTES; split; [exact Y1| exact Y2]].
+ destruct PLOC as [(Y & _)|[(q & m & _ & _ & _ & Y & _)|(_ & _ & Y)]]; clear - Y; lia.
+ destruct PLOC as [(_ & Y)|[(q & m & _ & _ & _ & Y & _)|(_ & _ & Y)]]; [left; exact Y| right; clear - Y; lia| right; clear - Y; lia].
+ destruct PLOC as [(Y1 & Y2)|[(q & m & _ & _ & _ & _ & Y)|(_ & Y & _)]]; [subst; clear - GSPT; lia| clear - Y CEIL GSHI GSPT; lia| clear - Y FSCEIL CEIL GSHI GSPT; lia].
+ destruct PLOC as [(_ & Y)|[(q & m & _ & _ & _ & _ & Y)|(_ & Y & _)]]; [left; exact Y| right; right; clear - Y CEIL; lia| right; right; clear - Y FSCEIL CEIL; lia].
+ intros (IM & ID & IDP & ISH & ITB). split; [rewrite MO'; exact IM|]. split; [rewrite DO'; exact ID|]. split; [rewrite DP', STK'; exact IDP|].
split; [rewrite STK'; exact ISH| exact TB'].
Qed.
End WithHeap.
End SCFG_1.
End PMBRVG.
