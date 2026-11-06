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
PmModelFactsA PmStepA PmStep PmParStep PmParKit PmASrcKit PmAParKit PmAReset1 PmAUarK PmAUar PmASrcRead1 PmARvK.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmARvC () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmARvK.PMARVK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayout."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAa.PMA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStepA.PMKA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Ac"; "0Ac'"; "1app"; "1bool"; "1list"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "2ex"; "2or"; "3Z"; "0E"; "0Fv"]; ["0HI"; "0L"; "0LK'"; "0LKc"; "4Model"; "5bvmap"; "0M"; "0M'"; "0MKE"; "0Mc"; "0R'"; "0R1"; "0Rc"; "6mrestrict"; "7msteps"; "8credit"]; ["8regs_preserved"; "9FS_BYTES"; "9aacc"; "9ahid"; "9ar_fs"; "9fframe"; "9shadow_zero"; ";defined"; ";ra_ok"; ";u8_at"; ":SCFG"; "<FF'"; "<WR"; "<mid"; "<oec"; "<op"]; ["<rvc"; "<rve"; "<rvst"; "<vF"; "<vK"; "<vLBX"; "<vfb"; "<vsp"; "=pa_errcat_obj"; ">ADDR_A"; "?parser_own"; "?pst"; "?srcst"; "?strm"; "@cfg"; "@entryA"]; ["@ffroomA"; "@ffrsA"; "@scan_spec"; "@with_src"; "Amake_ec_spec"; "Asrc_read_spec"; "Bwapp"; "CFPState"; "Cgetr"; "Cmkst"; "Cseg_rom"; "Dsrealizes"; "Eloaded_segments"; "0SC"; "0SCFG_P"; "0SR"]; ["FIn"; "Gadd"; "Gdiv"; "Gle"; "Glt"; "Gmodulo"; "Gmul"; "Gof_nat"; "Gpow"; "Gsub"; "0X"; "0a"; "0ar"; "0c"; "0c0"; "0crc"]; ["0d"; "0e"; "0fx"; "0fx'"; "0fx1"; "0g"; "0h"; "0j"; "0k"; "0lo"; "0m"; "0model'"; "0model1"; "0modelc"; "0n"; "0p"]; ["0pc"; "0pc1"; "0pcs"; "0q"; "0ra"; "0s"; "0sa"; "0sm"; "0sm'"; "0src'"; "HZ_to_bv"; "Hbv"; "0v"; "0v0"; "0vb"; "0w"]]).
Local Ltac lia := L5FastLia.plia.
Module PMARVC.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithHeap.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.
Lemma wapp_WR : ltac2:(TCodec.tc2 tcn__PmARvC "?'QA'Q@vR>vAvRLv@r1%6554321&R6&Q<r2%211%411pUF61pN>1").
Proof. intros E X.
pose proof (PMARVK.c_FOK L ar HI E X) as ((rs & Hfb) & Fal).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ (PMARVK.c_HH L ar HI E X)) as (WB & WF & FSAPP & FSCEIL & _).
pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 4) with 1024 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, F1, F2.
unfold PMARVK.WR, PMSPA.W_run, PMSPA.W_srcf, PMSPA.err_W, PMSPA.o_src, PMSPA.o_is, PMSPA.o_tb, PMSPA.o_vec, PMSPA.o_ec, PMSPA.o_p.
cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMA.AD ADDR_A].
pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
repeat apply PMKA.wapp_cons; [..| apply PMKA.wapp_nil]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia.
Qed.
Lemma rv_stksh : ltac2:(TCodec.tc2 tcn__PmARvC "RH'QA'Q@vR>vAvRLv@r1%6554321&Ey5'SKyR0%211%5241'5y8%611%311p061'D'4&Q5%211&O'7'=%2211%711'QK'QM'3&QBr=r;r:r9r8r7r6r5r4r3r2%<?Q8Q7Q6;:987654321Q5&RC&RI&QGr@%211+lP0%5221%7219&RA&RF+8%221=%42?1rA%<11%?231':&RE%12F8z%43Q721%E22I&Q6%13:MLp031p051p0;1p0D1pV<Q?1pVDQ@1p0O1pULQB1pWJQC1pV4Q?1pW@QA1pW<QC1p2QE1pV0QJ1pQ8QL1pVLR01pQDR21pQJR81pUFR?1pNRG1").
Proof. intros E X Rc Mc modelc LKc crc Ac s sm e v c.
intros ST lo g H1 H2 H3 H4. pose proof ST as (BI & _). pose proof BI as (_ & _ & _ & _ & _ & _ & EKc & _).
pose proof (PMARVK.c_ASTK L ar HI E X) as (A16 & SLO & SHI & SPT & _). pose proof (PMARVK.c_STKSH L ar HI E X) as STKSH.
unfold PMARVK.SCR in *. change (28672 / 8) with 3584 in STKSH.
apply (PMKA.stksh_keepA L ar _ _ _ _ _ _ _ EKc (wapp_WR E X) lo g); [lia| lia| lia| exact H3| exact H4|].
apply (PMKA.shadow_zero_sub _ (PMARVK.vsp E - 28672) 3584); [| exact H3| exact H1| lia| exact H4| exact STKSH].
apply PMKA.mod16_8'. replace (PMARVK.vsp E - 28672) with (PMARVK.vsp E + (-1792) * 16) by lia. rewrite Z_mod_plus_full. exact A16.
Qed.
Lemma rv_entryA : ltac2:(TCodec.tc2 tcn__PmARvC "RO'QA'Q@vR>vAvRLv@r1%6554321&Ey5'SKyR0%211%5241'5y8%611%311p061'D'4&Q5%211&O'7'=%2211%711'QK'QM'3&QBr?r=r<r;r:r9r8r7r6r5r4r3%=?Q9Q8Q7<;:987654321':&R8r>&SJ&RGu1%211%42Q;1%7261%62Q;;%:3Q;21&Q8%11?'9&RCz%221C+7%42E1%6231&QO&QIrAr@&RI&QGrC%211+T0%5221%:89R8R7871Q3Q2p0<1p0D1p0G1p0Q31pV>QG1pW:QH1pULQI1pWJQJ1pV4QF1pW@QH1pW<QJ1p2QL1pV0R11pQ8R31pVLR71pQDR91pQJR?1pUFRF1pNRN1").
Proof. intros E X Rc Mc modelc LKc crc Ac s sm e v c ra h.
intros ST R1 RA Hh. pose proof ST as (BI & MID & _). pose proof BI as (_ & _ & _ & _ & _ & ASTKc & _).
pose proof MID as (X2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & X3 & X4).
pose proof (PMARVK.c_ASTK L ar HI E X) as (A16 & SLO & SHI & SPT & _).
unfold PMARVK.SCR in ASTKc.
split; [rewrite L5K.rl1; exact R1|]. split; [exact RA|]. split; [rewrite L5K.rl2; exact X2|].
split; [rewrite L5K.rl3; rewrite X3; rewrite <- L5K.rl3; exact (PMARVK.c_Rgp L ar HI E X)|].
split; [rewrite L5K.rl4; rewrite X4; rewrite <- L5K.rl4; exact (PMARVK.c_Rtp L ar HI E X)|].
unfold PMSPA.pm_scr.
split; [apply (L5SAR.astk_sub ar Mc Mc (PMARVK.vsp E) 28672 128 (12288 + 2048 * h) ASTKc (mem_grows_refl Mc)); [lia| lia| lia|];
replace (PMARVK.vsp E - 128) with (PMARVK.vsp E + (-8) * 16) by lia; rewrite Z_mod_plus_full; exact A16|].
assert (G8 : (12288 + 2048 * h) / 8 = 1536 + 256 * h) by (replace (12288 + 2048 * h) with ((1536 + 256 * h) * 8) by lia; apply Z.div_mul; lia).
rewrite G8. apply (rv_stksh E X _ _ _ _ _ _ _ _ _ _ _ ST); [lia| lia| | lia].
apply PMKA.mod16_8'. replace (PMARVK.vsp E - 128 - (12288 + 2048 * h)) with (PMARVK.vsp E + (-776 - 128 * h) * 16) by lia. rewrite Z_mod_plus_full. exact A16.
Qed.
Lemma rv_room : ltac2:(TCodec.tc2 tcn__PmARvC "R5'QA'Q@vR>vAvRLv@r1%6554321&Ey5'SKyR0%211%5241'5y8%611%311p061'D'4&Q5%211&O'7'=%2211%711'QK'QM'3&QBr>r<r;r:r9r8r7r6r5r4r3r2%=?Q9Q8Q7<;:987654321&RC+7%2241&R0&Q;r@%211%43:1Bp061p0:1pV>N1pULO1pWJQ01pV4L1pW@N1pW<Q01p2Q21pV0Q71pQ8Q91pVLQ=1pQDQ?1pQJQE1pUFQL1pNR41").
Proof. intros E X Rc Mc modelc LKc crc Ac s sm e v c h.
intros ST Hh. pose proof ST as (BI & _). pose proof BI as (HHc & _ & _ & _ & INCLc & _).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDF & _).
apply (PMAUAR.ffroomA_push 8 h (PMARVK.vFF E) (PMARVK.vLK E) LKc _ (PMARVK.c_FRM L ar HI E X) INCLc); [exact NDF| lia].
Qed.
Lemma rv_frs : ltac2:(TCodec.tc2 tcn__PmARvC "D'QA'Q@vR>vAvRLv@r1%6554321&R1&Q;r2%211&RI&QG%114+T0%4221%9261pUF;1pNC1").
Proof. intros E X. apply (PMAUAR.ffrsA_push (PMARVK.vFF E) (PMARVK.vsp E) (PMARVK.vsp E - 128) (PMARVK.vF E) 3 (PMARVK.vsp E - 128 + 32) (PMARVK.c_FRS L ar HI E X)); lia. Qed.
Lemma rv_ro : ltac2:(TCodec.tc2 tcn__PmARvC "SB'QA'Q@vR>vAvRLv@r1%6554321'R7&Ey5'SKyR0%211%5241'='5y8%711%311p071'D'4&Q5%211&O'7%12<<%611'QK'QM'3&QBrBr?r=r<r;r:r9r8r7r6r5r4%=?Q:Q9Q8<;:987654321'N&R<&R9rAr@&SJ%12Q8B&M&Q3%12ADr>%4221&R:%11<%<5;:831r3r2%<2QC1%@5D3175%C3B51&Q=rD%221HrF%Q6?R3R2R11LER0Q4>Q3Q2Q1Q0ON':p0QKQ9%C2A;%D2BI%43321'R;&Q:%11R<&QNrC%26Q2Q:Q9Q81D&QDrH%211%94Q6741p0;1p0A1pVJR31%:6Q:F9QHQ8Q7%81E%?4Q<=21p041p0I1p0M1p0QB1pW4RA1pQHRC1pV:RJ1pULRD1pWJRE1pV4R61pW@R81pW<R:1p2R<1pV0R@1pQ8RB1pVLRF1pQDRH1pW2RN1pQJS01pV6S71pUFS91pNSA1").
Proof. intros E X fx Rc pc Mc modelc LKc crc Ac s sm e v c fx1 R1 pc1.
intros ST MS MID1 KC. pose proof ST as (BI & MID & REST). pose proof BI as (HHc & AMc & _).
unfold PMSPA.cfg.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ _ LKc crc Ac Mc modelc fx fx1 Rc pc R1 pc1 _ (PMARVK.vK E) HHc AMc MS (fun x Hx => Hx) (fun a Ha => eq_refl)).
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
assert (E1 : M1 = Mc) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1.
apply KC; [| exact HID1].
split; [eapply PMAUK.binv_model; [exact BI| exact HH1| exact AM1| exact MRT1]|].
split; [exact MID1| exact REST].
Qed.
Lemma rv_mkec : ltac2:(TCodec.tc2 tcn__PmARvC "TA&R4vR>vAvRLv@%544321'QA'Q@r1%2587651'R7&Ey5'SKyR0%211%5241'5y8%611%311p061'D'4&Q5%211&O'7'=%2211%711'QK'QM'3&QBr@r=r<r;r:r9r8r7r6r5r4r3%=?Q=Q<Q;<;:987654321':&R8r>&SJ&RGu1%211%42Q;1%7261r2%72Q<1%;3Q<31&Q8%11?u:%;11%=2QD1%@2N1&Q>rC%211%B2QG1%F3QG51rAu;%E11%G2QN1%J241%I2QNQ1%M3QN21'9&RC+1%221Q7+R0%42Q91%6231rLrErB(8&QH&QI%211%QJ?RJRIRH7Q@Q?Q>Q36RDI54Q:1&Q0rJ%221QD'R;&R<&Q:%11S2&QNr?%265QMQL1QKQJ&QDrN%211%:49741p0<1p0@1p4R?1pQ6RE1pVHRI1pQ@RK1pQFS11pV8S81rD+ej[D%A6DO21QBNrG%@11%H4GE31p071p0Q61p0Q>1p0QF1p0R01p0R31p0R@1pW:S41pX0S51pUNS61pWLS71pV4S31pW@S51pW<S71p2S91pV0S>1pQ8S@1pVLSD1pQDSF1pQJSL1pV6T31pUFT51pNT91pQBT;1").
Proof. intros MKE E X fx Rc Mc modelc LKc crc Ac s sm e v0 c0 w ra.
intros ST R1 RA R10 R11 Hw KC.
pose proof ST as (BI & MID & RPRE & STEP & EE & CK & EC).
pose proof BI as (HHc & AMc & MRTc & INCAc & INCLc & ASTKc & EKc & DKc & OWNc & DEFc).
pose proof RPRE as (PA & IA & VIS & VREF & BASE & ERR & TBOK).
pose proof EC as (_ & _ & ECD & ECA).
pose proof (PMARVK.c_AR L ar HI E X) as AR. unfold PMARVK.rvar in AR. cbn zeta in AR.
destruct AR as ((ARsp1 & ARsp2) & (ARop1 & ARop2 & ARop3 & ARop4) & (ARq1 & ARq2 & ARq3 & ARq4 & ARq5) & _ & _).
pose proof (PMARVK.c_FOK L ar HI E X) as ((rs & Hfb) & Fal).
assert (AOF : forall a n, PMARVK.vfb E + 32 <= a -> a + n <= PMARVK.vfb E + 1016 -> PMSPA.aobjA (PMARVK.vFF E) a n).
{ intros a n Xa1 Xa2. exists (PMARVK.vfb E, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. clear - Xa1 Xa2; lia. }
assert (Eoec : PMARVK.oec E = PMARVK.vfb E + 992) by reflexivity. assert (Eop : PMARVK.op E = PMARVK.vfb E + 464) by reflexivity.
assert (Eois : PMARVK.ois E = PMARVK.vfb E + 96) by reflexivity. assert (Eov : PMARVK.ov E = PMARVK.vfb E + 432) by reflexivity.
unfold PMA.make_ec_spec, PMSPA.make_ec_spec in MKE.
change 0xae974 with (pa_make_ec PMA.AD).
apply (MKE fx Rc Mc modelc (PMARVK.vK E) (PM.parser_own s ++ PMARVK.vLBX E) (PMARVK.FF' E) LKc Ac crc (PMARVK.oec E) w (PMARVK.vsp E - 128) ra e
HHc AMc (PMARVK.c_K0 L ar HI E X)).
- exact (rv_entryA E X _ _ _ _ _ _ _ _ _ _ _ ra 1 ST R1 RA ltac:(lia)).
- exact (rv_room E X _ _ _ _ _ _ _ _ _ _ _ 1 ST ltac:(lia)).
- exact (rv_frs E X).
- rewrite L5K.rl10. exact R10.
- rewrite L5K.rl11. exact R11.
- exact Hw.
- apply PMAUAR.aobjA_push. apply AOF; clear - Eoec; lia.
- exact ARq2.
- exact ECD.
- exact ECA.
- exact BASE.
- exact ERR.
- intros fx' R' M' model' LK' Aw' RP' EC' ERR' HP' MRT' INCLK' INCA' AM' HH'.
change (PMSPA.pm_scr 1) with 14336 in HP'.
apply (KC fx' R' M' model' LK' Aw'); [| exact RP'].
pose proof (PMARVK.c_G L ar HI E X) as XG.
pose proof XG as G'. destruct G' as [GHk GSPT GSLO GSHI GSPC GOCR GOWNAG GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ (PMARVK.c_HH L ar HI E X)) as (WB0 & WF0 & FSAPP & FSCEIL & _).
pose proof (WF0 _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 4) with 1024 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, F1, F2.
set (Wc6 := (PMARVK.oec E, 16) :: (if e then [] else PMSPA.err_W PMA.AD)) in HP'.
assert (Wc6R : forall rr a, In rr Wc6 -> L5.in_rng rr a -> (PMARVK.oec E <= a < PMARVK.oec E + 16) \/ (0x66d380 <= a < 0x68f0f4)).
{ intros rr a Hin Hr. unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [left; exact Hr|]. right. destruct e; [destruct Hin|].
unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr; lia. }
assert (BI6 : PMAUK.binv L ar HI (PMARVK.vM E) (PMARVK.vmodel E) (PMARVK.vLBX E) (PMARVK.vFF E) (PMARVK.vLK E) (PMARVK.vAw E) (PMARVK.vsp E) PMARVK.SCR
(PMARVK.vsp E - 128) (PMARVK.own (PMARVK.vsp E) (PMARVK.vR E)) (PMARVK.vF E) 3 (PMARVK.WR E) (PM.parser_own s) M' model' LK' crc Aw').
{ apply (PMAUK.binv_callee L ar C HI HIok (PMARVK.vM E) (PMARVK.vmodel E) (PMARVK.vLBX E) (PMARVK.vFF E) (PMARVK.vLK E) (PMARVK.vAw E) (PMARVK.vsp E) PMARVK.SCR
(PMARVK.vsp E - 128) (PMARVK.vsp E - 104) (PMARVK.vsp E) (PMARVK.ocell (PMARVK.vsp E)) (PMARVK.own (PMARVK.vsp E) (PMARVK.vR E)) (PMARVK.vF E) (PMARVK.vfl E) 3
(PMARVK.vLK2 E) (PMARVK.vM2 E) (PMARVK.vmodel2 E) (PMARVK.vcr E) (PM.parser_own (PMARVK.vs0 E)) XG
(PMARVK.WR E) (PMARVK.WR E) (PM.parser_own s) (PM.parser_own s) (PM.parser_own s) Mc modelc LKc crc Ac M' model' LK' crc Aw' 14336 Wc6 BI HP' HH' AM' MRT' INCA' INCLK');
[clear; lia| unfold PMARVK.SCR; clear; lia| | | intros a Xa; exact Xa].
- intros rr a Hin Hr. change (ff_bytes 3 / 8) with 64. unfold PMARVK.ocell, SB.
assert (DF1 : 0 <= PMARVK.vF E / 8) by (apply Z.div_pos; clear - ARsp1 GFR; lia).
assert (DF2 : PMARVK.vF E / 8 <= 17592186044408) by (apply Z.div_le_upper_bound; clear - GFR; lia).
pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
destruct (Wc6R rr a Hin Hr) as [Xa|Xa]; (split; [clear - Xa ARq4 Eoec F2 FSCEIL GSLO GSPT ARsp1; unfold PMARVK.SCR in GSLO; lia|]).
+ destruct FA1 as [Y|Y]; clear - Xa Y DF1 DF2 F1 F2 Eoec; lia.
+ clear - Xa DF1; lia.
- intros a Hc Ho rr Hin Hr. destruct (Wc6R rr a Hin Hr) as [Xa|Xa].
+ apply (Ho (PMSPA.o_ec PMA.AD (PMARVK.vfb E), 16)); [unfold PMARVK.WR, PMSPA.W_run, PMSPA.W_srcf, PMSPA.err_W; cbn [app]; do 6 right; left; reflexivity|
unfold L5.in_rng; fold (PMARVK.oec E); cbn [fst snd]; clear - Xa; lia].
+ unfold PMARVK.WR, PMSPA.W_run, PMSPA.W_srcf, PMSPA.err_W in Ho. cbn [app pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Ho.
unfold Wc6, PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin.
destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Xa Eoec ARq1; lia|].
destruct e; [destruct Hin|]. destruct Hin as [<-|[<-|[]]].
* apply (Ho _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))))); exact Hr.
* apply (Ho _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))))); exact Hr. }
set (LB := PM.parser_own s ++ PMARVK.vLBX E) in *.
pose proof (L5SAR.ek_callee L ar LB [] (PMARVK.vFF E) [(PMARVK.vF E, 3, PMARVK.vsp E - 128 + 32)] (PMARVK.vsp E) 28672 (PMARVK.vsp E - 128) 14336 Wc6 Wc6 Mc M' HP'
ltac:(clear; lia) ltac:(clear; lia) (fun a _ X0 => X0)) as EK46.
assert (WAPP6 : PMKA.wapp Wc6).
{ intros rr Hin. unfold Wc6 in Hin. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct Hin as [<-|Hin]; cbn [fst snd].
- pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1. destruct FA1 as [Y|Y]; clear - Y F1 F2 Eoec; lia.
- destruct e; [destruct Hin|]. unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd]; clear; lia. }
pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ (PMARVK.c_HH L ar HI E X)) as FRB.
pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHc) as BRB.
assert (OUT6 : forall a n, PMARVK.vfb E + 32 <= a -> a + n <= PMARVK.vfb E + 1016 -> (a + n <= PMARVK.oec E \/ PMARVK.oec E + 16 <= a) -> forall i, a <= i < a + n -> L5.outside Wc6 i).
{ intros a n X1 X2 X3 i Hi rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y|Y]; [clear - Hi Y X3; lia| clear - Hi Y X1 Eop ARop1; lia]. }
assert (OUTB6 : forall q m, In (q, m) LB -> forall i, q <= i < q + m -> L5.outside Wc6 i).
{ intros q m Hq i Hi rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y|Y].
- destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m (PMARVK.oec E) 16 HHc Hq (PMAUAR.aobjA_push _ _ 16 _ (AOF (PMARVK.oec E) 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia)))) as [Z|Z];
clear - Hi Y Z; lia.
- pose proof (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ q m HHc Hq) as Z. destruct Z as [Z|Z]; clear - Hi Y Z; lia. }
assert (AOP : PMSPA.aobjA (PMARVK.vFF E) (PMARVK.op E) 384) by (apply AOF; clear - Eop; lia).
assert (PA6 : PM.parser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA M' (PMARVK.op E) (PMARVK.ois E) s).
{ apply (PMKA.parser_keepA RSEGS PMA.AD L ar LB (PMARVK.vFF E) (PMARVK.vsp E) 28672 Wc6 Mc M' EK46 WAPP6 FRB BRB _ _ _ AOP); [| | | | | exact PA].
- unfold LB. apply incl_appl, incl_refl.
- apply OUT6; clear - Eop Eoec; lia.
- unfold PMKA.blk_out. apply (OUTB6 _ _). unfold LB. apply in_or_app; left. unfold PM.parser_own, PM.src_own. left; reflexivity.
- unfold PMKA.blk_out. apply (OUTB6 _ _). unfold LB. apply in_or_app; left. unfold PM.parser_own, PM.vec_own. right; left; reflexivity.
- intros cc0 nn0 pp0 E0. unfold PMKA.blk_out. apply (OUTB6 pp0 cc0). unfold LB. apply in_or_app; left. unfold PM.parser_own, PM.vs_own. rewrite E0. right; right; left; reflexivity. }
assert (IA6 : PM.iss_at RSEGS PMA.AD PMSPA.accA M' (PMARVK.ois E) (PMARVK.vstr E) sm).
{ apply (PMKA.iss_keepA RSEGS PMA.AD L ar LB (PMARVK.vFF E) (PMARVK.vsp E) 28672 Wc6 Mc M' EK46 WAPP6 FRB BRB _ _ sm (AOF (PMARVK.ois E) 272 ltac:(clear - Eois; lia) ltac:(clear - Eois; lia)));
[| | | exact IA].
- unfold LB. apply incl_appr. exact (PMARVK.c_INCS L ar HI E X).
- apply OUT6; clear - Eois Eoec; lia.
- intros cc0 nn0 pp0 E0. unfold PMKA.blk_out. apply (OUTB6 pp0 cc0). unfold LB. apply in_or_app; right. apply (PMARVK.c_INCS L ar HI E X). rewrite E0. left; reflexivity. }
assert (VIS6 : PMSPA.visitor_at RSEGS PMA.AD M' (PMARVK.ov E)).
{ apply (PMKA.visitor_keepA RSEGS PMA.AD L ar LB (PMARVK.vFF E) (PMARVK.vsp E) 28672 Wc6 Mc M' EK46 WAPP6 FRB _ (AOF (PMARVK.ov E) 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia))); [| exact VIS].
apply OUT6; clear - Eov Eoec; lia. }
assert (VREF6 : L5.u64_at RSEGS M' (PMARVK.op E + 384) (PMARVK.ov E)).
{ apply (PMKA.u64_keepA RSEGS L ar LB (PMARVK.vFF E) (PMARVK.vsp E) 28672 Wc6 Mc M' EK46 WAPP6 FRB (PMARVK.op E + 384) _ (AOF (PMARVK.op E + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [| exact VREF].
apply OUT6; clear - Eop Eoec; lia. }
assert (BASE6 : PMSTA.base_okA RSEGS PMA.AD M').
{ apply (PMAPAR.base_keepW L ar C LY LB (PMARVK.vFF E) (PMARVK.vsp E) 28672 Wc6 Mc M' EK46); [| | | | exact BASE].
- intros a Ha rr Hin Hr. destruct (Wc6R rr a Hin Hr) as [Y|Y]; [clear - Ha Y Eoec ARq1; lia|].
unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Ha Eoec ARq1; lia|]. destruct e; [destruct Hin|].
unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr Ha; lia.
- intros a Ha rr Hin Hr. unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Ha Eoec ARq1; lia|]. destruct e; [destruct Hin|].
unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr Ha; lia.
- intros rr Hin Hr. unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Eoec ARq1; lia|]. destruct e; [destruct Hin|].
unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr; lia.
- intros a Ha rr Hin Hr. unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Ha Eoec ARq1; lia|]. destruct e; [destruct Hin|].
unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit PMA.AD ADDR_A] in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr Ha; lia. }
unfold PMARVK.rvst. split; [exact BI6|].
split; [apply (PMARVK.mid_keep E Rc R' MID); intros k Hk; apply (L5SAR.cs_of_preserved Rc R' k RP'); revert k Hk; PMARVK.kin|].
split; [unfold PMSPA.run_pre; split; [exact PA6|]; split; [exact IA6|]; split; [exact VIS6|]; split; [exact VREF6|]; split; [exact BASE6|];
split; [exact ERR'| exact TBOK]|].
split; [exact STEP|]. split; [intros _; reflexivity|]. split; [exact CK| exact EC'].
Qed.
Lemma fbF_apart : ltac2:(TCodec.tc2 tcn__PmARvC "K'QA'Q@vR>vAvRLv@r1%6554321'<&RC&RA&QFr2%211+oH%5221&QC%115%9231+`0%:231+Q0%<291%>231%@261pUFB1pNJ1").
Proof. intros E X.
pose proof (PMARVK.c_FOK L ar HI E X) as ((rs & Hfb) & Fal).
pose proof (PMARVK.c_G L ar HI E X) as G'. destruct G' as [_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ GNCF _].
change (ff_bytes 3) with 512 in GNCF.
destruct (Z_le_gt_dec (PMARVK.vfb E + 1016) (PMARVK.vF E)) as [Y|Y]; [left; exact Y|].
destruct (Z_le_gt_dec (PMARVK.vF E + 512) (PMARVK.vfb E + 32)) as [Z|Z]; [right; exact Z|].
exfalso. set (a := Z.max (PMARVK.vF E) (PMARVK.vfb E + 32)).
apply (GNCF a); [left; unfold a; lia|].
unfold aclient, aclient_g. do 3 right; left. exists (PMARVK.vfb E, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
change (ff_bytes 4) with 1024. unfold a. split; [lia| intros W; lia].
Qed.
Lemma rv_local_acc : ltac2:(TCodec.tc2 tcn__PmARvC "SF'QA'Q@vR>vAvRLv@r1%6554321&Ey5'SKyR0%211%5241'5y8%611%311p061'D'4&Q5%211&O'7'=%2211%711'QK'QM'3&QBrAr?r>r=r<r;r:r9r8r7r6r5%=?Q9Q8Q7<;:987654321'9&RC+4%2215&RD+QO%2281%7241+1%821;+8%:2=1%<231'<':%13Q3AB%<2C6%A221z%53Q7E1%63Q8G:%E221%9251&RA&RB&QCrE%211%421B+QoooPP0%7221%821Q4%B3QDQ21&Q9&R<&M&Q3rB%22QB1rC%5221%8471Q<Q=&Q2rDrG%D11&RF%12Q5QF%I231%7361QGp091p0C1p0N1p0Q91p0Q?1p0QH1pW>R<1pWNR=1pVBR>1pV@R?1pULR@1pWJRA1pV4R=1pW@R?1pW<RA1p2RC1pV0RH1pQ8RJ1pVLRN1pQDS01pQJS61pUFS=1pNSE1").
Proof. intros E X Rc Mc modelc LKc crc Ac s sm e v c j k vb sa.
intros ST Hj Hk Hvb Esa U. pose proof ST as (BI & _).
destruct (PMAUK.vis_facts L ar C HI LYa HIok (PMARVK.vM E) (PMARVK.vmodel E) (PMARVK.vLBX E) (PMARVK.vFF E) (PMARVK.vLK E) (PMARVK.vAw E) (PMARVK.vsp E) PMARVK.SCR
(PMARVK.vsp E - 128) (PMARVK.vsp E - 104) (PMARVK.vsp E) (PMARVK.ocell (PMARVK.vsp E)) (PMARVK.own (PMARVK.vsp E) (PMARVK.vR E)) (PMARVK.vF E) (PMARVK.vfl E) 3
(PMARVK.vLK2 E) (PMARVK.vM2 E) (PMARVK.vmodel2 E) (PMARVK.vcr E) (PM.parser_own (PMARVK.vs0 E)) (PMARVK.c_G L ar HI E X)
(PMARVK.WR E) (PM.parser_own s) Mc modelc LKc crc Ac BI) as (_ & _ & _ & (_ & _ & _ & _ & VSH)).
change (ff_bytes 3 / 8) with 64 in VSH.
pose proof (PMARVK.c_AR L ar HI E X) as AR. unfold PMARVK.rvar in AR. cbn zeta in AR.
destruct AR as (_ & _ & _ & (ARF1 & ARF2 & _) & _).
assert (DF1 : 0 <= PMARVK.vF E / 8) by (apply Z.div_pos; lia).
assert (DF2 : PMARVK.vF E / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; lia).
assert (UM : L5.u8_at RSEGS Mc sa vb).
{ apply (proj1 (L5A.u8_at_vis _ Mc sa vb (L5A.avis_sub _ (PMARVK.vF E / 8 + SB) 64 sa 1 VSH ltac:(unfold SB; lia) ltac:(unfold SB; lia)) ltac:(lia) ltac:(lia))). exact U. }
assert (BM : byte_at Mc sa vb) by (unfold byte_at; apply (L5ADHR.byte_of_u8 Mc sa vb UM); lia).
assert (F8 : PMARVK.vF E = 8 * (PMARVK.vF E / 8)) by (pose proof (Z.div_mod (PMARVK.vF E) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (PMARVK.vF E) 8 ltac:(lia));
assert (PMARVK.vF E mod 8 = 0) by (apply PMKA.mod16_8'; apply Z.mod_divide in ARF2; [destruct ARF2 as (q & Hq); rewrite Hq; replace (q * 32) with ((2 * q) * 16) by lia; apply Z_mod_mult| lia]); lia).
intros a Ha.
assert (Sa : HeapIfaceA.S a = sa).
{ unfold HeapIfaceA.S, HeapIfaceA.SB. rewrite Esa. replace a with ((a - (PMARVK.vF E + 8 * j)) + (PMARVK.vF E / 8 + j) * 8) by lia.
rewrite Z.div_add by lia. rewrite (Z.div_small (a - (PMARVK.vF E + 8 * j)) 8) by lia. lia. }
assert (Ma : a mod 8 = a - (PMARVK.vF E + 8 * j)).
{ replace a with ((a - (PMARVK.vF E + 8 * j)) + (PMARVK.vF E / 8 + j) * 8) at 1 by lia. rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity. }
rewrite Sa. destruct Hvb as [(E1 & E2)|(E1 & E2)]; subst vb.
- right. exists k. split; [exact BM|]. split; [lia| lia].
- left. exact BM.
Qed.
Lemma rv_local_acc_full : ltac2:(TCodec.tc2 tcn__PmARvC "R>'SKyR0%211'5y8%511%311p051'='9&RC+VbTP0r5%3221+Sooooooo`0%5231%7231':&REr6+Q0%3221z%63?21+4%?216&RD+QO%2291%D241+1%E21<+8%G2>1%I231'<r7%D3MB1%<226%N221%G3Q0EB%H3Q159%Q1221%8241&RA&RBr:%221?+QoooPP0%5221r9%7221%Q33Q<Q11&Q9&R<r<r8%4432E1&Q2r=&RFr;%22N1%C281%6351Bp081p0>1p0H1p0Q21p0Q81p0Q?1p0QG1pW>R01pWNR11pVBR21pV@R31pQ0R41pQ>R61").
Proof. intros M Fv j k vb sa.
intros ARF1 ARF2 Hj Hk Hvb Esa UM.
assert (DF1 : 0 <= Fv / 8) by (apply Z.div_pos; lia).
assert (DF2 : Fv / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; lia).
assert (BM : byte_at M sa vb) by (unfold byte_at; apply (L5ADHR.byte_of_u8 M sa vb UM); lia).
assert (F8 : Fv = 8 * (Fv / 8)) by (pose proof (Z.div_mod Fv 8 ltac:(lia)); pose proof (Z.mod_pos_bound Fv 8 ltac:(lia));
assert (Fv mod 8 = 0) by (apply PMKA.mod16_8'; apply Z.mod_divide in ARF2; [destruct ARF2 as (q & Hq); rewrite Hq; replace (q * 32) with ((2 * q) * 16) by lia; apply Z_mod_mult| lia]); lia).
intros a Ha.
assert (Sa : HeapIfaceA.S a = sa).
{ unfold HeapIfaceA.S, HeapIfaceA.SB. rewrite Esa. replace a with ((a - (Fv + 8 * j)) + (Fv / 8 + j) * 8) by lia.
rewrite Z.div_add by lia. rewrite (Z.div_small (a - (Fv + 8 * j)) 8) by lia. lia. }
assert (Ma : a mod 8 = a - (Fv + 8 * j)).
{ replace a with ((a - (Fv + 8 * j)) + (Fv / 8 + j) * 8) at 1 by lia. rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity. }
rewrite Sa. destruct Hvb as [(E1 & E2)|(E1 & E2)]; subst vb.
- right. exists k. split; [exact BM|]. split; [lia| lia].
- left. exact BM.
Qed.
Lemma rv_local_def : ltac2:(TCodec.tc2 tcn__PmARvC "RC'QA'Q@vR>vAvRLv@r1%6554321&Ey5'SKyR0%211%5241'5y8%611%311p061'D'4&Q5%211&O'7'=%2211%711'QK'QM'3&QBr?r=r<r;r:r9r8r7r6r5r4r3%=?Q9Q8Q7<;:987654321&RC&QCr@%211%4216&RA%1298rA%711+`0%5221%;251&Q7%13JA@&M&Q3%12KM%321?%631GFp061p091p0A1p0G1pVNQ;1pW0Q<1pULQ=1pWJQ>1pV4Q:1pW@Q<1pW<Q>1p2Q@1pV0QE1pQ8QG1pVLQK1pQDQM1pQJR31pUFR:1pNRB1").
Proof. intros E X Rc Mc modelc LKc crc Ac s sm e v c p n.
intros ST H1 H2 D. pose proof ST as (BI & _).
destruct (PMAUK.vis_facts L ar C HI LYa HIok (PMARVK.vM E) (PMARVK.vmodel E) (PMARVK.vLBX E) (PMARVK.vFF E) (PMARVK.vLK E) (PMARVK.vAw E) (PMARVK.vsp E) PMARVK.SCR
(PMARVK.vsp E - 128) (PMARVK.vsp E - 104) (PMARVK.vsp E) (PMARVK.ocell (PMARVK.vsp E)) (PMARVK.own (PMARVK.vsp E) (PMARVK.vR E)) (PMARVK.vF E) (PMARVK.vfl E) 3
(PMARVK.vLK2 E) (PMARVK.vM2 E) (PMARVK.vmodel2 E) (PMARVK.vcr E) (PM.parser_own (PMARVK.vs0 E)) (PMARVK.c_G L ar HI E X)
(PMARVK.WR E) (PM.parser_own s) Mc modelc LKc crc Ac BI) as (_ & _ & _ & (_ & _ & VF & _)).
change (ff_bytes 3) with 512 in VF.
apply (proj2 (L5A.defined_vis _ Mc p n (L5A.avis_sub _ (PMARVK.vF E) 512 p n VF H1 H2))). exact D.
Qed.
Lemma rv_sread : ltac2:(TCodec.tc2 tcn__PmARvC "V@&R5vR>vAvRLv@%544321'QA'Q@r1%2587651'R7&Ey5'SKyR0%211%5241'5y8%611%311p061'D'4&Q5%211&O'7'=%2211%711'QK'QM'3&QBrAr>r=r<r;r:r9r8r7r6r5r4%=?Q=Q<Q;<;:987654321':&R8r?&SJ&RGu1%211%42Q;1%7261%62Q;;%:3Q;21&Q8%11?u:%:11%<2QC1%?2M1&RA&Q?rD%211+H%5221%D2QI1%H3QI81rBu;%G11%I2R01%L241%K2R0Q2%O3R021rCu<%N11%Q02R71%Q3241%Q53R617'9&RC+1%221Q>+8%42Q@1%6231&QCrH%211+Q0%Q0221%;21QI%Q22QKQJrI%811+_H%Q6221%A251&Q2rF%231R4R3'QLrQ4rM&R3rKr3%3221r2rG%RC?SCSBSA8R;R:R9R87R732AG1&Q0rQ2%221R?%R82RAQJ%R72S<9%R;3S<21z%Q621R?%Q72R@:%Q9221&Q7%13RJMRD&RBrQ:%Q711%321Q;+QoooPP0%R6221%QA21T0&RD+R0%R:241%32T41%QG251%RK2T0K%S;11rQ7%113%S23SN31p061pUHSH1'R;&R<&Q:%11TG&QNrL%265S9SG1SFSE&QD%11J%948631p0;1p0O1p0Q21p0Q71p0Q;1p0Q?1pV2T91pWBT61pWDQK1p4T:1pQ6T@1pVHTD1pQ@TF1pQFTL1pV8U31rJ+eliD%G6J2R<1RBQL%E1G%M4LJ21p061p0R91p0R=1p0RD1p0RK1p0S31p0S:1p0SB1p0SO1p0T21p0T>1pVBU21pW0U31pW:U41pULU51pWJU61pV4U21pW@U41pW<U61p2U81pV0U=1pQ8U?1pVLUC1pQDUE1pQJUK1pV6V21pUFV41pNV81pU0V:1").
Proof. intros SR E X fx Rc Mc modelc LKc crc Ac s sm e v c ra p k.
intros ST R1 RA R10 R11 R12 Hk Hp1 Hp2 ACC KC.
pose proof ST as (BI & MID & RPRE & STEP & EE & CK & EC).
pose proof BI as (HHc & AMc & MRTc & INCAc & INCLc & ASTKc & EKc & DKc & OWNc & DEFc).
pose proof RPRE as (PA & IA & VIS & VREF & BASE & ERR & TBOK).
pose proof (PMARVK.c_AR L ar HI E X) as AR. unfold PMARVK.rvar in AR. cbn zeta in AR.
destruct AR as ((ARsp1 & ARsp2) & (ARop1 & ARop2 & ARop3 & ARop4) & (ARq1 & ARq2 & ARq3 & ARq4 & ARq5)
& (ARF1 & ARF2 & ARF3 & ARF4 & ARF5 & ARF6 & ARF7 & ARF8 & ARF9 & ARF10 & ARF11 & ARF12 & ARF13 & ARF14 & ARF15 & ARF16) & _).
pose proof (fbF_apart E X) as AFB.
pose proof (PMARVK.c_FOK L ar HI E X) as ((rs & Hfb) & Fal).
assert (AOF : forall a n, PMARVK.vfb E + 32 <= a -> a + n <= PMARVK.vfb E + 1016 -> PMSPA.aobjA (PMARVK.vFF E) a n).
{ intros a n Xa1 Xa2. exists (PMARVK.vfb E, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. clear - Xa1 Xa2; lia. }
assert (Eoec : PMARVK.oec E = PMARVK.vfb E + 992) by reflexivity. assert (Eop : PMARVK.op E = PMARVK.vfb E + 464) by reflexivity.
assert (Eois : PMARVK.ois E = PMARVK.vfb E + 96) by reflexivity. assert (Eov : PMARVK.ov E = PMARVK.vfb E + 432) by reflexivity.
pose proof (PMARVK.c_G L ar HI E X) as XG.
pose proof XG as G'. destruct G' as [GHk GSPT GSLO GSHI GSPC GOCR GOWNAG GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ (PMARVK.c_HH L ar HI E X)) as (WB0 & WF0 & FSAPP & FSCEIL & _).
pose proof (WF0 _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 4) with 1024 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, F1, F2.
unfold PMA.src_read_spec, PMSPA.src_read_spec, PMSPA.src_spec in SR.
change 0xaf334 with (pa_src_read PMA.AD).
apply (SR fx Rc Mc modelc (PMARVK.vK E) (PMARVK.vLBX E) (PMARVK.FF' E) LKc Ac crc (PMARVK.vsp E - 128) ra (PMARVK.vfb E) s (PMARVK.vstr E) sm [(p, k)]
HHc AMc (PMARVK.c_K0 L ar HI E X)).
- exact (rv_entryA E X _ _ _ _ _ _ _ _ _ _ _ ra 4 ST R1 RA ltac:(lia)).
- exact (rv_room E X _ _ _ _ _ _ _ _ _ _ _ 4 ST ltac:(lia)).
- exact (rv_frs E X).
- exact (PMARVK.frame_okA' E (PMARVK.c_FOK L ar HI E X)).
- rewrite L5K.rl10. unfold PMSPA.o_src. exact R10.
- exists p, k. split; [rewrite L5K.rl11; exact R11|]. split; [rewrite L5K.rl12; exact R12|]. split; [unfold PM.CHUNK; clear - Hk; lia|].
left. split; [exists (PMARVK.vF E, 3, PMARVK.vsp E - 128 + 32); split; [left; reflexivity| cbn [ff_addr ff_class fst snd]; change (ff_bytes 3) with 512; clear - Hp1 Hp2; lia]|].
split; [clear - Hk; lia|].
split; [apply (L5.defined_sub Mc (PMARVK.vF E) 512); [| clear - Hp1 Hp2; lia| clear - Hp1 Hp2; lia]|].
{ pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHc) as (_ & WFc & _).
destruct (WFc _ (or_introl eq_refl)) as (_ & _ & _ & _ & DF & _). cbn [ff_addr ff_class fst snd] in DF. change (ff_bytes 3) with 512 in DF. exact DF. }
split; [exact ACC|].
split; [fold (PMARVK.ois E); clear - AFB Hp1 Hp2 Eois; lia| fold (PMARVK.op E); clear - AFB Hp1 Hp2 Eop; lia].
- exists p, k. split; [rewrite L5K.rl11; exact R11|]. split; [rewrite L5K.rl12; exact R12|]. split; [clear - Hp1 Hp2 Hk ARF1; lia|]. split; [clear - Hk; lia| reflexivity].
- exact PA.
- exact IA.
- exact BASE.
- exact (PMARVK.c_INCS L ar HI E X).
- intros fx' R' M' model' LK' Aw' src' sm' RP' PA' IA' STEP' RES' HP' MRT' INCLK' INCA' AM' HH'.
change (PMSPA.pm_scr 4) with 20480 in HP'.
destruct RES' as (p' & k' & d & Yp & Yk & Hp' & Hk' & Yd & Hd & CONS & DEFd & RM1 & RM0).
assert (Ek : k' = k).
{ rewrite L5K.rl12 in Yk. rewrite R12 in Yk. apply (f_equal bv_unsigned) in Yk. unfold PM.CHUNK in Hk'. rewrite !L5.unsigned_lit in Yk by (clear - Hk' Hk; lia). clear - Yk; lia. }
assert (Ep : p' = p).
{ rewrite L5K.rl11 in Yp. rewrite R11 in Yp. apply (f_equal bv_unsigned) in Yp. rewrite !L5.unsigned_lit in Yp by (clear - Hp' Hp1 Hp2 Hk ARF1; lia). clear - Yp; lia. }
subst k' p'. rewrite L5K.rl10 in Yd.
assert (QC : PM.sr_qc src' = PM.sr_qc (PM.p_src s)) by (destruct STEP' as (Xq & _); exact Xq).
assert (EOWN : PM.parser_own (PMSPA.with_src s src') = PM.parser_own s) by (unfold PMSPA.with_src, PM.parser_own, PM.src_own; cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]; rewrite QC; reflexivity).
set (LB := PM.parser_own s ++ PMARVK.vLBX E) in *.
assert (Iq : In (PM.sr_qc (PM.p_src s), PM.CHUNK) (PM.parser_own s)) by (unfold PM.parser_own, PM.src_own; left; reflexivity).
assert (IqL : In (PM.sr_qc (PM.p_src s), PM.CHUNK) LB) by (unfold LB; apply in_or_app; left; exact Iq).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHc) as (WBc & _).
pose proof (WBc _ IqL) as ((Bq0 & _ & _ & _ & Bq4 & Bq5) & _). cbn [fst snd] in Bq0, Bq4, Bq5. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI, PM.CHUNK in Bq5, Bq4.
destruct Bq5 as (_ & Bq5 & _).
pose proof (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ _ _ HHc IqL) as Bqi. unfold PM.CHUNK in Bqi.
set (qc := PM.sr_qc (PM.p_src s)) in *.
set (Wc := PMSPA.W_src PMA.AD (PMARVK.vfb E) (PM.p_src s) ++ [(p, k)]) in HP'.
assert (WcR : forall rr a, In rr Wc -> L5.in_rng rr a ->
(PMARVK.op E + 280 <= a < PMARVK.op E + 320) \/ (PMARVK.ois E + 40 <= a < PMARVK.ois E + 48) \/ (PMARVK.ois E + 152 <= a < PMARVK.ois E + 156)
\/ (qc <= a < qc + 16384) \/ (p <= a < p + k)).
{ intros rr a Hin Hr. unfold Wc, PMSPA.W_src, PMSPA.W_srcf, PMSPA.o_src, PMSPA.o_is, PMSPA.o_p in Hin. cbn [app pa_off_p pa_off_is PMA.AD ADDR_A] in Hin.
unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hr; unfold PM.CHUNK in Hr; clear - Hr Eop Eois;
[left|right;left|right;right;left|right;right;right;left|right;right;right;right]; lia. }
assert (DF1 : 0 <= PMARVK.vF E / 8) by (apply Z.div_pos; clear - GFR; lia).
assert (DF2 : PMARVK.vF E / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; clear - GFR; lia).
pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
assert (BI' : PMAUK.binv L ar HI (PMARVK.vM E) (PMARVK.vmodel E) (PMARVK.vLBX E) (PMARVK.vFF E) (PMARVK.vLK E) (PMARVK.vAw E) (PMARVK.vsp E) PMARVK.SCR
(PMARVK.vsp E - 128) (PMARVK.own (PMARVK.vsp E) (PMARVK.vR E)) (PMARVK.vF E) 3 (PMARVK.WR E) (PM.parser_own s) M' model' LK' crc Aw').
{ apply (PMAUK.binv_callee L ar C HI HIok (PMARVK.vM E) (PMARVK.vmodel E) (PMARVK.vLBX E) (PMARVK.vFF E) (PMARVK.vLK E) (PMARVK.vAw E) (PMARVK.vsp E) PMARVK.SCR
(PMARVK.vsp E - 128) (PMARVK.vsp E - 104) (PMARVK.vsp E) (PMARVK.ocell (PMARVK.vsp E)) (PMARVK.own (PMARVK.vsp E) (PMARVK.vR E)) (PMARVK.vF E) (PMARVK.vfl E) 3
(PMARVK.vLK2 E) (PMARVK.vM2 E) (PMARVK.vmodel2 E) (PMARVK.vcr E) (PM.parser_own (PMARVK.vs0 E)) XG
(PMARVK.WR E) (PMARVK.WR E) (PM.parser_own s) (PM.parser_own s) (PM.parser_own s) Mc modelc LKc crc Ac M' model' LK' crc Aw' 20480 Wc BI HP' HH' AM' MRT' INCA' INCLK');
[clear; lia| unfold PMARVK.SCR; clear; lia| | | intros a Xa; exact Xa].
- intros rr a Hin Hr. change (ff_bytes 3 / 8) with 64. unfold PMARVK.ocell, SB.
destruct (WcR rr a Hin Hr) as [Xa|[Xa|[Xa|[Xa|Xa]]]]; (split; [clear - Xa ARop4 F2 FSCEIL GSLO GSPT ARsp1 Eop Eois Bq4 ARF1 Hp1 Hp2 GFCEIL; unfold PMARVK.SCR in GSLO; lia|]).
+ destruct FA1 as [Y|Y]; clear - Xa Y DF1 DF2 F1 F2 Eop; lia.
+ destruct FA1 as [Y|Y]; clear - Xa Y DF1 DF2 F1 F2 Eois; lia.
+ destruct FA1 as [Y|Y]; clear - Xa Y DF1 DF2 F1 F2 Eois; lia.
+ destruct Bq5 as [Y|Y]; clear - Xa Y DF1 DF2; lia.
+ destruct GFBIG as [Y|Y]; clear - Xa Y DF1 DF2 Hp1 Hp2; lia.
- intros a Hc Ho rr Hin Hr. destruct (WcR rr a Hin Hr) as [Xa|[Xa|[Xa|[Xa|Xa]]]].
+ apply (Ho (PMSPA.o_src PMA.AD (PMARVK.vfb E) + 256, 40)); [unfold PMARVK.WR, PMSPA.W_run, PMSPA.W_srcf; right; left; reflexivity|
unfold L5.in_rng, PMSPA.o_src; fold (PMARVK.op E); cbn [fst snd]; clear - Xa; lia].
+ apply (Ho (PMSPA.o_is PMA.AD (PMARVK.vfb E) + 40, 8)); [unfold PMARVK.WR, PMSPA.W_run, PMSPA.W_srcf; right; right; left; reflexivity|
unfold L5.in_rng; fold (PMARVK.ois E); cbn [fst snd]; clear - Xa; lia].
+ apply (Ho (PMSPA.o_is PMA.AD (PMARVK.vfb E) + 152, 4)); [unfold PMARVK.WR, PMSPA.W_run, PMSPA.W_srcf; right; right; right; left; reflexivity|
unfold L5.in_rng; fold (PMARVK.ois E); cbn [fst snd]; clear - Xa; lia].
+ exact (PMARS1.own_not_aclient L ar C HI HIok (PM.parser_own s) (PMARVK.vLBX E) _ LKc crc Ac Mc _ qc 16384 a (PMARVK.vsp E) 28672 HHc Iq Xa
(L5SAR.aclient_cons L ar _ _ _ _ _ _ Hc)).
+ apply (GNCF a); [left; clear - Xa Hp1 Hp2; lia| exact Hc]. }
pose proof (L5SAR.ek_callee L ar LB [] (PMARVK.vFF E) [(PMARVK.vF E, 3, PMARVK.vsp E - 128 + 32)] (PMARVK.vsp E) 28672 (PMARVK.vsp E - 128) 20480 Wc Wc Mc M' HP'
ltac:(clear; lia) ltac:(clear; lia) (fun a _ X0 => X0)) as EKc'.
pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ (PMARVK.c_HH L ar HI E X)) as FRB.
pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHc) as BRB.
assert (WAPPc : PMKA.wapp Wc).
{ intros rr Hin. unfold Wc, PMSPA.W_src, PMSPA.W_srcf, PMSPA.o_src, PMSPA.o_is, PMSPA.o_p in Hin. cbn [app pa_off_p pa_off_is PMA.AD ADDR_A] in Hin.
unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd]; unfold PM.CHUNK.
- destruct FA1 as [Y|Y]; clear - Y F1 F2 Eop; lia.
- destruct FA1 as [Y|Y]; clear - Y F1 F2 Eois; lia.
- destruct FA1 as [Y|Y]; clear - Y F1 F2 Eois; lia.
- destruct Bq5 as [Y|Y]; clear - Y; lia.
- destruct GFBIG as [Y|Y]; clear - Y Hp1 Hp2; lia. }
assert (OUTc : forall a n, PMARVK.vfb E + 32 <= a -> a + n <= PMARVK.vfb E + 1016 -> (a + n <= PMARVK.op E + 280 \/ PMARVK.op E + 320 <= a)
-> (a + n <= PMARVK.ois E + 40 \/ PMARVK.ois E + 48 <= a) -> (a + n <= PMARVK.ois E + 152 \/ PMARVK.ois E + 156 <= a) -> forall i, a <= i < a + n -> L5.outside Wc i).
{ intros a n X1 X2 X3 X4 X5 i Hi rr Hin Hr. destruct (WcR rr i Hin Hr) as [Y|[Y|[Y|[Y|Y]]]]; [clear - Hi Y X3; lia| clear - Hi Y X4; lia| clear - Hi Y X5; lia| |].
- destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ qc 16384 a n HHc IqL (PMAUAR.aobjA_push _ _ _ _ (AOF a n X1 X2))) as [Z|Z]; clear - Hi Y Z; lia.
- clear - Hi Y X1 X2 AFB Hp1 Hp2. lia. }
assert (VIS' : PMSPA.visitor_at RSEGS PMA.AD M' (PMARVK.ov E)).
{ apply (PMKA.visitor_keepA RSEGS PMA.AD L ar LB (PMARVK.vFF E) (PMARVK.vsp E) 28672 Wc Mc M' EKc' WAPPc FRB _ (AOF (PMARVK.ov E) 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia))); [| exact VIS].
apply OUTc; clear - Eov Eop Eois; lia. }
assert (VREF' : L5.u64_at RSEGS M' (PMARVK.op E + 384) (PMARVK.ov E)).
{ apply (PMKA.u64_keepA RSEGS L ar LB (PMARVK.vFF E) (PMARVK.vsp E) 28672 Wc Mc M' EKc' WAPPc FRB (PMARVK.op E + 384) _ (AOF (PMARVK.op E + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [| exact VREF].
apply OUTc; clear - Eop Eois; lia. }
assert (BASE' : PMSTA.base_okA RSEGS PMA.AD M').
{ apply (PMASK.base_keep L ar C LY LB (PMARVK.vFF E) (PMARVK.vsp E) 28672 Wc Mc M' EKc'); [| exact BASE].
intros a Ha rr Hin Hr. destruct (WcR rr a Hin Hr) as [Y|[Y|[Y|[Y|Y]]]]; [clear - Ha Y ARop1; lia| clear - Ha Y Eois Eop ARop1 Fal; lia| clear - Ha Y Eois Eop ARop1 Fal; lia| destruct Bqi as [Z|Z]; clear - Ha Y Z; lia| clear - Ha Y ARF1 Hp1; lia]. }
assert (ERR' : PMSTA.err_okA RSEGS PMA.AD PMA.AAD M' e).
{ apply (PMKA.err_okA_keep RSEGS PMA.AD PMA.AAD L ar LB (PMARVK.vFF E) (PMARVK.vsp E) 28672 Wc Mc M' EKc' e PMA.addrs_wf_A); [| exact ERR].
intros a D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
split; [exact (PMA.ly_static L C LY a D)|]. intros rr Hin Hr. destruct (WcR rr a Hin Hr) as [Y|[Y|[Y|[Y|Y]]]];
[clear - DI Y ARop1; lia| clear - DI Y Eois Eop ARop1 Fal; lia| clear - DI Y Eois Eop ARop1 Fal; lia| destruct Bqi as [Z|Z]; clear - DI Y Z; lia| clear - DI Y ARF1 Hp1; lia]. }
assert (EC' : PMSPA.ec_at RSEGS M' (PMARVK.oec E) v c).
{ apply (PMKA.ec_keepA RSEGS L ar LB (PMARVK.vFF E) (PMARVK.vsp E) 28672 Wc Mc M' EKc' WAPPc FRB _ v c (AOF (PMARVK.oec E) 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia))); [| exact EC].
apply OUTc; clear - Eoec Eop Eois; lia. }
assert (SHK : forall a, PMARVK.vF E / 8 + 2147450880 <= a < PMARVK.vF E / 8 + 2147450880 + 64 -> M' (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
{ intros a Ha. apply (proj1 HP'). split; [clear - Ha DF1 DF2; lia|]. split.
- apply (L5SAR.fframe_shadow_client L ar _ (PMARVK.FF' E) _ _ (PMARVK.vF E) 3 (PMARVK.vsp E - 128 + 32)); [left; reflexivity|].
change (ff_bytes 3) with 512. unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - Ha; lia.
- intros rr Hin Hr. destruct (WcR rr a Hin Hr) as [Xa|[Xa|[Xa|[Xa|Xa]]]].
+ destruct FA1 as [Y|Y]; clear - Xa Y Ha DF1 DF2 F1 F2 Eop; lia.
+ destruct FA1 as [Y|Y]; clear - Xa Y Ha DF1 DF2 F1 F2 Eois; lia.
+ destruct FA1 as [Y|Y]; clear - Xa Y Ha DF1 DF2 F1 F2 Eois; lia.
+ destruct Bq5 as [Y|Y]; clear - Xa Y Ha DF1 DF2; lia.
+ destruct GFBIG as [Y|Y]; clear - Xa Y Ha DF1 DF2 Hp1 Hp2; lia. }
apply (KC fx' R' M' model' LK' Aw' src' sm' d); [| exact RP'| exact Yd| exact Hd| exact DEFd| exact SHK].
unfold PMARVK.rvst. rewrite EOWN. split; [exact BI'|].
split; [apply (PMARVK.mid_keep E Rc R' MID); intros kk Hkk; apply (L5SAR.cs_of_preserved Rc R' kk RP'); revert kk Hkk; PMARVK.kin|].
split; [unfold PMSPA.run_pre; split; [exact PA'|]; split; [exact IA'|]; split; [exact VIS'|]; split; [exact VREF'|]; split; [exact BASE'|];
split; [exact ERR'| unfold PMSPA.with_src; cbn [PM.p_tb PM.p_tg]; exact TBOK]|].
split; [unfold PMSPA.with_src; cbn [PM.p_src]; exact (PMAPAR.src_step_transA _ _ _ _ _ _ STEP STEP')|].
split; [exact EE|].
split; [unfold PMSPA.credit_keep in *; unfold PMSPA.with_src, PM.pot_parser in *; cbn [PM.p_k PM.p_tb PM.p_tg] in *; exact CK| exact EC'].
Qed.
Lemma rv_scan : ltac2:(TCodec.tc2 tcn__PmARvC "VG'=&R2vR>&R<&QIvAvRLv@r1%877654321'QA'Q@%15:7654'R7&Ey5'SKyR0%211%5241'5y8%611%311p061'D'4&Q5%211&O'7%12OO%611'QK'QM'3&QBrAr>r=r<r;r:r9r8r7r6r5r4%=?Q<Q;Q:<;:987654321':&R8r?&SJ&RGu1%211%42Q:1%7261%62Q:;%:3Q:21&Q8%11?u:%:11%<2QB1%?2M1%>2QBD%B3QB21rBu;%A11%C2QI1%F241%H3QH17'9&RCz%221Q0&RD&RH+2+J%3221%52Q61%:271%:29Q:'<%Q63RHQ<;%:2<Q>%3221&RA%12QBQA+Q?%>2=1%C231&Q7rF%231QIQH&Q2rG%231QMQL%QD3S6QNI&Q4%11S2%M21R2%?2R3R2&Q1%A241%Q1231%Q3251';&R@(6r2%24SCSC1S;&2&QJrE%211&QErN%211%73RL41%<3RM91%QA2;R9%Q32R:RH%Q42=SG%QD221%QF241%QG261qVFT31%E2T41qW8T51%G2T61%Q@2I1%QA2Q21%RG3T9S2QL&RI&QGrM%211+T0%5221%R421S:%QF2S;S:+\P0%9241%R8231%QN251%QO2=1rQ2r3rLrKrJrIrH%SJ?TITHTG76Q<TF54321QJQMQ8&Q0rQ0%221SA'R;&Q:%11U2&QN%16U3SHSGR5SF>&QDrQ4%211%84U7641p0:1p0>1pVHTD1pQ@TF1pQFTL1pV8U31rQ1%=6U?Q6I1HGrO%=11%C4UBA31p061p0Q11p0Q@1p0RD1p0RH1p0RL1p0S21p0S71p0S91p0SE1p0SL1p0T31p0T61p0TB1pVNV41pW0V51pW:V61pULV71pWJV81pV4U61pW@U81pW<U:1p2U<1pV0U@1pQ8UB1pVLUF1pQDUH1pQJUN1pV6V51pUFV71pNV:1pTLV<1pW6VF1").
Proof. intros pcs SC E X fx Rc Mc modelc LKc crc Ac s sm e v c ra p n.
intros ST R1 RA R10 R11 Hn Hp Hp0 Hpn DEF ACC LOC LOC2 KC.
pose proof ST as (BI & MID & RPRE & STEP & EE & CK & EC).
pose proof BI as (HHc & AMc & MRTc & INCAc & INCLc & ASTKc & EKc & DKc & OWNc & DEFc).
pose proof RPRE as (PA & IA & VIS & VREF & BASE & ERR & TBOK).
pose proof (PMARVK.c_AR L ar HI E X) as AR. unfold PMARVK.rvar in AR. cbn zeta in AR.
destruct AR as ((ARsp1 & ARsp2) & _).
pose proof (PMARVK.c_G L ar HI E X) as XG.
pose proof XG as G'. destruct G' as [GHk GSPT GSLO GSHI GSPC GOCR GOWNAG GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
unfold PMARVK.SCR in *.
pose proof ASTKc as (A16 & SLO & SHI & SPT & SDEF & SUP).
unfold PMSPA.scan_spec in SC.
apply (SC fx Rc Mc modelc (PMARVK.vK E) (PM.parser_own s ++ PMARVK.vLBX E) (PMARVK.FF' E) LKc Ac crc p n (PMARVK.vsp E - 128) ra HHc AMc (PMARVK.c_K0 L ar HI E X)).
- exact (rv_entryA E X _ _ _ _ _ _ _ _ _ _ _ ra 0 ST R1 RA ltac:(lia)).
- exact (rv_room E X _ _ _ _ _ _ _ _ _ _ _ 0 ST ltac:(lia)).
- exact (rv_frs E X).
- rewrite L5K.rl10. exact R10.
- rewrite L5K.rl11. exact R11.
- exact Hn.
- exact Hp.
- exact Hp0.
- exact Hpn.
- exact DEF.
- exact ACC.
- exact (PMASR1.vis_scan L ar C HI LY HIok _ _ _ _ _ _ _ p n HHc LOC).
- change (PMSPA.pm_scr 0) with 12288. exact LOC2.
- exact BASE.
- intros fx' R' M' model' RP' FB' MG' MRT' AM' HH'.
change (PMSPA.pm_scr 0) with 12288 in FB'.
apply (KC fx' R' M' model'); [| exact RP'].
assert (AH : L5CA.ahpres L ar (PM.parser_own s ++ PMARVK.vLBX E) (PMARVK.FF' E) (PMARVK.vsp E - 128) 12288 [] Mc M').
{ apply (PMAUAR.ahpres_of_frame_but L ar C HI LY HIok _ _ _ _ _ Mc M' _ (PMARVK.vsp E - 128) 12288 HHc GSPT); [lia| lia| exact FB'| exact MG'|].
apply (L5.defined_sub Mc (PMARVK.vsp E - 28672) 28672); [exact SDEF| lia| lia]. }
assert (BI' : PMAUK.binv L ar HI (PMARVK.vM E) (PMARVK.vmodel E) (PMARVK.vLBX E) (PMARVK.vFF E) (PMARVK.vLK E) (PMARVK.vAw E) (PMARVK.vsp E) PMARVK.SCR
(PMARVK.vsp E - 128) (PMARVK.own (PMARVK.vsp E) (PMARVK.vR E)) (PMARVK.vF E) 3 (PMARVK.WR E) (PM.parser_own s) M' model' LKc crc Ac).
{ apply (PMAUK.binv_callee L ar C HI HIok (PMARVK.vM E) (PMARVK.vmodel E) (PMARVK.vLBX E) (PMARVK.vFF E) (PMARVK.vLK E) (PMARVK.vAw E) (PMARVK.vsp E) PMARVK.SCR
(PMARVK.vsp E - 128) (PMARVK.vsp E - 104) (PMARVK.vsp E) (PMARVK.ocell (PMARVK.vsp E)) (PMARVK.own (PMARVK.vsp E) (PMARVK.vR E)) (PMARVK.vF E) (PMARVK.vfl E) 3
(PMARVK.vLK2 E) (PMARVK.vM2 E) (PMARVK.vmodel2 E) (PMARVK.vcr E) (PM.parser_own (PMARVK.vs0 E)) XG
(PMARVK.WR E) (PMARVK.WR E) (PM.parser_own s) (PM.parser_own s) (PM.parser_own s) Mc modelc LKc crc Ac M' model' LKc crc Ac 12288 [] BI AH HH' AM' MRT'
(incl_refl _) (incl_refl _)); [clear; lia| unfold PMARVK.SCR; clear; lia| intros rr a [] | intros a _ _ rr []| intros a Xa; exact Xa]. }
set (LB := PM.parser_own s ++ PMARVK.vLBX E) in *.
pose proof (L5SAR.ek_callee L ar LB [] (PMARVK.vFF E) [(PMARVK.vF E, 3, PMARVK.vsp E - 128 + 32)] (PMARVK.vsp E) 28672 (PMARVK.vsp E - 128) 12288 [] [] Mc M' AH
ltac:(clear; lia) ltac:(clear; lia) (fun a _ X0 => X0)) as EKc'.
pose proof (PMARVK.c_FOK L ar HI E X) as ((rs & Hfb) & Fal).
assert (AOF : forall a nn, PMARVK.vfb E + 32 <= a -> a + nn <= PMARVK.vfb E + 1016 -> PMSPA.aobjA (PMARVK.vFF E) a nn).
{ intros a nn Xa1 Xa2. exists (PMARVK.vfb E, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. clear - Xa1 Xa2; lia. }
assert (Eoec : PMARVK.oec E = PMARVK.vfb E + 992) by reflexivity. assert (Eop : PMARVK.op E = PMARVK.vfb E + 464) by reflexivity.
assert (Eois : PMARVK.ois E = PMARVK.vfb E + 96) by reflexivity. assert (Eov : PMARVK.ov E = PMARVK.vfb E + 432) by reflexivity.
pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ (PMARVK.c_HH L ar HI E X)) as FRB.
pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHc) as BRB.
assert (OUT0 : forall i, L5.outside [] i) by (intros i rr []).
assert (PA' : PM.parser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA M' (PMARVK.op E) (PMARVK.ois E) s).
{ apply (PMKA.parser_keepA RSEGS PMA.AD L ar LB (PMARVK.vFF E) (PMARVK.vsp E) 28672 [] Mc M' EKc' PMKA.wapp_nil FRB BRB _ _ _ (AOF (PMARVK.op E) 384 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia)));
[unfold LB; apply incl_appl, incl_refl| intros i _; apply OUT0| intros i _; apply OUT0| intros i _; apply OUT0| intros cc0 nn0 pp0 _ i _; apply OUT0| exact PA]. }
assert (IA' : PM.iss_at RSEGS PMA.AD PMSPA.accA M' (PMARVK.ois E) (PMARVK.vstr E) sm).
{ apply (PMKA.iss_keepA RSEGS PMA.AD L ar LB (PMARVK.vFF E) (PMARVK.vsp E) 28672 [] Mc M' EKc' PMKA.wapp_nil FRB BRB _ _ sm (AOF (PMARVK.ois E) 272 ltac:(clear - Eois; lia) ltac:(clear - Eois; lia)));
[unfold LB; apply incl_appr; exact (PMARVK.c_INCS L ar HI E X)| intros i _; apply OUT0| intros cc0 nn0 pp0 _ i _; apply OUT0| exact IA]. }
assert (VIS' : PMSPA.visitor_at RSEGS PMA.AD M' (PMARVK.ov E)).
{ apply (PMKA.visitor_keepA RSEGS PMA.AD L ar LB (PMARVK.vFF E) (PMARVK.vsp E) 28672 [] Mc M' EKc' PMKA.wapp_nil FRB _ (AOF (PMARVK.ov E) 8 ltac:(clear - Eov; lia) ltac:(clear - Eov; lia)));
[intros i _; apply OUT0| exact VIS]. }
assert (VREF' : L5.u64_at RSEGS M' (PMARVK.op E + 384) (PMARVK.ov E)).
{ apply (PMKA.u64_keepA RSEGS L ar LB (PMARVK.vFF E) (PMARVK.vsp E) 28672 [] Mc M' EKc' PMKA.wapp_nil FRB (PMARVK.op E + 384) _ (AOF (PMARVK.op E + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia)));
[intros i _; apply OUT0| exact VREF]. }
assert (BASE' : PMSTA.base_okA RSEGS PMA.AD M') by (apply (PMASK.base_keep L ar C LY LB (PMARVK.vFF E) (PMARVK.vsp E) 28672 [] Mc M' EKc'); [intros a _; apply OUT0| exact BASE]).
assert (ERR' : PMSTA.err_okA RSEGS PMA.AD PMA.AAD M' e).
{ apply (PMKA.err_okA_keep RSEGS PMA.AD PMA.AAD L ar LB (PMARVK.vFF E) (PMARVK.vsp E) 28672 [] Mc M' EKc' e PMA.addrs_wf_A); [| exact ERR].
intros a D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
split; [exact (PMA.ly_static L C LY a D)| apply OUT0]. }
assert (EC' : PMSPA.ec_at RSEGS M' (PMARVK.oec E) v c).
{ apply (PMKA.ec_keepA RSEGS L ar LB (PMARVK.vFF E) (PMARVK.vsp E) 28672 [] Mc M' EKc' PMKA.wapp_nil FRB _ v c (AOF (PMARVK.oec E) 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia)));
[intros i _; apply OUT0| exact EC]. }
unfold PMARVK.rvst. split; [exact BI'|].
split; [apply (PMARVK.mid_keep E Rc R' MID); intros kk Hkk; apply (L5SAR.cs_of_preserved Rc R' kk RP'); revert kk Hkk; PMARVK.kin|].
split; [unfold PMSPA.run_pre; split; [exact PA'|]; split; [exact IA'|]; split; [exact VIS'|]; split; [exact VREF'|]; split; [exact BASE'|]; split; [exact ERR'| exact TBOK]|].
split; [exact STEP|]. split; [exact EE|]. split; [exact CK| exact EC'].
Qed.
End WithHeap.
End SCFG_1.
End PMARVC.
