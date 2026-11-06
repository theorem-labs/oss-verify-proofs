(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
PmLayout PmLayoutS PmModel PmModelFacts PmStatics PmSpecs PmSpecsS PmStep PmKeep PmKitS PmFrame PmParSpecs PmParSpecsS PmParKit
PmCertKitG PmBaKit PmBaStmts PmBa1 PmBa2 PmBaSP2.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBa4 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBa2.PMBA2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBaStmts.PMBAS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsS.PMS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0B"; "1app"; "1bool"; "1cons"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "3Z"; "0HI"; "0K"; "0L"]; ["0LBX"; "0LBc"; "4Model"; "4VmMaps"; "4m_vmmaps"; "5bvmap"; "0M"; "0M'"; "0M0"; "0M1"; "0M2"; "0R"; "0R'"; "0R0"; "6credit"; "6hi_heap"]; ["6model_but_vm"; "6regs_preserved"; "7agree_on"; "7hpres"; "9defined"; "9ra_ok"; "9range"; "9u64_at"; "8SCFG"; ":push_st"; ";mem_ok"; ";regs_at"; ";saves"; ";world"; "<ADDR_S"; "=inv"]; ["=p_b"; "=p_k"; "=p_src"; "=parser_own"; "=pot_parser"; "=pst"; "=pstate"; "=strm"; ">cfg"; ">credit_keep"; ">ec_at"; ">prog_value"; ">run_pre"; ">src_step"; "?opdel_spec"; "@FPState"]; ["@getr"; "Asrealizes"; "Bloaded_segments"; "0S"; "0SCFG_P"; "Cincl"; "Dadd"; "Dle"; "Dlt"; "Dmul"; "Dof_nat"; "Dpow"; "Dsub"; "0VM"; "0a"; "0c"]; ["0cat"; "0cr"; "0cr0"; "0e"; "0e0"; "0fb"; "0fx"; "0fx'"; "0i"; "0l"; "0len"; "0model"; "0model'"; "0model0"; "0n"; "0ra"]; ["0s'"; "0s0"; "0s1"; "0scr'"; "0sm"; "0sm0"; "0sp'"; "EZ_to_bv"; "Ebv"; "Ebv_unsigned"; "0str"; "0v"; "0w"; "0x"; "0y"]]).
Local Ltac lia := L5FastLia.plia.
Module PMBA4.
Import PMS.
Set Default Proof Using "All".
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation push_st := PMBA2.push_st.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.
Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet).
Variables (LBX : list (Z * Z)) (cr0 : credit) (S r fb cat : Z) (s0 : PM.pst) (str : PM.vstr) (sm0 : PM.strm) (e0 : bool).
Hypothesis PRE : PMBAS.pre L HI R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0.
Hypothesis KONT : PMBAS.kont L HI R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0.
Local Abbreviation kept0 := (PMBAS.kept0 R0).
Local Abbreviation regs_at := (PMBAS.regs_at R0 S fb).
Local Abbreviation saves := (PMBAS.saves R0 S).
Local Abbreviation mem_ok := (PMBAS.mem_ok L M0 LBX S fb).
Local Abbreviation world := (PMBAS.world L HI model0 LBX cr0 fb s0 str sm0 e0).
Local Abbreviation SCR := PMBAS.SCR.
Local Abbreviation CALL := (L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT) (only parsing).
Let MOK0 := PMBA1.MOK0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let FOK := PMBA1.FOK L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let SBND := PMBA1.SBND L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let INV0 := PMBA1.INV0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let fin := PMBA1.fin L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let keep_step := PMBA1.keep_step L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let own_blk := PMBA1.own_blk L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let kept0_of := PMBA1.kept0_of L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let tail_ct := PMBA2.tail_ct L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let tail_i := PMBA2.tail_i L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let push_end_fast := PMBA2.push_end_fast L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Lemma bvu : ltac2:(TCodec.tc2 tcn__PmBa4 "B'S8yR0%211':&R7z&S9r1%2271%5241&R8&R;+2+R0%3221%5271%=271pVJ?1").
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as B. change (bv_modulus 64) with (2 ^ 64) in B. exact B. Qed.
Local Ltac fsc := first [PMK.sc | apply bvu | unfold PMBAP2.aligned; first [assumption | lia]].
Local Ltac prep_ctx M W MO :=
let PA := fresh "PA" in let IA := fresh "IA" in let VIS := fresh "VIS" in let VREF := fresh "VREF" in let BASE := fresh "BASE" in
let ERR := fresh "ERR" in let TB := fresh "TB" in let HH := fresh "HH" in let MB := fresh "MB" in let STEP := fresh "STEP" in
let EE := fresh "EE" in let CK := fresh "CK" in let EK := fresh "EK" in let DK := fresh "DK" in let STK := fresh "STK" in
pose proof W as ((PA & IA & VIS & VREF & BASE & ERR & TB) & HH & MB & STEP & EE & CK);
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v in PA, IA, VIS, VREF; cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutS.ADDR_S] in PA, IA, VIS, VREF;
unfold PMSP.visitor_at in VIS; cbn [pa_vp_visitor AD PmLayoutS.ADDR_S] in VIS;
pose proof MO as (EK & DK & STK);
let MOK := fresh "MOK" in pose proof (PMFR.model_ok_but_vm model0 _ MOK0 MB) as MOK;
let Mh := fresh "Mh" in let Ml := fresh "Ml" in pose proof MOK as (Mh & Ml & _);
let F1 := fresh "F1" in let F2 := fresh "F2" in let F3 := fresh "F3" in pose proof FOK as (F1 & F2 & F3);
let X1 := fresh "X1" in let X2 := fresh "X2" in let X3 := fresh "X3" in let X4 := fresh "X4" in let X5 := fresh "X5" in
pose proof SBND as (X1 & X2 & X3 & X4 & X5);
let WR := fresh "WR" in pose proof (L5C.stk_writable RSEGS _ M S SCR STK) as WR; unfold PMBAS.SCR in WR;
let PDEF := fresh "PDEF" in pose proof PA as (_ & PDEF & _);
let WO := fresh "WO" in assert (WO : L5.writable RSEGS M (fb + 40) 384) by (apply (L5C.writable_of_defined RSEGS); [exact PDEF|lia|lia]);
let IMG := fresh "IMG" in pose proof BASE as (IMG & _); cbn [pa_rw_lo AD PmLayoutS.ADDR_S] in IMG;
let AL1 := fresh "AL1" in assert (AL1 : (fb + 8) mod 8 = 0) by (replace (fb + 8) with (fb + 8 * 1) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3);
let AL5 := fresh "AL5" in assert (AL5 : (fb + 40) mod 8 = 0) by (replace (fb + 40) with (fb + 8 * 5) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3);
let AL54 := fresh "AL54" in assert (AL54 : (fb + 432) mod 8 = 0) by (replace (fb + 432) with (fb + 8 * 54) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
Let Rtp0 := PMBA1.Rtp0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let brx := PMBA1.brx L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let INCS := PMBA1.INCS L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Let K0 := PMBA1.K0 L HI LY HIok R0 M0 model0 K LBX cr0 S r fb cat s0 str sm0 e0 PRE KONT.
Lemma u64_same_agree : ltac2:(TCodec.tc2 tcn__PmBa4 "Q@'S8yR0%211'6y8%511%311p051'<&R7zr2%3221&R6r3+8%3221&R;+2+R0%3221%<251&Q7&R2r6r4%44321<r5%645413&Q4r8%2317@r7%4331B&Q2r:r9%34217Fp051p081p0<1p0?1p0E1p0O1pVHQ41pTNQ51pQDQ71pQ>Q81").
Proof. intros M M1 a v.
intros H1 H2 U U1 D D1 i Hi. unfold L5.u64_at in U, U1.
pose proof (PMBK.rdn_nth RSEGS M 8 a _ H1 ltac:(lia) D U (Z.to_nat (i - a)) ltac:(lia)) as E.
pose proof (PMBK.rdn_nth RSEGS M1 8 a _ H1 ltac:(lia) D1 U1 (Z.to_nat (i - a)) ltac:(lia)) as E1.
rewrite Z2Nat.id in E, E1 by lia. replace (a + (i - a)) with i in E, E1 by lia. rewrite E, E1. reflexivity.
Qed.
Lemma mem_eq_of_frz : ltac2:(TCodec.tc2 tcn__PmBa4 "Q4'S8yR0%211'6y8%511%311p051'<':&R7zr1%3221&R8&R;+2+R0%3221%5271%;271';r3&S7r2%22H1%411r4%113%83G31p0:1pUBG1%;3I8:p021pQDK1pQ>L1").
Proof. intros M M1.
intros F. apply functional_extensionality_dep. intros w. rewrite <- (PMPK.word_id w). apply F. apply bvu.
Qed.
Lemma grow_end_i : ltac2:(TCodec.tc2 tcn__PmBa4 "S3'QO&Ey5'S8yR0%211%5241'6y8%611%311p061'B'QE'QG'2&N&Q;vMvR3vREr7%544321&Q7&R2&R6+\H%2271&S9&R0r8&S7&R:uD%211%42Q11%7261%92Q11%?4>A;1&Q<%13FE:&Q:v?vHv@r9%56432KJ1&Q=v=vRMvRBvS1vS:vS5vRDr:r6r5%;@@:9>8Q676543=LQ521&QJr;+8%Q52Q:1zvR@%65Q95321&Q?%11<&QK%14B9@>'R1&Q8vR4%211&QHr@r?+Vle0r>r=%66QH54321v>%<4QJ921p0>1p0A1p0D1p0L1p0Q91p0Q@1p0QC1p0R41pU4R;1pU8R=1pV:R?1pV2RA1pUHRC1pQ>RE1pQHRK1pU>S21").
Proof. intros fx R M model s' sm e cr.
intros RA C408 SV MO W ECZ INV' PV. pose proof RA as (R2 & R8 & R9 & R18 & KP).
prep_ctx M W MO.
cfeed P (PMBAP2.baI1_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & C1).
assert (EM : M1 = M).
{ apply mem_eq_of_frz. intros i Hi. destruct (PMK.rng_dec i (fb + 40 + 368) (fb + 40 + 368 + 8)) as [In8|Out8]; [|apply FRZ1; [exact Hi| exact Out8]].
apply (u64_same_agree M M1 (fb + 408) (bv_unsigned (getr R (reg 20)))); [lia|lia| exact C408| replace (fb + 408) with (fb + 40 + 368) by lia; exact C1| | |lia].
- apply (L5.defined_sub M (fb + 40) 384); [exact PDEF|lia|lia].
- intros j Hj. apply MG1. apply (L5.defined_sub M (fb + 40) 384 (fb + 408) 8); [exact PDEF|lia|lia|exact Hj]. }
subst M1.
apply (PMK.spiece_ro RSEGS model fx fx1 R 0x372a0 R1 0x372a4 M K Mh Ml MS1).
apply (tail_i fx1 R1 M model s' sm e cr); [| exact SV| exact MO| exact W| exact ECZ| exact INV'| exact PV].
split; [rewrite (KS1 2%nat) by PMK.inl; exact R2|]. split; [rewrite (KS1 8%nat) by PMK.inl; exact R8|].
split; [rewrite (KS1 9%nat) by PMK.inl; exact R9|]. split; [rewrite (KS1 18%nat) by PMK.inl; exact R18|].
apply (kept0_of R R1 _ KS1); [vm_compute; reflexivity| exact KP].
Qed.
Lemma grow_end_ct : ltac2:(TCodec.tc2 tcn__PmBa4 "SF'QO&Ey5'S8yR0%211%5241'6y8%611%311p061'B'QE'QG'2&N'<&Q;vMvR3vREr8%544321';&R0r9&S7&R:uC%211%42M1%7261r2%72N1%;3N31':&R7zr3%3221+`PPP0%5231%7231&Q7&R2r:&R6+\H%22L1&S9r;uE%I11%K2QD1%N241%62QD1%=4<;81&Q<%13Q8Q78&Q:v?vHv@r<%56432Q=Q<1&Q=v=vRMvRBvS1vS:vS5vRDr=%9@>87<6QF54321;HMQAQE&QJr>+8%Q02QJ1vR@%55Q442Q;1&Q?%119&QK%14?8=;'R1&Q8vR4%211&QHrCrB+VmQDrAr@%66QC54321v>%<4QE921p0>1p0A1p0D1p0K1p0Q61p0Q=1p0Q@1p0QO1p0R81p0RE1pUFRL1pU4RN1pU8S01pV:S21pV2S41pUHS61pQ>S81pQHS>1pU>SE1").
Proof. intros fx R M model s' sm e cr len.
intros RA R19 HLn C408 SV MO W ECZ INV' PV. pose proof RA as (R2 & R8 & R9 & R18 & KP).
prep_ctx M W MO.
cfeed P (PMBAP2.baC1s_conc fx R M (fun j => match j with 2%nat => S | 36%nat => fb + 40 | 37%nat => fb + 432 | 38%nat => fb + 8 | _ => 0 end)) ltac:(fsc).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & C1).
assert (EM : M1 = M).
{ apply mem_eq_of_frz. intros i Hi. destruct (PMK.rng_dec i (fb + 40 + 368) (fb + 40 + 368 + 8)) as [In8|Out8]; [|apply FRZ1; [exact Hi| exact Out8]].
apply (u64_same_agree M M1 (fb + 408) (bv_unsigned (getr R (reg 21)))); [lia|lia| exact C408| replace (fb + 408) with (fb + 40 + 368) by lia; exact C1| | |lia].
- apply (L5.defined_sub M (fb + 40) 384); [exact PDEF|lia|lia].
- intros j Hj. apply MG1. apply (L5.defined_sub M (fb + 40) 384 (fb + 408) 8); [exact PDEF|lia|lia|exact Hj]. }
subst M1.
apply (PMK.spiece_ro RSEGS model fx fx1 R 0x37434 R1 0x37438 M K Mh Ml MS1).
apply (tail_ct fx1 R1 M model s' sm e cr len); [| rewrite (KS1 19%nat) by PMK.inl; exact R19| exact HLn| exact SV| exact MO| exact W| exact ECZ| exact INV'| exact PV].
split; [rewrite (KS1 2%nat) by PMK.inl; exact R2|]. split; [rewrite (KS1 8%nat) by PMK.inl; exact R8|].
split; [rewrite (KS1 9%nat) by PMK.inl; exact R9|]. split; [rewrite (KS1 18%nat) by PMK.inl; exact R18|].
apply (kept0_of R R1 _ KS1); [vm_compute; reflexivity| exact KP].
Qed.
Lemma call_keep0 : ltac2:(TCodec.tc2 tcn__PmBa4 "QG'4'8'<%2211%411'S8yR0%211'6y8%511%311p051&Q:v?vHv@vR3vREr4%76654321&Q3r6r3r2(5&Q6%211r5%87?76521:&R5r7%23M@1&R7&R<+jP0%22C1%329B%5221%62AFz%821Cr9%N6MLKJI1p031p061p081p0?1p0C1p0M1pV8Q@1pV>QA1pQFQ81pQ>Q91pQ4QB1").
Proof. intros LBc M M2 sp' scr'.
intros (EK & DK & STK) HP INC H1 H2 H3. pose proof SBND as (X1 & X2 & X3 & X4 & X5).
split; [|split].
- apply (PMK.ek_trans L LBX S SCR _ M0 M M2 EK). intros a (Ha & CA & NE & OW).
apply (L5C.hpres_kept L _ sp' scr' [] M M2 a HP). split; [exact Ha|]. split; [|split; [exact NE| intros r0 []]].
apply (PMK.client_mono L LBX _ S SCR sp' scr' a CA INC). intros x Hx. unfold PMBAS.SCR. lia.
- apply (PMK.dk_trans L LBX S SCR M0 M M2 DK). apply (PMK.dk_callee L LBX _ S SCR sp' scr' [] M M2 HP INC); unfold PMBAS.SCR; lia.
- apply (PMK.stk_after RSEGS L KL _ M M2 S SCR sp' scr' [] STK HP); unfold PMBAS.SCR; lia.
Qed.
Lemma heap_swap2 : ltac2:(TCodec.tc2 tcn__PmBa4 "Q6'8'<%2211'4%112&N'S8yR0%211'6y8%511%311p051'C&Ov=(3r6r5r4%43C21%53D41r3r2r1%;5:4321r7%;3J19%<3K;1%?5>1:76p051pTLB1pQ>D1pU4M1pUDO1pVNQ21pVLQ31").
Proof. intros x y l cr M VM.
intros HH. apply (hio_perm L SCFG HI HIok _ _ cr M VM HH).
- intros z. cbn [In]. split; intros [E|[E|E]]; auto.
- pose proof (PMPK.heap_nodup L HI HIok _ cr M VM HH) as ND. cbn [map] in ND |- *. apply PMCG.nodup_swap. exact ND.
Qed.
Lemma grow_del : ltac2:(TCodec.tc2 tcn__PmBa4 "VI'<'QO&Ey5'S8yR0%211%5241'6y8%611%311p061'B'QE'QG'2&N'QF';&R0r9&S7&R:u1%211%42G1%7261r;%72H1%;3H31&Q5r<%211&Q;vMvR3vRE%44321:u:%A11%C2Q61%F2:1&Q@%11G%G2Q81%K3Q841&Q<%13=<@&Q:v?vHv@r=%56432BA1&QL&R2&Q>r>&Q9r8&R6&QA%11O+1%4221r7%84Q3721vS:r:%?8>=<Q132Q:1&Ov=(3'8%12R;R;(7&R9+Q0&R;+2%C1L%E21B%4231%7261%94RERER01&1&QC%11Q3%33>1Q5%A3?51r?&D%11Q3%G5F4I31&Q0vRM%2216&QM&QBvS1%211%31;vS5%64321Q>vRD(9%RH3RK21%RI3RLA2p021&QIvRB&QD%12QO=rA%QE11%QG21QD%QJ43R01RE%62R41%948QM61&QJrD+8%QN2RF1zvR@%65R65321&R7rC%R311%3261&QNvR4%231RCQM&Q1rLr3%3221%RK3S7S62r4%RK6RJRIRHS8S71&Q=r5rH%RB19%RD21RArG%RH4<421rKrJrI%:@S5R?QGS3Q8SBQCRCQ@Q>9<4321r6%Q15S11NML&R<+S@%22SH1r2%O221%S22G2+R0%RB2RA1%Q3231&Q2rQ4%241T9JMp041p091pUNU81pTNU91'R1&Q8%11Q8&QH%16SFS9TI:SBS<v>%64SH421p081p0I1p0L1p0Q81p0Q;1p0Q=1pUJU:1pQ@U<1pQJUB1pU@UI1+ZaP0%?6T4Q7Q61Q=Q:%C4T5A1>p041p0QJ1p0QN1p0R31p0R;1p0RF1p0RL1p0S41p0S81p0T11p0TB1p0TI1p0TL1p0U51p0U;1p0U?1pU0UL1p2V?1pU4UO1pU8V11pV:V31pV6V51pUHV71pQ>V91pQHV?1pU>VF1pV0VH1").
Proof. intros ra fx R M model s1 sm e cr B c.
intros X1r RAra (R2 & R8 & R9 & R18 & KP) X10 SV MO RP HH MB STEP EE CK ECZ Hk0 OPD KNT.
pose proof MO as (EK & DK & STK).
pose proof (PMFR.model_ok_but_vm model0 _ MOK0 MB) as MOK. pose proof FOK as (F1 & F2 & F3). pose proof SBND as (X1 & X2 & X3 & X4 & X5).
destruct s1 as [mo1 dn1 dp1 [qc de rem] tb1 tg1 vb1 vk1 stk1]. cbn [PM.p_b PM.p_k PM.p_src] in *.
set (n := 32 * 2 ^ (vk1 + 1)) in *.
set (LBn := (B, n) :: PM.parser_own (PM.PST mo1 dn1 dp1 (PM.SRC qc de rem) tb1 tg1 vb1 vk1 stk1) ++ LBX) in *.
assert (Hin : In (vb1, 32 * 2 ^ vk1) LBn) by (unfold LBn, PM.parser_own, PM.vec_own; cbn; right; right; left; reflexivity).
pose proof (PMPK.heap_nodup L HI HIok _ cr M _ HH) as ND. unfold LBn, PM.parser_own, PM.src_own, PM.vec_own in ND. cbn [map fst app] in ND.
assert (NB : B <> vb1). { intros E. subst B. inversion ND as [|? ? N1 _]. apply N1. apply PMPK.elem_of_In. cbn. right. left. reflexivity. }
assert (NQ : qc <> vb1). { intros E. subst qc. inversion ND as [|? ? _ ND1]. inversion ND1 as [|? ? N2 _]. apply N2. apply PMPK.elem_of_In. cbn. left. reflexivity. }
assert (LR : lb_remove vb1 LBn = (B, n) :: (qc, 16384) :: PM.vs_own tb1 ++ LBX).
{ unfold LBn, PM.parser_own, PM.src_own, PM.vec_own, PM.CHUNK. cbn.
destruct (Z.eqb_spec B vb1) as [E|_]; [exfalso; exact (NB E)|].
destruct (Z.eqb_spec qc vb1) as [E|_]; [exfalso; exact (NQ E)|].
destruct (Z.eqb_spec vb1 vb1) as [_|E]; [reflexivity| exfalso; exact (E eq_refl)]. }
assert (STKc : L5C.stk (hl_sptop L) M (S - 112) PMSP.OPDEL_SCR).
{ apply (PMK.stk_call L M S SCR (S - 112) PMSP.OPDEL_SCR STK); unfold PMBAS.SCR, PMSP.OPDEL_SCR; [lia|lia|lia|]. replace (S - 112) with (S + (-7) * 16) by lia. rewrite Z.mod_add by lia. exact X4. }
unfold PMS.opdel_spec, PMSP.opdel_spec, PMSP.opdel_spec_at in OPD. cbn [pa_opdel AD PmLayoutS.ADDR_S] in OPD.
apply (OPD fx R M model K LBn cr vb1 (32 * 2 ^ vk1) (S - 112) ra HH MOK K0 Hin).
{ rewrite L5K.rl10. exact X10. } { rewrite L5K.rl1. exact X1r. } { exact RAra. } { rewrite L5K.rl2. exact R2. }
{ rewrite L5K.rl4. rewrite (KP 4%nat) by PMK.inl. exact Rtp0. } { exact STKc. }
intros fx2 R2' M2 model2 RP2 HP2 MB2 HH2.
rewrite LR in HP2, HH2.
set (LBr := (B, n) :: (qc, 16384) :: PM.vs_own tb1 ++ LBX) in HP2, HH2.
assert (INCr : incl LBX LBr) by (intros x Hx; unfold LBr; right; right; apply in_or_app; right; exact Hx).
assert (MO2 : mem_ok M2) by (apply (call_keep0 LBr M M2 (S - 112) PMSP.OPDEL_SCR MO HP2 INCr); unfold PMSP.OPDEL_SCR; lia).
assert (EKc : PMK.ek L LBr (S - 112) PMSP.OPDEL_SCR [] M M2) by (apply (PMK.ek_of_hpres L); exact HP2).
assert (SCc : 0 <= PMSP.OPDEL_SCR) by (unfold PMSP.OPDEL_SCR; lia).
assert (BRr : PMFR.brange L LBr) by (apply (PMFR.brange_of_heap L HI HIok LBr LBr cr M2 _ HH2); apply incl_refl).
assert (WHI0 : forall a, PMK.inW [] a -> S - 112 <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; destruct (PMFR.inW_nil a I)).
assert (NW : forall a n0, forall i, a <= i < a + n0 -> ~ PMK.inW [] i) by (intros a n0 i _ I; exact (PMFR.inW_nil i I)).
assert (AGH : forall a n0, S - 112 <= a -> a + n0 <= 2 ^ 64 -> L5C.agree_on M M2 a n0).
{ intros a n0 H1 H2. apply (PMPK.ag_hi RSEGS L KL LBr (S - 112) PMSP.OPDEL_SCR [] M M2 EKc STKc SCc a n0 H1 H2). apply NW. }
set (s' := push_st (PM.PST mo1 dn1 dp1 (PM.SRC qc de rem) tb1 tg1 vb1 vk1 stk1) B (vk1 + 1) c) in *.
assert (OWNr : incl (PM.parser_own s') LBr).
{ unfold s', push_st, PM.parser_own, PM.src_own, PM.vec_own, PM.CHUNK, LBr. cbn [PM.p_src PM.p_b PM.p_k PM.p_tb PM.sr_qc app].
intros x [<-|[<-|Hx]]; [right; left; reflexivity| left; reflexivity| right; right; apply in_or_app; left; exact Hx]. }
destruct RP as (PA & IA & VIS & VREF & BASE & ERR & TB).
unfold PMSP.o_p, PMSP.o_is, PMSP.o_v in PA, IA, VIS, VREF. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutS.ADDR_S] in PA, IA, VIS, VREF.
apply (KNT fx2 R2' M2 model2 RP2).
- pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64).
unfold PMBAS.saves. repeat split; (apply (L5C.u64_at_agree RSEGS M M2); [apply AGH; lia|lia|lia|assumption]).
- exact MO2.
- split; [|split; [|split; [apply (L5C.model_but_vm_trans _ _ _ MB MB2)|split; [exact STEP|split; [exact EE| exact CK]]]]].
+ unfold PMSP.run_pre, PMSP.o_p, PMSP.o_is, PMSP.o_v. cbn [pa_off_p pa_off_is pa_off_v AD PmLayoutS.ADDR_S].
split. { apply (PMFR.parser_keep RSEGS AD L KL LBr (S - 112) PMSP.OPDEL_SCR [] M M2 EKc STKc SCc BRr WHI0); [lia|lia| apply NW| exact OWNr| exact PA]. }
split. { apply (PMFR.iss_keep RSEGS AD L KL LBr (S - 112) PMSP.OPDEL_SCR [] M M2 EKc STKc SCc BRr WHI0); [lia|lia| apply NW| | exact IA].
intros x Hx. apply INCr. apply INCS. exact Hx. }
split. { apply (L5C.u64_at_agree RSEGS M M2); [apply AGH; lia|lia|lia| exact VIS]. }
split. { apply (L5C.u64_at_agree RSEGS M M2); [apply AGH; lia|lia|lia| exact VREF]. }
split.
{ apply (PMKP.base_ok_keep RSEGS AD L KL SF LBr (S - 112) PMSP.OPDEL_SCR [] M M2 EKc); [| | | | exact BASE].
all: intros a _; apply PMFR.outside_of_not_inW; apply PMFR.inW_nil. }
split; [|exact TB].
{ apply (PMKP.err_ok_keep RSEGS AD L KL SF LBr (S - 112) PMSP.OPDEL_SCR [] M M2 EKc); [| | exact ERR].
all: intros a _; apply PMFR.outside_of_not_inW; apply PMFR.inW_nil. }
+ unfold s', push_st, PM.parser_own, PM.src_own, PM.vec_own, PM.CHUNK. cbn [PM.p_src PM.p_b PM.p_k PM.p_tb PM.sr_qc app].
apply heap_swap2. exact HH2.
- apply (PMBK.ec_agree RSEGS M M2); [apply AGH; lia|lia|lia| exact ECZ].
- exact AGH.
Qed.
End Call.
End WithHeap.
End PMBA4.
