(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim StoreOk ShapeAlg SpinAlg AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__As0DrvKitA () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.As0DrvKitA.FPX_1.KitA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1Some"; "1bool"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2eq"; "3Z"; "0E"; "0H"; "4store_ok"]; ["5mkCfg"; "6Model"; "6m_halted"; "6m_vm_lazy"; "7bvmap"; "0M"; "0M'"; "0MV'"; "0R"; "0R'"; "8lzinv"; "9A_wf"; "9H_off_segments"; "9MInv"; "9lazy_cover"; "9mrestrict"]; ["9munrestrict"; "9same_but_materialized"; "9wx_segs_nowrap"; ":msteps"; ";mkst"; ";rdn"; ";seg_rom"; "<TSet"; "=srealizes"; ">SS"; ">carry"; ">env"; ">expr"; ">kentry"; ">s_log"; ">s_pc"]; [">s_regs"; ">scripts"; ">sentry"; ">sidecond"; ">sym_exec"; ">sym_state"; "?know_ok"; "?mem_denot"; "?regs_ok"; "?scs_denot"; "0T"; "0a"; "0b"; "0bs"; "0fuel"; "0fx"]; ["0hs2"; "0kn"; "0kn'"; "0m"; "0m'"; "0model"; "0model'"; "0n"; "0nx"; "0pc"; "0pc'"; "0scfg"; "0scr"; "0scr'"; "0scs"; "0scs2"]; ["0segs"; "0sr"; "0ss'"; "@Z_to_bv"; "@bv"; "0stops"]]).
Section FPX_1. Context {fx : PropExec.FPState}.
Section KitA.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Lemma mrestrict_munrestrict : ltac2:(TCodec.tc2 tcn__As0DrvKitA "Q1'RDyR0%211'3p021'7y8%711%311p071';r4r1%211(:%53<21r3r2%211(1%11=%;3=31p071pSHE1&O&Q0%13?:9%32@1%B3C1;p061pQ>E1pQ<F1pNL1").
Proof.
intros H M M' Hc. apply functional_extensionality. intros a. unfold mrestrict, munrestrict.
destruct (H a) eqn:E; [symmetry; apply Hc; exact E | reflexivity].
Qed.
Theorem rz_run_lz : ltac2:(TCodec.tc2 tcn__As0DrvKitA "V3'RDyR0%211'3p021'4'9'<%2211%411'5%614'QA'Q<%911'Q=%;11'QE'QC%>11%?1A'Q;'7y8%H11%311p0H1&Dy5%221K'A&Q7&LvR@rD%3221&Q2%114&NrF&Cr4%211rE%63521&K%117'MrGr6%3221';%Q>2Q3Q1%Q?21Q9&QD(:(Q9rC(6'QB%211rBrA%75M6321%61Q>%;7Q0A:JF21(8r@r?%34QDQB21r>%54CQK21%E3C71%R32QIQF%R421QF&Q:&Q>%11?%D1R;%432F1r=%?4R1QN;1r<%A4:QO21%Q13:51&QHr:%235Q<1&QF&OrL%2219%44QK<1QA&QIrM%621?%34QO1JQ7rN%921L%64R21OQ5%R>1S2&B%11F(1%11S6%QF3531&Q@rJ%211r3%I3R<21rH%H4R?R531&QGrQ5%J21R8%Q81J%43R>21%R33RLR=1rQ6&Q0r5%233RC1%Q2241%R93S213%R>264&Q1%12RHR>'Q8vR;(@&Q4vQOr9&RC&Q?rQ0%211%42T91rQ9rIr8%F3321&Q6%11S?%>5=<731r7%A221%D4SCC1S=p0F1p0I1p0K1p0Q21p0Q91p0Q<1pT>SM1pQ@T21pQDT01%H2TMR4%L5KRL1S1?%N21RL%Q14T0Q01RKp051p0QJ1p0R11p0R51p0R:1p0R@1p0RD1p0S11p0SH1p0SM1p0T01p0T81p0T;1pSFT@1pT<TB1pQBTD1pQ<TH1pLTN1pT2U01pU0U21pT6U61pTLU;1pTNU51pU6U81pTBU@1pT4U;1pU4U>1pTDUF1pTJUB1pU<UD1pSNUF1p2UH1pNUN1").
Proof.
intros H A fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M R model T
HH Hwx HL HA HI Hex Hc HR HK Hsc Hsc2 Hh Hcont.
destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E (mrestrict H M) (seg_rom segs) R Hex HR HK Hsc)
as (R' & HR' & Hlf & Hms).
apply (srz_msteps_restricted_T segs scfg H HH Hwx A (mkst R (Z_to_bv 64 pc) M (seg_rom segs)) _ model T HL HA HI Hh Hms).
intros model' HI' HS HC.
change (unrestrict H (ms_mem (mkst R (Z_to_bv 64 pc) M (seg_rom segs)))
(mkst R' (Z_to_bv 64 (s_pc ss')) (mem_denot E (mrestrict H M) (s_log ss')) (seg_rom segs)))
with (mkst R' (Z_to_bv 64 (s_pc ss')) (munrestrict H M (mem_denot E (mrestrict H M) (s_log ss'))) (seg_rom segs)).
apply (Hcont R' _ model' HR'); [ | reflexivity | | exact HI' | exact HS].
- eapply carry_after; eassumption.
- apply mrestrict_munrestrict. intros a Ha. exact (HC a Ha).
Qed.
Theorem rz_msteps_lz : ltac2:(TCodec.tc2 tcn__As0DrvKitA "S9'RDyR0%211'3p021'4'9'<%2211%411&Dy5%221:'7y8%?11%311p0?1'A&Q7&LvR@r:%3221&Q2%114&Nr<&Cr4%211r;%63521&K%117'Mr=r6%3221';%K1Q6&Br7%211(1%11Q;%73631'Q3&Q4vQOr>&Or@%221J&Q6%11Q2%8576D31r9%:59KQ413%<3Q631rAr1%K221&Q1r2%22Q21rD&Q0%132@Q0%B231%O3QE1Q2'Q8vR;(@r?rE%931@J%M5LI31F%521QA%84QJ71QDp0:1p0@1p0D1pT>R11%Q45Q3Q0:Q2M%<21QO%?4R1>1Mp041p0M1p0Q;1p0QD1p0QI1p0QL1p0R41p0R71pSFR<1pT<R>1pQ@R@1pTFS01pQDRG1pQ<RC1pTDS31pQBRJ1p2RN1pNS41").
Proof.
intros H A R pc M R' pc' MV' model T HH Hwx HL HA HI Hh Hms Hcont.
apply (srz_msteps_restricted_T segs scfg H HH Hwx A (mkst R pc M (seg_rom segs)) _ model T HL HA HI Hh Hms).
intros model' HI' HS HC.
change (unrestrict H (ms_mem (mkst R pc M (seg_rom segs))) (mkst R' pc' MV' (seg_rom segs)))
with (mkst R' pc' (munrestrict H M MV') (seg_rom segs)).
apply (Hcont model' HI' HS). apply mrestrict_munrestrict. intros a Ha. exact (HC a Ha).
Qed.
Definition lzinv (H : word -> bool) (A : list (Z * Z)) (model : Model) : Prop :=
H_off_segments segs H /\ lazy_cover H (m_vm_lazy model) A /\ A_wf A /\ MInv A model /\ m_halted model = None.
Lemma sbm_lazy_eq : ltac2:(TCodec.tc2 tcn__As0DrvKitA "E'A&Q1r2r1%3221';'4'9'RDyR0%211%4211%611&C%11<r3%311%<3531p0>1pT:C1pT8D1").
Proof. intros m m' ->. destruct m as [fd [maps lazy mat] io fsy pr lim tm]. reflexivity. Qed.
Lemma sbm_halted_eq : ltac2:(TCodec.tc2 tcn__As0DrvKitA "C'A&Q1r2r1%3221';'7'RDyR0%211%411&B%11:r3%311%:3531p0<1pT:A1pT8B1").
Proof. intros m m' ->. destruct m as [fd [maps lazy mat] io fsy pr lim tm]. reflexivity. Qed.
Lemma lzinv_sbm : ltac2:(TCodec.tc2 tcn__As0DrvKitA "N'RDyR0%211'3p021'4'9'<%2211%411'A&Jr4r3r2%43321'M%1253&Q1%1276r7r6%;321:p041p071p0:1pT>@1pT<A1p2C1pNI1").
Proof.
intros H A model model' (H1 & H2 & H3 & _ & H5) HI HS.
split; [exact H1|]. split; [rewrite (sbm_lazy_eq _ _ HS); exact H2|]. split; [exact H3|]. split; [exact HI|].
rewrite (sbm_halted_eq _ _ HS); exact H5.
Qed.
Lemma mrestrict_some : ltac2:(TCodec.tc2 tcn__As0DrvKitA "L'RDyR0%211'3p021'7y8%711%311p071';&Or4r3r2%43321(2r1%22;1%93;41%817%52>7%<3>21p041pSJA1pSHG1pQ<A1pNG1").
Proof. intros H M a b. unfold mrestrict. destruct (H a); [discriminate | auto]. Qed.
Lemma store_ok_of_mrestrict : ltac2:(TCodec.tc2 tcn__As0DrvKitA "N'RDyR0%211'3p021'7y8%711%311p071'5';&?vR@&Or4r3%3221r1r2%847321(:%;3C21%;4:847%=3E13p031pSHH1pT@A1pQ<C1pNI1").
Proof.
intros H M n. induction n as [|n IH]; intros a Hs; [reflexivity|]. cbn [store_ok] in *.
unfold wview in *. unfold mrestrict in Hs at 1. destruct (H a) eqn:EH.
- destruct (M a) as [b|]; [apply IH | ].
+ destruct (find_segment segs (bv_unsigned a) 1) as [sg|]; [|discriminate]. destruct (seg_writable sg); [|discriminate].
destruct (segment_byte_at _ _); [exact Hs | discriminate].
+ destruct (find_segment segs (bv_unsigned a) 1) as [sg|]; [|discriminate]. destruct (seg_writable sg); [|discriminate].
destruct (segment_byte_at _ _); [apply IH; exact Hs | discriminate].
- destruct (M a) as [b|]; [apply IH; exact Hs|].
destruct (find_segment segs (bv_unsigned a) 1) as [sg|]; [|discriminate]. destruct (seg_writable sg); [|discriminate].
destruct (segment_byte_at _ _); [apply IH; exact Hs | discriminate].
Qed.
Lemma rdn_of_mrestrict : ltac2:(TCodec.tc2 tcn__As0DrvKitA "Q9'RDyR0%211'3p021'7y8%711%311p071&LvR@r2%3221'5'4%119';%=12&Q5&Or6r5%3221r3%64>2=1(2r1%22<1%<3;41r4%<4D:71%62@D%@3?21p051pSLC1pSHQ21pT@G1p0I1pQ<N1pNQ41").
Proof.
intros H M HH n. induction n as [|n IH]; intros a bs Hr; [exact Hr|]. cbn [rdn] in *.
unfold mrestrict in Hr at 1. destruct (H a) eqn:EH.
-
exfalso. unfold seg_rom, memory_read in Hr. change (Z.of_N 1) with 1 in Hr. rewrite (HH a EH) in Hr. discriminate.
- destruct (M a) as [b|].
+ destruct (rdn segs (mrestrict H M) (a + 1)%bv n) as [r|] eqn:E2; [|discriminate]. rewrite (IH _ _ E2). exact Hr.
+ destruct (seg_rom segs a) as [b|]; [|discriminate].
destruct (rdn segs (mrestrict H M) (a + 1)%bv n) as [r|] eqn:E2; [|discriminate]. rewrite (IH _ _ E2). exact Hr.
Qed.
Theorem rz_run_lz2 : ltac2:(TCodec.tc2 tcn__As0DrvKitA "UF'RDyR0%211'3p021'4'9'<%2211%411'5%614'QA'Q<%911'Q=%;11'QE'QC%>11%?1A'Q;'7y8%H11%311p0H1&Dy5%221K'A&Q7&Q2vR@%211&JrErDr3%43321';%Q32HF%Q421N&QD(:rCrB(Q9rAr@(6'QB%211r?r>%8576321%61Q6%>7HD=<;21(8r=r<%34Q<Q:21r;%54FQC21%H3F71%QK2QAQ>%QL21Q>&Q:&Q>%11?%D1R3%432F1r:%?4QIQF;1r9%A4:QG21%Q43:51&QHr7%235Q11&QF&OrI%2219%44QC<1Q6&QIrJ%621?%34QG1JQ7rK%921L%64QJ1OQ5&Q@rF%211%B3Q>1QIrQ0%@21QK%B4R1QB1QMrQ1r4%D221&QG%F24QGrH%Q511%43QL31%R33RA61rQ3r1%211%R73S<1R3r2%Q311%R=12%R;3RJ21p051pSHSC1rQ2r5%RE3<21&Q1r6%22R=1'Q8vR;(@&Q4vQO&RC&Q?rL%211%42T41r8&Q6%11S7%:59QO431%<21QL%?4S:>1RMp0A1p0E1p0I1p0Q41p0Q>1p0QB1pT>SD1pQ>SI1pQDSG1%D2TDQ=%G5FRJ1RK>%I21RI%L4SGK1R@p051p0QO1p0R31p0R81p0R>1p0RB1p0RO1p0SI1p0SO1pSFT31pT<T51pQBT71pQ<T;1pLTA1pT2TC1pU0TE1pT6TI1pTLTN1pTNTH1pU6TK1pTBU31pT4TN1pU4U11pTDU91pTJU51pU<U71pSNU91p2U;1pNUA1").
Proof.
intros H A fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M R model T Hwx HZ Hex Hc HR HK Hsc Hsc2 Hcont.
pose proof HZ as (H1 & H2 & H3 & H4 & H5).
apply (rz_run_lz H A fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M R model T H1 Hwx H2 H3 H4 Hex Hc HR HK Hsc Hsc2 H5).
intros R' MV' model' HR' HK' EQ EQV HI' HS.
apply (Hcont R' (munrestrict H M MV') model' HR').
- rewrite EQV. exact HK'.
- rewrite EQV. exact EQ.
- intros a Ha. unfold munrestrict. rewrite Ha. reflexivity.
- exact (lzinv_sbm H A model model' HZ HI' HS).
- exact HS.
Qed.
End KitA.
End FPX_1.
Ltac run_block_lz_with HR HK HZ Hwx fuel stops scr NX keep :=
lazymatch type of HR with
| regs_ok ?E ?sr ?R =>
lazymatch type of HK with
| know_ok ?segs _ (mrestrict ?H ?M) ?kn =>
lazymatch type of HZ with
| lzinv _ _ ?A ?model =>
lazymatch goal with
| |- srealizes _ ?scfg (mkCfg (mkst R (Z_to_bv 64 ?pc) M _) model) ?T =>
let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn NX) []) in
lazymatch r with
| (?ss', ?scs, ?scr') =>
let c := eval vm_compute in (carry (s_log ss') kn []) in
lazymatch c with
| (?kn', ?scs2, ?hs2) =>
eapply (rz_run_lz2 segs scfg H A fuel stops scr pc sr kn NX ss' scs scr' kn' scs2 hs2 E M R model T Hwx HZ);
[ vm_compute; reflexivity
| vm_compute; reflexivity
| exact HR | exact HK
| split_foralls
| split_foralls
| let R' := fresh "R" in let M' := fresh "M" in let model' := fresh "model" in
let EQM := fresh "EQM" in let EQH := fresh "EQH" in let SBM := fresh "SBM" in
let HR' := fresh "HR" in let HK' := fresh "HK" in let HZ' := fresh "HZ" in
intros R' M' model' HR' HK' EQM EQH HZ' SBM; cbn [s_pc s_regs s_log] in HR', EQM |- *;
lazymatch keep with
| true => idtac
| false => clear EQM EQH SBM HR HK HZ; try clear R; try clear M; try clear model;
try rename R' into R; try rename M' into M; try rename model' into model;
rename HR' into HR; rename HK' into HK; rename HZ' into HZ
end ]
end
end
end
end
end
end.
