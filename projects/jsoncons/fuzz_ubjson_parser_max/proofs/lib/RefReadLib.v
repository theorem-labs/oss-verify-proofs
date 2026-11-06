(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg
SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX Frame RefMemcpyLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__RefReadLib () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefReadLib.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "2and"; "2eq"; "2or"; "3Forall"; "3firstn"; "3skipn"; "4Z"; "0E"; "0K"]; ["5len_word"; "5word_to_nat"; "6file_read"; "7Segment"; "8word_to_le_bytes"; "0M"; "9wbytes"; ":rdn"; ";kfoot_far"; "<SE"; "<adenot"; "<edenot"; "<env"; "<expr"; "<kentry"; "<saddr"]; ["<sentry"; "=kentry_ok"; "=know_ok"; "=mem_denot"; ">add"; ">le"; ">lt"; ">of_nat"; ">pow"; ">to_nat"; "0a"; "0bs"; "0cnt"; "0data"; "0kn"; "0m"]; ["0off"; "0segs"; "?Z_to_bv"; "?bv"; "?bv_unsigned"; "0v"; "0w"; "0x"; "0z"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.
Definition kfootprint (E : env) (K : kentry) : option (Z * Z) :=
match K with
| KWord a w _ => Some (estart E a, Z.of_nat w)
| KZero a n => Some (estart E a, elenZ E n)
| KBlob a n _ => Some (estart E a, elenZ E n)
| KImg lo hi => Some (lo, hi - lo)%Z
| _ => None
end.
Definition kfoot_far (E : env) (K : kentry) (wa wn : Z) : Prop :=
match kfootprint E K with
| None => True
| Some (s, n) => (s + n <= wa \/ wa + wn <= s)%Z
end.
Lemma wbytes_same_far : ltac2:(TCodec.tc2 tcn__RefReadLib "QC'QCyR0%211'6y8%511%311p051'3%114&Q5&Q4&QDr3%22=1&Q7&2r2%22=1%411%9261&Q8+2+R0%3221%?251'9%?2J:+1%B221r4%C2N1%F231%A2LD%C11%H241%J219%;251'8&Fr6r5%3421<M%31N%63Q621p081p0E1pS@Q=1pRHQ71pRFQ?1pS0Q;1").
Proof.
intros m a bs x Hnw Hfar. apply wbytes_outside; [|exact Hnw]. unfold in_rng. lia.
Qed.
Lemma kentry_ok_wbytes_far : ltac2:(TCodec.tc2 tcn__RefReadLib "QG'3'C%211'L'QCyR0%211'6y8%511%311p051%<13'N&Q5&Q4&QDr3%22=1&Q7&2r2%22=1%411%9261&Q8+2+R0%3221%?251&Hr6r4%A2L1%>2IA%@11%645?31&Q1r8r7%34219Gr9&Fr5%235=1%84471=p061p0;1p0C1pQ0Q41pRHQ61pRFQ=1pQ<Q91pNQB1pS4QD1").
Proof.
intros segs E M a bs K Hnw Hfar HK.
destruct K as [[b k] w v|[b k] n|[b k] n bk|lo hi|e m|e lo hi|[b k] n|a1 n1 a2 n2];
cbn [kfoot_far kfootprint kentry_ok] in *; try exact HK.
- destruct HK as (Hw & Hfl & Hr). split; [exact Hw|]. split; [exact Hfl|].
rewrite <- Hr. pose proof (flat_u E _ _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
apply rdn_agree. intros j Hj. rewrite Hu. apply wbytes_same_far; [exact Hnw|].
rewrite u_small by lia. unfold estart in *. cbn [a_base a_off] in *. lia.
- destruct HK as (Hfl & Hz). split; [exact Hfl|]. intros i Hi.
destruct Hfl as (F1 & F2 & F3 & F4).
rewrite wbytes_same_far; [apply Hz; exact Hi | exact Hnw |]. rewrite u_small by lia. lia.
- destruct HK as (Hfl & Hlen & Hz). split; [exact Hfl|]. split; [exact Hlen|]. intros i Hi.
destruct Hfl as (F1 & F2 & F3 & F4).
rewrite wbytes_same_far; [apply Hz; exact Hi | exact Hnw |]. rewrite u_small by lia. lia.
- destruct HK as (H0 & H64 & Hnone). split; [exact H0|]. split; [exact H64|]. intros i Hi.
rewrite wbytes_same_far; [apply Hnone; exact Hi | exact Hnw |]. rewrite u_small by lia. lia.
- destruct HK as [Hfl Hst]. split; [exact Hfl|]. intros d m Hd Hm.
eapply store_ok_mono; [apply wbytes_grows|]. apply Hst; assumption.
Qed.
Lemma know_ok_wbytes_far : ltac2:(TCodec.tc2 tcn__RefReadLib "QL'3'C%211'L'QCyR0%211'6y8%511%311p051%<13'N%>11&Q5&Q4&QDr3%22>1&Q7&2r2%22>1%411%9261&Q8+2+R0%3221%?251':&Hr7r1r5%C2O1r4%A2M1%C11%847641qQ0L1%;3M1D&Q2r8r6%342=1Lr9&F%13@4>%74361=p051p0:1p0G1pRNQ81pRHQ;1pRFQB1pQ<Q>1pNQG1pS4QI1").
Proof.
intros segs E M a bs kn Hnw Hfar HK. unfold know_ok in *.
induction kn as [|K rest IH]; [constructor|].
apply Forall_cons_iff in Hfar as [F1 F2]. apply Forall_cons_iff in HK as [K1 K2].
constructor; [eapply kentry_ok_wbytes_far; eassumption | apply IH; assumption].
Qed.
Lemma wbytes_nil' : ltac2:(TCodec.tc2 tcn__RefReadLib "B'QCyR0%211'6y8%511%311p051'8&Fr2r1(5%118%53431%73815pRF>1pS0:1").
Proof. reflexivity. Qed.
Lemma mem_denot_1 : ltac2:(TCodec.tc2 tcn__RefReadLib "Q9'L'QCyR0%211'6y8%511%311p051'O'4'M'8&Q3r5r4(1'Q0(Ir3r2r1%43321(5%117%93831%=3<;1&F&J%12?:&D&K%12B;%32=1%73C51%G3K91pS<I1pS>K1pRFM1pQ<O1pNQ81").
Proof. reflexivity. Qed.
Lemma mem_denot_nil : ltac2:(TCodec.tc2 tcn__RefReadLib "D'L'QCyR0%211'6y8%511%311p051'8&Q3r2r1(5'Q0%211%63541%83915pQ<:1pNC1").
Proof. reflexivity. Qed.
Lemma rdn_wbytes_self : ltac2:(TCodec.tc2 tcn__RefReadLib "Q>'3'C%211'QCyR0%211'6y8%511%311p051%;13&Q5&Q4&QDr2%22<1&Q7&2r1%22<1%411%9261&Q8+2+R0%3221%?251'8%G1B&Gr5&Fr4r3%3321D%B2LE%746231(0%12LH%<3;31p0>1pRHO1pRFQ61pS0Q21pS4Q;1").
Proof. intros. apply rdn_wbytes_hit. assumption. Qed.
Lemma word_to_nat_lit : ltac2:(TCodec.tc2 tcn__RefReadLib "J'='7&Q5zr1%3221&Q6&Q8+2+R0%3221%5271%;271'8'4&A&QByR0r2%3221%511&Q9%114%:3931p0<1pSBI1").
Proof. intros z Hz. unfold word_to_nat. rewrite u_small by lia. reflexivity. Qed.
Lemma file_read_all : ltac2:(TCodec.tc2 tcn__RefReadLib "Q3'3'QCy8%211%411'='7&Q5&Q7&2r2%2281%411r1%7221&Q6&Q8+2+R0%3221%5271%?271'8&Br3&QByR0z%3221%423C%73621%93K17p0;1pRJL1pRLN1").
Proof.
intros data cnt Hc. rewrite file_read_unguarded. rewrite !word_to_nat_lit by lia. cbn [Z.to_nat skipn].
apply firstn_all2. lia.
Qed.
Lemma file_read_eof : ltac2:(TCodec.tc2 tcn__RefReadLib "L'3'QCy8%211%411yR0%511&Q5&Q7&2r3%2281%411&QDr2%22:1%9241'8&Br4%231:6(5%11C%63C31p081pRJC1pS2D1pRLG1").
Proof.
intros data off cnt Ho. rewrite file_read_unguarded.
rewrite skipn_all2 by (unfold word_to_nat; lia). apply firstn_nil.
Qed.
Lemma file_read_full : ltac2:(TCodec.tc2 tcn__RefReadLib "QI'3'QCy8%211%411'=&Q5zr2%3221&Q4r4r3%3221&Q7&2r5%22>1%411%=261&Q6r6%72C1%911&Q8+2+R0%3221%8251'7'8&Br7&QByR0%221>%322D%63521&;&Q9%11H&<%31E%23Q81;%63Q941%?3Q981'4%Q02Q<:%B3218%D241p0F1p0Q01p0Q;1p0Q<1pRJQA1pS2QB1pRLQD1").
Proof.
intros data off cnt H0 H1 H2 H3. rewrite !file_read_unguarded. rewrite !word_to_nat_lit by lia.
split; [reflexivity|]. rewrite length_firstn, length_skipn. lia.
Qed.
Lemma len_word_Z : ltac2:(TCodec.tc2 tcn__RefReadLib "C'3'QCy8%211%411'8yR0%611&@r1%2271&QB&Q7&2%12;5%311%52:1%<3:71pRH>1").
Proof. intros. reflexivity. Qed.
End FPX_1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
