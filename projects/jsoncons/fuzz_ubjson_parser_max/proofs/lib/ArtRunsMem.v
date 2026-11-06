(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MemSplit ArtMem ArtRuns.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__ArtRunsMem () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtRuns."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1bool"; "1list"; "1nat"; "1option"; "2and"; "2eq"; "2not"; "3le"; "4repeat"; "5Z"; "6Segment"; "7store_ok"; "7word_to_le_bytes"; "7wview"; "0M"]; ["0M'"; "8apart"; "8cell"; "8wok"; "8wr"; "9art_reveal"; "9art_unmap"; "9art_zfill"; ":mem_grows"; ";add"; ";le"; ";lt"; ";of_nat"; ";pow"; ";sub"; "0a"]; ["0hi"; "0len"; "0lo"; "0m"; "0m1"; "0m2"; "0n"; "0r"; "0segs"; "<Z_to_bv"; "<bv"; "<bv_unsigned"; "0v"; "0x"]]).
Lemma art_le_bytes_zero : ltac2:(TCodec.tc2 tcn__ArtRunsMem "H'3'8r1u8%3221'6'2'Q:y8%211%411&=r2&Q9yR0z%3221%6251&9%62;4%23;18%@3;41p0B1pR>G1").
Proof. intros n Hn. do 9 (destruct n as [|n]; [vm_compute; reflexivity|]). exfalso. lia. Qed.
Lemma art_store_ok_ext : ltac2:(TCodec.tc2 tcn__ArtRunsMem "QI'2';%211'3'Q:yR0%211'4y8%511%311p051&J&I&Q;r1%22;1&Lr4%211%7241&M+2+R0%3221%=251'5r3%>2G1%A21=&Kr6%?11%D251%42B1%9261'6r2%711r5%113%53O31p071pRLQ51'1&<r7%2418D@%342NEA%=3521p071p0J1pR0Q>1pR<Q:1pR:Q;1pR>QD1pRBQF1").
Proof.
intros segs n. induction n as [|n IH]; intros m1 m2 a Hnw Hext; [reflexivity|].
cbn [store_ok]. unfold wview. rewrite (Hext a) by (pose proof (u64_range a); lia).
destruct n as [|n']; [reflexivity|].
assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1) by (apply u_add1; rewrite !Nat2Z.inj_succ in Hnw; lia).
rewrite (IH m1 m2 (a + 1)%bv) by (rewrite Hu1; first [rewrite !Nat2Z.inj_succ in *; lia | intros x Hx; apply Hext; rewrite !Nat2Z.inj_succ in *; lia]).
reflexivity.
Qed.
Section WithSegs.
Variable segs : list Segment.
#[local] Abbreviation cell := (cell segs).
#[local] Abbreviation wr := (wr segs).
#[local] Abbreviation wok := (wok segs).
Lemma art_cell_agree : ltac2:(TCodec.tc2 tcn__ArtRunsMem "QJ'Q:yR0%211'4y8%511%311p051':'3'5&Jr4&Q;r1%22>1%5241&K&I&Lr3%211%42:1%6281%>281'6r6r2%211r7%113%63I31p081pRLO1z%H21Gr5%B1I%D221&M+2+R0%3221%J251&BvQ8r8%3521E;Q3%4532CF<p021p071p0@1p0C1pRJQ=1pR>Q=1pR0Q?1pQ2QA1pQ0QB1").
Proof.
intros M M' a n v AG Ha Hn C. unfold ArtMem.cell in *. rewrite <- C.
apply rdn_ext. rewrite art_u_lit by lia. lia.
intros x Hx. rewrite art_u_lit in Hx by lia. apply AG. lia.
Qed.
Lemma art_wr_of_defined : ltac2:(TCodec.tc2 tcn__ArtRunsMem "QD'Q:yR0%211'4y8%511%311p051':&Jzr2%3221&K&Ir3%2215&M+2+R0%3221%8251'5r5&Q;r1%22I1%B241r4%?261%A241%9241&7'6r7%11H(0%11Q0%53Q031%711p091pRLQ71&DvQ8r6%3421FAp051p0J1p0Q41pR>Q91pR0Q:1pQ0Q<1").
Proof.
intros M a n Ha Hn D d k Hd Hk. apply store_ok_of_all.
- rewrite art_u_lit by lia. lia.
- intros x Hx. rewrite art_u_lit in Hx by lia. unfold wview. destruct (M x) eqn:E; [discriminate|]. exfalso. apply (D x); [lia|exact E].
Qed.
Lemma art_wr_of_wview : ltac2:(TCodec.tc2 tcn__ArtRunsMem "QE'Q:yR0%211'4y8%511%311p051':&Jzr2%3221&K&Ir3%2215&M+2+R0%3221%8251'5r5&Q;r1%22I1%B241r4%?261%A241%9241&7'6&>vQ8r7%3321J(0%11Q2%73Q231%911p0;1pRLQ91&Dr6%24;1GBp041p0K1p0Q51pR>Q:1pR0Q;1pQ0Q=1").
Proof.
intros M a n Ha Hn D d k Hd Hk. apply store_ok_of_all.
- rewrite art_u_lit by lia. lia.
- intros x Hx. rewrite art_u_lit in Hx by lia. apply D. lia.
Qed.
Lemma art_wr_wview : ltac2:(TCodec.tc2 tcn__ArtRunsMem "QE'Q:yR0%211'4y8%511%311p051':&Jzr2%3221&K&Ir3%2215&M+2+R0%3221%8251&DvQ8r5r4%44321;'5r6&Q;r1%22N1%G241%C259%E231%8231&7'6&>r8%23A1M(0%11Q5%63Q531%811p0:1pRLQ<1p0E1p0K1p0Q51pR>Q:1pR0Q;1pQ0Q=1").
Proof.
intros M a n Ha Hn W x Hx.
pose proof (W (bv_unsigned x - a) 1%nat ltac:(lia) ltac:(cbn; lia)) as OK.
replace (a + (bv_unsigned x - a)) with (bv_unsigned x) in OK by lia. rewrite Z_to_bv_bv_unsigned in OK.
apply (store_ok_all segs M 1 x); [pose proof (u64_range x); cbn; lia | exact OK | cbn; lia].
Qed.
Lemma wr_join : ltac2:(TCodec.tc2 tcn__ArtRunsMem "Q='Q:yR0%211'4y8%511%311p051':&Jzr3%3221&K&Ir6r5%3221r4%5221&M+2+R0%3221%;251&DvQ8r8r7%44321>r9%A243%74621Ar:%948143p031p071p0=1p0J1p0K1p0L1pR8Q11pR>Q21pR0Q31pQ0Q51").
Proof.
intros M a n m Ha Hn Hm Hb W1 W2. apply art_wr_of_wview; [lia|lia|]. intros x Hx.
destruct (Z_lt_le_dec (bv_unsigned x) (a + n)) as [L|G].
- apply (art_wr_wview M a n); [lia|lia|exact W1|lia].
- apply (art_wr_wview M (a + n) m); [lia|lia|exact W2|lia].
Qed.
Lemma art_zfill_grows : ltac2:(TCodec.tc2 tcn__ArtRunsMem "C'Q:yR0%211'4y8%511%311p051':&Hr3&Gr2r1%33421%6251pR481pR@91pQ0;1").
Proof. intros M r len x Hx. unfold art_zfill. destruct ((r <=? bv_unsigned x) && (bv_unsigned x <? r + len)); [discriminate|exact Hx]. Qed.
Lemma wr_zfill : ltac2:(TCodec.tc2 tcn__ArtRunsMem "Q2'Q:yR0%211'4y8%511%311p051':&Jzr2%3221&K&Ir3%2215&M+2+R0%3221%8251&DvQ8&Gr5r4%3321<%64512=p081p0B1pR4G1pR@H1pQ0J1").
Proof. intros M r len Hr Hl. apply art_wr_of_defined; [lia|lia|]. intros x Hx. rewrite art_zfill_in by lia. discriminate. Qed.
Lemma wr_zfill_other : ltac2:(TCodec.tc2 tcn__ArtRunsMem "K'Q:yR0%211'4y8%511%311p051':&DvQ8r5r2r1%544321&Gr6r4%33271r3%;4:218p071pR>>1pR0?1pR4@1pR@A1pQ0C1").
Proof. intros. eapply wr_grows; [apply art_zfill_grows|assumption]. Qed.
Lemma wok_zfill_other : ltac2:(TCodec.tc2 tcn__ArtRunsMem "L'Q:yR0%211'4y8%511%311p051':'3&CvQ8r5r2r1%544321&Gr6r4%33271r3%;4:218p071pR>>1pR0@1pR4A1pR@B1pQ0D1").
Proof. intros. eapply wok_grows; [apply art_zfill_grows|assumption]. Qed.
Lemma cell_zfill_other : ltac2:(TCodec.tc2 tcn__ArtRunsMem "QB'Q:yR0%211'4y8%511%311p051':'3&Jzr3%3221&K&Ir4&L%116%4231&M+2+R0%3221%:251&Ar7r6r5%<1=%544321&BvQ8r9%352176B&Gr:r8%33251%8571=<;p061p0;1p0B1p0N1pRJQ41pR>Q41pR0Q61pR4Q71pR@Q81pQ0Q:1").
Proof. intros M r len a n v Ha Hn A C. eapply art_cell_agree; [|exact Ha|exact Hn|exact C]. intros x Hx. apply art_zfill_out. unfold apart in A. lia. Qed.
Lemma cell_zfill_zero : ltac2:(TCodec.tc2 tcn__ArtRunsMem "QG'Q:yR0%211'4y8%511%311p051':'3'8r1u8%3221&Jzr3%3221&K&Ir4&L%116%4231&M+2+R0%3221%:251r7r5%A221r6%<13%?221r8%A217%G231&BvQ8&Gr:r9%33218%6551?<Mp081p0?1p0C1p0O1p0Q41pR>Q91pR0Q;1pR4Q<1pR@Q=1pQ0Q?1").
Proof.
intros M r len a n Hn8 Ha Hn Hlo Hhi. unfold ArtMem.cell. rewrite art_le_bytes_zero by exact Hn8.
apply rdn_const. rewrite art_u_lit by lia. lia.
intros x Hx. rewrite art_u_lit in Hx by lia. apply art_zfill_in. lia.
Qed.
Lemma art_reveal_grows : ltac2:(TCodec.tc2 tcn__ArtRunsMem "C'Q:yR0%211'4y8%511%311p051':&Hr3&Er2r1%33421%6251pR281pR691pQ0;1").
Proof. intros M lo hi x Hx. unfold art_reveal. destruct ((lo <=? bv_unsigned x) && (bv_unsigned x <? hi)); [|exact Hx]. destruct (M x); [discriminate|contradiction]. Qed.
Lemma wr_reveal : ltac2:(TCodec.tc2 tcn__ArtRunsMem "Q2'Q:yR0%211'4y8%511%311p051':&Jzr2%3221&K&M+2+R0%3221%5271&DvQ8&Er5r4r3%43321&N%1234%948351p0;1p0B1pR2G1pR6H1pQ0J1").
Proof. intros M lo hi Hlo Hhi. apply art_wr_of_defined; [lia|lia|]. intros x Hx. apply art_reveal_defined. lia. Qed.
Lemma wr_reveal_other : ltac2:(TCodec.tc2 tcn__ArtRunsMem "K'Q:yR0%211'4y8%511%311p051':&DvQ8r5r2r1%544321&Er6r4%33271r3%;4:218p071pR>>1pR0?1pR2@1pR6A1pQ0C1").
Proof. intros. eapply wr_grows; [apply art_reveal_grows|assumption]. Qed.
Lemma cell_reveal_other : ltac2:(TCodec.tc2 tcn__ArtRunsMem "QD'Q:yR0%211'4y8%511%311p051':'3&Jzr3%3221&K&Ir4&L%116%4231&M+2+R0%3221%:251&Ar7&Nr6%2213r5%>1?%746321&BvQ8r9%352186D&Er:r8%33251%8571?=;p061p0;1p0D1p0Q01pRJQ61pR>Q61pR0Q81pR2Q91pR6Q:1pQ0Q<1").
Proof. intros M lo hi a n v Ha Hn A C. eapply art_cell_agree; [|exact Ha|exact Hn|exact C]. intros x Hx. apply art_reveal_out. unfold apart in A. lia. Qed.
Lemma cell_unmap_other : ltac2:(TCodec.tc2 tcn__ArtRunsMem "QB'Q:yR0%211'4y8%511%311p051':'3&Jzr3%3221&K&Ir4&L%116%4231&M+2+R0%3221%:251&Ar7r6r5%<1=%544321&BvQ8r9%352176B&Fr:r8%33251%8571=<;p061p0;1p0B1p0N1pRJQ41pR>Q41pR0Q61pR4Q71pR@Q81pQ0Q:1").
Proof. intros M r len a n v Ha Hn A C. eapply art_cell_agree; [|exact Ha|exact Hn|exact C]. intros x Hx. apply art_unmap_out. unfold apart in A. lia. Qed.
Lemma wr_unmap_other : ltac2:(TCodec.tc2 tcn__ArtRunsMem "Q='Q:yR0%211'4y8%511%311p051':&Jzr2%3221&K&Ir3%2215&M+2+R0%3221%8251&Ar6r5r4%44321;&DvQ8r8%342165&Fr9r7%33251%8471<;p061p0;1p0A1p0K1pR>Q01pR0Q11pR4Q21pR@Q31pQ0Q51").
Proof.
intros M r len a n Ha Hn A W d k Hd Hk. pose proof (W d k Hd Hk) as OK.
destruct (Nat.eq_dec k 0) as [->|NZ]; [reflexivity|].
rewrite (art_store_ok_ext segs k (art_unmap M r len) M); [exact OK| |]; [rewrite art_u_lit by lia; lia|].
intros x Hx. rewrite art_u_lit in Hx by lia. apply art_unmap_out. unfold apart in A. lia.
Qed.
End WithSegs.
