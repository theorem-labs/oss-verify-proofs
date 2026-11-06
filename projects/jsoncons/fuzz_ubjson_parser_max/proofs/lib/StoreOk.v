(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase MemImageType RiscvSemantics StackLayout State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec StepTac StreamSim AllocSim Footprint.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__StoreOk () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AllocSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Footprint."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StreamSim."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1bool"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "1true"; "2and"; "2eq"; "2ex"; "2not"; "3Z"; "4word_to_nat"; "5PhdrInfo"]; ["5Segment"; "5seg_base"; "5seg_bytes"; "5seg_writable"; "6find_segment"; "6machine_state"; "6ms_mem"; "6ms_writable_byte"; "6segment_byte_at"; "6store_ok"; "6write_to_mem"; "6wview"; "7apply_writes"; "7apply_zeros"; "7zeros_cover"; "8EntryDraw"]; ["9read_bytes_aux"; "9read_bytes_map"; "9stack_max_size"; "0N"; ":zmem"; ";wbytes"; "<covers"; "<heap_rg"; "=wrap_mem"; ">mem_grows"; ">store_grant_ok"; "?wseg_ok"; "@add"; "@le"; "@lt"; "@of_N"]; ["@of_nat"; "@pow"; "@sub"; "@to_N"; "0a"; "0argv"; "0b"; "0base"; "0bs"; "0buf"; "0cnt"; "0cur"; "0envp"; "0hi"; "0hw"; "0l"]; ["0lo"; "0logical"; "0m"; "0m'"; "0m1"; "0m2"; "0m3"; "0ms"; "0n"; "0ph"; "0physical"; "0rnd"; "0seg"; "0segs"; "0sp"; "Abv"]; ["Abv_unsigned"; "0uid"; "0w"; "0ws"; "0x"; "0zs"]]).
Definition mem_grows (m m' : word -> option byte) : Prop :=
forall x, m x <> None -> m' x <> None.
Lemma mem_grows_refl : ltac2:(TCodec.tc2 tcn__StoreOk "<'R?yR0%211'6y8%511%311p051&Q9r1%2211pT641").
Proof. intros m x H. exact H. Qed.
Lemma mem_grows_trans : ltac2:(TCodec.tc2 tcn__StoreOk "C'R?yR0%211'6y8%511%311p051&Q9r3r2%3221r5%5214p031p041pT>91pT<:1pT:;1").
Proof. intros m1 m2 m3 H12 H23 x Hx. apply H23, H12, Hx. Qed.
Lemma wview_grows : ltac2:(TCodec.tc2 tcn__StoreOk "Q3'3'@%211'R?yR0%211'6y8%511%311p051&Q9r3r2%3221&<':&Kr5r4%33217(0%11>%73>31%911r6%9317>%;3B15%=11p051p0@1pU:J1pT8F1pT6G1pTLQ01").
Proof.
intros segs m m' x Hg Hx. unfold wview in *.
destruct (m' x) as [b'|] eqn:Hm'; [discriminate|].
destruct (m x) as [b|] eqn:Hm.
- exfalso. apply (Hg x); [rewrite Hm; discriminate|exact Hm'].
- exact Hx.
Qed.
Lemma store_ok_mono : ltac2:(TCodec.tc2 tcn__StoreOk "Q3'3'@%211'4'R?yR0%211'6y8%511%311p051&Q9r3r2%3221':'2&Ir6r4r5%443281(8%83721r7%8416=7%;3:14p041p0>1pS:H1pT8D1pT6E1pTBN1pTLQ01").
Proof.
intros segs n; induction n as [|n IH]; intros m m' a Hg H; [reflexivity|].
cbn [store_ok] in *.
destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
destruct (wview segs m' a) as [b'|] eqn:Hv'.
- apply (IH m m'); assumption.
- exfalso. apply (wview_grows segs m m' a Hg); [rewrite Hv; discriminate|exact Hv'].
Qed.
Lemma wbytes_grows : ltac2:(TCodec.tc2 tcn__StoreOk "D'3'R?y8%211%411yR0%511'6%115p031&Q9r2&Q5r1r3%33421%6251pS:;1pT691pSB?1").
Proof.
induction bs as [|b rest IH]; intros m a x Hx; [exact Hx|].
cbn [wbytes]. apply IH.
destruct (bv_eqb x a); [discriminate|exact Hx].
Qed.
Lemma apply_zeros_grows : ltac2:(TCodec.tc2 tcn__StoreOk "D'3'7'R?yR0%211%4211%611'6y8%711%311p071&Q9r1&Mr2%2231%5241pT671pU<=1").
Proof.
intros zs m x Hx. unfold apply_zeros.
destruct zs as [|z zs']; [exact Hx|].
destruct (zeros_cover (z :: zs') x); [discriminate|exact Hx].
Qed.
Lemma zmem_grows : ltac2:(TCodec.tc2 tcn__StoreOk "B'R?yR0%211'6y8%511%311p051&Q9r3&Q4r2r1%33421%6251pT0=1pS>>1pT6:1").
Proof.
intros m b l x Hx. unfold zmem.
destruct (Z.leb _ _ && Z.ltb _ _)%bool; [discriminate|exact Hx].
Qed.
Lemma write_to_mem_grows : ltac2:(TCodec.tc2 tcn__StoreOk "D'3'R?y8%211%411yR0%511'6%115p031&Q9r2&Jr1r3%33421%6251pS:;1pT691pSB?1").
Proof.
induction bs as [|b rest IH]; intros m a x Hx; [exact Hx|].
cbn [write_to_mem]. apply IH.
destruct (bv_eqb x a); [discriminate|exact Hx].
Qed.
Lemma apply_writes_grows : ltac2:(TCodec.tc2 tcn__StoreOk "E'3'7'R?yR0%211y8%411%711%7241%911'6%115p081&Q9r1&Lr2%2231%5241pT671pU8;1").
Proof.
induction ws as [|w ws' IH]; intros m x Hx.
- exact Hx.
- destruct w as [a bs]. cbn [apply_writes].
apply IH. apply write_to_mem_grows. exact Hx.
Qed.
Lemma store_ok_of_all : ltac2:(TCodec.tc2 tcn__StoreOk "QL'3'@%211'4'R?yR0%211'6y8%511%311p051&Q=&Q<&R@r1%22;1&Q@r3%211%7241&QA+2+R0%3221%=251'9%=2F9%@21<&Q>r5%>11%C251%42A1%8261&<':&Kr7r2%332:1(0%11Q1%73Q131%911p0;1pU:Q81'2&Ir6r4%3421Q1E(8%A3621p081p0N1pS:QB1pT6Q>1pTBQG1pTLQI1").
Proof.
intros segs n; induction n as [|n IH]; intros m a Hnw Hall; [reflexivity|].
cbn [store_ok].
destruct (wview segs m a) as [b|] eqn:Hv.
2: { exfalso. refine (Hall a _ Hv). rewrite Nat2Z.inj_succ. lia. }
destruct n as [|n']; [reflexivity|].
rewrite Nat2Z.inj_succ in Hnw.
assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1)
by (apply u_add1; rewrite Nat2Z.inj_succ in Hnw; lia).
apply IH.
- rewrite Hu1. lia.
- intros x Hx. rewrite Hu1 in Hx. apply Hall.
rewrite Nat2Z.inj_succ. lia.
Qed.
Lemma wrap_mem_window_defined : ltac2:(TCodec.tc2 tcn__StoreOk "QB'?'R?yR0%211'3y8%511%311%411'O&Q=&QB&R@r7%22<1&Q2%5221r4%62@1%9231&Q>r5%:2D1r8%<2F1%5231&<':'6%11G&Q8r:r9r3r6%5843<F>B21(0%11O%;3931%=11p0?1p0F1pTHQ11pSNQ81pU4Q91pU:Q:1pSJQ61pS<Q71pTNQ=1pTDQA1").
Proof.
intros ph sp argv envp x uid hw rnd Hlo Hhi. unfold wrap_mem.
destruct (stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rnd) x) as [b|];
[discriminate|].
rewrite (proj2 (Z.leb_le _ _) Hlo), (proj2 (Z.ltb_lt _ _) Hhi).
cbn. discriminate.
Qed.
Lemma store_ok_wrap_window : ltac2:(TCodec.tc2 tcn__StoreOk "QJ'3'@%211'?'R?yR0%211y8%411%911%:11'4'O&Q=&QB&R@r8%22<1&Q2%5221r5%62@1%9231&Q<r6%:2D1&Q@%117%5231r9%?2I1%B231':'2&Ir<&Q8r;r:r4r3%5743<IE21r7%94821C(8%=3<21p0?1p0I1pTHQ41pSNQ;1pU4Q<1pTBQ81pS:Q>1pSJQ;1pS<Q<1pTNQA1pTDQE1pTLQG1").
Proof.
intros segs ph sp argv envp a n uid hw rnd Hlo Hhi.
assert (Hsp : bv_unsigned sp < 2 ^ 64) by apply bv_unsigned_in_range.
apply store_ok_of_all; [lia|].
intros x Hx. unfold wview.
destruct (wrap_mem ph sp argv envp uid hw rnd x) as [b|] eqn:Hw; [discriminate|].
exfalso. revert Hw. apply wrap_mem_window_defined; lia.
Qed.
Lemma store_ok_zeros_hit : ltac2:(TCodec.tc2 tcn__StoreOk "R6'3'@%211'R?yR0%211'6y8%511%311p051'7%1277%=11'4&<':r3(5%117%43731%611&Q=&Q<&R@%12E8&Q@r2%211%6241&QA+2+R0%3221%<251'9r5%=2Q11r1%?2Q31%B231&Q>r4%A11%E271%4261%;261'2&Nr7%221G(8%Q43521p071pU:QA1&Ir8&Mr6%22:1%5441HB%Q=3>1:p081p0M1p0Q;1pTBQC1pS:QM1pU<QF1pT6QJ1pTLR31").
Proof.
intros segs m zs a n Hne Hnw Hcov.
apply store_ok_of_all; [exact Hnw|].
intros x Hx. unfold wview, apply_zeros.
destruct zs as [|z zs']; [contradiction|].
rewrite (Hcov x Hx). discriminate.
Qed.
Lemma store_ok_zmem : ltac2:(TCodec.tc2 tcn__StoreOk "QK'3'@%211'R?yR0%211'6y8%511%311p051'4&Q=&Q<&R@r2%22<1&Q@r1%211%7241&QA+2+R0%3221%=251r5%=2G1r3%?2I1%B231r4%B2L1%@15%E221r6%F2Q01%H21:%J241':'2&Ir9&Q4r8r7%3321;%6451E@(8%:3921p0<1p0E1p0K1pTBQ:1pS:QA1pT0QB1pS>QC1pT6Q?1pTLQH1").
Proof.
intros segs m b l a n Hnw Hlo Hhi.
apply store_ok_of_all; [exact Hnw|].
intros x Hx. unfold wview, zmem.
rewrite (proj2 (Z.leb_le _ _)) by lia.
rewrite (proj2 (Z.ltb_lt _ _)) by lia.
cbn. discriminate.
Qed.
Definition store_grant_ok (segs : list Segment) (m : word -> option byte)
(b l : word) : Prop :=
forall (a : word) (n : nat),
bv_unsigned b <= bv_unsigned a ->
bv_unsigned a + Z.of_nat n <= bv_unsigned b + bv_unsigned l ->
store_ok segs m a n = true.
Lemma store_grant_zmem : ltac2:(TCodec.tc2 tcn__StoreOk "Q4'3'@%211'R?yR0%211'6y8%511%311p051&Q=&Q<&R@r2%22;1r1%42=1%6231&QA+2+R0%3221%<251&Q:r5&Q4r4r3%3321?%64512@p081pT0K1pS>L1pT6H1pTLQ11").
Proof.
intros segs m b l Hnw a n Hlo Hhi. apply store_ok_zmem; lia.
Qed.
Lemma store_grant_zmem_prefix : ltac2:(TCodec.tc2 tcn__StoreOk "Q:'3'@%211'R?yR0%211'6y8%511%311p051&Q=&R@r2%22:1r1%42<1%6231&Q<r4%82@1%3217&QA+2+R0%3221%?251&Q:r7&Q4r6r5r3%43321%74613?p091p0C1pTFQ01pT4Q11pS>Q21pT6N1pTLQ71").
Proof.
intros segs m b logical physical Hle Hnw a n Hlo Hhi.
apply store_ok_zmem; lia.
Qed.
Lemma store_grant_mono : ltac2:(TCodec.tc2 tcn__StoreOk "M'3'@%211'R?yR0%211'6y8%511%311p051&Q9r4r3%3221&Q:r6r5r2%443261r7%641498p031p091pT0C1pS>D1pT8@1pT6A1pTLJ1").
Proof.
intros segs m m' b l Hg H a n Hlo Hhi.
eapply store_ok_mono; [exact Hg|]. apply H; assumption.
Qed.
Lemma store_ok_seg_writable : ltac2:(TCodec.tc2 tcn__StoreOk "RG'3'@%211'R?yR0%211'6y8%511%311p051'4&Q=&Q<&R@r2%22<1&Q@r1%211%7241&QA+2+R0%3221%=251'9r4%>2H1%?2I;%B221&Q>r3%@11%E261%4261%:261';':%Q11Q6&Dr8%L2Q6:+1%43321(1%12Q=L%93831'2&C%11Q0(8%>3421&<&H&B%11Q6&QC&QB&Q?&A%11Q;%311%52E1%711%;291(0%11QK%N3QK31%@11%Q<2B1%Q=2H1qTJR71%Q42R81p0Q61pU:R61&Ir6r5%3421QDQ?%Q:3Q01Mp061p0QI1pTBR81pS:R?1pT6R;1pTLRD1").
Proof.
intros segs m a n Hnw Hall.
apply store_ok_of_all; [exact Hnw|].
intros x Hx. unfold wview.
destruct (m x) as [b|]; [discriminate|].
destruct (Hall x Hx) as [seg [Hfind [Hw Hb]]].
rewrite Hfind, Hw. exact Hb.
Qed.
Lemma store_ok_wseg : ltac2:(TCodec.tc2 tcn__StoreOk "O'3'@%211'R?yR0%211'6y8%511%311p051'4':'2&Q;r4r2r1%43321(8%83721&Ir5r3%342918%=3<16p061pTB@1pS:G1pT6C1pTLL1").
Proof.
intros segs m a n; revert a m; induction n as [|n IH]; intros a m H; [reflexivity|].
cbn [wseg_ok] in H.
destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:Hseg; [|discriminate].
apply andb_true_iff in H as [H Hrec].
apply andb_true_iff in H as [Hwr Hbyte].
destruct (segment_byte_at (seg_bytes seg)
(Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)))) as [b|] eqn:Hb;
[|discriminate].
cbn [store_ok]. unfold wview at 1.
destruct (m a) as [b0|]; [apply IH, Hrec|].
rewrite Hseg, Hwr, Hb. apply IH, Hrec.
Qed.
Lemma store_ok_all : ltac2:(TCodec.tc2 tcn__StoreOk "QL'3'@%211'R?yR0%211'6y8%511%311p051'4&Q=&Q<&R@r1%22<1&Q@r2%211%7241&QA+2+R0%3221%=251':'2&Ir5r4r3%4432>1(8%83721'9%F2Q06%I21E&Q>%F1:%K241%32I1%7251&<&Kr8r7%3321M(0%11Q9%H3Q931%811p0:1pU:Q@1p0D1p0N1pS:QC1pTBQ>1pT6Q@1pTLQI1").
Proof.
intros segs m n; induction n as [|n IH]; intros a Hnw H x Hx;
[cbn in Hx; lia|].
cbn [store_ok] in H.
destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
rewrite Nat2Z.inj_succ in Hnw, Hx.
destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
{ assert (x = a) by (apply bv_eq; exact Heq). subst x.
rewrite Hv. discriminate. }
assert (Hn : (1 <= Z.of_nat n)%Z) by lia.
assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1) by (apply u_add1; lia).
eapply IH; [ | exact H | ]; lia.
Qed.
Lemma store_ok_sub : ltac2:(TCodec.tc2 tcn__StoreOk "QK'3'@%211'R?yR0%211'6y8%511%311p051'4&Q=&Q<&R@r4%22<1&Q@r2%211%7241&QA+2+R0%3221%=251':'2&Ir7r6r5r3%544321(8%93821%F2Q06%G2Q16%J221%F1H%K241%K2Q5<%I1;%N221%Q0241r:r9%C421B@%F3E1>p051p0<1p0@1p0K1pTBQ:1pR8Q;1pS:QB1pT2QC1pT6Q?1pTLQH1").
Proof.
intros segs m lo a N n Hnw Hok Hl Hh.
apply store_ok_of_all; [lia|].
intros x Hx. apply (store_ok_all segs m N lo Hnw Hok). lia.
Qed.
Lemma store_ok_window : ltac2:(TCodec.tc2 tcn__StoreOk "R3'3'@%211'R?yR0%211'6y8%511%311p051'4'=':&R@r6%22<1r2%53621&Q<r3&Q@r5%211%5241%<3=18&Q=&QA+2+R0%3221%52;1'2&Q;r;r9r7%43321(8%J3721%J2Q45%?2J1r:%M2Q71r8%H11%K231%E21Q0&Ir>r=%3421A@%Q73D1>p061p0=1p0@1p0I1p0Q01p0Q81pSLQ?1pS@Q@1pTBQB1pR8QC1pS:QJ1pT2QK1pT6QG1pTLR01").
Proof.
intros segs m lo a N n base hi Hbase Htop Hnw Hw Hl Hh.
eapply store_ok_sub; [ | apply store_ok_wseg, Hw | | ]; lia.
Qed.
Lemma store_ok_read_aux : ltac2:(TCodec.tc2 tcn__StoreOk "Q9'3'@%211'R?yR0%211'6y8%511%311p051'4':'2&Ir4r3r1r2%544321(8%93821';%G1?%B11&Q0&Kr6r5%3221%531>?(1%129?%E3931qU6;1%=2<1p0?1pS:Q01pTBK1pT6M1pTLQ61").
Proof.
intros segs m n; induction n as [|n IH]; intros a H.
- exists []. reflexivity.
- cbn [store_ok] in H. cbn [read_bytes_aux].
destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
destruct (IH (a + 1)%bv H) as [w Hw]. rewrite Hw. exists (b :: w). reflexivity.
Qed.
Lemma store_ok_wbuf : ltac2:(TCodec.tc2 tcn__StoreOk "Q;'3'@%211'E'R?yR0%211':'2&Ir4&Fr3%211r2&>r1%211%948541(8%=3<21';y8%C11%H11'6%112&Q1&Gr6r5%3221%531FD(1%12:B%L3931qU6<1%@2=1p0B1pSFQ11pSDQ21pT@Q61pTLQ81").
Proof.
intros segs ms buf cnt H.
rewrite read_bytes_map_eq. unfold ms_writable_byte.
apply store_ok_read_aux. exact H.
Qed.
Lemma of_nat_word_to_nat : ltac2:(TCodec.tc2 tcn__StoreOk ">'R?yR0%211':'=&Q@&>r1%211%411&R@%12:4%93831pU6;1").
Proof.
intro w. unfold word_to_nat. pose proof (u64_range w). lia.
Qed.
Lemma store_grant_wbuf : ltac2:(TCodec.tc2 tcn__StoreOk "QF'3'@%211'E'R?yR0%211&Q:r6&Fr5%211r4r3%746321&Q=&R@%12<7%22=5%4221&Q<%52@9%2214%72B?%4217%:231';y8%H11%M11':'6%113&Q1&Gr:r9%3221%531NL(1r1%22<1%<3:41qU6>1%B2?1p0D1p0K1p0Q11pSFQ:1pSDQ;1pT0Q<1pS>Q=1pT@QA1pTLQC1").
Proof.
intros segs ms b l buf cnt Hg Hlo Hhi.
apply store_ok_wbuf, Hg; rewrite ?of_nat_word_to_nat; lia.
Qed.
Lemma heap_rg_wbuf : ltac2:(TCodec.tc2 tcn__StoreOk "QN'3'@%211'E'R?yR0%211'=&Q:r7&Fr6%211r5r4%746321&Q=r2&QB&Q<&R@%12@:%22A9%4221%6213%9281&Q6&Q7r3%22D1&>%11A%633C1';y8%O11%Q411':'6%113&Q1&Gr;r:%3221%531Q4Q2(1r1%22<1%<3:41qU6>1%B2?1p0D1p0L1p0Q71pSHQ@1pSFQB1pSDQC1pT0QD1pS>QE1pT@QI1pTLQK1").
Proof.
intros segs ms b l buf cnt cur Hg Hcur Hc.
destruct Hc as [Hlo Hhi]. cbn [heap_rg rg_lo rg_hi] in Hlo, Hhi.
rewrite of_nat_word_to_nat in Hhi.
eapply store_grant_wbuf; [exact Hg | lia | lia].
Qed.
Lemma zmem_wbuf : ltac2:(TCodec.tc2 tcn__StoreOk "R2'3'@%211'E'R?yR0%211'6y8%511%311p051&Q9&Q4r5r4r3%43321&Fr6%211%9241&Q=&Q<&R@%12D;%22E;%4221&QA+2+R0%3221%:251%92L>%<218r7%<2O1%>214%@2;1';%Q81O':%Q312&Q1&Gr<r;%3221%531=M(1r1%22;1%;3:41qU6=1%?2>1p0A1p0F1p0I1p0Q51pSFQE1pSDQF1pT0QG1pS>QH1pT6QD1pT@QM1pTLQO1").
Proof.
intros segs ms m b l buf cnt Hgr Hnw Hlo Hhi.
eapply store_grant_wbuf; [ | exact Hlo | exact Hhi ].
eapply store_grant_mono; [exact Hgr|]. apply store_grant_zmem. exact Hnw.
Qed.
Example drain_buffer_in_grant : forall segs ms m (b l buf cnt : word) a bs,
ms_mem ms = wbytes (zmem m b l) a bs ->
bv_unsigned b + bv_unsigned l <= 2 ^ 64 ->
bv_unsigned b <= bv_unsigned buf ->
bv_unsigned buf + bv_unsigned cnt <= bv_unsigned b + bv_unsigned l ->
exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w.
Proof.
intros segs ms m b l buf cnt a bs Hm Hnw Hlo Hhi.
eapply zmem_wbuf;
[ rewrite Hm; apply wbytes_grows | exact Hnw | exact Hlo | exact Hhi ].
Qed.
Ltac store_ok_peel :=
repeat first
[ eapply store_ok_mono; [apply wbytes_grows|]
| eapply store_ok_mono; [apply write_to_mem_grows|]
| eapply store_ok_mono; [apply apply_zeros_grows|]
| eapply store_ok_mono; [apply apply_writes_grows|] ].
Ltac store_ok_base :=
first
[ apply store_ok_wrap_window; unfold stack_max_size; u_norm; lia
| eapply store_ok_zeros_hit;
[ discriminate | u_norm; lia | intros; u_norm; lia ]
| apply store_ok_zmem; u_norm; lia ].
Ltac solve_store_ok :=
store_ok_peel;
first [ store_ok_base
| eapply store_ok_mono; [apply zmem_grows|];
store_ok_peel; store_ok_base ].
Create HintDb store_ok_db.
Ltac store_ok_grows := solve [ eauto with store_ok_db ].
Ltac solve_store_ok_inv :=
first [ solve_store_ok
| store_ok_peel;
eapply store_ok_mono; [ store_ok_grows | ]; solve_store_ok ].
Ltac solve_mem_grows :=
repeat first
[ solve [ eauto with store_ok_db ]
| apply mem_grows_refl
| eapply mem_grows_trans; [ | apply wbytes_grows ]
| eapply mem_grows_trans; [ | apply zmem_grows ]
| eapply mem_grows_trans; [ | apply write_to_mem_grows ]
| eapply mem_grows_trans; [ | apply apply_zeros_grows ]
| eapply mem_grows_trans; [ | apply apply_writes_grows ] ].
