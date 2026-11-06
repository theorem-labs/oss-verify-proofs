(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__RefMemcpyLib () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib.FPX_2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib.FPX_4."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1app"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nat"; "1negb"; "1nil"; "1option"; "1orb"; "1true"; "2I"; "2and"; "2eq"]; ["2ex"; "2not"; "2or"; "3add"; "3sub"; "4le"; "4lt"; "5firstn"; "5nth"; "5skipn"; "6Z"; "7Z_to_le_bytes"; "7bytes_le_to_Z"; "7nat_to_word"; "8Segment"; "9machine_state"]; ["9store_ok"; "9word_to_le_bytes"; ":bv_eqb"; ":bvmap"; "0N"; "0P1"; "0P2"; ";wbytes"; "<msteps"; "=at_"; ">getr"; ">rdn"; ">regupd"; ">v_or"; ">v_slli"; ">v_srli"]; [">v_srliw"; "@sub"; "ALBv"; "ALWv"; "Acallee_kept"; "Akeeps"; "Bcallee_saved"; "Bkeeps_cs"; "?keeps"; "CIn"; "Cforallb"; "Dadd"; "Dle"; "Dlor"; "Dlt"; "Dmodulo"]; ["Dmul"; "Dof_nat"; "Dpow"; "Dshiftl"; "Dsub"; "Dtestbit"; "0a"; "0b"; "0bs"; "0bs1"; "0bs2"; "0bsw"; "0d"; "0dst"; "0i"; "0j"]; ["0k"; "0l"; "0l1"; "0l2"; "0m"; "0mem"; "0n"; "0q"; "0r"; "0r1"; "0r2"; "0r3"; "0rd"; "0regs"; "0regs'"; "0s0"]; ["0segs"; "0st1"; "0st2"; "EBV"; "EZ_to_bv"; "Ebv"; "Ebv_add"; "Ebv_unsigned"; "0v"; "0x"; "0y"]]).
Section FPX_1. Context {fx : PropExec.FPState}.
Definition sub {A} (bs : list A) (j k : nat) : list A := firstn k (skipn j bs).
Lemma firstn_add : forall {A} (l : list A) a b,
firstn (a + b) l = firstn a l ++ firstn b (skipn a l).
Proof.
intros A l a. revert l. induction a as [|a IH]; intros l b.
- cbn. reflexivity.
- destruct l as [|x l]; cbn.
+ destruct b; reflexivity.
+ rewrite IH. reflexivity.
Qed.
Lemma firstn_sub_app : forall {A} (bs : list A) j k,
firstn j bs ++ sub bs j k = firstn (j + k) bs.
Proof. intros. unfold sub. rewrite firstn_add. reflexivity. Qed.
Lemma skipn_add : forall {A} (l : list A) a b, skipn (a + b) l = skipn b (skipn a l).
Proof.
intros A l a. revert l. induction a as [|a IH]; intros l b; [reflexivity|].
destruct l as [|x l]; cbn; [destruct b; reflexivity|]. apply IH.
Qed.
Lemma sub_length : forall {A} (bs : list A) j k,
(j + k <= length bs)%nat -> length (sub bs j k) = k.
Proof.
intros A bs j k H. unfold sub. rewrite length_firstn, length_skipn. lia.
Qed.
Lemma sub_split : forall {A} (bs : list A) j a b,
sub bs j (a + b) = sub bs j a ++ sub bs (j + a) b.
Proof.
intros A bs j a b. unfold sub. rewrite firstn_add. f_equal.
rewrite <- skipn_add. f_equal; lia.
Qed.
Lemma sub_0_all : forall {A} (bs : list A), sub bs 0 (length bs) = bs.
Proof. intros. unfold sub. cbn. apply firstn_all. Qed.
Lemma length_firstn_id : forall {A} (bs : list A) k, k = length bs -> firstn k bs = bs.
Proof. intros A bs k ->. apply firstn_all. Qed.
Lemma sub_nth : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "N'6'S5y8%211%411'7&Fr1&5r2%2271%5241'?&QAr3u1%34=271(3&H&S4z%22C1%44C=81(9%11E%83F31%>3F:1p0@1pU0G1pTBI1").
Proof.
intros bs j. revert bs. induction j as [|j IH]; intros bs H.
- destruct bs; cbn in *; [lia|reflexivity].
- destruct bs; cbn in *; [lia|]. unfold sub in IH. apply IH. lia.
Qed.
Lemma at_succ : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "E'S5yR0%211'J'?&S6&Q9r2r1%3221(S3+1(=%33<21%93=51&QK%1285%;2:1%>3@41pTJ@1pT>B1").
Proof.
intros a d. unfold at_. apply bv_eq.
rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_unsigned (1 : word)) with 1.
rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.
Lemma word_succ_at : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "?'S5yR0%211'?&S6r1(S3+1(=%33821%63951&Q9%1275%:3;31pT><1").
Proof. intros a. rewrite <- (at_0 a) at 1. rewrite at_succ. reflexivity. Qed.
Lemma at_u : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "Q2'S5yR0%211'J&QLz&QK&S7r2%2281r1%5221%8271&QNr3%82>1%:218&R2+2+R0%3221%8251'?&Q9r4%221;%C2I1%D2J3%F21>%73J31p091p0C1pTJM1pT>O1").
Proof. intros a d H1 H2. unfold at_. apply u_Z2bv; lia. Qed.
Lemma at_nat : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "B'S5yR0%211'7'?&S6r2&Mr1%211%53941&Q9&R1%115%3281%;3=51pU0=1pT>?1").
Proof.
intros a j. unfold at_, nat_to_word. apply bv_eq.
rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
rewrite Zplus_mod_idemp_r. reflexivity.
Qed.
Lemma wbytes_app : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "Q0'6'S5y8%211%411yR0%511':%115p031'?&Q7r2r1&1r4r3%33>21%73651%83764&Q9&R1&5%12D8%311%52<1%?371:%A3B91pT>F1pU:D1pTFJ1pTDK1").
Proof.
induction bs1 as [|b r IH]; intros bs2 m a.
- cbn [app wbytes length Z.of_nat]. rewrite at_0. reflexivity.
- cbn [app wbytes length]. rewrite IH. f_equal.
rewrite word_succ_at, at_at. f_equal. lia.
Qed.
Lemma wbytes_extend : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "Q<'S5yR0%211':y8%511%311p051'6%114'7'B'?&Q7r5r4&Gr2r3%33>21%73651&Q9&R1%116%3291&QAr1%24F9:1%?3841&C%12=4%?3J1=%C3BA1%E3J51&F&5%12OB%321D%K251pU2M1pU0N1pTBQ01pTLQ81pU:Q41").
Proof.
intros m dst bs j k.
destruct (Nat.le_gt_cases j (length bs)) as [H|H]; [left|right; exact H].
rewrite <- firstn_sub_app, wbytes_app. rewrite length_firstn. f_equal. f_equal. f_equal. lia.
Qed.
Lemma wbytes_extend' : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "Q;'S5yR0%211':y8%511%311p051'6%114'7'Er2&5r3%22:1%5241'?&Q7r6r5&Gr4%23B91%63541&Q9&R1%11=%3281&QA%14I8@B%=3731&C%12CE%=3M1<%A3@?1%C3M51p0E1pU2L1pU0M1pTBO1pTLQ71pU:Q31").
Proof.
intros m dst bs j k H. destruct (wbytes_extend m dst bs j k) as [E|E]; [exact E|lia].
Qed.
Lemma rdn_skipn : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "Q@'6'N%211'S5yR0%211':y8%511%311p051'7%<14'?%812&Q;r6r5r3r4%544321(0r2%22;1%;3:41'E%1249r8r7&Q9&R1%11=%32?1&D%12B@%D48731&I%13MCB%A2J1%J3I41p0>1p0A1pU0O1pTBO1pT>Q71pU>Q21pU<Q41pV2Q=1").
Proof.
intros segs mem n. induction n as [|n IH]; intros a bs j H Hj.
- assert (j = 0)%nat by lia. subst j. cbn in H. injection H as <-.
rewrite at_0. reflexivity.
- cbn [rdn] in H.
destruct (match mem a with Some b => Some b | None => seg_rom segs a end) as [b|] eqn:Eb; [|discriminate].
destruct (rdn segs mem (a+1)%bv n) as [rest|] eqn:Er; [|discriminate].
injection H as <-.
destruct j as [|j].
+ rewrite at_0. cbn [Nat.sub skipn rdn]. rewrite Eb, Er. reflexivity.
+ cbn [skipn]. replace (S n - S j)%nat with (n - j)%nat by lia.
replace (at_ a (Z.of_nat (S j))) with (at_ (a + 1)%bv (Z.of_nat j))
by (rewrite word_succ_at, at_at; f_equal; lia).
apply IH; [exact Er|lia].
Qed.
Lemma rdn_sub : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "QB'6'N%211'S5yR0%211':y8%511%311p051'7%<14'?%812&Q;r7r6r4r5%544321(0r3%22;1%;3:41'E&Cr2%2261%421<r9r8&Q9&R1%11@%32B1%E4651>&QA%14NCD@%B2K1%K3J41p0<1p0B1pU2Q01pU0Q11pTBQ11pT>Q91pU>Q41pU<Q61pV2Q?1").
Proof.
intros segs mem n a bs j k H Hjk. unfold sub.
apply (rdn_firstn segs mem (n - j)); [|lia].
apply rdn_skipn; [exact H|lia].
Qed.
End FPX_1.
Abbreviation lez := bytes_le_to_Z.
Section FPX_2. Context {fx : PropExec.FPState}.
Definition LWv (l : list byte) : word := v_lw (Z_to_bv 64 (lez l)).
Lemma lez_bound_len : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "Q1'6'S5y8%211%411'7'?&5r2%2261r1%53621'>&QLz&Lr3%211%5241&QN&R2+2&R0+8&R1%11A%4231%7261%92;1%A2;1p0C1pU2J1pTBL1").
Proof. intros bs k <-. split; [apply bytes_le_to_Z_nonneg | apply bytes_le_to_Z_bound]. Qed.
Lemma lez4_range : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "L'6'S5y8%211%411'?'7&5r1%2261u4%63521'>&QLz&Lr2%211%5241&QN&R2+2+Q0%3221%5271%=271p0?1pU4G1").
Proof. intros l H. pose proof (lez_bound_len l 4%nat H). change (8 * Z.of_nat 4) with 32 in H0. lia. Qed.
Lemma u_lez4 : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "H'6'S5y8%211%411'?'7&5r1%2261u4%63521'J&S7yR0&S4&Lr2%211%4251%7261%@3913p0;1pU4C1").
Proof. intros l H. pose proof (lez4_range l H). apply u_Z2bv; lia. Qed.
Lemma testbit_u_LWv : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "Q7'6'S5y8%211%411'J'?'7&5r2%2271u4%63521'>&QLz%2217&QN+Q0%22:1%7241'2&R5&S7yR0&QCr4%211%5241r3%8221&L%116%;214%L3=41p0?1p0H1pTNQ01pU4Q21").
Proof.
intros l i H Hi. unfold LWv, v_lw. rewrite Z_to_bv_unsigned, u_lez4 by exact H.
rewrite bv_wrap_spec_low by lia.
rewrite bv_swrap_spec by lia.
case_bool_decide; [reflexivity|].
replace i with 31 by lia. reflexivity.
Qed.
Lemma u_vlw_mod32 : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "N'6'S5y8%211%411'?'7&5r1%2261u4%63521'J&QO&S7yR0&QCr2%211%5241&R2+2+Q0%3221%;251&L%119%F3?31p0A1pU4I1").
Proof.
intros l H. pose proof (lez4_range l H) as R.
apply Z.bits_inj'. intros i Hi.
destruct (Z.lt_ge_cases i 32) as [Hl|Hh].
- rewrite Z.mod_pow2_bits_low by lia. apply testbit_u_LWv; [exact H|lia].
- rewrite Z.mod_pow2_bits_high by lia. symmetry. apply (Z_testbit_high 32); lia.
Qed.
Lemma lez_cons : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "H'S5y8%211'6%112'?'J&L(3r2r1%33921%511&QM&S7%12>6&R3%:17+8%3221%7251%@3?91pTBB1pT@E1").
Proof. reflexivity. Qed.
Lemma testbit_lez_high : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "M'6'S5y8%211%411'J&QL&R0+8&R1&5r2%2291%411%7261r1%:221'?'2&R5&Lr3%211%421<(4%83721p0:1pTNF1pTBH1").
Proof.
intros bs i Hi. apply (Z_testbit_high (8 * Z.of_nat (length bs))); try lia.
apply lez_bound_len. reflexivity.
Qed.
Lemma testbit_lez_skipn : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "Q4'7'6'S5y8%211%411'J&QLzr1%3221'?'2&R5&L&Ir4r3%33>21%511r2%8221%815&QK&R0+8&R1%11;%4231%6291%A281%D3C:1p0F1pTNK1pTBM1pU@Q31").
Proof.
induction q as [|q IH]; intros bs i Hi.
- cbn [skipn]. f_equal. lia.
- destruct bs as [|b bs].
+ cbn [skipn lez]. rewrite !Z.bits_0. reflexivity.
+ cbn [skipn]. rewrite IH by lia. rewrite lez_cons.
rewrite Z.lor_spec, Z.shiftl_spec by lia.
pose proof (u8_range b).
rewrite (Z_testbit_high 8 (bv_unsigned b)) by lia. cbn [orb]. f_equal. lia.
Qed.
Lemma testbit_lez_firstn : forall q bs i, 0 <= i ->
Z.testbit (lez (firstn q bs)) i = if i <? 8 * Z.of_nat q then Z.testbit (lez bs) i else false.
Proof.
induction q as [|q IH]; intros bs i Hi.
- cbn [firstn lez]. rewrite Z.bits_0. destruct (Z.ltb_spec i (8 * Z.of_nat 0)); [lia|reflexivity].
- destruct bs as [|b bs].
+ cbn [firstn lez]. rewrite !Z.bits_0. destruct (i <? _); reflexivity.
+ cbn [firstn]. rewrite !lez_cons, !Z.lor_spec, !Z.shiftl_spec by lia.
destruct (Z.lt_ge_cases i 8) as [H8|H8].
* rewrite !(Z.testbit_neg_r _ (i - 8)) by lia.
destruct (Z.ltb_spec i (8 * Z.of_nat (S q))); [reflexivity|lia].
* rewrite IH by lia.
destruct (Z.ltb_spec (i - 8) (8 * Z.of_nat q)), (Z.ltb_spec i (8 * Z.of_nat (S q))); try lia; try reflexivity.
pose proof (u8_range b). rewrite (Z_testbit_high 8 (bv_unsigned b)) by lia. reflexivity.
Qed.
Lemma testbit_lez_app : forall xs ys i, 0 <= i ->
Z.testbit (lez (xs ++ ys)) i =
if i <? 8 * Z.of_nat (length xs) then Z.testbit (lez xs) i else Z.testbit (lez ys) (i - 8 * Z.of_nat (length xs)).
Proof.
intros xs ys i Hi. rewrite bytes_le_app, Z.lor_spec, Z.shiftl_spec by lia.
destruct (Z.ltb_spec i (8 * Z.of_nat (length xs))).
- rewrite (Z.testbit_neg_r (lez ys)) by lia. apply orb_false_r.
- rewrite testbit_lez_high by lia. reflexivity.
Qed.
Lemma Z_to_le_bytes_lez : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "?'6'S5y8%211%411'?&K&5r1%2261&L%113%6231%83915pTB:1").
Proof.
induction bs as [|b bs IH]; [reflexivity|].
cbn [length Z_to_le_bytes].
replace (Z.shiftr (lez (b :: bs)) 8) with (lez bs).
2:{ apply Z.bits_inj'. intros i Hi. rewrite Z.shiftr_spec by lia.
pose proof (testbit_lez_skipn 1 (b :: bs) i Hi) as E. change (skipn 1 (b :: bs)) with bs in E.
rewrite E. reflexivity. }
rewrite IH. f_equal.
apply bv_eq. rewrite Z_to_bv_unsigned.
apply Z.bits_inj'. intros i Hi. pose proof (u8_range b).
destruct (Z.lt_ge_cases i 8).
- rewrite bv_wrap_spec_low by lia. rewrite lez_cons, Z.lor_spec, Z.shiftl_spec by lia.
rewrite (Z.testbit_neg_r _ (i - 8)) by lia. apply orb_false_r.
- rewrite bv_wrap_spec_high by lia. symmetry. apply (Z_testbit_high 8); lia.
Qed.
Lemma word_to_le_bytes_4_eq : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "Q='S5yR0%211'6y8%511%311'?'7&5r1%2261u4%63521'J'>&QLz%2218&QN+Q0%22;1%7241'2&R5&S7r5%22J1r2%5221&Lr4%211%9215%K3;51p0=1pTNF1&Q1%12J7r3%Q13Q221p051p0M1pU4Q51pVBQ:1").
Proof.
intros v l Hl Hb. unfold word_to_le_bytes.
rewrite <- (Z_to_le_bytes_wrap 4 32) by (cbn; lia).
rewrite <- Hl at 1. rewrite <- (Z_to_le_bytes_lez l). rewrite Hl. f_equal.
apply Z.bits_inj'. intros i Hi.
destruct (Z.lt_ge_cases i 32).
- rewrite bv_wrap_spec_low by lia. apply Hb. lia.
- rewrite bv_wrap_spec_high by lia. symmetry. apply testbit_lez_high. rewrite Hl. cbn. lia.
Qed.
Lemma sw_bytes_LWv : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "D'6'S5y8%211%411'?'7&5r1%2261u4%63521&Q1&QCr2%211%4261%<3=13p071pU4?1").
Proof.
intros l H. apply word_to_le_bytes_4_eq; [exact H|]. intros i Hi. apply testbit_u_LWv; assumption.
Qed.
Definition LBv (b : byte) : word := Z_to_bv 64 (bv_unsigned b).
Lemma sb_byte_LBv : ltac2:(TCodec.tc2 tcn__RefMemcpyLib ">'S5y8%211'?&S4&S7yR0&QBr1%211%5241%72:1%93:14pT@;1").
Proof.
intros b. unfold LBv. pose proof (u8_range b). rewrite u_Z2bv by lia.
apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.
Lemma sb_byte_eq : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "Q4'S5yR0%211y8%411'J'>&QLzr1%3221&QN+8%2241%8241'?'2&R5&S7r4%22C1r2%5221r3%62E1%8214%;3:41p0=1pTNG1&S4%<2M7%22L1%A3L1;p051pT@N1pVBQ11").
Proof.
intros v b Hb. apply bv_eq. rewrite Z_to_bv_unsigned.
apply Z.bits_inj'. intros i Hi. pose proof (u8_range b).
destruct (Z.lt_ge_cases i 8).
- rewrite bv_wrap_spec_low by lia. apply Hb. lia.
- rewrite bv_wrap_spec_high by lia. symmetry. apply (Z_testbit_high 8); lia.
Qed.
Lemma testbit_nth_lez : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "Q@'6'S5y8%211%411'7'J'>&QLzr1%3221&QN+8%2241%8241&Fr3&5r4%22A1%5241'?'2&R5&S7&Hr5&S4%12KD%44K;31%62M1%821?&L%117&QK&R0&R1%11C%32J1%52G1%A271%D3C:1p0F1p0M1pTNQ71pU@Q91pU4Q;1").
Proof.
intros l q i Hi Hq. rewrite <- testbit_lez_skipn by lia.
revert l Hq. induction q as [|q IH]; intros l Hq.
- destruct l as [|b l]; [cbn in Hq; lia|]. cbn [nth skipn]. rewrite lez_cons.
rewrite Z.lor_spec, Z.shiftl_spec, (Z.testbit_neg_r _ (i - 8)) by lia. symmetry. apply orb_false_r.
- destruct l as [|b l]; [cbn in Hq; lia|]. cbn [nth skipn]. apply IH. cbn in Hq. lia.
Qed.
Lemma sb_byte_srli_LWv : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "Q8'6'S5y8%211%411'7'?&5r2%2261u4%53621'Eu3%2261&S4&S7yR0&Q?&QCr4%211&R0+8&R1r3%211%5241%:271%=2<1%?2L1&Hz%B2O1%34O9>1%M3Q051p0F1p0J1pU@Q11pU4Q31").
Proof.
intros l q H Hq. apply sb_byte_eq. intros i Hi.
unfold v_srli. rewrite Z_to_bv_unsigned, bv_wrap_spec_low, Z.shiftr_spec by lia.
rewrite testbit_u_LWv by (try exact H; lia).
rewrite testbit_nth_lez by (try rewrite H; lia). reflexivity.
Qed.
Lemma testbit_u_srliw_LWv : forall l s i, length l = 4%nat -> 1 <= s -> 0 <= i ->
Z.testbit (bv_unsigned (v_srliw (LWv l) s)) i = if i + s <? 32 then Z.testbit (lez l) (i + s) else false.
Proof.
intros l s i H Hs Hi. unfold v_srliw. rewrite Z_to_bv_unsigned.
assert (Sh : forall j, 0 <= j -> Z.testbit (Z.shiftr (bv_wrap 32 (bv_unsigned (LWv l))) s) j
= if j + s <? 32 then Z.testbit (lez l) (j + s) else false).
{ intros j Hj. rewrite Z.shiftr_spec by lia.
destruct (Z.ltb_spec (j + s) 32).
- rewrite bv_wrap_spec_low by lia. apply testbit_u_LWv; [exact H|lia].
- apply bv_wrap_spec_high. lia. }
destruct (Z.lt_ge_cases i 64).
- rewrite bv_wrap_spec_low by lia. rewrite bv_swrap_spec by lia.
case_bool_decide.
+ apply Sh. lia.
+ rewrite Sh by lia.
destruct (Z.ltb_spec (Z.of_N 32 - 1 + s) 32), (Z.ltb_spec (i + s) 32); try lia; reflexivity.
- rewrite bv_wrap_spec_high by lia. destruct (Z.ltb_spec (i + s) 32); [lia|reflexivity].
Qed.
Lemma testbit_u_slli_LWv : forall l s i, length l = 4%nat -> 0 <= s -> 0 <= i < 32 ->
Z.testbit (bv_unsigned (v_slli (LWv l) s)) i = if i <? s then false else Z.testbit (lez l) (i - s).
Proof.
intros l s i H Hs Hi. unfold v_slli. rewrite Z_to_bv_unsigned.
rewrite bv_wrap_spec_low by lia. rewrite Z.shiftl_spec by lia.
destruct (Z.ltb_spec i s).
- apply Z.testbit_neg_r. lia.
- apply testbit_u_LWv; [exact H|lia].
Qed.
Lemma testbit_u_vor : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "N'S5yR0%211'J&QLzr1%3221'?'2&R5&S7&Q=r4r3%3221%52?1r2%8221&;%92C7%;214%;2E8%=216%5231%A3@71p0C1pTNH1pVFJ1pVDK1").
Proof.
intros x y i Hi. unfold v_or. rewrite Z_to_bv_unsigned.
destruct (Z.lt_ge_cases i 64).
- rewrite bv_wrap_spec_low by lia. apply Z.lor_spec.
- rewrite bv_wrap_spec_high by lia.
pose proof (u64_range x). pose proof (u64_range y).
rewrite (Z_testbit_high 64 (bv_unsigned x)) by lia. rewrite (Z_testbit_high 64 (bv_unsigned y)) by lia. reflexivity.
Qed.
Lemma sw_bytes_merge : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "QL'6'S5y8%211%411'7yR0%611'?&5r4%2281u4%53821'>'Eu1%2217u3%4291%6231&Q=&Q>&QCr6%211&R4+Q0&R0+8&R1r5%211%5241%8271%=2:1&Q@r7%?11%3216%C251%Q13Q2O1&Q1%12O<&1&Ir8%23Q<G1&G%13Q>I<%63Q?31%Q;3Q?81p0;1p0Q11p0Q91p0Q:1pVBQA1pU@QD1pU8QF1pU6QG1").
Proof.
intros l1 l2 q v H1 H2 Hq ->.
apply word_to_le_bytes_4_eq.
{ rewrite length_app, length_skipn, length_firstn, H1, H2. lia. }
intros i Hi.
rewrite testbit_u_vor by lia.
rewrite testbit_u_slli_LWv by (try exact H2; lia).
rewrite testbit_u_srliw_LWv by (try exact H1; lia).
rewrite testbit_lez_app by lia. rewrite length_skipn, H1.
rewrite testbit_lez_skipn by lia.
destruct (Z.ltb_spec i (32 - 8 * Z.of_nat q)), (Z.ltb_spec i (8 * Z.of_nat (4 - q))),
(Z.ltb_spec (i + 8 * Z.of_nat q) 32); try lia.
- reflexivity.
- rewrite testbit_lez_firstn by lia.
destruct (Z.ltb_spec (i - 8 * Z.of_nat (4 - q)) (8 * Z.of_nat q)); [|lia].
rewrite orb_false_r. f_equal. lia.
Qed.
Lemma sw_bytes_merge' : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "QL'6'S5y8%211%411'7yR0%611'?&5r4%2281u4%53821'>'Eu1%2217u3%4291%6231&Q=&Q@&QCr7%211&R0+8&R1r5%211%5241%:271&Q>r6%<11&R4+Q0%2217%6241%C281%Q13Q2O1&Q1%12O>&1&Ir8%23Q<=1&G%13Q>?I%63Q?31%Q;3Q?81p0;1p0Q11p0Q91p0Q:1pVBQA1pU@QD1pU8QF1pU6QG1").
Proof.
intros l1 l2 q v H1 H2 Hq ->. apply (sw_bytes_merge l1 l2 q); try assumption.
unfold v_or. f_equal. apply Z.lor_comm.
Qed.
Lemma store_ok_at : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "QN'6'N%211'S5yR0%211':y8%511%311p051'7%<14'J&QL&QK&S7r5%22>1&R1r4%211%7241&R2+2+R0%3221%=251'?'2&Q0r8r7r6%44321A(<%83721z%H21B%H2FB%E18%K221r;&Q7r:r9%3321>&Q9%123?%C4731Q0%F3E1?p0:1p0>1p0A1p0K1pU2Q<1pU0Q;1pTHQ=1pR:Q?1pTLQF1pU:QB1pV2QK1").
Proof.
intros segs m dst N bsw j k Hnw Hok Hj Hk.
destruct k as [|k]; [reflexivity|].
pose proof (u64_range dst).
apply (store_ok_mono segs (S k) m); [apply wbytes_grows|].
apply (store_ok_sub segs m dst (at_ dst j) N (S k) Hnw Hok); rewrite at_u; lia.
Qed.
Definition callee_kept : list reg :=
[1; 2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition keeps (regs regs' : bvmap 5 word) : Prop :=
forall r : reg, In r callee_kept -> getr regs' r = getr regs r.
Lemma keeps_refl : ltac2:(TCodec.tc2 tcn__RefMemcpyLib ":&Q3y5'S5yR0%211%5241&QEr1%2211pUL41").
Proof. intros regs r _. reflexivity. Qed.
Lemma keeps_trans : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "A&Q3y5'S5yR0%211%5241&QEr3r2%3221r5%5214p031p041pUH91pUF:1pUD;1").
Proof. intros r1 r2 r3 A B r Hr. rewrite (B r Hr). apply A, Hr. Qed.
Lemma keeps_upd : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "K&Q3y5'S5yR0%211%5241%415&QEr4r3%3221&A&QI&QD%23851%411r6&Q<r5%231;:%=241p061p0<1pVBC1pUJB1pUND1pULE1").
Proof.
intros regs regs' rd v K Hn r Hr.
rewrite getr_other; [apply K, Hr|]. intros ->. exact (Hn Hr).
Qed.
Lemma keeps_getr : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "J&Q3y5'S5yR0%211%5241%415&QEr3r2%3221&QI&QD%23741'?&Q:r4%2219r5%421;%63@31p081p0<1pUBA1pUNC1pULD1").
Proof. intros regs regs' r K Hr. apply K, Hr. Qed.
End FPX_2.
Ltac kept_reg := cbv [callee_kept In]; intuition congruence.
Section FPX_3. Context {fx : PropExec.FPState}.
Example keeps_sp_example : forall regs regs', keeps regs regs' -> getr regs' 2 = getr regs 2.
Proof. intros regs regs' K. apply (keeps_getr _ _ 2 K). kept_reg. Qed.
End FPX_3.
Lemma wf_not_in_b : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "J'S5y5%211'6%112'?'2&QJ&8&Q2r1r3%33;21%511qVD<1%83=15(<%<3;21&A&QIr2%23C:1%411p061pU4D1pUBG1").
Proof.
intros r l H Hin. rewrite forallb_forall in H. specialize (H r Hin). rewrite PropExec.bv_eqb_refl in H. discriminate H.
Qed.
Ltac not_kept := first [ apply wf_not_in_b; reflexivity | cbv; intuition discriminate ].
Ltac solve_keeps :=
repeat (apply keeps_upd; [| not_kept]); first [apply keeps_refl | assumption].
Section FPX_4. Context {fx : PropExec.FPState}.
Lemma runs_trans : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "QC'6'N%211'O&Q3y5'S5yR0%211%5241p017!p031'@'>'Q8r7r6r5r1%211%63541r4%114%:231qUD@1%=2A1r:r8r3%211%>1<%A3521%C21=qUFI1%F2J1p0@1pUDL1r9%H31;C%J21AqUFQ01%M2Q11p061p0B1pR>Q11pV6Q41pR<Q31pV4Q61pV0Q>1pV2Q@1").
Proof.
intros segs s0 st1 P1 st2 P2 (r1 & R1 & H1) K.
destruct (K r1 H1) as (r2 & R2 & H2).
exists r2. split; [eapply msteps_trans; eassumption | exact H2].
Qed.
Definition callee_saved : list reg :=
[1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition keeps_cs (regs regs' : bvmap 5 word) : Prop :=
forall r : reg, In r callee_saved -> getr regs' r = getr regs r.
Lemma keeps_cs_refl : ltac2:(TCodec.tc2 tcn__RefMemcpyLib ":&Q3y5'S5yR0%211%5241&QGr1%2211pUL41").
Proof. intros regs r _. reflexivity. Qed.
Lemma keeps_cs_trans : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "A&Q3y5'S5yR0%211%5241&QGr3r2%3221r5%5214p031p041pUH91pUF:1pUD;1").
Proof. intros r1 r2 r3 A B r Hr. rewrite (B r Hr). apply A, Hr. Qed.
Lemma keeps_cs_upd : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "K&Q3y5'S5yR0%211%5241%415&QGr4r3%3221&A&QI&QF%23851%411r6&Q<r5%231;:%=241p061p0<1pVBC1pUJB1pUND1pULE1").
Proof.
intros regs regs' rd v K Hn r Hr.
rewrite getr_other; [apply K, Hr|]. intros ->. exact (Hn Hr).
Qed.
Lemma keeps_cs_upd_same : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "Q4&Q3y5'S5yR0%211%5241%415&QGr4r3%3221'?&Q:r5%2215r2%53<21&A(S3z(=%33D21%;3@>1%611r7&Q<r6%231>C%E241p061p0>1p0E1pVBL1pUJK1pUNM1pULN1").
Proof.
intros regs regs' rd v K Hv Hnz r Hr.
destruct (decide (r = rd)) as [->|Hne].
- rewrite getr_same by exact Hnz. symmetry. exact Hv.
- rewrite getr_other by exact Hne. apply K, Hr.
Qed.
Lemma keeps_keeps_cs : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "@&Q3y5'S5yR0%211%5241&QHr2r1%3221&QGr3%2215p041pUN91pUL:1").
Proof.
intros regs regs' K r Hr. apply K. unfold callee_saved, callee_kept in *. cbn [In] in *. intuition.
Qed.
Lemma keeps_cs_getr : ltac2:(TCodec.tc2 tcn__RefMemcpyLib "J&Q3y5'S5yR0%211%5241%415&QGr3r2%3221&QI&QF%23741'?&Q:r4%2219r5%421;%63@31p081p0<1pUBA1pUNC1pULD1").
Proof. intros regs regs' r K Hr. apply K, Hr. Qed.
End FPX_4.
Ltac solve_keeps_cs :=
repeat (first [ apply keeps_cs_upd; [| not_kept]
| apply keeps_cs_upd_same; [| solve [eauto | symmetry; eauto] | let X := fresh in intro X; discriminate X ] ]);
first [apply keeps_cs_refl | assumption | apply keeps_keeps_cs; assumption].
