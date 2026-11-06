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
PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg DivergeSim SpinAlg SpinAlgX MmapSim
SymExec SymExec2 SymExec2Sound SymRun SymDrive MemSplit RefMemcpyLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__SymDriveX () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MmapSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymDrive."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymDriveX.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymDriveX.FPX_2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1app"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2I"; "2and"; "2eq"]; ["2iff"; "2not"; "2or"; "3add"; "4le"; "4lt"; "5map"; "5nth"; "6Z"; "0E"; "0K"; "7Segment"; "8is_ecall"; "8store_ok"; "8word_to_le_bytes"; "8wview"]; ["9ALU_ADD"; ":bvmap"; "0M"; "0M'"; "0R"; "0R'"; ";wbytes"; "<unfill"; "=getr"; "=rdn"; ">callee_kept"; "?junk_vals"; "?sr_after_call_j"; "@ECALLW"; "@asub"; "@entry_below_b"]; ["@esub"; "@ksub"; "@log_below_b"; "Akn_unfill"; "BEAlu"; "BELit"; "BEnv"; "BKImg"; "BKWr"; "BSA"; "BSE"; "Badenot"; "Bcarry"; "Bedenot"; "Benv"; "Bev"]; ["Bexpr"; "Bkentry"; "Bridx"; "Bsaddr"; "Bsentry"; "Bsidecond"; "Cestart"; "Cflat"; "Ckentry_ok"; "Cknow_ok"; "Cmem_denot"; "Cregs_ok"; "Dexpr_vars_lt"; "Dkn_vars_lt"; "Dsr_vars_lt"; "Dvals_ev"]; ["EIn"; "Enth_error"; "Fadd"; "Fle"; "Flt"; "Fof_nat"; "Fpow"; "0a"; "0b"; "0bs"; "0e"; "0ebs"; "0extra"; "0f"; "0hi"; "0hs"]; ["0i"; "0ihi"; "0j"; "0k"; "0k1"; "0k2"; "0kept"; "0kk"; "0kn"; "0kn'"; "0len"; "0lo"; "0log"; "0m"; "0n"; "0r"]; ["0sa"; "0scs"; "0segs"; "0spi"; "0sr"; "0sr'"; "GBV"; "GZ_to_bv"; "Gbv"; "Gbv_unsigned"; "0t"; "0ub"; "0uk"; "0un"; "0v"; "0vals"]; ["0w"; "0x"; "0z"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.
Lemma know_nth : ltac2:(TCodec.tc2 tcn__SymDriveX "Q9'6'K%211'QN'SHyR0%211'9y8%511%311p051'R1%=11'7&R9r6r5r4r3%544321'?%?1:&RA%13<65(1r2%22?1%73641&R8r8r7%3421@=p051p0>1pQFG1pV2F1pVBH1pR6K1pQDQ41pW6Q61").
Proof.
intros segs E M kn i K HK Hn. unfold know_ok in HK.
apply (proj1 (Forall_forall _ _) HK K). eapply nth_error_In. exact Hn.
Qed.
Lemma know_ok_app : ltac2:(TCodec.tc2 tcn__SymDriveX "Q2'6'K%211'QN'SHyR0%211'9y8%511%311p051'R1%=11&@&R9r5r4r3&2r2r1%33:21%847651'>%:49875%;4:985%3221%>251pV<@1pV:A1pR6D1pQDM1pW6O1").
Proof. intros. unfold know_ok. apply Forall_app. Qed.
Lemma know_ok_cons : ltac2:(TCodec.tc2 tcn__SymDriveX "Q2'6'K%211'QN'SHyR0%211'9y8%511%311p051'R1%=11&R8r5r4r3r2%544321&R9r6%241764r7(4%13=98%6435;1p051p091pVB@1pQFB1pR6D1pQDM1pW6O1").
Proof. intros. constructor; assumption. Qed.
Fixpoint kindex (p : kentry -> bool) (kn : list kentry) (i : nat) : option nat :=
match kn with
| [] => None
| K :: r => if p K then Some i else kindex p r (S i)
end.
Definition is_krange (e : expr) (K : kentry) : bool :=
match K with KRange e' _ _ => expr_eqb e e' | _ => false end.
Definition is_kalign (e : expr) (K : kentry) : bool :=
match K with KAlign e' _ => expr_eqb e e' | _ => false end.
Definition is_kdisj (b1 : expr) (b2 : expr) (K : kentry) : bool :=
match K with
| KDisj (SA c1 _) _ (SA c2 _) _ => expr_eqb b1 c1 && expr_eqb b2 c2
| _ => false
end.
Definition is_kwr_cov (b : expr) (k m : Z) (K : kentry) : bool :=
match K with
| KWr (SA c kk) len => expr_eqb b c && Z.leb kk k && Z.leb (k + m) (kk + len)
| _ => false
end.
Definition is_kimg_cov (a n : Z) (K : kentry) : bool :=
match K with
| KImg lo hi => Z.leb lo a && Z.leb (a + n) hi
| _ => false
end.
Lemma rdn_agree : ltac2:(TCodec.tc2 tcn__SymDriveX "Q>'6'K%211'SHyR0%211'9y8%511%311pX451'7&Er1r3%3221'?r6&SG&RB&SI%12A7&REr2%211%6241%82F1%:11r5%113%>3E31p0@1pV6E1%Q11I%L11&Q9%14C8=Fr4%34E1?H%G3531p081pU@Q41pVNO1pR8Q11pR6Q21pW6Q;1").
Proof.
intros segs M M' n. induction n as [|n IH]; intros a Hag; [reflexivity|].
cbn [rdn].
pose proof (Hag 0%nat ltac:(lia)) as H0.
rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned in H0. rewrite H0.
rewrite (IH (a + 1)); [reflexivity|].
intros j Hj. rewrite w_add_1.
pose proof (u64_range a) as Ha.
destruct (Z_lt_le_dec (bv_unsigned a + 1) (2 ^ 64)) as [Hlt | Hge].
- rewrite u_small by lia.
replace (bv_unsigned a + 1 + Z.of_nat j)%Z with (bv_unsigned a + Z.of_nat (S j))%Z by lia.
apply Hag. lia.
- replace (Z_to_bv 64 (bv_unsigned a + 1)) with (Z_to_bv 64 0)
by (apply bv_eq; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod; replace (bv_unsigned a + 1)%Z with (2^64)%Z by lia; reflexivity).
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
specialize (Hag (S j) ltac:(lia)).
replace (bv_unsigned a + Z.of_nat (S j))%Z with (2 ^ 64 + Z.of_nat j)%Z in Hag by lia.
replace (Z_to_bv 64 (2 ^ 64 + Z.of_nat j)) with (Z_to_bv 64 (0 + Z.of_nat j)) in Hag; [exact Hag|].
apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
rewrite <- (Zplus_mod_idemp_l (2 ^ 64) (Z.of_nat j)), Z_mod_same_full. reflexivity.
Qed.
Lemma rdn_untouched : ltac2:(TCodec.tc2 tcn__SymDriveX "QO'6'K%211'SHyR0%211'9y8%511%311pX451'H'7&RCzr2%3221&RBr3&RE%115%4231&RF+2+R0%3221%=251'>r5r1%A221&RDr4%>11%A261%4261%9261'?r7&SG%12Q4I%311(0%11Q3%73Q331p091pV2Q31%Q?1Q7%Q:11&Q9r6%<2Q?G%34>21Dq0Q@:%54@13F%B3731p0:1p0O1p0Q:1pVNQ?1pU@QA1pR6QC1pW6QL1").
Proof.
intros segs M a n H0 Hnw Hnone. apply rdn_agree. intros j Hj.
rewrite u_small by lia. rewrite Hnone by lia. reflexivity.
Qed.
Lemma kimg_rdn : ltac2:(TCodec.tc2 tcn__SymDriveX "R2'6'K%211'QN'SHyR0%211'9y8%511%311p051'R1%=11'7'H&R9r9r8r7r6%544321'?%@1;&RA%13=65(1(QGr5r4%3221%52C1%:3971&RC%12>5&RB&RE%118%32:1%621C%Q81O%Q211&Q9r=r;&SG%12Q9J%54431C(0%11Q8q0Q<1%94815G%N3;51p0>1p0D1p0G1p0Q31pVNQ;1pU@Q;1pUNQ<1pVHQ=1pV2Q?1pVBQA1pR6QD1pQDQM1pW6QO1").
Proof.
intros segs E M kn i lo hi a n HK Hn Hlo Hhi.
pose proof (know_nth segs E M kn i _ HK Hn) as (H0 & H64 & Hnone).
apply rdn_untouched; [lia | lia |]. intros j Hj. apply Hnone. lia.
Qed.
Lemma kwr_store_ok : ltac2:(TCodec.tc2 tcn__SymDriveX "R6'6'K%211'QN'SHyR0%211'9y8%511%311p051'R1%=11'7'R0'H&R9r:r9r8r7%544321'?%A1<&RA%13>65(1(QH(QIr6r5%3221r4%6221%82G1%=3<:1&RC%1285&RB&RE%118%32;1%42F=%7221'3&Mr>r<&QKr=%F2Q0E%3221%74651F(<%Q03:21p0<1p0C1p0F1p0Q51pVLQ>1pV8Q=1pVFQ>1pV@Q?1pUBQA1pV2QC1pVBQE1pR6QH1pQDR11pW6R31").
Proof.
intros segs E M kn i b kk len k m HK Hn H1 H2.
pose proof (know_nth segs E M kn i _ HK Hn) as (Hfl & Hst).
unfold adenot. cbn [a_base a_off].
destruct Hfl as (F1 & F2 & F3 & F4). unfold estart in *. cbn [a_base a_off] in *.
specialize (Hst (k - kk)%Z m ltac:(lia) ltac:(lia)).
replace (bv_unsigned (edenot E b) + kk + (k - kk))%Z with (bv_unsigned (edenot E b) + k)%Z in Hst by lia.
unfold v_addi. exact Hst.
Qed.
Lemma kwr_store_ok_lit : ltac2:(TCodec.tc2 tcn__SymDriveX "R>'6'K%211'QN'SHyR0%211'9y8%511%311p051'R1%=11'7'H&R9r9r8r7r6%544321'?%@1;&RA%13=65(1(QH(QI(QEz%211r5%5221r4%8221%:2H1%?3><1&RC%12C5&RB&RE%118%32;1%42IH%7221'>%92AK&RD&RF+2+R0%3221%52Q11%8271'3&Mr>r<&SG%12QGQ9%54431Q9(<%Q93821p0:1p0D1p0K1p0N1p0Q?1pVLQG1pV8QG1pVFQH1pV@QI1pV2QK1pVBQM1pR6R01pQDR91pW6R;1").
Proof.
intros segs E M kn i kk len k m HK Hn H1 H2 Hk.
pose proof (kwr_store_ok segs E M kn i (ELit 0) kk len k m HK Hn H1 H2) as H.
unfold adenot, v_addi in H. cbn [a_base a_off edenot] in H.
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in H. rewrite Z.add_0_l in H. exact H.
Qed.
Definition entry_below_b (spi : nat) (ihi : Z) (e : sentry) : bool :=
match e with
| SE (SA (EVar i) k) w _ => Nat.eqb i spi && Z.leb (k + Z.of_nat w) 0 && Z.leb (- 2 ^ 40) k
| SE (SA (ELit 0) k) w _ => Z.leb 0 k && Z.leb (k + Z.of_nat w) ihi
| _ => false
end.
Definition log_below_b (spi : nat) (ihi : Z) (log : list sentry) : bool :=
forallb (entry_below_b spi ihi) log.
Lemma entry_below_sound : ltac2:(TCodec.tc2 tcn__SymDriveX "R1'QN'7'H'R0'SHyR0%211'?'3&Q?r7r6(QJ(QIr5r4%3221r3r2%73321%;3:91(<%?3>21&RC&RF+2+Q8%3221&SI&QOr9r8%3221%52L1%;271r:%7216%92Q01%:2Q1E%@221%<2Q3I%B2;1&RB&QKr<%Q02?>%3221%C2Q:1&RE%11Q7%8231%G2Q>Q5%M221p0<1p0?1p0E1p0Q21pX4QC1pWNQG1pX2QJ1pV8QJ1pUBQJ1pV4QL1pW8QN1pQDR01").
Proof.
intros E spi ihi b k w v x He Hsp Hx1 Hx2.
unfold adenot, v_addi. cbn [a_base a_off]. pose proof (u64_range x) as Hxr.
destruct b as [z|i| | | | | |]; cbn [entry_below_b] in He; try discriminate.
- destruct z; try discriminate. apply andb_prop in He as [He1 He2].
apply Z.leb_le in He1. apply Z.leb_le in He2. cbn [edenot].
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l, u_small by lia. lia.
- apply andb_prop in He as [He1 He3]. apply andb_prop in He1 as [He1 He2].
apply Nat.eqb_eq in He1. subst i. apply Z.leb_le in He2. apply Z.leb_le in He3.
cbn [edenot]. pose proof (u64_range (ev E spi)) as Hs. rewrite u_small by lia. lia.
Qed.
Lemma mem_denot_above : ltac2:(TCodec.tc2 tcn__SymDriveX "QJ'QN'SHyR0%211'9y8%511%311p051'6'R4%211'7'H'?'3&QBr3r2r4%43321(<%83721&RC&RF+2+Q8%3221&SI&QOr7%221<%42N1%:261r8r5%7221%92Q31%:2Q4E%@221%<2Q6E%B261&R:r:r9%3421;:%21;%Q13Q821p071p0:1p0A1p0M1pX4QA1pV4Q81pW8Q:1pVJQ<1pR6Q@1pQDQI1").
Proof.
intros E M log spi ihi x Hb Hsp Hx1 Hx2.
induction log as [|[[b k] w v] rest IH]; [reflexivity|].
cbn [log_below_b forallb] in Hb. apply andb_prop in Hb as [He Hrest].
pose proof (entry_below_sound E spi ihi b k w v x He Hsp Hx1 Hx2) as Hbnd.
pose proof (u64_range x) as Hxr.
cbn [mem_denot]. rewrite wbytes_outside.
- apply IH. exact Hrest.
- rewrite length_N_to_le_bytes. lia.
- rewrite length_N_to_le_bytes. right. lia.
Qed.
Lemma rdn_mem_denot_above : ltac2:(TCodec.tc2 tcn__SymDriveX "R>'6'K%211'QN'SHyR0%211'9y8%511%311p051'R4%=11'7'H'?'3&QBr4r3r5%43321(<%83721&RC&RF+2+Q8%3221&SI&QOr8%221<%42M1%:261r9r6%7221%92Q21%:2Q3E%@221%<2Q5E%B261&RB%?2Q88&RE%11J%4231+R0%H2G1%J231%QD1Q;%Q>11&Q9r=&R:r<r;r:%43321r7%84721I%94852J%Q@3;21p0>1p0G1p0J1p0Q11p0Q=1pVNQH1pU@R11pV4QI1pW8QK1pVJQM1pR6R01pQDR91pW6R;1").
Proof.
intros segs E M log spi ihi a n Hb Hsp H1 H2 Hnw.
apply rdn_agree. intros j Hj. pose proof (u64_range a).
apply (mem_denot_above E M log spi ihi); try assumption; rewrite u_small by lia; lia.
Qed.
Fixpoint esub (f t : expr) (e : expr) : expr :=
if expr_eqb e f then t else
match e with
| EAlu op a b => EAlu op (esub f t a) (esub f t b)
| EAluw op a b => EAluw op (esub f t a) (esub f t b)
| EMd op a b => EMd op (esub f t a) (esub f t b)
| EMdw op a b => EMdw op (esub f t a) (esub f t b)
| EExt sx lo n a => EExt sx lo n (esub f t a)
| _ => e
end.
Lemma esub_sound : ltac2:(TCodec.tc2 tcn__SymDriveX "H'QN'R0'?'SHyR0%211&QMr4r3%3221r2%5241%:3731r5&Q@%13875%:231%;247%@3=21p071pUFC1pWFD1pULE1pQDG1").
Proof.
intros E f t e Hft. induction e; cbn [esub];
(destruct (expr_eqb _ f) eqn:Eq;
[apply expr_eqb_eq in Eq; rewrite <- Eq in Hft; symmetry; exact Hft|]);
cbn [edenot]; try reflexivity;
try (rewrite IHe1, IHe2; reflexivity);
try (rewrite IHe; reflexivity).
Qed.
Definition asub (f t : expr) (a : saddr) : saddr := SA (esub f t (a_base a)) (a_off a).
Lemma asub_sound : ltac2:(TCodec.tc2 tcn__SymDriveX "J'QN'R0'R3'?'SHyR0%211&QMr4r3%3221r2%5241%:3731&QKr5&Q>%13986%4231%5248%A3>21p081pU@D1pWFF1pULG1pQDI1").
Proof. intros E f t [b k] H. unfold asub, adenot. cbn [a_base a_off]. rewrite esub_sound by exact H. reflexivity. Qed.
Lemma asub_estart : ltac2:(TCodec.tc2 tcn__SymDriveX "K'QN'R0'R3'?'SHyR0%211&QMr4r3%3221r2%5241%:3731'H&R6r5&Q>%13:97%4231%5249%B3721p091pU@E1pWFG1pULH1pQDJ1").
Proof. intros E f t [b k] H. unfold asub, estart. cbn [a_base a_off]. rewrite esub_sound by exact H. reflexivity. Qed.
Definition ksub (f t : expr) (K : kentry) : kentry :=
match K with
| KWord a w v => KWord (asub f t a) w (esub f t v)
| KZero a n => KZero (asub f t a) (esub f t n)
| KBlob a n bk => KBlob (asub f t a) (esub f t n) bk
| KImg lo hi => K
| KAlign e m => KAlign (esub f t e) m
| KRange e lo hi => KRange (esub f t e) lo hi
| KWr a n => KWr (asub f t a) n
| KDisj a1 n1 a2 n2 => KDisj (asub f t a1) n1 (asub f t a2) n2
end.
Lemma flat_asub : ltac2:(TCodec.tc2 tcn__SymDriveX "N'QN'R0'R3'H'?'SHyR0%211&QMr5r4%3221r3%5241%:3731&@&R7r6&Q>%13:97r2%53421%635:2%8221p0:1pVNF1pU@H1pWFJ1pULK1pQDM1").
Proof. intros E f t a n H. unfold flat. rewrite asub_estart by exact H. tauto. Qed.
Lemma ksub_sound : ltac2:(TCodec.tc2 tcn__SymDriveX "Q7'6'K%211'QN'SHyR0%211'9y8%511%311p051'R0'R1'?&QMr5r3%3221r2%5241%73?31&R8r7r6%342196r8&QAr4%23=1<%844761p061p0;1pQFD1pWFF1pULG1pR6I1pQDQ21pW6Q41").
Proof.
intros segs E M f t K H HK. destruct K; cbn [ksub kentry_ok] in *.
- rewrite (asub_sound E f t a H), (esub_sound E f t v H). rewrite (flat_asub E f t a _ H). exact HK.
- unfold elenZ in *. rewrite (esub_sound E f t n H), (asub_estart E f t a H). rewrite (flat_asub E f t a _ H). exact HK.
- unfold elenZ in *. rewrite (esub_sound E f t n H), (asub_estart E f t a H). rewrite (flat_asub E f t a _ H). exact HK.
- exact HK.
- rewrite (esub_sound E f t e H). exact HK.
- rewrite (esub_sound E f t e H). exact HK.
- rewrite (asub_estart E f t a H). rewrite (flat_asub E f t a _ H). exact HK.
- rewrite (asub_estart E f t a1 H), (asub_estart E f t a2 H). exact HK.
Qed.
Lemma know_ok_ksub : ltac2:(TCodec.tc2 tcn__SymDriveX "Q:'6'K%211'QN'SHyR0%211'9y8%511%311p051'R0'R1%>11'?&QMr5r3%3221r2%5241%73@31&R9r7r6%342196r8&F&QAr4%22>1%44CC1>%:46981p081p0=1pVBF1pWFI1pULJ1pR6L1pQDQ51pW6Q71").
Proof.
intros segs E M f t kn H HK. unfold know_ok in *. apply Forall_map.
eapply Forall_impl; [|exact HK]. intros K. apply ksub_sound. exact H.
Qed.
Lemma regs_ok_esub : ltac2:(TCodec.tc2 tcn__SymDriveX "Q3'QN'R0'6%112&Q1y5'SHyR0%211%5241'?&QMr5r4%3221r3%5241%73931&R;r6r2%33261r7&F&Q@%126=%34II1=%9351<p071p0<1pR:E1pW:L1pWFO1pULQ01pQDQ21").
Proof.
intros E f t sr R H HR r. rewrite (HR r). unfold sr_get.
destruct (bv_eqb r 0); [reflexivity|].
revert sr HR. generalize (ridx r) as i. intros i sr _.
revert i. induction sr as [|e rest IH]; intros i.
- destruct i; reflexivity.
- destruct i as [|i]; cbn [map nth].
+ symmetry. apply esub_sound. exact H.
+ apply IH.
Qed.
Lemma regs_ok_ext : ltac2:(TCodec.tc2 tcn__SymDriveX "Q@'QN'6'R0%211&Q1y5'SHyR0%211%5241'?'7&5r3%22<1r2%42>1%73631&Er1r5%92C1%4231&QMr7&Gr6(QEz%211%54L?41%8271%74NA<3%:291%H3J31p0=1pV2I1&R;%13<BIr4%33@D1p031p061p0J1pR:Q31pW<Q:1pW:Q;1pQDQ?1").
Proof.
intros E sr sr' R Hlen Heq HR r. rewrite (HR r). unfold sr_get.
destruct (bv_eqb r 0); [reflexivity|].
destruct (Nat.lt_ge_cases (ridx r) (length sr)) as [Hlt | Hge].
- apply Heq. exact Hlt.
- rewrite !nth_overflow by lia. reflexivity.
Qed.
Lemma junk_vals_length : ltac2:(TCodec.tc2 tcn__SymDriveX "@&Q1y5'SHyR0%211%5241'?'7&5&Q;r1%211%4281uQ0%83721pR::1").
Proof. intros R. unfold junk_vals. rewrite length_map, length_seq. reflexivity. Qed.
Lemma vals_ev_app_l : ltac2:(TCodec.tc2 tcn__SymDriveX "I'6'SHyR0%211%411'7&Er1&5r3%2271%5241'?&R?&2r4%23=17r2%5221%6242%83A21p0:1pVNA1pUJC1pX0D1").
Proof. intros. unfold vals_ev. rewrite app_nth1 by assumption. reflexivity. Qed.
Lemma vals_ev_app_r : ltac2:(TCodec.tc2 tcn__SymDriveX "G'6'SHyR0%211%411'7'?&R?&2r3r2%33821&C&5%12;5r1%4221%:261%;283%=3@21pVN?1pUJA1pX0B1").
Proof. intros. unfold vals_ev. rewrite app_nth2_plus. reflexivity. Qed.
Lemma env_app_know : ltac2:(TCodec.tc2 tcn__SymDriveX "QD'6'K%211'SHyR0%211%611'7y8%611%:11p041'9%114p091'R1%@11'?'3&R=&5r5%22A1r1%5221(<%93821&R9r7(QF&R?r6%211r4%5221r3r2%:49321r8&2%13Q3<9%;11%=21E%@451:8p071p0C1pVBN1pR6Q11pUHQ51pUJQ;1pX0Q<1pW6QA1").
Proof. intros. eapply know_ok_agree; [apply vals_app_agree | eassumption | eassumption]. Qed.
Lemma env_app_regs : ltac2:(TCodec.tc2 tcn__SymDriveX "Q?'6'SHyR0%211%411'7y8%611%811p041'R0%;11&Q1y5%221;'?'3&R>&5r5%22A1r2%5221(<%93821&R;(QF&R?r6%211r4%5221r3%8321<&2r7%23Q118%:11%<21C%>3197p071p0A1pR:L1pW:Q01pUHQ31pUJQ91pX0Q:1").
Proof. intros. eapply regs_ok_agree; [apply vals_app_agree | eassumption | eassumption]. Qed.
Lemma env_app_edenot : ltac2:(TCodec.tc2 tcn__SymDriveX "Q9'6'SHyR0%211%411'7y8%611%811p041'R0'?'3&R<&5r4%22=1r1%5221(<%93821&QM(QF&R?&2r5%23G1;%411r3%7221r2%:221%917%;215%=214%H3Q041p0@1pUFK1pUHM1pUJQ31pX0Q41").
Proof. intros. symmetry. eapply edenot_agree; [apply vals_app_agree | assumption]. Qed.
Lemma regs_after_keeps : ltac2:(TCodec.tc2 tcn__SymDriveX "R>'6'SHyR0%211%411'7y8%611%811p041'R0%;11&Q1y5%221;%>12%@11'?'3&R>&5r6%22C1r4%5221(<%93821&R;(QF&R?r7%211%421;r5%7321;&R@r1%23F1>&Q8r2%22C1%32;2%I3Q721p061pW0M1&A(SFz(=%33Q421%?3Q31K%611&2r:&Q;%11Q2%43QE31%L11r9%O221&Q<r8&F&R2%24QAQK1O%Q=2QN<%63521%Q8381Q>p0A1p0I1p0Q41p0Q=1pV>QH1pR<QK1pR:QL1pW:R01pUHR31pX0R91").
Proof.
intros vals ebs sr R R' kept Hlt HR Hk H0.
apply (regs_after_call vals ebs sr R R' (map ridx kept) Hlt HR).
- intros i Hi. apply in_map_iff in Hi as (r & <- & Hr). split; [apply ridx_range|].
rewrite ridx_roundtrip. apply Hk. exact Hr.
- intros Hin. apply in_map_iff in Hin as (r & Hr0 & Hr). apply H0.
replace 0%bv with r; [exact Hr|]. apply ridx_inj. rewrite Hr0. reflexivity.
Qed.
Lemma know_after_store : ltac2:(TCodec.tc2 tcn__SymDriveX "RN'6'K%211'QN'SHyR0%211'9y8%511%311p051'R1%=11'R3'7'R0%A18'R5%C11'3%E11'?';%12;5%2214&QL(4'R4(QJr7r6r5%43321(8%117%93831r8%41B%=3321(:r3r2%34NH21r1%54EH21%H3E71%=1M%J3M71&R9r=r<r;r:%544321'Dr9u8%3221&R7r>&RE%119%433;1&N&QMr?%221>%42@1%Q?3QD=1rAr@&Q6&QK%123H%3391F%K4651Dp081p0?1p0E1p0J1p0Q11p0Q41pV0QN1pW4R11pVDR81pUDR51pWNR71pX2R91pW2R;1pVBR=1pR6R@1pQDRI1pW6RK1").
Proof.
intros segs E M kn sa w v bs kn' scs hs Hc -> HK Hw Hfl ->.
change (wbytes M (adenot E sa) (word_to_le_bytes w (edenot E v))) with (mem_denot E M [SE sa w v]).
eapply carry_after; [exact Hc | | exact HK | constructor].
cbn [log_flat]. auto.
Qed.
Lemma Z_to_bv_lit : ltac2:(TCodec.tc2 tcn__SymDriveX "A'H'SHyR0%211'?&SIr1%2251r2%53921&SGr3%22:1%93:15p051pX2<1pX6@1").
Proof. intros z w <-. apply Z_to_bv_bv_unsigned. Qed.
Lemma flat_intro : ltac2:(TCodec.tc2 tcn__SymDriveX "Q?'QN'R0'H&RCz&RB&SIyR0&QMr4r3%3221%6251r2%9221%<2;1%=2<3&RDr6r5%<221%?2>1%A21=&RF+2+R0%3221%:251r7%E21;%H2G1%J21<%K21G%N217&R7r8(QI%129C%4331Cp061p0=1p0I1p0K1pVNQ91pV8Q:1pUBQ<1pQDQ>1").
Proof. intros. unfold flat, estart. cbn [a_base a_off]. lia. Qed.
Definition ECALLW : bv 32 := Z_to_bv 32 0x73.
Lemma is_ecall_ECALLW : ltac2:(TCodec.tc2 tcn__SymDriveX "7'?'3&L&Q=%211(<%63521"). Proof. reflexivity. Qed.
Lemma adenot_lit0 : ltac2:(TCodec.tc2 tcn__SymDriveX "D'QN'H'?'SHyR0%211&QKr2(QI(QEz%211r1%5221%8271&SG%12<4%?3<31pU@A1pQDC1").
Proof. intros. unfold adenot, v_addi. cbn [a_base a_off edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l. reflexivity. Qed.
Lemma edenot_add_lit : ltac2:(TCodec.tc2 tcn__SymDriveX "I'QN'R0'H'?'SHyR0%211&QMr3(QD(Q0r2(QEr1%211%63541%9281&QK(QI%1286%32<1%B3?51pV8D1pUBF1pQDH1").
Proof.
intros. cbn [edenot]. rewrite alu_add. unfold adenot, v_addi, v_add. cbn [a_base a_off].
apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. apply Zplus_mod_idemp_r.
Qed.
End FPX_1.
Ltac split_foralls :=
repeat lazymatch goal with
| |- scs_denot _ _ _ [] => constructor
| |- scs_denot _ _ _ (_ :: _) => constructor; [| ]
| |- Forall _ [] => constructor
| |- Forall _ (_ :: _) => constructor; [| ]
end.
Ltac run_block_with HR HK fuel stops scr NX keep :=
lazymatch type of HR with
| regs_ok ?E ?sr ?R =>
lazymatch type of HK with
| know_ok ?segs _ ?M ?kn =>
lazymatch goal with
| |- srealizes _ ?scfg (mkCfg (mkst R (Z_to_bv 64 ?pc) M ?rom) ?model) ?T =>
let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn NX) []) in
lazymatch r with
| (?ss', ?scs, ?scr') =>
let c := eval vm_compute in (carry (s_log ss') kn []) in
lazymatch c with
| (?kn', ?scs2, ?hs2) =>
eapply (rz_run segs scfg fuel stops scr pc sr kn NX ss' scs scr' kn' scs2 hs2 E M rom R model T);
[ vm_compute; reflexivity
| vm_compute; reflexivity
| exact HR | exact HK
| split_foralls
| split_foralls
| try reflexivity; try assumption
| try reflexivity; try assumption
| clear HR HK;
let R' := fresh "R" in let M' := fresh "M" in let EQM := fresh "EQM" in
intros R' M' HR HK EQM; cbn [s_pc s_regs s_log] in HR, EQM |- *;
lazymatch keep with
| true => idtac
| false => clear EQM; try clear R; try clear M;
try rename R' into R; try rename M' into M
end ]
end
end
end
end
end.
Tactic Notation "run_block_gen" constr(fuel) constr(stops) constr(scr) constr(NX) constr(keep) :=
match goal with
| HR : regs_ok _ _ _, HK : know_ok _ _ _ _ |- _ => run_block_with HR HK fuel stops scr NX keep
end.
Ltac regv HR r :=
lazymatch type of HR with regs_ok ?E ?sr ?R =>
let e := eval vm_compute in (sr_get sr r) in
rewrite (reg_val E sr R r HR); change (sr_get sr r) with e;
lazymatch e with ELit _ => cbn [edenot] | _ => idtac end
end.
Ltac krd HK a n H :=
lazymatch type of HK with
| know_ok ?segs ?E ?M ?kn =>
let r := eval vm_compute in (kread segs kn (ELit 0) a n) in
lazymatch r with
| Some ?v =>
pose proof (kread_rdn segs E M kn (ELit 0) a n v HK
ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)
ltac:(unfold flat, estart; cbn [a_base a_off edenot];
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia)) as H;
rewrite adenot_lit0 in H; cbn [edenot] in H
| None => fail "krd: knowledge does not determine this read"
end
end.
Ltac krdv HK i k n H :=
lazymatch type of HK with
| know_ok ?segs ?E ?M ?kn =>
let r := eval vm_compute in (kread segs kn (EVar i) k n) in
lazymatch r with
| Some ?v =>
let Hf := fresh "Hflat" in
assert (Hf : flat E (SA (EVar i) k) (Z.of_nat n));
[ | pose proof (kread_rdn segs E M kn (EVar i) k n v HK
ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) Hf) as H;
clear Hf; cbn [edenot] in H ]
| None => fail "krdv: knowledge does not determine this read"
end
end.
Ltac kidx kn p :=
let r := eval vm_compute in (kindex p kn 0) in
lazymatch r with Some ?i => i | None => fail "kidx: no such entry" end.
Ltac krd_solve HK :=
lazymatch goal with
| |- rdn _ _ (Z_to_bv 64 ?a) ?n = Some _ =>
let H := fresh "Hrd" in
krd HK a n H; rewrite H; clear H;
first [ reflexivity | rewrite ?Z_to_bv_bv_unsigned; reflexivity | idtac ]
end.
Section FPX_2. Context {fx : PropExec.FPState}.
Lemma callee_kept_no0 : ltac2:(TCodec.tc2 tcn__SymDriveX "=&A&R@'SHy5%211(SFz(=%33521/015&Q:%:3721%<11").
Proof.
unfold callee_kept. intros Hin.
repeat (destruct Hin as [Hin|Hin]; [apply (f_equal bv_unsigned) in Hin; cbn in Hin; discriminate Hin|]).
exact Hin.
Qed.
Definition kentry_apart_b (allkn : list kentry) (ub : expr) (uk un : Z) (K : kentry) : bool :=
match K with
| KWord (SA b k) w _ => ranges_apart allkn ub uk un b k (Z.of_nat w)
| KZero (SA b k) (ELit l) => Z.leb 0 l && Z.ltb l (2 ^ 64) && ranges_apart allkn ub uk un b k l
| KBlob (SA b k) (ELit l) _ => Z.leb 0 l && Z.ltb l (2 ^ 64) && ranges_apart allkn ub uk un b k l
| KImg _ _ => true
| KAlign _ _ => true
| KRange _ _ _ => true
| KDisj _ _ _ _ => true
| KWr (SA b k) n => ranges_apart allkn ub uk un b k n
| _ => false
end.
Definition kn_unfill (kn : list kentry) (ub : expr) (uk un : Z) : list kentry :=
List.filter (kentry_apart_b kn ub uk un) kn.
Lemma unfill_outside : ltac2:(TCodec.tc2 tcn__SymDriveX "Q3'SHyR0%211'9y8%511%311p051'B&RD&SIr1%22;1r4%42=1%6231&RC&RBr3%92B1%3261%5219%>271'?&Q7r5r2%342>91%:12%63G21p081pX4M1pR6I1pVNO1pU@Q01").
Proof.
intros a n M x H. unfold unfill.
destruct H as [H|H].
- rewrite (proj2 (Z.leb_gt _ _) H). reflexivity.
- destruct (bv_unsigned a <=? bv_unsigned x)%Z; [|reflexivity].
rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity.
Qed.
Lemma unfill_none : ltac2:(TCodec.tc2 tcn__SymDriveX "J'SHyR0%211'9y8%511%311pX451'?r2r1%211(0%118%63831&Q7r5r4r3%44321:%<3>17p071pX4D1pR6@1pVNF1pU@G1").
Proof. intros a n M x H. unfold unfill. rewrite H. destruct (_ && _)%bool; reflexivity. Qed.
Lemma wview_ext : ltac2:(TCodec.tc2 tcn__SymDriveX "M'6'K%211'SHyR0%211'9y8%511%311pX451'?r2r1%211r3%113%63831&Or5%23158r4%4331:%<3>31p071pX4D1pR8@1pR6A1pW6J1").
Proof. intros segs M M' x H. unfold wview. rewrite H. reflexivity. Qed.
Lemma store_ok_agree : ltac2:(TCodec.tc2 tcn__SymDriveX "QN'6'K%211'SHyR0%211'9y8%511%311pX451'7&RC&RB&SIr2%22<1&REr1%211%7241&RF+2+R0%3221%=251'>r4%>2H1%?2I;%B221&RDr3%@11%E261%4261%:261'?r6%11Hr7%11J%53Q131p071pX4Q71'3&M%1479D?(<%<3421r8r5%642>1I%@3815p051p0;1p0O1pVNQ>1pU@QE1pR8QA1pR6QB1pW6QK1").
Proof.
intros segs M M' a n Hnw Hag Hs. apply store_ok_of_all; [exact Hnw|].
intros x Hx. rewrite (wview_ext segs M M' x (Hag x Hx)). exact (store_ok_all segs M n a Hnw Hs x Hx).
Qed.
Lemma know_ok_unfill : ltac2:(TCodec.tc2 tcn__SymDriveX "QI'6'K%211'QN'SHyR0%211'9y8%511%311p051'R1%=11'R0'H&R9r7r6r5r4%544321&R7(QIr3%2251r2%53:21&RD&RF+2+R0%3221%5291r:r9&Q7&QK%?2DC%2241&SG%12Q4Er8%73421&QC%14LKJI%N4<;31p0>1p0E1p0L1pWLQ31pWJQ41pWHQ61pVBQ81pR6Q;1pQDQD1pW6QF1").
Proof.
intros segs E M kn ub uk un HK Hfl Hun.
pose proof (flat_u E _ _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
set (a := adenot E (SA ub uk)) in *. set (nw := Z_to_bv 64 un).
assert (Hn : bv_unsigned nw = un) by (subst nw; apply u_small; lia).
assert (OUT : forall x : word,
(bv_unsigned x < estart E (SA ub uk) \/ estart E (SA ub uk) + un <= bv_unsigned x)%Z ->
unfill a nw M x = M x).
{ intros x Hx. apply unfill_outside. rewrite Hu, Hn. exact Hx. }
unfold know_ok, kn_unfill. apply Forall_forall. intros K HinF.
apply filter_In in HinF as [Hin Hb].
pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
assert (APART : forall b k n, ranges_apart kn ub uk un b k n = true ->
((estart E (SA ub uk) + un <= estart E (SA b k))%Z \/ (estart E (SA b k) + n <= estart E (SA ub uk))%Z)).
{ intros b k n H. eapply ranges_apart_sound; [exact HK | exact H]. }
destruct K as [[b k] w v|[b k] len|[b k] len bk|lo hi|e m|e lo hi|[b k] n|a1 n1 a2 n2];
cbn [kentry_apart_b] in Hb; cbn [kentry_ok] in HKK |- *; try exact HKK.
-
destruct HKK as (Hw & Hf & Hr). split; [exact Hw|]. split; [exact Hf|].
rewrite <- Hr. apply rdn_agree. intros j Hj.
pose proof (flat_u E _ _ Hf) as Hub. destruct Hf as (G1 & G2 & G3 & G4).
apply OUT. rewrite u_small by lia. destruct (APART b k (Z.of_nat w) Hb); lia.
-
destruct len as [l| | | | | | |]; try discriminate.
apply andb_prop in Hb as [Hb Hap]. apply andb_prop in Hb as [Hl0 Hl1].
apply Z.leb_le in Hl0. apply Z.ltb_lt in Hl1.
destruct HKK as (Hf & Hz). split; [exact Hf|].
assert (El : elenZ E (ELit l) = l) by (unfold elenZ; cbn [edenot]; apply u_small; lia).
rewrite El in *. destruct Hf as (G1 & G2 & G3 & G4).
intros i Hi. rewrite OUT; [apply Hz; exact Hi|].
rewrite u_small by lia. destruct (APART b k l Hap); lia.
-
destruct len as [l| | | | | | |]; try discriminate.
apply andb_prop in Hb as [Hb Hap]. apply andb_prop in Hb as [Hl0 Hl1].
apply Z.leb_le in Hl0. apply Z.ltb_lt in Hl1.
destruct HKK as (Hf & Hlen & Hz). split; [exact Hf|]. split; [exact Hlen|].
assert (El : elenZ E (ELit l) = l) by (unfold elenZ; cbn [edenot]; apply u_small; lia).
rewrite El in *. destruct Hf as (G1 & G2 & G3 & G4).
intros i Hi. rewrite OUT; [apply Hz; exact Hi|].
rewrite u_small by lia. destruct (APART b k l Hap); lia.
-
destruct HKK as (H0 & H1 & Hnone). split; [exact H0|]. split; [exact H1|].
intros i Hi. apply unfill_none. apply Hnone. exact Hi.
-
destruct HKK as (Hf & Hst). split; [exact Hf|].
destruct Hf as (G1 & G2 & G3 & G4).
intros d m Hd Hm. destruct m as [|m]; [reflexivity|].
apply (store_ok_agree segs M); [rewrite u_small by lia; lia | | apply Hst; assumption].
intros x Hx. rewrite u_small in Hx by lia. apply OUT. destruct (APART b k n Hb); lia.
Qed.
End FPX_2.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
