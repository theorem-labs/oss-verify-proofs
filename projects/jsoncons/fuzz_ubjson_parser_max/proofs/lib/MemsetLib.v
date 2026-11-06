(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk MemSplit MmapSim RefMemcpyLib.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__MemsetLib () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MemsetLib.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MemsetLib.FPX_1.CFill."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1app"; "1bool"; "1cons"; "1false"; "1list"; "1nat"; "1nil"; "1option"; "1orb"; "1pair"; "1prod"; "1true"; "2I"; "2and"; "2eq"]; ["2ex"; "2iff"; "2not"; "2or"; "3repeat"; "4Z"; "0L"; "0L'"; "0L1"; "0L2"; "5Z_to_le_bytes"; "6Segment"; "7MachineOk"; "7fetch_word"; "7is_ecall"; "7machine_result"]; ["7machine_state"; "7step"; "7store_ok"; "7word_to_le_bytes"; "8decode_any"; "9ALU_OR"; "9ALU_SUB"; "9M_MULHU"; "9Mul"; "9Op"; "9Op32"; "9SZ1"; "9SZ4"; "9SZ8"; "9Store"; "9instr"]; [":bv_eqb"; ":bvmap"; ";wbytes"; "<at_"; ">cfill"; "=c32"; "=c32h"; "=c64"; "=cbyte"; "=cbz"; "=cfill"; "=ms_agree"; "=ms_chain"; "=ms_clob"; "=ms_cov"; "=ms_inb"]; ["=ms_repl"; "?getr"; "?mkst"; "?regupd"; "?v_add"; "?v_addi"; "?v_andi"; "?v_mulhu"; "?v_or"; "?v_slli"; "?v_srli"; "?v_sub"; "?v_subw"; "@keeps"; "Amem_grows"; "BIn"]; ["Bincl"; "Cadd"; "Cland"; "Cle"; "Clor"; "Clt"; "Cmodulo"; "Cmul"; "Cof_nat"; "Copp"; "Cpow"; "Csub"; "Cto_nat"; "0a"; "0b"; "0c"]; ["0cv"; "0d"; "0from"; "0fx"; "0i"; "0imm"; "0iv"; "0j"; "0k"; "0m"; "0mem"; "0mem0"; "0n"; "0o"; "0o0"; "0pc"]; ["0r"; "0r1"; "0r2"; "0r3"; "0rd"; "0regs"; "0regs'"; "0rom"; "0rs1"; "0rs2"; "0s4"; "0segs"; "DBV"; "DZ_to_bv"; "Dbv"; "Dbv_signed"]; ["Dbv_unsigned"; "0t"; "0to"; "0u"; "0v"; "0w"; "0x"; "0z"]]).
Section FPX_1. Context {fx : PropExec.FPState}.
Definition ms_inb (i : Z) (iv : Z * Z) : bool := (fst iv <=? i) && (i <? fst iv + snd iv).
Definition ms_cov (L : list (Z * Z)) (i : Z) : bool := existsb (ms_inb i) L.
Lemma ms_inb_true : ltac2:(TCodec.tc2 tcn__MemsetLib "I'E&A'?'2&QOr3(:r2r1%349921%6251(<%:3921'>&RC%128:&RE&RA%12;:%32>1%7251%D291pVDF1pVLG1pV:H1").
Proof.
intros i o m. unfold ms_inb. cbn [fst snd]. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto.
Qed.
Lemma ms_cov_cons : ltac2:(TCodec.tc2 tcn__MemsetLib "G';'E%2211'5%112'?'2&QN(3r3r2%33921r1%6221&9&QO%1247%:275%4221%>3=61pV:C1pQ>A1pV>D1").
Proof. reflexivity. Qed.
Lemma ms_cov_app : ltac2:(TCodec.tc2 tcn__MemsetLib "F'5';'E%2211%411'?'2&QN&1r3r2%33821r1%6221&9%8263%9264%3221%=3<51pV:A1pQD@1pQBA1").
Proof. intros. unfold ms_cov. apply existsb_app. Qed.
Lemma ms_cov_In : ltac2:(TCodec.tc2 tcn__MemsetLib "Q3'5';'E%2211%411&R?(:r2r1%347721r4%63821'>&RCr3%2215&RE&RA%124;%3291%8251'?'2&QNr6r5%3221(<%73621p091p0C1pVDM1pVLN1pV:O1pQ>N1").
Proof.
intros L i o m Hin Hi. unfold ms_cov. apply existsb_exists. exists (o, m). split; [exact Hin|].
apply ms_inb_true. exact Hi.
Qed.
Fixpoint ms_chain (from to : Z) (L : list (Z * Z)) : Prop :=
match L with
| [] => to <= from
| (o, m) :: L' => o <= from /\ ms_chain (o + m) to L'
end.
Lemma ms_chain_cov : ltac2:(TCodec.tc2 tcn__MemsetLib "Q8'5';'E%2211%411&QLr3r2r4%43321'>&RC%1245&RE%1278%5231'@&R?(:r1%24BB=1r8%53C21r5%=2A1&RA%12C7%>241%B241%C271qVDL1%?2M1qVLN1%A2O1p0C1p0J1pV:Q21pX6Q31pV6Q41pQ>Q31").
Proof.
induction L as [|[o m] L IH]; intros from to i Hc Hi; cbn [ms_chain] in Hc.
- lia.
- destruct Hc as [Ho Hc].
destruct (Z.lt_ge_cases i (o + m)) as [Hlt|Hge].
+ exists o, m. split; [left; reflexivity | lia].
+ destruct (IH (o + m) to i Hc ltac:(lia)) as (o' & m' & Hin & Hi').
exists o', m'. split; [right; exact Hin | exact Hi'].
Qed.
Lemma ms_cov_by_chain : ltac2:(TCodec.tc2 tcn__MemsetLib "Q2'5';'E%2211%411&R@r2r3%33521&QLz%23154'>&RCr1%2251&REr4%2241%7241'?'2&QNr7%221B(<%63521p081pV:J1p0B1p0F1pVJM1pQ@L1pQ>M1").
Proof.
intros L L' n Hincl Hc i Hi.
destruct (ms_chain_cov L' 0 n i Hc Hi) as (o & m & Hin & Hom).
apply (ms_cov_In L i o m); [apply Hincl, Hin | exact Hom].
Qed.
Section CFill.
Variable mem0 : word -> option byte.
Variable d : word.
Variable n : Z.
Variable c : byte.
Hypothesis Hn : 0 <= n.
Hypothesis Hnw : bv_unsigned d + n < 2 ^ 64.
Definition cfill (L : list (Z * Z)) : word -> option byte :=
fun x => if (bv_unsigned d <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned d + n)
&& ms_cov L (bv_unsigned x - bv_unsigned d)
then Some c else mem0 x.
Lemma cfill_nil : ltac2:(TCodec.tc2 tcn__MemsetLib "B'?'SNyR0%211'8y8%511%311p051&QD(7';'E%2211%411%611vS;%A3921").
Proof.
apply functional_extensionality. intro x. unfold cfill. cbn [ms_cov existsb].
rewrite andb_false_r. reflexivity.
Qed.
Lemma cfill_grows : ltac2:(TCodec.tc2 tcn__MemsetLib "<'5';'E%2211%411&R>vS;&QDr1%211%5241pQ>71").
Proof.
intros L x Hx. unfold cfill. destruct (_ && _); [discriminate | exact Hx].
Qed.
Lemma cfill_ext : ltac2:(TCodec.tc2 tcn__MemsetLib "Q8'5';'E%2211%411'>&RCzr1%3221&REvS<%2241%8241'?'2&QNr4r2%3221r3%5213%83731p0:1pV:F1'SNyR0%211'8y8%511%311p051&QD%11>%21A%F3421p0=1pQDQ21pQBQ31").
Proof.
intros L1 L2 H. apply functional_extensionality. intro x. unfold cfill.
destruct (Z.leb_spec (bv_unsigned d) (bv_unsigned x)); [|reflexivity].
destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned d + n)); [|reflexivity].
cbn [andb]. rewrite H by lia. reflexivity.
Qed.
Lemma cfill_store : ltac2:(TCodec.tc2 tcn__MemsetLib "QB'5';'E%2211%411'6&RCzr2%3221&RAr3&RH%115%4231vS<%:221'?'SNyR0%211'8y8%511%311p051&QB&QDr5%211&QCvS1r4%3221&DvRO%23=1I%;3841(3(:%L1M%24Q7Q791%43Q71>%@11%K3C71p0M1p0Q51pVDQ:1pVLQ>1pQ>Q=1").
Proof.
intros L o m Ho Hm. apply functional_extensionality. intro x.
pose proof (u64_range d). pose proof (u64_range x).
assert (Ha : bv_unsigned (at_ d o) = bv_unsigned d + o) by (apply at_u; lia).
destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned d + o)) as [Hlo|Hge];
[| destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned d + o + Z.of_nat m)) as [Hin|Hhi]].
- rewrite wbytes_outside by (rewrite repeat_length, Ha; lia).
unfold cfill. rewrite ms_cov_cons.
replace (ms_inb (bv_unsigned x - bv_unsigned d) (o, Z.of_nat m)) with false
by (symmetry; apply not_true_iff_false; rewrite ms_inb_true; lia).
reflexivity.
- rewrite wbytes_inside by (rewrite repeat_length, Ha; lia).
rewrite nth_repeat_lt by (rewrite Ha; lia). unfold cfill. rewrite ms_cov_cons.
replace (ms_inb (bv_unsigned x - bv_unsigned d) (o, Z.of_nat m)) with true
by (symmetry; apply ms_inb_true; lia).
destruct (Z.leb_spec (bv_unsigned d) (bv_unsigned x)); [|lia].
destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned d + n)); [|lia].
reflexivity.
- rewrite wbytes_outside by (rewrite repeat_length, Ha; lia).
unfold cfill. rewrite ms_cov_cons.
replace (ms_inb (bv_unsigned x - bv_unsigned d) (o, Z.of_nat m)) with false
by (symmetry; apply not_true_iff_false; rewrite ms_inb_true; lia).
reflexivity.
Qed.
Lemma cfill_full : ltac2:(TCodec.tc2 tcn__MemsetLib "Q>'5';'E%2211%411'>&RCzr1%3221&REvS<%2241%8241'?'2&QNr3r2%3221(<%73621p091pV:E1'SNyR0%211'8y8%511%311p051&QD%11?&QBvS;vS1&DvRO&RL%11M%43<31%83761%M3<:1p0E1pQ>Q91").
Proof.
intros L Hcov. apply functional_extensionality. intro x.
pose proof (u64_range d). pose proof (u64_range x).
unfold cfill.
destruct (Z.leb_spec (bv_unsigned d) (bv_unsigned x)) as [H1|H1].
- destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned d + n)) as [H2|H2]; cbn [andb].
+ rewrite Hcov by lia. rewrite wbytes_inside by (rewrite repeat_length; lia).
rewrite nth_repeat_lt by lia. reflexivity.
+ rewrite wbytes_outside by (rewrite repeat_length; lia). reflexivity.
- cbn [andb]. rewrite wbytes_outside by (rewrite repeat_length; lia). reflexivity.
Qed.
Lemma cfill_full_chain : ltac2:(TCodec.tc2 tcn__MemsetLib "Q7'5';'E%2211%411&R@r1r2%33521&QLzvS<%33215'?'SNyR0%211'8y8%511%311p051&QDr4%211&QBvS;vS1&DvRO&RL%11D%43=31%83761%E3=:1p0G1p0L1pQ@Q11pQ>Q21").
Proof. intros L L' Hi Hc. apply cfill_full. apply (ms_cov_by_chain L L'); assumption. Qed.
Lemma cfill_store_ok : ltac2:(TCodec.tc2 tcn__MemsetLib "Q='5'K%211';'E%2211%611'6'?'2&Q2r4vS;vS1&RLvS<%211%746541(<%;3:21&RCzr3%3221&RA&RH%114%32@1%821=r7&QDr6%211&QCr5%22F1%J4741I%M3L1Cp0:1p0@1p0E1pVDQ21pVLQ61pQ>Q51pWHQ:1").
Proof.
intros segs L o m Hok Ho Hm. pose proof (u64_range d).
apply (store_ok_mono segs m mem0); [apply cfill_grows|].
apply (store_ok_sub segs mem0 d (at_ d o) (Z.to_nat n) m); try (rewrite ?at_u; lia). exact Hok.
Qed.
End CFill.
Lemma mod4_mod_pow2_gen : ltac2:(TCodec.tc2 tcn__MemsetLib "I'E'>&RCzr1%3221r2%5231%7231'?&RFr4&RJ+2r3%3221%6251%524;%8221%9282%;3D21p0=1pV@F1pVBG1pX4H1").
Proof.
intros t k j Hk. apply Z.mod_mod_divide.
exists (2 ^ (k - j)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.
Definition cbyte (cv : word) : byte := Z_to_bv 8 (bv_unsigned cv).
Definition cbz (cv : word) : Z := bv_unsigned cv mod 256.
Definition c32 (cv : word) : word := Z_to_bv 64 (cbz cv * 16843009).
Definition c32h (cv : word) : word := Z_to_bv 64 (cbz cv * 16843009 * 2 ^ 32).
Definition c64 (cv : word) : word := Z_to_bv 64 (cbz cv * 72340172838076673).
Lemma cbz_range : ltac2:(TCodec.tc2 tcn__MemsetLib "?'SNyR0%211'>&RCz&QIr1%211%5241&RE+X0%2241%:241pV2<1").
Proof. intros cv. unfold cbz. apply Z.mod_pos_bound. lia. Qed.
Lemma cbyte_mod : ltac2:(TCodec.tc2 tcn__MemsetLib "B'SNyR0%211'?y8%511&SM&RF&T0r1%2291+X0%5221%7291&QH%116%=3;31pV2?1").
Proof.
intros cv. unfold cbyte. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap8_mod. apply Z.mod_mod. lia.
Qed.
Lemma cbyte_cbz : ltac2:(TCodec.tc2 tcn__MemsetLib "?'SNyR0%211'?y8%511&QHr1%211&SM&QI%114%3281%:3851pV2<1").
Proof. intros cv. unfold cbz. symmetry. apply cbyte_mod. Qed.
Lemma cbyte_Z : ltac2:(TCodec.tc2 tcn__MemsetLib ">'E'?'SNy8%211&QH&SMyR0r1%3221%511%5283%;3821pX@=1").
Proof.
intros z. unfold cbyte. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap8_mod, bv_wrap64_mod.
apply mod4_mod_pow2_gen. lia.
Qed.
Fixpoint ms_repl (k : nat) : Z := match k with O => 0 | S k' => 1 + 256 * ms_repl k' end.
Lemma ms_repl_nonneg : ltac2:(TCodec.tc2 tcn__MemsetLib "8'6&RCz&R0r1%211%5241pVB71").
Proof. induction k; cbn [ms_repl]; lia. Qed.
Lemma Z_to_le_bytes_ms_repl : ltac2:(TCodec.tc2 tcn__MemsetLib "Q1'6'E'>&RCzr1%3221&RE+X0%2241%8241'?'5'SNy8%211%411&Jr3&RGr2&R0%114%4231%7261&D&SM%12=7%33=1:%B3=51p0D1pX@N1pVBQ01").
Proof.
induction k as [|k IH]; intros z Hz; [reflexivity|].
cbn [Z_to_le_bytes ms_repl repeat]. pose proof (ms_repl_nonneg k). f_equal.
- apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap8_mod.
replace (z * (1 + 256 * ms_repl k)) with (z + (z * ms_repl k) * 256) by lia.
rewrite Z.mod_add by lia. reflexivity.
- rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
replace (z * (1 + 256 * ms_repl k)) with (z + (z * ms_repl k) * 256) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l. apply IH. exact Hz.
Qed.
Lemma u_c32 : ltac2:(TCodec.tc2 tcn__MemsetLib "A'SNyR0%211'?'E&T0&QEr1%211%4281&RG&QI%115+`RPX1%4221%<3;61pV2>1").
Proof. intros cv. pose proof (cbz_range cv). unfold c32. apply u_Z2bv; lia. Qed.
Lemma u_c32h : ltac2:(TCodec.tc2 tcn__MemsetLib "F'SNyR0%211'?'E&T0&QFr1%211%4281&RG&QI%115+`RPX1%4221&RJ+2+Q0%3221%9251%A3@;1pV2C1").
Proof. intros cv. pose proof (cbz_range cv). unfold c32h. apply u_Z2bv; lia. Qed.
Lemma u_c64 : ltac2:(TCodec.tc2 tcn__MemsetLib "A'SNyR0%211'?'E&T0&QGr1%211%4281&RG&QI%115+RPXQPTP`RPX1%4221%<3;61pV2>1").
Proof. intros cv. pose proof (cbz_range cv). unfold c64. apply u_Z2bv; lia. Qed.
Lemma wleb4_c32 : ltac2:(TCodec.tc2 tcn__MemsetLib "D'SNyR0%211'?'5y8%611%311&Q3u4&QEr1%211%5241&D&QH%115%33;18%?3;51pV2A1").
Proof.
intros cv. unfold word_to_le_bytes. rewrite u_c32, cbyte_cbz.
change 16843009 with (ms_repl 4). apply Z_to_le_bytes_ms_repl. apply cbz_range.
Qed.
Lemma wleb8_c64 : ltac2:(TCodec.tc2 tcn__MemsetLib "D'SNyR0%211'?'5y8%611%311&Q3u8&QGr1%211%5241&D&QH%115%33;18%?3;51pV2A1").
Proof.
intros cv. unfold word_to_le_bytes. rewrite u_c64, cbyte_cbz.
change 72340172838076673 with (ms_repl 8). apply Z_to_le_bytes_ms_repl. apply cbz_range.
Qed.
Lemma u_slli56 : ltac2:(TCodec.tc2 tcn__MemsetLib "D'SNyR0%211'?'E&T0&R9r1+QH%3221%5291&RG&QI%116&RJ+2%2218%6241%?3>81pV2A1").
Proof.
intros cv. unfold v_slli, cbz. rewrite Z_to_bv_unsigned, Z.shiftl_mul_pow2 by lia.
pose proof (u64_range cv).
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 56 * 256).
rewrite Z.mul_comm, Z.mul_mod_distr_l by lia. lia.
Qed.
Lemma mulhu_c32 : ltac2:(TCodec.tc2 tcn__MemsetLib "G'SNyR0%211'?'E&T0r1%2261+TP`RPX0%63521&R7&R9r3+QH%3221r2%6221&QE%116%@3A31p0;1pVDC1pV2D1").
Proof.
intros cv m Hm. unfold v_mulhu, c32. f_equal. rewrite u_slli56, Hm.
rewrite Z.shiftr_div_pow2 by lia.
replace (cbz cv * 2 ^ 56 * 4311810304) with ((cbz cv * 16843009) * 2 ^ 64) by lia.
apply Z.div_mul. lia.
Qed.
Lemma slli32_c32 : ltac2:(TCodec.tc2 tcn__MemsetLib ">'SNyR0%211'?&R9&QEr1%211+Q0%5221&QF%115%93:31pV2;1").
Proof.
intros cv. unfold v_slli, c32h. f_equal. rewrite u_c32, Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.
Lemma srli32_c32h : ltac2:(TCodec.tc2 tcn__MemsetLib ">'SNyR0%211'?&R:&QFr1%211+Q0%5221&QE%115%93:31pV2;1").
Proof.
intros cv. unfold v_srli, c32. f_equal. rewrite u_c32h, Z.shiftr_div_pow2 by lia.
apply Z.div_mul. lia.
Qed.
Lemma lor_disjoint_shift32 : ltac2:(TCodec.tc2 tcn__MemsetLib "K'E&RCzr2%3221'>&RE&RJ+2+Q0%3221%5281%7281'?&RD&RGr4%2217r3%5221&RA%1243%93F31p0;1p0D1pUNI1pULJ1").
Proof.
intros a b Ha Hb.
assert (Hl : Z.land (a * 2 ^ 32) b = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i 32).
- rewrite <- Z.shiftl_mul_pow2, Z.shiftl_spec by lia. rewrite (Z.testbit_neg_r a) by lia. reflexivity.
- rewrite (Z_testbit_high 32 b) by lia. apply andb_false_r. }
rewrite <- Z.lxor_lor by exact Hl. symmetry. apply Z.add_nocarry_lxor. exact Hl.
Qed.
Lemma or_c64 : ltac2:(TCodec.tc2 tcn__MemsetLib "?'SNyR0%211'?&R8&QFr1%211&QE%113%6231&QG%116%:3;31pV2<1").
Proof.
intros cv. pose proof (cbz_range cv). unfold v_or, c64. f_equal. rewrite u_c32h, u_c32.
rewrite lor_disjoint_shift32 by lia. lia.
Qed.
Lemma mod4_mod_pow2' : ltac2:(TCodec.tc2 tcn__MemsetLib "C'E&RC+2r1%3221'?&RFr3&RJr2%2281%5241+4%7221%8272%:3?21p0<1pVBA1pX4B1").
Proof.
intros t k Hk. apply Z.mod_mod_divide.
exists (2 ^ (k - 2)). change 4 with (2 ^ 2). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.
Lemma negw_and3 : ltac2:(TCodec.tc2 tcn__MemsetLib "G'SNyR0%211'?&R6&R<&SMz%2271r1%5221+3%8221&RF&RI&T0%12?7%311+4%6221%>2C1%B3C91pX>D1").
Proof.
intros x. unfold v_andi, v_subw. f_equal.
change (bv_wrap 64 3) with (Z.ones 2). rewrite Z.land_ones by lia.
rewrite Z_to_bv_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0.
unfold bv_swrap. rewrite bv_wrap64_mod.
change (bv_half_modulus 32) with (2 ^ 31).
unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). change (2 ^ 2) with 4.
rewrite mod4_mod_pow2' by lia.
rewrite <- Zminus_mod_idemp_l.
rewrite mod4_mod_pow2' by lia.
replace (0 - bv_unsigned x + 2 ^ 31) with ((- bv_unsigned x) + 536870912 * 4) by lia.
rewrite Z.mod_add by lia.
rewrite Zminus_mod_idemp_l.
replace (- bv_unsigned x - 2 ^ 31) with ((- bv_unsigned x) + (- 536870912) * 4) by lia.
rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma neg_mod4_range : ltac2:(TCodec.tc2 tcn__MemsetLib "?'E'>&RCz&RF&RIr1%211+4%5221%8271+3%:231%<231pX8>1").
Proof. intros u. pose proof (Z.mod_pos_bound (- u) 4). lia. Qed.
Lemma neg_mod4_aligns : ltac2:(TCodec.tc2 tcn__MemsetLib ">'E'?&RF&RAr1&RI%112+4%6221%6251%8213z%;3<21pX8=1").
Proof.
intros u. rewrite Z.add_mod, Z.mod_mod by lia.
rewrite <- Z.add_mod by lia. replace (u + - u) with 0 by lia. reflexivity.
Qed.
Lemma land_trunc4 : ltac2:(TCodec.tc2 tcn__MemsetLib "J'E'>&RCzr1%3221&RE&RJ+2+R0%3221%5271%;271'?&RBr2&RK+4%2281%5241&RF%1264%6271%:3G41p0<1pULI1").
Proof.
intros a Ha.
replace (2 ^ 64 - 4) with (Z.ldiff (Z.ones 64) (Z.ones 2)).
2:{ rewrite Z.ldiff_land, <- Z.sub_land_same_l, Z.land_ones by lia.
rewrite Z.ones_mod_pow2 by lia. rewrite !Z.ones_equiv. lia. }
rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia.
rewrite Z.mod_small by lia.
rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
pose proof (Z.div_mod a 4 ltac:(lia)). lia.
Qed.
Lemma andi_m4 : ltac2:(TCodec.tc2 tcn__MemsetLib "Q0'E'>&RCzr1%3221&RE&RJ+2+R0%3221%5271%;271'?'SNyR0%211&R6&SMr2%2251-4%5221&RK&RF+4%2271%4281%:2=1%@3=71p0B1pVDO1").
Proof.
intros m Hm. unfold v_andi. f_equal. rewrite u_Z2bv by lia.
change (bv_wrap 64 (-4)) with (2 ^ 64 - 4). apply land_trunc4. exact Hm.
Qed.
Lemma land_4_cases : ltac2:(TCodec.tc2 tcn__MemsetLib "@'E&RCzr1%3221'C'?&RBr2+4%3221%53;19%63<23%8221p0:1pUL?1").
Proof.
intros a Ha.
destruct (Z.testbit a 2) eqn:E; [right|left];
apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec;
change 4 with (2 ^ 2); rewrite Z.pow2_bits_eqb by lia;
destruct (Z.eqb_spec 2 i) as [<-|Hne]; rewrite ?E, ?Z.bits_0; try reflexivity;
apply andb_false_r.
Qed.
Lemma andi_4_cases : ltac2:(TCodec.tc2 tcn__MemsetLib "H'SNyR0%211'@'E'>'?&R6r2+4%3221&SMr1%22<1%83<41'Cz%;3=51%<3>69%4221%?261qWFA1%C2B1pX>E1").
Proof.
intros x. exists (Z.land (bv_unsigned x) 4). split.
- unfold v_andi. f_equal.
- apply land_4_cases. apply u64_range.
Qed.
Lemma ms_v_add_Z : ltac2:(TCodec.tc2 tcn__MemsetLib "M'SNyR0%211'E'>&RCzr1%3221&RE&RJ+2+R0%3221%5271%;271'?&R4r3&SMr2%22D1%5241&QC%1264%93G31p0;1pX@H1pX>J1").
Proof. intros x z Hz. unfold v_add, at_. rewrite u_Z2bv by lia. reflexivity. Qed.
Lemma ms_v_add_at_Z : ltac2:(TCodec.tc2 tcn__MemsetLib "Q2'SNyR0%211'E'>&RCzr1%3221&RE&RJ+2+R0%3221%5271%;271'?&R4&QCr4r3%3221&SMr2%22G1%8241&RA%1274%:291%=3K41p0?1pX@L1pVLM1pX>O1").
Proof. intros x o z Hz. rewrite ms_v_add_Z by lia. apply at_at. Qed.
Lemma ms_v_sub_ZZ : ltac2:(TCodec.tc2 tcn__MemsetLib "Q2'E'>&RCzr1%3221r2%5231%7231&REr3&RJ+2+R0%3221%6251'?'SNyR0%211&R;&SMr4%2251%326>%5221&RK%125A%72:1%=3:41p0?1p0G1pUNQ01pULQ11").
Proof. intros a b H1 H2. unfold v_sub. rewrite !u_Z2bv by lia. reflexivity. Qed.
Lemma ms_v_addi_Z : ltac2:(TCodec.tc2 tcn__MemsetLib "M'E'>&RCzr2%3221&RE&RJ+2+R0%3221%5271%;271'?'SNyR0%211&R5&SMr3%2251%421A&RA%124C%6291%<3941p0>1pV:K1pULL1").
Proof. intros a i Ha. unfold v_addi. rewrite u_Z2bv by lia. reflexivity. Qed.
Lemma ms_step_subw_at : ltac2:(TCodec.tc2 tcn__MemsetLib "S4'5'K%211&QAy5'SNyR0%211%5241'8y8%611%311p061yQ0%:11%;1<'?%913&Mr:r8%3221(0r5%22:1%93841'2&Nr6%211(4%?3521';'Q?'E%3221%L11&Q4r7%211(:(Q:(Q6r4%342@E1+4%64=<21%I2<1%Q03<91&Q@(SLz(=%33QB21%53QC@1%Q73M1I&R<&R1r=%221E%322Q0%5221%Q>3QH1Q7'O'Q0%211&Q1r?&R2vS3r>r<r;%5543?21%8271(L&R3r9%2381QB&R5%12FQ3%=5<31:9%72B1%R33B91p0F1p0N1p0Q61p0QH1p0QO1pX:RC1pWDR;1pWBR<1pW:R=1pX<R?1pW@RB1pVFRC1pW0RJ1pW<RJ1pWHS11").
Proof.
intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
rewrite (step_subw segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.
Lemma ms_step_mulhu_at : ltac2:(TCodec.tc2 tcn__MemsetLib "S4'5'K%211&QAy5'SNyR0%211%5241'8y8%611%311p061yQ0%:11%;1<'?%913&Mr:r8%3221(0r5%22:1%93841'2&Nr6%211(4%?3521';'Q?'E%3221%L11&Q4r7%211(:(Q8(Q7r4%342@E1+4%64=<21%I2<1%Q03<91&Q@(SLz(=%33QB21%53QC@1%Q73M1I&R7&R1r=%221E%322Q0%5221%Q>3QH1Q7'O'Q0%211&Q1r?&R2vS3r>r<r;%5543?21%8271(L&R3r9%2381QB&R5%12FQ3%=5<31:9%72B1%R33B91p0F1p0N1p0Q61p0QH1p0QO1pX:RC1pWDR;1pWBR<1pW:R=1pX<R?1pW@RB1pVFRC1pW0RJ1pW<RJ1pWHS11").
Proof.
intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
rewrite (step_mulhu segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.
Lemma ms_step_or_at : ltac2:(TCodec.tc2 tcn__MemsetLib "S4'5'K%211&QAy5'SNyR0%211%5241'8y8%611%311p061yQ0%:11%;1<'?%913&Mr:r8%3221(0r5%22:1%93841'2&Nr6%211(4%?3521';'Q?'E%3221%L11&Q4r7%211(:(Q9(Q5r4%342@E1+4%64=<21%I2<1%Q03<91&Q@(SLz(=%33QB21%53QC@1%Q73M1I&R8&R1r=%221E%322Q0%5221%Q>3QH1Q7'O'Q0%211&Q1r?&R2vS3r>r<r;%5543?21%8271(L&R3r9%2381QB&R5%12FQ3%=5<31:9%72B1%R33B91p0F1p0N1p0Q61p0QH1p0QO1pX:RC1pWDR;1pWBR<1pW:R=1pX<R?1pW@RB1pVFRC1pW0RJ1pW<RJ1pWHS11").
Proof.
intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
rewrite (step_or segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.
Section Stores.
Variable segs : list Segment.
Variable mem0 : word -> option byte.
Variable d : word.
Variable n : Z.
Variable cv : word.
Hypothesis Hn : 0 <= n.
Hypothesis Hnw : bv_unsigned d + n < 2 ^ 64.
Hypothesis Hok : store_ok segs mem0 d (Z.to_nat n) = true.
#[local] Abbreviation CF := (cfill mem0 d n (cbyte cv)).
Lemma cf_sb : ltac2:(TCodec.tc2 tcn__MemsetLib "SI&QAy5'SNyR0%211%5241'8y8%611%311p061yQ0%:11%;1<y<%=11'5';'E%2211%411'?%@1:&MvSKr9%3221(0r7%22A1%93841'2&Nr8%211(4%?3521'Q?%E21D%Q111&Q4%11@(:(Q>(Q;r6%342=B1+4%64;N21%F2;1%M3;91&R1r=%221L&QCvS1r5%3221%Q53QF51&RA&SO%12Q?L%32A1%Q:3Q=17r?r:%?221vS0%Q?3R021&RCz%221Q;+1%>2Q81vS<%6221'O'Q0%211&Q1&R2vS3rBrA&QJvS;&QH%11Dr;%554Q2?21r@%;5:9821%=2R41(L&R5%12<Q@(3%QG4R?R?R8I%23R?1:%?5>Q<I<1%D5CB51:%82H1%RA3H:1p0L1p0Q11p0Q51p0Q;1p0QA1p0QJ1p0R91p0R@1pVLRM1pVNRN1pQ>RM1pV<S31pWDS61pWBS71pX<S91pW@S<1pW0SC1pW<SC1").
Proof.
intros regs pc rom w rs1 rs2 imm L o0 o Hf He Hdc Hrs1 Ho Hrs2 H0 H1.
replace ((o, 1) :: L) with ((o, Z.of_nat 1) :: L) by reflexivity.
rewrite <- (cfill_store mem0 d n (cbyte cv) Hnw L o 1) by lia.
eapply step_sb_at; [exact Hf | exact He | exact Hdc | | exact Hrs2 | reflexivity |].
- rewrite Hrs1, at_addi, Ho. reflexivity.
- apply (cfill_store_ok mem0 d n (cbyte cv) Hnw segs); assumption || lia.
Qed.
Lemma cf_sw : ltac2:(TCodec.tc2 tcn__MemsetLib "T1&QAy5'SNyR0%211%5241'8y8%611%311p061yQ0%:11%;1<y<%=11'5';'E%2211%411'?%@1:&MvSKr:%3221(0r8%22A1%93841'2&Nr9%211(4%?3521'Q?%E21D%Q111&Q4%11@(:(Q>(Q<r7%342=B1+4%64;N21%F2;1%M3;91&R1r>%221L&QCvS1r6%3221%Q53QF51&RA&SO%12Q?L%32A1%Q:3Q=17r@r;%?221%Q>3QO1;%QD1QL&Q3u4%221J&D&QHvS0%211%43R416%QH3961&RCz%221Q?%F2QHQ2vS<%5221'O'Q0%211&Q1&R2vS3rDrC&QJvS;r=%352Q8=D1rB%9587621%;2R:1(L&R5%12:QF(3%QM4REREQ6QH%23RE1:%=5<QBGN1%B5A@51:%82F1%RG3F:1p0J1p0N1p0Q21p0Q=1p0QB1p0QH1p0R11p0R@1p0RG1pX:SB1pVLS51pVNS61pQ>S51pV<S;1pWDS>1pWBS?1pX<SA1pW@SD1pW0SK1pW<SK1").
Proof.
intros regs pc rom w rs1 rs2 imm L o0 o v Hf He Hdc Hrs1 Ho Hrs2 Hv H0 H1.
replace ((o, 4) :: L) with ((o, Z.of_nat 4) :: L) by reflexivity.
rewrite <- (cfill_store mem0 d n (cbyte cv) Hnw L o 4) by lia.
rewrite <- Hv.
eapply step_sw_at; [exact Hf | exact He | exact Hdc | | exact Hrs2 |].
- rewrite Hrs1, at_addi, Ho. reflexivity.
- apply (cfill_store_ok mem0 d n (cbyte cv) Hnw segs); assumption || lia.
Qed.
Lemma cf_sd : ltac2:(TCodec.tc2 tcn__MemsetLib "T2&QAy5'SNyR0%211%5241'8y8%611%311p061yQ0%:11%;1<y<%=11'5';'E%2211%411'?%@1:&MvSKr:%3221(0r8%22A1%93841'2&Nr9%211(4%?3521'Q?%E21D%Q111&Q4%11@(:(Q>(Q=r7%342=B1+4%64;N21%F2;1%M3;91&R1r>%221L&QCvS1r6%3221%Q53QF51&RA&SO%12Q?L%32A1%Q:3Q=17r@r;%?221%Q>3QO1;%QD1QL&Q3u8%221J&D&QHvS0%211%43R416%QH3961&RCz%221Q?+8%G2QI1vS<%6221'O'Q0%211&Q1&R2vS3rDrC&QJvS;r=%352Q9=E1rB%9587621%;2R;1(L&R5%12:QG(3%QN4RFRFQ7G%23RF1:%=5<QCGO1%B5A@51:%82F1%RH3F:1p0J1p0O1p0Q31p0Q>1p0QC1p0QI1p0R21p0RA1p0RH1pX:SC1pVLS61pVNS71pQ>S61pV<S<1pWDS?1pWBS@1pX<SB1pW@SE1pW0SL1pW<SL1").
Proof.
intros regs pc rom w rs1 rs2 imm L o0 o v Hf He Hdc Hrs1 Ho Hrs2 Hv H0 H1.
replace ((o, 8) :: L) with ((o, Z.of_nat 8) :: L) by reflexivity.
rewrite <- (cfill_store mem0 d n (cbyte cv) Hnw L o 8) by lia.
rewrite <- Hv.
eapply step_sd_at; [exact Hf | exact He | exact Hdc | | exact Hrs2 |].
- rewrite Hrs1, at_addi, Ho. reflexivity.
- apply (cfill_store_ok mem0 d n (cbyte cv) Hnw segs); assumption || lia.
Qed.
End Stores.
Definition ms_clob : list reg := [11; 12; 13; 14; 15; 16]%bv.
Definition ms_agree (regs regs' : bvmap 5 word) : Prop :=
regs_agree (fun r => In r ms_clob) regs regs'.
Lemma ms_agree_refl : ltac2:(TCodec.tc2 tcn__MemsetLib ":&QAy5'SNyR0%211%5241&QKr1%2211pW<41").
Proof. intros regs. apply regs_agree_refl. Qed.
Lemma ms_agree_trans : ltac2:(TCodec.tc2 tcn__MemsetLib "A&QAy5'SNyR0%211%5241&QKr3r2%3221r5%5214p031p041pW891pW6:1pW4;1").
Proof. intros r1 r2 r3. apply regs_agree_trans. Qed.
Lemma ms_agree_upd : ltac2:(TCodec.tc2 tcn__MemsetLib "I&QAy5'SNyR0%211%5241%415&QKr4r3%3221&R?&QM%23741r6&R3r5%23198%;241p061p0:1pX:A1pW:@1pW>B1pW<C1").
Proof. intros regs regs' rd v H Hin. apply regs_agree_upd; assumption. Qed.
Lemma ms_agree_getr : ltac2:(TCodec.tc2 tcn__MemsetLib "L&QAy5'SNyR0%211%5241%415&QKr3r2%3221&B&R?&QM%23851%411'?&R1r4%221;r5%421=%63B31p081p0>1pW2C1pW>E1pW<F1").
Proof. intros regs regs' r H Hn. apply H. exact Hn. Qed.
Lemma ms_agree_keeps : ltac2:(TCodec.tc2 tcn__MemsetLib "@&QAy5'SNyR0%211%5241&QKr2r1%3221&R=r3%2215p041pW>91pW<:1").
Proof.
intros regs regs' H r Hr. apply H. unfold callee_kept in Hr. unfold ms_clob. cbn [In] in *.
intros Hc. decompose [or] Hr; subst; decompose [or] Hc; try discriminate; auto.
Qed.
End FPX_1.
Ltac in_clob := cbn [ms_clob In]; repeat first [ left; reflexivity | right ].
Ltac solve_ms_agree :=
repeat (apply ms_agree_upd; [| in_clob]); first [apply ms_agree_refl | assumption].
