(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MemSplit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__ArtMem () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem.WithSegs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "2and"; "2eq"; "2not"; "3Z"; "4bytes_le_to_Z"; "5word_to_le_bytes"; "0M"; "0M'"; "6Wf"]; ["6Wn"; "6apart"; "6cell"; "6wok"; "6wr"; "7c_eq"; "7c_ltu"; "7rdn"; "7v_add"; "7v_addi"; "7v_and"; "7v_andi"; "7v_lb"; "7v_lh"; "7v_lw"; "7v_mul"]; ["7v_slli"; "7v_srli"; "7v_sub"; "7v_xori"; "8mem_grows"; "9add"; "9div"; "9eqb"; "9land"; "9le"; "9lt"; "9ltb"; "9modulo"; "9mul"; "9of_nat"; "9pow"]; ["9sub"; "0a"; "0a'"; "0b"; "0b'"; "0c"; "0i"; "0k"; "0k'"; "0m"; "0n"; "0n'"; "0segs"; ":Z_to_bv"; ":bv"; ":bv_unsigned"]; ["0u"; "0v"; "0v'"; "0x"; "0y"; "0z"]]).
Lemma art_u_lit : ltac2:(TCodec.tc2 tcn__ArtMem "G':'7&Q9zr1%3221&Q:&Q?+2+R0%3221%5271%;271'8&QOyR0&QMr2%2231%5241%73D13p091pS4F1").
Proof. intros a H. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2^64). lia. Qed.
Lemma art_zb_eq : ltac2:(TCodec.tc2 tcn__ArtMem "G':'8&Q<r2&Q?+2+R0%3221%6251r1%8213%:3;31'QNyR0%211&QMr3%2241%325?%B3521p091pT:E1pT8F1").
Proof. intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). exact H. Qed.
Lemma art_zb_addi : ltac2:(TCodec.tc2 tcn__ArtMem "A':'8'QNyR0%211&I&QMr2%2251r1%5221&Q5%1253%72:1%=3:41pS@?1pT8@1").
Proof.
intros x k. unfold v_addi. rewrite Z_to_bv_unsigned. apply art_zb_eq. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma art_zb_add : ltac2:(TCodec.tc2 tcn__ArtMem "B':'8'QNyR0%211&H&QMr2%2251r1%4271%6231&Q5%1264%82;1%>3;41pT:@1pT8A1").
Proof.
intros x y. unfold v_add. rewrite !Z_to_bv_unsigned. apply art_zb_eq. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite <- Zplus_mod. reflexivity.
Qed.
Lemma art_zb_sub : ltac2:(TCodec.tc2 tcn__ArtMem "B':'8'QNyR0%211&Q2&QMr2%2251r1%4271%6231&Q@%1264%82;1%>3;41pT:@1pT8A1").
Proof.
intros x y. unfold v_sub. rewrite !Z_to_bv_unsigned. apply art_zb_eq. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite <- Zminus_mod. reflexivity.
Qed.
Lemma art_zb_mul : ltac2:(TCodec.tc2 tcn__ArtMem "B':'8'QNyR0%211&O&QMr2%2251r1%4271%6231&Q=%1264%82;1%>3;41pT:@1pT8A1").
Proof.
intros x y. unfold v_mul. rewrite !Z_to_bv_unsigned. apply art_zb_eq. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite <- Zmult_mod. reflexivity.
Qed.
Lemma art_zb_slli : ltac2:(TCodec.tc2 tcn__ArtMem "I':&Q9zr1%3221'8'QNyR0%211&Q0&QMr3%2251r2%5221&Q=&Q?+2%2215%4281%:2=1%@3=71p0B1pS@G1pT8H1").
Proof.
intros x k Hk. unfold v_slli. rewrite Z_to_bv_unsigned, Z.shiftl_mul_pow2 by lia. apply art_zb_eq. unfold bv_wrap.
change (bv_modulus 64) with (2^64). rewrite Zmult_mod_idemp_l. reflexivity.
Qed.
Lemma art_zb_srli : ltac2:(TCodec.tc2 tcn__ArtMem "Q0':'7&Q9zr2%3221&Q:&Q?+2+R0%3221%5271%;271'8'QNyR0%211&Q1&QMr4%2251r3%5221&Q6%A2@3%2261%82;1%>3;51p0G1p0A1pS@N1pT8O1").
Proof. intros x k Hx Hk. unfold v_srli. rewrite art_u_lit by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma art_zb_srli_exact : ltac2:(TCodec.tc2 tcn__ArtMem "Q:':&Q9zr2%3221'8r5&Q=r3&Q?+2r4%3221%6251%93>81&Q:+R0%8271%3271r6%;2:1%>2?1%7215'QNyR0%211&Q1&QMr8%2251r7%5221%528=%L3821p0<1p0A1p0F1p0Q11p0Q21pT:Q71pS@Q81pT8Q91").
Proof.
intros x k y Hk Hy Hx Hy' Hyk. subst x. rewrite art_zb_srli by lia. f_equal. apply Z.div_mul. pose proof (Z.pow_pos_nonneg 2 k). lia.
Qed.
Lemma art_zb_and : ltac2:(TCodec.tc2 tcn__ArtMem "Q0':'7&Q9zr2%3221&Q:&Q?+2+R0%3221%5271%;271'8'QNyR0%211&J&QMr4%2251r3%4271%6231&Q8%1264%82;1%>3;41p0@1p0A1pT:N1pT8O1").
Proof. intros x y Hx Hy. unfold v_and. rewrite !art_u_lit by lia. reflexivity. Qed.
Lemma art_zb_andi : ltac2:(TCodec.tc2 tcn__ArtMem "O':'7&Q9zr2%3221&Q:&Q?+2+R0%3221%5271%;271'8'QNyR0%211&K&QMr4%2251r3%5221&Q8%1253%72:1%=3:41p0?1p0@1pS@M1pT8N1").
Proof. intros x k Hx Hk. unfold v_andi. rewrite art_u_lit by lia. rewrite bv_wrap_small by (change (bv_modulus 64) with (2^64); lia). reflexivity. Qed.
Lemma art_v_lw_small : ltac2:(TCodec.tc2 tcn__ArtMem "I':'7&Q9zr1%3221&Q:&Q?+2+O%3221%5271%;271'8'QNyR0%211&N&QMr2%2251%411%93612p0;1pT<H1").
Proof.
intros z Hz. unfold v_lw. rewrite art_u_lit by lia. f_equal. unfold bv_swrap, bv_wrap.
change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32). rewrite Z.mod_small by lia. lia.
Qed.
Lemma art_v_lh_small : ltac2:(TCodec.tc2 tcn__ArtMem "I':'7&Q9zr1%3221&Q:&Q?+2+?%3221%5271%;271'8'QNyR0%211&M&QMr2%2251%411%93612p0;1pT<H1").
Proof.
intros z Hz. unfold v_lh. rewrite art_u_lit by lia. f_equal. unfold bv_swrap, bv_wrap.
change (bv_half_modulus 16) with (2^15). change (bv_modulus 16) with (2^16). rewrite Z.mod_small by lia. lia.
Qed.
Lemma art_bytes2 : ltac2:(TCodec.tc2 tcn__ArtMem "L':'7&Q9zr1%3221&Q:&Q?+2+@%3221%5271%;271'8&;&<u2&QMyR0r2%3221%6251%811&QO%1264%<3I31p0>1pT<K1").
Proof.
intros z Hz. rewrite bytes_le_N. change (2 ^ (8 * Z.of_nat 2)) with (2^16). rewrite art_u_lit by lia. apply Z.mod_small. lia.
Qed.
Lemma art_land_m8 : ltac2:(TCodec.tc2 tcn__ArtMem "J':'7&Q9zr1%3221&Q:&Q?+2+R0%3221%5271%;271'8&Q8r2+_oooooooooooH%3221&Q=&Q6+8%2261%4212%:3G61p0<1pT8I1").
Proof.
intros x Hx. change 18446744073709551608 with (Z.shiftl (Z.ones 61) 3).
change 8 with (2 ^ 3). rewrite <- Z.shiftr_div_pow2, <- Z.shiftl_mul_pow2 by lia.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
destruct (Z.lt_ge_cases i 3) as [L|G].
- rewrite !Z.shiftl_spec_low by lia. apply Bool.andb_false_r.
- rewrite !Z.shiftl_spec_high by lia. rewrite Z.shiftr_spec by lia. rewrite Z.testbit_ones by lia.
replace (i - 3 + 3) with i by lia.
destruct (Z.lt_ge_cases i 64) as [L2|G2].
+ replace ((0 <=? i - 3) && (i - 3 <? 61))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
apply Bool.andb_true_r.
+ assert (Tf : Z.testbit x i = false).
{ destruct (Z.eq_dec x 0) as [->|NZ]. apply Z.testbit_0_l. apply Z.bits_above_log2; [lia|].
apply Z.lt_le_trans with (m := 64); [|lia]. apply Z.log2_lt_pow2; lia. }
rewrite Tf. reflexivity.
Qed.
Lemma art_v_lb_small : ltac2:(TCodec.tc2 tcn__ArtMem "H':'7&Q9zr1%3221&Q:+T0%2241%8241'8'QNyR0%211&L&QMy8r2%3221%511%5283%;3821p0=1pT<G1").
Proof.
intros z Hz. unfold v_lb. f_equal. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap.
change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. lia.
Qed.
Lemma art_bytes1 : ltac2:(TCodec.tc2 tcn__ArtMem "Q2':'7&Q9zr1%3221&Q:&Q?+2+R0%3221%5271%;271'8'3'QNy8%211%411&<u1&QMyR0r2%3221%6251(2%62;4(5%11<%43=31%B3=61p0D1pT<Q11").
Proof.
intros z Hz. unfold word_to_le_bytes. cbn. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. change (bv_modulus 64) with (2^64). rewrite (Z.mod_small z (2^64)) by lia. reflexivity.
Qed.
Lemma art_u8_lit : ltac2:(TCodec.tc2 tcn__ArtMem "D':'7&Q9zr1%3221&Q:+X0%2241%8241'8&QOy8&QMr2%2231%5241%73A13p091pT<C1").
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia. Qed.
Lemma art_bytes4 : ltac2:(TCodec.tc2 tcn__ArtMem "L':'7&Q9zr1%3221&Q:&Q?+2+Q0%3221%5271%;271'8&;&<u4&QMyR0r2%3221%6251%811&QO%1264%<3I31p0>1pT<K1").
Proof.
intros z Hz. rewrite bytes_le_N. change (2 ^ (8 * Z.of_nat 4)) with (2^32). rewrite art_u_lit by lia. apply Z.mod_small. lia.
Qed.
Lemma art_land_full_l : ltac2:(TCodec.tc2 tcn__ArtMem "E':'7&Q9zr1%3221&Q:&Q?+2+R0%3221%5271%;271'8&Q8+_oooooooooooOr2%3221%53B12p071pT8D1").
Proof. intros x Hx. rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma art_land_full_r : ltac2:(TCodec.tc2 tcn__ArtMem "E':'7&Q9zr1%3221&Q:&Q?+2+R0%3221%5271%;271'8&Q8r2+_oooooooooooO%3221%53B13p071pT8D1").
Proof. intros x Hx. rewrite Z.land_comm. apply art_land_full_l. exact Hx. Qed.
Lemma art_c_eq_zb : ltac2:(TCodec.tc2 tcn__ArtMem "N':'7&Q9zr2%3221&Q:&Q?+2+R0%3221%5271%;271'8'1&E&QMyR0r4%3221r3%5241%7231&Q7%1264%<3;31p0>1p0?1pT:L1pT8M1").
Proof. intros x y Hx Hy. unfold c_eq, bv_eqb. rewrite !art_u_lit by lia. reflexivity. Qed.
Lemma art_c_ltu_zb : ltac2:(TCodec.tc2 tcn__ArtMem "N':'7&Q9zr2%3221&Q:&Q?+2+R0%3221%5271%;271'8'1&F&QMyR0r4%3221r3%5241%7231&Q;%1264%<3;31p0>1p0?1pT:L1pT8M1").
Proof. intros x y Hx Hy. unfold c_ltu, bv_ltu. rewrite !art_u_lit by lia. reflexivity. Qed.
Lemma art_zb_xori_m1 : ltac2:(TCodec.tc2 tcn__ArtMem "O':'7&Q9zr1%3221&Q:&Q?+2+R0%3221%5271%;271'8'QNyR0%211&Q3&QMr2%2251-1%5221&Q@+1%22?1%3217%92<1%?3<61p0A1pT8N1").
Proof.
intros x Hx. unfold v_xori. rewrite art_u_lit by lia. change (bv_wrap 64 (-1)) with (Z.ones 64). f_equal.
rewrite <- Z.ldiff_ones_l_low; [| lia |].
- rewrite Z.ldiff_land. rewrite <- Z.sub_land_same_l. rewrite Z.land_comm, Z.land_ones, Z.mod_small by lia. rewrite Z.ones_equiv. lia.
- destruct (Z.eq_dec x 0) as [->|Hz]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma art_zb_sltiu : forall x k, 0 <= x < 2 ^ 64 -> 0 <= k < 2 ^ 64 ->
v_sltiu (Z_to_bv 64 x) k = Z_to_bv 64 (if x <? k then 1 else 0).
Proof.
intros x k Hx Hk. unfold v_sltiu. rewrite art_u_lit by lia. rewrite bv_wrap_small by (change (bv_modulus 64) with (2^64); lia).
destruct (x <? k); reflexivity.
Qed.
Lemma art_zb_sltu : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
v_sltu (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (if x <? y then 1 else 0).
Proof. intros x y Hx Hy. unfold v_sltu. rewrite art_c_ltu_zb by lia. destruct (x <? y); reflexivity. Qed.
Section WithSegs.
Variable segs : list Segment.
Definition cell (M : word -> option byte) (a : Z) (n : nat) (v : Z) : Prop :=
rdn segs M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).
Definition Wn (n : nat) (M : word -> option byte) (a : Z) (v : Z) : word -> option byte :=
wbytes M (Z_to_bv 64 a) (word_to_le_bytes n (Z_to_bv 64 v)).
Definition wok (M : word -> option byte) (a : Z) (n : nat) : Prop := store_ok segs M (Z_to_bv 64 a) n = true.
Definition apart (a n b m : Z) : Prop := a + n <= b \/ b + m <= a.
Lemma apart_sym : ltac2:(TCodec.tc2 tcn__ArtMem ">':&Ar4r3r2r1%544321r5%745416p031pSD:1pS8;1pSF<1pS4=1").
Proof. unfold apart. lia. Qed.
Lemma rdn_Wn_other : ltac2:(TCodec.tc2 tcn__ArtMem "QN'4'QNyR0%211'6y8%511%311p051':&Q9zr4%3221&Q:&Q5r5&Q>r7%211%5241&Q?+2+R0%3221%;251%91>%<2;1%>214&Ar8r:%?11r6%A1B%645321'8'3%11Q0%Q311&GvQL&@r;r9%342>1?&QM%12Q=M%84731?%948B2@%>3;21p0@1p0H1p0Q81p0M1p0Q:1pSDQH1pS8Q@1pT4QA1pS4QB1pLQD1pSFQM1").
Proof.
intros n M a v b m Ha Han Hb Hbm Hap. unfold Wn.
apply rdn_wbytes_out; rewrite ?length_N_to_le_bytes; rewrite ?(art_u_lit a) by lia; rewrite ?(art_u_lit b) by lia; unfold apart in Hap; lia.
Qed.
Lemma cell_Wn_other : ltac2:(TCodec.tc2 tcn__ArtMem "QI'4'QNyR0%211'6y8%511%311p051':&Q9zr5%3221&Q:&Q5r6&Q>r8%211%5241&Q?+2+R0%3221%;251%91>%<2;1%>214&Ar9r;%?11r7%A1B%645321&B%146C4E&@r=r<r:%4432;1%741=I:p071p0:1p0B1p0Q21p0G1p0Q41pT2Q91pSDQC1pS8Q;1pT4Q<1pS4Q=1pLQ?1pSFQH1").
Proof. intros n M a v b m u Ha Han Hb Hbm Hap H. unfold cell. rewrite rdn_Wn_other by assumption. exact H. Qed.
Lemma cell_Wn_hit : ltac2:(TCodec.tc2 tcn__ArtMem "Q6'4'QNyR0%211'6y8%511%311p051':&Q9zr2%3221&Q:&Q5r3&Q>r5%211%5241&Q?+2+R0%3221%;251&B&@r6r4%342<1>%54123?p071p0D1pT4I1pS4J1pLL1pSFQ51").
Proof.
intros n M a v Ha Han. unfold cell, Wn.
pose proof (rdn_wbytes_hit segs (word_to_le_bytes n (Z_to_bv 64 v)) M (Z_to_bv 64 a)) as H.
rewrite length_N_to_le_bytes in H. apply H. rewrite art_u_lit by lia. lia.
Qed.
Lemma Wn_grows : ltac2:(TCodec.tc2 tcn__ArtMem "F'4'QNyR0%211'6y8%511%311p051':&Q4r3&@r4r2r1%443521%7261pT491pS4:1pL<1pSFE1").
Proof. intros. unfold Wn. apply wbytes_grows. Qed.
Lemma wok_Wn : ltac2:(TCodec.tc2 tcn__ArtMem "M'4'QNyR0%211'6y8%511%311p051':&Cr5r2r1%43321&@r7r6r4%443281r3%;3219p081pSDG1pS8?1pT4@1pS4A1pLC1pSFL1").
Proof. intros n M a v b m H. unfold wok. eapply store_ok_mono; [apply Wn_grows | exact H]. Qed.
Lemma wok_grows : ltac2:(TCodec.tc2 tcn__ArtMem "I'QNyR0%211'6y8%511%311p051':'4&Q4r4r3%3221&Cr5r2%33251%43376p021p071pSD<1pS8>1pN@1pLA1").
Proof. intros M M' b m G H. unfold wok. eapply store_ok_mono; [exact G | exact H]. Qed.
Definition wr (M : word -> option byte) (a n : Z) : Prop :=
forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok segs M (Z_to_bv 64 (a + d)) k = true.
Lemma wr_wok : ltac2:(TCodec.tc2 tcn__ArtMem "Q5'QNyR0%211'6y8%511%311p051':&Dr3r2r1%43321'4&Q9r5%2216&Q5&Q>%119%32;1r6%5217%9231&Cr8r4%3321Bp051p0=1pS@A1pS8H1p0D1pSFJ1pS4K1pLM1").
Proof. intros M a n W b k H1 H2. unfold wok. replace b with (a + (b - a)) by lia. apply W; lia. Qed.
Lemma wr_grows : ltac2:(TCodec.tc2 tcn__ArtMem "H'QNyR0%211'6y8%511%311p051':&Q4r4r3%3221&Dr5r2%33251%43376p021p071pSF<1pS4=1pN?1pL@1").
Proof. intros M M' a n G W d k Hd Hk. eapply store_ok_mono; [exact G | apply W; assumption]. Qed.
Lemma wr_Wn : ltac2:(TCodec.tc2 tcn__ArtMem "M'4'QNyR0%211'6y8%511%311p051':&Dr5r2r1%43321&@r7r6r4%443281r3%;3219p081pSD>1pS8?1pT4@1pS4A1pLC1pSFL1").
Proof. intros. eapply wr_grows; [apply Wn_grows | assumption]. Qed.
Lemma wr_sub : ltac2:(TCodec.tc2 tcn__ArtMem "O'QNyR0%211'6y8%511%311p051':&Dr5r4r3%43321&Q9%1253&Q5%1265r6%3219%6231r8%=31<;p031p091p0<1pSHB1pS6C1pSFD1pS4E1pLG1").
Proof. intros M a n a' n' W H1 H2 d k Hd Hk. replace (a' + d) with (a + (a' - a + d)) by lia. apply W; lia. Qed.
Lemma Wn_outside : ltac2:(TCodec.tc2 tcn__ArtMem "QD'4'QNyR0%211'6y8%511%311p051':&Q9zr3%3221&Q:&Q5r4&Q>r6%211%5241&Q?+2+R0%3221%;251&9'7r5&QO%12LB%E231r7%@11%C261%E251%9251%;11'8&@r8%2519G=I%:1J%53Q421p071p0D1p0Q11pT8Q<1pT4Q71pS4Q81pLQ:1pSFQC1").
Proof.
intros n M a v x Ha Han Hx. unfold Wn.
destruct (Z_lt_le_dec (bv_unsigned x) a) as [L|G].
- apply wbytes_below; rewrite ?length_N_to_le_bytes, art_u_lit by lia; lia.
- apply wbytes_above. rewrite length_N_to_le_bytes, art_u_lit by lia. lia.
Qed.
Definition Wf (M : word -> option byte) (a : Z) (k : nat) (b : Z) : word -> option byte :=
wbytes M (Z_to_bv 64 a) (repeat (Z_to_bv 8 b) k).
Lemma Wf_grows : ltac2:(TCodec.tc2 tcn__ArtMem "F'QNyR0%211'6y8%511%311p051':'4&Q4r4&?r3r2r1%445321%7261pS8:1pS@:1pS4<1pL>1").
Proof. intros. unfold Wf. apply wbytes_grows. Qed.
Lemma wok_Wf : ltac2:(TCodec.tc2 tcn__ArtMem "M'QNyR0%211'6y8%511%311p051':'4&Cr6r2r1%43321&?r7r5r4%443821r3%;3219p081pSD>1pS<@1pS8A1pS@A1pS4C1pLE1").
Proof. intros. eapply wok_grows; [apply Wf_grows | assumption]. Qed.
Lemma wr_Wf : ltac2:(TCodec.tc2 tcn__ArtMem "M'QNyR0%211'6y8%511%311p051':'4&Dr6r2r1%43321&?r7r5r4%443821r3%;3219p081pSD?1pS<@1pS8A1pS@A1pS4C1pLE1").
Proof. intros. eapply wr_grows; [apply Wf_grows | assumption]. Qed.
Lemma rdn_Wf_other : ltac2:(TCodec.tc2 tcn__ArtMem "QN'QNyR0%211'6y8%511%311p051':'4&Q9zr5%3221&Q:&Q5r6&Q>%116%4231&Q?+2+R0%3221%:251r4%@2?1%:12%=2@1%?216&Ar9r8%@11%4431B@'8'3%11Q0%Q311&GvQL&?r;r:%3421=<&QMr7%22Q>1%94841Q0%:4972Q1%?3<21p0A1p0G1p0K1p0N1p0Q:1pSDQ?1pS<QA1pS8QB1pS@QB1pS4QD1pLQF1").
Proof.
intros M a k b c m Ha Hk Hc Hm Hap. unfold Wf.
apply rdn_wbytes_out; rewrite ?repeat_length; rewrite ?(art_u_lit a) by lia; rewrite ?(art_u_lit c) by lia; unfold apart in Hap; lia.
Qed.
Lemma cell_Wf_other : ltac2:(TCodec.tc2 tcn__ArtMem "QI'QNyR0%211'6y8%511%311p051':'4&Q9zr6%3221&Q:&Q5r7&Q>%116%4231&Q?+2+R0%3221%:251r5%@2?1%:12%=2@1%?216&Ar:r9%@11%4431B@&Br<r8%3421FJ&?r=r;%34261;%841;6Kp061p0;1p0A1p0E1p0H1p0Q41pT2Q:1pSDQ:1pS<Q<1pS8Q=1pS@Q=1pS4Q?1pLQA1").
Proof. intros M a k b c m u Ha Hk Hc Hm Hap H. unfold cell. rewrite rdn_Wf_other by assumption. exact H. Qed.
Lemma Wf_outside : ltac2:(TCodec.tc2 tcn__ArtMem "QD'QNyR0%211'6y8%511%311p051':'4&Q9zr4%3221&Q:&Q5r5&Q>%116%4231&Q?+2+R0%3221%:251&9'7r6&QOr3%22M1%E241%?1@%B261%D241%9241%;11'8&?r8r7%3521>IM%31N%63Q521p081p0E1p0Q11pT8Q=1pS8Q81pS@Q81pS4Q:1pLQ<1").
Proof.
intros M a k b x Ha Hk Hx. unfold Wf.
destruct (Z_lt_le_dec (bv_unsigned x) a) as [L|G].
- apply wbytes_below; rewrite ?repeat_length, art_u_lit by lia; lia.
- apply wbytes_above. rewrite repeat_length, art_u_lit by lia. lia.
Qed.
Lemma Wf_inside : ltac2:(TCodec.tc2 tcn__ArtMem "QD'QNyR0%211'6y8%511%311p051':'4&Q9zr4%3221&Q:&Q5r5&Q>%116%4231&Q?+2+R0%3221%:251'7r3%A2@1%;1<%?231%5231'8&?r8r7r6&QM%F23I%22Q51%75654G1(0%52Q5I%22Q51%<3Q541p0>1p0E1p0Q11pS>Q71pS8Q81pS@Q81pS4Q:1pLQ<1").
Proof.
intros M a k b i Ha Hk Hi. unfold Wf.
rewrite wbytes_inside; rewrite ?repeat_length, ?art_u_lit by lia; try lia.
rewrite nth_repeat_lt by lia. reflexivity.
Qed.
Lemma Wn_eq : ltac2:(TCodec.tc2 tcn__ArtMem "Q4'4'QNyR0%211'6y8%511%311p051':'8r6r5%33521r4%53631r3%73831&@r:r9r7%44321:r8%6451=:%?3A31p091p0<1p0?1pT6D1pT4E1pS6F1pS4G1pNI1pLJ1pSFQ31").
Proof. intros; subst; reflexivity. Qed.
Lemma Wf_eq : ltac2:(TCodec.tc2 tcn__ArtMem "Q8'QNyR0%211'6y8%511%311p051':'4'8r8r7%33621r6%53731r5%73831r4%93;31&?r<r:%3421<9r;r9%6421>:%A3D41p091p0<1p0?1p0B1pS:H1pS8I1pSBI1pS@J1pS6L1pS4M1pNO1pLQ01").
Proof. intros; subst; reflexivity. Qed.
Lemma cell_rdn8 : ltac2:(TCodec.tc2 tcn__ArtMem "Q:'QNyR0%211'6y8%511%311p051':&Br3r2u8r1%544321'7'8'3%11=%@11&GvQLr4&QM%12G>%54431=(0&<%52KA%22A1%42<1%?3<61&;%114&QO%12Q27%D3L31%F261p0H1pT4O1pS4Q01pLQ21").
Proof. intros M a v H. split; [exact H | apply bytes_le_to_Z_8]. Qed.
Lemma cell_rdn1 : ltac2:(TCodec.tc2 tcn__ArtMem "Q?'QNyR0%211'6y8%511%311p051':'7&Q9zr1%3221&Q:+X0%2241%8241&Br4r3u1r2%544321'8'3%11E%H11&GvQLr5&QM%12O=%54431<(0(2%52Q0@(5%11Q1%43Q231%62>1%A3>81p0C1p0J1pT4Q41pS4Q51pLQ71").
Proof. intros M a v Hv H. unfold cell in H. rewrite art_bytes1 in H by lia. exact H. Qed.
Lemma cell_rdn4 : ltac2:(TCodec.tc2 tcn__ArtMem "QF'QNyR0%211'6y8%511%311p051':'7&Q9zr1%3221&Q:&Q?+2+Q0%3221%5271%;271&Br4r3u4r2%544321'8'3%11H%K11&GvQLr5&QM%12Q2=%54431<(0&<%52Q6@%22@1%42<1%?3<61&;%114&QO%12Q=7%D3Q731%Q7261p0G1p0N1pT4Q;1pS4Q<1pLQ>1").
Proof. intros M a v Hv H. split; [exact H | apply art_bytes4; exact Hv]. Qed.
End WithSegs.
