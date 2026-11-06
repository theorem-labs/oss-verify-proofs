(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec SeqExec StepTac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__MuslStrlen () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MuslStrlen.HZ."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1O"; "1S"; "1Some"; "1app"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "2and"; "2eq"; "2ex"; "2not"; "3add"; "4le"]; ["4lt"; "5Forall"; "5firstn"; "5map"; "5nth"; "6Z"; "7bytes_le_to_Z"; "7nat_to_word"; "8PhdrInfo"; "8Segment"; "9entry_stack_image"; ":EntryDraw"; ":build_stack_bytes"; ":stack_to_mem"; "0Q"; ";byte_at"]; [";cat_argv_ptr"; ";cat_struct_size"; "<ALLONES"; "<HIGHS"; "<ONESNEG"; "<Tz"; "<zb"; "<zdig"; "=rdn"; "=total_arg_bytes_nat"; "=v_add"; "=v_and"; "=v_xori"; "=wrap_mem"; ">add"; ">land"]; [">le"; ">lor"; ">lt"; ">lxor"; ">modulo"; ">mul"; ">of_nat"; ">pow"; ">shiftl"; ">shiftr"; ">sub"; "0a"; "0av"; "0b"; "0bs"; "0c"]; ["0d"; "0ds"; "0e"; "0ev"; "0hi"; "0hw"; "0i"; "0j"; "0k"; "0l"; "0lo"; "0m"; "0mem"; "0p"; "0ph"; "0post"]; ["0pre"; "0ptr"; "0rnd"; "0s"; "0segs"; "0sp"; "?Z_to_bv"; "?bv"; "?bv_add"; "?bv_unsigned"; "0u"; "0uid"; "0v"; "0w"; "0x"; "0y"]]).
Module HZ.
Local Open Scope Z_scope.
Definition zb (x : Z) (i : nat) : Z := (x / 2^(8 * Z.of_nat i)) mod 256.
Fixpoint zdig (ds : list Z) : Z :=
match ds with [] => 0 | d :: r => d + 256 * zdig r end.
Lemma pow2_8i_pos : ltac2:(TCodec.tc2 tcn__MuslStrlen ">'7&QBz&QG+2&QE+8&QFr1%211%5241%8271%;2:1pT>=1").
Proof. intro i. apply Z.pow_pos_nonneg; lia. Qed.
Lemma zb_bound : ltac2:(TCodec.tc2 tcn__MuslStrlen "@'E'7':&Q@z&Q6r2r1%3221%6251&QB+X0%2241%;241pT>=1pUN?1").
Proof. intros. unfold zb. apply Z.mod_pos_bound. lia. Qed.
Lemma zb_0 : ltac2:(TCodec.tc2 tcn__MuslStrlen "9'7';'E&Q6zr1%3221%63513pT>81").
Proof. intro i. unfold zb. rewrite Zdiv_0_l. reflexivity. Qed.
Lemma land_land_m : ltac2:(TCodec.tc2 tcn__MuslStrlen "?'E';&Q?r3r2%3221r1%5221%6252%7253%8221%:3;41pTH<1pSL=1pSH>1").
Proof.
intros. apply Z.bits_inj'. intros n Hn.
rewrite !Z.land_spec.
destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit m n); reflexivity.
Qed.
Lemma land_lxor_m : ltac2:(TCodec.tc2 tcn__MuslStrlen "@'E';&Q?&QCr3r2%3221r1%6221%7252%8253%8221%;3<41pTH=1pSL>1pSH?1").
Proof.
intros. apply Z.bits_inj'. intros n Hn.
rewrite Z.land_spec, !Z.lxor_spec, !Z.land_spec.
destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit m n); reflexivity.
Qed.
Lemma lxor_lt64 : ltac2:(TCodec.tc2 tcn__MuslStrlen "H'E':&Q@zr2%3221&QB&QG+2+R0%3221%5271%;271&QCr4r3%3221%?2>1%<228%B221p081p091pSLF1pSHG1").
Proof.
intros a b Ha Hb.
assert (Hn : 0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia).
split; [lia|].
assert (E : Z.lxor a b mod 2^64 = Z.lxor a b).
{ rewrite <- Z.land_ones by lia. rewrite land_lxor_m.
rewrite !Z.land_ones by lia. rewrite !Z.mod_small by lia. reflexivity. }
rewrite <- E. apply Z.mod_pos_bound. lia.
Qed.
Lemma zb_alt : ltac2:(TCodec.tc2 tcn__MuslStrlen "D'E'7';&Q6r2r1%3221&Q?&QI&QE+8&QF%117%4231%62:1+WO%9221%?3A;1pT>A1pUNC1").
Proof.
intros x i. unfold zb.
rewrite Z.shiftr_div_pow2 by lia.
change 255 with (Z.ones 8).
rewrite Z.land_ones by lia. reflexivity.
Qed.
Lemma zb_land : ltac2:(TCodec.tc2 tcn__MuslStrlen "A'E'7';&Q6&Q?r3r2%3221r1%6221%7252%8253%8221%;3=41pT>=1pUL?1pUF@1").
Proof.
intros u w i. rewrite !zb_alt.
rewrite Z.shiftr_land, land_land_m. reflexivity.
Qed.
Lemma zb_lxor : ltac2:(TCodec.tc2 tcn__MuslStrlen "A'E'7';&Q6&QCr3r2%3221r1%6221%7252%8253%8221%;3=41pT>=1pUL?1pUF@1").
Proof.
intros u w i. rewrite !zb_alt.
rewrite Z.shiftr_lxor, land_lxor_m. reflexivity.
Qed.
Lemma zdig_nonneg : ltac2:(TCodec.tc2 tcn__MuslStrlen "E'6'E%211'A':&Q@zr1%3221&QB+X0%2241%8241qT2<1%;3=17&Q7r2%211%=2<1p051pT4B1").
Proof.
induction ds as [|d ds IH]; intro H; cbn [zdig]; [lia|].
apply Forall_cons_iff in H as [Hd Hds]; cbv beta in Hd.
specialize (IH Hds). lia.
Qed.
Lemma zdig_lt : ltac2:(TCodec.tc2 tcn__MuslStrlen "O'6'E%211'A':&Q@zr1%3221&QB+X0%2241%8241qT2<1%;3=17&Q7r2%211&QG+2&QE+8&QF&5%12G8%311%6251%9281%C2;1p0?1pT4L1").
Proof.
induction ds as [|d ds IH]; intro H; cbn [zdig length].
- cbn. lia.
- apply Forall_cons_iff in H as [Hd Hds]; cbv beta in Hd.
specialize (IH Hds).
replace (8 * Z.of_nat (S (length ds))) with (8 + 8 * Z.of_nat (length ds)) by lia.
rewrite Z.pow_add_r by lia. change (2^8) with 256. lia.
Qed.
Lemma zb_zdig : ltac2:(TCodec.tc2 tcn__MuslStrlen "Q3'6'E%211'A':&Q@zr1%3221&QB+X0%2241%8241qT2<1%;3=17'7&@&5r3%22B1%42=1';&Q6&Q7r4%211r2%5221&D%14L35G%93M31p0;1pT>A1p0C1pT4Q01").
Proof.
induction ds as [|d ds IH]; intros H i Hi; [cbn in Hi; lia|].
apply Forall_cons_iff in H as [Hd Hds]; cbv beta in Hd.
pose proof (zdig_nonneg ds Hds) as Hnn.
destruct i as [|i]; cbn [nth].
- cbn [zdig]. unfold zb.
change (8 * Z.of_nat 0) with 0. change (2^0) with 1.
rewrite Z.div_1_r.
replace (d + 256 * zdig ds) with (d + zdig ds * 256) by lia.
rewrite Z.mod_add by lia.
apply Z.mod_small. lia.
- cbn [length] in Hi.
rewrite <- (IH Hds i ltac:(lia)).
cbn [zdig]. unfold zb.
replace (8 * Z.of_nat (S i)) with (8 + 8 * Z.of_nat i) by lia.
rewrite Z.pow_add_r by lia. change (2^8) with 256.
rewrite <- Z.div_div by (try lia; apply pow2_8i_pos).
replace ((d + 256 * zdig ds) / 256) with (zdig ds); [reflexivity|].
replace (d + 256 * zdig ds) with (zdig ds * 256 + d) by lia.
rewrite Z.div_add_l by lia.
rewrite (Z.div_small d 256) by lia. lia.
Qed.
Lemma zdig_recon8 : ltac2:(TCodec.tc2 tcn__MuslStrlen "Q@'E':&Q@zr1%3221&QB&QG+2+R0%3221%5271%;271';r2&Q7(4&Q6(0%2251u1%4271u2%6291u3%82;1u4%:2=1u5%<2?1u6%>2A1u7%@2C1(8%11Q3%D3Q431%E3Q561%F3Q691%G3Q7<1%H3Q8?1%I3Q9B1%J3Q:E1%K3Q;H1%M11%Q03Q=O1p0Q21pUNQ?1").
Proof.
intros x Hx. cbn [zdig]. unfold zb.
change (8 * Z.of_nat 0) with 0. change (8 * Z.of_nat 1) with 8.
change (8 * Z.of_nat 2) with 16. change (8 * Z.of_nat 3) with 24.
change (8 * Z.of_nat 4) with 32. change (8 * Z.of_nat 5) with 40.
change (8 * Z.of_nat 6) with 48. change (8 * Z.of_nat 7) with 56.
change (2^0) with 1. rewrite Z.div_1_r.
change (2^8) with 256.
change (2^16) with (256*256).
change (2^24) with (256*256*256).
change (2^32) with (256*256*256*256).
change (2^40) with (256*256*256*256*256).
change (2^48) with (256*256*256*256*256*256).
change (2^56) with (256*256*256*256*256*256*256).
rewrite <- !Z.div_div by lia.
pose proof (Z.div_mod x 256 ltac:(lia)).
pose proof (Z.div_mod (x/256) 256 ltac:(lia)).
pose proof (Z.div_mod (x/256/256) 256 ltac:(lia)).
pose proof (Z.div_mod (x/256/256/256) 256 ltac:(lia)).
pose proof (Z.div_mod (x/256/256/256/256) 256 ltac:(lia)).
pose proof (Z.div_mod (x/256/256/256/256/256) 256 ltac:(lia)).
pose proof (Z.div_mod (x/256/256/256/256/256/256) 256 ltac:(lia)).
pose proof (Z.div_mod (x/256/256/256/256/256/256/256) 256 ltac:(lia)).
assert (Htop : x/256/256/256/256/256/256/256/256 = 0).
{ rewrite !Z.div_div by lia. apply Z.div_small. lia. }
lia.
Qed.
Lemma zb_eq0 : ltac2:(TCodec.tc2 tcn__MuslStrlen "N'E':&Q@zr1%3221&QB&QG+2+R0%3221%5271%;271'7&@u8%22<1';&Q6r4r2%3221%53F1Cp071pT>;1r3%93J1Gp031p0@1pUNM1").
Proof.
intros x Hx H. rewrite (zdig_recon8 x Hx).
rewrite !H by lia. cbn [zdig]. lia.
Qed.
Lemma zb_neq0 : ltac2:(TCodec.tc2 tcn__MuslStrlen "A'E'7&=';&Q6r2r1%3221z%63921%811r3%93<14%;11p041pT>>1pUN@1").
Proof. intros x i H Hc. subst. rewrite zb_0 in H. lia. Qed.
Lemma zb_split : ltac2:(TCodec.tc2 tcn__MuslStrlen "Q7'E'7':&Q@zr3%3221&QB&QG+2&QE+8&QFr1%211%5241%8271%:2<1%@2<1';&Q6&Q>r5%;1B%>2=1%A2@1r4%A221%7261%921H&QD+X0%2261%>3Q141p0L1p0A1pT>Q31pT:Q51pTFQ61").
Proof.
intros lo hi i Hlo Hhi. unfold zb.
rewrite Z.mul_comm, Z.div_add by (pose proof (pow2_8i_pos i); lia).
rewrite (Z.div_small lo) by lia. reflexivity.
Qed.
Lemma zb_mod64 : ltac2:(TCodec.tc2 tcn__MuslStrlen "Q0'E'7&@r1u8%3221':&Q@zr3%3221&QB&QG+2+R1%3221%5271%;271';&Q6&QDr4+R0%;2:1%4231%621@%725A%93K21p0;1p0H1pT>M1pV0O1").
Proof.
intros y i Hi Hy.
destruct (Z_lt_le_dec y (2^64)) as [Hlt|Hge].
- rewrite Z.mod_small by lia. reflexivity.
- assert (Hm : y mod 2^64 = y - 2^64).
{ replace y with ((y - 2^64) + 1 * 2^64) at 1 by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
rewrite Hm. unfold zb.
pose proof (pow2_8i_pos i) as Hk.
assert (Hd : 2^64 = 2^(64 - 8 * Z.of_nat i) * 2^(8 * Z.of_nat i)).
{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
assert (Hdiv : (256 | 2^(64 - 8 * Z.of_nat i))).
{ replace (64 - 8 * Z.of_nat i) with (8 + (56 - 8 * Z.of_nat i)) by lia.
rewrite Z.pow_add_r by lia. change (2^8) with 256.
apply Z.divide_factor_l. }
destruct Hdiv as [q Hq].
replace (y - 2^64) with (y + (- (q * 256)) * 2^(8 * Z.of_nat i))
by (rewrite Hd, Hq; lia).
rewrite Z.div_add by lia.
replace (y / 2 ^ (8 * Z.of_nat i) + - (q * 256))
with (y / 2 ^ (8 * Z.of_nat i) + (- q) * 256) by lia.
rewrite Z.mod_add by lia. reflexivity.
Qed.
Definition ONESNEG : Z := 18374403900871474943.
Definition HIGHS : Z := 9259542123273814144.
Definition ALLONES : Z := 18446744073709551615.
Definition Tz (x : Z) : Z :=
Z.land (Z.land ((x + ONESNEG) mod 2^64) (Z.lxor x ALLONES)) HIGHS.
Lemma land_le_r : ltac2:(TCodec.tc2 tcn__MuslStrlen "='E&Q@zr1%3221&Q?r3r2%3221%8212p061pSL;1pSH<1").
Proof.
intros a b Hb.
rewrite Z.land_comm.
pose proof (Z.sub_land_same_l b a) as H.
assert (0 <= Z.land b (Z.lnot a)) by (apply Z.land_nonneg; left; lia).
lia.
Qed.
Lemma land_le_l : ltac2:(TCodec.tc2 tcn__MuslStrlen "<'E&Q@zr2%3221&Q?r3%2214%7212p051pSL:1pSH;1").
Proof. intros a b Ha. rewrite Z.land_comm. apply land_le_r. exact Ha. Qed.
Lemma Tz_range : ltac2:(TCodec.tc2 tcn__MuslStrlen "@'E':&Q@z&Q5r1%211%5241&QB&QG+2+R0%3221%5271%=271pUN?1").
Proof.
intro x. unfold Tz. split.
- apply Z.land_nonneg. right. unfold HIGHS. lia.
- pose proof (land_le_r (Z.land ((x + ONESNEG) mod 2^64) (Z.lxor x ALLONES)) HIGHS
ltac:(unfold HIGHS; lia)). unfold HIGHS in *. lia.
Qed.
Ltac by8 i := destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; try lia; vm_compute; reflexivity.
Lemma zb_ALLONES : ltac2:(TCodec.tc2 tcn__MuslStrlen "?'7&@r1u8%3221';'E&Q6&Q2r2%3221+WO%73621p091pT>>1").
Proof. intros i Hi. by8 i. Qed.
Lemma zb_HIGHS : ltac2:(TCodec.tc2 tcn__MuslStrlen "?'7&@r1u8%3221';'E&Q6&Q3r2%3221+T0%73621p091pT>>1").
Proof. intros i Hi. by8 i. Qed.
Lemma Tz_byte : ltac2:(TCodec.tc2 tcn__MuslStrlen "Q3'E'7&@r1u8%3221';&Q6&Q5r3%211r2%5221&Q?&QD&Q>&Q4%2281&QG+2+R0%3221%8251%@21<&QC%B2@>+WO%3221%?251+T0%A221%I3OC1p0K1pT>Q01pUNQ21").
Proof.
intros x i Hi. unfold Tz.
rewrite !zb_land, zb_lxor, zb_ALLONES by exact Hi.
rewrite zb_HIGHS by exact Hi. reflexivity.
Qed.
Lemma byte_nozero : ltac2:(TCodec.tc2 tcn__MuslStrlen "G'E':&Q@+1r1%3221+WO%5231%7231';&Q?&QJr2%221:&QC%1239%6231+T0%8221z%;3D21p0=1pT0F1").
Proof.
intros c Hc.
assert (Hin : In (Z.to_nat c) (seq 1 255)) by (apply in_seq; lia).
assert (Hall : forallb (fun n =>
Z.eqb (Z.land (Z.land (Z.of_nat n - 1) (Z.lxor (Z.of_nat n) 255)) 128) 0)
(seq 1 255) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in Hall. specialize (Hall _ Hin).
apply Z.eqb_eq in Hall.
replace (Z.of_nat (Z.to_nat c)) with c in Hall by lia. exact Hall.
Qed.
Lemma Tz_nozero : ltac2:(TCodec.tc2 tcn__MuslStrlen "Q2'E':&Q@zr1%3221&QB&QG+2+R0%3221%5271%;271'7&@u8%22<1&=';&Q6r4r2%3221%53G1D%711p091pT>=1&Q5r3%211%<3N1Kp051p0D1pUNQ11").
Proof.
intros x Hx Hnz.
pose proof (zb_bound x 0). pose proof (zb_bound x 1). pose proof (zb_bound x 2).
pose proof (zb_bound x 3). pose proof (zb_bound x 4). pose proof (zb_bound x 5).
pose proof (zb_bound x 6). pose proof (zb_bound x 7).
pose proof (Hnz 0%nat ltac:(lia)). pose proof (Hnz 1%nat ltac:(lia)).
pose proof (Hnz 2%nat ltac:(lia)). pose proof (Hnz 3%nat ltac:(lia)).
pose proof (Hnz 4%nat ltac:(lia)). pose proof (Hnz 5%nat ltac:(lia)).
pose proof (Hnz 6%nat ltac:(lia)). pose proof (Hnz 7%nat ltac:(lia)).
pose proof (zdig_recon8 x Hx) as Hrec.
set (ds' := [zb x 0 - 1; zb x 1 - 1; zb x 2 - 1; zb x 3 - 1;
zb x 4 - 1; zb x 5 - 1; zb x 6 - 1; zb x 7 - 1]).
assert (Hds' : Forall (fun d => 0 <= d < 256) ds').
{ unfold ds'. repeat constructor; lia. }
assert (Hlt' : 0 <= zdig ds' < 2^64).
{ split; [apply zdig_nonneg; exact Hds'|].
pose proof (zdig_lt ds' Hds') as H'. unfold ds' in H' |- *.
cbn [length] in H'. exact H'. }
assert (Hy : (x + ONESNEG) mod 2^64 = zdig ds').
{ rewrite Hrec at 1.
replace (zdig [zb x 0; zb x 1; zb x 2; zb x 3; zb x 4; zb x 5; zb x 6; zb x 7]
+ ONESNEG)
with (zdig ds' + 1 * 2^64)
by (unfold ds', ONESNEG; cbn [zdig]; lia).
rewrite Z.mod_add by lia. apply Z.mod_small. exact Hlt'. }
apply zb_eq0; [apply Tz_range|].
intros i Hi. rewrite Tz_byte by exact Hi. rewrite Hy.
rewrite (zb_zdig ds' Hds' i) by (unfold ds'; cbn [length]; lia).
destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; try lia;
unfold ds'; cbn [nth]; apply byte_nozero; lia.
Qed.
Lemma zb_split_255 : ltac2:(TCodec.tc2 tcn__MuslStrlen "Q>'E'7';r1&QG+2&QE+8&QFr2%211%5241%8271%;3=:1r6&Q>r5+WO+X0r4%>221%6241%@2=1%8271%F3H:1':&Q@z%221>&QBr3%22A1%7241&Q6r9%221E%Q23Q41Cp091p061p0?1p0K1pTLQ91pT>Q91pQNQ;1pTFQ<1pUJQ=1").
Proof.
intros v lo Q i p Hp Hv Hlo HQ. subst p v.
rewrite zb_split by (try lia; assumption).
replace (255 + 256 * Q) with (255 + Q * 256) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma sum_byte_255 : ltac2:(TCodec.tc2 tcn__MuslStrlen "Q>'E'7':&Q@zr2%3221&QB&QG+2+R0%3221%5271%;271&@u8%22;1';&Q6r4r3%3221%53F1Br1r5%;221&=r7%:21G%<3M1I%411p061pT@O1&Q>r6&Q4%3221%C21=+WO%F3Q721p081p0C1p0J1p0N1pT>Q;1pUNQ=1").
Proof.
intros x i Hx Hi Hz Hlow.
pose proof (zb_bound x 0). pose proof (zb_bound x 1). pose proof (zb_bound x 2).
pose proof (zb_bound x 3). pose proof (zb_bound x 4). pose proof (zb_bound x 5).
pose proof (zb_bound x 6). pose proof (zb_bound x 7).
pose proof (zdig_recon8 x Hx) as Hrec. cbn [zdig] in Hrec.
unfold ONESNEG.
destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; try lia.
-
apply (zb_split_255 _ (0) (zb x 1 * 1 + zb x 2 * 256 + zb x 3 * 65536 + zb x 4 * 16777216 + zb x 5 * 4294967296 + zb x 6 * 1099511627776 + zb x 7 * 281474976710656 + 71775015237779198) 0%nat 1);
[ vm_compute; reflexivity | lia | lia | lia ].
-
pose proof (Hlow 0%nat ltac:(lia)).
apply (zb_split_255 _ ((zb x 0 - 1) * 1) (zb x 2 * 1 + zb x 3 * 256 + zb x 4 * 65536 + zb x 5 * 16777216 + zb x 6 * 4294967296 + zb x 7 * 1099511627776 + 280371153272574) 1%nat 256);
[ vm_compute; reflexivity | lia | lia | lia ].
-
pose proof (Hlow 0%nat ltac:(lia)).
pose proof (Hlow 1%nat ltac:(lia)).
apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256) (zb x 3 * 1 + zb x 4 * 256 + zb x 5 * 65536 + zb x 6 * 16777216 + zb x 7 * 4294967296 + 1095199817470) 2%nat 65536);
[ vm_compute; reflexivity | lia | lia | lia ].
-
pose proof (Hlow 0%nat ltac:(lia)).
pose proof (Hlow 1%nat ltac:(lia)).
pose proof (Hlow 2%nat ltac:(lia)).
apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536) (zb x 4 * 1 + zb x 5 * 256 + zb x 6 * 65536 + zb x 7 * 16777216 + 4278124286) 3%nat 16777216);
[ vm_compute; reflexivity | lia | lia | lia ].
-
pose proof (Hlow 0%nat ltac:(lia)).
pose proof (Hlow 1%nat ltac:(lia)).
pose proof (Hlow 2%nat ltac:(lia)).
pose proof (Hlow 3%nat ltac:(lia)).
apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536 + (zb x 3 - 1) * 16777216) (zb x 5 * 1 + zb x 6 * 256 + zb x 7 * 65536 + 16711422) 4%nat 4294967296);
[ vm_compute; reflexivity | lia | lia | lia ].
-
pose proof (Hlow 0%nat ltac:(lia)).
pose proof (Hlow 1%nat ltac:(lia)).
pose proof (Hlow 2%nat ltac:(lia)).
pose proof (Hlow 3%nat ltac:(lia)).
pose proof (Hlow 4%nat ltac:(lia)).
apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536 + (zb x 3 - 1) * 16777216 + (zb x 4 - 1) * 4294967296) (zb x 6 * 1 + zb x 7 * 256 + 65278) 5%nat 1099511627776);
[ vm_compute; reflexivity | lia | lia | lia ].
-
pose proof (Hlow 0%nat ltac:(lia)).
pose proof (Hlow 1%nat ltac:(lia)).
pose proof (Hlow 2%nat ltac:(lia)).
pose proof (Hlow 3%nat ltac:(lia)).
pose proof (Hlow 4%nat ltac:(lia)).
pose proof (Hlow 5%nat ltac:(lia)).
apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536 + (zb x 3 - 1) * 16777216 + (zb x 4 - 1) * 4294967296 + (zb x 5 - 1) * 1099511627776) (zb x 7 * 1 + 254) 6%nat 281474976710656);
[ vm_compute; reflexivity | lia | lia | lia ].
-
pose proof (Hlow 0%nat ltac:(lia)).
pose proof (Hlow 1%nat ltac:(lia)).
pose proof (Hlow 2%nat ltac:(lia)).
pose proof (Hlow 3%nat ltac:(lia)).
pose proof (Hlow 4%nat ltac:(lia)).
pose proof (Hlow 5%nat ltac:(lia)).
pose proof (Hlow 6%nat ltac:(lia)).
apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536 + (zb x 3 - 1) * 16777216 + (zb x 4 - 1) * 4294967296 + (zb x 5 - 1) * 1099511627776 + (zb x 6 - 1) * 281474976710656) (0) 7%nat 72057594037927936);
[ vm_compute; reflexivity | lia | lia | lia ].
Qed.
Lemma Tz_haszero : ltac2:(TCodec.tc2 tcn__MuslStrlen "Q<'E'7':&Q@zr2%3221&QB&QG+2+R0%3221%5271%;271&@u8%22;1';&Q6r4r3%3221%53F1Br1r5%;221&=r7%:21G%<3M1I%411p061pT@O1&Q5r6%211%C3Q41Q0%;11p061p0A1p0H1p0L1pT>Q91pUNQ;1").
Proof.
intros x i Hx Hi Hz Hlow.
apply (zb_neq0 _ i).
rewrite Tz_byte by exact Hi.
rewrite zb_mod64 by (first [exact Hi | unfold ONESNEG; lia]).
rewrite (sum_byte_255 x i Hx Hi Hz Hlow), Hz.
vm_compute. discriminate.
Qed.
End HZ.
Lemma u8_zero : ltac2:(TCodec.tc2 tcn__MuslStrlen "9';'E&RIy8&RFz%2231%5241%83713").
Proof. vm_compute. reflexivity. Qed.
Lemma lor_shiftl8 : ltac2:(TCodec.tc2 tcn__MuslStrlen "K'E':&Q@zr2%3221&QB+X0%2241%8241';&QAr4&QHr3+8%3221%6251&Q>&QE%12=6%3291%<3F51p0B1p0?1pV0I1pSHJ1").
Proof.
intros a y Ha Hy.
assert (Hs : Z.shiftl y 8 = (y * 2^8)%Z) by (apply Z.shiftl_mul_pow2; lia).
assert (Hland : Z.land a (Z.shiftl y 8) = 0%Z).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z.ltb n 8) eqn:E.
- apply Z.ltb_lt in E.
rewrite Hs, Z.mul_pow2_bits_low by lia. apply andb_false_r.
- apply Z.ltb_ge in E.
replace (Z.testbit a n) with false; [reflexivity|].
symmetry. apply Z.testbit_false; [lia|].
rewrite Z.div_small; [reflexivity|].
split; [lia|]. eapply Z.lt_le_trans; [apply Ha|].
change 256%Z with (2^8)%Z. apply Z.pow_le_mono_r; lia. }
rewrite <- Z.lxor_lor by exact Hland.
rewrite <- Z.add_nocarry_lxor by exact Hland.
rewrite Hs. lia.
Qed.
Lemma bytes_le_to_Z_zdig : ltac2:(TCodec.tc2 tcn__MuslStrlen "B'6'RGy8%211%411';'E&Fr1%211&Q7&C&RI%11;%34;816%511%;3:71pSN=1").
Proof.
induction bs as [|b bs IH]; [reflexivity|].
cbn [bytes_le_to_Z map HZ.zdig]. rewrite IH.
apply lor_shiftl8; [apply u8_range|].
apply HZ.zdig_nonneg. apply Forall_map, Forall_forall.
intros x _. apply u8_range.
Qed.
Lemma zb_of_bytes : ltac2:(TCodec.tc2 tcn__MuslStrlen "N'6'RGy8%211%411'7&@r1&5r2%2271%5241';'E&Q6&Fr3%211%4219&RI&D&RFz%22E1%44E?81%62G1%>3=81p0@1pT>G1pSNI1").
Proof.
intros bs i Hi. rewrite bytes_le_to_Z_zdig.
rewrite HZ.zb_zdig
by (first [ apply Forall_map, Forall_forall; intros x _; apply u8_range
| rewrite length_map; exact Hi ]).
rewrite <- (map_nth bv_unsigned bs (Z_to_bv 8 0) i), u8_zero. reflexivity.
Qed.
Lemma bytes_le_to_Z_range : ltac2:(TCodec.tc2 tcn__MuslStrlen "L'6'RGy8%211%411';'7&5r1%2261u8%63521':&Q@z&Fr2%211%5241&QB&QG+2+R0%3221%5271%=271p0?1pSNG1").
Proof.
intros bs Hl. rewrite bytes_le_to_Z_zdig.
assert (HF : Forall (fun d => (0 <= d < 256)%Z) (map bv_unsigned bs))
by (apply Forall_map, Forall_forall; intros x _; apply u8_range).
split; [apply HZ.zdig_nonneg; exact HF|].
pose proof (HZ.zdig_lt _ HF) as H.
rewrite length_map, Hl in H. exact H.
Qed.
Lemma v_haszero : ltac2:(TCodec.tc2 tcn__MuslStrlen "J'RGyR0%211';'E&RI&Q;&Q:r1&RF+_mognoko_mogO%22:1%5241&Q<-1%2271%:241+XQPTP`RPXQPT0%92A1%=231%?2C1&Q5%A2E>%211%E3D41pUJG1").
Proof.
intro v. pose proof (u64_range v) as Hv.
unfold v_and, v_add, v_xori, HZ.Tz, HZ.ONESNEG, HZ.HIGHS, HZ.ALLONES.
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
rewrite (Z.mod_small 18374403900871474943 (2^64)) by lia.
rewrite (Z.mod_small 9259542123273814144 (2^64)) by lia.
replace ((-1) mod 2^64)%Z with 18446744073709551615%Z
by (vm_compute; reflexivity).
assert (Hx : (0 <= Z.lxor (bv_unsigned v) 18446744073709551615 < 2^64)%Z)
by (apply HZ.lxor_lt64; lia).
rewrite (Z.mod_small (Z.lxor (bv_unsigned v) 18446744073709551615)) by exact Hx.
assert (Hm : (0 <= (bv_unsigned v + 18374403900871474943) mod 2^64 < 2^64)%Z)
by (apply Z.mod_pos_bound; lia).
assert (Hz : (0 <= Z.land ((bv_unsigned v + 18374403900871474943) mod 2^64)
(Z.lxor (bv_unsigned v) 18446744073709551615) < 2^64)%Z).
{ split; [apply Z.land_nonneg; left; lia|].
pose proof (HZ.land_le_l ((bv_unsigned v + 18374403900871474943) mod 2^64)
(Z.lxor (bv_unsigned v) 18446744073709551615) ltac:(lia)). lia. }
rewrite (Z.mod_small
(Z.land ((bv_unsigned v + 18374403900871474943) mod 2^64)
(Z.lxor (bv_unsigned v) 18446744073709551615))
(2^64)) by exact Hz.
apply Z.mod_small. split.
- apply Z.land_nonneg. right. lia.
- pose proof (HZ.land_le_r
(Z.land ((bv_unsigned v + 18374403900871474943) mod 2^64)
(Z.lxor (bv_unsigned v) 18446744073709551615))
9259542123273814144 ltac:(lia)). lia.
Qed.
Lemma total_arg_bytes_firstn_S : ltac2:(TCodec.tc2 tcn__MuslStrlen "Q4'6'RGy8%211%411%511'7&@r1&5r2%2271%5241';&Q9&B(1%117r3%43?21%611&>%73B<4%911&D(8%11G%34GA91%C2I1%8261u1%:221%C3J<1p0E1pTBL1pTDN1").
Proof.
induction l as [|s rest IH]; intros k Hk; [cbn in Hk; lia|].
destruct k as [|k]; cbn [firstn nth].
- cbv [total_arg_bytes_nat]. cbn [firstn fold_right].
rewrite firstn_O. cbn [fold_right]. lia.
- rewrite !total_arg_bytes_cons. cbn [length] in Hk.
rewrite (IH k ltac:(lia)). lia.
Qed.
Lemma bsb_len_lower : ltac2:(TCodec.tc2 tcn__MuslStrlen "Q6'H'RGyR0%211'6y8%511%311%411'K'?&>&Q1r5r4%3221&Q9%114%7231u@%9221&5&Lr7r6r3r2r1%6754?>321%82G1%D2:1pU6F1pT<M1pUHN1pT6J1pSHK1pU<Q11pTNQ51").
Proof.
intros ph sp a e uid hw rnd.
unfold build_stack_bytes, cat_struct_size. cbv zeta.
rewrite (string_addrs_pair a). cbv beta iota.
rewrite (string_addrs_pair e). cbv beta iota.
rewrite !length_app, !length_flat_map_le8,
!length_string_addrs_fst, !length_n_to_le_8, length_auxv_bytes,
!length_flatten_strings, !repeat_length, length_at_random_bytes.
lia.
Qed.
Lemma bsb_word_k : ltac2:(TCodec.tc2 tcn__MuslStrlen "R8'H'RGyR0%211'6y8%511%311%411'7'K&@r5&5r7%2281%5241'?&Dr6r8(8%11@%54@431%;2B1%82=1'<':';&Lr=r<r;r:%574321D?F&3r2r1%33Q021%;3Q051%K2Q24&>&Q1%12;:&Q9&Br9%23Q81?%411%8261%921N%G3Q:;1u8%Q82Q?@%Q5221%L241%M2A1qU0QB1%Q02QC1qU2QD1%Q22QE1p0Q41p0Q>1pU6QE1pT<QM1pUHQN1pTHQI1pTBQJ1pT6QL1pSHQM1pU<R31pTNR71").
Proof.
intros ph sp a e k m uid hw rnd Hk Hm.
destruct (bsb_byte_k ph sp a e k uid hw rnd Hk) as [pre0 [post0 [E Hlen0]]].
pose proof (bsb_len_lower ph sp a e uid hw rnd) as Hlow.
pose proof (total_arg_bytes_firstn_le (S k) a) as Hmono.
pose proof (total_arg_bytes_firstn_S a k Hk) as Hstep.
set (s1 := (nth k a [] ++ [Z_to_bv 8 0])) in *.
assert (Hs1 : length s1 = (length (nth k a []) + 1)%nat)
by (unfold s1; rewrite length_app; cbn [length]; lia).
assert (Hpost0 : (16 <= length post0)%nat).
{ assert (Hl : length (build_stack_bytes ph sp a e uid hw rnd)
= (length pre0 + length s1 + length post0)%nat)
by (rewrite E, !length_app; lia).
lia. }
exists (pre0 ++ firstn m s1), (skipn m s1 ++ post0).
split; [|split].
- rewrite E, <- !app_assoc. f_equal.
rewrite app_assoc, firstn_skipn. reflexivity.
- rewrite length_app, Hlen0, firstn_length_le by lia. lia.
- rewrite length_app, length_skipn. lia.
Qed.
Lemma read_word_stack : ltac2:(TCodec.tc2 tcn__MuslStrlen "RK'H'6'I%211'RGyR0%211y8%411%811%911'7'K&@r5&5r7%2281%5241'?&Dr6r8(8%11@%54@431%;2B1%82=1&QB&Q>&RIr:%22K1&QF&Lr<r9r4r3%57483AI21%I2Q01%811%=2:1&QG+2+R0%3221%C251'<':';r1%Q52Q<1u8%43Q;21'9%11Q?&Q8r=&M&Jr>r;%372L1Q0Q?Q:QA%52M1&RH&Q0%14Q05Q4O&G%11Q?%53R131%>4=71B(2%12R0F%H3B31%J2E1qSNR31%M2R41p0O1p0QD1p0QN1pU6R51pT<R<1pUHR=1pTHR91pTBR:1pT6R<1pSHR=1pU<RB1pU:RF1pTNRJ1").
Proof.
intros ph segs sp a e k m uid hw rnd Hk Hm Hnw.
destruct (bsb_word_k ph sp a e k m uid hw rnd Hk Hm) as [pre [post [E [Hlen Hpost]]]].
exists (firstn 8 post). split; [apply firstn_length_le; lia|].
replace (cat_argv_ptr sp a e k + nat_to_word m)
with (sp + nat_to_word (length pre)).
2:{ rewrite Hlen, (cat_argv_ptr_offset sp a e k Hk). unfold cat_string_base.
rewrite !nat_to_word_add_merge. f_equal. f_equal. lia. }
apply (read_at_offset_image segs ph sp a e uid hw rnd
pre (firstn 8 post) (skipn 8 post) 8%nat).
- rewrite E. f_equal. symmetry. apply firstn_skipn.
- apply firstn_length_le. lia.
- exact Hnw.
Qed.
Lemma word_bytes_nth : ltac2:(TCodec.tc2 tcn__MuslStrlen "R>'6'I%211'RGyR0%211'9y8%511%311p051%;13'7';%813&Q8r7r6&RHr5&Gr3%211%53C41u8%:49821(2r2%22A1%@3?41'?r1&5%12I@%4231r:r9r8%B1;%E3Q321u1%J46521(4&O%12LA(8%11Q6%53Q731%F2Q51%Q43Q381p0@1pT>Q71&@%12Q0M&>r4%22Q71%I2QAQ9%L221&D&RFz%22QG1%44QGQ<Q>1%:2Q@Q=%F2L1%QE3QJ31p091p0?1p0B1p0Q91pT@QK1pSNQM1pTHQM1pU8QO1pU4R61pTJR21pU:R;1").
Proof.
intros segs mem ptr s m bs j Hr Hb Hj Hmj.
pose proof (rdn_nth segs mem 8%nat _ bs j Hr Hj) as H1.
rewrite nat_to_word_add_merge in H1.
rewrite (Hb (m + j)%nat Hmj) in H1.
congruence.
Qed.
Section ArgvWord.
Variable segs : list Segment.
Variable ph : PhdrInfo.
Variable sp : word.
Variable av ev : list (list byte).
Variable uid : word.
Variable hw : word.
Variable rnd : EntryDraw.
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned sp)%Z.
Hypothesis Hsp_hi : (bv_unsigned sp <= sp_window_hi)%Z.
Lemma mstr_sp_lo : ltac2:(TCodec.tc2 tcn__MuslStrlen "7&Q@+SoonPPPPP0&RIyR0vRE%3221%6251").
Proof. exact Hsp_lo. Qed.
Lemma mstr_sp_hi : ltac2:(TCodec.tc2 tcn__MuslStrlen "7&Q@&RIyR0vRE%3221+TPPPPPPPP0%6221").
Proof. exact Hsp_hi. Qed.
Lemma mstr_bsb_nw : ltac2:(TCodec.tc2 tcn__MuslStrlen "K&QB&Q>&RIyR0vRE%3221&QF&5'RGy8%211&LvR>vQLvR3vRKvR5vRB%776>54321%<291%>11%D2@1&QG+2+R0%3221%J251").
Proof.
pose proof (bsb_bound ph sp av ev uid hw rnd Hva Hve). pose proof mstr_sp_hi. lia.
Qed.
Lemma argv_ptr_room : ltac2:(TCodec.tc2 tcn__MuslStrlen "Q='7&@r1&5'6'RGy8%211%411vQL%7221%:291&Q@&Q>&RIyR0&Q0vREvR3r2%443;21%7261&QF&D(8%11B%34B7A1%H2D1%611%@281+A%B221%B2A?&LvR>vRKvR5vRB%574EMD321%Q42Q01%B11%L291%N2;1p0Q01pTBQ<1").
Proof.
intros k Hk.
pose proof mstr_sp_lo. pose proof mstr_sp_hi.
pose proof mstr_bsb_nw as Hnw.
pose proof (bsb_len_lower ph sp av ev uid hw rnd) as Hlow.
pose proof (total_arg_bytes_firstn_le (S k) av) as Hmono.
pose proof (total_arg_bytes_firstn_S av k Hk) as Hstep.
assert (Hptr : cat_argv_ptr sp av ev k
= sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (firstn k av))).
{ rewrite (cat_argv_ptr_offset sp av ev k Hk). unfold cat_string_base.
rewrite nat_to_word_add_merge. reflexivity. }
rewrite Hptr, word_add_nat, u_Z2bv by lia. lia.
Qed.
Lemma mstr_argv_ptr_bounds : ltac2:(TCodec.tc2 tcn__MuslStrlen "Q<'7&@r1&5'6'RGy8%211%411vQL%7221%:291':&Q@&RIyR0vRE%3221&Q0vR3r2%345<21%8271%:261&QB&Q>&QF&D(8%11F%34F:E1%L2H1%611%82;1+1%:221&QG+2+R0%3221%@251%M2B1p0O1pTBQ;1").
Proof.
intros k Hk. apply argv_ptr_bounds; try assumption.
pose proof mstr_sp_hi. unfold argv_layout_slack. lia.
Qed.
Lemma argv_word_readable : ltac2:(TCodec.tc2 tcn__MuslStrlen "QK'7&@r2&5'6'RGy8%211%411vQL%7221%:291'?&Dr3(8%119%449381%?2;1%72A1'<':';r1%E2A1u8%43J21'9%11D&Q8vRD&Q=vR>vREvR3vRKvR5vRB%7765M4321&RHyR0&Q0r5%24:Q291&Gr4%211%83741%C4B:1G(2%12Q:K%M3G31%O2J1qSNQ=1%Q22Q>1p0Q41p0Q=1pTHQI1pTBQJ1").
Proof.
intros k m Hk Hm.
pose proof mstr_sp_lo. pose proof mstr_sp_hi.
destruct (mstr_argv_ptr_bounds k Hk) as [Hge Hup].
pose proof (argv_ptr_room k Hk) as Hroom.
pose proof mstr_bsb_nw as Hnw.
pose proof (u64_range (cat_argv_ptr sp av ev k)).
assert (Hu : bv_unsigned (cat_argv_ptr sp av ev k + nat_to_word m)
= (bv_unsigned (cat_argv_ptr sp av ev k) + Z.of_nat m)%Z)
by (rewrite word_add_nat; apply u_Z2bv; lia).
destruct (read_word_stack ph segs sp av ev k m uid hw rnd Hk Hm Hnw) as [bs [Hl Hr]].
exists bs. split; [exact Hl|].
rewrite rdn_wrap_stack_above by (rewrite Hu; lia).
exact Hr.
Qed.
End ArgvWord.
