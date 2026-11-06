(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import PropExec MState.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Lib_Mem () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem.WithSegs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.Lists.List."; "Stdlib.NArith.BinNat.N."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1app"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1true"; "2I"; "2and"; "2eq"; "2ex"]; ["2iff"; "2not"; "2or"; "3add"; "4le"; "4lt"; "5firstn"; "5skipn"; "6N"; "6Z"; "7Z_to_le_bytes"; "7bytes_le_to_Z"; "7le_bytes_to_word"; "8ov_read_bytes"; "8store_ok"; "8width_bytes"]; ["8write_to_mem"; "8wview"; "9bv_eqb"; "9sext"; "9zext"; ":low32"; "<bytes_at"; "<mem_inv"; "<mrd"; "<ro_addr"; "<ro_byte"; "<ro_bytes"; "<upd_bytes"; "<wr_at"; ";le1"; ";le2"]; [";le4"; ";le8"; ";sx16"; ";sx32"; ";sx8"; ";sxb"; ";wa"; ";zx16"; ";zx32"; ";zx8"; ";zxb"; "=rdn"; ">nth_error"; "?lt"; "@add"; "@eqb"]; ["@le"; "@lt"; "@modulo"; "@mul"; "@of_N"; "@of_nat"; "@pow"; "@shiftr"; "@to_nat"; "0a"; "0b"; "0bs"; "0bs'"; "0bs1"; "0bs2"; "0c"]; ["0cs"; "0i"; "0j"; "0k"; "0m"; "0n"; "0segs"; "ABV"; "AZ_to_bv"; "Abv"; "Abv_add"; "Abv_extract"; "Abv_signed"; "Abv_swrap"; "Abv_unsigned"; "0v"]; ["0w"; "0x"; "0y"; "0z"]]).
Definition wa (a : Z) : word := Z_to_bv 64 a.
Lemma wa_unsigned : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "G'I'=&R0zr1%3221&R1&R6+2+R0%3221%5271%;271'>&RNyR0&QFr2%211%5241%73D13p091pTDF1").
Proof. intros. unfold wa. apply unsigned_lit. assumption. Qed.
Lemma wa_succ : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "D'I'>'RIyR0%211&RJ&QFr1%211(RG+1(<%33921%83:51/01:&QN%1296%;11%A3>41pTDC1").
Proof.
intros. unfold wa. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
change (bv_unsigned (1 : word)) with 1%Z. unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma wa_eqb : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "N'I'=&R0zr2%3221&R1&R6+2+R0%3221%5271%;271'>'3&Q2yR0&QFr4%211r3%411%73631&QO%1264%<3;31p0>1p0?1pTFL1pTDM1").
Proof. intros. unfold bv_eqb. rewrite !wa_unsigned by assumption. reflexivity. Qed.
Lemma wa_add_nat : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "F'RIyR0%211'8'>&RJr2&RH&R5r1%211%42:1%73;61&QF&QN&RN%12?:%3217%511%?3A71pU4A1pTDC1").
Proof.
intros. unfold wa. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
rewrite Zplus_mod_idemp_r. reflexivity.
Qed.
Lemma firstn_skipn_step : forall {A} (bs : list A) k n b,
nth_error bs k = Some b -> b :: firstn n (skipn (S k) bs) = firstn (S n) (skipn k bs).
Proof.
intros A bs. induction bs as [|x bs IH]; intros k n b E.
- destruct k; discriminate.
- destruct k as [|k]; cbn in E.
+ inversion E; subst. reflexivity.
+ cbn [skipn]. apply IH. exact E.
Qed.
Section WithSegs.
Variable segs : list Segment.
Definition mrd (m : word -> option byte) (a : word) : option byte :=
match m a with Some b => Some b | None => seg_rom segs a end.
Lemma rdn_unfold : forall m a n,
rdn segs m a n = match n with
| O => Some []
| S n' => match mrd m a with
| Some b => match rdn segs m (a + 1) n' with Some r => Some (b :: r) | None => None end
| None => None end
end.
Proof. intros m a [|n']; reflexivity. Qed.
Definition bytes_at (m : word -> option byte) (a : Z) (bs : list byte) : Prop :=
(0 <= a)%Z /\ (a + Z.of_nat (length bs) <= 2^64)%Z /\
forall i, (i < length bs)%nat -> mrd m (wa (a + Z.of_nat i)) = nth_error bs i.
Definition wr_at (m : word -> option byte) (a : Z) (n : Z) : Prop :=
(0 <= a)%Z /\ (a + n <= 2^64)%Z /\
forall i, (0 <= i < n)%Z -> wview segs m (wa (a + i)) <> None.
Definition ro_addr (a : word) : bool :=
match find_segment segs (bv_unsigned a) 1 with
| Some seg => negb (seg_writable seg)
| None => false
end.
Definition mem_inv (m : word -> option byte) : Prop :=
forall a b, m a = Some b -> ro_addr a = false.
Lemma bytes_at_rdn : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "QC'RIyR0%211':y8%511%311p051'I'7%115'8&Q6r5r4r3%43321'D&Cr2%2251&6%12A8%6231'>%F1?&QKvRFr7&QF&QNr6&R5%11C%4231%611%:4981E(1&F&G%13Q3JK%33Q4J1%52Q01%C3B71p0E1p0M1pU<Q31pU8Q41pTHQ61pTDQ91pU:Q;1").
Proof.
intros m a bs k n (Ha & Hlen & H). revert k.
induction n as [|n IH]; intros k Hk.
- reflexivity.
- rewrite rdn_unfold. rewrite (H k) by lia.
destruct (nth_error bs k) as [b|] eqn:E.
2:{ apply nth_error_None in E. lia. }
rewrite wa_succ. replace (a + Z.of_nat k + 1)%Z with (a + Z.of_nat (S k))%Z by lia.
rewrite (IH (S k)) by lia.
f_equal. apply firstn_skipn_step. exact E.
Qed.
Lemma bytes_at_ov_read : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "QC'RIyR0%211':y8%511%311p051'I'7%115'8&Q6r5r4r3%43321'D&Cr2%2251&6%12A8%6231'>%F1?&MvRFr7&QF&QNr6&R5%11C%4231%611%:4981E(1&F&G%13Q3JK%33Q4J1%52Q01%C3B71p0E1p0M1pU<Q31pU8Q41pTHQ61pTDQ91pU:Q;1").
Proof. intros. rewrite ov_rdn. apply bytes_at_rdn; assumption. Qed.
Lemma bytes_at_read : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "QH'RIyR0%211':y8%511%311p051'I'7%115'8&Q6r5r4r3%43321&R0z%2214'D&C&R8%119%3219&6%12E=%7231'>%J1C&MvRFr8&QF&QNr7%221G%411%84761H(1&F&G%D1Mr6%33Q721%53Q8O1%72Q41%C3B91p0E1p0N1p0Q21pU<Q81pU8Q<1pTHQ;1pTDQ>1pU:Q@1").
Proof.
intros m a bs k n H Hk Hn. rewrite <- (Z2Nat.id k) at 1 by lia.
apply bytes_at_ov_read; assumption.
Qed.
Lemma wr_at_store_ok : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "Q;'RIyR0%211':y8%511%311p051'I'8&Q=r5r4r3%43321&R0z%2214&QN&R5%117%3291%721;'>'3&NvRFr8&QFr7%<21C%311%74651D(;%;3:21p0=1p0C1p0G1pU6M1pU8O1pU<Q01pTDQ11pU:Q31").
Proof.
intros m a n k j (Ha & Hn & H) Hk Hj. revert k Hk Hj.
induction j as [|j IH]; intros k Hk Hj; [reflexivity|].
cbn [store_ok]. destruct (wview segs m (wa (a + k))) eqn:E.
2:{ exfalso. apply (H k); [lia|exact E]. }
rewrite wa_succ. replace (a + k + 1)%Z with (a + (k + 1))%Z by lia.
apply (IH (k + 1)%Z); lia.
Qed.
Lemma write_to_mem_spec : forall bs m (a : Z) (x : word),
(0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
write_to_mem m (wa a) bs x =
if (Z.leb a (bv_unsigned x) && Z.ltb (bv_unsigned x) (a + Z.of_nat (length bs)))%bool
then nth_error bs (Z.to_nat (bv_unsigned x - a))
else m x.
Proof.
induction bs as [|b bs IH]; intros m a x Ha Hl.
- cbn [write_to_mem length].
destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat 0)); cbn [andb]; try reflexivity.
exfalso; lia.
- cbn [write_to_mem]. cbn [length] in Hl.
rewrite wa_succ.
rewrite (IH _ (a + 1)%Z x) by lia.
pose proof (bv_unsigned_in_range 64 x) as Hx. unfold bv_modulus in Hx.
assert (Ewa : bv_unsigned (wa a) = a) by (apply wa_unsigned; lia).
unfold bv_eqb. rewrite Ewa. cbn [length].
destruct (Z.eqb_spec (bv_unsigned x) a) as [E|E];
destruct (Z.leb_spec0 (a+1) (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + 1 + Z.of_nat (length bs)));
destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat (S (length bs)))); cbn [andb];
try (exfalso; lia); try reflexivity.
+ rewrite E, Z.sub_diag. reflexivity.
+ replace (Z.to_nat (bv_unsigned x - a)) with (S (Z.to_nat (bv_unsigned x - (a + 1)))) by lia. reflexivity.
Qed.
Lemma bytes_at_write_same : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "Q8'RIyR0%211':y8%511%311p051'I'7%115&R0zr2%3221&QNr3&R5&6%12>6%311%6251&R6+2+R0%3221%?251&Q6&Q0r5&QFr4%211%5341A%7313Bp091p0F1pTHK1pTDN1pU:Q01").
Proof.
intros m a bs Ha Hl. split; [lia|]. split; [lia|].
intros i Hi. unfold mrd. rewrite write_to_mem_spec by lia.
rewrite wa_unsigned by lia.
destruct (Z.leb_spec0 a (a + Z.of_nat i)); destruct (Z.ltb_spec0 (a + Z.of_nat i) (a + Z.of_nat (length bs))); cbn [andb]; try (exfalso; lia).
replace (Z.to_nat (a + Z.of_nat i - a)) with i by lia.
destruct (nth_error bs i) eqn:E; [reflexivity|]. apply nth_error_None in E. lia.
Qed.
Lemma bytes_at_write_other : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "QK'RIyR0%211':y8%511%311p051'I'7%115&Q6r5r2r1%43321&R0z%2216&QNr6&R5&6%12B;%311%6251&R6+2+R0%3221%>251'Br4%;2L1%=11%@2G1r7%E221%@2Q1B%B11%E241%I21M%;251&Q0r9&QFr8%211%5341<%Q631MQ5p081p0E1p0Q21p0Q61pU2Q<1pU0Q?1pTHQ>1pTDQA1pU:QC1").
Proof.
intros m a bs c cs (Hc & Hcl & H) Ha Hal Hd. split; [lia|]. split; [lia|].
intros i Hi. unfold mrd. rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
destruct (Z.leb_spec0 a (c + Z.of_nat i)); destruct (Z.ltb_spec0 (c + Z.of_nat i) (a + Z.of_nat (length bs))); cbn [andb]; try (exfalso; lia);
apply H; exact Hi.
Qed.
Definition upd_bytes (cs : list byte) (k : nat) (bs : list byte) : list byte :=
firstn k cs ++ bs ++ skipn (k + length bs) cs.
Lemma upd_bytes_length : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "K'7'RIy8%211%411'8'D&Cr2&6r1%2281%5241r3%52;1%9231'>&Q<r4%2316;%;2A1%<2B3%63A21p081pTHD1pU8D1pU2F1").
Proof.
intros. unfold upd_bytes. rewrite !app_length, firstn_length, skipn_length. lia.
Qed.
Lemma upd_bytes_nth : forall cs k bs i, (k + length bs <= length cs)%nat -> (i < length cs)%nat ->
nth_error (upd_bytes cs k bs) i =
if (Nat.leb k i && Nat.ltb i (k + length bs))%bool then nth_error bs (i - k) else nth_error cs i.
Proof.
intros cs k bs i Hk Hi. unfold upd_bytes.
destruct (Nat.leb_spec0 k i); destruct (Nat.ltb_spec0 i (k + length bs)); cbn [andb].
- rewrite nth_error_app2 by (rewrite firstn_length; lia).
rewrite firstn_length. replace (Nat.min k (length cs)) with k by lia.
rewrite nth_error_app1 by lia. reflexivity.
- rewrite nth_error_app2 by (rewrite firstn_length; lia).
rewrite firstn_length. replace (Nat.min k (length cs)) with k by lia.
rewrite nth_error_app2 by lia.
rewrite nth_error_skipn. f_equal. lia.
- rewrite nth_error_app1 by (rewrite firstn_length; lia).
rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i k); [reflexivity| exfalso; lia].
- rewrite nth_error_app1 by (rewrite firstn_length; lia).
rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i k); [reflexivity| exfalso; lia].
Qed.
Lemma nth_error_write : forall m a bs c cs i,
bytes_at m c cs ->
(0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
(i < length cs)%nat ->
mrd (write_to_mem m (wa a) bs) (wa (c + Z.of_nat i)) =
if (Z.leb a (c + Z.of_nat i) && Z.ltb (c + Z.of_nat i) (a + Z.of_nat (length bs)))%bool
then nth_error bs (Z.to_nat (c + Z.of_nat i - a))
else nth_error cs i.
Proof.
intros m a bs c cs i (Hc & Hcl & H) Ha Hal Hi. unfold mrd. rewrite write_to_mem_spec by lia.
rewrite wa_unsigned by lia.
destruct (Z.leb_spec0 a (c + Z.of_nat i)); destruct (Z.ltb_spec0 (c + Z.of_nat i) (a + Z.of_nat (length bs))); cbn [andb];
try (apply H; exact Hi).
destruct (nth_error bs _) eqn:E2; [reflexivity|]. apply nth_error_None in E2. lia.
Qed.
Lemma bytes_at_write_inside : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "QA'RIyR0%211':y8%511%311p051'I'7%115&Q6r5r4r3%43321&R0z%2214'D&C&R8%119&6%12C:%5231%32E>%8221&Q0r8&QF&QNr7%221E%411%7361F&Q<r6%A1J%3321J%M3581p0>1p0H1p0L1pTHQ21pU8Q51pU2Q41pU0Q71pU:Q91").
Proof.
intros m c cs k bs Hat Hk Hkl. pose proof Hat as (Hc & Hcl & H).
split; [lia|]. split. { rewrite upd_bytes_length by lia. lia. }
intros i Hi. rewrite upd_bytes_length in Hi by lia.
rewrite (nth_error_write m (c + k) bs c cs i Hat) by lia.
rewrite upd_bytes_nth by lia.
destruct (Z.leb_spec0 (c + k) (c + Z.of_nat i)); destruct (Z.ltb_spec0 (c + Z.of_nat i) (c + k + Z.of_nat (length bs)));
destruct (Nat.leb_spec0 (Z.to_nat k) i); destruct (Nat.ltb_spec0 i (Z.to_nat k + length bs)); cbn [andb]; try (exfalso; lia); try reflexivity.
f_equal. lia.
Qed.
Lemma wview_write_mono : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "Q2'RIyR0%211':y8%511%311p051'7%114&A'>&Q1vRFr4r1%43321(0%11=%83=31%:11&Q0r5r3%332:1r2%>3=21%@3E19%B11p091pV4L1pTHF1pTDN1pU:J1").
Proof.
intros m a bs. revert m a. induction bs as [|b bs IH]; intros m a x H; cbn; [exact H|].
apply IH. unfold wview in *. destruct (bv_eqb x a); [discriminate|]. exact H.
Qed.
Lemma wr_at_write : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "K'RIyR0%211':y8%511%311p051'I'7%115&Q=r5r4r3%43321&Q0r6r2%33251%93187p061pTH<1pU0E1pU<@1pTDA1pU:C1").
Proof.
intros m a n c bs (Ha & Hn & H). split; [lia|]. split; [lia|].
intros i Hi. apply wview_write_mono. apply H. lia.
Qed.
Lemma write_to_mem_some : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "QD'7'RIy8%211%411yR0%511':%115p031'>&Q0r4r3r5r2%544321(1r1%22@1%:3<41'B%819%62D8%>3@21'?'8'=&E&6r7%22L1%42>1&QF&QN&RN%12OF&R5%11D%5231%711%O3Q3M1%?2:1qU4A1%C2B1%H2E1p0J1pTFQ<1pV4Q:1pTDQ;1pU:Q91pTHQ?1").
Proof.
induction bs as [|b0 bs IH]; intros m a x b H; cbn in H.
- left; exact H.
- destruct (IH _ _ _ _ H) as [H1 | (i & Hi & Hx)].
+ destruct (bv_eqb x a) eqn:E.
* right. exists 0%nat. split; [cbn; lia|]. unfold bv_eqb in E. apply Z.eqb_eq in E.
apply bv_eq. rewrite wa_unsigned. 2:{ pose proof (bv_unsigned_in_range 64 a); unfold bv_modulus in *; cbn [Z.of_nat]; lia. }
cbn [Z.of_nat]. lia.
* left; exact H1.
+ right. exists (S i). split; [cbn; lia|]. rewrite Hx. unfold wa. apply bv_eq.
rewrite !Z_to_bv_unsigned, bv_add_unsigned. change (bv_unsigned (1:word)) with 1%Z.
unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.
Lemma store_ok_wview : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "Q<'RIyR0%211':y8%511%311p051'8'>'3&NvRFr4r3r2%544321(;%93821&E%1256&A&Q1r6&QF&QN&RNr5%22K1&R5%11@%6231%811%;3E:1(0%11N%K3N31%@11p0B1p0E1pU4Q01pU6Q11pTDQ81pU:Q41").
Proof.
intros m a j. revert a. induction j as [|j IH]; intros a i Hs Hi; [lia|].
cbn [store_ok] in Hs. destruct (wview segs m a) eqn:E; [|discriminate].
destruct i as [|i].
- replace (wa (bv_unsigned a + Z.of_nat 0)) with a. { rewrite E. discriminate. }
unfold wa. apply bv_eq. rewrite Z_to_bv_unsigned. cbn [Z.of_nat]. rewrite Z.add_0_r, bv_wrap_small; [reflexivity|apply bv_unsigned_in_range].
- specialize (IH (a + 1) i Hs ltac:(lia)).
replace (wa (bv_unsigned a + Z.of_nat (S i))) with (wa (bv_unsigned (a + 1) + Z.of_nat i)); [exact IH|].
unfold wa. apply bv_eq. rewrite !Z_to_bv_unsigned, bv_add_unsigned. change (bv_unsigned (1:word)) with 1%Z.
unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.
Lemma wview_not_ro : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "O'RIyR0%211':y8%511%311p051&A'>&Q1vRFr2r1%43321(0%11;%83;31%:11r3%118%<3?15'3&Q9%115(5%A3421p061p0:1pTDK1pU:G1").
Proof.
intros m a H Hm. unfold wview, ro_addr in *. rewrite Hm in H.
destruct (find_segment segs (bv_unsigned a) 1) as [seg|]; [|reflexivity].
destruct (seg_writable seg); [reflexivity|]. exfalso; apply H; reflexivity.
Qed.
Lemma mem_inv_store : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "Q1'RIyR0%211':y8%511%311p051'7%114&Q7r3%211'>'3&NvRFr4&6r2%22?1%6454:1(;%:3921&Q0r5%2319?%A11p051p0A1pTHE1pTDM1pU:I1").
Proof.
intros m a bs Hinv Hok x b Hx.
destruct (write_to_mem_some _ _ _ _ _ Hx) as [H | (i & Hi & ->)].
- exact (Hinv _ _ H).
- pose proof (store_ok_wview _ _ _ _ Hok Hi) as W.
destruct (m (wa (bv_unsigned a + Z.of_nat i))) eqn:E.
+ exact (Hinv _ _ E).
+ exact (wview_not_ro _ _ W E).
Qed.
Definition ro_byte (a : Z) (b : byte) : Prop :=
seg_rom segs (wa a) = Some b /\ ro_addr (wa a) = true.
Lemma mem_inv_ro_read : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "N'RIyR0%211':y8%511%311p051'I&Q7r3%211&Q:r2%2241'>&Q8r5&QFr4%211%5241(1%12B=%93B31p0;1p0?1pTFF1pTDD1pU:F1").
Proof.
intros m a b Hinv [Hro Hnw]. unfold mrd. destruct (m (wa a)) eqn:E.
- exfalso. pose proof (Hinv _ _ E). congruence.
- exact Hro.
Qed.
Fixpoint ro_bytes (a : Z) (bs : list byte) : Prop :=
match bs with
| [] => True
| b :: bs' => ro_byte a b /\ ro_bytes (a + 1) bs'
end.
Lemma ro_bytes_nth : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "Q1'7'RIy8%211%411'I'8&Q;r3r4%3221'>':%11:&QLr5%23=18(1r2%22@1%93741&Q:&QN&R5%11?%32:1%521Bp071p0B1pTFJ1pU4H1pTDJ1pTHL1").
Proof.
induction bs as [|x bs IH]; intros a i b H Hn; [destruct i; discriminate|].
destruct H as [H1 H2]. destruct i as [|i]; cbn in Hn.
- inversion Hn; subst. rewrite Z.add_0_r. exact H1.
- replace (a + Z.of_nat (S i))%Z with (a + 1 + Z.of_nat i)%Z by lia. apply IH; assumption.
Qed.
Lemma ro_bytes_at : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "Q;'RIyR0%211':y8%511%311p051'I'7%115&Q7r3%211&R0z%2214&QNr4&R5&6%12@9%311%6251&R6+2+R0%3221%>251&Q;r5%221=&Q6r7r6%33215p051p091p0F1p0J1pTHN1pTDQ11pU:Q31").
Proof.
intros m a bs Hinv Ha Hl H. split; [lia|]. split; [lia|].
intros i Hi. destruct (nth_error bs i) eqn:E. 2:{ apply nth_error_None in E; lia. }
apply mem_inv_ro_read; [assumption|]. eapply ro_bytes_nth; eassumption.
Qed.
Section SE.
Local Abbreviation SEC_T_bytes_at_app := (ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "Q3'RIyR0%211':y8%511%311p051'I'7%115&@&Q6r4r3&2r2r1%33=21%73651'=%93875&QN&R5&6%12D9%311%52=1%@3?1;%9281%C2;1pTNE1pTLF1pTDI1pU:K1")) (only parsing).
Variable m : ltac:(sec_ty2 constr:(SEC_T_bytes_at_app) 0%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_bytes_at_app) 1%nat 0%nat).
Variable bs1 : ltac:(sec_ty2 constr:(SEC_T_bytes_at_app) 2%nat 0%nat).
Variable bs2 : ltac:(sec_ty2 constr:(SEC_T_bytes_at_app) 3%nat 0%nat).
Lemma bytes_at_app : ltac:(sec_stmt2 constr:(SEC_T_bytes_at_app) 4%nat 0%nat).
Proof.
unfold bytes_at. rewrite app_length. split.
- intros (Ha & Hl & H). repeat split; try lia.
+ intros i Hi. rewrite (H i) by lia. rewrite nth_error_app1 by lia. reflexivity.
+ intros i Hi. replace (a + Z.of_nat (length bs1) + Z.of_nat i)%Z with (a + Z.of_nat (length bs1 + i))%Z by lia.
rewrite (H (length bs1 + i)%nat) by lia. rewrite nth_error_app2 by lia. f_equal. lia.
- intros ((Ha & Hl1 & H1) & (Ha2 & Hl2 & H2)). repeat split; try lia.
intros i Hi. destruct (Nat.ltb_spec0 i (length bs1)).
+ rewrite nth_error_app1 by lia. apply H1. lia.
+ rewrite nth_error_app2 by lia. rewrite <- (H2 (i - length bs1)%nat) by lia. f_equal. f_equal. lia.
Qed.
End SE.
Lemma bytes_at_nil : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "M'RIyR0%211':y8%511%311p051'I'=&R0zr1%3221&R6+2+R0%3221%8261%:261&Q6r3r2(9%11C%53431p071pTDC1pU:E1").
Proof. intros. split; [lia|]. split; [cbn; lia|]. intros i Hi; cbn in Hi; lia. Qed.
Lemma bytes_at_bound : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "Q4'RIyR0%211':y8%511%311p051'I'7%115&Q6r3r2r1%43321'=&R0z%2217&QN&R5&6%12B:%311%52=1&R6+2+R0%3221%=251%?2<1p0A1pTHG1pTDJ1pU:L1").
Proof. intros m a bs (Ha & Hl & _). lia. Qed.
Lemma bytes_at_ext : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "K'RIyR0%211':y8%511%311p051'I'7%115&Q6r4r3r2%43321'>%13743r6r5%93217p041p071pTJ=1pTH>1pTDA1pU:C1").
Proof. intros; subst; assumption. Qed.
End WithSegs.
Definition le8 (v : word) : list byte := word_to_le_bytes 8 v.
Definition le4 (v : word) : list byte := Z_to_le_bytes 4 (bv_unsigned v).
Definition le2 (v : word) : list byte := Z_to_le_bytes 2 (bv_unsigned v).
Definition le1 (v : word) : list byte := Z_to_le_bytes 1 (bv_unsigned v).
Lemma length_Z_to_le_bytes : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "?'8'I'>&6'RIy8%211&Jr2r1%3221%8251%:3<14pV8<1pU<>1").
Proof. induction n; intros; cbn; [reflexivity| now rewrite IHn]. Qed.
Lemma length_le8 : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "?'RIyR0%211'>'8&6y8%711&QAr1%211%6241u8%:3921pV0<1"). Proof. intros; apply length_Z_to_le_bytes. Qed.
Lemma length_le4 : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "?'RIyR0%211'>'8&6y8%711&Q@r1%211%6241u4%:3921pV0<1"). Proof. intros; apply length_Z_to_le_bytes. Qed.
Lemma length_le2 : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "?'RIyR0%211'>'8&6y8%711&Q?r1%211%6241u2%:3921pV0<1"). Proof. intros; apply length_Z_to_le_bytes. Qed.
Lemma length_le1 : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "?'RIyR0%211'>'8&6y8%711&Q>r1%211%6241u1%:3921pV0<1"). Proof. intros; apply length_Z_to_le_bytes. Qed.
Lemma bytes_le_to_Z_to_le_bytes : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "K'8'I&R0zr1%3221'>&K&Jr3r2%3221%511&R2&R6+2&R3+8&R5%11:%4231%7261%92<1%A3F;1p0C1pV8H1pU<J1").
Proof.
induction n as [|n IH]; intros z Hz.
- cbn. rewrite Z.mod_1_r. reflexivity.
- cbn [Z_to_le_bytes bytes_le_to_Z]. rewrite IH by (apply Z.shiftr_nonneg; lia).
rewrite Z_to_bv_unsigned. change (bv_wrap 8 z) with (z mod 2^8)%Z.
set (w := (8 * Z.of_nat (S n))%Z). set (w' := (8 * Z.of_nat n)%Z).
assert (Hw : (w = w' + 8)%Z) by lia. assert (Hw' : (0 <= w')%Z) by lia.
apply Z.bits_inj'. intros k Hk.
rewrite Z.lor_spec, Z.shiftl_spec by lia.
rewrite <- !Z.land_ones by lia. rewrite !Z.land_spec.
destruct (Z.ltb_spec0 k 8).
+ rewrite (Z.testbit_neg_r _ (k - 8)) by lia. rewrite (Z.ones_spec_low 8) by lia.
rewrite (Z.ones_spec_low w) by lia. rewrite orb_false_r. reflexivity.
+ rewrite (Z.ones_spec_high 8) by lia. rewrite andb_false_r. rewrite orb_false_l.
rewrite Z.shiftr_spec by lia. replace (k - 8 + 8)%Z with k by lia.
destruct (Z.ltb_spec0 k w).
* rewrite !Z.ones_spec_low by lia. reflexivity.
* rewrite !Z.ones_spec_high by lia. reflexivity.
Qed.
Lemma le_bytes_to_word_le8 : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem ";'RIyR0%211'>&L&QAr1%211%411%63713pV081").
Proof.
intros v. unfold le_bytes_to_word, le8, word_to_le_bytes.
rewrite bytes_le_to_Z_to_le_bytes by (apply bv_unsigned_in_range).
apply bv_eq. rewrite Z_to_bv_unsigned. change (8 * Z.of_nat 8)%Z with 64%Z.
pose proof (bv_unsigned_in_range 64 v) as Hr. unfold bv_modulus in Hr.
rewrite Z.mod_small by lia. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.
Lemma bytes_le_to_Z_le4 : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "D'RIyR0%211'>'I&K&Q@r1%211%411&R2&RN%12;5&R6+2+Q0%3221%7251%?3>91pV0A1").
Proof. intros. unfold le4. rewrite bytes_le_to_Z_to_le_bytes by apply bv_unsigned_in_range. reflexivity. Qed.
Lemma bytes_le_to_Z_le2 : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "D'RIyR0%211'>'I&K&Q?r1%211%411&R2&RN%12;5&R6+2+@%3221%7251%?3>91pV0A1").
Proof. intros. unfold le2. rewrite bytes_le_to_Z_to_le_bytes by apply bv_unsigned_in_range. reflexivity. Qed.
Lemma bytes_le_to_Z_le1 : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "D'RIyR0%211'>'I&K&Q>r1%211%411&R2&RN%12;5&R6+2+8%3221%7251%?3>91pV0A1").
Proof. intros. unfold le1. rewrite bytes_le_to_Z_to_le_bytes by apply bv_unsigned_in_range. reflexivity. Qed.
Lemma Z_to_bv8_mod : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "G'I'>&R2r2&R6+2+8%3221%6251r1%8213%:3;31'RIy8%211&RHr3%2241%325?%B3521p091pV6E1pV4F1").
Proof. intros. apply bv_eq. rewrite !Z_to_bv_unsigned. change (bv_wrap 8 ?a) with (a mod 2^8)%Z. exact H. Qed.
Lemma shiftr_mod_mod8 : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "N'I&R0zr2%3221&QNr3+8%3221%8216'>&R2&R7r5&R6+2%221:%6241r4%7221%625=%:221%:294%<213%>3H31p0@1p0F1pV2K1pU8L1pV8M1").
Proof.
intros z k w Hk Hw. apply Z.bits_inj'. intros i Hi.
rewrite <- !Z.land_ones by lia. rewrite !Z.land_spec, !Z.shiftr_spec by lia.
rewrite Z.land_spec.
destruct (Z.ltb_spec0 i 8).
- rewrite !Z.ones_spec_low by lia. rewrite !andb_true_r. reflexivity.
- rewrite (Z.ones_spec_high 8) by lia. rewrite !andb_false_r. reflexivity.
Qed.
Lemma mod_mod8_of_modw : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "D'I&R0+8r1%3221'>&R2r3&R6+2r2%3221%6251%524;%8221%9282%;3@21p0=1pV2B1pV8C1").
Proof.
intros z w Hw. pose proof (shiftr_mod_mod8 z 0 w ltac:(lia) ltac:(lia)) as H.
rewrite !Z.shiftr_0_r in H. exact H.
Qed.
Lemma Z_to_le_bytes_mod : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "Q0'8'I&R0&R3+8&R5r3%211%5241r1%8221'>'7'RIy8%211%411&Jr4&R2&R6+2r2%3221%52B1%8271%928D%@3;21p0B1pV2L1pV8M1pU<O1").
Proof.
induction n as [|n IH]; intros z w Hw; [reflexivity|].
cbn [Z_to_le_bytes]. f_equal.
- apply Z_to_bv8_mod. apply mod_mod8_of_modw. lia.
- rewrite !Z.shiftr_div_pow2 by lia.
replace w with (8 + (w - 8))%Z at 1 by lia. rewrite Z.pow_add_r by lia.
rewrite Z.rem_mul_r by lia.
rewrite <- (IH (z / 2^8)%Z (w - 8)%Z) by lia. f_equal.
rewrite Z.mul_comm, Z.div_add by lia. rewrite (Z.div_small (z mod 2^8)) by (apply Z.mod_pos_bound; lia).
rewrite Z.add_0_l. reflexivity.
Qed.
Lemma store_bytes_8 : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "C'RIyR0%211'>'7y8%611%311&J&O%119&RNr1%22<1%6241&QA%114%>3:31pV0@1").
Proof. reflexivity. Qed.
Lemma store_bytes_4 : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "F'RIyR0%211'>'7y8%611%311&J&OyQ0%211&RN&Q5r1%211%4261%9261&Q@%115%A3=31pV0C1").
Proof.
intros. unfold le4, low32. cbn [width_bytes]. rewrite bv_extract_unsigned, Z.shiftr_0_r.
change (bv_wrap 32 ?x) with (x mod 2^32)%Z. apply Z_to_le_bytes_mod. cbn; lia.
Qed.
Lemma store_bytes_2 : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "G'RIyR0%211'>'7y8%611%311&J&Oy@%211&RN&RKwr1%34?261%5271%:271&Q?%115%B3>31pV0D1").
Proof.
intros. unfold le2. cbn [width_bytes]. rewrite bv_extract_unsigned, Z.shiftr_0_r.
change (bv_wrap 16 ?x) with (x mod 2^16)%Z. apply Z_to_le_bytes_mod. cbn; lia.
Qed.
Lemma store_bytes_1 : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "F'RIyR0%211'>'7y8%611%311&J&O%115&RN&RKwr1%34>2:1%52;1%9271&Q>%115%A3=31pV0C1").
Proof.
intros. unfold le1. cbn [width_bytes]. rewrite bv_extract_unsigned, Z.shiftr_0_r.
change (bv_wrap 8 ?x) with (x mod 2^8)%Z. apply Z_to_le_bytes_mod. cbn; lia.
Qed.
Definition zx32 (v : word) : word := Z_to_bv 64 (bv_unsigned v mod 2^32).
Definition sx32 (v : word) : word := Z_to_bv 64 (bv_swrap 32 (bv_unsigned v)).
Definition zx16 (v : word) : word := Z_to_bv 64 (bv_unsigned v mod 2^16).
Definition sx16 (v : word) : word := Z_to_bv 64 (bv_swrap 16 (bv_unsigned v)).
Definition zx8 (v : word) : word := Z_to_bv 64 (bv_unsigned v mod 2^8).
Definition sx8 (v : word) : word := Z_to_bv 64 (bv_swrap 8 (bv_unsigned v)).
Definition zxb (b : byte) : word := Z_to_bv 64 (bv_unsigned b).
Definition sxb (b : byte) : word := Z_to_bv 64 (bv_signed b).
Lemma zext_small : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "A'H'RIr1%211'>yR0%511&Q4r2%23147&RH&RN%124:%3281%:3851pTF<1pU<@1").
Proof. intros. reflexivity. Qed.
Lemma sext_small : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "A'H'RIr1%211'>yR0%511&Q3r2%23147&RH&RL%124:%3281%:3851pTF<1pU<@1").
Proof. intros. reflexivity. Qed.
Lemma extract_low_mod : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "K'H'RIyR0%211&QMwr2%3221'>'I&RNr3&RK%14;827%4231&R2%62>:&R6+2&R4%119%4231%7261%?3>91p0A1pV2F1pU<J1").
Proof. intros. rewrite bv_extract_unsigned, Z.shiftr_0_r. reflexivity. Qed.
Lemma signed_of_extract : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "G'H'RIyR0%211&QMwr2%3221'>'I&RLr3&RK%14;827%4231&RM&RN%12?;%3271%;3:51p0=1pV2B1pU<F1").
Proof.
intros. unfold bv_signed. rewrite extract_low_mod by assumption. unfold bv_swrap.
f_equal. unfold bv_wrap, bv_modulus. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma le_bytes_to_word_le4 : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "E'RIyR0%211'>'I&RN&L&Q@r1%211%411%62:1&R2%82<5&R6+2+Q0%3221%6251%@3?81pV0B1").
Proof.
intros. unfold le_bytes_to_word. rewrite Z_to_bv_unsigned, bytes_le_to_Z_le4.
apply bv_wrap_small. unfold bv_modulus. pose proof (Z.mod_pos_bound (bv_unsigned v) (2^32)). lia.
Qed.
Lemma le_bytes_to_word_le2 : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "E'RIyR0%211'>'I&RN&L&Q?r1%211%411%62:1&R2%82<5&R6+2+@%3221%6251%@3?81pV0B1").
Proof.
intros. unfold le_bytes_to_word. rewrite Z_to_bv_unsigned, bytes_le_to_Z_le2.
apply bv_wrap_small. unfold bv_modulus. pose proof (Z.mod_pos_bound (bv_unsigned v) (2^16)). lia.
Qed.
Lemma le_bytes_to_word_le1 : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "E'RIyR0%211'>'I&RN&L&Q>r1%211%411%62:1&R2%82<5&R6+2+8%3221%6251%@3?81pV0B1").
Proof.
intros. unfold le_bytes_to_word. rewrite Z_to_bv_unsigned, bytes_le_to_Z_le1.
apply bv_wrap_small. unfold bv_modulus. pose proof (Z.mod_pos_bound (bv_unsigned v) (2^8)). lia.
Qed.
Lemma le_bytes_to_word_byte : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "B'RIy8%211'>'I&RNyR0&L(4r1(9%119%43:31%611%9281%:2>6%=3<21pTF?1").
Proof.
intros. unfold le_bytes_to_word. cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r, Z_to_bv_unsigned.
apply bv_wrap_small. pose proof (bv_unsigned_in_range 8 b). unfold bv_modulus in *. lia.
Qed.
Lemma load_u64 : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem ">'RIyR0%211'>&RKw&L&QAr1%211%411%74:6:1%93:14pV0;1").
Proof.
intros. rewrite le_bytes_to_word_le8. apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r.
apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.
Lemma zext_extract_le4 : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "C'RIyR0%211'>&Q4yQ0&RKw&L&Q@r1%211%411%74<681%:39=1&QH%116%>3?31pV0@1").
Proof.
intros. rewrite zext_small. unfold zx32. f_equal. rewrite extract_low_mod by lia. rewrite le_bytes_to_word_le4.
change (Z.of_N 32) with 32%Z. apply Z.mod_mod. lia.
Qed.
Lemma zext_extract_le2 : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "C'RIyR0%211'>&Q4y@&RKw&L&Q?r1%211%411%74<681%:39=1&QG%116%>3?31pV0@1").
Proof.
intros. rewrite zext_small. unfold zx16. f_equal. rewrite extract_low_mod by lia. rewrite le_bytes_to_word_le2.
change (Z.of_N 16) with 16%Z. apply Z.mod_mod. lia.
Qed.
Lemma zext_extract_le1 : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "C'RIyR0%211'>&Q4y8&RKw&L&Q>r1%211%411%74<681%:39=1&QI%116%>3?31pV0@1").
Proof.
intros. rewrite zext_small. unfold zx8. f_equal. rewrite extract_low_mod by lia. rewrite le_bytes_to_word_le1.
change (Z.of_N 8) with 8%Z. apply Z.mod_mod. lia.
Qed.
Lemma sext_extract_le4 : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "C'RIyR0%211'>&Q3yQ0&RKw&L&Q@r1%211%411%74<681%:39=1&QC%116%>3?31pV0@1").
Proof.
intros. rewrite sext_small. unfold sx32. f_equal. rewrite signed_of_extract by lia. rewrite le_bytes_to_word_le4.
unfold bv_swrap. f_equal. unfold bv_wrap, bv_modulus. change (Z.of_N 32) with 32%Z. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma sext_extract_le2 : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "C'RIyR0%211'>&Q3y@&RKw&L&Q?r1%211%411%74<681%:39=1&QB%116%>3?31pV0@1").
Proof.
intros. rewrite sext_small. unfold sx16. f_equal. rewrite signed_of_extract by lia. rewrite le_bytes_to_word_le2.
unfold bv_swrap. f_equal. unfold bv_wrap, bv_modulus. change (Z.of_N 16) with 16%Z. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma sext_extract_le1 : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "C'RIyR0%211'>&Q3y8&RKw&L&Q>r1%211%411%74<681%:39=1&QD%116%>3?31pV0@1").
Proof.
intros. rewrite sext_small. unfold sx8. f_equal. rewrite signed_of_extract by lia. rewrite le_bytes_to_word_le1.
unfold bv_swrap. f_equal. unfold bv_wrap, bv_modulus. change (Z.of_N 8) with 8%Z. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma zext_extract_byte : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "F'RIy8%211'>yR0%511&Q4&RKw&L(4r1(9%11;%43<31%611%94<8?1%;3@=1&QJ%118%A3?31pTFC1").
Proof.
intros. rewrite zext_small. unfold zxb. f_equal. rewrite extract_low_mod by lia. rewrite le_bytes_to_word_byte.
apply Z.mod_small. pose proof (bv_unsigned_in_range 8 b). unfold bv_modulus in *. change (Z.of_N 8) with 8%Z in *. lia.
Qed.
Lemma sext_extract_byte : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "F'RIy8%211'>yR0%511&Q3&RKw&L(4r1(9%11;%43<31%611%94<8?1%;3@=1&QE%118%A3?31pTFC1").
Proof.
intros. rewrite sext_small. unfold sxb. f_equal. rewrite signed_of_extract by lia. rewrite le_bytes_to_word_byte.
reflexivity.
Qed.
Lemma le1_zxb : ltac2:(TCodec.tc2 tcn__CJ_Lib_Mem "A'RIy8%211'>'7%113&Q>&QJr1%211%411(4(9%11;%33<61%<3:51pTF>1").
Proof.
intros. unfold le1, zxb. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
pose proof (bv_unsigned_in_range 8 b). unfold bv_modulus in H.
rewrite !Z_to_bv_unsigned, (bv_wrap_small 64) by (unfold bv_modulus; lia).
apply bv_wrap_small. unfold bv_modulus; lia.
Qed.
