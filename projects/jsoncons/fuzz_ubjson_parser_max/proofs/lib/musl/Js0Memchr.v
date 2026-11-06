(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim MuslStrlen RefMemcpyLib Js0MemcpyBase.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__musl_Js0Memchr () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MuslStrlen.HZ."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.musl.Js0Memchr.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.musl.Js0Memchr.FPX_1.MCHR."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1andb"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nat"; "1negb"; "1nil"; "1option"; "1true"; "2I"; "2and"; "2eq"; "2ex"]; ["2not"; "3add"; "4le"; "4lt"; "5nth"; "6Z"; "0K"; "7bytes_le_to_Z"; "8bvmap"; "9msteps"; ":at_"; ":ret_ok"; ";Tz"; "<c_eq"; "<getr"; "<mkst"]; ["<rdn"; "<v_andi"; "<v_xor"; "=LBv"; "=keeps_cs"; "=sub"; ">Hc"; ">LDv"; "?KE"; "?b_"; "?sb_"; ">Mc"; ">TW"; ">mchrH"; ">rodata_clear"; "@loaded_segments"]; ["Aadd"; "Adiv"; "Aeqb"; "Ale"; "Alt"; "Amodulo"; "Aof_nat"; "Apow"; "Asub"; "Atestbit"; "0b"; "0bs"; "0buf"; "0d"; "0fx"; "0i"]; ["0j"; "0l"; "0m"; "0mem"; "0n"; "0regs"; "0regs'"; "0ret"; "0rom"; "0s"; "BBV"; "BZ_to_bv"; "Bbv"; "Bbv_unsigned"; "0x"; "0y"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.
Definition Mc : Z := 0x0101010101010100.
Definition Hc : Z := 0x8080808080808080.
Definition LDv (l : list byte) : word := Z_to_bv 64 (bytes_le_to_Z l).
Lemma u_LDv : ltac2:(TCodec.tc2 tcn__musl_Js0Memchr "H'6'R<y8%211%411'>'7&5r1%2261u8%63521'E&R=yR0&Q7r2%211%5241&G%114%@3931p0;1pT4C1").
Proof. intros l H. unfold LDv. pose proof (bytes_le_to_Z_range l H). apply u_Z2bv; lia. Qed.
Definition TW (x : word) : word :=
v_and (v_or (v_sub (Z_to_bv 64 Mc) (v_xor x (Z_to_bv 64 0))) (v_xor x (Z_to_bv 64 0))) (Z_to_bv 64 Hc).
Lemma v_xor_0 : ltac2:(TCodec.tc2 tcn__musl_Js0Memchr "<'R<yR0%211'>&Q2r1&R;z%2271%5241%73815pTN91").
Proof.
intros x. unfold v_xor. rewrite (u_Z2bv 0) by lia. rewrite Z.lxor_0_r. apply Z_to_bv_bv_unsigned.
Qed.
Section SE.
Variables (x : word).
Lemma TW_bits : let y := bv_unsigned x in
(forall i, (0 <= i)%Z ->
Z.testbit (bv_unsigned (TW x)) i = (Z.testbit Hc i && negb (Z.testbit (HZ.Tz y) i))%bool)
/\ (forall i, (0 <= i)%Z -> Z.testbit (HZ.Tz y) i = true -> Z.testbit Hc i = true).
Proof.
intros y.
pose proof (u64_range x) as Hx. subst y.
assert (A64 : (0 <= (bv_unsigned x + HZ.ONESNEG) mod 2 ^ 64 < 2 ^ 64)%Z) by (apply Z.mod_pos_bound; lia).
set (A := ((bv_unsigned x + HZ.ONESNEG) mod 2 ^ 64)%Z) in *.
assert (SUB : ((Mc - bv_unsigned x) mod 2 ^ 64 = 2 ^ 64 - 1 - A)%Z).
{ subst A. unfold Mc, HZ.ONESNEG.
rewrite <- (Z.mod_add _ 1) by lia.
replace (72340172838076672 - bv_unsigned x + 1 * 2 ^ 64)%Z
with (2 ^ 64 - 1 - (bv_unsigned x + 18374403900871474943) + 1 * 2 ^ 64)%Z by lia.
set (z := (bv_unsigned x + 18374403900871474943)%Z).
rewrite Zminus_mod_idemp_r || idtac.
pose proof (Z.div_mod z (2^64) ltac:(lia)). pose proof (Z.mod_pos_bound z (2^64) ltac:(lia)).
set (q := (z / 2 ^ 64)%Z) in *. set (r := (z mod 2 ^ 64)%Z) in *.
replace (2 ^ 64 - 1 - z + 1 * 2 ^ 64)%Z with ((2 ^ 64 - 1 - r) + (1 - q) * 2 ^ 64)%Z by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
assert (NOTA : forall i, (0 <= i < 64)%Z -> Z.testbit (2 ^ 64 - 1 - A) i = negb (Z.testbit A i)).
{ intros i Hi. replace (2 ^ 64 - 1 - A)%Z with ((Z.lnot A) mod 2 ^ 64)%Z.
- rewrite Z.mod_pow2_bits_low by lia. apply Z.lnot_spec. lia.
- unfold Z.lnot. replace (Z.pred (- A)) with ((2 ^ 64 - 1 - A) + (-1) * 2 ^ 64)%Z by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
assert (TWu : bv_unsigned (TW x) = Z.land (Z.lor ((Mc - bv_unsigned x) mod 2 ^ 64) (bv_unsigned x)) Hc).
{ unfold TW. rewrite !v_xor_0. unfold v_and, v_or, v_sub.
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
rewrite (Z.mod_small Mc) by (unfold Mc; lia). rewrite (Z.mod_small Hc) by (unfold Hc; lia).
assert (R1 : (0 <= (Mc - bv_unsigned x) mod 2 ^ 64 < 2 ^ 64)%Z) by (apply Z.mod_pos_bound; lia).
assert (R2 : (0 <= Z.lor ((Mc - bv_unsigned x) mod 2 ^ 64) (bv_unsigned x) < 2 ^ 64)%Z) by (apply Z_lor_range; lia).
rewrite (Z.mod_small (Z.lor _ _)) by exact R2.
apply Z.mod_small. apply Z_land_range; [exact R2 | unfold Hc; lia]. }
split.
- intros i Hi. rewrite TWu, SUB.
unfold HZ.Tz. fold A.
rewrite Z.land_spec. rewrite Z.lor_spec. rewrite Z.land_spec. rewrite Z.land_spec. rewrite Z.lxor_spec.
change HZ.HIGHS with Hc.
destruct (Z.lt_ge_cases i 64) as [Hl|Hh].
+ rewrite NOTA by lia.
replace (Z.testbit HZ.ALLONES i) with true.
2:{ symmetry. unfold HZ.ALLONES. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.ones_spec_low; [reflexivity|lia]. }
destruct (Z.testbit A i), (Z.testbit (bv_unsigned x) i), (Z.testbit Hc i); reflexivity.
+ replace (Z.testbit Hc i) with false.
2:{ symmetry. apply (Z_testbit_high 64); unfold Hc; lia. }
rewrite andb_false_r. reflexivity.
- intros i Hi H. unfold HZ.Tz in H. rewrite Z.land_spec in H. rewrite Z.land_spec in H.
change HZ.HIGHS with Hc in H.
destruct (Z.testbit Hc i); [reflexivity|]. rewrite andb_false_r in H. discriminate H.
Qed.
End SE.
Lemma TW_eq_H : ltac2:(TCodec.tc2 tcn__musl_Js0Memchr "F'R<yR0%211'>'2&M&Q<r1%211&R;&Q6%22:1%7241&QB&L&R=%12?9%311z%6221%A3@81pTNC1").
Proof.
intros x. destruct (TW_bits x) as [B1 B2].
unfold c_eq, bv_eqb. rewrite (u_Z2bv Hc) by (unfold Hc; lia).
pose proof (HZ.Tz_range (bv_unsigned x)) as TR.
destruct (Z.eqb_spec (HZ.Tz (bv_unsigned x)) 0) as [Z0|NZ].
- apply Z.eqb_eq. apply Z.bits_inj'. intros i Hi. rewrite B1 by lia. rewrite Z0, Z.bits_0.
rewrite andb_true_r. reflexivity.
- apply Z.eqb_neq. intros E.
apply NZ. apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0.
destruct (Z.testbit (HZ.Tz (bv_unsigned x)) i) eqn:T; [|reflexivity].
pose proof (B2 i Hi T) as HH.
pose proof (B1 i Hi) as BB. rewrite E, HH, T in BB. discriminate BB.
Qed.
Lemma TW_nozero : ltac2:(TCodec.tc2 tcn__musl_Js0Memchr "Q='6'R<y8%211%411'>'7&5r1%2261u8%63521&C%1253&@'E&R=&Dr2r4&R;z%22D1%64D541%82F1%D3:14%<11p0>1pT0F1'2&M&Q<&Q7r3%211%411yR0&Q6%B221%9241(;%Q43<21p0>1p0Q01pT4Q81").
Proof.
intros l Hl Hnz. rewrite TW_eq_H. apply Z.eqb_eq.
rewrite u_LDv by exact Hl. apply HZ.Tz_nozero.
- apply bytes_le_to_Z_range. exact Hl.
- intros i Hi. rewrite zb_of_bytes by (rewrite Hl; exact Hi). apply Hnz. exact Hi.
Qed.
Lemma TW_haszero : ltac2:(TCodec.tc2 tcn__musl_Js0Memchr "QG'6'R<y8%211%411'7'>&5r2%2261u8%53621&C%1253'E&R=&Dr3r4&R;z%22C1%64C541%82E1%B3:14r1r5%?221&@r7%>4KF19%@2M1%J3B1<%511p071pT2N1'2&M&Q<&Q7r6%211%411yR0&Q6%J221%9241(4%Q:3<21p0>1p0J1p0Q61p0Q91pT0Q@1pT4QB1").
Proof.
intros l i Hl Hi Hz Hnz. rewrite TW_eq_H. apply Z.eqb_neq.
rewrite u_LDv by exact Hl. apply (HZ.Tz_haszero _ i).
- apply bytes_le_to_Z_range. exact Hl.
- exact Hi.
- rewrite zb_of_bytes by (rewrite Hl; exact Hi). exact Hz.
- intros j Hj. rewrite zb_of_bytes by (rewrite Hl; lia). apply Hnz. exact Hj.
Qed.
Definition rodata_clear (mem : word -> option byte) : Prop :=
forall i, (0x13a98 <= i < 0x13ab0)%Z -> mem (Z_to_bv 64 i) = None.
Lemma rd_const_M : ltac2:(TCodec.tc2 tcn__musl_Js0Memchr "Q9'R<yR0%211':y8%511%311p051&Q>r1%211'?'6%118'='>%=13&Q0&Q?r3&R;+R^e8%22E1u8%746521(0%12=A%<3;31'E&G%11E&R=&Q;%=2Q01%32Q11%D3751%F291qSHH1%K2I1p0M1pT8Q11").
Proof.
intros mem Hr.
rewrite (rdn_ext RSEGS 8 mem (fun _ => None)).
- eexists. split; [vm_compute; reflexivity|]. vm_compute. reflexivity.
- change (bv_unsigned (Z_to_bv 64 80552)) with 80552%Z. cbn. lia.
- intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hr.
change (bv_unsigned (Z_to_bv 64 80552)) with 80552%Z in Hx. cbn in Hx. lia.
Qed.
Lemma rd_const_H : ltac2:(TCodec.tc2 tcn__musl_Js0Memchr "Q9'R<yR0%211':y8%511%311p051&Q>r1%211'?'6%118'='>%=13&Q0&Q?r3&R;+R^dH%22E1u8%746521(0%12=A%<3;31'E&G%11E&R=&Q6%=2Q01%32Q11%D3751%F291qSHH1%K2I1p0M1pT8Q11").
Proof.
intros mem Hr.
rewrite (rdn_ext RSEGS 8 mem (fun _ => None)).
- eexists. split; [vm_compute; reflexivity|]. vm_compute. reflexivity.
- change (bv_unsigned (Z_to_bv 64 80536)) with 80536%Z. cbn. lia.
- intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hr.
change (bv_unsigned (Z_to_bv 64 80536)) with 80536%Z in Hx. cbn in Hx. lia.
Qed.
Lemma nth_sub : ltac2:(TCodec.tc2 tcn__musl_Js0Memchr "Q3'6'R<y8%211%411'7&Cr2r3%3221'B&Ar5r4%3221&5r6%22>1%8241'>&D&Q5r7%24D17;%44E;1@%>29<%64G14B%83H31p0:1p0D1pSLK1pT0J1pT6K1pT2L1pSHN1").
Proof.
intros bs j m i d Hi Hjm. unfold sub.
rewrite nth_firstn. replace (i <? m)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi).
rewrite nth_skipn. reflexivity.
Qed.
Lemma c_eq_LBv_0 : ltac2:(TCodec.tc2 tcn__musl_Js0Memchr "D'R<y8%211'>'2&M&Q3r1%211&R;yR0z%3221%8251&QB&R=%12?9%3216%?3>51pSFA1").
Proof.
intros b. unfold c_eq, bv_eqb, LBv. pose proof (bv_unsigned_in_range _ b) as R.
change (bv_modulus 8) with 256%Z in R.
rewrite (u_Z2bv (bv_unsigned b)) by lia. rewrite (u_Z2bv 0) by lia. reflexivity.
Qed.
Record mchrH (mem : word -> option byte) (s : word) (buf : list byte) (K n : Z) : Prop := MCHRH {
Hbuf : rdn RSEGS mem s (length buf) = Some buf;
Hwin : ((bv_unsigned s + K) / 8 * 8 + 8 <= bv_unsigned s + Z.of_nat (length buf))%Z;
Hnw : (bv_unsigned s + Z.of_nat (length buf) < 2 ^ 64)%Z;
HK0 : (0 <= K)%Z;
Hzero : bv_unsigned (nth (Z.to_nat K) buf (Z_to_bv 8 0)) = 0%Z;
Hnz : forall j, (j < Z.to_nat K)%nat -> bv_unsigned (nth j buf (Z_to_bv 8 0)) <> 0%Z;
HKn : (K + 8 <= n)%Z;
Hn64 : (n < 2 ^ 64)%Z;
Hro : rodata_clear mem }.
Section MCHR.
Variable mem : word -> option byte.
Variable s : word.
Variable buf : list byte.
Variables K n : Z.
Variable rom : word -> option byte.
Hypothesis HOK : mchrH mem s buf K n.
#[local] Notation L := (Z.of_nat (length buf)).
Definition b_ (j : Z) : byte := nth (Z.to_nat j) buf (Z_to_bv 8 0).
Definition sb_ (j : Z) (m : nat) : list byte := sub buf (Z.to_nat j) m.
Let Hbuf := Hbuf _ _ _ _ _ HOK.
Let Hwin : ((bv_unsigned s + K) / 8 * 8 + 8 <= bv_unsigned s + L)%Z := Hwin _ _ _ _ _ HOK.
Let Hnw : (bv_unsigned s + L < 2 ^ 64)%Z := Hnw _ _ _ _ _ HOK.
Let HK0 : (0 <= K)%Z := HK0 _ _ _ _ _ HOK.
Let HKn : (K + 8 <= n)%Z := HKn _ _ _ _ _ HOK.
Let Hn64 : (n < 2 ^ 64)%Z := Hn64 _ _ _ _ _ HOK.
Let Hro := Hro _ _ _ _ _ HOK.
Lemma KL : ltac2:(TCodec.tc2 tcn__musl_Js0Memchr ">&QC&Q@vF+1%3221&QF&5'R<y8%211vQL%5221%711%=291").
Proof.
clear -Hwin HK0. pose proof (u64_range s).
pose proof (Z.div_mod (bv_unsigned s + K) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (bv_unsigned s + K) 8 ltac:(lia)). lia.
Qed.
Definition KE : Z := ((bv_unsigned s + K) / 8 * 8 + 8 - bv_unsigned s)%Z.
Lemma KE_facts : ltac2:(TCodec.tc2 tcn__musl_Js0Memchr "Q2'=&QC&Q@vF+1%3221&Q8%6221+8%7261%9241%;241&QF&5'R<y8%211vQL%5221%711%C2>1'>'E&QE&R=yR0vR9%3221%J21F%621Ez%:3921%Q02<1%Q12F1").
Proof.
unfold KE. clear -Hwin HK0. pose proof (u64_range s).
pose proof (Z.div_mod (bv_unsigned s + K) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (bv_unsigned s + K) 8 ltac:(lia)).
repeat split; try lia.
replace (bv_unsigned s + ((bv_unsigned s + K) / 8 * 8 + 8 - bv_unsigned s))%Z
with (8 + ((bv_unsigned s + K) / 8) * 8)%Z by lia.
rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma bz : ltac2:(TCodec.tc2 tcn__musl_Js0Memchr ":'>'E&R=y8&Q9vF%211%5241z%93821").
Proof. exact (Hzero _ _ _ _ _ HOK). Qed.
Lemma bnz : ltac2:(TCodec.tc2 tcn__musl_Js0Memchr "F'E'=&QCzr1%3221&QDvF%2241%8241&@'>&R=y8&Q9r2%211%5241%73B1?%911p0;1pT2E1").
Proof. intros j Hj. unfold b_. apply (Hnz _ _ _ _ _ HOK). lia. Qed.
Lemma rd_w : ltac2:(TCodec.tc2 tcn__musl_Js0Memchr "Q9'E'7&QCzr2%3221&Q@r3&QF%115%4231&5'R<y8%211vQL%5221%911%@281'>':'6%118%311&Q0&Q?vR3&JvR9r4%3221%74651H(0&Q:%125K%32=1%A3=51p0C1p0Q11pT6Q61pT2Q81").
Proof.
intros j m Hj Hm. unfold sb_.
replace (at_ s j) with (at_ s (Z.of_nat (Z.to_nat j))) by (f_equal; lia).
apply (rdn_sub RSEGS mem (length buf)); [exact Hbuf | lia].
Qed.
Lemma rd_b : ltac2:(TCodec.tc2 tcn__musl_Js0Memchr "Q<'E&QCzr1%3221&Q@r2+1%3221&QF&5'R<y8%211vQL%5221%711%@291'>':'6%118%311&Q0&Q?vR3&JvR9r3%3221u1%847621(0(3&Q9%117(9%11H%53I31%72B1%F3B91p0H1p0Q61pT2Q;1").
Proof.
intros j Hj H1. rewrite (rd_w j 1) by lia. unfold sb_, b_.
rewrite sub_nth; [reflexivity | lia].
Qed.
Lemma sb_len : ltac2:(TCodec.tc2 tcn__musl_Js0Memchr "M'E'7&QCzr2%3221&Q@r3&QF%115%4231&5'R<y8%211vQL%5221%911%@281'>&Q:r4%221?%<291%53G1Ap071p0E1pT6J1pT2L1").
Proof. intros j m Hj Hm. unfold sb_. apply sub_length. lia. Qed.
Lemma sb_nth : ltac2:(TCodec.tc2 tcn__musl_Js0Memchr "Q8'E'7&QCzr2%3221&Cu8%2241&Q@r4+8%3221&QF&5'R<y8%211vQL%5221%711%C291'>&D&Q:r5%221C&R;%12<I%64<C31&Q9%B1E%G271%311%<3A51p0>1p0L1p0Q01pT0Q51pT2Q71").
Proof.
intros j i Hj Hi H8. unfold sb_, b_. rewrite nth_sub by lia. f_equal. lia.
Qed.
Lemma m_lbu : forall regs pc w rd rs (imm : bv 12) j0 j,
fetch_word RSEGS pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
getr regs rs = at_ s j0 -> (j0 + bv_signed imm = j)%Z ->
(0 <= j)%Z -> (j + 1 <= L)%Z ->
RiscvSemantics.step RSEGS (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LBv (b_ j))) (v_addi pc 4) mem rom).
Proof.
intros regs pc w rd rs imm j0 j Hf He Hd Hrs Hj Hj0 Hj1.
eapply step_lbu; [exact Hf | exact He | exact Hd |].
rewrite Hrs, at_addi, Hj. apply rd_b; lia.
Qed.
Lemma m_ld : forall regs pc w rd rs (imm : bv 12) j0 j,
fetch_word RSEGS pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ8 true rd rs imm, 4%Z) ->
getr regs rs = at_ s j0 -> (j0 + bv_signed imm = j)%Z ->
(0 <= j)%Z -> (j + 8 <= L)%Z ->
RiscvSemantics.step RSEGS (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LDv (sb_ j 8))) (v_addi pc 4) mem rom).
Proof.
intros regs pc w rd rs imm j0 j Hf He Hd Hrs Hj Hj0 Hj8.
eapply step_ld; [exact Hf | exact He | exact Hd | |].
- rewrite Hrs, at_addi, Hj. apply (rd_w j 8); lia.
- symmetry. apply u_LDv. apply sb_len; lia.
Qed.
Lemma al_room : ltac2:(TCodec.tc2 tcn__musl_Js0Memchr "L'E'>&QE&Q@&R=yR0vR9%3221r1%6221+8%9221z%<3=21'=&QCr2%2251vF%4231%6231r3%C21<&Q8%9221p051p0=1pT2K1").
Proof.
intros j Hal Hj. unfold KE. clear -Hal Hj HK0. pose proof (u64_range s).
pose proof (Z.div_mod (bv_unsigned s + K) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (bv_unsigned s + K) 8 ltac:(lia)).
pose proof (Z.div_mod (bv_unsigned s + j) 8 ltac:(lia)).
assert ((bv_unsigned s + j) / 8 <= (bv_unsigned s + K) / 8)%Z by (apply Z.div_le_mono; lia).
lia.
Qed.
Lemma tw_hit : ltac2:(TCodec.tc2 tcn__musl_Js0Memchr "Q@'E'=&QCzr1%3221vF%5231%7231&QD&Q@r2+8%3221%5281r3%6214&QF&5'R<y8%211vQL%5221%711%G291'>'2&M&Q<&Q7&Q:r4u8%3221%511%711&R;yR0&Q6%3221%=251(4%A3@21p0C1p0O1p0Q61pT2Q?1").
Proof.
intros j Hj HKj HL.
apply (TW_haszero _ (Z.to_nat (K - j))).
- apply sb_len; lia.
- lia.
- rewrite sb_nth by lia. rewrite <- bz. f_equal. unfold b_. f_equal. lia.
- intros jj Hjj. rewrite sb_nth by lia. apply bnz. lia.
Qed.
Lemma tw_miss : ltac2:(TCodec.tc2 tcn__musl_Js0Memchr "Q<'E&QCzr1%3221&Q@r2+8%3221vF%9221r3%7215&QF&5'R<y8%211vQL%5221%711%D291'>'2&M&Q<&Q7&Q:r4u8%3221%511%711&R;yR0&Q6%3221%=251(;%A3@21p0C1p0O1p0Q61pT2Q;1").
Proof.
intros j Hj HKj HL. apply TW_nozero.
- apply sb_len; lia.
- intros i Hi. rewrite sb_nth by lia. apply bnz. lia.
Qed.
Ltac mlbu F D jj :=
chain_step; [reflexivity
| eapply m_lbu with (j := jj);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; lia] | imm_norm; lia | lia | lia]
| step_simpl]; vnorm.
Ltac mld F D jj :=
chain_step; [reflexivity
| eapply m_ld with (j := jj);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; lia] | imm_norm; lia | lia | lia]
| step_simpl]; vnorm.
Ltac condb :=
rwH; rewrite c_eq_LBv_0;
first [ apply Z.eqb_eq; rewrite <- bz; f_equal; f_equal; lia
| apply Z.eqb_neq; apply bnz; lia ].
Ltac cond := try unfold v_addi; cond_lia.
Ltac condw lem :=
rwH;
lazymatch goal with |- c_eq (v_and (v_or (v_sub _ (v_xor ?x _)) _) _) _ = ?b =>
change (c_eq (TW x) (Z_to_bv 64 Hc) = b) end;
apply lem; lia.
Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try reflexivity; try (f_equal; lia);
try (unfold v_addi; unorm; f_equal; lia); try solve_keeps_cs.
Lemma t_found : ltac2:(TCodec.tc2 tcn__musl_Js0Memchr "R2&Hy5'R<yR0%211%5241&Kr1%211'>&Nr3(R:+1(<%33>21%6251r2%93>21r4+:%93D17%<231&JvR9vF%3221%B3G51r5+;%B3M1@%E231&R;z%22O1%J3O41'?'='I&Q?&OvQNr7+eTX4%Q03Q91N/01Q9vR3vR8%8576321r6%:59Q;143%=3<31%Q:2Q=O%Q<3QA1K&Q4%12=Q@%C231%D261qT>QE1%G2QF1p0I1p0Q21p0Q<1p0QG1pT@QL1pT<QL1").
Proof.
intros regs ret Hret H1 H10 H11. pose proof KL. eexists. split.
- mlbu (ltac:(oF' 0xa9104%Z)) (ltac:(oD' 0xa9104%Z)) K.
stepb_tk (ltac:(oF' 0xa9108%Z)) (ltac:(oD' 0xa9108%Z)) ltac:(condb).
stepret (ltac:(oF' 0xa911c%Z)) (ltac:(oD' 0xa911c%Z)) ret ltac:(exact H1).
apply mst_refl.
- post.
Qed.
Lemma t_loop : ltac2:(TCodec.tc2 tcn__musl_Js0Memchr "S:'7&Hy5'R<yR0%211%5241'E&Kr3%211'>&Nr5(R:+1(<%33?21%6251r4%93?21r6+:%93E17%<231&JvR9%2218%A3G41r7+;%A3M1?%D231&R;z%22O1%I3O41r8+=%I3Q51G%L231%82Q5L%O3Q521'=&QC%12;@&QDvF%22C1%6241&QFr;%211&QH%127Q7%221B%Q=3QA41&Q@r9%62<1%321Q=%A21H&QG+2+R0%3221%D2M1%H261'?'I&Q?&OvQNr=+eTX<%QM3R71QK/01R7vR3vR8%8576321r1r<%;5:2154%>3=41%R824QM%QL2QKQ6%R;3RA21&Q4%12?8%Q>231%Q?271qT>RE1%H2RF1p0J1p0Q61p0Q>1p0QF1p0QM1p0R61p0R?1p0RJ1pT6RN1pT2RO1pT@S21pT<S21pT0S91").
Proof.
pose proof KL as HKL.
induction i as [|i IH]; intros regs ret j m Hret H1 H10 H11 H13 Hj Hi Hm.
-
eexists. split.
+ stepn (ltac:(oF' 0xa910c%Z)) (ltac:(oD' 0xa910c%Z)).
stepn (ltac:(oF' 0xa9110%Z)) (ltac:(oD' 0xa9110%Z)).
stepb_tk (ltac:(oF' 0xa9114%Z)) (ltac:(oD' 0xa9114%Z)) ltac:(cond).
mlbu (ltac:(oF' 0xa9104%Z)) (ltac:(oD' 0xa9104%Z)) K.
stepb_tk (ltac:(oF' 0xa9108%Z)) (ltac:(oD' 0xa9108%Z)) ltac:(condb).
stepret (ltac:(oF' 0xa911c%Z)) (ltac:(oD' 0xa911c%Z)) ret ltac:(exact H1).
apply mst_refl.
+ post.
-
eapply (runs_trans RSEGS _ (fun r => mkst r (0xa910c : word) mem rom)
(fun r => getr r 1 = ret /\ getr r 10 = at_ s (j + 1) /\ getr r 11 = Z_to_bv 64 0
/\ getr r 13 = Z_to_bv 64 (m - 1) /\ keeps_cs regs r)).
+ eexists. split.
* stepn (ltac:(oF' 0xa910c%Z)) (ltac:(oD' 0xa910c%Z)).
stepn (ltac:(oF' 0xa9110%Z)) (ltac:(oD' 0xa9110%Z)).
stepb_tk (ltac:(oF' 0xa9114%Z)) (ltac:(oD' 0xa9114%Z)) ltac:(cond).
mlbu (ltac:(oF' 0xa9104%Z)) (ltac:(oD' 0xa9104%Z)) (j + 1)%Z.
stepb_ft (ltac:(oF' 0xa9108%Z)) (ltac:(oD' 0xa9108%Z)) ltac:(condb).
apply mst_refl.
* post.
+ cbv beta. intros r1 (R1 & R10 & R11 & R13 & KC).
destruct (IH r1 ret (j + 1)%Z (m - 1)%Z Hret R1 R10 R11 R13 ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & A10 & K2).
exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
Qed.
Lemma w_loop : ltac2:(TCodec.tc2 tcn__musl_Js0Memchr "TB'7&Hy5'R<yR0%211%5241'E&Kr3%211'>&Nr5(R:+1(<%33?21%6251r4%93?21r6+:%93E17%<231&JvR9%2218%A3G41r7+;%A3M1?%D231&R;z%22O1%I3O41r8+<%I3Q51G%L231%82Q5L%O3Q521r9+=%O3Q;1M%Q2231&Q;%?2Q<1%Q63Q<31r:+>%Q63QB1Q4%Q9231&Q6%F2QC1%Q=3QC31r;+?%Q=3QI1Q;%Q@231%QB3QH1Jr<+@%QB3QN1Q@%QE231+7%Q22QO1%QI3QO31'=&QC%12Q5>vF%32@1%5231&QE&Q@&R=%12R:QD%321A+8%6221%R73R;1Q@&QFr@%211&QA&QHr=%22A1%421:%R@3RD61r>%62E1%B21>%I217&QD&QG+2+R0%3221%52=1%Q1271'?'I&Q?&OvQNrB+eTVH%S03S:1RN/01S:vR3vR8%8576321r1rA%;5:2154%>3=41%S;24S0%RO2RNQ@%S>3SD21&Q4%12?8%QG231%QH271qT>SH1%H2SI1p0J1p0Q61p0Q@1p0QI1p0R01p0R81p0R>1p0RF1p0RN1p0S51p0S>1p0SG1p0T21pT6T61pT2T71pT@T:1pT<T:1pT0TA1").
Proof.
pose proof KL as HKL. pose proof KE_facts as (HKE1 & HKE2 & HKE3).
induction i as [|i IH]; intros regs ret j m Hret H1 H10 H11 H12 H13 H14 H15 H16 Hj Hal Hi Hm;
pose proof (al_room j Hal Hj) as HR.
-
assert (HKj : (K < j + 8)%Z).
{ clear -Hi Hj. pose proof (Z.div_mod (K - j) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (K - j) 8 ltac:(lia)). lia. }
destruct (Z.eq_dec j K) as [HjK|HjK].
+
eexists. split.
* mld (ltac:(oF' 0xa90d8%Z)) (ltac:(oD' 0xa90d8%Z)) j.
stepn (ltac:(oF' 0xa90dc%Z)) (ltac:(oD' 0xa90dc%Z)).
stepn (ltac:(oF' 0xa90e0%Z)) (ltac:(oD' 0xa90e0%Z)).
stepn (ltac:(oF' 0xa90e4%Z)) (ltac:(oD' 0xa90e4%Z)).
stepn (ltac:(oF' 0xa90e8%Z)) (ltac:(oD' 0xa90e8%Z)).
stepb_tk (ltac:(oF' 0xa90ec%Z)) (ltac:(oD' 0xa90ec%Z)) ltac:(condw tw_hit).
stepn (ltac:(oF' 0xa9120%Z)) (ltac:(oD' 0xa9120%Z)).
mlbu (ltac:(oF' 0xa9124%Z)) (ltac:(oD' 0xa9124%Z)) j.
stepb_ft (ltac:(oF' 0xa9128%Z)) (ltac:(oD' 0xa9128%Z)) ltac:(condb).
stepn (ltac:(oF' 0xa912c%Z)) (ltac:(oD' 0xa912c%Z)).
stepret (ltac:(oF' 0xa911c%Z)) (ltac:(oD' 0xa911c%Z)) ret ltac:(exact H1).
apply mst_refl.
* post.
+
eapply (runs_trans RSEGS _ (fun r => mkst r (0xa910c : word) mem rom)
(fun r => getr r 1 = ret /\ getr r 10 = at_ s j /\ getr r 11 = Z_to_bv 64 0
/\ getr r 13 = Z_to_bv 64 m /\ keeps_cs regs r)).
* eexists. split.
-- mld (ltac:(oF' 0xa90d8%Z)) (ltac:(oD' 0xa90d8%Z)) j.
stepn (ltac:(oF' 0xa90dc%Z)) (ltac:(oD' 0xa90dc%Z)).
stepn (ltac:(oF' 0xa90e0%Z)) (ltac:(oD' 0xa90e0%Z)).
stepn (ltac:(oF' 0xa90e4%Z)) (ltac:(oD' 0xa90e4%Z)).
stepn (ltac:(oF' 0xa90e8%Z)) (ltac:(oD' 0xa90e8%Z)).
stepb_tk (ltac:(oF' 0xa90ec%Z)) (ltac:(oD' 0xa90ec%Z)) ltac:(condw tw_hit).
stepn (ltac:(oF' 0xa9120%Z)) (ltac:(oD' 0xa9120%Z)).
mlbu (ltac:(oF' 0xa9124%Z)) (ltac:(oD' 0xa9124%Z)) j.
stepb_tk (ltac:(oF' 0xa9128%Z)) (ltac:(oD' 0xa9128%Z)) ltac:(condb).
apply mst_refl.
-- post.
* cbv beta. intros r1 (R1 & R10 & R11 & R13 & KC).
destruct (t_loop (Z.to_nat (K - 1 - j)) r1 ret j m Hret R1 R10 R11 R13
ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & A10 & K2).
exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
-
assert (HKj : (j + 8 <= K)%Z).
{ clear -Hi Hj. pose proof (Z.div_mod (K - j) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (K - j) 8 ltac:(lia)). lia. }
eapply (runs_trans RSEGS _ (fun r => mkst r (0xa90d8 : word) mem rom)
(fun r => getr r 1 = ret /\ getr r 10 = at_ s (j + 8) /\ getr r 11 = Z_to_bv 64 0
/\ getr r 12 = Z_to_bv 64 (m - 8) /\ getr r 13 = Z_to_bv 64 Mc /\ getr r 14 = Z_to_bv 64 Hc
/\ getr r 15 = Z_to_bv 64 0 /\ getr r 16 = Z_to_bv 64 7 /\ keeps_cs regs r)).
+ eexists. split.
* mld (ltac:(oF' 0xa90d8%Z)) (ltac:(oD' 0xa90d8%Z)) j.
stepn (ltac:(oF' 0xa90dc%Z)) (ltac:(oD' 0xa90dc%Z)).
stepn (ltac:(oF' 0xa90e0%Z)) (ltac:(oD' 0xa90e0%Z)).
stepn (ltac:(oF' 0xa90e4%Z)) (ltac:(oD' 0xa90e4%Z)).
stepn (ltac:(oF' 0xa90e8%Z)) (ltac:(oD' 0xa90e8%Z)).
stepb_ft (ltac:(oF' 0xa90ec%Z)) (ltac:(oD' 0xa90ec%Z)) ltac:(condw tw_miss).
stepn (ltac:(oF' 0xa90f0%Z)) (ltac:(oD' 0xa90f0%Z)).
stepn (ltac:(oF' 0xa90f4%Z)) (ltac:(oD' 0xa90f4%Z)).
stepb_tk (ltac:(oF' 0xa90f8%Z)) (ltac:(oD' 0xa90f8%Z)) ltac:(cond).
apply mst_refl.
* post.
+ cbv beta. intros r1 (R1 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & KC).
destruct (IH r1 ret (j + 8)%Z (m - 8)%Z Hret R1 R10 R11 R12 R13 R14 R15 R16 ltac:(lia)
ltac:(rewrite Z.add_assoc, <- Zplus_mod_idemp_l, Hal; reflexivity)
ltac:(clear -Hi HKj; pose proof (Z.div_mod (K - j) 8 ltac:(lia));
pose proof (Z.mod_pos_bound (K - j) 8 ltac:(lia));
pose proof (Z.div_mod (K - (j + 8)) 8 ltac:(lia));
pose proof (Z.mod_pos_bound (K - (j + 8)) 8 ltac:(lia)); nia)
ltac:(lia)) as (r2 & RUN & A10 & K2).
exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
Qed.
Ltac ldc F D vv RD :=
chain_step; [reflexivity
| eapply step_ld with (v := vv);
[exact F | reflexivity | exact D
| gres; imm_norm;
lazymatch goal with |- rdn _ _ ?a _ = _ =>
lazymatch type of RD with rdn _ _ ?c _ = _ =>
replace a with c by (apply bv_eq; vm_compute; reflexivity) end end;
exact RD
| assumption ]
| step_simpl]; vnorm.
Section SE.
Local Abbreviation SEC_T_a_entry := (ltac2:(TCodec.tc2 tcn__musl_Js0Memchr "S@&Hy5'R<yR0%211%5241'E&Kr3%211'>&Nr5(R:+1(<%33?21%6251r4%93?21r6+:%93E17%<231&JvR9%2218%A3G41r7+;%A3M1?%D231&R;z%22O1%I3O41r8+<%I3Q51G%L231%82Q5L%O3Q521r9+>%O3Q;1M%Q2231%>2Q;Q0%Q53Q;21'=&QC%12A>vF%32@1%5231&QE&Q@&R=%12QFQ0%321@+8%6221%QC3QG1L&QHr:%22=1%:216%A21H&QD&QG+2+R0%3221%52N1%I271'?'I&Q?&OvQNr>+eTU8%R43R>1R2/01R>vR3vR8%8576321r1r=%;5:2154%>3=41%R?24R4%R32R2Q8%RB3RH21&Q4%12?8%Q?231%Q@271qT>RL1%H2RM1p0J1p0Q71p0Q@1p0QG1p0QN1p0R51p0R>1p0RG1p0S21pT6S61pT2S71pT@S:1pT<S:1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_a_entry) 0%nat 0%nat).
Variable ret : ltac:(sec_ty2 constr:(SEC_T_a_entry) 1%nat 0%nat).
Variable j : ltac:(sec_ty2 constr:(SEC_T_a_entry) 2%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_a_entry) 3%nat 0%nat).
Lemma a_entry : ltac:(sec_stmt2 constr:(SEC_T_a_entry) 4%nat 0%nat).
Proof.
intros Hret H1 H10 H11 H12 H14 Hj Hal Hm.
pose proof KL as HKL. pose proof KE_facts as (HKE1 & HKE2 & HKE3). pose proof (al_room j Hal Hj) as HR.
destruct (rd_const_M mem Hro) as (bsM & RM & EM).
destruct (rd_const_H mem Hro) as (bsH & RH & EH).
destruct (Z.eq_dec j K) as [HjK|HjK].
-
eapply (runs_trans RSEGS _ (fun r => mkst r (0xa9104 : word) mem rom)
(fun r => getr r 1 = ret /\ getr r 10 = at_ s K /\ getr r 11 = Z_to_bv 64 0 /\ keeps_cs regs r)).
+ eexists. split.
* stepb_ft (ltac:(oF' 0xa90a8%Z)) (ltac:(oD' 0xa90a8%Z)) ltac:(cond).
mlbu (ltac:(oF' 0xa90ac%Z)) (ltac:(oD' 0xa90ac%Z)) j.
stepb_tk (ltac:(oF' 0xa90b0%Z)) (ltac:(oD' 0xa90b0%Z)) ltac:(condb).
stepn (ltac:(oF' 0xa90fc%Z)) (ltac:(oD' 0xa90fc%Z)).
stepb_ft (ltac:(oF' 0xa9100%Z)) (ltac:(oD' 0xa9100%Z)) ltac:(cond).
apply mst_refl.
* post.
+ cbv beta. intros r1 (R1 & R10 & R11 & KC).
destruct (t_found r1 ret Hret R1 R10 R11) as (r2 & RUN & A10 & K2).
exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
-
eapply (runs_trans RSEGS _ (fun r => mkst r (0xa90d8 : word) mem rom)
(fun r => getr r 1 = ret /\ getr r 10 = at_ s j /\ getr r 11 = Z_to_bv 64 0
/\ getr r 12 = Z_to_bv 64 m /\ getr r 13 = Z_to_bv 64 Mc /\ getr r 14 = Z_to_bv 64 Hc
/\ getr r 15 = Z_to_bv 64 0 /\ getr r 16 = Z_to_bv 64 7 /\ keeps_cs regs r)).
+ eexists. split.
* stepb_ft (ltac:(oF' 0xa90a8%Z)) (ltac:(oD' 0xa90a8%Z)) ltac:(cond).
mlbu (ltac:(oF' 0xa90ac%Z)) (ltac:(oD' 0xa90ac%Z)) j.
stepb_ft (ltac:(oF' 0xa90b0%Z)) (ltac:(oD' 0xa90b0%Z)) ltac:(condb).
stepn (ltac:(oF' 0xa90b4%Z)) (ltac:(oD' 0xa90b4%Z)).
stepb_ft (ltac:(oF' 0xa90b8%Z)) (ltac:(oD' 0xa90b8%Z)) ltac:(cond).
stepn (ltac:(oF' 0xa90bc%Z)) (ltac:(oD' 0xa90bc%Z)).
ldc (ltac:(oF' 0xa90c0%Z)) (ltac:(oD' 0xa90c0%Z)) (Z_to_bv 64 Mc) RM.
stepn (ltac:(oF' 0xa90c4%Z)) (ltac:(oD' 0xa90c4%Z)).
ldc (ltac:(oF' 0xa90c8%Z)) (ltac:(oD' 0xa90c8%Z)) (Z_to_bv 64 Hc) RH.
stepn (ltac:(oF' 0xa90cc%Z)) (ltac:(oD' 0xa90cc%Z)).
stepiv (ltac:(oF' 0xa90d0%Z)) (ltac:(oD' 0xa90d0%Z)) (Z_to_bv 64 0)
ltac:(gres; rwH; apply bv_eq; vm_compute; reflexivity).
vnorm.
stepn (ltac:(oF' 0xa90d4%Z)) (ltac:(oD' 0xa90d4%Z)).
apply mst_refl.
* post.
+ cbv beta. intros r1 (R1 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & KC).
destruct (w_loop (Z.to_nat ((K - j) / 8)) r1 ret j m Hret R1 R10 R11 R12 R13 R14 R15 R16 Hj Hal
ltac:(clear -Hj; pose proof (Z.div_pos (K - j) 8); lia) Hm) as (r2 & RUN & A10 & K2).
exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
Qed.
End SE.
Ltac snez1 :=
match goal with |- context [v_sltu ?a ?b] =>
replace (v_sltu a b) with (Z_to_bv 64 1)
by (symmetry; rwH; unfold v_sltu; rewrite c_ltu_ltb; try unfold v_addi; unorm;
rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity) end.
Lemma andi7_u : ltac2:(TCodec.tc2 tcn__musl_Js0Memchr "Q2'E'=&QCz&Q@&R=yR0vR9%3221r1%6221%9281&QD&QG+2+R0%3221%5271%A271'>&Q1&Jr2%22@1+7%5221%E2D1&QE%H2D6+8%3221%<3O51p0>1pT2Q11").
Proof.
intros j Hj. rewrite u_andi by lia. rewrite at_u by lia.
change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
Qed.
Lemma h_loop : ltac2:(TCodec.tc2 tcn__musl_Js0Memchr "SO'7&Hy5'R<yR0%211%5241'E&Kr3%211'>&Nr5(R:+1(<%33?21%6251r4%93?21r6+:%93E17%<231&JvR9%2218%A3G41r7+;%A3M1?%D231&R;z%22O1%I3O41r8+<%I3Q51G%L231%82Q5L%O3Q521r9+?%O3Q;1M%Q2231&Q@%12CQ1%H2G1%Q73Q=41r:+@%Q73QC1Q5%Q:231%F2QCQ8%Q=3QC21'=&QC%12I@vF%32B1%5231&QFr=%211&QH+7&QE&R=%12R2Q<%H21D+8%5221%8271%R03R4:1r;%;2A1%O216%E21L&QD&QG+2+R0%3221%52Q21%M271'?'I&Q?&OvQNr?+eTT0%R@3RJ1R>/01RJvR3vR8%8576321r1r>%;5:2154%>3=41%RK24R@%R?2R>Q<%RN3S421&Q4%12?8%QC231%QD271qT>S81%H2S91p0J1p0Q61p0QD1p0QK1p0R21p0R;1p0RB1p0RK1p0S41p0S?1pT6SC1pT2SD1pT@SG1pT<SG1pT0SN1").
Proof.
pose proof KL as HKL. pose proof (u64_range s) as Hs.
induction i as [|i IH]; intros regs ret j m Hret H1 H10 H11 H12 H15 H16 Hj Hi Hm.
-
destruct (Z.eq_dec j K) as [HjK|HjK].
+ eapply (runs_trans RSEGS _ (fun r => mkst r (0xa9104 : word) mem rom)
(fun r => getr r 1 = ret /\ getr r 10 = at_ s K /\ getr r 11 = Z_to_bv 64 0 /\ keeps_cs regs r)).
* eexists. split.
-- mlbu (ltac:(oF' 0xa9080%Z)) (ltac:(oD' 0xa9080%Z)) j.
stepn (ltac:(oF' 0xa9084%Z)) (ltac:(oD' 0xa9084%Z)).
stepb_tk (ltac:(oF' 0xa9088%Z)) (ltac:(oD' 0xa9088%Z)) ltac:(condb).
apply mst_refl.
-- post.
* cbv beta. intros r1 (R1 & R10 & R11 & KC).
destruct (t_found r1 ret Hret R1 R10 R11) as (r2 & RUN & A10 & K2).
exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
+ eapply (runs_trans RSEGS _ (fun r => mkst r (0xa90a8 : word) mem rom)
(fun r => getr r 1 = ret /\ getr r 10 = at_ s (j + 1) /\ getr r 11 = Z_to_bv 64 0
/\ getr r 12 = Z_to_bv 64 (m - 1) /\ getr r 14 = Z_to_bv 64 1 /\ keeps_cs regs r)).
* eexists. split.
-- mlbu (ltac:(oF' 0xa9080%Z)) (ltac:(oD' 0xa9080%Z)) j.
stepn (ltac:(oF' 0xa9084%Z)) (ltac:(oD' 0xa9084%Z)).
stepb_ft (ltac:(oF' 0xa9088%Z)) (ltac:(oD' 0xa9088%Z)) ltac:(condb).
stepn (ltac:(oF' 0xa908c%Z)) (ltac:(oD' 0xa908c%Z)).
stepn (ltac:(oF' 0xa9090%Z)) (ltac:(oD' 0xa9090%Z)).
stepn (ltac:(oF' 0xa9094%Z)) (ltac:(oD' 0xa9094%Z)).
stepn (ltac:(oF' 0xa9098%Z)) (ltac:(oD' 0xa9098%Z)). snez1.
stepb_tk (ltac:(oF' 0xa909c%Z)) (ltac:(oD' 0xa909c%Z))
ltac:(rwH; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_eq;
rewrite Z.add_assoc, <- Zplus_mod_idemp_l;
replace ((bv_unsigned s + j) mod 8)%Z with 7%Z by lia; reflexivity).
apply mst_refl.
-- post.
* cbv beta. intros r1 (R1 & R10 & R11 & R12 & R14 & KC).
destruct (a_entry r1 ret (j + 1)%Z (m - 1)%Z Hret R1 R10 R11 R12 R14 ltac:(lia)
ltac:(rewrite Z.add_assoc, <- Zplus_mod_idemp_l;
replace ((bv_unsigned s + j) mod 8)%Z with 7%Z by lia; reflexivity)
ltac:(lia)) as (r2 & RUN & A10 & K2).
exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
-
destruct (Z.eq_dec j K) as [HjK|HjK].
+ eapply (runs_trans RSEGS _ (fun r => mkst r (0xa9104 : word) mem rom)
(fun r => getr r 1 = ret /\ getr r 10 = at_ s K /\ getr r 11 = Z_to_bv 64 0 /\ keeps_cs regs r)).
* eexists. split.
-- mlbu (ltac:(oF' 0xa9080%Z)) (ltac:(oD' 0xa9080%Z)) j.
stepn (ltac:(oF' 0xa9084%Z)) (ltac:(oD' 0xa9084%Z)).
stepb_tk (ltac:(oF' 0xa9088%Z)) (ltac:(oD' 0xa9088%Z)) ltac:(condb).
apply mst_refl.
-- post.
* cbv beta. intros r1 (R1 & R10 & R11 & KC).
destruct (t_found r1 ret Hret R1 R10 R11) as (r2 & RUN & A10 & K2).
exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
+ pose proof (Z.mod_pos_bound (bv_unsigned s + j + 1) 8 ltac:(lia)) as HM1.
assert (HM : ((bv_unsigned s + j + 1) mod 8 = (bv_unsigned s + j) mod 8 + 1)%Z).
{ clear -Hi Hs Hj. rewrite <- (Zplus_mod_idemp_l (bv_unsigned s + j)).
pose proof (Z.mod_pos_bound (bv_unsigned s + j) 8 ltac:(lia)). apply Z.mod_small. lia. }
eapply (runs_trans RSEGS _ (fun r => mkst r (0xa9080 : word) mem rom)
(fun r => getr r 1 = ret /\ getr r 10 = at_ s (j + 1) /\ getr r 11 = Z_to_bv 64 0
/\ getr r 12 = Z_to_bv 64 (m - 1) /\ getr r 15 = at_ s (j + 1 + 1)
/\ getr r 16 = Z_to_bv 64 1 /\ keeps_cs regs r)).
* eexists. split.
-- mlbu (ltac:(oF' 0xa9080%Z)) (ltac:(oD' 0xa9080%Z)) j.
stepn (ltac:(oF' 0xa9084%Z)) (ltac:(oD' 0xa9084%Z)).
stepb_ft (ltac:(oF' 0xa9088%Z)) (ltac:(oD' 0xa9088%Z)) ltac:(condb).
stepn (ltac:(oF' 0xa908c%Z)) (ltac:(oD' 0xa908c%Z)).
stepn (ltac:(oF' 0xa9090%Z)) (ltac:(oD' 0xa9090%Z)).
stepn (ltac:(oF' 0xa9094%Z)) (ltac:(oD' 0xa9094%Z)).
stepn (ltac:(oF' 0xa9098%Z)) (ltac:(oD' 0xa9098%Z)). snez1.
stepb_ft (ltac:(oF' 0xa909c%Z)) (ltac:(oD' 0xa909c%Z))
ltac:(rwH; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_neq;
rewrite Z.add_assoc; lia).
stepn (ltac:(oF' 0xa90a0%Z)) (ltac:(oD' 0xa90a0%Z)).
stepb_tk (ltac:(oF' 0xa90a4%Z)) (ltac:(oD' 0xa90a4%Z)) ltac:(cond).
apply mst_refl.
-- post.
* cbv beta. intros r1 (R1 & R10 & R11 & R12 & R15 & R16 & KC).
destruct (IH r1 ret (j + 1)%Z (m - 1)%Z Hret R1 R10 R11 R12 R15 R16 ltac:(lia)
ltac:(rewrite Z.add_assoc; lia) ltac:(lia)) as (r2 & RUN & A10 & K2).
exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
Qed.
Section SE.
Local Abbreviation SEC_T_memchr0_run := (ltac2:(TCodec.tc2 tcn__musl_Js0Memchr "R:&Hy5'R<yR0%211%5241&Kr1%211'>&Nr3(R:+1(<%33>21%6251r2%93>21r4+:%93D17%<231vR9%?3D21r5+;%?3J1=%B231&R;z%22L1%G3L41r6+<%G3Q21E%J231vR4%92Q31%N3Q331'?'='I&Q?&OvQNr8+eTS4%Q43Q=1Q2/01Q=vR3vR8%8576321r7%:59Q?143%=3<31%Q>2QAQ3&JvF%22Q41%QC3QH41&Q4%12@QG%F231%G291qT>QL1%J2QM1p0L1p0Q41p0Q=1p0QD1p0QO1pT@R41pT<R41")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_memchr0_run) 0%nat 0%nat).
Variable ret : ltac:(sec_ty2 constr:(SEC_T_memchr0_run) 1%nat 0%nat).
Lemma memchr0_run : ltac:(sec_stmt2 constr:(SEC_T_memchr0_run) 2%nat 0%nat).
Proof.
intros Hret H1 H10 H11 H12.
pose proof KL as HKL. pose proof (u64_range s) as Hs. rewrite <- (at_0 s) in H10.
pose proof (Z.mod_pos_bound (bv_unsigned s) 8 ltac:(lia)) as HM.
destruct (Z.eq_dec (bv_unsigned s mod 8) 0) as [Hal|Hal].
-
eapply (runs_trans RSEGS _ (fun r => mkst r (0xa90a8 : word) mem rom)
(fun r => getr r 1 = ret /\ getr r 10 = at_ s 0 /\ getr r 11 = Z_to_bv 64 0
/\ getr r 12 = Z_to_bv 64 n /\ getr r 14 = Z_to_bv 64 1 /\ keeps_cs regs r)).
+ eexists. split.
* stepn (ltac:(oF' 0xa9064%Z)) (ltac:(oD' 0xa9064%Z)). rwH. vals_lit.
stepn (ltac:(oF' 0xa9068%Z)) (ltac:(oD' 0xa9068%Z)).
stepn (ltac:(oF' 0xa906c%Z)) (ltac:(oD' 0xa906c%Z)). snez1.
stepb_tk (ltac:(oF' 0xa9070%Z)) (ltac:(oD' 0xa9070%Z))
ltac:(rwH; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_eq;
rewrite Z.add_0_r; exact Hal).
apply mst_refl.
* post.
+ cbv beta. intros r1 (R1 & R10 & R11 & R12 & R14 & KC).
destruct (a_entry r1 ret 0 n Hret R1 R10 R11 R12 R14 ltac:(lia) ltac:(rewrite Z.add_0_r; exact Hal) ltac:(lia))
as (r2 & RUN & A10 & K2).
exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
-
eapply (runs_trans RSEGS _ (fun r => mkst r (0xa9080 : word) mem rom)
(fun r => getr r 1 = ret /\ getr r 10 = at_ s 0 /\ getr r 11 = Z_to_bv 64 0
/\ getr r 12 = Z_to_bv 64 n /\ getr r 15 = at_ s (0 + 1) /\ getr r 16 = Z_to_bv 64 1
/\ keeps_cs regs r)).
+ eexists. split.
* stepn (ltac:(oF' 0xa9064%Z)) (ltac:(oD' 0xa9064%Z)). rwH. vals_lit.
stepn (ltac:(oF' 0xa9068%Z)) (ltac:(oD' 0xa9068%Z)).
stepn (ltac:(oF' 0xa906c%Z)) (ltac:(oD' 0xa906c%Z)). snez1.
stepb_ft (ltac:(oF' 0xa9070%Z)) (ltac:(oD' 0xa9070%Z))
ltac:(rwH; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_neq;
rewrite Z.add_0_r; exact Hal).
stepb_ft (ltac:(oF' 0xa9074%Z)) (ltac:(oD' 0xa9074%Z)) ltac:(cond).
stepn (ltac:(oF' 0xa9078%Z)) (ltac:(oD' 0xa9078%Z)).
stepn (ltac:(oF' 0xa907c%Z)) (ltac:(oD' 0xa907c%Z)).
apply mst_refl.
* post.
+ cbv beta. intros r1 (R1 & R10 & R11 & R12 & R15 & R16 & KC).
destruct (h_loop (Z.to_nat (7 - bv_unsigned s mod 8)) r1 ret 0 n Hret R1 R10 R11 R12 R15 R16
ltac:(lia) ltac:(rewrite Z.add_0_r; lia) ltac:(lia)) as (r2 & RUN & A10 & K2).
exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
Qed.
End SE.
End MCHR.
Theorem ref_memchr0 : ltac2:(TCodec.tc2 tcn__musl_Js0Memchr "RN'R<yR0%211':y8%511%311p051'6%114'E&Hy5%221;'Q=r8r7r6r5r4%6554321&Kr2%211'>&N(R:+1(<%33A21%52;1r3%83N21+:%83F16%:2A1r:%=3Q321+;%=3K1;%?2G1&R;z%22Q:1%D3Q:41+<%D3Q21B%F2O1r9%82Q@1%J3Q@31'?'='I&Q?&OvQN+eTS4%Q03QI1N/01QIr?%655=21Ir1%8571Q@3K%;3:31&Q4%12B4%Q:25Q1&Q@&R=r>%22R61r<%5221%Q12R91%QC3R981%H2:1%I2=1qT>R11%L2R21p0N1p0Q51p0Q=1p0QC1p0QM1p0R11pT@RD1pT<R:1pTBRA1pT:R?1pQ>R@1pSJRB1pTDRJ1pT8RF1").
Proof.
intros mem s buf K n rom regs ret HOK Hret H1 H10 H11 H12.
destruct (memchr0_run mem s buf K n rom HOK regs ret Hret H1 H10 H11 H12) as (r & RUN & A10 & KC).
exists r. split; [exact RUN | split; [exact KC | exact A10]].
Qed.
End FPX_1.
