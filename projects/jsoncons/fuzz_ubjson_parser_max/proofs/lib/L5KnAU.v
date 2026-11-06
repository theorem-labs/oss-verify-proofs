(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec StoreOk AxSymExec3 AxSymExec3B AxSymExec3Sound BigLinkBase BigLinkGlueUb0 L5Defs L5KnU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__L5KnAU () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3.AX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3Sound.AX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigLinkBase.BL."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5KnAU.L5KA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5KnAU.L5KA.WithSegs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5KnU.L5K."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "2and"; "2eq"; "3Z"; "0E"; "4word_to_le_bytes"; "0M"; "0M'"; "5KWord"; "5KZero"; "5SA"]; ["5edenot"; "5env"; "5expr"; "6kentry_ok"; "7MM"; "8defined"; "8u8_at"; ":zeros_at"; "9zpolyA"; ";zagree"; "<add"; "<le"; "<lt"; "<modulo"; "<pow"; "0V"]; ["0a"; "0a'"; "0b"; "0e"; "0i"; "0n"; "0n'"; "0ne"; "0off"; "0segs"; "=Z_to_bv"; "=bv"; "=bv_unsigned"; "0v"; "0x"; "0z"]; ["0zz"]]).
Module L5KA.
Fixpoint zpolyA (V : nat -> Z) (e : expr) : option Z :=
match e with
| ELit z => Some z
| EVar n => Some (V n)
| EAlu ALU_ADD a b => match zpolyA V a, zpolyA V b with Some x, Some y => Some (x + y) | _, _ => None end
| EAlu ALU_SUB a b => match zpolyA V a, zpolyA V b with Some x, Some y => Some (x - y) | _, _ => None end
| EAlu ALU_SRL a (ELit s) =>
if (Z.leb 0 s && Z.ltb s 64)%bool then match zpolyA V a with Some x => Some (x mod 18446744073709551616 / 2 ^ s) | None => None end else None
| EMd M_MUL a b => match zpolyA V a, zpolyA V b with Some x, Some y => Some (x * y) | _, _ => None end
| _ => None
end.
Lemma zpolyA_sound : ltac2:(TCodec.tc2 tcn__L5KnAU "Q2'A'3'8p021'B&Ir4r3r2%43321'7'5%11:&H%1287(0%12>8%73531&Q<yR0&@r6%221@%5241&M&D%22C1%A3I41p0;1p0D1pS2L1pR8K1pR0M1pDQ11").
Proof. intros E V e.
induction e; intros zz HA HZ; cbn [zpolyA L5K.zagree] in HA, HZ; try discriminate; cbn [edenot].
- inversion HZ; subst. rewrite Z_to_bv_unsigned. reflexivity.
- inversion HZ; subst. rewrite <- HA. symmetry. apply Z.mod_small. apply (BL.bvu_range (ev E n)).
- destruct HA as [HA1 HA2]. destruct op; try discriminate.
+ destruct (zpolyA V e1) as [x|] eqn:E1; destruct (zpolyA V e2) as [y|] eqn:E2; try discriminate. inversion HZ; subst.
rewrite (BL.zalu_sound ALU_ADD _ _ ((bv_unsigned (edenot E e1) + bv_unsigned (edenot E e2)) mod BL.MM)) by reflexivity.
rewrite (IHe1 x HA1 eq_refl), (IHe2 y HA2 eq_refl). rewrite <- Zplus_mod. reflexivity.
+ destruct (zpolyA V e1) as [x|] eqn:E1; destruct (zpolyA V e2) as [y|] eqn:E2; try discriminate. inversion HZ; subst.
rewrite (BL.zalu_sound ALU_SUB _ _ ((bv_unsigned (edenot E e1) - bv_unsigned (edenot E e2)) mod BL.MM)) by reflexivity.
rewrite (IHe1 x HA1 eq_refl), (IHe2 y HA2 eq_refl). rewrite <- Zminus_mod. reflexivity.
+ destruct e2 as [s| | | | | | |]; try discriminate.
destruct (Z.leb 0 s && Z.ltb s 64)%bool eqn:Hs; try discriminate. apply andb_prop in Hs as [Hs0 Hs1]. apply Z.leb_le in Hs0. apply Z.ltb_lt in Hs1.
destruct (zpolyA V e1) as [x|] eqn:E1; try discriminate. inversion HZ; subst.
rewrite (BL.zalu_sound ALU_SRL _ _ (bv_unsigned (edenot E e1) / 2 ^ (bv_unsigned (edenot E (ELit s)) mod 64))) by reflexivity.
rewrite (IHe1 x HA1 eq_refl). cbn [edenot]. rewrite BGU.unsigned_lit by lia.
rewrite (Z.mod_small s 64) by lia. rewrite BL.MM_val.
symmetry. apply Z.mod_small. split. apply Z.div_pos. apply Z.mod_pos_bound. lia. lia.
apply Z.div_lt_upper_bound. lia. assert (0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
pose proof (Z.mod_pos_bound x 18446744073709551616 ltac:(lia)). nia.
- destruct HA as [HA1 HA2]. destruct op; try discriminate.
destruct (zpolyA V e1) as [x|] eqn:E1; destruct (zpolyA V e2) as [y|] eqn:E2; try discriminate. inversion HZ; subst.
rewrite (BL.zmd_sound M_MUL _ _ ((bv_unsigned (edenot E e1) * bv_unsigned (edenot E e2)) mod BL.MM)) by reflexivity.
rewrite (IHe1 x HA1 eq_refl), (IHe2 y HA2 eq_refl). rewrite <- Zmult_mod. reflexivity.
Qed.
Lemma zpolyA_val : ltac2:(TCodec.tc2 tcn__L5KnAU "Q6'A'3'8p021'B&Ir5r4r3%43321'7'5%11:&H%1287(0%12>8%73531&M&D%22=1%;3C1=&Q<yR0&@r8r6%3221%6251%C3K1Fp091p0>1p0G1pRLO1pS0Q01pR8O1pR0Q11pDQ51").
Proof. intros E V e z v. intros HA HZ Hv. rewrite (zpolyA_sound E V e z HA HZ). exact Hv. Qed.
Lemma zpolyA_word : ltac2:(TCodec.tc2 tcn__L5KnAU "Q8'A'3'8p021'B&Ir5r4r3%43321'7'5%11:&H%1287(0%12>8%73531&M&D%22=1%;3C1='Q;yR0%211&@r8r6%3221&Q:%127G%E3731p0;1p0@1p0I1pRLQ11pS0Q21pR8Q11pR0Q31pDQ71").
Proof. intros E V e z v. intros HA HZ Hv. apply BGU.word_of_unsigned. eapply zpolyA_val; eauto. Qed.
Section WithSegs.
Variable segs : list Segment.
Definition zeros_at (M : word -> option byte) (a n : Z) : Prop :=
forall i, 0 <= i < n -> M (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0).
Lemma kentry_KZero : ltac2:(TCodec.tc2 tcn__L5KnAU "R4'A'Q;yR0%211'5y8%511%311p051'B'8'7&Q<&@r7r5%3221%52?1r2%83921r8r4%9221%;2E1%=3>16&Kz&Jr6%2281%5241&L%126;%625=%721C&N+2+R0%3221%>251&Gr;r9%@2M1%4331@&CvQ9r=r<(>(?r:%22;1%421;%948761p0;1p0A1p0I1p0L1p0Q31p0Q91pR<QC1pR2QD1pR@QF1pRBQF1pR6QH1pHQJ1pDR31").
Proof. intros E M b off ne a n.
intros Ha Hn H1 H2 H3 Hz. cbn [kentry_ok]. unfold flat, elenZ. rewrite L5K.estart_e, Ha, Hn.
split. lia. intros i Hi. apply Hz. lia.
Qed.
Lemma zeros_of_KZero : ltac2:(TCodec.tc2 tcn__L5KnAU "Q@'A'Q;yR0%211'5y8%511%311p051'B'8&CvQ9r7r6(>(?r5r4%3221r3%6221%;4:981'7&Q<&@r8%221=%42J1%63C19r9%621>%82N1%:3G1=&G&J%12CG%3371Cp051p0:1p0B1pR<O1pR2Q01pR@Q21pRBQ21pR6Q41pHQ61pDQ?1").
Proof. intros E M b off ne a n.
intros (Hf & Hz) Ha Hn i Hi. unfold elenZ in Hz. rewrite L5K.estart_e, Ha, Hn in Hz. apply Hz. lia.
Qed.
Lemma zeros_at_sub : ltac2:(TCodec.tc2 tcn__L5KnAU "O'Q;yR0%211'5y8%511%311p051'8&Gr5r4r3%43321&K%1253&J%1265r6%3219%6231r8%=31<;p031p091p0<1pR>B1pR4C1pR<D1pR2E1pHG1").
Proof. intros M a n a' n'. intros Hz H1 H2 i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply Hz. lia. Qed.
Lemma zeros_at_agree1 : ltac2:(TCodec.tc2 tcn__L5KnAU "Q8'Q;yR0%211'5y8%511%311pRN51'8'6&Kr3r1%3221&L&Jr2%2261%4261%:261'7r5&Q:%12F7%311r6%113%73E31p091pR:E1&G%13:D?r4%33<1Fp031p061pR<L1pR2M1pJO1pHQ01").
Proof. intros M M' a n. intros HA Hz i Hi. rewrite HA by lia. apply Hz. lia. Qed.
Lemma zeros_at_defined : ltac2:(TCodec.tc2 tcn__L5KnAU "E'Q;yR0%211'5y8%511%311p051'8&Gr3r2r1%43321&Er4%23165p041pR<:1pR2;1pH=1").
Proof. intros M a n. intros Hz i Hi. rewrite (Hz i Hi). discriminate. Qed.
Lemma u8_of_zeros : ltac2:(TCodec.tc2 tcn__L5KnAU "Q<'Q;yR0%211'5y8%511%311p051'8&Gr4r3r2%43321'6&Kz%2215&L%1278%6231&Jr5%221<%9281&N+2+R0%3221%;261%@261&FvQ9r7r6%>21I%54431Dp071p0B1p0J1pR:Q01pR<Q11pR2Q21pHQ41").
Proof. intros M a n i.
intros Hz Hi Hr. unfold L5.u8_at. cbn [rdn]. rewrite (Hz i Hi). reflexivity.
Qed.
Lemma word_to_le_bytes_1_mod : ltac2:(TCodec.tc2 tcn__L5KnAU "Q5'8'6&Kzr1%3221&L&N+2+R0%3221%5271%;271'7'2'Q;y8%211%411&:u1&Q:yR0r2%3221%6251(1&M+X0%2261%92>1(4%11?%73@31%E3@91p0G1pS0Q41").
Proof. intros z.
intros Hz. unfold word_to_le_bytes. cbn. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. change (bv_modulus 64) with (2^64). rewrite (Z.mod_small z (2^64)) by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma u8_of_KWord1_mod : ltac2:(TCodec.tc2 tcn__L5KnAU "QD'A'Q;yR0%211'5y8%511%311p051'B'8&CvQ9r7r6(=(?r5r4%3221u1r3%73321%<4;:91'7&Q<&@r8%221>%42K1%63D19r9%621?%82O1%:3H1=&F&J%12DH&M+X0%22F1%64M:41p081p0=1p0E1pRLQ31pR2Q41pR8Q61pRBQ61pR6Q81pHQ:1pDQC1").
Proof. intros E M b off e a v.
intros K Ha Hv. cbn [kentry_ok] in K. destruct K as (_ & _ & Rd). unfold L5.u8_at.
rewrite L5K.adenot_e, Ha in Rd. rewrite (BGU.word_of_unsigned _ _ Hv) in Rd.
rewrite word_to_le_bytes_1_mod in Rd. exact Rd. rewrite <- Hv. apply (BL.bvu_range (edenot E e)).
Qed.
End WithSegs.
End L5KA.
