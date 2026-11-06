(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AxSymExec3 AxSymExec3Sound.
From Stdlib Require Import FunctionalExtensionality.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AsanPopFree () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPopFree.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1S"; "1Some"; "1bool"; "1length"; "1list"; "1nat"; "1option"; "1pair"; "1prod"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "2or"]; ["3add"; "3mul"; "4lt"; "5firstn"; "5nth"; "5skipn"; "6Z"; "7Z_to_le_bytes"; "8store_ok"; "8word_to_le_bytes"; "9decode_any"; ":ALU_ADD"; ":ALU_SLL"; ":ALU_SRL"; ":ALU_XOR"; ":BC_LTU"]; [":Branch"; ":Op"; ":OpImm"; ":SZ4"; ":ShiftImm"; ":Store"; ":instr"; ";bvmap"; "<PW0"; "<PW1"; "<PW2"; "<PW3"; "<PW4"; "<PW5"; "<PW6"; "<PW7"]; ["<pf_bytes"; "<pf_mem"; "<popfree_spec"; "=wbytes"; ">msteps"; "?getr"; "?mkst"; "?rdn"; "@add"; "@div"; "@divide"; "@le"; "@lt"; "@mul"; "@of_nat"; "@opp"]; ["@pow"; "@sub"; "@to_nat"; "0a"; "0bs"; "0c"; "0d"; "0e"; "0fx"; "0i"; "0j"; "0k"; "0m"; "0mem"; "0n"; "0p"]; ["0r"; "0regs"; "0regs'"; "0rom"; "0s"; "0segs"; "ABV"; "AZ_to_bv"; "Abv"; "Abv_unsigned"; "0t"; "0v"; "0x"; "0z"]]).
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Section FPX_1. Context {fx : PropExec.FPState}.
Definition PW0 : bv 32 := 0x00465713.
Definition PW1 : bv 32 := 0xfff54793.
Definition PW2 : bv 32 := 0x00150513.
Definition PW3 : bv 32 := 0x00279793.
Definition PW4 : bv 32 := 0x00f587b3.
Definition PW5 : bv 32 := 0x00e7a023.
Definition PW6 : bv 32 := 0x01560633.
Definition PW7 : bv 32 := 0xff3562e3.
Lemma PD0 : ltac2:(TCodec.tc2 tcn__AsanPopFree "L'<'6'8'Q6'F%3221%511&J&Q8%211(1(7(Q4(M(RFy5+>(:%43321+<%63513y6+4%93216%<4;641%>4FE13%@2E1%K3EB1"). Proof. vm_refl. Qed.
Lemma PD1 : ltac2:(TCodec.tc2 tcn__AsanPopFree "M'<'6'8'Q6'F%3221%511&J&Q9%211(1(7(Q2(N(RFy5+?(:%43321+:%63513y<+SoO%93216%<4;641+4%?4GF21%A2F1%L3FC1"). Proof. vm_refl. Qed.
Lemma PD2 : ltac2:(TCodec.tc2 tcn__AsanPopFree "K'<'6'8'Q6'F%3221%511&J&Q:%211(1(7(Q2(K(RFy5+:(:%43321y<+1%73214%:49441+4%=4ED21%?2D1%J3DA1"). Proof. vm_refl. Qed.
Lemma PD3 : ltac2:(TCodec.tc2 tcn__AsanPopFree "K'<'6'8'Q6'F%3221%511&J&Q;%211(1(7(Q4(L(RFy5+?(:%43321y6+2%73214%:49441+4%=4ED21%?2D1%J3DA1"). Proof. vm_refl. Qed.
Lemma PD4 : ltac2:(TCodec.tc2 tcn__AsanPopFree "J'<'6'8'Q6'F%3221%511&J&Q<%211(1(7(Q1(K(RFy5+?(:%43321+;%63513%948313+4%<4DC21%>2C1%I3C@1"). Proof. vm_refl. Qed.
Lemma PD5 : ltac2:(TCodec.tc2 tcn__AsanPopFree "M'<'6'8'Q6'F%3221%511&J&Q=%211(1(7(Q5(Q3(RFy5+?(:%43321+>%63513y<z%93216%<4;641+4%?4GF21%A2F1%L3FC1"). Proof. vm_refl. Qed.
Lemma PD6 : ltac2:(TCodec.tc2 tcn__AsanPopFree "J'<'6'8'Q6'F%3221%511&J&Q>%211(1(7(Q1(K(RFy5+<(:%43321+E%63513%948331+4%<4DC21%>2C1%I3C@1"). Proof. vm_refl. Qed.
Lemma PD7 : ltac2:(TCodec.tc2 tcn__AsanPopFree "M'<'6'8'Q6'F%3221%511&J&Q?%211(1(7(Q0(O(RFy5+:(:%43321+C%63513y=+Wo4%93216%<4;641+4%?4GF21%A2F1%L3FC1"). Proof. vm_refl. Qed.
Fixpoint pf_mem (mem : word -> option byte) (e c s i : Z) (k : nat) : word -> option byte :=
match k with
| O => mem
| S k' => pf_mem (wbytes mem (Z_to_bv 64 (e - 4 * (i + 1))) (word_to_le_bytes 4 (Z_to_bv 64 (c / 16))))
e (c + s) s (i + 1) k'
end.
Fixpoint pf_bytes (c s : Z) (k : nat) : list byte :=
match k with
| O => []
| S k' => Z_to_le_bytes 4 ((c + Z.of_nat k' * s) / 16) ++ pf_bytes c s k'
end.
Lemma pf_bytes_length : ltac2:(TCodec.tc2 tcn__AsanPopFree "D'F'5'<&3'RHy8%211&Q@r3r2r1%43321%9261&Au4%2215%>3?41pTH@1pU:B1pT<C1").
Proof. intros c s k. induction k as [|k IH]; cbn [pf_bytes length]; [reflexivity|]. rewrite length_app, length_Z_to_le_bytes, IH. lia. Qed.
Lemma pf_bytes_nth : ltac2:(TCodec.tc2 tcn__AsanPopFree "QK'F'5';&QKzr2%3221&QL&QNr3%211%4261%:261&Bu4%22:1'<'RHy8%211&D&@&R2&QM+4r4%3221%511%721C&Q@r7r6r5%43321&RG%12AO%@4A831&G&QI&QH&R1%Q119+1%3221%421C%F21>%72@1+@%:221%<2Q31%N4OQ91?%Q33Q0?1p0Q51p0Q91pUFQE1pTFQG1pTHQG1pU:QI1pT<QJ1").
Proof.
intros c s k. induction k as [|k IH]; intros j t Hj Ht; [lia|].
cbn [pf_bytes]. rewrite Nat2Z.inj_succ in *.
destruct (Z.eq_dec j 0) as [->|Hj0].
- rewrite app_nth1 by (rewrite length_Z_to_le_bytes; lia). replace (Z.to_nat (4 * 0) + t)%nat with t by lia. f_equal. f_equal. f_equal. lia.
- rewrite app_nth2 by (rewrite length_Z_to_le_bytes; lia). rewrite length_Z_to_le_bytes.
replace (Z.to_nat (4 * j) + t - 4)%nat with (Z.to_nat (4 * (j - 1)) + t)%nat by lia.
rewrite IH by lia. f_equal. f_equal. f_equal. lia.
Qed.
Lemma pf_bytes_cell : ltac2:(TCodec.tc2 tcn__AsanPopFree "QE'F'5';&QKzr1%3221&QL&QNr2%211%4261%:261'<'4'RHy8%211%411&Cu4&E&R2&QM+4%221@%411&Q@r5r4r3%43321%;3?61%>3@=1&G&QI&QH&R1%N18+1%3221%421Q0%C21=%72?1+@%:221%<2J1%Q23M>1p0Q41pTFQA1pTHQA1pU:QC1pT<QD1").
Proof.
intros c s k. induction k as [|k IH]; intros j Hj; [lia|].
cbn [pf_bytes]. rewrite Nat2Z.inj_succ in *.
destruct (Z.eq_dec j 0) as [->|Hj0].
- replace (Z.to_nat (4 * 0)) with 0%nat by lia. rewrite skipn_O. rewrite firstn_app, length_Z_to_le_bytes, Nat.sub_diag, firstn_O, app_nil_r.
rewrite firstn_all2 by (rewrite length_Z_to_le_bytes; lia). f_equal. f_equal. lia.
- rewrite skipn_app, length_Z_to_le_bytes. rewrite skipn_all2 by (rewrite length_Z_to_le_bytes; lia). cbn [app].
replace (Z.to_nat (4 * j) - 4)%nat with (Z.to_nat (4 * (j - 1)))%nat by lia.
rewrite IH by lia. f_equal. f_equal. lia.
Qed.
Definition popfree_spec (SEGS : list Segment) (p : Z) : Prop :=
forall regs mem (i e c s n : Z),
getr regs 10%bv = Z_to_bv 64 i -> getr regs 11%bv = Z_to_bv 64 e -> getr regs 12%bv = Z_to_bv 64 c ->
getr regs 21%bv = Z_to_bv 64 s -> getr regs 19%bv = Z_to_bv 64 n ->
(0 <= i < n)%Z -> (4 * n <= e < 2 ^ 64)%Z -> (0 <= c)%Z -> (0 <= s)%Z -> (c + (n - i) * s < 2 ^ 64)%Z ->
store_ok SEGS mem (Z_to_bv 64 (e - 4 * n)) (Z.to_nat (4 * (n - i))) = true ->
exists regs',
msteps SEGS (mkst regs (Z_to_bv 64 p) mem (seg_rom SEGS))
(mkst regs' (Z_to_bv 64 (p + 32)) (wbytes mem (Z_to_bv 64 (e - 4 * n)) (pf_bytes c s (Z.to_nat (n - i)))) (seg_rom SEGS))
/\ getr regs' 10%bv = Z_to_bv 64 n /\ getr regs' 12%bv = Z_to_bv 64 (c + (n - i) * s)
/\ getr regs' 14%bv = Z_to_bv 64 ((c + (n - i - 1) * s) / 16) /\ getr regs' 15%bv = Z_to_bv 64 (e - 4 * n)
/\ (forall r : bv 5, r <> 10%bv -> r <> 12%bv -> r <> 14%bv -> r <> 15%bv -> getr regs' r = getr regs r).
Section PopFreeLoop.
Variable segs : list Segment.
Variable p : Z.
Hypothesis Hp : (28 <= p)%Z /\ (p + 32 < 2 ^ 64)%Z.
Hypothesis HF0 : fetch_word segs (Z_to_bv 64 p) = Some PW0.
Hypothesis HF1 : fetch_word segs (Z_to_bv 64 (p + 4)) = Some PW1.
Hypothesis HF2 : fetch_word segs (Z_to_bv 64 (p + 8)) = Some PW2.
Hypothesis HF3 : fetch_word segs (Z_to_bv 64 (p + 12)) = Some PW3.
Hypothesis HF4 : fetch_word segs (Z_to_bv 64 (p + 16)) = Some PW4.
Hypothesis HF5 : fetch_word segs (Z_to_bv 64 (p + 20)) = Some PW5.
Hypothesis HF6 : fetch_word segs (Z_to_bv 64 (p + 24)) = Some PW6.
Hypothesis HF7 : fetch_word segs (Z_to_bv 64 (p + 28)) = Some PW7.
Definition iter_regs (regs : bvmap 5 word) (i e c s : Z) : bvmap 5 word :=
regupd (regupd (regupd (regupd regs 14 (Z_to_bv 64 (c / 16))) 10 (Z_to_bv 64 (i + 1)))
15 (Z_to_bv 64 (e - 4 * (i + 1)))) 12 (Z_to_bv 64 (c + s)).
Ltac red_if :=
repeat match goal with
| |- context [if bv_eqb ?a ?b then ?x else ?y] =>
let v := eval vm_compute in (bv_eqb a b) in
lazymatch v with
| true => change (if bv_eqb a b then x else y) with x
| false => change (if bv_eqb a b then x else y) with y
end
end.
Lemma u64_of_Z : ltac2:(TCodec.tc2 tcn__AsanPopFree "G'F';&QKzr1%3221&QL&R0+2+R0%3221%5271%;271'<&RIyR0&RGr2%2231%5241%73D13p091pULF1").
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. lia. Qed.
Ltac gr := repeat first [ rewrite getr_same by reg_neq_tac | rewrite getr_other by reg_neq_tac ].
Lemma pf_iter : forall regs mem rom i e c s n,
getr regs 10 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 e -> getr regs 12 = Z_to_bv 64 c ->
getr regs 21 = Z_to_bv 64 s -> getr regs 19 = Z_to_bv 64 n ->
(0 <= i)%Z -> (i + 1 <= n)%Z -> (4 * n <= e)%Z -> (e < 2 ^ 64)%Z ->
(0 <= c)%Z -> (0 <= s)%Z -> (c + s < 2 ^ 64)%Z ->
RiscvSemantics.store_ok segs mem (Z_to_bv 64 (e - 4 * (i + 1))) 4 = true ->
exists regs',
msteps segs (mkst regs (Z_to_bv 64 p) mem rom)
(mkst regs' (Z_to_bv 64 (if (i + 1 <? n)%Z then p else p + 32))
(wbytes mem (Z_to_bv 64 (e - 4 * (i + 1))) (word_to_le_bytes 4 (Z_to_bv 64 (c / 16)))) rom)
/\ getr regs' 10 = Z_to_bv 64 (i + 1) /\ getr regs' 11 = Z_to_bv 64 e /\ getr regs' 12 = Z_to_bv 64 (c + s)
/\ getr regs' 21 = Z_to_bv 64 s /\ getr regs' 19 = Z_to_bv 64 n
/\ getr regs' 14 = Z_to_bv 64 (c / 16) /\ getr regs' 15 = Z_to_bv 64 (e - 4 * (i + 1))
/\ (forall r : reg, r <> 10 -> r <> 12 -> r <> 14 -> r <> 15 -> getr regs' r = getr regs r).
Proof.
intros regs mem rom i e c s n H10 H11 H12 H21 H19 Hi Hin Hne He Hc Hs Hcs Hok.
destruct Hp as [Hp0 Hp1].
assert (V14 : v_srli (Z_to_bv 64 c) (bv_unsigned (4 : bv 6)) = Z_to_bv 64 (c / 16)).
{ unfold v_srli. rewrite u64_of_Z by lia. change (bv_unsigned (4 : bv 6)) with 4%Z.
rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
assert (V15a : v_xori (Z_to_bv 64 i) (bv_signed (4095 : bv 12)) = Z_to_bv 64 (2 ^ 64 - 1 - i)).
{ unfold v_xori. rewrite u64_of_Z by lia. change (bv_wrap 64 (bv_signed (4095 : bv 12))) with (2 ^ 64 - 1)%Z.
rewrite AX2S.lxor_ones64 by lia. reflexivity. }
assert (V10 : v_addi (Z_to_bv 64 i) (bv_signed (1 : bv 12)) = Z_to_bv 64 (i + 1)).
{ change (bv_signed (1 : bv 12)) with 1%Z. apply v_addi_lit. }
assert (V15b : v_slli (Z_to_bv 64 (2 ^ 64 - 1 - i)) (bv_unsigned (2 : bv 6)) = Z_to_bv 64 (2 ^ 66 - 4 - 4 * i)).
{ unfold v_slli. rewrite u64_of_Z by lia. change (bv_unsigned (2 : bv 6)) with 2%Z.
rewrite Z.shiftl_mul_pow2 by lia. apply bv_eq. rewrite !Z_to_bv_unsigned. f_equal. lia. }
assert (V15c : v_add (Z_to_bv 64 e) (Z_to_bv 64 (2 ^ 66 - 4 - 4 * i)) = Z_to_bv 64 (e - 4 * (i + 1))).
{ unfold v_add. rewrite u64_of_Z by lia. apply bv_eq. rewrite !Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
rewrite Z.add_mod_idemp_r by lia.
replace (e + (2 ^ 66 - 4 - 4 * i))%Z with ((e - 4 * (i + 1)) + 4 * 2 ^ 64)%Z by lia.
rewrite Z_mod_plus_full. reflexivity. }
assert (Vst : v_addi (Z_to_bv 64 (e - 4 * (i + 1))) (bv_signed (0 : bv 12)) = Z_to_bv 64 (e - 4 * (i + 1))).
{ change (bv_signed (0 : bv 12)) with 0%Z. rewrite v_addi_lit. f_equal. lia. }
assert (V12 : v_add (Z_to_bv 64 c) (Z_to_bv 64 s) = Z_to_bv 64 (c + s)).
{ unfold v_add. rewrite !u64_of_Z by lia. reflexivity. }
eexists. split.
- eapply mst_step; [reflexivity | eapply (step_srli segs); [exact HF0 | reflexivity | exact PD0] |].
red_if. rewrite v_addi_lit, H12, V14.
eapply mst_step; [reflexivity | eapply (step_xori segs); [exact HF1 | reflexivity | exact PD1] |].
red_if. rewrite v_addi_lit. replace (p + 4 + 4)%Z with (p + 8)%Z by lia. gr. rewrite H10, V15a.
eapply mst_step; [reflexivity | eapply (step_addi segs); [exact HF2 | reflexivity | exact PD2] |].
red_if. rewrite v_addi_lit. replace (p + 8 + 4)%Z with (p + 12)%Z by lia. gr. rewrite H10, V10.
eapply mst_step; [reflexivity | eapply (step_slli segs); [exact HF3 | reflexivity | exact PD3] |].
red_if. rewrite v_addi_lit. replace (p + 12 + 4)%Z with (p + 16)%Z by lia. gr. rewrite V15b.
eapply mst_step; [reflexivity | eapply (step_add segs); [exact HF4 | reflexivity | exact PD4] |].
red_if. rewrite v_addi_lit. replace (p + 16 + 4)%Z with (p + 20)%Z by lia. gr. rewrite H11, V15c.
eapply mst_step; [reflexivity | eapply (step_sw_val segs); [exact HF5 | reflexivity | exact PD5 | gr; rewrite Vst; exact Hok] |].
rewrite v_addi_lit. replace (p + 20 + 4)%Z with (p + 24)%Z by lia. gr. rewrite Vst.
eapply mst_step; [reflexivity | eapply (step_add segs); [exact HF6 | reflexivity | exact PD6] |].
red_if. rewrite v_addi_lit. replace (p + 24 + 4)%Z with (p + 28)%Z by lia. gr. rewrite H12, H21, V12.
destruct (Z.ltb (i + 1) n) eqn:Hlt.
+ eapply mst_step; [reflexivity | eapply (step_bltu_tk segs); [exact HF7 | reflexivity | exact PD7 | ] |].
{ gr. rewrite H19. unfold c_ltu, bv_ltu. rewrite !u64_of_Z by lia. exact Hlt. }
rewrite btgt_lit. change (bv_signed (8164 : bv 13)) with (-28)%Z.
replace (p + 28 + -28)%Z with p by lia. apply mst_refl.
+ eapply mst_step; [reflexivity | eapply (step_bltu_ft segs); [exact HF7 | reflexivity | exact PD7 | ] |].
{ gr. rewrite H19. unfold c_ltu, bv_ltu. rewrite !u64_of_Z by lia. exact Hlt. }
rewrite v_addi_lit. replace (p + 28 + 4)%Z with (p + 32)%Z by lia. apply mst_refl.
- gr. rewrite H11, H21, H19.
repeat (split; [reflexivity|]).
intros r Hr10 Hr12 Hr14 Hr15. rewrite !getr_other by assumption. reflexivity.
Qed.
Lemma pf_loop : ltac2:(TCodec.tc2 tcn__AsanPopFree "V?'5&Q7y5'RHyR0%211%5241'6y8%611%311p061'F'<r1&QHr5&QN(0r9%211%411%7261%:3;91&QE(RF+:(:%33J21%52:1&RGr6%22L1%D3L41r:+;%;3Q219%=231%I3Q116r;+<%@3Q71>%B231%N3Q61;r<+E%E3Q<1C%G231%Q33Q;1@r=+C%J3QA1H%L231%Q83Q@1E&QKz%221A&QM+4r8%3221%721F&QL&R0+2+R0%3221%52G1%>2=Hr>rD%QE11%QG11%@21H%QK251%=219';rB%H21R0%A2R1:%4221'2&HvRErE&R1r2+1%R9221%Q02O1%52=1%QM2RG1u4%;4:921(9%RB3>21p0@1pTFRE1'='QD&QFvR8rFvR?%R:2S41%55431EQ3+Q0%RL241%R>2S81&QArAr@rCrG%S011%66OQ65431%@5?S681Q>%B3Q2<1%RN2S8RJr?%RJ2SD1%S<3SD31%S22S<RF%RM2SGQ>%S?3SG21%S52S?RD%S=1<%R621@%SA2B1%S32SM1%SE3SM51%S;2SERE%S62T0E%SH3T021%S>2SHRC%SJ3T21?+>%S@3T71S>%SB2SL1&QI%SK1K%RD21N%SO2Q01+@%5221%SC2T=1%T53T=81+?%SK3TB1SI%SM2T71%RM2RLO%R22R:1%SJ2TD1%T<3TD41%TG1TH&>%T?32T>T0%211%TA34R8SE%411r3%TD371H%711r4%TG3:1@%:11%T>2T7TFrK%T@21TH%TL3U431p051p091p0=1p0@1pU2D1%S32F1%S42N1%S52Q:1%S62Q=1%S72QA1%S82QH1%S92QL1%S:2R11qU6UA1%RF2UB1p0RH1p0S?1p0SG1p0SH1p0SJ1p0T11p0T71p0T;1p0TA1p0TG1p0TM1p0U31p0U>1pTNUJ1pU:UK1pT<UL1pT@UM1pTDUN1pU8V01pTLV11pU4V71pTHV>1").
Proof.
induction k as [|k IH]; intros regs mem rom i e c s n Hn H10 H11 H12 H21 H19 Hi Hne He Hc Hs Hcs Hok.
-
change (Z.of_nat 1) with 1%Z in *. change (Z.of_nat 0) with 0%Z. rewrite Z.mul_1_l in *. rewrite Z.mul_0_l, Z.add_0_r.
assert (Hs1 : (c + s < 2 ^ 64)%Z) by lia.
destruct (pf_iter regs mem rom i e c s n H10 H11 H12 H21 H19 Hi ltac:(lia) Hne He Hc Hs Hs1
(Hok i ltac:(lia))) as (regs' & Hms & R10 & R11 & R12 & R21 & R19 & R14 & R15 & Rothers).
exists regs'. destruct (Z.ltb_spec (i + 1) n); [lia|].
cbn [pf_mem].
split; [exact Hms|]. rewrite R10, R11, R12, R21, R19, R14, R15. subst n.
repeat (split; [reflexivity|]). exact Rothers.
-
rewrite Nat2Z.inj_succ in Hn, Hcs |- *. rewrite Nat2Z.inj_succ in Hcs |- *.
assert (Hks : (0 <= Z.of_nat k * s)%Z) by (apply Z.mul_nonneg_nonneg; lia).
assert (Hs1 : (c + s < 2 ^ 64)%Z) by lia.
destruct (pf_iter regs mem rom i e c s n H10 H11 H12 H21 H19 Hi ltac:(lia) Hne He Hc Hs Hs1
(Hok i ltac:(lia))) as (regs1 & Hms1 & R10 & R11 & R12 & R21 & R19 & R14 & R15 & Rothers).
destruct (Z.ltb_spec (i + 1) n); [|lia].
destruct (IH regs1 (wbytes mem (Z_to_bv 64 (e - 4 * (i + 1))) (word_to_le_bytes 4 (Z_to_bv 64 (c / 16)))) rom
(i + 1)%Z e (c + s)%Z s n ltac:(rewrite Nat2Z.inj_succ; lia) R10 R11 R12 R21 R19 ltac:(lia) Hne He ltac:(lia) Hs
ltac:(rewrite Nat2Z.inj_succ; lia))
as (regs2 & Hms2 & S10 & S11 & S12 & S21 & S19 & S14 & S15 & Sothers).
{ intros j Hj. eapply store_ok_mono; [apply wbytes_grows | apply Hok; lia]. }
exists regs2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
rewrite S10, S11, S12, S21, S19, S14, S15.
split; [reflexivity|]. split; [reflexivity|]. split; [f_equal; lia|]. split; [reflexivity|]. split; [reflexivity|].
split; [f_equal; f_equal; lia|]. split; [reflexivity|].
intros r A B C D. rewrite (Sothers r A B C D). apply Rothers; assumption.
Qed.
Lemma pf_wbytes_inside : ltac2:(TCodec.tc2 tcn__AsanPopFree "QL'4'RHy8%211%411yR0%511'6%115p031&QK&QH&RIr2%2291&QN&3r4%22?1%411%9261&R0+2+R0%3221%?251';r3%@2G1%C21?&QLr5%@2M1%B11%G261%52E1%:271'<&QCr6%249G1=(1&D&R2&R1%Q12Q8L%22B1%411&RGz%22Q@1%94Q@4<1%;2QA1%@3Q==1p0B1p0N1pUJQB1pT8QC1pTJQA1pT:QG1").
Proof.
induction bs as [|b rest IH]; intros m a x Hnw Hx; [cbn in Hx; lia|].
cbn [wbytes length] in *.
destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
- assert (x = a) by (apply bv_eq; exact Heq). subst x.
rewrite Z.sub_diag. cbn [Z.to_nat nth].
destruct rest as [|b' rest'].
+ cbn [wbytes]. rewrite bv_eqb_refl. reflexivity.
+ cbn [length] in Hnw. rewrite wbytes_below.
* rewrite bv_eqb_refl. reflexivity.
* rewrite u_add1 by lia. cbn [length]. lia.
* rewrite u_add1 by lia. lia.
- assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
rewrite (IH _ (a + 1)%bv) by (rewrite Hu1; lia).
rewrite Hu1.
replace (Z.to_nat (bv_unsigned x - bv_unsigned a))
with (S (Z.to_nat (bv_unsigned x - (bv_unsigned a + 1)))) by lia.
reflexivity.
Qed.
Lemma pf_wbytes_outside : ltac2:(TCodec.tc2 tcn__AsanPopFree "QA'4'RHy8%211%411yR0%511'6%115p031&QK&QH&RIr2%2291&QN&3r4%22?1%411%9261&R0+2+R0%3221%?251'?&QLr3%A2H1%32@1r5%@2M1%B11%G251%I21E%:261'<&QCr6%249G1<%:1=%53Q221p071p0C1pUJQ71pT8Q81pTJQ61pT:Q<1").
Proof.
intros bs m a x Hnw [Hlt|Hge].
- apply wbytes_below; assumption.
- apply wbytes_above; assumption.
Qed.
Lemma pf_mem_frame : ltac2:(TCodec.tc2 tcn__AsanPopFree "R2'5'RHyR0%211'6y8%511%311p051'F&QKzr2%3221&QM+4&QHr3&QNr8%211%5241%8271r6%>221&QLr7&R0+2+R0%3221%6251'?&RIr4%22Q11&R1r5r:%E11%H231%K2J1%62G1%B281%N2M7%92J1%Q421;%?241'<&QAr9r;%37>2Q1JM1?%?1@%63Q?21p081p0I1p0Q11p0Q=1pT8QH1pTDQC1pU:QD1pT<QE1pT@QF1pTLQH1pTHR11").
Proof.
induction k as [|k IH]; intros mem e c s i a Hi Hk He Ha; [reflexivity|].
cbn [pf_mem]. rewrite IH by lia.
apply pf_wbytes_outside; rewrite length_N_to_le_bytes, u64_of_Z by lia; cbn [Z.of_nat]; lia.
Qed.
Lemma word_to_le_bytes4_Z : ltac2:(TCodec.tc2 tcn__AsanPopFree "B'F'<'4'RHy8%211%411&Iu4&RGyR0r1%3221%6251&G%1274%?3:31pUHA1").
Proof. intros v. unfold word_to_le_bytes. rewrite Z_to_bv_unsigned. apply Z_to_le_bytes_wrap. cbn; lia. Qed.
Lemma pf_mem_cell : ltac2:(TCodec.tc2 tcn__AsanPopFree "RI'5'RHyR0%211'6y8%511%311p051'F&QKzr3%3221&QM+4&QHr4&QNr9%211%5241%8271r7%>221&QLr8&R0+2+R0%3221%6251';r5%H2G1r;%B11%<241%6241&Bu4%2281'<&QAr<r:r=&RG&R1%O13%Q22H1%Q52Q41%42A1%Q72Q6N%Q6221r6%Q611%Q9231%;2QH1%@7?H>Q8Q1=1(1&D&G&QI+1%A2@1%B21Q;%QE21Q@%QD2G1+@%7221%92O1%I2R3QM%<4R3B21%>2R41%Q13R4@1p0Q31p0Q71p0Q?1p0QG1p0R31pUFRA1pTFR91pTDR:1pU:R;1pT<R<1pT@R=1pTLR?1pTHRH1").
Proof.
induction k as [|k IH]; intros mem e c s i j t Hi Hk He Hj Ht; [lia|].
rewrite Nat2Z.inj_succ in *.
cbn [pf_mem].
destruct (Z.eq_dec j (Z.of_nat k)) as [->|Hne].
-
rewrite pf_mem_frame; [| lia | lia | lia | rewrite u64_of_Z by lia; lia].
rewrite pf_wbytes_inside; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; [| cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia].
rewrite word_to_le_bytes4_Z. f_equal. f_equal; [lia|]. f_equal. f_equal. lia.
- replace (e - 4 * (i + Z.succ (Z.of_nat k)) + 4 * j + Z.of_nat t)%Z
with (e - 4 * ((i + 1) + Z.of_nat k) + 4 * j + Z.of_nat t)%Z by lia.
rewrite (IH _ e (c + s)%Z s (i + 1)%Z j t) by lia.
f_equal. f_equal. f_equal. f_equal. lia.
Qed.
Lemma pf_mem_rdn : ltac2:(TCodec.tc2 tcn__AsanPopFree "RE'5'RHyR0%211'6y8%511%311p051'F&QKzr2%3221&QM+4&QHr3&QNr8%211%5241%8271r6%>221&QLr7&R0+2+R0%3221%6251';r4%H2G1r:%B11%<241%6241'<'4%11Q3%Q611&QGvRE&QAr9r;%36=2MFI1&RG&R1%Q114%Q42M1%Q72Q61%4281r5%Q:2Q91%Q9231%92QH1u4%A4@<21(1&G&QI+1%?2>1%@21;%QE21Q9%QD2QA1+@%7221%92<1%;2O1%Q23O=1p0Q41p0Q<1p0QD1p0R01pTFR51pTDR61pU:R71pT<R81pT@R91pTLR;1pTHRD1").
Proof.
intros k mem e c s i j Hi Hk He Hj.
apply AX2S.rdn_pointwise; [apply length_Z_to_le_bytes | rewrite u64_of_Z by lia; cbn [Z.of_nat]; lia |].
intros t Ht. rewrite u64_of_Z by lia. apply pf_mem_cell; assumption.
Qed.
Lemma pf_cell_linear : ltac2:(TCodec.tc2 tcn__AsanPopFree "Q1'F&QJ+@r3%3221'<&QI&QHr5&QM&R1+1%2291r2%4221r4%7221%:291%<21@%:274%=2<1%?21C&QO%A28E%211%@2<1%C251%F3K91p0H1pTFM1pTHN1pU:O1pT<Q01").
Proof.
intros c s k j [q ->].
replace (c + (k - 1 - j) * (q * 16))%Z with ((c + (k - 1) * (q * 16)) + (- (j * q)) * 16)%Z by lia.
rewrite Z.div_add by lia. rewrite Z.div_mul by lia. lia.
Qed.
Theorem popfree_loop_run : ltac2:(TCodec.tc2 tcn__AsanPopFree "V?&Q7y5'RHyR0%211%5241'6y8%611%311p061'F'<&QEr8(RF+:(:%33A21%6251&RGr5%22C1%;3C41r9+;%;3I19%>231%@3H16r:+<%@3N1>%C231%E3M1;r;+E%E3Q31C%H231%J3Q21@r<+C%J3Q81H%M231%O3Q71E&QKz%221A&QLr7%22?1&QM+4%221Q6%921C&R0+2+R0%3221%;2C1%?2>D&QHr>&R1r@%22I1r=%@221%7261%E21;'5r2%K2J1r3&QN%114%?231rD%?2>1%L2K1%Q3241'2&HvRErGrA%Q32Q21%H2:1r4%L221%R52RF1%94871B(9%R@3<21p0>1p0G1pTJJ1pT>RE1'=';'QD&QFvR8rFvR?%RD2S51rE%655421Nr1+Q0%QA261%RJ2S;1&QArBrC&R2r?%QF213%311%76=6Q2QG51%C5B<91Q;%E3Q6>1%S<2>S7%S62SG7%S?3SG21%S?2AS2%S92SJ=%SB3SJ21%SB2DS0%R>2<R1%R52Q=1%S>2SO1%SG3SO41%SG2IS0%SA2T2R6%SJ3T221%SJ2LRN%SL3T41>+>%SK3T91SI%SN2Q01&QI+1%R@2J1%RM21R@%RD2QL1+@%6221%SO2T@1%T83T@91+?%T73TE1T5%T:2Q<1%S62S5Q5%RK2Q91%T62TG1%T?3TG41%TJ1TK&>%TB32QCT<%211%TD34RJT1%411%TF36RJH%611%TH38R=>%811r6%TJ21TBrK%TL21TD%TN3U631p061p091p0<1p0?1pU2C1%R>2E1%R?2M1%R@2Q:1%RA2Q=1%RB2QA1%RC2QG1%RD2QK1%RE2QO1qU6UC1%RH2UD1p0RJ1p0SG1p0T11p0T21p0T41p0T:1p0T?1p0TC1p0TG1p0TM1p0U31p0U91p0U?1pTNUL1pU:UM1pT<UN1pT@UO1pTDV01pU8V21pTLV31pU4V91").
Proof.
intros regs mem rom i e c s n H10 H11 H12 H21 H19 Hi Hin Hne He Hc Hs Hcs Hwr.
destruct (Z.to_nat (n - i)) as [|k] eqn:Hk; [lia|].
assert (Hkz : (Z.of_nat (S k) = n - i)%Z) by lia.
destruct (pf_loop k regs mem rom i e c s n ltac:(lia) H10 H11 H12 H21 H19 Hi Hne He Hc Hs ltac:(rewrite Hkz; exact Hcs))
as (regs' & Hms & R10 & R11 & R12 & R21 & R19 & R14 & R15 & Ro).
{ intros j Hj. replace (e - 4 * (j + 1))%Z with (e - 4 * n + 4 * (n - j - 1))%Z by lia. apply Hwr; lia. }
exists regs'. rewrite R10, R11, R12, R21, R19, R14, R15, Hkz.
replace (Z.of_nat k) with (n - i - 1)%Z by lia.
repeat (split; [first [exact Hms | reflexivity]|]). exact Ro.
Qed.
Lemma pf_mem_wbytes : ltac2:(TCodec.tc2 tcn__AsanPopFree "QK'5'RHyR0%211'6y8%511%311p051'F&QKzr1%3221&QM+4&QHr2&QNr7%211%5241%8271r5%>221&QLr6&R0+2+R0%3221%6251'<&QAr8r4r9%463B;>21&QC&RG&R1%G15%J271%M2L1%42I1%62Q;1&Q@%13EH;%:3>31%A3Q9<1p0C1p0K1p0Q71pTDQ<1pU:Q=1pT<Q>1pT@Q?1pTLQA1pTHQJ1").
Proof.
intros k mem e c s i Hi Hk He. apply functional_extensionality. intros a.
pose proof (u64_range a) as Ra. pose proof (pf_bytes_length c s k) as L.
destruct (Z_lt_le_dec (bv_unsigned a) (e - 4 * (i + Z.of_nat k))) as [Hlt|Hge];
[|destruct (Z_lt_le_dec (bv_unsigned a) (e - 4 * i)) as [Hlt2|Hge2]].
- rewrite pf_mem_frame by lia. symmetry. apply pf_wbytes_outside; rewrite L, u64_of_Z by lia; lia.
- set (base := (e - 4 * (i + Z.of_nat k))%Z) in *.
set (j := ((bv_unsigned a - base) / 4)%Z). set (t := Z.to_nat ((bv_unsigned a - base) mod 4)).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (Hj : (0 <= j < Z.of_nat k)%Z) by (subst j base; lia).
assert (Ht : (t < 4)%nat) by (subst t; lia).
assert (Ha : a = Z_to_bv 64 (base + 4 * j + Z.of_nat t)).
{ apply bv_eq. rewrite u64_of_Z by (subst j t base; lia). subst j t base. lia. }
rewrite Ha. subst base. rewrite (pf_mem_cell k mem e c s i j t Hi Hk He Hj Ht).
rewrite pf_wbytes_inside; rewrite ?L, ?u64_of_Z by lia; [|lia|lia].
replace (Z.to_nat (e - 4 * (i + Z.of_nat k) + 4 * j + Z.of_nat t - (e - 4 * (i + Z.of_nat k)))) with (Z.to_nat (4 * j) + t)%nat by lia.
symmetry. f_equal. apply pf_bytes_nth; assumption.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
- rewrite pf_mem_frame by lia. symmetry. apply pf_wbytes_outside; rewrite L, u64_of_Z by lia; lia.
Qed.
Theorem popfree_spec_of_code : ltac2:(TCodec.tc2 tcn__AsanPopFree "4&QBvREvR?%3221").
Proof.
intros regs mem i e c s n H10 H11 H12 H21 H19 Hin He Hc Hs Hcs Hok.
destruct (popfree_loop_run regs mem (seg_rom segs) i e c s n H10 H11 H12 H21 H19
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hc Hs Hcs) as (regs' & Hms & R10 & R11 & R12 & R21 & R19 & R14 & R15 & Ro).
{ intros d m Hd Hdm. eapply (store_ok_sub segs mem _ _ (Z.to_nat (4 * (n - i))) m); [| exact Hok | |]; rewrite !u64_of_Z by lia; lia. }
exists regs'. rewrite (pf_mem_wbytes (Z.to_nat (n - i)) mem e c s i) in Hms by lia.
replace (i + Z.of_nat (Z.to_nat (n - i)))%Z with n in Hms by lia.
split; [exact Hms|]. split; [exact R10|]. split; [exact R12|]. split; [exact R14|]. split; [exact R15|]. exact Ro.
Qed.
End PopFreeLoop.
End FPX_1.
