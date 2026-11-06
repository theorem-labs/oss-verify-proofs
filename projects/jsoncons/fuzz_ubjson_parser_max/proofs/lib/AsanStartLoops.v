(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StoreOk Hoare.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AsanStartLoops () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanStartLoops.FPX_2.EnvLoop."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanStartLoops.FPX_2.PnLoop."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "3add"; "4le"]; ["5skipn"; "6Z"; "7store_ok"; "7word_to_le_bytes"; "8bvmap"; "0M"; "0M'"; "0M0"; "9env_post"; ":cellrel"; ":pn_post"; ";byte_at"; ";wbytes"; "<msteps"; "=btgt"; "=c_eq"]; ["=getr"; "=mkst"; "=rdn"; "=v_addi"; "0SEGS"; ">add"; ">eqb"; ">le"; ">lt"; ">mul"; ">of_nat"; ">pow"; "0a"; "0b"; "0e"; "0envc"]; ["0fx"; "0j"; "0k"; "0l2"; "0n"; "0p"; "0pn"; "0regs"; "0regs'"; "0rom"; "0s"; "?BV"; "?Z_to_bv"; "?bv"; "?bv_signed"; "?bv_unsigned"]; ["0v"; "0x"; "0z"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.
Lemma u_lit : ltac2:(TCodec.tc2 tcn__AsanStartLoops "G'A':&Q7zr1%3221&Q8&Q;+2+R0%3221%5271%;271';&QOyR0&QLr2%2231%5241%73D13p091pT6F1").
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. Qed.
Lemma v_addi_lit : ltac2:(TCodec.tc2 tcn__AsanStartLoops "M'A':&Q7zr2%3221&Q8&Q;+2+R0%3221%5271%;271';'QMyR0%211&Q3&QLr3%2251%421A&Q5%124C%6291%<3941p0>1pS6K1pRJL1").
Proof. intros a k Ha. unfold v_addi. rewrite u_lit by lia. reflexivity. Qed.
Lemma btgt_lit : ltac2:(TCodec.tc2 tcn__AsanStartLoops "M'A':&Q7zr2%3221&Q8&Q;+2+R0%3221%5271%;271';'QMyR0%211&N&QLr3%2251%421A&Q5%124C%6291%<3941p0>1pS6K1pRJL1").
Proof. intros a k Ha. unfold btgt. apply v_addi_lit. exact Ha. Qed.
Lemma c_eq_lit : ltac2:(TCodec.tc2 tcn__AsanStartLoops "N'A':&Q7zr2%3221&Q8&Q;+2+R0%3221%5271%;271';'1&O&QLyR0r4%3221r3%5241%7231&Q6%1264%<3;31p0>1p0?1pRLL1pRJM1").
Proof. intros a b Ha Hb. unfold c_eq, bv_eqb. rewrite !u_lit by lia. reflexivity. Qed.
Lemma reg_neq : ltac2:(TCodec.tc2 tcn__AsanStartLoops "O'A':&Q7zr2%3221&Q8+Q0%2241%8241&=';r4r3%33>21%511'QMy5%211&QLr5%2241/014%426;%=3621%?11p0;1p0B1p0C1pRLM1pRJN1").
Proof.
intros a b Ha Hb Hne Heq. apply (f_equal bv_unsigned) in Heq.
rewrite !Z_to_bv_unsigned in Heq. unfold bv_wrap in Heq. change (bv_modulus 5) with 32 in Heq.
rewrite !Z.mod_small in Heq by lia. lia.
Qed.
End FPX_1.
Ltac rif :=
repeat match goal with
| |- context [if bv_eqb ?a ?b then ?u else ?v] =>
lazymatch a with
| @BV _ _ _ =>
lazymatch b with
| @BV _ _ _ =>
let c := eval vm_compute in (bv_eqb a b) in
lazymatch c with
| true => change (if bv_eqb a b then u else v) with u
| false => change (if bv_eqb a b then u else v) with v
end
end
end
end.
Ltac pc_is v :=
lazymatch goal with
| |- msteps _ (mkst _ (Z_to_bv 64 ?q) _ _) _ => first [constr_eq q v | replace q with v by lia]
end.
Section FPX_2. Context {fx : PropExec.FPState}.
Lemma signed12_0 : ltac2:(TCodec.tc2 tcn__AsanStartLoops "=';'A&QNy<(QKz(9%33421'QM%116/031%9281%<3;17"). Proof. reflexivity. Qed.
Lemma signed12_1 : ltac2:(TCodec.tc2 tcn__AsanStartLoops "=';'A&QNy<(QK+1(9%33421'QM%116/031%9281%<3;17"). Proof. reflexivity. Qed.
Lemma signed12_8 : ltac2:(TCodec.tc2 tcn__AsanStartLoops "=';'A&QNy<(QK+8(9%33421'QM%116/031%9281%<3;17"). Proof. reflexivity. Qed.
Lemma signed12_m1 : ltac2:(TCodec.tc2 tcn__AsanStartLoops ">';'A&QNy<(QK+SoO(9%33421'QM%116/031%9281-1%=3<21"). Proof. reflexivity. Qed.
Lemma signed13_m8 : ltac2:(TCodec.tc2 tcn__AsanStartLoops ">';'A&QNy=(QK+WoH(9%33421'QM%116/031%9281-8%=3<21"). Proof. reflexivity. Qed.
Lemma signed13_m12 : ltac2:(TCodec.tc2 tcn__AsanStartLoops ">';'A&QNy=(QK+WoD(9%33421'QM%116/031%9281-<%=3<21"). Proof. reflexivity. Qed.
Section EnvLoop.
Variable SEGS : list Segment.
Variable x : Z.
Variables w1 w2 w3 : bv 32.
Hypothesis Hx : 0 <= x /\ x + 12 < 2 ^ 64.
Hypothesis F1 : fetch_word SEGS (Z_to_bv 64 x) = Some w1.
Hypothesis F2 : fetch_word SEGS (Z_to_bv 64 (x + 4)) = Some w2.
Hypothesis F3 : fetch_word SEGS (Z_to_bv 64 (x + 8)) = Some w3.
Hypothesis E1 : is_ecall w1 = false.
Hypothesis E2 : is_ecall w2 = false.
Hypothesis E3 : is_ecall w3 = false.
Hypothesis D1 : decode_any w1 = Some (Load SZ8 true 10 9 0, 4%Z).
Hypothesis D2 : decode_any w2 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Hypothesis D3 : decode_any w3 = Some (Branch BC_NE 10 0 8184, 4%Z).
Variable M : word -> option byte.
Variable rom : word -> option byte.
Variable e : Z.
Variable envc : nat.
Variable ptr : nat -> word.
Hypothesis He : 0 <= e /\ e + 8 * Z.of_nat envc + 16 < 2 ^ 64.
Hypothesis Rk : forall k, (k < envc)%nat ->
rdn SEGS M (Z_to_bv 64 (e + 8 * Z.of_nat k)) 8 = Some (word_to_le_bytes 8 (ptr k))
/\ bv_unsigned (ptr k) <> 0.
Hypothesis Rn : rdn SEGS M (Z_to_bv 64 (e + 8 * Z.of_nat envc)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Definition env_post (regs regs' : bvmap 5 word) : Prop :=
getr regs' 9 = Z_to_bv 64 (e + 8 * Z.of_nat envc + 8)
/\ getr regs' 10 = Z_to_bv 64 0
/\ regs_agree (fun r => r = 9%bv \/ r = 10%bv) regs regs'.
Lemma env_loop : ltac2:(TCodec.tc2 tcn__AsanStartLoops "QK'5&Dy5'QMyR0%211%5241';&>r2r3%3221vQ?%63=21&Q0(QK+9(9%33@21%52:1&QL&Q5vQ>&Q9+8&Q:%11@%4231%7261%92I1%G3I;1'<':'MvQ4&Q1vQ@r4vR1%C2Q31vEvQI%7565321r1+<%H271%J2Q:1%<5;4176%?3>61&H%12=7%C231qSBQ>1%F2Q?1p0H1p0Q:1pS@QB1pS6QI1pS:QJ1").
Proof.
induction n as [|n IH]; intros k regs Hkn H9.
-
assert (k = envc) by lia. subst k.
eexists. split.
+ eapply mst_step; [reflexivity| |].
{ eapply (step_ld SEGS regs _ M rom w1 10 9 0 _ (Z_to_bv 64 0) F1 E1 D1).
- rewrite H9, signed12_0, v_addi_lit by lia. rewrite Z.add_0_r. exact Rn.
- apply bytes_le_to_Z_8. }
rif. rewrite v_addi_lit by lia. pc_is (x + 4).
eapply mst_step; [reflexivity| |].
{ eapply (step_addi SEGS _ _ M rom w2 9 9 8 F2 E2 D2). }
rif. rewrite v_addi_lit by lia. pc_is (x + 8). rewrite signed12_8.
rewrite getr_other by reg_neq_tac. rewrite H9, v_addi_lit by lia.
eapply mst_step; [reflexivity| |].
{ eapply (step_bne_ft SEGS _ _ M rom w3 10 0 8184 F3 E3 D3).
rewrite getr_other by reg_neq_tac. rewrite getr_same by reg_neq_tac.
rewrite getr_zero. reflexivity. }
rewrite v_addi_lit by lia. pc_is (x + 12). apply mst_refl.
+ split; [|split].
* rewrite getr_same by reg_neq_tac. reflexivity.
* rewrite getr_other by reg_neq_tac. rewrite getr_same by reg_neq_tac. reflexivity.
* intros r Hr. rewrite !getr_other; [reflexivity| |]; intros ->; apply Hr; auto.
- assert (Hk : (k < envc)%nat) by lia.
destruct (Rk k Hk) as [Rd Hnz].
destruct (IH (S k) (regupd (regupd regs 10 (ptr k)) 9 (Z_to_bv 64 (e + 8 * Z.of_nat (S k)))) ltac:(lia)) as [regs' [Hms Hpost]].
{ rewrite getr_same by reg_neq_tac. reflexivity. }
exists regs'. split.
+ eapply mst_step; [reflexivity| |].
{ eapply (step_ld SEGS regs _ M rom w1 10 9 0 _ (ptr k) F1 E1 D1).
- rewrite H9, signed12_0, v_addi_lit by lia. rewrite Z.add_0_r. exact Rd.
- apply bytes_le_to_Z_8. }
rif. rewrite v_addi_lit by lia. pc_is (x + 4).
eapply mst_step; [reflexivity| |].
{ eapply (step_addi SEGS _ _ M rom w2 9 9 8 F2 E2 D2). }
rif. rewrite v_addi_lit by lia. pc_is (x + 8). rewrite signed12_8.
rewrite getr_other by reg_neq_tac. rewrite H9, v_addi_lit by lia.
eapply mst_step; [reflexivity| |].
{ eapply (step_bne_tk SEGS _ _ M rom w3 10 0 8184 F3 E3 D3).
rewrite getr_other by reg_neq_tac. rewrite getr_same by reg_neq_tac.
rewrite getr_zero. apply c_eq_0_false. exact Hnz. }
rewrite signed13_m8, btgt_lit by lia. pc_is x.
replace (e + 8 * Z.of_nat k + 8) with (e + 8 * Z.of_nat (S k)) by lia.
exact Hms.
+ destruct Hpost as (P9 & P10 & Pag). split; [exact P9|]. split; [exact P10|].
intros r Hr. rewrite (Pag r Hr). rewrite !getr_other; [reflexivity| |]; intros ->; apply Hr; auto.
Qed.
End EnvLoop.
Section PnLoop.
Variable SEGS : list Segment.
Variable x : Z.
Variables w0 w1 w2 w3 w4 : bv 32.
Hypothesis Hx : 8 <= x /\ x + 12 < 2 ^ 64.
Hypothesis F0 : fetch_word SEGS (Z_to_bv 64 (x - 8)) = Some w0.
Hypothesis F1 : fetch_word SEGS (Z_to_bv 64 (x - 4)) = Some w1.
Hypothesis F2 : fetch_word SEGS (Z_to_bv 64 x) = Some w2.
Hypothesis F3 : fetch_word SEGS (Z_to_bv 64 (x + 4)) = Some w3.
Hypothesis F4 : fetch_word SEGS (Z_to_bv 64 (x + 8)) = Some w4.
Hypothesis E0 : is_ecall w0 = false.
Hypothesis E1 : is_ecall w1 = false.
Hypothesis E2 : is_ecall w2 = false.
Hypothesis E3 : is_ecall w3 = false.
Hypothesis E4 : is_ecall w4 = false.
Hypothesis D0 : decode_any w0 = Some (Store SZ8 10 11 0, 4%Z).
Hypothesis D1 : decode_any w1 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Hypothesis D2 : decode_any w2 = Some (Load SZ1 false 13 11 4095, 4%Z).
Hypothesis D3 : decode_any w3 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Hypothesis D4 : decode_any w4 = Some (Branch BC_NE 13 0 8180, 4%Z).
Variable M0 : word -> option byte.
Variable rom : word -> option byte.
Variable p pn : Z.
Variable s : list byte.
Hypothesis Hp : 0 <= p /\ p + 8 <= 2 ^ 64.
Hypothesis Hpn : 0 <= pn /\ pn + Z.of_nat (length s) + 2 < 2 ^ 64.
Hypothesis Hapart : p + 8 <= pn \/ pn + Z.of_nat (length s) + 1 <= p.
Hypothesis Hnz : ~ In (Z_to_bv 8 0) s.
Hypothesis Hrd : forall j, (j <= length s)%nat ->
rdn SEGS M0 (Z_to_bv 64 (pn + Z.of_nat j)) 1 = Some [byte_at s j].
Hypothesis Hst : store_ok SEGS M0 (Z_to_bv 64 p) 8 = true.
Definition cellrel (M : word -> option byte) : Prop :=
(forall a : word, bv_unsigned a < p \/ p + 8 <= bv_unsigned a -> M a = M0 a) /\ mem_grows M0 M.
Lemma cellrel_refl : ltac2:(TCodec.tc2 tcn__AsanStartLoops "3&IvG%211").
Proof. split; [intros; reflexivity | apply mem_grows_refl]. Qed.
Lemma cellrel_wbytes : ltac2:(TCodec.tc2 tcn__AsanStartLoops "H'QMyR0%211'7y8%511%311p051&Ir2%211&Lr3&QLvQE%22>1&Cu8%2219%83741%<11p0;1pT2D1pQ<@1").
Proof.
intros M v [H1 H2]. split.
- intros a Ha. rewrite <- (H1 a Ha).
destruct Ha as [Ha|Ha].
+ apply wbytes_below; rewrite ?length_N_to_le_bytes, u_lit by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
+ apply wbytes_above. rewrite length_N_to_le_bytes, u_lit by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
- eapply mem_grows_trans; [exact H2 | apply wbytes_grows].
Qed.
Lemma cellrel_rd : ltac2:(TCodec.tc2 tcn__AsanStartLoops "Q?'QMyR0%211'7y8%511%311p051'5&Ir2%211'?&3vQJ%22:1%4261';'4%11>%A11&Q2vQ4r4&QL&Q5vQF&Q:r3%211%5241%72N1u1%<4;:21(0(2&K%12G9(6%11Q2%53Q331%72F1%I3F91p0K1p0Q11pS4Q51pQ<Q71").
Proof.
intros M j [H1 _] Hj. rewrite <- (Hrd j Hj). apply rdn_ext.
- rewrite u_lit by lia. change (Z.of_nat 1) with 1. lia.
- intros y Hy. rewrite u_lit in Hy by lia. change (Z.of_nat 1) with 1 in Hy. apply H1. lia.
Qed.
Lemma cellrel_st : ltac2:(TCodec.tc2 tcn__AsanStartLoops "I'QMyR0%211'7y8%511%311p051&Ir1%211';'1&BvQ4r2&QLvQE%22A1u8%746521(8%;3:21p0=1pQ<A1").
Proof. intros M [_ H2]. eapply store_ok_mono; [exact H2 | exact Hst]. Qed.
Definition pn_post (regs regs' : bvmap 5 word) : Prop :=
getr regs' 11 = Z_to_bv 64 (pn + Z.of_nat (length s) + 1)
/\ getr regs' 13 = Z_to_bv 64 0
/\ regs_agree (fun r => r = 11%bv \/ r = 13%bv) regs regs'.
Lemma byte_u : ltac2:(TCodec.tc2 tcn__AsanStartLoops "?'QMy8%211':&Q7z&QOr1%2271%5241&Q8+X0%2241%:241pRL<1").
Proof. intros b. pose proof (u8_range b). lia. Qed.
Lemma pn_loop : ltac2:(TCodec.tc2 tcn__AsanStartLoops "RN'4'QMy8%211%411'5&Dy5yR0%811%4231'7%119p041';&@r3vQJ%33?21r4%63@21'?&3%12D6%3251&Q0(QK+:(9%33F21%52;1&QLvQE%22I1%D3I41r5+;%;3N19%=231&Q5vQF&Q:r6%211%5241+1%7221%@2Q71%Q23Q7:1+<%H3Q;1F%J291+Q?%F2Q=1%Q83Q=31&I%11>'<':'MvQ4&Q1vQ@r:vR1%Q22QI1r9vQI%7565321r2%O26E%Q82QO1r1%<5;4216%?3>61&J%12=7%F15%D221%E251qQ>R31%H2R41qSBR81%J2R91p0L1p0O1p0Q61p0QE1p0R01p0R51pQ<R=1pS@RA1pS4RG1pS8RI1").
Proof.
induction l2 as [|b l2 IH]; intros j regs M Hskip Hj H10 H11 H12 HM.
-
assert (Hjl : j = length s).
{ pose proof (f_equal (@length byte) Hskip) as HL. rewrite length_skipn in HL. cbn in HL. lia. }
subst j.
exists (regupd regs 13 (Z_to_bv 64 (bv_unsigned (byte_at s (length s))))), M. split; [|split; [|exact HM]].
+ eapply mst_step; [reflexivity| |].
{ eapply (step_lbu SEGS regs _ M rom w2 13 11 4095 (byte_at s (length s)) F2 E2 D2).
rewrite H11, signed12_m1, v_addi_lit by lia.
replace (pn + Z.of_nat (length s) + 1 + -1) with (pn + Z.of_nat (length s)) by lia.
apply cellrel_rd; [exact HM | lia]. }
rif. rewrite v_addi_lit by lia. pc_is (x + 4).
rewrite byte_at_len. change (bv_unsigned (Z_to_bv 8 0)) with 0.
eapply mst_step; [reflexivity| |].
{ eapply (step_beq_ft SEGS _ _ M rom w3 13 12 8180 F3 E3 D3).
rewrite getr_same by reg_neq_tac. rewrite getr_other by reg_neq_tac.
rewrite H12. rewrite c_eq_lit by lia. reflexivity. }
rewrite v_addi_lit by lia. pc_is (x + 8).
eapply mst_step; [reflexivity| |].
{ eapply (step_bne_ft SEGS _ _ M rom w4 13 0 8180 F4 E4 D4).
rewrite getr_same by reg_neq_tac. rewrite getr_zero. rewrite c_eq_lit by lia. reflexivity. }
rewrite v_addi_lit by lia. pc_is (x + 12). apply mst_refl.
+ split; [|split].
* rewrite getr_other by reg_neq_tac. exact H11.
* rewrite getr_same by reg_neq_tac. rewrite byte_at_len. reflexivity.
* intros r Hr. rewrite getr_other; [reflexivity|]. intros ->. apply Hr. auto.
- assert (Hjlt : (j < length s)%nat).
{ pose proof (f_equal (@length byte) Hskip) as HL. rewrite length_skipn in HL. cbn in HL. lia. }
assert (Hb : byte_at s j = b).
{ unfold byte_at. rewrite app_nth1 by lia. rewrite <- (Nat.add_0_r j), <- nth_skipn, Hskip. reflexivity. }
assert (Hbnz : bv_unsigned b <> 0).
{ intros Hb0. apply Hnz. rewrite <- Hb in Hb0. rewrite nth_lt_byte_at in Hb0 by lia.
replace (Z_to_bv 8 0) with (nth j s (Z_to_bv 8 0)); [apply nth_In; lia|].
apply bv_eq. rewrite Hb0. reflexivity. }
assert (Hskip' : skipn (S j) s = l2).
{ replace (S j) with (1 + j)%nat by lia. rewrite <- skipn_skipn, Hskip. reflexivity. }
pose proof (byte_u b) as Hbu.
set (regs1 := regupd regs 13 (Z_to_bv 64 (bv_unsigned b))).
assert (S1 : RiscvSemantics.step SEGS (mkst regs (Z_to_bv 64 x) M rom) = MachineOk (mkst regs1 (Z_to_bv 64 (x + 4)) M rom)).
{ erewrite (step_lbu SEGS regs _ M rom w2 13 11 4095 b F2 E2 D2).
- rif. rewrite v_addi_lit by lia. reflexivity.
- rewrite H11, signed12_m1, v_addi_lit by lia.
replace (pn + Z.of_nat j + 1 + -1) with (pn + Z.of_nat j) by lia. rewrite <- Hb.
apply cellrel_rd; [exact HM | lia]. }
assert (G13 : getr regs1 13 = Z_to_bv 64 (bv_unsigned b)) by (unfold regs1; rewrite getr_same by reg_neq_tac; reflexivity).
assert (G10 : getr regs1 10 = Z_to_bv 64 p) by (unfold regs1; rewrite getr_other by reg_neq_tac; exact H10).
assert (G11 : getr regs1 11 = Z_to_bv 64 (pn + Z.of_nat j + 1)) by (unfold regs1; rewrite getr_other by reg_neq_tac; exact H11).
assert (G12 : getr regs1 12 = Z_to_bv 64 47) by (unfold regs1; rewrite getr_other by reg_neq_tac; exact H12).
destruct (Z.eqb (bv_unsigned b) 47) eqn:Eb.
+
set (M1 := wbytes M (Z_to_bv 64 p) (word_to_le_bytes 8 (Z_to_bv 64 (pn + Z.of_nat j + 1)))).
set (regs2 := regupd regs1 11 (Z_to_bv 64 (pn + Z.of_nat (S j) + 1))).
assert (HM1 : cellrel M1) by (unfold M1; apply cellrel_wbytes; exact HM).
destruct (IH (S j) regs2 M1 Hskip' ltac:(lia)) as (regs' & M' & Hms & Hpost & HM').
{ unfold regs2. rewrite getr_other by reg_neq_tac. exact G10. }
{ unfold regs2. rewrite getr_same by reg_neq_tac. reflexivity. }
{ unfold regs2. rewrite getr_other by reg_neq_tac. exact G12. }
{ exact HM1. }
exists regs', M'. split; [|split; [|exact HM']].
* eapply mst_step; [reflexivity | exact S1 |].
eapply mst_step; [reflexivity| |].
{ eapply (step_beq_tk SEGS _ _ M rom w3 13 12 8180 F3 E3 D3).
rewrite G13, G12. rewrite c_eq_lit by lia. exact Eb. }
rewrite signed13_m12, btgt_lit by lia. pc_is (x - 8).
eapply mst_step; [reflexivity| |].
{ eapply (step_sd_at SEGS regs1 _ M rom w0 10 11 0 (Z_to_bv 64 p) _ F0 E0 D0).
- rewrite G10, signed12_0, v_addi_lit by lia. f_equal. lia.
- exact G11.
- apply cellrel_st. exact HM. }
fold M1. rewrite v_addi_lit by lia. pc_is (x - 4).
eapply mst_step; [reflexivity| |].
{ eapply (step_addi SEGS regs1 _ M1 rom w1 11 11 1 F1 E1 D1). }
rif. rewrite G11, signed12_1, !v_addi_lit by lia. pc_is x.
replace (pn + Z.of_nat j + 1 + 1) with (pn + Z.of_nat (S j) + 1) by lia.
exact Hms.
* destruct Hpost as (P11 & P13 & Pag). split; [exact P11|]. split; [exact P13|].
intros r Hr. rewrite (Pag r Hr). unfold regs2, regs1.
rewrite !getr_other; [reflexivity| |]; intros ->; apply Hr; auto.
+
set (regs2 := regupd regs1 11 (Z_to_bv 64 (pn + Z.of_nat (S j) + 1))).
destruct (IH (S j) regs2 M Hskip' ltac:(lia)) as (regs' & M' & Hms & Hpost & HM').
{ unfold regs2. rewrite getr_other by reg_neq_tac. exact G10. }
{ unfold regs2. rewrite getr_same by reg_neq_tac. reflexivity. }
{ unfold regs2. rewrite getr_other by reg_neq_tac. exact G12. }
{ exact HM. }
exists regs', M'. split; [|split; [|exact HM']].
* eapply mst_step; [reflexivity | exact S1 |].
eapply mst_step; [reflexivity| |].
{ eapply (step_beq_ft SEGS _ _ M rom w3 13 12 8180 F3 E3 D3).
rewrite G13, G12. rewrite c_eq_lit by lia. exact Eb. }
rewrite v_addi_lit by lia. pc_is (x + 8).
eapply mst_step; [reflexivity| |].
{ eapply (step_bne_tk SEGS _ _ M rom w4 13 0 8180 F4 E4 D4).
rewrite G13, getr_zero. apply c_eq_0_false. rewrite u_lit by lia. exact Hbnz. }
rewrite signed13_m12, btgt_lit by lia. pc_is (x - 4).
eapply mst_step; [reflexivity| |].
{ eapply (step_addi SEGS regs1 _ M rom w1 11 11 1 F1 E1 D1). }
rif. rewrite G11, signed12_1, !v_addi_lit by lia. pc_is x.
replace (pn + Z.of_nat j + 1 + 1) with (pn + Z.of_nat (S j) + 1) by lia.
exact Hms.
* destruct Hpost as (P11 & P13 & Pag). split; [exact P11|]. split; [exact P13|].
intros r Hr. rewrite (Pag r Hr). unfold regs2, regs1.
rewrite !getr_other; [reflexivity| |]; intros ->; apply Hr; auto.
Qed.
End PnLoop.
End FPX_2.
