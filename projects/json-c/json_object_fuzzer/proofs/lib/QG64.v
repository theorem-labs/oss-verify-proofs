(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC QgpE Q3bI QU0c Q85Z Qo8J.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import QWTC QgpE Q3bI QU0c Q85Z.Mq1 Qo8J.Mq0.
Local Instance asanreflect_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma u_lit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. Qed.

Lemma v_addi_lit : forall a k, 0 <= a < 2 ^ 64 -> v_addi (Z_to_bv 64 a) k = Z_to_bv 64 (a + k).
Proof. intros a k Ha. unfold v_addi. rewrite u_lit by lia. reflexivity. Qed.

Lemma btgt_lit : forall a k, 0 <= a < 2 ^ 64 -> btgt (Z_to_bv 64 a) k = Z_to_bv 64 (a + k).
Proof. intros a k Ha. unfold btgt. apply v_addi_lit. exact Ha. Qed.

Lemma c_eq_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = Z.eqb a b.
Proof. intros a b Ha Hb. unfold c_eq, bv_eqb. rewrite !u_lit by lia. reflexivity. Qed.

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

Lemma signed12_0 : bv_signed (0 : bv 12) = 0. Proof. reflexivity. Qed.
Lemma signed12_1 : bv_signed (1 : bv 12) = 1. Proof. reflexivity. Qed.
Lemma signed12_8 : bv_signed (8 : bv 12) = 8. Proof. reflexivity. Qed.
Lemma signed12_m1 : bv_signed (4095 : bv 12) = -1. Proof. reflexivity. Qed.
Lemma signed13_m8 : bv_signed (8184 : bv 13) = -8. Proof. reflexivity. Qed.
Lemma signed13_m12 : bv_signed (8180 : bv 13) = -12. Proof. reflexivity. Qed.

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

Lemma env_loop : forall n k regs,
(k + n = envc)%nat ->
getr regs 9 = Z_to_bv 64 (e + 8 * Z.of_nat k) ->
exists regs',
msteps SEGS (mkst regs (Z_to_bv 64 x) M rom) (mkst regs' (Z_to_bv 64 (x + 12)) M rom)
/\ env_post regs regs'.
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

Lemma cellrel_refl : cellrel M0.
Proof. split; [intros; reflexivity | apply mem_grows_refl]. Qed.

Lemma cellrel_wbytes : forall M (v : word), cellrel M -> cellrel (wbytes M (Z_to_bv 64 p) (word_to_le_bytes 8 v)).
Proof.
intros M v [H1 H2]. split.
- intros a Ha. rewrite <- (H1 a Ha).
destruct Ha as [Ha|Ha].
+ apply wbytes_below; rewrite ?length_N_to_le_bytes, u_lit by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
+ apply wbytes_above. rewrite length_N_to_le_bytes, u_lit by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
- eapply mem_grows_trans; [exact H2 | apply wbytes_grows].
Qed.

Lemma cellrel_rd : forall M j, cellrel M -> (j <= length s)%nat ->
rdn SEGS M (Z_to_bv 64 (pn + Z.of_nat j)) 1 = Some [byte_at s j].
Proof.
intros M j [H1 _] Hj. rewrite <- (Hrd j Hj). apply rdn_ext.
- rewrite u_lit by lia. change (Z.of_nat 1) with 1. lia.
- intros y Hy. rewrite u_lit in Hy by lia. change (Z.of_nat 1) with 1 in Hy. apply H1. lia.
Qed.

Lemma cellrel_st : forall M, cellrel M -> store_ok SEGS M (Z_to_bv 64 p) 8 = true.
Proof. intros M [_ H2]. eapply store_ok_mono; [exact H2 | exact Hst]. Qed.

Definition pn_post (regs regs' : bvmap 5 word) : Prop :=
getr regs' 11 = Z_to_bv 64 (pn + Z.of_nat (length s) + 1)
/\ getr regs' 13 = Z_to_bv 64 0
/\ regs_agree (fun r => r = 11%bv \/ r = 13%bv) regs regs'.

Lemma byte_u : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (u8_range b). lia. Qed.

Lemma pn_loop : forall l2 j regs M,
skipn j s = l2 -> (j <= length s)%nat ->
getr regs 10 = Z_to_bv 64 p ->
getr regs 11 = Z_to_bv 64 (pn + Z.of_nat j + 1) ->
getr regs 12 = Z_to_bv 64 47 ->
cellrel M ->
exists regs' M',
msteps SEGS (mkst regs (Z_to_bv 64 x) M rom) (mkst regs' (Z_to_bv 64 (x + 12)) M' rom)
/\ pn_post regs regs' /\ cellrel M'.
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
End Mq0.
From Stdlib Require FunctionalExtensionality.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJ4Q Qek8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QWTC QgpE QU0c QJ4Q.Mq0 Q85Z.Mq1 Qek8.Mq0.
Import ListNotations. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Local Open Scope Z_scope.

Lemma wbytes_inside : forall bs m (a x : word),
bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs) ->
wbytes m a bs x = Some (nth (Z.to_nat (bv_unsigned x - bv_unsigned a)) bs (Z_to_bv 8 0)).
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
- assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1)
by (apply u_add1; lia).
rewrite (IH _ (a + 1)%bv) by (rewrite Hu1; lia).
rewrite Hu1.
replace (Z.to_nat (bv_unsigned x - bv_unsigned a))
with (S (Z.to_nat (bv_unsigned x - (bv_unsigned a + 1)))) by lia.
reflexivity.
Qed.

Lemma wbytes_outside : forall bs m (a x : word),
bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
(bv_unsigned x < bv_unsigned a \/ bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned x) ->
wbytes m a bs x = m x.
Proof.
intros bs m a x Hnw [Hlt|Hge].
- apply wbytes_below; assumption.
- apply wbytes_above; assumption.
Qed.

Lemma wbytes_select : forall (P : word -> bool) (f g : word -> option byte) (a : word) bs,
bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
(forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs) ->
P x = true) ->
wbytes (fun x => if P x then f x else g x) a bs
= (fun x => if P x then wbytes f a bs x else g x).
Proof.
intros P f g a bs Hnw HP. apply functional_extensionality. intro x.
destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
- rewrite !wbytes_outside by lia. reflexivity.
- destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [Hin|Hout].
+ rewrite !wbytes_inside by lia. rewrite (HP x) by lia. reflexivity.
+ rewrite !wbytes_outside by lia. reflexivity.
Qed.

Lemma wbytes_select_r : forall (P : word -> bool) (f g : word -> option byte) (a : word) bs,
bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
(forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs) ->
P x = false) ->
wbytes (fun x => if P x then f x else g x) a bs
= (fun x => if P x then f x else wbytes g a bs x).
Proof.
intros P f g a bs Hnw HP. apply functional_extensionality. intro x.
destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
- rewrite !wbytes_outside by lia. reflexivity.
- destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [Hin|Hout].
+ rewrite !wbytes_inside by lia. rewrite (HP x) by lia. reflexivity.
+ rewrite !wbytes_outside by lia. reflexivity.
Qed.

Definition win_lo (sp0 : word) : Z := bv_unsigned sp0 - stack_max_size.

Definition in_win (sp0 : word) (x : word) : Prop :=
win_lo sp0 <= bv_unsigned x < bv_unsigned sp0.

Definition cmem (sp0 : word) (mem0 J D : word -> option byte) : word -> option byte :=
fun a => if (bv_unsigned sp0 <=? bv_unsigned a) then mem0 a
else if (win_lo sp0 <=? bv_unsigned a) then J a else D a.

Definition wfJ (sp0 : word) (J : word -> option byte) : Prop :=
forall x : word, in_win sp0 x -> J x <> None.

Lemma wfJ_wbytes : forall sp0 J a bs, wfJ sp0 J -> wfJ sp0 (wbytes J a bs).
Proof. intros sp0 J a bs H x Hx. apply wbytes_grows. apply H. exact Hx. Qed.

Definition agree_above (lo : Z) (J J' : word -> option byte) : Prop :=
forall x : word, lo <= bv_unsigned x -> J' x = J x.

Section CMem.
Variable sp0 : word.
Variable mem0 : word -> option byte.

Let csel := cmem sp0 mem0.

Lemma stack_max_size_pos : 0 < stack_max_size.
Proof. rewrite stack_max_size_val. lia. Qed.

Lemma wbytes_cmem_win : forall J D (a : word) bs,
win_lo sp0 <= bv_unsigned a ->
bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned sp0 ->
wbytes (cmem sp0 mem0 J D) a bs = cmem sp0 mem0 (wbytes J a bs) D.
Proof.
intros J D a bs Hlo Hhi. unfold cmem.
pose proof (u64_range sp0) as Hsp.
rewrite (wbytes_select_r (fun x => bv_unsigned sp0 <=? bv_unsigned x) mem0
(fun x => if win_lo sp0 <=? bv_unsigned x then J x else D x) a bs)
by (first [lia | intros x Hx; apply Z.leb_gt; lia]).
apply functional_extensionality. intro x.
destruct (bv_unsigned sp0 <=? bv_unsigned x); [reflexivity|].
rewrite (wbytes_select (fun x => win_lo sp0 <=? bv_unsigned x) J D a bs)
by (first [lia | intros y Hy; apply Z.leb_le; lia]).
reflexivity.
Qed.

Lemma wbytes_cmem_data : forall J D (a : word) bs,
bv_unsigned a + Z.of_nat (length bs) <= win_lo sp0 ->
wbytes (cmem sp0 mem0 J D) a bs = cmem sp0 mem0 J (wbytes D a bs).
Proof.
intros J D a bs Hhi. unfold cmem.
pose proof (u64_range sp0) as Hsp. pose proof stack_max_size_pos.
unfold win_lo in *.
rewrite (wbytes_select_r (fun x => bv_unsigned sp0 <=? bv_unsigned x) mem0
(fun x => if bv_unsigned sp0 - stack_max_size <=? bv_unsigned x then J x else D x) a bs)
by (first [lia | intros x Hx; apply Z.leb_gt; lia]).
apply functional_extensionality. intro x.
destruct (bv_unsigned sp0 <=? bv_unsigned x); [reflexivity|].
rewrite (wbytes_select_r (fun x => bv_unsigned sp0 - stack_max_size <=? bv_unsigned x) J D a bs)
by (first [lia | intros y Hy; apply Z.leb_gt; lia]).
reflexivity.
Qed.

Lemma rdn_cmem_data : forall segs J D (a : word) n,
bv_unsigned a + Z.of_nat n <= win_lo sp0 ->
rdn segs (cmem sp0 mem0 J D) a n = rdn segs D a n.
Proof.
intros segs J D a n Hhi. pose proof (u64_range sp0). pose proof stack_max_size_pos.
unfold win_lo in *.
apply rdn_ext; [lia|].
intros x Hx. unfold cmem, win_lo.
rewrite (proj2 (Z.leb_gt _ _)) by lia.
rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
Qed.

Lemma cmem_at_win : forall J D (x : word),
in_win sp0 x -> cmem sp0 mem0 J D x = J x.
Proof.
intros J D x [Hlo Hhi]. unfold cmem.
rewrite (proj2 (Z.leb_gt _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
Qed.

Lemma store_ok_cmem_win : forall segs J D (a : word) n,
wfJ sp0 J ->
win_lo sp0 <= bv_unsigned a ->
bv_unsigned a + Z.of_nat n <= bv_unsigned sp0 ->
store_ok segs (cmem sp0 mem0 J D) a n = true.
Proof.
intros segs J D a n HJ Hlo Hhi. pose proof (u64_range sp0).
apply store_ok_of_all; [lia|].
intros x Hx. unfold wview.
rewrite cmem_at_win by (unfold in_win; lia).
destruct (J x) as [b|] eqn:E; [discriminate|].
exfalso. apply (HJ x); [unfold in_win; lia | exact E].
Qed.

Lemma store_ok_cmem_data : forall segs J D (a : word) n,
wseg_ok segs a n = true ->
store_ok segs (cmem sp0 mem0 J D) a n = true.
Proof. intros. apply store_ok_wseg. assumption. Qed.

End CMem.

End Mq1.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Fs Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require ExecutableSpecs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWXq QQny QHup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import QWXq.Mq2 QQny Q3bI QHup.Mq0 Q85Z.

Import ListNotations. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

Definition halt_ev (m' : Model) (code : word) : event :=
match m_killed m' with
| Some sig => KillEv sig (m_fs m')
| None => ExitEv code (m_fs m')
end.

Lemma sstep_svc_inv : forall ms model x8 e st,
ms_svc_pending ms = Some x8 ->
sstep segs (mkCfg ms model) e st ->
(exists eff model' evs,
check_syscall (sys_input segs ms x8) eff model = CheckOk model' evs
/\ ((exists model'', m_halted model' = None /\ e = evs
/\ materialize_model_accesses model' (syscall_effect_accesses eff) = Some model''
/\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model''))
\/ (m_halted model' = None /\ e = []
/\ materialize_model_accesses model' (syscall_effect_accesses eff) = None
/\ st = SError)
\/ (exists code, m_halted model' = Some code
/\ e = evs ++ [halt_ev model' code]
/\ st = SNext (mkCfg ms model'))))
\/ (exists eff, check_syscall (sys_input segs ms x8) eff model = CheckUnmodeled
/\ e = [] /\ st = SError).
Proof.
intros ms model x8 e st Hsvc Hss.
inversion Hss; subst; try congruence.
-
match goal with H : ms_svc_pending ms = Some ?y |- _ =>
rewrite Hsvc in H; inversion H; subst end.
left. eexists _, _, _. split.
+ apply check_syscall_ok_iff. eassumption.
+ left. eexists. repeat split; eauto.
-
match goal with H : ms_svc_pending ms = Some ?y |- _ =>
rewrite Hsvc in H; inversion H; subst end.
left. eexists _, _, _. split.
+ apply check_syscall_ok_iff. eassumption.
+ right. left. repeat split; auto.
-
match goal with H : ms_svc_pending ms = Some ?y |- _ =>
rewrite Hsvc in H; inversion H; subst end.
left. eexists _, _, _. split.
+ apply check_syscall_ok_iff. eassumption.
+ right. right. eexists. repeat split; eauto.
unfold halt_ev. match goal with Hk : m_killed _ = None |- _ => rewrite Hk end. reflexivity.
-
match goal with H : ms_svc_pending ms = Some ?y |- _ =>
rewrite Hsvc in H; inversion H; subst end.
left. eexists _, _, _. split.
+ apply check_syscall_ok_iff. eassumption.
+ right. right.
match goal with Hk : m_killed ?mm = Some _ |- _ =>
destruct (m_halted mm) as [code|] eqn:Hhc;
[| rewrite (m_killed_of_m_halted_none _ Hhc) in Hk; discriminate Hk];
exists code; split; [reflexivity | split; [unfold halt_ev; rewrite Hk; reflexivity | reflexivity]]
end.
-
match goal with H : ms_svc_pending ms = Some ?y |- _ =>
rewrite Hsvc in H; inversion H; subst end.
right. exists (mkEffect (Z_to_bv 64 0) [] []). split; [|split; reflexivity].
apply check_syscall_err_iff. assumption.
Qed.

Lemma sstep_cfg_svc_inv : forall ms model x8 e st,
ms_svc_pending ms = Some x8 ->
sstep_cfg segs (alloc_only_cfg false) (mkCfg ms model) e st ->
(exists eff model' evs,
check_syscall (sys_input segs ms x8) eff model = CheckOk model' evs
/\ ((exists model'', ~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model eff
/\ m_halted model' = None /\ e = evs
/\ materialize_model_accesses model' (syscall_effect_accesses eff) = Some model''
/\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model''))
\/ (~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model eff
/\ m_halted model' = None /\ e = []
/\ materialize_model_accesses model' (syscall_effect_accesses eff) = None
/\ st = SError)
\/ (exists code, m_halted model' = Some code
/\ e = evs ++ [halt_ev model' code]
/\ st = SNext (mkCfg ms model'))))
\/ (exists eff, check_syscall (sys_input segs ms x8) eff model = CheckUnmodeled
/\ e = [] /\ st = SError).
Proof.
intros ms model x8 e st Hsvc Hss.
inversion Hss; subst; try congruence.
-
match goal with H : ms_svc_pending ms = Some ?y |- _ =>
rewrite Hsvc in H; inversion H; subst end.
left. eexists _, _, _. split.
+ apply check_syscall_ok_iff. eassumption.
+ left. eexists. repeat split; eauto.
-
match goal with H : ms_svc_pending ms = Some ?y |- _ =>
rewrite Hsvc in H; inversion H; subst end.
left. eexists _, _, _. split.
+ apply check_syscall_ok_iff. eassumption.
+ right. left. repeat split; auto.
-
match goal with H : ms_svc_pending ms = Some ?y |- _ =>
rewrite Hsvc in H; inversion H; subst end.
left. eexists _, _, _. split.
+ apply check_syscall_ok_iff. eassumption.
+ right. right. eexists. repeat split; eauto.
unfold halt_ev. match goal with Hk : m_killed _ = None |- _ => rewrite Hk end. reflexivity.
-
match goal with H : ms_svc_pending ms = Some ?y |- _ =>
rewrite Hsvc in H; inversion H; subst end.
left. eexists _, _, _. split.
+ apply check_syscall_ok_iff. eassumption.
+ right. right.
match goal with Hk : m_killed ?mm = Some _ |- _ =>
destruct (m_halted mm) as [code|] eqn:Hhc;
[| rewrite (m_killed_of_m_halted_none _ Hhc) in Hk; discriminate Hk];
exists code; split; [reflexivity | split; [unfold halt_ev; rewrite Hk; reflexivity | reflexivity]]
end.
-
match goal with H : ms_svc_pending ms = Some ?y |- _ =>
rewrite Hsvc in H; inversion H; subst end.
right. exists (mkEffect (Z_to_bv 64 0) [] []). split; [|split; reflexivity].
apply check_syscall_err_iff. assumption.
Qed.

Definition open_I (model : Model) : Type := {e : Z | In e openat_errnos} + unit.

Definition open_nx (ms : machine_state) (model : Model) (mk : word -> Model)
(i : open_I model) : config :=
match i with
| inl (exist _ e _) => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
| inr _ => mkCfg (advance_past_svc (set_gpr0 ms (alloc_fd (m_fds model))))
(mk (alloc_fd (m_fds model)))
end.

End WithSegs.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import QWTC QgpE Q3bI QU0c QJ4Q.Mq0 Qo8J.Mq0 Q85Z.Mq1.
Import ListNotations. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Local Open Scope Z_scope.

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

Lemma sub_nth : forall (bs : list byte) j,
(j < length bs)%nat -> sub bs j 1 = [nth j bs (Z_to_bv 8 0)].
Proof.
intros bs j. revert bs. induction j as [|j IH]; intros bs H.
- destruct bs; cbn in *; [lia|reflexivity].
- destruct bs; cbn in *; [lia|]. unfold sub in IH. apply IH. lia.
Qed.

Lemma at_succ : forall (a : word) d, (at_ a d + 1)%bv = at_ a (d + 1).
Proof.
intros a d. unfold at_. apply bv_eq.
rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_unsigned (1 : word)) with 1.
rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma word_succ_at : forall (a : word), (a + 1)%bv = at_ a 1.
Proof. intros a. rewrite <- (at_0 a) at 1. rewrite at_succ. reflexivity. Qed.

Lemma at_u : forall (a : word) d,
0 <= bv_unsigned a + d -> bv_unsigned a + d < 2^64 ->
bv_unsigned (at_ a d) = bv_unsigned a + d.
Proof. intros a d H1 H2. unfold at_. apply u_Z2bv; lia. Qed.

Lemma wbytes_app : forall bs1 bs2 m (a : word),
wbytes m a (bs1 ++ bs2) = wbytes (wbytes m a bs1) (at_ a (Z.of_nat (length bs1))) bs2.
Proof.
induction bs1 as [|b r IH]; intros bs2 m a.
- cbn [app wbytes length Z.of_nat]. rewrite at_0. reflexivity.
- cbn [app wbytes length]. rewrite IH. f_equal.
rewrite word_succ_at, at_at. f_equal. lia.
Qed.

Lemma wbytes_extend : forall m (dst : word) bs j k,
wbytes (wbytes m dst (firstn j bs)) (at_ dst (Z.of_nat j)) (sub bs j k)
= wbytes m dst (firstn (j + k) bs) \/ (length bs < j)%nat.
Proof.
intros m dst bs j k.
destruct (Nat.le_gt_cases j (length bs)) as [H|H]; [left|right; exact H].
rewrite <- firstn_sub_app, wbytes_app. rewrite length_firstn. f_equal. f_equal. f_equal. lia.
Qed.

Lemma wbytes_extend' : forall m (dst : word) bs j k,
(j <= length bs)%nat ->
wbytes (wbytes m dst (firstn j bs)) (at_ dst (Z.of_nat j)) (sub bs j k)
= wbytes m dst (firstn (j + k) bs).
Proof.
intros m dst bs j k H. destruct (wbytes_extend m dst bs j k) as [E|E]; [exact E|lia].
Qed.

Lemma rdn_skipn : forall segs mem n (a : word) bs j,
rdn segs mem a n = Some bs -> (j <= n)%nat ->
rdn segs mem (at_ a (Z.of_nat j)) (n - j) = Some (skipn j bs).
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

Lemma rdn_sub : forall segs mem n (a : word) bs j k,
rdn segs mem a n = Some bs -> (j + k <= n)%nat ->
rdn segs mem (at_ a (Z.of_nat j)) k = Some (sub bs j k).
Proof.
intros segs mem n a bs j k H Hjk. unfold sub.
apply (rdn_firstn segs mem (n - j)); [|lia].
apply rdn_skipn; [exact H|lia].
Qed.

Abbreviation lez := bytes_le_to_Z.

Definition LWv (l : list byte) : word := v_lw (Z_to_bv 64 (lez l)).

Lemma lez_bound_len : forall bs k, length bs = k -> 0 <= lez bs < 2 ^ (8 * Z.of_nat k).
Proof. intros bs k <-. split; [apply bytes_le_to_Z_nonneg | apply bytes_le_to_Z_bound]. Qed.
Lemma lez4_range : forall l, length l = 4%nat -> 0 <= lez l < 2 ^ 32.
Proof. intros l H. pose proof (lez_bound_len l 4%nat H). change (8 * Z.of_nat 4) with 32 in H0. lia. Qed.
Lemma u_lez4 : forall l, length l = 4%nat -> bv_unsigned (Z_to_bv 64 (lez l)) = lez l.
Proof. intros l H. pose proof (lez4_range l H). apply u_Z2bv; lia. Qed.

Lemma testbit_u_LWv : forall l i, length l = 4%nat -> 0 <= i < 32 ->
Z.testbit (bv_unsigned (LWv l)) i = Z.testbit (lez l) i.
Proof.
intros l i H Hi. unfold LWv, v_lw. rewrite Z_to_bv_unsigned, u_lez4 by exact H.
rewrite bv_wrap_spec_low by lia.
rewrite bv_swrap_spec by lia.
case_bool_decide; [reflexivity|].
replace i with 31 by lia. reflexivity.
Qed.

Lemma lez_cons : forall b bs, lez (b :: bs) = Z.lor (bv_unsigned b) (Z.shiftl (lez bs) 8).
Proof. reflexivity. Qed.

Lemma testbit_lez_high : forall bs i, 8 * Z.of_nat (length bs) <= i -> Z.testbit (lez bs) i = false.
Proof.
intros bs i Hi. apply (Z_testbit_high (8 * Z.of_nat (length bs))); try lia.
apply lez_bound_len. reflexivity.
Qed.

Lemma testbit_lez_skipn : forall q bs i, 0 <= i ->
Z.testbit (lez (skipn q bs)) i = Z.testbit (lez bs) (i + 8 * Z.of_nat q).
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

Lemma Z_to_le_bytes_lez : forall bs, Z_to_le_bytes (length bs) (lez bs) = bs.
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

Lemma word_to_le_bytes_4_eq : forall (v : word) (l : list byte),
length l = 4%nat ->
(forall i, 0 <= i < 32 -> Z.testbit (bv_unsigned v) i = Z.testbit (lez l) i) ->
word_to_le_bytes 4 v = l.
Proof.
intros v l Hl Hb. unfold word_to_le_bytes.
rewrite <- (Z_to_le_bytes_wrap 4 32) by (cbn; lia).
rewrite <- Hl at 1. rewrite <- (Z_to_le_bytes_lez l). rewrite Hl. f_equal.
apply Z.bits_inj'. intros i Hi.
destruct (Z.lt_ge_cases i 32).
- rewrite bv_wrap_spec_low by lia. apply Hb. lia.
- rewrite bv_wrap_spec_high by lia. symmetry. apply testbit_lez_high. rewrite Hl. cbn. lia.
Qed.

Lemma sw_bytes_LWv : forall l, length l = 4%nat -> word_to_le_bytes 4 (LWv l) = l.
Proof.
intros l H. apply word_to_le_bytes_4_eq; [exact H|]. intros i Hi. apply testbit_u_LWv; assumption.
Qed.

Definition LBv (b : byte) : word := Z_to_bv 64 (bv_unsigned b).

Lemma sb_byte_LBv : forall b : byte, Z_to_bv 8 (bv_unsigned (LBv b)) = b.
Proof.
intros b. unfold LBv. pose proof (u8_range b). rewrite u_Z2bv by lia.
apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

Lemma sb_byte_eq : forall (v : word) (b : byte),
(forall i, 0 <= i < 8 -> Z.testbit (bv_unsigned v) i = Z.testbit (bv_unsigned b) i) ->
Z_to_bv 8 (bv_unsigned v) = b.
Proof.
intros v b Hb. apply bv_eq. rewrite Z_to_bv_unsigned.
apply Z.bits_inj'. intros i Hi. pose proof (u8_range b).
destruct (Z.lt_ge_cases i 8).
- rewrite bv_wrap_spec_low by lia. apply Hb. lia.
- rewrite bv_wrap_spec_high by lia. symmetry. apply (Z_testbit_high 8); lia.
Qed.

Lemma testbit_nth_lez : forall l q i, 0 <= i < 8 -> (q < length l)%nat ->
Z.testbit (bv_unsigned (nth q l (Z_to_bv 8 0))) i = Z.testbit (lez l) (i + 8 * Z.of_nat q).
Proof.
intros l q i Hi Hq. rewrite <- testbit_lez_skipn by lia.
revert l Hq. induction q as [|q IH]; intros l Hq.
- destruct l as [|b l]; [cbn in Hq; lia|]. cbn [nth skipn]. rewrite lez_cons.
rewrite Z.lor_spec, Z.shiftl_spec, (Z.testbit_neg_r _ (i - 8)) by lia. symmetry. apply orb_false_r.
- destruct l as [|b l]; [cbn in Hq; lia|]. cbn [nth skipn]. apply IH. cbn in Hq. lia.
Qed.

Lemma sb_byte_srli_LWv : forall l q, length l = 4%nat -> (q <= 3)%nat ->
Z_to_bv 8 (bv_unsigned (v_srli (LWv l) (8 * Z.of_nat q))) = nth q l (Z_to_bv 8 0).
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

Lemma testbit_u_vor : forall (x y : word) i, 0 <= i ->
Z.testbit (bv_unsigned (v_or x y)) i = Z.testbit (bv_unsigned x) i || Z.testbit (bv_unsigned y) i.
Proof.
intros x y i Hi. unfold v_or. rewrite Z_to_bv_unsigned.
destruct (Z.lt_ge_cases i 64).
- rewrite bv_wrap_spec_low by lia. apply Z.lor_spec.
- rewrite bv_wrap_spec_high by lia.
pose proof (u64_range x). pose proof (u64_range y).
rewrite (Z_testbit_high 64 (bv_unsigned x)) by lia. rewrite (Z_testbit_high 64 (bv_unsigned y)) by lia. reflexivity.
Qed.

Lemma sw_bytes_merge : forall l1 l2 (q : nat) (v : word),
length l1 = 4%nat -> length l2 = 4%nat -> (1 <= q <= 3)%nat ->
v = v_or (v_slli (LWv l2) (32 - 8 * Z.of_nat q)) (v_srliw (LWv l1) (8 * Z.of_nat q)) ->
word_to_le_bytes 4 v = skipn q l1 ++ firstn q l2.
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

Lemma store_ok_at : forall segs m (dst : word) (N : nat) bsw j k,
bv_unsigned dst + Z.of_nat N <= 2 ^ 64 ->
store_ok segs m dst N = true ->
0 <= j -> j + Z.of_nat k <= Z.of_nat N ->
store_ok segs (wbytes m dst bsw) (at_ dst j) k = true.
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

Lemma keeps_refl : forall regs, keeps regs regs.
Proof. intros regs r _. reflexivity. Qed.

Lemma keeps_trans : forall r1 r2 r3, keeps r1 r2 -> keeps r2 r3 -> keeps r1 r3.
Proof. intros r1 r2 r3 A B r Hr. rewrite (B r Hr). apply A, Hr. Qed.

Lemma keeps_upd : forall regs regs' (rd : reg) v,
keeps regs regs' -> ~ In rd callee_kept -> keeps regs (regupd regs' rd v).
Proof.
intros regs regs' rd v K Hn r Hr.
rewrite getr_other; [apply K, Hr|]. intros ->. exact (Hn Hr).
Qed.

Lemma keeps_getr : forall regs regs' (r : reg), keeps regs regs' -> In r callee_kept -> getr regs' r = getr regs r.
Proof. intros regs regs' r K Hr. apply K, Hr. Qed.

Ltac kept_reg := cbv [callee_kept In]; intuition congruence.

Example keeps_sp_example : forall regs regs', keeps regs regs' -> getr regs' 2 = getr regs 2.
Proof. intros regs regs' K. apply (keeps_getr _ _ 2 K). kept_reg. Qed.

Ltac not_kept := cbv; intuition discriminate.

Ltac solve_keeps :=
repeat (apply keeps_upd; [| not_kept]); first [apply keeps_refl | assumption].

Lemma runs_trans : forall segs (s0 : machine_state)
(st1 : bvmap 5 word -> machine_state) (P1 : bvmap 5 word -> Prop)
(st2 : bvmap 5 word -> machine_state) (P2 : bvmap 5 word -> Prop),
(exists r1, msteps segs s0 (st1 r1) /\ P1 r1) ->
(forall r1, P1 r1 -> exists r2, msteps segs (st1 r1) (st2 r2) /\ P2 r2) ->
exists r2, msteps segs s0 (st2 r2) /\ P2 r2.
Proof.
intros segs s0 st1 P1 st2 P2 (r1 & R1 & H1) K.
destruct (K r1 H1) as (r2 & R2 & H2).
exists r2. split; [eapply msteps_trans; eassumption | exact H2].
Qed.

Definition callee_saved : list reg :=
[1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Definition keeps_cs (regs regs' : bvmap 5 word) : Prop :=
forall r : reg, In r callee_saved -> getr regs' r = getr regs r.

Lemma keeps_cs_refl : forall regs, keeps_cs regs regs.
Proof. intros regs r _. reflexivity. Qed.

Lemma keeps_cs_upd : forall regs regs' (rd : reg) v,
keeps_cs regs regs' -> ~ In rd callee_saved -> keeps_cs regs (regupd regs' rd v).
Proof.
intros regs regs' rd v K Hn r Hr.
rewrite getr_other; [apply K, Hr|]. intros ->. exact (Hn Hr).
Qed.

Lemma keeps_cs_upd_same : forall regs regs' (rd : reg) v,
keeps_cs regs regs' -> getr regs rd = v -> rd <> 0%bv -> keeps_cs regs (regupd regs' rd v).
Proof.
intros regs regs' rd v K Hv Hnz r Hr.
destruct (decide (r = rd)) as [->|Hne].
- rewrite getr_same by exact Hnz. symmetry. exact Hv.
- rewrite getr_other by exact Hne. apply K, Hr.
Qed.

Lemma keeps_keeps_cs : forall regs regs', keeps regs regs' -> keeps_cs regs regs'.
Proof.
intros regs regs' K r Hr. apply K. unfold callee_saved, callee_kept in *. cbn [In] in *. intuition.
Qed.

Ltac solve_keeps_cs :=
repeat (first [ apply keeps_cs_upd; [| not_kept]
| apply keeps_cs_upd_same; [| solve [eauto | symmetry; eauto] | let X := fresh in intro X; discriminate X ] ]);
first [apply keeps_cs_refl | assumption | apply keeps_keeps_cs; assumption].
End Mq3.

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgpE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgpE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU0c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QU0c. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJ4Q.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJ4Q.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q85Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q85Z.Mq0.

Import ListNotations. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Lemma rdn_skipn : forall segs mem n (a : word) bs off k,
rdn segs mem a n = Some bs -> (off + k <= n)%nat ->
rdn segs mem (a + nat_to_word off) k = Some (firstn k (skipn off bs)).
Proof.
intros segs mem n. induction n as [|n IH]; intros a bs off k H Hk.
- assert (off = 0%nat) by lia. assert (k = 0%nat) by lia. subst.
rewrite word_add_0. cbn in H |- *. injection H as <-. reflexivity.
- cbn [rdn] in H.
destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
as [b|] eqn:Eb; [|discriminate].
destruct (rdn segs mem (a+1) n) as [rest|] eqn:Er; [|discriminate].
injection H as <-.
destruct off as [|off].
+ rewrite word_add_0. cbn [skipn].
eapply rdn_firstn; [|exact Hk].
cbn [rdn]. rewrite Eb, Er. reflexivity.
+ cbn [skipn].
replace (a + nat_to_word (S off)) with (a + 1 + nat_to_word off)
by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
apply (IH (a+1) rest off k Er). lia.
Qed.

Lemma firstn_app_exact : forall {A} (l1 l2 : list A) n,
length l1 = n -> firstn n (l1 ++ l2) = l1.
Proof.
intros A l1 l2 n H. subst n. rewrite firstn_app, firstn_all, Nat.sub_diag.
cbn. apply app_nil_r.
Qed.

Lemma skipn_app_exact : forall {A} (l1 l2 : list A) n,
length l1 = n -> skipn n (l1 ++ l2) = l2.
Proof.
intros A l1 l2 n H. subst n. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

Definition cat_envp_ptr (sp : word) (av ev : list (list byte)) (k : nat) : word :=
nth k (fst (string_addrs (cat_env_base sp av ev) ev)) (Z_to_bv 64 0).

Definition envp_off (av : list (list byte)) : nat := (8 + 8 * (length av + 1))%nat.
Definition auxv_off (av ev : list (list byte)) : nat :=
(8 + 8 * (length av + 1) + 8 * (length ev + 1))%nat.

Definition auxv_words (ph : PhdrInfo) (rnd uid hw : word) : list word :=
flat_map (fun e => [fst e; snd e]) (auxv_entries ph rnd uid hw).

Lemma build_auxv_words : forall entries,
build_auxv entries = flat_map word_le8 (flat_map (fun e => [fst e; snd e]) entries).
Proof.
induction entries as [|[t v] es IH]; [reflexivity|].
cbn [build_auxv flat_map fst snd app].
change (build_auxv es) with
(flat_map (fun e : bv 64 * bv 64 => word_le8 (fst e) ++ word_le8 (snd e)) es) in IH.
rewrite IH, <- app_assoc. reflexivity.
Qed.

Lemma auxv_bytes_words : forall ph rnd uid hw,
auxv_bytes ph rnd uid hw = flat_map word_le8 (auxv_words ph rnd uid hw).
Proof. intros. unfold auxv_bytes, auxv_words. apply build_auxv_words. Qed.

Lemma length_auxv_words : forall ph rnd uid hw, length (auxv_words ph rnd uid hw) = 20%nat.
Proof. reflexivity. Qed.

Section Layout.

Variable segs : list Segment.
Variable ph : PhdrInfo.
Variable sp : word.
Variable rdraw : EntryDraw.
Variable av ev : list (list byte).
Variable uid : word.
Variable hw : word.

Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned sp)%Z.
Hypothesis Hsp_hi : (bv_unsigned sp <= sp_window_hi)%Z.

Let bsb := build_stack_bytes ph sp av ev uid hw rdraw.

Let stk := stack_to_mem sp (entry_stack_image ph sp av ev uid hw rdraw).

Lemma lay_bsb_nw : (bv_unsigned sp + Z.of_nat (length bsb) < 2^64)%Z.
Proof. exact (bsb_nw ph sp av ev uid hw rdraw Hva Hve Hsp_hi). Qed.

Lemma bsb_decomp : exists strs_tail,
bsb = (word_le8 (len_word av)
++ flat_map word_le8 (fst (string_addrs (cat_string_base sp av ev) av)))
++ word_le8 (Z_to_bv 64 0)
++ flat_map word_le8 (fst (string_addrs (cat_env_base sp av ev) ev))
++ word_le8 (Z_to_bv 64 0)
++ auxv_bytes ph (at_random_ptr sp av ev) uid hw
++ strs_tail.
Proof.
unfold bsb, build_stack_bytes, cat_env_base, cat_string_base, cat_struct_size.
rewrite (string_addrs_pair av). cbv beta iota.
rewrite (string_addrs_pair ev). cbv beta iota.
eexists. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma len_argc_argv :
length (word_le8 (len_word av)
++ flat_map word_le8 (fst (string_addrs (cat_string_base sp av ev) av)))
= (8 + 8 * length av)%nat.
Proof.
rewrite length_app, length_n_to_le_8, length_flat_map_le8, length_string_addrs_fst. lia.
Qed.

Lemma len_envp_ptrs :
length (flat_map word_le8 (fst (string_addrs (cat_env_base sp av ev) ev))) = (8 * length ev)%nat.
Proof. rewrite length_flat_map_le8, length_string_addrs_fst. lia. Qed.

Lemma read_argv_null :
rdn segs stk (sp + nat_to_word (8 + 8 * length av)) 8%nat = Some (word_le8 (Z_to_bv 64 0)).
Proof.
destruct bsb_decomp as [tl E].
pose proof (read_at_offset_image segs ph sp av ev uid hw rdraw _ (word_le8 (Z_to_bv 64 0)) _ 8%nat E
(length_n_to_le_8 _) lay_bsb_nw) as H.
rewrite len_argc_argv in H. exact H.
Qed.

Lemma read_envp_ptr_k : forall k, (k < length ev)%nat ->
rdn segs stk (sp + nat_to_word (envp_off av + 8 * k)) 8%nat
= Some (word_le8 (cat_envp_ptr sp av ev k)).
Proof.
intros k Hk.
destruct bsb_decomp as [tl E].
assert (Hk' : (k < length (fst (string_addrs (cat_env_base sp av ev) ev)))%nat)
by (rewrite length_string_addrs_fst; exact Hk).
rewrite (flat_map_le8_decomp _ k Hk') in E.
rewrite <- !app_assoc in E.
match type of E with
| bsb = ?p1 ++ ?p2 ++ ?p3 ++ ?p4 ++ ?mid ++ ?rest =>
pose proof (read_at_offset_image segs ph sp av ev uid hw rdraw (p1 ++ p2 ++ p3 ++ p4) mid rest 8%nat) as H
end.
rewrite <- !app_assoc in H.
specialize (H E (length_n_to_le_8 _) lay_bsb_nw).
rewrite !length_app in H.
rewrite !length_flat_map_le8 in H.
rewrite length_string_addrs_fst in H.
rewrite firstn_length_le in H by (rewrite length_string_addrs_fst; lia).
rewrite !length_n_to_le_8 in H.
unfold envp_off, cat_envp_ptr.
replace (8 + 8 * (length av + 1) + 8 * k)%nat with (8 + (8 * length av + (8 + 8 * k)))%nat by lia.
exact H.
Qed.

Lemma read_envp_null :
rdn segs stk (sp + nat_to_word (envp_off av + 8 * length ev)) 8%nat
= Some (word_le8 (Z_to_bv 64 0)).
Proof.
destruct bsb_decomp as [tl E].
match type of E with
| bsb = ?p1 ++ ?p2 ++ ?p3 ++ ?mid ++ ?rest =>
pose proof (read_at_offset_image segs ph sp av ev uid hw rdraw (p1 ++ p2 ++ p3) mid rest 8%nat) as H
end.
rewrite <- !app_assoc in H.
specialize (H E (length_n_to_le_8 _) lay_bsb_nw).
rewrite !length_app in H. rewrite len_envp_ptrs in H.
rewrite !length_n_to_le_8 in H.
rewrite length_flat_map_le8, length_string_addrs_fst in H.
unfold envp_off.
match type of H with
| rdn _ _ (sp + nat_to_word ?n) 8 = _ =>
replace (8 + 8 * (length av + 1) + 8 * length ev)%nat with n by lia
end.
exact H.
Qed.

Lemma read_auxv_all :
rdn segs stk (sp + nat_to_word (auxv_off av ev)) 160%nat
= Some (auxv_bytes ph (at_random_ptr sp av ev) uid hw).
Proof.
destruct bsb_decomp as [tl E].
match type of E with
| bsb = ?p1 ++ ?p2 ++ ?p3 ++ ?p4 ++ ?mid ++ ?rest =>
pose proof (read_at_offset_image segs ph sp av ev uid hw rdraw (p1 ++ p2 ++ p3 ++ p4) mid rest 160%nat) as H
end.
rewrite <- !app_assoc in H.
specialize (H E (length_auxv_bytes _ _ _ _) lay_bsb_nw).
rewrite !length_app in H. rewrite len_envp_ptrs in H.
rewrite !length_n_to_le_8 in H.
rewrite length_flat_map_le8, length_string_addrs_fst in H.
unfold auxv_off.
match type of H with
| rdn _ _ (sp + nat_to_word ?n) _ = _ =>
replace (8 + 8 * (length av + 1) + 8 * (length ev + 1))%nat with n by lia
end.
exact H.
Qed.

Lemma read_auxv_word : forall j, (j < 20)%nat ->
rdn segs stk (sp + nat_to_word (auxv_off av ev + 8 * j)) 8%nat
= Some (word_le8 (nth j (auxv_words ph (at_random_ptr sp av ev) uid hw) (Z_to_bv 64 0))).
Proof.
intros j Hj.
rewrite <- nat_to_word_add_merge.
rewrite (rdn_skipn segs stk 160 _ _ (8 * j) 8 read_auxv_all) by lia.
f_equal. rewrite auxv_bytes_words.
rewrite (flat_map_le8_decomp _ j) by (rewrite length_auxv_words; exact Hj).
rewrite skipn_app_exact
by (rewrite length_flat_map_le8, firstn_length_le by (rewrite length_auxv_words; lia); lia).
apply firstn_app_exact. apply length_n_to_le_8.
Qed.

Lemma bsb_random_split : exists pre,
bsb = pre ++ at_random_bytes (ed_random rdraw)
/\ at_random_ptr sp av ev = sp + nat_to_word (length pre)
/\ (Z.of_nat (length pre) mod 8 = 0)%Z.
Proof.
unfold bsb, build_stack_bytes, at_random_ptr.
rewrite (string_addrs_pair av). cbv beta iota.
rewrite (string_addrs_pair ev). cbv beta iota zeta.
match goal with
| |- exists pre, ?raw ++ repeat ?z ?pd ++ at_random_bytes (ed_random rdraw) = _ /\ _ /\ _ =>
exists (raw ++ repeat z pd)
end.
split; [rewrite <- !app_assoc; reflexivity|].
rewrite !length_app, !repeat_length, !length_flat_map_le8, !length_string_addrs_fst,
!length_n_to_le_8, length_auxv_bytes, !length_flatten_strings.
unfold auxv_size.
match goal with
| |- _ /\ (Z.of_nat (?L' + _) mod 8 = 0)%Z => set (L := L')
end.
replace (8 + (length av + 1) * 8 + (length ev + 1) * 8 + 160
+ total_arg_bytes_nat av + total_arg_bytes_nat ev)%nat with L by lia.
assert (Hpd : (0 <= (8 - Z.of_nat L mod 8) mod 8 < 8)%Z) by (apply Z.mod_pos_bound; lia).
split; [reflexivity|].
rewrite Nat2Z.inj_add, Z2Nat.id by lia.
rewrite <- Zplus_mod_idemp_l. rewrite Zplus_mod_idemp_r.
replace (Z.of_nat L mod 8 + (8 - Z.of_nat L mod 8))%Z with 8%Z by lia.
reflexivity.
Qed.

Lemma at_random_off : exists off : nat,
at_random_ptr sp av ev = sp + nat_to_word off
/\ (off + 16 = length bsb)%nat
/\ (Z.of_nat off mod 8 = 0)%Z
/\ forall j n, (j + n <= 16)%nat ->
rdn segs stk (at_random_ptr sp av ev + nat_to_word j) n
= Some (firstn n (skipn j (at_random_bytes (ed_random rdraw)))).
Proof.
destruct bsb_random_split as [pre [E [Hp Hmod]]].
pose proof (length_at_random_bytes (ed_random rdraw)) as HL.
exists (length pre). split; [exact Hp|]. split.
{ unfold bsb in E |- *. rewrite E, length_app, HL. reflexivity. }
split; [exact Hmod|].
intros j n Hjn. rewrite Hp, nat_to_word_add_merge.
rewrite <- (firstn_skipn j (at_random_bytes (ed_random rdraw))) in E.
rewrite app_assoc in E.
rewrite <- (firstn_skipn n (skipn j (at_random_bytes (ed_random rdraw)))) in E.
pose proof (read_at_offset_image segs ph sp av ev uid hw rdraw (pre ++ firstn j (at_random_bytes (ed_random rdraw)))
(firstn n (skipn j (at_random_bytes (ed_random rdraw))))
(skipn n (skipn j (at_random_bytes (ed_random rdraw)))) n E) as H.
assert (Hlen : length (pre ++ firstn j (at_random_bytes (ed_random rdraw))) = (length pre + j)%nat).
{ rewrite length_app, firstn_length_le by lia. reflexivity. }
rewrite Hlen in H.
apply H; [rewrite firstn_length_le; [reflexivity | rewrite length_skipn; lia] | exact lay_bsb_nw].
Qed.

Lemma cat_envp_ptr_eq : forall k, (k < length ev)%nat ->
cat_envp_ptr sp av ev k
= sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat av
+ total_arg_bytes_nat (firstn k ev)).
Proof.
intros k Hk. unfold cat_envp_ptr. rewrite nth_string_addrs by exact Hk.
unfold cat_env_base, cat_string_base. rewrite !nat_to_word_add_merge.
rewrite Nat.add_assoc. reflexivity.
Qed.

Lemma total_firstn_ev_bound : forall k,
(Z.of_nat (total_arg_bytes_nat (firstn k ev)) <= 131072)%Z.
Proof.
intros k. destruct Hve as [_ [Htot _]]. rewrite total_arg_bytes_Z in Htot.
pose proof (total_arg_bytes_firstn_le k ev). lia.
Qed.

Lemma struct_av_bound :
(Z.of_nat (cat_struct_size av ev + total_arg_bytes_nat av) <= 2107576)%Z.
Proof.
destruct Hva as [[Hl0 Hl] [Hta _]]. destruct Hve as [Hle _].
rewrite total_arg_bytes_Z in Hta. unfold cat_struct_size, auxv_size. lia.
Qed.

Lemma u_cat_envp_ptr : forall k, (k < length ev)%nat ->
bv_unsigned (cat_envp_ptr sp av ev k)
= (bv_unsigned sp + Z.of_nat (cat_struct_size av ev + total_arg_bytes_nat av
+ total_arg_bytes_nat (firstn k ev)))%Z.
Proof.
intros k Hk. rewrite cat_envp_ptr_eq by exact Hk. rewrite word_add_nat.
pose proof struct_av_bound. pose proof (total_firstn_ev_bound k).
unfold sp_window_hi in Hsp_hi. unfold sp_window_lo in Hsp_lo.
apply u_Z2bv; lia.
Qed.

Lemma cat_envp_ptr_nz : forall k, (k < length ev)%nat ->
bv_unsigned (cat_envp_ptr sp av ev k) <> 0%Z.
Proof.
intros k Hk. rewrite u_cat_envp_ptr by exact Hk. unfold sp_window_lo in Hsp_lo. lia.
Qed.

Lemma u_cat_argv_ptr : forall k, (k < length av)%nat ->
bv_unsigned (cat_argv_ptr sp av ev k)
= (bv_unsigned sp + Z.of_nat (cat_struct_size av ev + total_arg_bytes_nat (firstn k av)))%Z.
Proof.
intros k Hk. rewrite cat_argv_ptr_offset by exact Hk. unfold cat_string_base.
rewrite nat_to_word_add_merge, word_add_nat.
pose proof struct_av_bound. pose proof (total_arg_bytes_firstn_le k av).
unfold sp_window_hi in Hsp_hi. unfold sp_window_lo in Hsp_lo.
apply u_Z2bv; lia.
Qed.

Lemma auxv_words_eq : forall rnd,
auxv_words ph rnd uid hw =
[AT_PHDR; Z_to_bv 64 (Z.of_N (ph_addr ph)); AT_PHENT; Z_to_bv 64 (Z.of_N (ph_ent ph));
AT_PHNUM; Z_to_bv 64 (Z.of_N (ph_num ph)); AT_HWCAP; hw; AT_PAGESZ; Z_to_bv 64 4096;
AT_UID; uid; AT_EUID; uid; AT_SECURE; Z_to_bv 64 0;
AT_RANDOM; rnd; AT_NULL; Z_to_bv 64 0].
Proof. reflexivity. Qed.

End Layout.
