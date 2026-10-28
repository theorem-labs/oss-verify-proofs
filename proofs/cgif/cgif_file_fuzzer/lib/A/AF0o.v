(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1a YK0s YK1b YK1h YK0v YE06.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB19 AB1s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section d.
Variable mem0 : word -> option byte.
Variables dst src : word.
Variable n : Z.
Variable bs : list byte.
Variable rom : word -> option byte.
Hypothesis HOK : mcH mem0 dst src n bs.
#[local] Notation MK := (memk mem0 dst bs).
#[local] Notation SB := (sb_ bs).
Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.
Ltac mlw F D jj :=
chain_step; [reflexivity
| eapply (mc_lw _ _ _ _ _ HOK) with (j := jj);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
| step_simpl]; vnorm.
Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
Ltac msw F D kk valtac :=
mk_at kk;
chain_step; [reflexivity
| eapply (mc_sw _ _ _ _ _ HOK) with (k := kk);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
| gres; rwH; reflexivity | valtac | lia | lia]
| step_simpl].
Lemma c_eq_at : forall a b, (0 <= bv_unsigned src + a < 2 ^ 64)%Z -> (0 <= bv_unsigned src + b < 2 ^ 64)%Z ->
c_eq (at_ src a) (at_ src b) = (a =? b)%Z.
Proof.
intros a b Ha Hb. unfold c_eq, bv_eqb, at_. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
rewrite !Z.mod_small by lia. destruct (Z.eqb_spec (bv_unsigned src + a) (bv_unsigned src + b)), (Z.eqb_spec a b); lia.
Qed.
Ltac cond := rwH; rewrite ?at_addi; rewrite c_eq_at by lia; first [apply Z.eqb_eq | apply Z.eqb_neq]; lia.
Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.
Lemma cpy4_iter : forall regs k,
getr regs 22 = at_ src k -> getr regs 25 = at_ dst k -> getr regs 10 = at_ src n ->
(0 <= k)%Z -> (k mod 4 = 0)%Z -> (k + 4 <= n)%Z ->
exists regs',
msteps TSEGS (mkst regs (0x34024 : word) (MK k) rom)
(mkst regs' (if (k + 4 =? n)%Z then (0x34038 : word) else (0x34024 : word)) (MK (k + 4)) rom)
/\ getr regs' 22 = at_ src (k + 4) /\ getr regs' 25 = at_ dst (k + 4) /\ getr regs' 10 = at_ src n
/\ (forall r : reg, r <> 11 -> r <> 22 -> r <> 25 -> getr regs' r = getr regs r).
Proof.
intros regs k H22 H25 H10 Hk Hk4 Hkn. pose proof (u64_range dst) as Rd. pose proof (u64_range src) as Rs.
eexists. split.
- mlw F_509d4 D_509d4 k.
stepn F_509d8 D_509d8.
msw F_509dc D_509dc k ltac:(eapply (sw_val_plain _ _ _ _ _ HOK); lia).
stepn F_509e0 D_509e0.
destruct (Z.eqb_spec (k + 4) n) as [E|NE].
+ stepb_ft F_509e4 D_509e4 ltac:(cond).
mk_eq. apply mst_refl.
+ stepb_tk F_509e4 D_509e4 ltac:(cond).
mk_eq. apply mst_refl.
- gres. rwH. rewrite ?at_addi. repeat split; try reflexivity.
intros r H11 H22' H25'. rewrite !getr_other by (assumption || (intros ->; contradiction)). reflexivity.
Qed.
Lemma cpy4_loop : forall (q : nat) regs k,
getr regs 22 = at_ src k -> getr regs 25 = at_ dst k -> getr regs 10 = at_ src n ->
(0 <= k)%Z -> (k mod 4 = 0)%Z -> (n = k + 4 * (Z.of_nat q + 1))%Z ->
exists regs',
msteps TSEGS (mkst regs (0x34024 : word) (MK k) rom) (mkst regs' (0x34038 : word) (MK n) rom)
/\ getr regs' 22 = at_ src n /\ getr regs' 25 = at_ dst n /\ getr regs' 10 = at_ src n
/\ (forall r : reg, r <> 11 -> r <> 22 -> r <> 25 -> getr regs' r = getr regs r).
Proof.
induction q as [|q IH]; intros regs k H22 H25 H10 Hk Hk4 Hnk.
- destruct (cpy4_iter regs k H22 H25 H10 Hk Hk4 ltac:(lia)) as (regs' & Hms & R22 & R25 & R10 & Rr).
replace (k + 4 =? n)%Z with true in Hms by (symmetry; apply Z.eqb_eq; lia).
assert (En : (k + 4)%Z = n) by lia. rewrite En in Hms, R22, R25.
exists regs'. split; [exact Hms|]. repeat (split; [assumption|]). exact Rr.
- destruct (cpy4_iter regs k H22 H25 H10 Hk Hk4 ltac:(lia)) as (regs1 & Hms1 & R22 & R25 & R10 & Rr1).
replace (k + 4 =? n)%Z with false in Hms1 by (symmetry; apply Z.eqb_neq; lia).
destruct (IH regs1 (k + 4)%Z R22 R25 R10 ltac:(lia) ltac:(rewrite Z.add_mod, Hk4 by lia; reflexivity) ltac:(lia))
as (regs' & Hms2 & R22' & R25' & R10' & Rr2).
exists regs'. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
repeat (split; [assumption|]). intros r A B' C. rewrite (Rr2 r A B' C). apply Rr1; assumption.
Qed.
End d.
Theorem tfib_cpy4k_run : forall mem0 (dst src : word) n bs rom regs,
mcH mem0 dst src n bs -> (n mod 4 = 0)%Z -> (4 <= n)%Z ->
getr regs 22 = src -> getr regs 25 = dst -> getr regs 10 = at_ src n ->
exists regs',
msteps TSEGS (mkst regs (0x34024 : word) mem0 rom) (mkst regs' (0x34038 : word) (wbytes mem0 dst bs) rom)
/\ getr regs' 22 = at_ src n /\ getr regs' 25 = at_ dst n /\ getr regs' 10 = at_ src n
/\ (forall r : reg, r <> 11 -> r <> 22 -> r <> 25 -> getr regs' r = getr regs r).
Proof.
intros mem0 dst src n bs rom regs HOK Hmod Hge H22 H25 H10.
pose proof (Hn _ _ _ _ _ HOK) as Hn0.
rewrite <- (memk_n mem0 dst src n bs HOK).
change (mkst regs (0x34024 : word) mem0 rom) with (mkst regs (0x34024 : word) (memk mem0 dst bs 0) rom).
apply (cpy4_loop mem0 dst src n bs rom HOK (Z.to_nat (n / 4) - 1) regs 0);
[rewrite H22; unfold at_; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| rewrite H25; unfold at_; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| exact H10 | lia | reflexivity |].
pose proof (Z.div_mod n 4 ltac:(lia)). rewrite Nat2Z.inj_sub by (apply Nat2Z.inj_le; rewrite Z2Nat.id; [apply Z.div_le_lower_bound|]; lia).
rewrite Z2Nat.id by (apply Z.div_pos; lia). change (Z.of_nat 1) with 1%Z. lia.
Qed.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
