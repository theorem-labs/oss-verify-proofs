(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1a YK0s YK1b YK1h YK0v YE06.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB19 AB18 AB1d AB1u.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section C1.
Variable mem0 : word -> option byte.
Variables dst src : word.
Variable n : Z.
Variable bs : list byte.
Variable rom : word -> option byte.
Hypothesis HOK : mcH mem0 dst src n bs.
#[local] Notation MK := (memk mem0 dst bs).
#[local] Notation SB := (sb_ bs).
#[local] Notation B := (b_ bs).
Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.
Ltac mlw F D jj :=
chain_step; [reflexivity
| eapply (mc_lw _ _ _ _ _ HOK) with (j := jj);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
| step_simpl]; vnorm.
Ltac mlbu F D jj :=
chain_step; [reflexivity
| eapply (mc_lbu _ _ _ _ _ HOK) with (j := jj);
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
Ltac msb F D kk valtac :=
mk_at kk;
chain_step; [reflexivity
| eapply (mc_sb _ _ _ _ _ HOK) with (k := kk);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
| gres; rwH; reflexivity | valtac | lia | lia]
| step_simpl].
Ltac cond :=
rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_andi by lia; imm_norm; unorm;
first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
rewrite ?land_3 by lia; lia.
Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.
Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
Ltac m24 := eapply (merge_s24 _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].
Lemma c1_pro : forall regs (ret : word) k,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 1 ->
(0 <= k)%Z -> (32 <= n - k)%Z ->
exists regs',
msteps TSEGS (mkst regs (0x97308 : word) (MK k) rom) (mkst regs' (0x974d4 : word) (MK (k + 3)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 3)
/\ getr regs' 12 = Z_to_bv 64 (n - (k + 3)) /\ getr regs' 14 = LWv (SB k 4)
/\ getr regs' 15 = Z_to_bv 64 16 /\ keeps regs regs'.
Proof.
intros regs ret k H1 H11 H13 H12 H15 Hk Hnk. eexists. split.
- mlw F_11d0f4 D_11d0f4 k.
stepn F_11d0f8 D_11d0f8.
stepb_ft F_11d0fc D_11d0fc ltac:(cond).
stepn F_11d100 D_11d100.
stepb_tk F_11d104 D_11d104 ltac:(cond).
stepn F_11d29c D_11d29c.
stepn F_11d2a0 D_11d2a0.
stepn F_11d2a4 D_11d2a4.
msb F_11d2a8 D_11d2a8 k ltac:(eapply (sb_val_word0' _ _ _ _ _ HOK); lia).
msb F_11d2ac D_11d2ac (k + 1)%Z ltac:(eapply (sb_val_srli8 _ _ _ _ _ HOK); lia).
msb F_11d2b0 D_11d2b0 (k + 2)%Z ltac:(eapply (sb_val_srli16 _ _ _ _ _ HOK); lia).
stepn F_11d2b4 D_11d2b4.
stepn F_11d2b8 D_11d2b8.
stepn F_11d2bc D_11d2bc.
mk_eq. apply mst_refl.
- post. unfold v_addi. unorm. f_equal. lia.
Qed.
Lemma c1_loop : forall (q : nat) regs (ret : word) kk ja jw,
getr regs 1 = ret -> getr regs 11 = at_ src ja -> getr regs 13 = at_ dst kk ->
getr regs 12 = Z_to_bv 64 (n - kk) -> getr regs 14 = LWv (SB jw 4) -> getr regs 15 = Z_to_bv 64 16 ->
(ja = kk + 13)%Z -> (jw = kk - 3)%Z -> (3 <= kk)%Z ->
(16 * (Z.of_nat q + 1) + 1 <= n - kk < 16 * (Z.of_nat q + 1) + 17)%Z ->
exists regs',
msteps TSEGS (mkst regs (0x974d4 : word) (MK kk) rom)
(mkst regs' (0x97534 : word) (MK (kk + 16 * (Z.of_nat q + 1))) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + 16 * (Z.of_nat q + 1) + 13)
/\ getr regs' 13 = at_ dst (kk + 16 * (Z.of_nat q + 1))
/\ getr regs' 12 = Z_to_bv 64 (n - (kk + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
Proof.
induction q as [|q IH]; intros regs ret kk ja jw H1 H11 H13 H12 H14 H15 Hja Hjw Hkk Hq; subst ja jw.
- eexists. split.
+ stepn F_11d2c0 D_11d2c0.
mlw F_11d2c4 D_11d2c4 (kk + 1)%Z.
mlw F_11d2c8 D_11d2c8 (kk + 5)%Z.
mlw F_11d2cc D_11d2cc (kk + 9)%Z.
mlw F_11d2d0 D_11d2d0 (kk + 13)%Z.
stepn F_11d2d4 D_11d2d4. stepn F_11d2d8 D_11d2d8. stepn F_11d2dc D_11d2dc.
stepn F_11d2e0 D_11d2e0. stepn F_11d2e4 D_11d2e4. stepn F_11d2e8 D_11d2e8.
stepn F_11d2ec D_11d2ec. stepn F_11d2f0 D_11d2f0. stepn F_11d2f4 D_11d2f4.
stepn F_11d2f8 D_11d2f8. stepn F_11d2fc D_11d2fc.
stepn F_11d300 D_11d300.
msw F_11d304 D_11d304 kk ltac:(m24).
msw F_11d308 D_11d308 (kk + 4)%Z ltac:(m24).
msw F_11d30c D_11d30c (kk + 8)%Z ltac:(m24).
msw F_11d310 D_11d310 (kk + 12)%Z ltac:(m24).
stepn F_11d314 D_11d314.
stepn F_11d318 D_11d318.
stepb_ft F_11d31c D_11d31c ltac:(unfold v_addi; cond).
mk_eq. apply mst_refl.
+ post. unfold v_addi. unorm. f_equal. lia.
- eapply (runs_trans TSEGS _ (fun r => mkst r (0x974d4 : word) (MK (kk + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16 + 13) /\ getr r 13 = at_ dst (kk + 16)
/\ getr r 12 = Z_to_bv 64 (n - (kk + 16)) /\ getr r 14 = LWv (SB (kk + 13) 4)
/\ getr r 15 = Z_to_bv 64 16 /\ keeps regs r)).
+ eexists. split.
* stepn F_11d2c0 D_11d2c0.
mlw F_11d2c4 D_11d2c4 (kk + 1)%Z.
mlw F_11d2c8 D_11d2c8 (kk + 5)%Z.
mlw F_11d2cc D_11d2cc (kk + 9)%Z.
mlw F_11d2d0 D_11d2d0 (kk + 13)%Z.
stepn F_11d2d4 D_11d2d4. stepn F_11d2d8 D_11d2d8. stepn F_11d2dc D_11d2dc.
stepn F_11d2e0 D_11d2e0. stepn F_11d2e4 D_11d2e4. stepn F_11d2e8 D_11d2e8.
stepn F_11d2ec D_11d2ec. stepn F_11d2f0 D_11d2f0. stepn F_11d2f4 D_11d2f4.
stepn F_11d2f8 D_11d2f8. stepn F_11d2fc D_11d2fc.
stepn F_11d300 D_11d300.
msw F_11d304 D_11d304 kk ltac:(m24).
msw F_11d308 D_11d308 (kk + 4)%Z ltac:(m24).
msw F_11d30c D_11d30c (kk + 8)%Z ltac:(m24).
msw F_11d310 D_11d310 (kk + 12)%Z ltac:(m24).
stepn F_11d314 D_11d314.
stepn F_11d318 D_11d318.
stepb_tk F_11d31c D_11d31c ltac:(unfold v_addi; cond).
mk_eq. apply mst_refl.
* cbv beta. post. unfold v_addi. unorm. f_equal. lia.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
destruct (IH r1 ret (kk + 16)%Z (kk + 16 + 13)%Z (kk + 13)%Z R1 R11 R13 R12 R14 R15
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.
Lemma c1_exit : forall regs (ret : word) kk,
getr regs 1 = ret -> getr regs 11 = at_ src (kk + 13) -> getr regs 13 = at_ dst kk ->
getr regs 12 = Z_to_bv 64 (n - kk) ->
(0 <= kk)%Z -> (n - kk < 32)%Z -> (kk <= n)%Z ->
let m := (n - kk)%Z in
exists regs',
msteps TSEGS (mkst regs (0x97534 : word) (MK kk) rom)
(mkst regs' (0x97654 : word) (MK (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
/\ getr regs' 13 = at_ dst (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret kk H1 H11 H13 H12 Hkk Hm Hkn m. subst m.
destruct (bits_lt32 (n - kk) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (0 <= Z.land (n - kk) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 4)%Z by (apply Z.land_nonneg; lia).
assert (0 <= Z.land (n - kk) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 1)%Z by (apply Z.land_nonneg; lia).
destruct B16 as [HL16|HL16].
- eapply (runs_trans TSEGS _ (fun r => mkst r (0x972f4 : word) (MK kk) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
+ eexists. split.
* stepn F_11d320 D_11d320.
stepn F_11d324 D_11d324.
stepb_tk F_11d328 D_11d328 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
- eapply (runs_trans TSEGS _ (fun r => mkst r (0x97540 : word) (MK kk) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
+ eexists. split.
* stepn F_11d320 D_11d320.
stepn F_11d324 D_11d324.
stepb_ft F_11d328 D_11d328 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
eapply (runs_trans TSEGS _ (fun r => mkst r (0x975cc : word) (MK (kk + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16) /\ getr r 13 = at_ dst (kk + 16) /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
* destruct (b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma c1_run : forall regs (ret : word) k,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 1 ->
(0 <= k)%Z -> (32 <= n - k)%Z ->
exists regs' m,
msteps TSEGS (mkst regs (0x97308 : word) (MK k) rom)
(mkst regs' (0x97654 : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
/\ (0 <= m < 32)%Z
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
/\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k H1 H11 H13 H12 H15 Hk Hnk.
set (q := Z.to_nat ((n - k - 4) / 16 - 1)).
assert (Hq : (16 * (Z.of_nat q + 1) + 1 <= n - (k + 3) < 16 * (Z.of_nat q + 1) + 17)%Z).
{ subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
set (kk := (k + 3 + 16 * (Z.of_nat q + 1))%Z).
set (m := (n - kk)%Z).
destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
destruct (c1_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk) as (r1 & RUN1 & P1 & P11 & P13 & P12 & P14 & P15 & K1).
destruct (c1_loop q r1 ret (k + 3)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)
as (r2 & RUN2 & Q1 & Q11 & Q13 & Q12 & K2).
fold kk in RUN2, Q11, Q13, Q12.
destruct (c1_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r3 & RUN3 & S1 & S11 & S13 & S12 & K3).
fold m in RUN3, S11, S13, S12.
exists r3, m.
assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
rewrite E in RUN3, S11, S13.
split; [| split; [lia | repeat split; try assumption]].
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
- eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
Qed.
End C1.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
