(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.zstd.fse_read_ncount.images Require Import AsanUbsan.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim
RefMemcpyLib BothMemcpyBase Both_code_memcpy.
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
From Stdlib Require Import Zify.
Local Ltac Stdlib.micromega.Lia.lia ::=
first [ intros; Zify.zify_pre_hook; zify_elim_let; zify_op; (Zify.zify_iter_specs); Zify.zify_saturate; Zify.zify_post_hook; xlia zchecker
| Zify.zify; xlia zchecker ].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section AL.
Variable mem0 : word -> option byte.
Variables dst src : word.
Variable n : Z.
Variable bs : list byte.
Variable rom : word -> option byte.
Hypothesis HOK : mcH mem0 dst src n bs.
#[local] Notation MK := (memk mem0 dst bs).
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
#[using="HOK"] Lemma b1_run : forall regs (ret : word) k,
ret_ok ret -> getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
(0 <= k)%Z -> (k + 1 = n)%Z ->
exists regs',
msteps BSEGS (mkst regs (0x93038 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
/\ keeps regs regs'.
Proof.
intros regs ret k Hret H1 H11 H13 Hk Hkn.
eexists. split.
- mlbu F_931b4 D_931b4 k.
msb F_931b8 D_931b8 k ltac:(apply sb_val_plain).
replace (k + 1)%Z with n by lia.
stepret F_931bc D_931bc ret ltac:(exact H1).
apply mst_refl.
- solve_keeps.
Qed.
#[using="HOK"] Lemma t2_run : forall regs (ret : word) k m,
ret_ok ret -> getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 2 ^ 64)%Z ->
(Z.land m 2 = 0 \/ Z.land m 2 = 2)%Z -> (Z.land m 1 = 0 \/ Z.land m 1 = 1)%Z ->
(0 <= k)%Z -> (n - k = Z.land m 2 + Z.land m 1)%Z ->
exists regs',
msteps BSEGS (mkst regs (0x93000 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
/\ keeps regs regs'.
Proof.
intros regs ret k m Hret H1 H11 H13 H12 Hm [HL2|HL2] [HL1|HL1] Hk Hrem.
-
eexists. split.
+ stepn F_9317c D_9317c.
stepb_ft F_93180 D_93180 ltac:(cond).
stepn F_93184 D_93184.
stepb_ft F_93188 D_93188 ltac:(cond).
stepret F_9318c D_9318c ret ltac:(exact H1).
mk_eq. apply mst_refl.
+ solve_keeps.
-
eapply (runs_trans BSEGS _ (fun r => mkst r (0x93038 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ keeps regs r)).
+ eexists. split.
* stepn F_9317c D_9317c.
stepb_ft F_93180 D_93180 ltac:(cond).
stepn F_93184 D_93184.
stepb_tk F_93188 D_93188 ltac:(cond).
apply mst_refl.
* cbv beta. repeat split; [gres; exact H1 | gres; exact H11 | gres; exact H13 | solve_keeps].
+ cbv beta. intros r1 (R1 & R11 & R13 & K1).
destruct (b1_run r1 ret k Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
-
eexists. split.
+ stepn F_9317c D_9317c.
stepb_tk F_93180 D_93180 ltac:(cond).
mlbu F_93190 D_93190 k.
mlbu F_93194 D_93194 (k + 1)%Z.
stepn F_93198 D_93198.
stepn F_9319c D_9319c.
msb F_931a0 D_931a0 k ltac:(apply sb_val_plain).
msb F_931a4 D_931a4 (k + 1)%Z ltac:(apply sb_val_plain).
stepn F_931a8 D_931a8.
stepn F_931ac D_931ac.
stepb_tk F_931b0 D_931b0 ltac:(cond).
stepret F_9318c D_9318c ret ltac:(exact H1).
mk_eq. apply mst_refl.
+ solve_keeps.
-
eapply (runs_trans BSEGS _ (fun r => mkst r (0x93038 : word) (MK (k + 2)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 2) /\ getr r 13 = at_ dst (k + 2) /\ keeps regs r)).
+ eexists. split.
* stepn F_9317c D_9317c.
stepb_tk F_93180 D_93180 ltac:(cond).
mlbu F_93190 D_93190 k.
mlbu F_93194 D_93194 (k + 1)%Z.
stepn F_93198 D_93198.
stepn F_9319c D_9319c.
msb F_931a0 D_931a0 k ltac:(apply sb_val_plain).
msb F_931a4 D_931a4 (k + 1)%Z ltac:(apply sb_val_plain).
stepn F_931a8 D_931a8.
stepn F_931ac D_931ac.
stepb_ft F_931b0 D_931b0 ltac:(cond).
mk_eq. apply mst_refl.
* cbv beta. repeat split; [gres; exact H1 | gres; rwH; rewrite ?at_addi; reflexivity
| gres; rwH; rewrite ?at_addi; reflexivity | solve_keeps].
+ cbv beta. intros r1 (R1 & R11 & R13 & K1).
destruct (b1_run r1 ret (k + 2)%Z Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
Qed.
#[using="HOK"] Lemma al4_run : forall regs (ret : word) k m,
getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
(Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
exists regs',
msteps BSEGS (mkst regs (0x92dbc : word) (MK k) rom)
(mkst regs' (0x93000 : word) (MK (k + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4)
/\ getr regs' 13 = at_ dst (k + Z.land m 4) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk [HL4|[HL4 Hk4]].
- eexists. split.
+ stepn F_92f38 D_92f38.
stepb_tk F_92f3c D_92f3c ltac:(cond).
mk_eq. apply mst_refl.
+ repeat split; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
- eexists. split.
+ stepn F_92f38 D_92f38.
stepb_ft F_92f3c D_92f3c ltac:(cond).
mlw F_92f40 D_92f40 k.
stepn F_92f44 D_92f44.
msw F_92f48 D_92f48 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
stepn F_92f4c D_92f4c.
stepn F_92f50 D_92f50.
mk_eq. apply mst_refl.
+ repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
Qed.
#[using="HOK"] Lemma al8_run : forall regs (ret : word) k m e8,
getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
(m < 8 /\ e8 = 0 \/ 8 <= m /\ e8 = 8 /\ k + 8 <= n)%Z ->
exists regs',
msteps BSEGS (mkst regs (0x92d9c : word) (MK k) rom)
(mkst regs' (0x92dbc : word) (MK (k + e8)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + e8)
/\ getr regs' 13 = at_ dst (k + e8) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m e8 H1 H11 H13 H12 Hm Hk [[HL8 He]|[HL8 [He Hk8]]]; subst e8.
- eexists. split.
+ stepn F_92f18 D_92f18.
stepb_tk F_92f1c D_92f1c ltac:(cond).
mk_eq. apply mst_refl.
+ repeat split; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
- eexists. split.
+ stepn F_92f18 D_92f18.
stepb_ft F_92f1c D_92f1c ltac:(cond).
mlw F_92f20 D_92f20 k.
mlw F_92f24 D_92f24 (k + 4)%Z.
msw F_92f28 D_92f28 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw F_92f2c D_92f2c (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
stepn F_92f30 D_92f30.
stepn F_92f34 D_92f34.
mk_eq. apply mst_refl.
+ repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
Qed.
#[using="HOK Hn0"] Lemma al_loop : forall (q : nat) regs (ret : word) k,
getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
getr regs 14 = Z_to_bv 64 15 ->
(0 <= k)%Z -> (16 * (Z.of_nat q + 1) <= n - k < 16 * (Z.of_nat q + 1) + 16)%Z ->
exists regs',
msteps BSEGS (mkst regs (0x92d6c : word) (MK k) rom)
(mkst regs' (0x92d9c : word) (MK (k + 16 * (Z.of_nat q + 1))) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16 * (Z.of_nat q + 1))
/\ getr regs' 13 = at_ dst (k + 16 * (Z.of_nat q + 1))
/\ getr regs' 12 = Z_to_bv 64 (n - (k + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
Proof.
induction q as [|q IH]; intros regs ret k H1 H11 H13 H12 H14 Hk Hq.
-
eexists. split.
+ mlw F_92ee8 D_92ee8 k.
mlw F_92eec D_92eec (k + 4)%Z.
mlw F_92ef0 D_92ef0 (k + 8)%Z.
mlw F_92ef4 D_92ef4 (k + 12)%Z.
stepn F_92ef8 D_92ef8.
stepn F_92efc D_92efc.
msw F_92f00 D_92f00 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw F_92f04 D_92f04 (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw F_92f08 D_92f08 (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw F_92f0c D_92f0c (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
stepn F_92f10 D_92f10.
stepb_ft F_92f14 D_92f14 ltac:(unfold v_addi; cond).
mk_eq. apply mst_refl.
+ repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
* unfold v_addi. unorm. f_equal. lia.
* solve_keeps.
- eapply (runs_trans BSEGS _ (fun r => mkst r (0x92d6c : word) (MK (k + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16)
/\ getr r 12 = Z_to_bv 64 (n - (k + 16)) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
+ eexists. split.
* mlw F_92ee8 D_92ee8 k.
mlw F_92eec D_92eec (k + 4)%Z.
mlw F_92ef0 D_92ef0 (k + 8)%Z.
mlw F_92ef4 D_92ef4 (k + 12)%Z.
stepn F_92ef8 D_92ef8.
stepn F_92efc D_92efc.
msw F_92f00 D_92f00 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw F_92f04 D_92f04 (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw F_92f08 D_92f08 (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
msw F_92f0c D_92f0c (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
stepn F_92f10 D_92f10.
stepb_tk F_92f14 D_92f14 ltac:(unfold v_addi; cond).
mk_eq. apply mst_refl.
* cbv beta. repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
-- unfold v_addi. unorm. f_equal. lia.
-- solve_keeps.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & K1).
destruct (IH r1 ret (k + 16)%Z R1 R11 R13 R12 R14 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split.
* replace (k + 16 * (Z.of_nat (S q) + 1))%Z with (k + 16 + 16 * (Z.of_nat q + 1))%Z by lia. exact RUN.
* replace (k + 16 * (Z.of_nat (S q) + 1))%Z with (k + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
#[using="HOK Hn0"] Lemma al16_run : forall regs (ret : word) k,
getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
(0 <= k <= n)%Z ->
exists regs',
msteps BSEGS (mkst regs (0x92d60 : word) (MK k) rom)
(mkst regs' (0x92d9c : word) (MK (n - (n - k) mod 16)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (n - k) mod 16)
/\ getr regs' 13 = at_ dst (n - (n - k) mod 16)
/\ getr regs' 12 = Z_to_bv 64 ((n - k) mod 16) /\ keeps regs regs'.
Proof.
intros regs ret k H1 H11 H13 H12 Hk.
destruct (Z.lt_ge_cases (n - k) 16) as [Hsmall|Hbig].
-
eexists. split.
+ stepn F_92edc D_92edc.
stepb_tk F_92ee0 D_92ee0 ltac:(cond).
replace (n - (n - k) mod 16)%Z with k by (rewrite Z.mod_small; lia).
apply mst_refl.
+ rewrite (Z.mod_small (n - k) 16) by lia. replace (n - (n - k))%Z with k by lia.
repeat split; gres; rwH; try reflexivity. solve_keeps.
- set (q := Z.to_nat ((n - k) / 16 - 1)).
assert (Hq : (16 * (Z.of_nat q + 1) <= n - k < 16 * (Z.of_nat q + 1) + 16)%Z).
{ subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
pose proof (Z.div_mod (n - k) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k) 16 ltac:(lia)). lia. }
assert (Hk' : (k + 16 * (Z.of_nat q + 1) = n - (n - k) mod 16)%Z).
{ subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
pose proof (Z.div_mod (n - k) 16 ltac:(lia)). lia. }
eapply (runs_trans BSEGS _ (fun r => mkst r (0x92d6c : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k
/\ getr r 12 = Z_to_bv 64 (n - k) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
+ eexists. split.
* stepn F_92edc D_92edc.
stepb_ft F_92ee0 D_92ee0 ltac:(cond).
stepn F_92ee4 D_92ee4.
apply mst_refl.
* cbv beta. repeat split; gres; rwH; try reflexivity. solve_keeps.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & K1).
destruct (al_loop q r1 ret k R1 R11 R13 R12 R14 ltac:(lia) Hq) as (r2 & RUN & P).
exists r2. rewrite <- Hk'. replace ((n - k) mod 16)%Z with (n - (k + 16 * (Z.of_nat q + 1)))%Z by lia.
decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption.
Qed.
End AL.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
