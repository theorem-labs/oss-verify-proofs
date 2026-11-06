(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.zstd.fse_read_ncount.images Require Import Asan.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim
RefMemcpyLib AsanMemcpyBase AsanMemcpyAL Asan_code_memcpy.
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section MIS.
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
Ltac mlbu F D jj :=
chain_step; [reflexivity
| eapply (mc_lbu _ _ _ _ _ HOK) with (j := jj);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
| step_simpl]; vnorm.
Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
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
Ltac sbp := apply sb_val_plain.
#[using="HOK"] Lemma b4_blk : forall regs (ret : word) k (a2 : word),
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
(0 <= k)%Z -> (k + 4 <= n)%Z ->
exists regs',
msteps ASEGS (mkst regs (0x92e44 : word) (MK k) rom) (mkst regs' (0x92e70 : word) (MK (k + 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 4) /\ getr regs' 13 = at_ dst (k + 4)
/\ getr regs' 12 = a2 /\ keeps regs regs'.
Proof.
intros regs ret k a2 H1 H11 H13 H12 Hk Hk4. eexists. split.
- mlbu F_92ea0 D_92ea0 k. mlbu F_92ea4 D_92ea4 (k+1)%Z. mlbu F_92ea8 D_92ea8 (k+2)%Z. mlbu F_92eac D_92eac (k+3)%Z.
stepn F_92eb0 D_92eb0.
stepn F_92eb4 D_92eb4.
msb F_92eb8 D_92eb8 k ltac:(sbp). msb F_92ebc D_92ebc (k+1)%Z ltac:(sbp).
msb F_92ec0 D_92ec0 (k+2)%Z ltac:(sbp). msb F_92ec4 D_92ec4 (k+3)%Z ltac:(sbp).
stepn F_92ec8 D_92ec8.
mk_eq. apply mst_refl.
- post.
Qed.
#[using="HOK"] Lemma b8_blk : forall regs (ret : word) k (a2 : word),
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
(0 <= k)%Z -> (k + 8 <= n)%Z ->
exists regs',
msteps ASEGS (mkst regs (0x92df0 : word) (MK k) rom) (mkst regs' (0x92e3c : word) (MK (k + 8)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 8) /\ getr regs' 13 = at_ dst (k + 8)
/\ getr regs' 12 = a2 /\ keeps regs regs'.
Proof.
intros regs ret k a2 H1 H11 H13 H12 Hk Hk8. eexists. split.
- mlbu F_92e4c D_92e4c k. mlbu F_92e50 D_92e50 (k+1)%Z. mlbu F_92e54 D_92e54 (k+2)%Z. mlbu F_92e58 D_92e58 (k+3)%Z.
mlbu F_92e5c D_92e5c (k+4)%Z. mlbu F_92e60 D_92e60 (k+5)%Z. mlbu F_92e64 D_92e64 (k+6)%Z. mlbu F_92e68 D_92e68 (k+7)%Z.
stepn F_92e6c D_92e6c.
msb F_92e70 D_92e70 k ltac:(sbp). msb F_92e74 D_92e74 (k+1)%Z ltac:(sbp).
msb F_92e78 D_92e78 (k+2)%Z ltac:(sbp). msb F_92e7c D_92e7c (k+3)%Z ltac:(sbp).
stepn F_92e80 D_92e80.
msb F_92e84 D_92e84 (k+4)%Z ltac:(sbp). msb F_92e88 D_92e88 (k+5)%Z ltac:(sbp).
msb F_92e8c D_92e8c (k+6)%Z ltac:(sbp). msb F_92e90 D_92e90 (k+7)%Z ltac:(sbp).
stepn F_92e94 D_92e94.
mk_eq. apply mst_refl.
- post.
Qed.
#[using="HOK"] Lemma b16_blk : forall regs (ret : word) k (a2 : word),
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
(0 <= k)%Z -> (k + 16 <= n)%Z ->
exists regs',
msteps ASEGS (mkst regs (0x92d5c : word) (MK k) rom) (mkst regs' (0x92de8 : word) (MK (k + 16)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 16)
/\ getr regs' 12 = a2 /\ keeps regs regs'.
Proof.
intros regs ret k a2 H1 H11 H13 H12 Hk Hk16. eexists. split.
- mlbu F_92db8 D_92db8 k. mlbu F_92dbc D_92dbc (k+1)%Z. mlbu F_92dc0 D_92dc0 (k+2)%Z. mlbu F_92dc4 D_92dc4 (k+3)%Z.
mlbu F_92dc8 D_92dc8 (k+4)%Z. mlbu F_92dcc D_92dcc (k+5)%Z. mlbu F_92dd0 D_92dd0 (k+6)%Z. mlbu F_92dd4 D_92dd4 (k+7)%Z.
msb F_92dd8 D_92dd8 k ltac:(sbp). msb F_92ddc D_92ddc (k+1)%Z ltac:(sbp).
msb F_92de0 D_92de0 (k+2)%Z ltac:(sbp). msb F_92de4 D_92de4 (k+3)%Z ltac:(sbp).
mlbu F_92de8 D_92de8 (k+8)%Z. mlbu F_92dec D_92dec (k+9)%Z. mlbu F_92df0 D_92df0 (k+10)%Z. mlbu F_92df4 D_92df4 (k+11)%Z.
msb F_92df8 D_92df8 (k+4)%Z ltac:(sbp). msb F_92dfc D_92dfc (k+5)%Z ltac:(sbp).
msb F_92e00 D_92e00 (k+6)%Z ltac:(sbp). msb F_92e04 D_92e04 (k+7)%Z ltac:(sbp).
mlbu F_92e08 D_92e08 (k+12)%Z. mlbu F_92e0c D_92e0c (k+13)%Z. mlbu F_92e10 D_92e10 (k+14)%Z. mlbu F_92e14 D_92e14 (k+15)%Z.
stepn F_92e18 D_92e18.
msb F_92e1c D_92e1c (k+8)%Z ltac:(sbp). msb F_92e20 D_92e20 (k+9)%Z ltac:(sbp).
msb F_92e24 D_92e24 (k+10)%Z ltac:(sbp). msb F_92e28 D_92e28 (k+11)%Z ltac:(sbp).
stepn F_92e2c D_92e2c.
msb F_92e30 D_92e30 (k+12)%Z ltac:(sbp). msb F_92e34 D_92e34 (k+13)%Z ltac:(sbp).
msb F_92e38 D_92e38 (k+14)%Z ltac:(sbp). msb F_92e3c D_92e3c (k+15)%Z ltac:(sbp).
stepn F_92e40 D_92e40.
mk_eq. apply mst_refl.
- post.
Qed.
#[using="HOK"] Lemma t4_run : forall regs (ret : word) k m,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
(Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
exists regs',
msteps ASEGS (mkst regs (0x92b18 : word) (MK k) rom) (mkst regs' (0x92e70 : word) (MK (k + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
- eexists. split.
+ stepn F_92b74 D_92b74.
stepb_ft F_92b78 D_92b78 ltac:(cond).
stepn F_92b7c D_92b7c.
mk_eq. apply mst_refl.
+ post.
- eapply (runs_trans ASEGS _ (fun r => mkst r (0x92e44 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_92b74 D_92b74.
stepb_tk F_92b78 D_92b78 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.
#[using="HOK"] Lemma b8_tail : forall regs (ret : word) k m,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
(Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
exists regs',
msteps ASEGS (mkst regs (0x92e3c : word) (MK k) rom) (mkst regs' (0x92e70 : word) (MK (k + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
- eexists. split.
+ stepn F_92e98 D_92e98.
stepb_tk F_92e9c D_92e9c ltac:(cond).
mk_eq. apply mst_refl.
+ post.
- eapply (runs_trans ASEGS _ (fun r => mkst r (0x92e44 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_92e98 D_92e98.
stepb_ft F_92e9c D_92e9c ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.
#[using="HOK"] Lemma t8_run : forall regs (ret : word) k m,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
(Z.land m 8 = 0 \/ Z.land m 8 = 8)%Z -> (Z.land m 4 = 0 \/ Z.land m 4 = 4)%Z ->
(k + Z.land m 8 + Z.land m 4 <= n)%Z ->
exists regs',
msteps ASEGS (mkst regs (0x92b10 : word) (MK k) rom)
(mkst regs' (0x92e70 : word) (MK (k + Z.land m 8 + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
/\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
destruct HL8 as [HL8|HL8].
-
eapply (runs_trans ASEGS _ (fun r => mkst r (0x92b18 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_92b6c D_92b6c.
stepb_ft F_92b70 D_92b70 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
-
eapply (runs_trans ASEGS _ (fun r => mkst r (0x92df0 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_92b6c D_92b6c.
stepb_tk F_92b70 D_92b70 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
eapply (runs_trans ASEGS _ (fun r => mkst r (0x92e3c : word) (MK (k + 8)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
* destruct (b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia)) as (r3 & RUN & P).
exists r3. rewrite HL8. replace (k + 8 + Z.land m 4)%Z with (k + 8 + Z.land m 4)%Z by lia.
split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.
#[using="HOK"] Lemma b16_tail : forall regs (ret : word) k m,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
(Z.land m 8 = 0 \/ Z.land m 8 = 8)%Z -> (Z.land m 4 = 0 \/ Z.land m 4 = 4)%Z ->
(k + Z.land m 8 + Z.land m 4 <= n)%Z ->
exists regs',
msteps ASEGS (mkst regs (0x92de8 : word) (MK k) rom)
(mkst regs' (0x92e70 : word) (MK (k + Z.land m 8 + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
/\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
destruct HL8 as [HL8|HL8].
- eapply (runs_trans ASEGS _ (fun r => mkst r (0x92b18 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_92e44 D_92e44.
stepb_tk F_92e48 D_92e48 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
- eapply (runs_trans ASEGS _ (fun r => mkst r (0x92df0 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_92e44 D_92e44.
stepb_ft F_92e48 D_92e48 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
eapply (runs_trans ASEGS _ (fun r => mkst r (0x92e3c : word) (MK (k + 8)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
* destruct (b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia)) as (r3 & RUN & P).
exists r3. rewrite HL8. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.
#[using="HOK"] Lemma t16_run : forall regs (ret : word) k m,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 32)%Z -> (0 <= k)%Z ->
(k + Z.land m 16 + Z.land m 8 + Z.land m 4 <= n)%Z ->
exists regs',
msteps ASEGS (mkst regs (0x92b08 : word) (MK k) rom)
(mkst regs' (0x92e70 : word) (MK (k + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
/\ getr regs' 13 = at_ dst (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk Hkn.
destruct (bits_lt32 m Hm) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (0 <= Z.land m 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
destruct B16 as [HL16|HL16].
-
eapply (runs_trans ASEGS _ (fun r => mkst r (0x92b10 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_92b64 D_92b64.
stepb_ft F_92b68 D_92b68 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (t8_run r1 ret k m R1 R11 R13 R12 ltac:(lia) Hk B8 B4 ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
-
eapply (runs_trans ASEGS _ (fun r => mkst r (0x92d5c : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_92b64 D_92b64.
stepb_tk F_92b68 D_92b68 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
eapply (runs_trans ASEGS _ (fun r => mkst r (0x92de8 : word) (MK (k + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
* destruct (b16_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (b16_tail r2 ret (k + 16)%Z m S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.
End MIS.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
