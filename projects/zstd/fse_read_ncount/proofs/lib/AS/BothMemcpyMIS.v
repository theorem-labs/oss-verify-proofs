(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.zstd.fse_read_ncount.images Require Import AsanUbsan.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim
RefMemcpyLib BothMemcpyBase BothMemcpyAL Both_code_memcpy.
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
msteps BSEGS (mkst regs (0x92fd4 : word) (MK k) rom) (mkst regs' (0x93000 : word) (MK (k + 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 4) /\ getr regs' 13 = at_ dst (k + 4)
/\ getr regs' 12 = a2 /\ keeps regs regs'.
Proof.
intros regs ret k a2 H1 H11 H13 H12 Hk Hk4. eexists. split.
- mlbu F_93150 D_93150 k. mlbu F_93154 D_93154 (k+1)%Z. mlbu F_93158 D_93158 (k+2)%Z. mlbu F_9315c D_9315c (k+3)%Z.
stepn F_93160 D_93160.
stepn F_93164 D_93164.
msb F_93168 D_93168 k ltac:(sbp). msb F_9316c D_9316c (k+1)%Z ltac:(sbp).
msb F_93170 D_93170 (k+2)%Z ltac:(sbp). msb F_93174 D_93174 (k+3)%Z ltac:(sbp).
stepn F_93178 D_93178.
mk_eq. apply mst_refl.
- post.
Qed.
#[using="HOK"] Lemma b8_blk : forall regs (ret : word) k (a2 : word),
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
(0 <= k)%Z -> (k + 8 <= n)%Z ->
exists regs',
msteps BSEGS (mkst regs (0x92f80 : word) (MK k) rom) (mkst regs' (0x92fcc : word) (MK (k + 8)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 8) /\ getr regs' 13 = at_ dst (k + 8)
/\ getr regs' 12 = a2 /\ keeps regs regs'.
Proof.
intros regs ret k a2 H1 H11 H13 H12 Hk Hk8. eexists. split.
- mlbu F_930fc D_930fc k. mlbu F_93100 D_93100 (k+1)%Z. mlbu F_93104 D_93104 (k+2)%Z. mlbu F_93108 D_93108 (k+3)%Z.
mlbu F_9310c D_9310c (k+4)%Z. mlbu F_93110 D_93110 (k+5)%Z. mlbu F_93114 D_93114 (k+6)%Z. mlbu F_93118 D_93118 (k+7)%Z.
stepn F_9311c D_9311c.
msb F_93120 D_93120 k ltac:(sbp). msb F_93124 D_93124 (k+1)%Z ltac:(sbp).
msb F_93128 D_93128 (k+2)%Z ltac:(sbp). msb F_9312c D_9312c (k+3)%Z ltac:(sbp).
stepn F_93130 D_93130.
msb F_93134 D_93134 (k+4)%Z ltac:(sbp). msb F_93138 D_93138 (k+5)%Z ltac:(sbp).
msb F_9313c D_9313c (k+6)%Z ltac:(sbp). msb F_93140 D_93140 (k+7)%Z ltac:(sbp).
stepn F_93144 D_93144.
mk_eq. apply mst_refl.
- post.
Qed.
#[using="HOK"] Lemma b16_blk : forall regs (ret : word) k (a2 : word),
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
(0 <= k)%Z -> (k + 16 <= n)%Z ->
exists regs',
msteps BSEGS (mkst regs (0x92eec : word) (MK k) rom) (mkst regs' (0x92f78 : word) (MK (k + 16)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 16)
/\ getr regs' 12 = a2 /\ keeps regs regs'.
Proof.
intros regs ret k a2 H1 H11 H13 H12 Hk Hk16. eexists. split.
- mlbu F_93068 D_93068 k. mlbu F_9306c D_9306c (k+1)%Z. mlbu F_93070 D_93070 (k+2)%Z. mlbu F_93074 D_93074 (k+3)%Z.
mlbu F_93078 D_93078 (k+4)%Z. mlbu F_9307c D_9307c (k+5)%Z. mlbu F_93080 D_93080 (k+6)%Z. mlbu F_93084 D_93084 (k+7)%Z.
msb F_93088 D_93088 k ltac:(sbp). msb F_9308c D_9308c (k+1)%Z ltac:(sbp).
msb F_93090 D_93090 (k+2)%Z ltac:(sbp). msb F_93094 D_93094 (k+3)%Z ltac:(sbp).
mlbu F_93098 D_93098 (k+8)%Z. mlbu F_9309c D_9309c (k+9)%Z. mlbu F_930a0 D_930a0 (k+10)%Z. mlbu F_930a4 D_930a4 (k+11)%Z.
msb F_930a8 D_930a8 (k+4)%Z ltac:(sbp). msb F_930ac D_930ac (k+5)%Z ltac:(sbp).
msb F_930b0 D_930b0 (k+6)%Z ltac:(sbp). msb F_930b4 D_930b4 (k+7)%Z ltac:(sbp).
mlbu F_930b8 D_930b8 (k+12)%Z. mlbu F_930bc D_930bc (k+13)%Z. mlbu F_930c0 D_930c0 (k+14)%Z. mlbu F_930c4 D_930c4 (k+15)%Z.
stepn F_930c8 D_930c8.
msb F_930cc D_930cc (k+8)%Z ltac:(sbp). msb F_930d0 D_930d0 (k+9)%Z ltac:(sbp).
msb F_930d4 D_930d4 (k+10)%Z ltac:(sbp). msb F_930d8 D_930d8 (k+11)%Z ltac:(sbp).
stepn F_930dc D_930dc.
msb F_930e0 D_930e0 (k+12)%Z ltac:(sbp). msb F_930e4 D_930e4 (k+13)%Z ltac:(sbp).
msb F_930e8 D_930e8 (k+14)%Z ltac:(sbp). msb F_930ec D_930ec (k+15)%Z ltac:(sbp).
stepn F_930f0 D_930f0.
mk_eq. apply mst_refl.
- post.
Qed.
#[using="HOK"] Lemma t4_run : forall regs (ret : word) k m,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
(Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
exists regs',
msteps BSEGS (mkst regs (0x92ca8 : word) (MK k) rom) (mkst regs' (0x93000 : word) (MK (k + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
- eexists. split.
+ stepn F_92e24 D_92e24.
stepb_ft F_92e28 D_92e28 ltac:(cond).
stepn F_92e2c D_92e2c.
mk_eq. apply mst_refl.
+ post.
- eapply (runs_trans BSEGS _ (fun r => mkst r (0x92fd4 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_92e24 D_92e24.
stepb_tk F_92e28 D_92e28 ltac:(cond).
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
msteps BSEGS (mkst regs (0x92fcc : word) (MK k) rom) (mkst regs' (0x93000 : word) (MK (k + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
- eexists. split.
+ stepn F_93148 D_93148.
stepb_tk F_9314c D_9314c ltac:(cond).
mk_eq. apply mst_refl.
+ post.
- eapply (runs_trans BSEGS _ (fun r => mkst r (0x92fd4 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_93148 D_93148.
stepb_ft F_9314c D_9314c ltac:(cond).
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
msteps BSEGS (mkst regs (0x92ca0 : word) (MK k) rom)
(mkst regs' (0x93000 : word) (MK (k + Z.land m 8 + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
/\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
destruct HL8 as [HL8|HL8].
-
eapply (runs_trans BSEGS _ (fun r => mkst r (0x92ca8 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_92e1c D_92e1c.
stepb_ft F_92e20 D_92e20 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
-
eapply (runs_trans BSEGS _ (fun r => mkst r (0x92f80 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_92e1c D_92e1c.
stepb_tk F_92e20 D_92e20 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
eapply (runs_trans BSEGS _ (fun r => mkst r (0x92fcc : word) (MK (k + 8)) rom)
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
msteps BSEGS (mkst regs (0x92f78 : word) (MK k) rom)
(mkst regs' (0x93000 : word) (MK (k + Z.land m 8 + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
/\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
destruct HL8 as [HL8|HL8].
- eapply (runs_trans BSEGS _ (fun r => mkst r (0x92ca8 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_930f4 D_930f4.
stepb_tk F_930f8 D_930f8 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
- eapply (runs_trans BSEGS _ (fun r => mkst r (0x92f80 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_930f4 D_930f4.
stepb_ft F_930f8 D_930f8 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
eapply (runs_trans BSEGS _ (fun r => mkst r (0x92fcc : word) (MK (k + 8)) rom)
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
msteps BSEGS (mkst regs (0x92c98 : word) (MK k) rom)
(mkst regs' (0x93000 : word) (MK (k + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
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
eapply (runs_trans BSEGS _ (fun r => mkst r (0x92ca0 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_92e14 D_92e14.
stepb_ft F_92e18 D_92e18 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (t8_run r1 ret k m R1 R11 R13 R12 ltac:(lia) Hk B8 B4 ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
-
eapply (runs_trans BSEGS _ (fun r => mkst r (0x92eec : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_92e14 D_92e14.
stepb_tk F_92e18 D_92e18 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
eapply (runs_trans BSEGS _ (fun r => mkst r (0x92f78 : word) (MK (k + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
* destruct (b16_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (b16_tail r2 ret (k + 16)%Z m S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.
End MIS.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
