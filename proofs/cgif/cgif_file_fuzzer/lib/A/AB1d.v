(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1a YK0s YK1b YK1h YK0v YE06.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB19 AB18 AB1u.
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
Ltac sbp := apply sb_val_plain.
Lemma b4_blk : forall regs (ret : word) k (a2 : word),
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
(0 <= k)%Z -> (k + 4 <= n)%Z ->
exists regs',
msteps TSEGS (mkst regs (0x97628 : word) (MK k) rom) (mkst regs' (0x97654 : word) (MK (k + 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 4) /\ getr regs' 13 = at_ dst (k + 4)
/\ getr regs' 12 = a2 /\ keeps regs regs'.
Proof.
intros regs ret k a2 H1 H11 H13 H12 Hk Hk4. eexists. split.
- mlbu F_11d414 D_11d414 k. mlbu F_11d418 D_11d418 (k+1)%Z. mlbu F_11d41c D_11d41c (k+2)%Z. mlbu F_11d420 D_11d420 (k+3)%Z.
stepn F_11d424 D_11d424.
stepn F_11d428 D_11d428.
msb F_11d42c D_11d42c k ltac:(sbp). msb F_11d430 D_11d430 (k+1)%Z ltac:(sbp).
msb F_11d434 D_11d434 (k+2)%Z ltac:(sbp). msb F_11d438 D_11d438 (k+3)%Z ltac:(sbp).
stepn F_11d43c D_11d43c.
mk_eq. apply mst_refl.
- post.
Qed.
Lemma b8_blk : forall regs (ret : word) k (a2 : word),
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
(0 <= k)%Z -> (k + 8 <= n)%Z ->
exists regs',
msteps TSEGS (mkst regs (0x975d4 : word) (MK k) rom) (mkst regs' (0x97620 : word) (MK (k + 8)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 8) /\ getr regs' 13 = at_ dst (k + 8)
/\ getr regs' 12 = a2 /\ keeps regs regs'.
Proof.
intros regs ret k a2 H1 H11 H13 H12 Hk Hk8. eexists. split.
- mlbu F_11d3c0 D_11d3c0 k. mlbu F_11d3c4 D_11d3c4 (k+1)%Z. mlbu F_11d3c8 D_11d3c8 (k+2)%Z. mlbu F_11d3cc D_11d3cc (k+3)%Z.
mlbu F_11d3d0 D_11d3d0 (k+4)%Z. mlbu F_11d3d4 D_11d3d4 (k+5)%Z. mlbu F_11d3d8 D_11d3d8 (k+6)%Z. mlbu F_11d3dc D_11d3dc (k+7)%Z.
stepn F_11d3e0 D_11d3e0.
msb F_11d3e4 D_11d3e4 k ltac:(sbp). msb F_11d3e8 D_11d3e8 (k+1)%Z ltac:(sbp).
msb F_11d3ec D_11d3ec (k+2)%Z ltac:(sbp). msb F_11d3f0 D_11d3f0 (k+3)%Z ltac:(sbp).
stepn F_11d3f4 D_11d3f4.
msb F_11d3f8 D_11d3f8 (k+4)%Z ltac:(sbp). msb F_11d3fc D_11d3fc (k+5)%Z ltac:(sbp).
msb F_11d400 D_11d400 (k+6)%Z ltac:(sbp). msb F_11d404 D_11d404 (k+7)%Z ltac:(sbp).
stepn F_11d408 D_11d408.
mk_eq. apply mst_refl.
- post.
Qed.
Lemma b16_blk : forall regs (ret : word) k (a2 : word),
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
(0 <= k)%Z -> (k + 16 <= n)%Z ->
exists regs',
msteps TSEGS (mkst regs (0x97540 : word) (MK k) rom) (mkst regs' (0x975cc : word) (MK (k + 16)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 16)
/\ getr regs' 12 = a2 /\ keeps regs regs'.
Proof.
intros regs ret k a2 H1 H11 H13 H12 Hk Hk16. eexists. split.
- mlbu F_11d32c D_11d32c k. mlbu F_11d330 D_11d330 (k+1)%Z. mlbu F_11d334 D_11d334 (k+2)%Z. mlbu F_11d338 D_11d338 (k+3)%Z.
mlbu F_11d33c D_11d33c (k+4)%Z. mlbu F_11d340 D_11d340 (k+5)%Z. mlbu F_11d344 D_11d344 (k+6)%Z. mlbu F_11d348 D_11d348 (k+7)%Z.
msb F_11d34c D_11d34c k ltac:(sbp). msb F_11d350 D_11d350 (k+1)%Z ltac:(sbp).
msb F_11d354 D_11d354 (k+2)%Z ltac:(sbp). msb F_11d358 D_11d358 (k+3)%Z ltac:(sbp).
mlbu F_11d35c D_11d35c (k+8)%Z. mlbu F_11d360 D_11d360 (k+9)%Z. mlbu F_11d364 D_11d364 (k+10)%Z. mlbu F_11d368 D_11d368 (k+11)%Z.
msb F_11d36c D_11d36c (k+4)%Z ltac:(sbp). msb F_11d370 D_11d370 (k+5)%Z ltac:(sbp).
msb F_11d374 D_11d374 (k+6)%Z ltac:(sbp). msb F_11d378 D_11d378 (k+7)%Z ltac:(sbp).
mlbu F_11d37c D_11d37c (k+12)%Z. mlbu F_11d380 D_11d380 (k+13)%Z. mlbu F_11d384 D_11d384 (k+14)%Z. mlbu F_11d388 D_11d388 (k+15)%Z.
stepn F_11d38c D_11d38c.
msb F_11d390 D_11d390 (k+8)%Z ltac:(sbp). msb F_11d394 D_11d394 (k+9)%Z ltac:(sbp).
msb F_11d398 D_11d398 (k+10)%Z ltac:(sbp). msb F_11d39c D_11d39c (k+11)%Z ltac:(sbp).
stepn F_11d3a0 D_11d3a0.
msb F_11d3a4 D_11d3a4 (k+12)%Z ltac:(sbp). msb F_11d3a8 D_11d3a8 (k+13)%Z ltac:(sbp).
msb F_11d3ac D_11d3ac (k+14)%Z ltac:(sbp). msb F_11d3b0 D_11d3b0 (k+15)%Z ltac:(sbp).
stepn F_11d3b4 D_11d3b4.
mk_eq. apply mst_refl.
- post.
Qed.
Lemma t4_run : forall regs (ret : word) k m,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
(Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
exists regs',
msteps TSEGS (mkst regs (0x972fc : word) (MK k) rom) (mkst regs' (0x97654 : word) (MK (k + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
- eexists. split.
+ stepn F_11d0e8 D_11d0e8.
stepb_ft F_11d0ec D_11d0ec ltac:(cond).
stepn F_11d0f0 D_11d0f0.
mk_eq. apply mst_refl.
+ post.
- eapply (runs_trans TSEGS _ (fun r => mkst r (0x97628 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_11d0e8 D_11d0e8.
stepb_tk F_11d0ec D_11d0ec ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.
Lemma b8_tail : forall regs (ret : word) k m,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
(Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
exists regs',
msteps TSEGS (mkst regs (0x97620 : word) (MK k) rom) (mkst regs' (0x97654 : word) (MK (k + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
- eexists. split.
+ stepn F_11d40c D_11d40c.
stepb_tk F_11d410 D_11d410 ltac:(cond).
mk_eq. apply mst_refl.
+ post.
- eapply (runs_trans TSEGS _ (fun r => mkst r (0x97628 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_11d40c D_11d40c.
stepb_ft F_11d410 D_11d410 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.
Lemma t8_run : forall regs (ret : word) k m,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
(Z.land m 8 = 0 \/ Z.land m 8 = 8)%Z -> (Z.land m 4 = 0 \/ Z.land m 4 = 4)%Z ->
(k + Z.land m 8 + Z.land m 4 <= n)%Z ->
exists regs',
msteps TSEGS (mkst regs (0x972f4 : word) (MK k) rom)
(mkst regs' (0x97654 : word) (MK (k + Z.land m 8 + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
/\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
destruct HL8 as [HL8|HL8].
-
eapply (runs_trans TSEGS _ (fun r => mkst r (0x972fc : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_11d0e0 D_11d0e0.
stepb_ft F_11d0e4 D_11d0e4 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
-
eapply (runs_trans TSEGS _ (fun r => mkst r (0x975d4 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_11d0e0 D_11d0e0.
stepb_tk F_11d0e4 D_11d0e4 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
eapply (runs_trans TSEGS _ (fun r => mkst r (0x97620 : word) (MK (k + 8)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
* destruct (b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia)) as (r3 & RUN & P).
exists r3. rewrite HL8. replace (k + 8 + Z.land m 4)%Z with (k + 8 + Z.land m 4)%Z by lia.
split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.
Lemma b16_tail : forall regs (ret : word) k m,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
(Z.land m 8 = 0 \/ Z.land m 8 = 8)%Z -> (Z.land m 4 = 0 \/ Z.land m 4 = 4)%Z ->
(k + Z.land m 8 + Z.land m 4 <= n)%Z ->
exists regs',
msteps TSEGS (mkst regs (0x975cc : word) (MK k) rom)
(mkst regs' (0x97654 : word) (MK (k + Z.land m 8 + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
/\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
destruct HL8 as [HL8|HL8].
- eapply (runs_trans TSEGS _ (fun r => mkst r (0x972fc : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_11d3b8 D_11d3b8.
stepb_tk F_11d3bc D_11d3bc ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
- eapply (runs_trans TSEGS _ (fun r => mkst r (0x975d4 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_11d3b8 D_11d3b8.
stepb_ft F_11d3bc D_11d3bc ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
eapply (runs_trans TSEGS _ (fun r => mkst r (0x97620 : word) (MK (k + 8)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
* destruct (b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia)) as (r3 & RUN & P).
exists r3. rewrite HL8. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.
Lemma t16_run : forall regs (ret : word) k m,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
(0 <= m < 32)%Z -> (0 <= k)%Z ->
(k + Z.land m 16 + Z.land m 8 + Z.land m 4 <= n)%Z ->
exists regs',
msteps TSEGS (mkst regs (0x972ec : word) (MK k) rom)
(mkst regs' (0x97654 : word) (MK (k + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
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
eapply (runs_trans TSEGS _ (fun r => mkst r (0x972f4 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_11d0d8 D_11d0d8.
stepb_ft F_11d0dc D_11d0dc ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (t8_run r1 ret k m R1 R11 R13 R12 ltac:(lia) Hk B8 B4 ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
-
eapply (runs_trans TSEGS _ (fun r => mkst r (0x97540 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
+ eexists. split.
* stepn F_11d0d8 D_11d0d8.
stepb_tk F_11d0dc D_11d0dc ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
eapply (runs_trans TSEGS _ (fun r => mkst r (0x975cc : word) (MK (k + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
* destruct (b16_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (b16_tail r2 ret (k + 16)%Z m S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.
End d.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
