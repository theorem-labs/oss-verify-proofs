(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1a YK0s YK1b YK1h YK0v YE06.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB19 AB18 AB1d AB1a AB1b AB1c AB1u.
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
Ltac conda := rwH; unfold at_; cond.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma al_finish : forall regs (ret : word) k,
ret_ok ret -> getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
(0 <= k <= n)%Z ->
exists regs',
msteps TSEGS (mkst regs (0x973b4 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
/\ keeps regs regs'.
Proof.
intros regs ret k Hret H1 H11 H13 H12 Hk.
set (m := ((n - k) mod 16)%Z).
pose proof (Z.mod_pos_bound (n - k) 16 ltac:(lia)) as Hm16.
destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (0 <= Z.land m 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
assert (Hl16 : Z.land m 16 = 0%Z) by (destruct B16 as [E|E]; [exact E|exfalso; lia]).
eapply (runs_trans TSEGS _ (fun r => mkst r (0x973f0 : word) (MK (n - m)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m) /\ getr r 13 = at_ dst (n - m) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
{ destruct (al16_run _ _ _ _ _ rom HOK regs ret k H1 H11 H13 H12 Hk) as (r & R & P). exists r.
subst m. split; [exact R|]. decompose [and] P. repeat split; try assumption. }
cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
eapply (runs_trans TSEGS _ (fun r => mkst r (0x97410 : word) (MK (n - m + Z.land m 8)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8) /\ getr r 13 = at_ dst (n - m + Z.land m 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
{ destruct (al8_run _ _ _ _ _ rom HOK r2 ret (n - m) m (Z.land m 8) S1 S11 S13 S12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r & R & P).
exists r. split; [exact R|]. decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption. }
cbv beta. intros r3 (T1 & T11 & T13 & T12 & K3).
eapply (runs_trans TSEGS _ (fun r => mkst r (0x97654 : word) (MK (n - m + Z.land m 8 + Z.land m 4)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8 + Z.land m 4) /\ getr r 13 = at_ dst (n - m + Z.land m 8 + Z.land m 4) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
{ destruct (al4_run _ _ _ _ _ rom HOK r3 ret (n - m + Z.land m 8) m T1 T11 T13 T12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r & R & P).
exists r. split; [exact R|]. decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption. }
cbv beta. intros r4 (U1 & U11 & U13 & U12 & K4).
destruct (t2_run _ _ _ _ _ rom HOK r4 ret (n - m + Z.land m 8 + Z.land m 4) m Hret U1 U11 U13 U12 ltac:(lia) B2 B1 ltac:(lia) ltac:(lia)) as (r & R & P).
exists r. split; [exact R | eapply keeps_trans; eassumption].
Qed.
Lemma mis_run : forall regs (ret : word) k q,
ret_ok ret -> getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
getr regs 15 = Z_to_bv 64 q -> (q = 1 \/ q = 2 \/ q = 3)%Z ->
(0 <= k <= n)%Z ->
exists regs',
msteps TSEGS (mkst regs (0x972e4 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
/\ keeps regs regs'.
Proof.
intros regs ret k q Hret H1 H11 H13 H12 H15 Hq Hk.
destruct (Z.lt_ge_cases (n - k) 32) as [Hsmall|Hbig].
-
destruct (bits_lt32 (n - k) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (0 <= Z.land (n - k) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - k) 4)%Z by (apply Z.land_nonneg; lia).
assert (0 <= Z.land (n - k) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - k) 1)%Z by (apply Z.land_nonneg; lia).
assert (0 <= Z.land (n - k) 16)%Z by (apply Z.land_nonneg; lia).
eapply (runs_trans TSEGS _ (fun r => mkst r (0x972ec : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k) /\ keeps regs r)).
+ eexists. split.
* stepn F_11d0d0 D_11d0d0.
stepb_ft F_11d0d4 D_11d0d4 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
set (m := (n - k)%Z) in *.
eapply (runs_trans TSEGS _ (fun r => mkst r (0x97654 : word) (MK (k + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
/\ getr r 13 = at_ dst (k + Z.land m 16 + Z.land m 8 + Z.land m 4) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
* destruct (t16_run _ _ _ _ _ rom HOK r1 ret k m R1 R11 R13 R12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (t2_run _ _ _ _ _ rom HOK r2 ret (k + Z.land m 16 + Z.land m 8 + Z.land m 4)%Z m Hret S1 S11 S13 S12
ltac:(lia) B2 B1 ltac:(lia) ltac:(lia)) as (r3 & RUN & K3).
exists r3. split; [exact RUN | eapply keeps_trans; eassumption].
-
eapply (runs_trans TSEGS _ (fun r => mkst r (0x97308 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k)
/\ getr r 15 = Z_to_bv 64 q /\ keeps regs r)).
+ eexists. split.
* stepn F_11d0d0 D_11d0d0.
stepb_tk F_11d0d4 D_11d0d4 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R15 & K1).
assert (CASE : exists regs' m,
msteps TSEGS (mkst r1 (0x97308 : word) (MK k) rom)
(mkst regs' (0x97654 : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
/\ (0 <= m < 32)%Z
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
/\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps r1 regs').
{ destruct Hq as [-> | [-> | ->]].
- apply (c1_run _ _ _ _ _ rom HOK r1 ret k); try assumption; lia.
- apply (c2_run _ _ _ _ _ rom HOK r1 ret k); try assumption; lia.
- apply (c3_run _ _ _ _ _ rom HOK r1 ret k); try assumption; lia. }
destruct CASE as (r2 & m & RUN & Hm & S1 & S11 & S13 & S12 & K2).
destruct (bits_lt32 m Hm) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
destruct (t2_run _ _ _ _ _ rom HOK r2 ret (n - (Z.land m 2 + Z.land m 1))%Z m Hret S1 S11 S13 S12
ltac:(lia) B2 B1 ltac:(lia) ltac:(lia)) as (r3 & RUN3 & K3).
exists r3. split; [eapply msteps_trans; [exact RUN | exact RUN3] |].
eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
Qed.
Lemma j_run : forall regs (ret : word) k,
ret_ok ret -> getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
(0 <= k <= n)%Z ->
exists regs',
msteps TSEGS (mkst regs (0x972dc : word) (MK k) rom) (mkst regs' ret (MK n) rom)
/\ keeps regs regs'.
Proof.
intros regs ret k Hret H1 H11 H13 H12 Hk.
pose proof (u64_range dst).
set (q := ((bv_unsigned dst + k) mod 4)%Z).
pose proof (Z.mod_pos_bound (bv_unsigned dst + k) 4 ltac:(lia)) as Hq4.
destruct (Z.eq_dec q 0) as [Hq0|Hq0].
-
eapply (runs_trans TSEGS _ (fun r => mkst r (0x973b4 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k) /\ keeps regs r)).
+ eexists. split.
* stepn F_11d0c8 D_11d0c8.
stepb_tk F_11d0cc D_11d0cc ltac:(conda).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (al_finish r1 ret k Hret R1 R11 R13 R12 Hk) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
- eapply (runs_trans TSEGS _ (fun r => mkst r (0x972e4 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k)
/\ getr r 15 = Z_to_bv 64 q /\ keeps regs r)).
+ eexists. split.
* stepn F_11d0c8 D_11d0c8.
stepb_ft F_11d0cc D_11d0cc ltac:(conda).
apply mst_refl.
* cbv beta. post. unfold v_andi, at_. subst q. rewrite <- land_3 by lia. unorm.
change (bv_wrap 64 3) with 3%Z. reflexivity.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R15 & K1).
destruct (mis_run r1 ret k q Hret R1 R11 R13 R12 R15 ltac:(lia) Hk) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
Qed.
Lemma hl_loop : forall (i : nat) regs (ret : word) k,
ret_ok ret -> getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
getr regs 14 = at_ src (k + 1) -> getr regs 15 = Z_to_bv 64 1 ->
(0 <= k)%Z -> (k < n)%Z -> ((bv_unsigned src + k) mod 4 <> 0)%Z ->
(Z.of_nat i + 1 = Z.min (n - k) (4 - (bv_unsigned src + k) mod 4))%Z ->
exists regs',
msteps TSEGS (mkst regs (0x972ac : word) (MK k) rom) (mkst regs' ret (MK n) rom)
/\ keeps regs regs'.
Proof.
induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 H14 H15 Hk Hkn Hal Hi.
-
pose proof (u64_range src).
destruct (Z.eq_dec ((bv_unsigned src + (k + 1)) mod 4) 0) as [Hz|Hz].
+ eapply (runs_trans TSEGS _ (fun r => mkst r (0x972dc : word) (MK (k + 1)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1)) /\ keeps regs r)).
* eexists. split.
-- mlbu F_11d098 D_11d098 k.
stepn F_11d09c D_11d09c.
stepn F_11d0a0 D_11d0a0.
stepn F_11d0a4 D_11d0a4.
msb F_11d0a8 D_11d0a8 k ltac:(apply sb_val_plain).
stepn F_11d0ac D_11d0ac.
stepn F_11d0b0 D_11d0b0.
stepb_tk F_11d0b4 D_11d0b4 ltac:(conda).
apply mst_refl.
-- cbv beta. post. unfold v_addi. unorm. f_equal. lia.
* cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (j_run r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
+ eapply (runs_trans TSEGS _ (fun r => mkst r (0x972dc : word) (MK (k + 1)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1)) /\ keeps regs r)).
* eexists. split.
-- mlbu F_11d098 D_11d098 k.
stepn F_11d09c D_11d09c.
stepn F_11d0a0 D_11d0a0.
stepn F_11d0a4 D_11d0a4.
msb F_11d0a8 D_11d0a8 k ltac:(apply sb_val_plain).
stepn F_11d0ac D_11d0ac.
stepn F_11d0b0 D_11d0b0.
stepb_ft F_11d0b4 D_11d0b4 ltac:(conda).
stepn F_11d0b8 D_11d0b8.
stepb_ft F_11d0bc D_11d0bc ltac:(cond).
stepn F_11d0c0 D_11d0c0.
apply mst_refl.
-- cbv beta. post. unfold v_addi. unorm. f_equal. lia.
* cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (j_run r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
-
pose proof (u64_range src).
eapply (runs_trans TSEGS _ (fun r => mkst r (0x972ac : word) (MK (k + 1)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1))
/\ getr r 14 = at_ src (k + 1 + 1) /\ getr r 15 = Z_to_bv 64 1 /\ keeps regs r)).
+ eexists. split.
* mlbu F_11d098 D_11d098 k.
stepn F_11d09c D_11d09c.
stepn F_11d0a0 D_11d0a0.
stepn F_11d0a4 D_11d0a4.
msb F_11d0a8 D_11d0a8 k ltac:(apply sb_val_plain).
stepn F_11d0ac D_11d0ac.
stepn F_11d0b0 D_11d0b0.
stepb_ft F_11d0b4 D_11d0b4 ltac:(conda).
stepn F_11d0b8 D_11d0b8.
stepb_tk F_11d0bc D_11d0bc ltac:(cond).
apply mst_refl.
* cbv beta. post. unfold v_addi. unorm. f_equal. lia.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
destruct (IH r1 ret (k + 1)%Z Hret R1 R11 R13 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
Qed.
Theorem ref_memcpy : forall regs (ret : word),
ret_ok ret -> getr regs 1 = ret ->
getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
exists regs',
msteps TSEGS (mkst regs (0x97294 : word) mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
/\ keeps regs regs'.
Proof.
intros regs ret Hret H1 H10 H11 H12.
pose proof (u64_range src). pose proof (u64_range dst).
rewrite <- (memk_n _ _ _ _ _ HOK). change mem0 with (MK 0).
assert (H11' : getr regs 11 = at_ src 0) by (rewrite at_0; exact H11).
assert (H12' : getr regs 12 = Z_to_bv 64 (n - 0)) by (rewrite Z.sub_0_r; exact H12).
destruct (Z.eq_dec (bv_unsigned src mod 4) 0) as [Hs4|Hs4].
-
destruct (Z.eq_dec (bv_unsigned dst mod 4) 0) as [Hd4|Hd4].
+ eapply (runs_trans TSEGS _ (fun r => mkst r (0x973b4 : word) (MK 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0) /\ keeps regs r)).
* eexists. split.
-- stepn F_11d080 D_11d080.
stepb_tk F_11d084 D_11d084 ltac:(conda).
stepn F_11d194 D_11d194.
stepn F_11d198 D_11d198.
stepb_ft F_11d19c D_11d19c ltac:(cond).
apply mst_refl.
-- cbv beta. post. rewrite at_0. reflexivity.
* cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (al_finish r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
+ eapply (runs_trans TSEGS _ (fun r => mkst r (0x972e4 : word) (MK 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0)
/\ getr r 15 = Z_to_bv 64 (bv_unsigned dst mod 4) /\ keeps regs r)).
* eexists. split.
-- stepn F_11d080 D_11d080.
stepb_tk F_11d084 D_11d084 ltac:(conda).
stepn F_11d194 D_11d194.
stepn F_11d198 D_11d198.
stepb_tk F_11d19c D_11d19c ltac:(cond).
apply mst_refl.
-- cbv beta. post; try (rewrite at_0; reflexivity).
unfold v_andi. rewrite <- land_3 by lia. change (bv_wrap 64 3) with 3%Z. reflexivity.
* cbv beta. intros r1 (R1 & R11 & R13 & R12 & R15 & K1).
pose proof (Z.mod_pos_bound (bv_unsigned dst) 4 ltac:(lia)).
destruct (mis_run r1 ret 0 (bv_unsigned dst mod 4) Hret R1 R11 R13 R12 R15 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
-
destruct (Z.eq_dec n 0) as [Hn0z|Hn0z].
+ eapply (runs_trans TSEGS _ (fun r => mkst r (0x972dc : word) (MK 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0) /\ keeps regs r)).
* eexists. split.
-- stepn F_11d080 D_11d080.
stepb_ft F_11d084 D_11d084 ltac:(conda).
stepb_tk F_11d088 D_11d088 ltac:(cond).
stepn F_11d0c4 D_11d0c4.
apply mst_refl.
-- cbv beta. post. rewrite at_0. reflexivity.
* cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (j_run r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
+ set (i := Z.to_nat (Z.min n (4 - bv_unsigned src mod 4) - 1)).
pose proof (Z.mod_pos_bound (bv_unsigned src) 4 ltac:(lia)).
eapply (runs_trans TSEGS _ (fun r => mkst r (0x972ac : word) (MK 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0)
/\ getr r 14 = at_ src (0 + 1) /\ getr r 15 = Z_to_bv 64 1 /\ keeps regs r)).
* eexists. split.
-- stepn F_11d080 D_11d080.
stepb_ft F_11d084 D_11d084 ltac:(conda).
stepb_ft F_11d088 D_11d088 ltac:(cond).
stepn F_11d08c D_11d08c.
stepn F_11d090 D_11d090.
stepn F_11d094 D_11d094.
apply mst_refl.
-- cbv beta. post. rewrite at_0. reflexivity.
* cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
destruct (hl_loop i r1 ret 0 Hret R1 R11 R13 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_0_r; exact Hs4)) as (r2 & RUN & K2).
{ subst i. rewrite Z.add_0_r, Z.sub_0_r. rewrite Z2Nat.id; lia. }
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
Qed.
End d.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
