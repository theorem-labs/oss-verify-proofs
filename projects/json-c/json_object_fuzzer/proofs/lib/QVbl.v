(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDM_c1 Lib.CodeAt Lib.StepGen Lib.GwCallee.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QnDM_c1.

Import ListNotations. Unset Keyed Unification.
Open Scope bv_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core.
Local Ltac zstep ::= sg_zstep. Local Ltac mkr__zstep_1 := sg_zstep.

Definition fe_getround_code (w_5 w_6 : Z) : list Z :=
[0x00202573; 0xfff5051b; 0x00200593; 0x00a5ee63; 0x00251513; w_5; w_6; 0x00a58533; 0x00052503; 0x00008067; 0x00000513; 0x00008067; 0x0010e073; 0x00000513; 0x00008067]%Z.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_5 w_6 : Z).
Hypothesis CODE : code_at segs base (fe_getround_code w_5 w_6).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 60.

Definition fe_getround_entry := (base + 0x0)%Z.
Definition fe_raise_inexact_entry := (base + 0x30)%Z.

Definition fe_getround_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists a1,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom segs)
/\ munch [] m m /\ wmono segs m m /\ mem_inv segs m.

#[using="CODE BASE4 BASER"] Lemma fe_getround_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte),
mem_inv segs m -> frm0 fc ->
evt segs (fe_getround_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof.
intros until m. intros MI FRM.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl segs m) as WM.
do 4 zstep. if_cases K; zify_cond K.
- zstep. zstep. finish.
- exfalso. revert K. vm_compute. congruence.
Qed.

Definition fe_raise_inexact_post (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists fc',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc' None m (seg_rom segs)
/\ munch [] m m /\ wmono segs m m /\ mem_inv segs m /\ frm0 fc'.

#[using="CODE BASE4 BASER"] Lemma fe_raise_inexact_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte),
mem_inv segs m -> frm0 fc ->
evt segs (fe_raise_inexact_post ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x30)) fc None m (seg_rom segs)).
Proof.
intros until m. intros MI FRM.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl segs m) as WM.
do 3 zstep. finish.
Qed.

End G.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import QZAi.

Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core.
Local Ltac zstep ::= sg_zstep. Local Ltac mkr__zstep_1 := sg_zstep.

Definition getf2_code : list Z :=
[0xfff00713; 0x07fff8b7; 0x00175813; 0x0105f7b3; 0x02489893; 0x01178a63; 0x00f8b8b3; 0x00088a63; 0x00070513; 0x00008067; 0x00a038b3; 0xfe089ae3; 0x0106f833; 0x07fff8b7; 0x02489893; 0x01180863; 0x0108b8b3; 0x00088863; 0xfd9ff06f; 0x00c038b3; 0xfc0898e3; 0x00a668b3; 0x00f867b3; 0x00f8e7b3; 0x00078e63; 0x00b6f7b3; 0x0007ce63; 0x02d58463; 0x00d5a7b3; 0xfa0796e3; 0x0300006f; 0x00000513; 0x00008067; 0x00d58e63; 0x00b6a7b3; 0xf8079ae3; 0x0180006f; 0x00c537b3; 0xf80794e3; 0x00c0006f; 0x00a637b3; 0xf6079ee3; 0x00c54533; 0x00d5c5b3; 0x00b56533; 0x00a03533; 0x00008067]%Z.

Section G.
Variables (segs : list Segment) (base : Z).
Hypothesis CODE : code_at segs base getf2_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 188.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition getf2_entry := (base + 0x0)%Z.

Definition ge_isnan_w (lo hi : Z) : bool :=
(let absHi := Z.land hi ABS_HI in
if absHi =? INF_HI then negb (lo =? 0) else INF_HI <? absHi)%Z.

Definition ge_isless (a_lo a_hi b_lo b_hi : Z) : bool :=
(if negb (is_neg64 (Z.land b_hi a_hi)) then
(if a_hi =? b_hi then a_lo <? b_lo else lt_s64 a_hi b_hi)
else
(if a_hi =? b_hi then b_lo <? a_lo else lt_s64 b_hi a_hi))%Z.

Definition ge_tail (il : bool) (a_lo a_hi b_lo b_hi : Z) : Z :=
if il then (-1)%Z else nez64 (Z.lor (Z.lxor a_lo b_lo) (Z.lxor a_hi b_hi)).

Definition ge_core (a_lo a_hi b_lo b_hi : Z) : Z :=
(if Z.lor (Z.lor b_lo a_lo) (Z.lor (Z.land b_hi ABS_HI) (Z.land a_hi ABS_HI)) =? 0 then 0
else ge_tail (ge_isless a_lo a_hi b_lo b_hi) a_lo a_hi b_lo b_hi)%Z.

#[using="CODE BASE4 BASER"] Lemma lo64_words : forall lo hi, (0 <= lo < 2^64)%Z -> lo64 (lo + 2^64 * hi) = lo.
Proof.
intros lo hi H. unfold lo64. rewrite wrap64_mod.
rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

#[using="CODE BASE4 BASER"] Lemma hi64_words : forall lo hi, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z -> hi64 (lo + 2^64 * hi) = hi.
Proof.
intros lo hi Hl Hh. unfold hi64. rewrite wrap64_mod, Z.shiftr_div_pow2 by lia.
rewrite Z.mul_comm, Z.div_add, Z.div_small by lia. apply Z.mod_small. lia.
Qed.

#[using="CODE BASE4 BASER"] Lemma f128_ge_split : forall a_lo a_hi b_lo b_hi,
(0 <= a_lo < 2^64)%Z -> (0 <= a_hi < 2^64)%Z -> (0 <= b_lo < 2^64)%Z -> (0 <= b_hi < 2^64)%Z ->
f128_ge (a_lo + 2^64 * a_hi) (b_lo + 2^64 * b_hi) =
if ge_isnan_w a_lo a_hi then (-1)%Z
else if ge_isnan_w b_lo b_hi then (-1)%Z
else ge_core a_lo a_hi b_lo b_hi.
Proof.
intros. unfold f128_ge. rewrite !lo64_words, !hi64_words by assumption. reflexivity.
Qed.

#[using="CODE BASE4 BASER"] Lemma b2z_snez : forall x, (0 <= x)%Z -> Z.b2z (0 <? x)%Z = nez64 x.
Proof.
intros x Hx. unfold nez64, b2z. destruct (Z.ltb_spec0 0 x); destruct (Z.eqb_spec x 0); cbn; lia.
Qed.

Definition getf2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(r : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [] m m' /\ wmono segs m m' /\ mem_inv segs m'.

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Hypothesis MI : mem_inv segs m.
Let MU : munch [] m m := munch_refl [] m.
Let WM : wmono segs m m := wmono_refl segs m.

Notation a_lo := (bv_unsigned a0). Notation a_hi := (bv_unsigned a1).
Notation b_lo := (bv_unsigned a2). Notation b_hi := (bv_unsigned a3).
Notation POST r := (getf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m).

Notation ST pc x14 x15 x16 x17 :=
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom segs)).
Notation M63 := 9223372036854775807%Z.

Lemma getf2_L54 : forall (a4 a5 a6 a7 : word) (r : Z),
r = nez64 (Z.lor (Z.lxor a_lo b_lo) (Z.lxor a_hi b_hi)) ->
evt segs (POST r) (ST (base + 0xa8) a4 a5 a6 a7).
Proof using CODE BASE4 BASER MI.
intros a4 a5 a6 a7 r HR. subst r.
do 5 zstep. rewrite b2z_snez by zrange_nonneg. finish.
Qed.

Lemma getf2_Lcc : forall (a5 a6 a7 : word) (r : Z),
r = (-1)%Z ->
evt segs (POST r) (ST (base + 0x20) (Z_to_bv 64 (-1)) a5 a6 a7).
Proof using CODE BASE4 BASER MI.
intros a5 a6 a7 r HR. subst r. zstep. zstep. finish.
Qed.

Lemma getf2_L00 : forall (a7 : word) (r : Z),
r = ge_core a_lo a_hi b_lo b_hi ->
evt segs (POST r) (ST (base + 0x54) (Z_to_bv 64 (-1)) (Z_to_bv 64 (Z.land a_hi M63)) (Z_to_bv 64 (Z.land b_hi M63)) a7).
Proof using CODE BASE4 BASER MI.
intros a7 r HR. subst r. unfold ge_core, ABS_HI.
zr_pose (Z.land b_hi a_hi).
do 4 zstep.
if_cases Kz; zify_cond Kz.
-
zstep. zstep. decide_tests_b. finish.
- decide_tests_b. unfold ge_isless, ge_tail, is_neg64, lt_s64, SIGN64.
zstep. zstep. if_cases Kn; zify_cond Kn; decide_tests_b.
+
zstep. if_cases Ke; zify_cond Ke; decide_tests_b.
*  zstep. zstep. if_cases Kl; zify_cond Kl; decide_tests_b.
-- apply getf2_Lcc. reflexivity.
-- apply getf2_L54. reflexivity.
* zstep. zstep. if_cases Kl; zify_cond Kl; decide_tests_b.
-- apply getf2_Lcc. reflexivity.
-- zstep. apply getf2_L54. reflexivity.
+ zstep. if_cases Ke; zify_cond Ke; decide_tests_b.
* zstep. zstep. if_cases Kl; zify_cond Kl; decide_tests_b.
-- apply getf2_Lcc. reflexivity.
-- zstep. apply getf2_L54. reflexivity.
* zstep. zstep. if_cases Kl; zify_cond Kl; decide_tests_b.
-- apply getf2_Lcc. reflexivity.
-- zstep. apply getf2_L54. reflexivity.
Qed.

Lemma getf2_Ldc : forall (a7 : word) (r : Z),
r = (if ge_isnan_w b_lo b_hi then (-1)%Z else ge_core a_lo a_hi b_lo b_hi) ->
evt segs (POST r) (ST (base + 0x30) (Z_to_bv 64 (-1)) (Z_to_bv 64 (Z.land a_hi M63)) (Z_to_bv 64 M63) a7).
Proof using CODE BASE4 BASER MI.
intros a7 r HR. unfold ge_isnan_w, ABS_HI, INF_HI in HR.
do 4 zstep.
if_cases K; zify_cond K.
-
zstep. zstep. if_cases Kl; zify_cond Kl.
+  apply getf2_Lcc. rewrite HR. decide_tests_b. reflexivity.
+ apply getf2_L00. rewrite HR. decide_tests_b. reflexivity.
- zstep. zstep. if_cases Kl; zify_cond Kl.
+ apply getf2_L00. rewrite HR. decide_tests_b. reflexivity.
+ zstep. apply getf2_Lcc. rewrite HR. decide_tests_b. reflexivity.
Qed.
End Proofs.

#[using="CODE BASE4 BASER"] Lemma getf2_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte),
mem_inv segs m ->
evt segs (getf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
(f128_ge (bv_unsigned a0 + 2^64 * bv_unsigned a1) (bv_unsigned a2 + 2^64 * bv_unsigned a3)) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof.
intros until m. intros MI.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl segs m) as WM.
rewrite f128_ge_split by (pose proof (bv_unsigned_in_range 64 a0); pose proof (bv_unsigned_in_range 64 a1);
pose proof (bv_unsigned_in_range 64 a2); pose proof (bv_unsigned_in_range 64 a3);
unfold bv_modulus in *; lia).
remember (if ge_isnan_w (bv_unsigned a0) (bv_unsigned a1) then _ else _) as r eqn:HR.
unfold ge_isnan_w at 1, ABS_HI, INF_HI in HR.
do 6 zstep.
if_cases K; zify_cond K.
-
do 2 zstep. if_cases Kl; zify_cond Kl.
+ apply getf2_Lcc; [exact MI|]. rewrite HR. decide_tests_b. reflexivity.
+ apply getf2_Ldc; [exact MI|]. rewrite HR. decide_tests_b. reflexivity.
- do 2 zstep. if_cases Kl; zify_cond Kl.
+ apply getf2_Ldc; [exact MI|]. rewrite HR. decide_tests_b. reflexivity.
+ apply getf2_Lcc; [exact MI|]. rewrite HR. decide_tests_b. reflexivity.
Qed.

End G.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import QZAi.

Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core.
Local Ltac zstep ::= sg_zstep. Local Ltac mkr__zstep_1 := sg_zstep.

Definition letf2_code : list Z :=
[0xfff00713; 0x07fff8b7; 0x00175813; 0x0105f7b3; 0x02489713; 0x00e78c63; 0x00f738b3; 0x00100713; 0x00088c63; 0x00070513; 0x00008067; 0x00a038b3; 0x00100713; 0xfe0898e3; 0x0106f833; 0x07fff8b7; 0x02489893; 0x01180863; 0x0108b8b3; 0x00088863; 0xfd5ff06f; 0x00c038b3; 0xfc0896e3; 0x00a66733; 0x00f867b3; 0x00f76733; 0xfa070ee3; 0x00b6f733; 0x00074a63; 0x02d58063; 0x00d5a733; 0x02071063; 0x0340006f; 0x02d58063; 0x00b6a733; 0x02071063; 0x0240006f; 0x00c53733; 0x00070e63; 0xfff00513; 0x00008067; 0x00a63733; 0x00070663; 0xfff00513; 0x00008067; 0x00c54533; 0x00d5c5b3; 0x00b56533; 0x00a03533; 0x00008067]%Z.

Section G.
Variables (segs : list Segment) (base : Z).
Hypothesis CODE : code_at segs base letf2_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 200.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition letf2_entry := (base + 0x0)%Z.

Definition f128_isnan_w (lo hi : Z) : bool :=
(let absHi := Z.land hi ABS_HI in
if absHi =? INF_HI then negb (lo =? 0) else INF_HI <? absHi)%Z.

Definition f128_le_isless (a_lo a_hi b_lo b_hi : Z) : bool :=
(if negb (is_neg64 (Z.land b_hi a_hi)) then
(if a_hi =? b_hi then a_lo <? b_lo else lt_s64 a_hi b_hi)
else
(if a_hi =? b_hi then b_lo <? a_lo else lt_s64 b_hi a_hi))%Z.

Definition f128_le_tail (il : bool) (a_lo a_hi b_lo b_hi : Z) : Z :=
if il then (-1)%Z else nez64 (Z.lor (Z.lxor a_lo b_lo) (Z.lxor a_hi b_hi)).

Definition f128_le_core (a_lo a_hi b_lo b_hi : Z) : Z :=
(if Z.lor (Z.lor b_lo a_lo) (Z.lor (Z.land b_hi ABS_HI) (Z.land a_hi ABS_HI)) =? 0 then 0
else f128_le_tail (f128_le_isless a_lo a_hi b_lo b_hi) a_lo a_hi b_lo b_hi)%Z.

#[using="CODE BASE4 BASER"] Lemma lo64_words : forall lo hi, (0 <= lo < 2^64)%Z -> lo64 (lo + 2^64 * hi) = lo.
Proof.
intros lo hi H. unfold lo64. rewrite wrap64_mod.
rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

#[using="CODE BASE4 BASER"] Lemma hi64_words : forall lo hi, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z -> hi64 (lo + 2^64 * hi) = hi.
Proof.
intros lo hi Hl Hh. unfold hi64. rewrite wrap64_mod, Z.shiftr_div_pow2 by lia.
rewrite Z.mul_comm, Z.div_add, Z.div_small by lia. apply Z.mod_small. lia.
Qed.

#[using="CODE BASE4 BASER"] Lemma f128_le_split : forall a_lo a_hi b_lo b_hi,
(0 <= a_lo < 2^64)%Z -> (0 <= a_hi < 2^64)%Z -> (0 <= b_lo < 2^64)%Z -> (0 <= b_hi < 2^64)%Z ->
f128_le (a_lo + 2^64 * a_hi) (b_lo + 2^64 * b_hi) =
if f128_isnan_w a_lo a_hi then 1%Z
else if f128_isnan_w b_lo b_hi then 1%Z
else f128_le_core a_lo a_hi b_lo b_hi.
Proof.
intros. unfold f128_le. rewrite !lo64_words, !hi64_words by assumption. reflexivity.
Qed.

#[using="CODE BASE4 BASER"] Lemma b2z_snez : forall x, (0 <= x)%Z -> Z.b2z (0 <? x)%Z = nez64 x.
Proof.
intros x Hx. unfold nez64, b2z. destruct (Z.ltb_spec0 0 x); destruct (Z.eqb_spec x 0); cbn; lia.
Qed.

Definition letf2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(r : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [] m m' /\ wmono segs m m' /\ mem_inv segs m'.

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Hypothesis MI : mem_inv segs m.
Let MU : munch [] m m := munch_refl [] m.
Let WM : wmono segs m m := wmono_refl segs m.

Notation a_lo := (bv_unsigned a0). Notation a_hi := (bv_unsigned a1).
Notation b_lo := (bv_unsigned a2). Notation b_hi := (bv_unsigned a3).
Notation POST r := (letf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m).

Notation ST pc x14 x15 x16 x17 :=
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom segs)).
Notation M63 := 9223372036854775807%Z.

Lemma letf2_L98 : forall (a4 a5 a6 a7 : word) (r : Z),
r = nez64 (Z.lor (Z.lxor a_lo b_lo) (Z.lxor a_hi b_hi)) ->
evt segs (POST r) (ST (base + 0xb4) a4 a5 a6 a7).
Proof using CODE BASE4 BASER MI.
intros a4 a5 a6 a7 r HR. subst r.
do 5 zstep. rewrite b2z_snez by zrange_nonneg. finish.
Qed.

Lemma letf2_L40 : forall (a4 a7 : word) (r : Z),
r = f128_le_core a_lo a_hi b_lo b_hi ->
evt segs (POST r) (ST (base + 0x5c) a4 (Z_to_bv 64 (Z.land a_hi M63)) (Z_to_bv 64 (Z.land b_hi M63)) a7).
Proof using CODE BASE4 BASER MI.
intros a4 a7 r HR. subst r. unfold f128_le_core, ABS_HI.
zr_pose (Z.land b_hi a_hi).
do 4 zstep.
if_cases Kz; zify_cond Kz.
-
zstep. zstep. decide_tests_b.
match goal with |- context [Z_to_bv 64 (Z.lor ?x ?y)] => replace (Z.lor x y) with 0%Z by (symmetry; exact Kz) end.
finish.
- decide_tests_b. unfold f128_le_isless, f128_le_tail, is_neg64, lt_s64, SIGN64.
zstep. zstep. if_cases Kn; zify_cond Kn; decide_tests_b.
+
zstep. if_cases Ke; zify_cond Ke; decide_tests_b.
*  zstep. zstep. if_cases Kl; zify_cond Kl; decide_tests_b.
-- apply letf2_L98. reflexivity.
-- zstep. zstep. finish.
* zstep. zstep. if_cases Kl; zify_cond Kl; decide_tests_b.
-- zstep. zstep. finish.
-- zstep. apply letf2_L98. reflexivity.
+ zstep. if_cases Ke; zify_cond Ke; decide_tests_b.
* zstep. zstep. if_cases Kl; zify_cond Kl; decide_tests_b.
-- apply letf2_L98. reflexivity.
-- zstep. zstep. finish.
* zstep. zstep. if_cases Kl; zify_cond Kl; decide_tests_b.
-- zstep. zstep. finish.
-- zstep. apply letf2_L98. reflexivity.
Qed.

Lemma letf2_L1c : forall (a7 : word) (r : Z),
r = (if f128_isnan_w b_lo b_hi then 1%Z else f128_le_core a_lo a_hi b_lo b_hi) ->
evt segs (POST r) (ST (base + 0x38) (Z_to_bv 64 1) (Z_to_bv 64 (Z.land a_hi M63)) (Z_to_bv 64 M63) a7).
Proof using CODE BASE4 BASER MI.
intros a7 r HR. unfold f128_isnan_w, ABS_HI, INF_HI in HR.
do 4 zstep.
if_cases K; zify_cond K.
-
zstep. zstep. if_cases Kl; zify_cond Kl.
+  rewrite HR. decide_tests_b. zstep. zstep. finish.
+ apply letf2_L40. rewrite HR. decide_tests_b. reflexivity.
- zstep. zstep. if_cases Kl; zify_cond Kl.
+ apply letf2_L40. rewrite HR. decide_tests_b. reflexivity.
+ rewrite HR. decide_tests_b. zstep. zstep. zstep. finish.
Qed.
End Proofs.

#[using="CODE BASE4 BASER"] Lemma letf2_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte),
mem_inv segs m ->
evt segs (letf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
(f128_le (bv_unsigned a0 + 2^64 * bv_unsigned a1) (bv_unsigned a2 + 2^64 * bv_unsigned a3)) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof.
intros until m. intros MI.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl segs m) as WM.
rewrite f128_le_split by (pose proof (bv_unsigned_in_range 64 a0); pose proof (bv_unsigned_in_range 64 a1);
pose proof (bv_unsigned_in_range 64 a2); pose proof (bv_unsigned_in_range 64 a3);
unfold bv_modulus in *; lia).
remember (if f128_isnan_w (bv_unsigned a0) (bv_unsigned a1) then _ else _) as r eqn:HR.
unfold f128_isnan_w at 1, ABS_HI, INF_HI in HR.
do 6 zstep.
if_cases K; zify_cond K.
-
do 3 zstep. if_cases Kl; zify_cond Kl.
+ rewrite HR. decide_tests_b. zstep. zstep. finish.
+ apply letf2_L1c; [exact MI|]. rewrite HR. decide_tests_b. reflexivity.
- do 3 zstep. if_cases Kl; zify_cond Kl.
+ apply letf2_L1c; [exact MI|]. rewrite HR. decide_tests_b. reflexivity.
+ rewrite HR. decide_tests_b. zstep. zstep. finish.
Qed.

End G.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg Lib.GwApply Lib.SepCache Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import Q9A7.

Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core.
Local Ltac zstep ::= sg_zstep. Local Ltac mkr__zstep_1 := sg_zstep.
Local Ltac cur_mem_addr ::= g_cur_mem_addr. Local Ltac mkr__cur_mem_addr_2 := g_cur_mem_addr.

Definition memcpy_code : list Z :=
[0x0035f693; 0x10068863; 0x02060e63; 0x00158713; 0x00100793; 0x00050693; 0x0005c883; 0x00060813; 0x00158593; 0x00377293; 0x01168023; 0x00168693; 0xfff60613; 0x00028a63; 0x00170713; 0xfcf81ee3; 0x0080006f; 0x00050693; 0x0036f793; 0x0c078a63; 0x02000713; 0x02e67063; 0x01000713; 0x24e67863; 0x00867713; 0x2c071e63; 0x00467713; 0x32071463; 0x3500006f; 0x0005a703; 0x00300813; 0x11078e63; 0x00200813; 0x19079c63; 0x00875793; 0xffe60613; 0x00e68023; 0x00f680a3; 0x00268693; 0x01058593; 0x01100793; 0x0107581b; 0xff45a883; 0xff85a283; 0xffc5a303; 0x0005a703; 0x01089393; 0x0108d89b; 0x0103e833; 0x01029393; 0x0102d29b; 0x0113e8b3; 0x01031393; 0x0103531b; 0x0053e2b3; 0x01071393; 0x0063e333; 0xff060613; 0x0106a023; 0x0116a223; 0x0056a423; 0x0066a623; 0x01068693; 0x01058593; 0xfac7e2e3; 0xff258593; 0x01000713; 0xf4e66ae3; 0x19c0006f; 0x00050693; 0x00357793; 0xf2079ae3; 0x01000713; 0x02e66c63; 0x00f00713; 0x0005a783; 0x0045a803; 0x0085a883; 0x00c5a283; 0x01058593; 0xff060613; 0x00f6a023; 0x0106a223; 0x0116a423; 0x0056a623; 0x01068693; 0xfcc76ae3; 0x00800713; 0x00e66e63; 0x0005a703; 0x0045a783; 0x00e6a023; 0x00f6a223; 0x00868693; 0x00858593; 0x00467713; 0x24070063; 0x0005a703; 0x00458593; 0x00e6a023; 0x00468693; 0x22c0006f; 0x00e68023; 0x00168693; 0xfff60613; 0x01058593; 0x01200793; 0x0087581b; 0xff45a883; 0xff85a283; 0xffc5a303; 0x0005a703; 0x01889393; 0x0088d89b; 0x0103e833; 0x01829393; 0x0082d29b; 0x0113e8b3; 0x01831393; 0x0083531b; 0x0053e2b3; 0x01871393; 0x0063e333; 0xff060613; 0x0106a023; 0x0116a223; 0x0056a423; 0x0066a623; 0x01068693; 0x01058593; 0xfac7e2e3; 0xff158593; 0x01000713; 0xe4e666e3; 0x0940006f; 0x00875793; 0x01075813; 0xffd60613; 0x00e68023; 0x00f680a3; 0x01068123; 0x00368693; 0x01058593; 0x01000793; 0x0187581b; 0xff45a883; 0xff85a283; 0xffc5a303; 0x0005a703; 0x00889393; 0x0188d89b; 0x0103e833; 0x00829393; 0x0182d29b; 0x0113e8b3; 0x00831393; 0x0183531b; 0x0053e2b3; 0x00871393; 0x0063e333; 0xff060613; 0x0106a023; 0x0116a223; 0x0056a423; 0x0066a623; 0x01068693; 0x01058593; 0xfac7e2e3; 0xff358593; 0x01000713; 0xdae66ce3; 0x0005c703; 0x0015c783; 0x0025c803; 0x0035c883; 0x0045c283; 0x0055c303; 0x0065c383; 0x0075ce03; 0x00e68023; 0x00f680a3; 0x01068123; 0x011681a3; 0x0085c703; 0x0095c783; 0x00a5c803; 0x00b5c883; 0x00568223; 0x006682a3; 0x00768323; 0x01c683a3; 0x00c5c283; 0x00d5c303; 0x00e5c383; 0x00f5ce03; 0x01058593; 0x00e68423; 0x00f684a3; 0x01068523; 0x011685a3; 0x01068713; 0x00568623; 0x006686a3; 0x00768723; 0x01c687a3; 0x00070693; 0x00867713; 0xd20706e3; 0x0005c703; 0x0015c783; 0x0025c803; 0x0035c883; 0x0045c283; 0x0055c303; 0x0065c383; 0x0075ce03; 0x00858593; 0x00e68023; 0x00f680a3; 0x01068123; 0x011681a3; 0x00868713; 0x00568223; 0x006682a3; 0x00768323; 0x01c683a3; 0x00070693; 0x00467713; 0x02070863; 0x0005c703; 0x0015c783; 0x0025c803; 0x0035c883; 0x00458593; 0x00468293; 0x00e68023; 0x00f680a3; 0x01068123; 0x011681a3; 0x00028693; 0x00267713; 0x00071863; 0x00167613; 0x02061663; 0x00008067; 0x0005c703; 0x0015c783; 0x00258593; 0x00268813; 0x00e68023; 0x00f680a3; 0x00080693; 0x00167613; 0xfc060ee3; 0x0005c583; 0x00b68023; 0x00008067]%Z.

Section G.
Variables (segs : list Segment) (base : Z).
Hypothesis CODE : code_at segs base memcpy_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 1028.

Definition memcpy_entry := (base + 0x0)%Z.

Definition memcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rw_cells segs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
/\ bytes_at segs m' (bv_unsigned a1) src.

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src : list byte).
Notation S := (bv_unsigned a1).
Notation D := (bv_unsigned a0).
Notation n := (bv_unsigned a2).
Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
Hypothesis LEN : length src = Z.to_nat n.
Hypothesis AB : (0 <= S /\ S + n <= 2^64 /\ 0 <= D /\ D + n <= 2^64 /\ 0 <= n < 2^64)%Z.
Hypothesis SEP : (S + n <= D \/ D + n <= S)%Z.

Notation POST := (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m).

Notation ST pc mm x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 :=
(MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a0 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
F (Z_to_bv 64 pc) fc None mm (seg_rom segs)).

Definition INV (m1 : word -> option byte) (bs : list byte) (P : Z) : Prop :=
bytes_at segs m1 S src /\ u8arr segs m1 D bs /\ copied src bs (Z.to_nat P) /\
mem_inv segs m1 /\ munch W m m1 /\ wmono segs m m1.

Ltac open_inv H := destruct H as (SRC & DST & CP & MI & MU & WM).
Ltac inv_tac :=
lazymatch goal with
| |- INV _ _ _ => split; [eassumption | split; [eassumption | split; [ | repeat split; eassumption ]]];
lazymatch goal with CP : copied _ _ (Z.to_nat ?P) |- copied _ _ (Z.to_nat ?P') =>
first [ exact CP | replace (Z.to_nat P') with (Z.to_nat P) by lia; exact CP ] end
end.

Ltac fin :=
lazymatch goal with
| DST : u8arr _ ?m1 _ ?bs, CP : copied _ ?bs (Z.to_nat ?P) |- _ =>
let E := fresh "E" in
pose proof (copied_all _ _ _ CP ltac:(lia)) as E; rewrite E in DST; clear E CP;
apply rw_cells_of_u8arr in DST; rewrite LEN in DST
end;
finish2.

Tactic Notation "use" uconstr(L) :=
eapply L; first [ inv_tac | idtac ]; try (f_equal; lia); try lia;
try (rewrite ?unsigned_lit by lia; Z.div_mod_to_equations; lia);
try (rewrite ?Z.add_0_r, ?Z.sub_0_r; symmetry; apply Z_to_bv_bv_unsigned).

Lemma mc_a8c : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 4 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt segs POST (ST (base + 0x3c0) m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using CODE BASE4 BASER AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_2 by lia.
zstep. if_cases K2; zify_cond K2.
-
destruct (Z.ltb_spec0 (bv_unsigned r mod 4) 2) as [Hl4|Hl4]; [exfalso; cbn in K2; lia|]; apply (proj1 (Z.nlt_ge _ _)) in Hl4.
window P 2%nat HW.
ld1 HW 0%nat. ld1 HW 1%nat. zstep. zstep.
st1 HW 0%nat. st1 HW 1%nat.
zstep. zstep. rewrite land_1.
zstep. if_cases K1; zify_cond K1.
+ zstep. fin.
+ window (P + 2)%Z 1%nat HW1.
ld1 HW1 0%nat. st1 HW1 0%nat. zstep. fin.
- destruct (Z.ltb_spec0 (bv_unsigned r mod 4) 2) as [Hl4|Hl4]; [|exfalso; cbn in K2; lia].
zstep. rewrite land_1.
zstep. if_cases K1; zify_cond K1.
+ window P 1%nat HW. ld1 HW 0%nat. st1 HW 0%nat. zstep. fin.
+ zstep. fin.
Qed.

Lemma mc_a60 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + 4 + bv_unsigned r mod 4 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt segs POST (ST (base + 0x394) m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using CODE BASE4 BASER AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
window P 4%nat HW.
ld1 HW 0%nat. ld1 HW 1%nat. ld1 HW 2%nat. ld1 HW 3%nat. zstep. zstep.
st1 HW 0%nat. st1 HW 1%nat. st1 HW 2%nat. st1 HW 3%nat. zstep.
use (mc_a8c _ _ (P + 4)%Z).
Qed.

Lemma mc_a58 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 8 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt segs POST (ST (base + 0x38c) m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using CODE BASE4 BASER AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_4 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_a8c m1 bs P).
- use (mc_a60 m1 bs P).
Qed.

Lemma mc_a0c : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + 8 + bv_unsigned r mod 8 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt segs POST (ST (base + 0x340) m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using CODE BASE4 BASER AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
window P 8%nat HW.
ld1 HW 0%nat. ld1 HW 1%nat. ld1 HW 2%nat. ld1 HW 3%nat. ld1 HW 4%nat. ld1 HW 5%nat. ld1 HW 6%nat. ld1 HW 7%nat.
zstep.
st1 HW 0%nat. st1 HW 1%nat. st1 HW 2%nat. st1 HW 3%nat. zstep.
st1 HW 4%nat. st1 HW 5%nat. st1 HW 6%nat. st1 HW 7%nat. zstep.
use (mc_a58 _ _ (P + 8)%Z).
Qed.

Lemma mc_734 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 8 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt segs POST (ST (base + 0x68) m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using CODE BASE4 BASER AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_4 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_a60 m1 bs P).
- zstep. use (mc_a8c m1 bs P).
Qed.

Lemma mc_a04 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 16 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt segs POST (ST (base + 0x338) m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using CODE BASE4 BASER AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_8 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 16) 8) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_734 m1 bs P).
- use (mc_a0c m1 bs P).
Qed.

Lemma mc_72c : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 16 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt segs POST (ST (base + 0x60) m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using CODE BASE4 BASER AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_8 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 16) 8) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_a0c m1 bs P).
- use (mc_734 m1 bs P).
Qed.

Lemma mc_978 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + 16 + bv_unsigned r mod 16 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt segs POST (ST (base + 0x2ac) m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using CODE BASE4 BASER AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
window P 16%nat HW.
ld1 HW 0%nat. ld1 HW 1%nat. ld1 HW 2%nat. ld1 HW 3%nat. ld1 HW 4%nat. ld1 HW 5%nat. ld1 HW 6%nat. ld1 HW 7%nat.
st1 HW 0%nat. st1 HW 1%nat. st1 HW 2%nat. st1 HW 3%nat.
ld1 HW 8%nat. ld1 HW 9%nat. ld1 HW 10%nat. ld1 HW 11%nat.
st1 HW 4%nat. st1 HW 5%nat. st1 HW 6%nat. st1 HW 7%nat.
ld1 HW 12%nat. ld1 HW 13%nat. ld1 HW 14%nat. ld1 HW 15%nat.
zstep.
st1 HW 8%nat. st1 HW 9%nat. st1 HW 10%nat. st1 HW 11%nat.
zstep.
st1 HW 12%nat. st1 HW 13%nat. st1 HW 14%nat. st1 HW 15%nat.
zstep.
use (mc_a04 _ _ (P + 16)%Z).
Qed.

Lemma mc_848 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 8 = n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
evt segs POST (ST (base + 0x17c) m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
Proof using CODE BASE4 BASER AB LEN SEP.
intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
zstep. rewrite land_bit_4 by lia.
zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
- use (mc_a8c m1 bs P).
- window P 4%nat HW. ld4 HW 0%nat q0. zstep. st4 HW 0%nat. zstep. zstep.
use (mc_a8c _ _ (P + 4)%Z).
Qed.

Lemma mc_828 : forall m1 bs (P r : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (P + r = n)%Z -> (0 <= r < 16)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 r -> xa3 = Z_to_bv 64 (D + P) ->
evt segs POST (ST (base + 0x15c) m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using CODE BASE4 BASER AB LEN SEP.
intros m1 bs P r xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr Rr -> -> ->; open_inv I.
zstep. zstep. if_cases K8; zify_cond K8.
- use (mc_848 m1 bs P (Z_to_bv 64 r)).
- window P 8%nat HW. ld4 HW 0%nat q0. ld4 HW 4%nat q1. st4 HW 0%nat. st4 HW 4%nat. zstep. zstep.
use (mc_848 _ _ (P + 8)%Z (Z_to_bv 64 r)).
Qed.

Lemma mc_7f8 : forall (K : nat) m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
Z.to_nat (n - P) = K -> INV m1 bs P -> (0 <= P)%Z -> (16 <= n - P)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt segs POST (ST (base + 0x12c) m1 x5 x6 x7 xa1 xa2 xa3 (Z_to_bv 64 15) x15 x16 x17 x28).
Proof using CODE BASE4 BASER AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 HK I HP Hr -> -> ->; open_inv I.
window P 16%nat HW.
ld4 HW 0%nat q0. ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3.
zstep. zstep.
st4 HW 0%nat. st4 HW 4%nat. st4 HW 8%nat. st4 HW 12%nat.
zstep. zstep. if_cases Kl; zify_cond Kl.
- use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z).
- use (mc_828 _ _ (P + 16)%Z (n - (P + 16))%Z).
Qed.

Lemma mc_7ec : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P <= n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt segs POST (ST (base + 0x120) m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using CODE BASE4 BASER AB LEN SEP.
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
zstep. zstep. if_cases K16; zify_cond K16.
- use (mc_828 m1 bs P (n - P)%Z).
- zstep. use (mc_7f8 (Z.to_nat (n - P)) m1 bs P).
Qed.

Notation LW w := (sext 64 (bv_extract 0 32 (le_bytes_to_word w))).

Lemma mc_770 : forall (K : nat) m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x16 x17 x28,
Z.to_nat (n - P) = K -> INV m1 bs P -> (2 <= P)%Z -> (18 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat (P - 2)) src) ->
xa1 = Z_to_bv 64 (S + P + 14) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt segs POST (ST (base + 0xa4) m1 x5 x6 x7 xa1 xa2 xa3 (LW w) (Z_to_bv 64 17) x16 x17 x28).
Proof using CODE BASE4 BASER AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
window (P - 2)%Z 20%nat HW.
pose proof (window_sub src _ (P - 2)%Z 20 0 4 (P - 2)%Z HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
zstep.
ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3. ld4 HW 16%nat q4.
do 11 zstep. zstep.
st HW 2%nat 4%nat ltac:(by_le 16%Z). st HW 6%nat 4%nat ltac:(by_le 16%Z).
st HW 10%nat 4%nat ltac:(by_le 16%Z). st HW 14%nat 4%nat ltac:(by_le 16%Z).
zstep. zstep. zstep. if_cases Kl; zify_cond Kl.
- use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z q4). by_win HW 16%nat.
- zstep. zstep. zstep. if_cases K16; zify_cond K16.
+ use (mc_72c _ _ (P + 16)%Z).
+ zstep. use (mc_978 _ _ (P + 16)%Z).
Qed.

Lemma mc_754 : forall m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (32 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat P) src) ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt segs POST (ST (base + 0x88) m1 x5 x6 x7 xa1 xa2 xa3 (LW w) x15 x16 x17 x28).
Proof using CODE BASE4 BASER AB LEN SEP.
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 I HP Hr Hw -> -> ->; open_inv I.
window P 4%nat HW.
pose proof (window_sub src _ P 4 0 4 P HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
zstep. zstep.
st HW 0%nat 1%nat ltac:(by_le 0%Z). st HW 1%nat 1%nat ltac:(by_le 0%Z).
zstep. zstep. zstep.
use (mc_770 (Z.to_nat (n - (P + 2))) _ _ (P + 2)%Z w). by_win HW 0%nat.
Qed.

Lemma mc_878 : forall (K : nat) m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x16 x17 x28,
Z.to_nat (n - P) = K -> INV m1 bs P -> (1 <= P)%Z -> (19 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat (P - 1)) src) ->
xa1 = Z_to_bv 64 (S + P + 15) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt segs POST (ST (base + 0x1ac) m1 x5 x6 x7 xa1 xa2 xa3 (LW w) (Z_to_bv 64 18) x16 x17 x28).
Proof using CODE BASE4 BASER AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
window (P - 1)%Z 20%nat HW.
pose proof (window_sub src _ (P - 1)%Z 20 0 4 (P - 1)%Z HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
zstep.
ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3. ld4 HW 16%nat q4.
do 11 zstep. zstep.
st HW 1%nat 4%nat ltac:(by_le 24%Z). st HW 5%nat 4%nat ltac:(by_le 24%Z).
st HW 9%nat 4%nat ltac:(by_le 24%Z). st HW 13%nat 4%nat ltac:(by_le 24%Z).
zstep. zstep. zstep. if_cases Kl; zify_cond Kl.
- use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z q4). by_win HW 16%nat.
- zstep. zstep. zstep. if_cases K16; zify_cond K16.
+ use (mc_72c _ _ (P + 16)%Z).
+ zstep. use (mc_978 _ _ (P + 16)%Z).
Qed.

Lemma mc_864 : forall m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (32 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat P) src) ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt segs POST (ST (base + 0x198) m1 x5 x6 x7 xa1 xa2 xa3 (LW w) x15 x16 x17 x28).
Proof using CODE BASE4 BASER AB LEN SEP.
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 I HP Hr Hw -> -> ->; open_inv I.
window P 4%nat HW.
pose proof (window_sub src _ P 4 0 4 P HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
st HW 0%nat 1%nat ltac:(by_le 0%Z).
zstep. zstep. zstep. zstep.
use (mc_878 (Z.to_nat (n - (P + 1))) _ _ (P + 1)%Z w). by_win HW 0%nat.
Qed.

Lemma mc_90c : forall (K : nat) m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x16 x17 x28,
Z.to_nat (n - P) = K -> INV m1 bs P -> (3 <= P)%Z -> (17 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat (P - 3)) src) ->
xa1 = Z_to_bv 64 (S + P + 13) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt segs POST (ST (base + 0x240) m1 x5 x6 x7 xa1 xa2 xa3 (LW w) (Z_to_bv 64 16) x16 x17 x28).
Proof using CODE BASE4 BASER AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
window (P - 3)%Z 20%nat HW.
pose proof (window_sub src _ (P - 3)%Z 20 0 4 (P - 3)%Z HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
zstep.
ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3. ld4 HW 16%nat q4.
do 11 zstep. zstep.
st HW 3%nat 4%nat ltac:(by_le 8%Z). st HW 7%nat 4%nat ltac:(by_le 8%Z).
st HW 11%nat 4%nat ltac:(by_le 8%Z). st HW 15%nat 4%nat ltac:(by_le 8%Z).
zstep. zstep. zstep. if_cases Kl; zify_cond Kl.
- use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z q4). by_win HW 16%nat.
- zstep. zstep. zstep. if_cases K16; zify_cond K16.
+ use (mc_72c _ _ (P + 16)%Z).
+ use (mc_978 _ _ (P + 16)%Z).
Qed.

Lemma mc_8e8 : forall m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (32 <= n - P)%Z ->
w = firstn 4 (skipn (Z.to_nat P) src) ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt segs POST (ST (base + 0x21c) m1 x5 x6 x7 xa1 xa2 xa3 (LW w) x15 x16 x17 x28).
Proof using CODE BASE4 BASER AB LEN SEP.
intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 I HP Hr Hw -> -> ->; open_inv I.
window P 4%nat HW.
pose proof (window_sub src _ P 4 0 4 P HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
zstep. zstep. zstep.
st HW 0%nat 1%nat ltac:(by_le 0%Z). st HW 1%nat 1%nat ltac:(by_le 0%Z). st HW 2%nat 1%nat ltac:(by_le 0%Z).
zstep. zstep. zstep.
use (mc_90c (Z.to_nat (n - (P + 3))) _ _ (P + 3)%Z w). by_win HW 0%nat.
Qed.

Lemma mc_740 : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P)%Z -> (32 <= n - P)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt segs POST (ST (base + 0x74) m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using CODE BASE4 BASER AB LEN SEP.
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> -> ->; open_inv I.
window P 4%nat HW. ld4 HW 0%nat q0.
zstep. zstep. if_cases K3; zify_cond K3.
- use (mc_864 m1 bs P q0). by_win HW 0%nat.
- zstep. zstep. if_cases K2; zify_cond K2.
+ use (mc_8e8 m1 bs P q0). by_win HW 0%nat.
+ use (mc_754 m1 bs P q0). by_win HW 0%nat.
Qed.

Lemma mc_71c : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P <= n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt segs POST (ST (base + 0x50) m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using CODE BASE4 BASER AB LEN SEP.
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
zstep. zstep. if_cases K32; zify_cond K32.
- use (mc_740 m1 bs P).
- zstep. zstep. if_cases K16; zify_cond K16.
+ use (mc_978 m1 bs P).
+ use (mc_72c m1 bs P).
Qed.

Lemma mc_714 : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
INV m1 bs P -> (0 <= P <= n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
evt segs POST (ST (base + 0x48) m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
Proof using CODE BASE4 BASER AB LEN SEP.
intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
zstep. zstep. if_cases Kal; zify_cond Kal.
- use (mc_7ec m1 bs P).
- use (mc_71c m1 bs P).
Qed.

Lemma mc_6e4 : forall (K : nat) m1 bs (P : Z) xa1 xa2 xa3 xa4 x5 x6 x7 x16 x17 x28,
Z.to_nat (n - P) = K -> INV m1 bs P -> (0 <= P < n)%Z ->
xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
xa4 = Z_to_bv 64 (S + P + 1) ->
evt segs POST (ST (base + 0x18) m1 x5 x6 x7 xa1 xa2 xa3 xa4 (Z_to_bv 64 1) x16 x17 x28).
Proof using CODE BASE4 BASER AB LEN SEP.
induction K as [K IH] using lt_wf_ind;
intros m1 bs P xa1 xa2 xa3 xa4 x5 x6 x7 x16 x17 x28 HK I HP -> -> -> ->; open_inv I.
window P 1%nat HW.
ld1 HW 0%nat. zstep. zstep. zstep. rewrite land_3.
st1 HW 0%nat. zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
- use (mc_714 _ _ (P + 1)%Z).
- zstep. zstep. if_cases K1; zify_cond K1.
+ use (IH (Z.to_nat (n - (P + 1))) ltac:(lia) _ _ (P + 1)%Z).
+ zstep. use (mc_714 _ _ (P + 1)%Z).
Qed.

Lemma memcpy_body : forall junk,
rw_cells segs m D [CB (Z.to_nat n) junk] -> bytes_at segs m S src -> mem_inv segs m ->
evt segs POST (ST (base + 0x0) m t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3).
Proof using CODE BASE4 BASER AB LEN SEP.
intros junk DST0 SRC MI.
pose proof (munch_refl W m) as MU. pose proof (wmono_refl segs m) as WM.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DST0) as DST.
pose proof (copied_0 src junk ltac:(rewrite (rw_cells_CB_length _ _ _ _ _ DST0); lia)) as CP.
change 0%nat with (Z.to_nat 0) in CP. clear DST0.
zstep. rewrite land_3. zstep. if_cases Ksal; zify_cond Ksal.
-
zstep. zstep. rewrite land_3. zstep. if_cases Kdal; zify_cond Kdal.
+ use (mc_71c m junk 0%Z).
+ use (mc_7ec m junk 0%Z).
- zstep. if_cases K0; zify_cond K0.
+ zstep. use (mc_714 m junk 0%Z).
+ zstep. zstep. zstep. use (mc_6e4 (Z.to_nat n) m junk 0%Z).
Qed.
End Proofs.

#[using="CODE BASE4 BASER"] Lemma memcpy_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
bytes_at segs m (bv_unsigned a1) src ->
length src = Z.to_nat (bv_unsigned a2) ->
rw_cells segs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
(bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1)%Z ->
mem_inv segs m ->
evt segs (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof.
intros until junk. intros SRC LEN DST SEP MI.
eapply memcpy_body; try eassumption.
pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
pose proof (bytes_at_bound _ _ _ _ SRC) as B2.
pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R. cbn. lia.
Qed.

End G.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import Qfw3_c1.Mq0.

Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core.
Local Ltac zstep ::= sg_zstep. Local Ltac mkr__zstep_1 := sg_zstep.

Definition memset_code : list Z :=
[0x0e060a63; 0x00b50023; 0x00c506b3; 0x00300713; 0xfeb68fa3; 0x0ee66063; 0x00b500a3; 0x00b50123; 0x00700713; 0xfeb68ea3; 0xfeb68f23; 0x0ce66463; 0x00b501a3; 0x00900793; 0xfeb68e23; 0x0af66c63; 0x40a006bb; 0x03859813; 0x101015b7; 0x0036f693; 0x00459713; 0x40d60633; 0x00d505b3; 0x10070693; 0xffc67713; 0x02d83633; 0x00c5a023; 0x00e586b3; 0xfec6ae23; 0x08f76063; 0x00c5a223; 0x00c5a423; 0x01900793; 0xfec6aa23; 0xfec6ac23; 0x06f76463; 0x00c5a623; 0x00c5a823; 0x00c5aa23; 0x00c5ac23; 0x0045f793; 0x02000813; 0x01878793; 0x40f70733; 0xfec6a223; 0xfec6a423; 0xfec6a623; 0xfec6a823; 0x03076a63; 0x02061613; 0x00f585b3; 0x02065693; 0x00d66633; 0x01f00693; 0x00c5b023; 0x00c5b423; 0x00c5b823; 0x00c5bc23; 0xfe070713; 0x02058593; 0xfee6e4e3; 0x00008067]%Z.

Section G.
Variables (segs : list Segment) (base : Z).
Hypothesis CODE : code_at segs base memset_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 248.

Definition memset_entry := (base + 0x0)%Z.

Ltac with_arr tac :=
lazymatch goal with
| ARR : u8arr ?segs_ ?m ?A ?bs, FIL : filled ?cb ?bs _, LEN : length ?bs = _ |- _ => tac segs_ ARR FIL LEN A cb
end.

Ltac brute256 c Rc :=
first [ apply word_eq_of_eqb | apply Z.eqb_eq | idtac ];
repeat match goal with H : context [c] |- _ => tryif constr_eq H Rc then fail else clear H end;
revert c Rc; apply brute256_ok; vm_compute; reflexivity.

Ltac reg_val r :=
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
end.

Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

#[using="CODE BASE4 BASER"] Lemma land4_of_aligned : forall x, (0 <= x)%Z -> (x mod 4 = 0)%Z -> Z.land x 4 = (x mod 8)%Z.
Proof.
intros x Hx H4.
transitivity (Z.land (x mod 8) 4).
{ change 8%Z with (2^3)%Z. rewrite <- Z.land_ones by lia. change (Z.ones 3) with 7%Z.
rewrite <- Z.land_assoc. reflexivity. }
assert (R : (x mod 8 = 0 \/ x mod 8 = 4)%Z) by (Z.div_mod_to_equations; lia).
destruct R as [R|R]; rewrite R; reflexivity.
Qed.

Definition memset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rw_cells segs m' (bv_unsigned a0)
[CB (Z.to_nat (bv_unsigned a2)) (repeat (Z_to_bv 8 (bv_unsigned a1 mod 256)) (Z.to_nat (bv_unsigned a2)))].

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Hypothesis MI0 : mem_inv segs m.
Hypothesis AB : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= 2^64 /\ 0 <= bv_unsigned a2 < 2^64)%Z.

Notation A := (bv_unsigned a0).
Notation n := (bv_unsigned a2).
Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
Notation POST := (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m).

Notation ST pc mm x11 x12 x13 x14 x15 x16 :=
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None mm (seg_rom segs)).

Ltac fin_with cover :=
zstep;
with_arr ltac:(fun segs_ ARR FIL LEN A cb =>
let E := fresh "E" in
pose proof (filled_all _ _ _ FIL ltac:(cover)) as E;
rewrite LEN in E; rewrite E in ARR;
apply rw_cells_of_u8arr in ARR; rewrite repeat_length in ARR);
finish; subst; assumption.
Ltac fin := fin_with ltac:(intros j Hj; cbv beta; lia).
Ltac disj_lia := first [ lia | right; lia | left; disj_lia ].

Lemma memset_loop : forall (K : nat) (c p r e : Z) (m1 : word -> option byte) (bs : list byte) (Q : Z -> Prop)
(x15 x16 : word),
Z.to_nat r = K ->
c = (bv_unsigned a1 mod 256)%Z ->
u8arr segs m1 A bs -> filled (Z_to_bv 8 c) bs Q -> length bs = Z.to_nat n ->
mem_inv segs m1 -> munch W m m1 -> wmono segs m m1 ->
(forall j, (0 <= j < p \/ e <= j < n) -> Q j)%Z ->
(0 <= p)%Z -> (32 <= r)%Z -> (exists q, r = 4 * q)%Z -> (p + r <= n)%Z -> (e + 28 <= p + r)%Z ->
evt segs POST (ST (base + 0xd8) m1 (Z_to_bv 64 (A + p)) (Z_to_bv 64 (c * BC8)) (Z_to_bv 64 31) (Z_to_bv 64 r) x15 x16).
Proof using CODE BASE4 BASER AB.
induction K as [K IH] using lt_wf_ind; intros c p r e m1 bs Q x15 x16 HK Hc ARR FIL LEN MI MU WM HQ Hp Hr [q4 Hq4] Hpr He;
assert (Rc : (0 <= c < 256)%Z) by (subst c; apply Z.mod_pos_bound; lia).
mst p 8%nat ltac:(symmetry; apply le8_bcast; lia).
mst (p + 8)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
mst (p + 16)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
mst (p + 24)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
zstep. zstep. zstep.
if_cases KK; zify_cond KK.
-
replace (A + p + 32)%Z with (A + (p + 32))%Z by lia.
replace (r + -32)%Z with (r - 32)%Z by lia.
eapply (IH (Z.to_nat (r - 32)) ltac:(lia) c (p + 32)%Z (r - 32)%Z e _ _ _ x15 x16 eq_refl Hc ARR); try eassumption; try lia.
2:{ exists (q4 - 8)%Z. lia. }
intros j Hj.
destruct (Z_lt_le_dec j p) as [Hlt|Hge]. { left; left; left; left. apply HQ. lia. }
destruct (Z_lt_le_dec j (p + 32)) as [Hlt2|Hge2]. 2:{ left; left; left; left. apply HQ. lia. }
assert (D : ((p <= j < p + 8 \/ p + 8 <= j < p + 16) \/ (p + 16 <= j < p + 24 \/ p + 24 <= j < p + 32))%Z) by lia.
destruct D as [[?|?]|[?|?]]; [left; left; left; right| left; left; right| left; right| right]; lia.
- fin_with ltac:(intros j Hj; destruct (Z_lt_le_dec j p); [repeat left; apply HQ; lia|];
destruct (Z_lt_le_dec j (p + 32)); [|repeat left; apply HQ; lia]; disj_lia).
Qed.

Lemma memset_body : forall junk,
rw_cells segs m A [CB (Z.to_nat n) junk] ->
evt segs POST (ST (base + 0x0) m a1 a2 a3 a4 a5 a6).
Proof using CODE BASE4 BASER AB MI0.
intros junk DST. pose proof MI0 as MI.
pose proof (munch_refl W m) as MU. pose proof (wmono_refl segs m) as WM.
pose proof (zr_word a1) as R1. unfold inr64 in R1.
remember (bv_unsigned a1 mod 256)%Z as c eqn:Hc.
assert (Rc : (0 <= c < 256)%Z) by (subst c; apply Z.mod_pos_bound; lia).
pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as ARR.
pose proof (rw_cells_CB_length _ _ _ _ _ DST) as LEN.
pose proof (filled_init (Z_to_bv 8 c) junk) as FIL.

zstep. if_cases K0; zify_cond K0. { fin. }
assert (MF : ms_facts A n 0 1) by (unfold ms_facts; lia).
pose proof (ms_store_ok segs _ A n _ 0 1 a0 ARR LEN MF (eq_sym (Z_to_bv_plus0 a0))) as SOK.
zstep. ms_arr_store MF ltac:(rewrite Hc, le1_byte; reflexivity).
zstep. zstep. mst (n - 1)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep. if_cases K3; zify_cond K3. { fin. }
mst 1%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
mst 2%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep.
mst (n - 3)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
mst (n - 2)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep. if_cases K7; zify_cond K7. { fin. }
mst 3%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep.
mst (n - 4)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep. if_cases K9; zify_cond K9. { fin. }

zstep. zstep.
setreg 16%Z (Z_to_bv 64 (c * 2^56)) ltac:(apply Z_to_bv_eqm; rewrite Z.shiftl_mul_pow2 by lia; subst c; Z.div_mod_to_equations; lia).
zstep. zstep.
remember (Z.land (bv_swrap 32 (0 - A) mod 18446744073709551616) 3) as k eqn:Hk.
assert (Rk : (0 <= k < 4 /\ (A + k) mod 4 = 0)%Z).
{ subst k. change 3%Z with (2^2 - 1)%Z. rewrite zb_land_mask by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ (Z.of_N 32 - 1))%Z with (2^31)%Z. change (2 ^ Z.of_N 32)%Z with (2^32)%Z.
Z.div_mod_to_equations. lia. }
clear Hk.
zstep. zstep. zstep. zstep. zstep.
change 18446744073709551612%Z with (2^64 - 2^2)%Z. rewrite land_align_down by lia.
remember (n - k - (n - k) mod 2^2)%Z as n4 eqn:Hn4.
assert (Rn4 : (exists q, n4 = 4 * q)%Z /\ (n - k - 3 <= n4 <= n - k)%Z).
{ split. { exists ((n - k) / 4)%Z. subst n4. Z.div_mod_to_equations. lia. } subst n4. Z.div_mod_to_equations. lia. }
clear Hn4. destruct Rn4 as [[q4 Hq4] Rn4].
zstep. setreg 12%Z (Z_to_bv 64 (c * BC4)) ltac:(unfold BC4; brute256 c Rc).

mst k 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep. mst (k + n4 - 4)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep. if_cases K9'; zify_cond K9'. { fin. }
mst (k + 4)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + 8)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep.
mst (k + n4 - 12)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + n4 - 8)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep. if_cases K25; zify_cond K25. { fin. }
mst (k + 12)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + 16)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + 20)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + 24)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).

zstep.
remember (Z.land (A + k) 4) as k4 eqn:Hk4.
assert (Rk4 : ((k4 = 0 \/ k4 = 4) /\ (A + k + k4 + 24) mod 8 = 0)%Z).
{ subst k4. rewrite land4_of_aligned by lia. Z.div_mod_to_equations. lia. }
clear Hk4.
zstep. zstep. zstep.
mst (k + n4 - 28)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + n4 - 24)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + n4 - 20)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + n4 - 16)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep. if_cases K32; zify_cond K32. { fin. }

zstep. zstep. zstep. zstep. setreg 12%Z (Z_to_bv 64 (c * BC8)) ltac:(unfold BC4, BC8; brute256 c Rc).
zstep.
replace (A + k + (k4 + 24))%Z with (A + (k + k4 + 24))%Z by lia.
eapply (memset_loop _ c (k + k4 + 24) _ (k + n4 - 28) _ _ _ _ _ eq_refl Hc ARR); try eassumption; try lia.
exists (q4 - Z.div k4 4 - 6)%Z. lia.
Qed.
End Proofs.

#[using="CODE BASE4 BASER"] Lemma memset_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte),
rw_cells segs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
mem_inv segs m ->
evt segs (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof.
intros until junk. intros DST MI.
eapply memset_body; [exact MI | | exact DST].
pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R. cbn. lia.
Qed.

End G.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.

Import QgoP.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core.
Local Ltac zstep ::= sg_zstep. Local Ltac mkr__zstep_1 := sg_zstep.

Definition strcmp_code : list Z :=
[0x00054603; 0x0005c683; 0x02060463; 0x02d61263; 0x00158593; 0x00150513; 0x00054603; 0x0005c683; 0x00060863; 0x00158593; 0x00150513; 0xfed606e3; 0x40d60533; 0x00008067]%Z.

Section G.
Variables (segs : list Segment) (base : Z).
Hypothesis CODE : code_at segs base strcmp_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 56.

Definition strcmp_entry := (base + 0x0)%Z.

Definition strcmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 : word) (ls rs : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0' a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [] m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ a0' = Z_to_bv 64 (strcmp_model ls rs)
/\ bytes_at segs m' (bv_unsigned a0) (ls ++ [b0]) /\ bytes_at segs m' (bv_unsigned a1) (rs ++ [b0]).

Definition strcmp_stmt : Prop :=
forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (ls rs : list byte),
bytes_at segs m (bv_unsigned a0) (ls ++ [b0]) ->
bytes_at segs m (bv_unsigned a1) (rs ++ [b0]) ->
~ In b0 ls -> ~ In b0 rs ->
mem_inv segs m ->
evt segs (strcmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 ls rs m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ls rs : list byte).
Hypothesis MI : mem_inv segs m.
Hypothesis LS : bytes_at segs m (bv_unsigned a0) (ls ++ [b0]).
Hypothesis RS : bytes_at segs m (bv_unsigned a1) (rs ++ [b0]).
Hypothesis NL : ~ In b0 ls.
Hypothesis NR : ~ In b0 rs.
Let MU : munch [] m m := munch_refl [] m.
Let WM : wmono segs m m := wmono_refl segs m.

Notation A := (bv_unsigned a0).
Notation B := (bv_unsigned a1).
Notation L := (Z.of_nat (length ls)).
Notation R := (Z.of_nat (length rs)).
Notation v := (strcmp_model ls rs).
Notation POST := (strcmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 ls rs m).

Notation ST pc x10 x11 x12 x13 :=
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom segs)).

#[using="CODE BASE4 BASER m LS RS"] Lemma bounds : (0 <= A /\ A + L + 1 <= 2^64 /\ 0 <= B /\ B + R + 1 <= 2^64)%Z.
Proof.
pose proof (bytes_at_bound _ _ _ _ LS) as H1. pose proof (bytes_at_bound _ _ _ _ RS) as H2.
rewrite length_app in H1, H2. cbn [length] in H1, H2. lia.
Qed.

#[using="CODE BASE4 BASER"] Lemma full_nth : forall (s : list byte) i, ~ In b0 s -> (i <= length s)%nat ->
exists b, nth_error (s ++ [b0]) i = Some b /\ (bv_unsigned b <> 0%Z <-> (i < length s)%nat).
Proof.
intros s i Hn Hi. destruct (Nat.lt_ge_cases i (length s)) as [Hlt|Hge].
- destruct (nth_error s i) as [b|] eqn:E. 2:{ apply nth_error_None in E. lia. }
exists b. rewrite nth_error_app1 by lia. split; [exact E|]. split; [intros; lia|].
intros _. eapply notin0_nth; eauto.
- exists b0. rewrite nth_error_app2 by lia. replace (i - length s)%nat with 0%nat by lia. cbn.
split; [reflexivity|]. split; [intros H; exfalso; apply H; reflexivity | lia].
Qed.

#[using="CODE BASE4 BASER"] Lemma walk_at : forall i (a b : byte) w,
nth_error (ls ++ [b0]) i = Some a -> nth_error (rs ++ [b0]) i = Some b ->
strcmp_walk (skipn i (ls ++ [b0])) (skipn i (rs ++ [b0])) = w ->
(if ((bv_unsigned a =? 0) || negb (bv_unsigned a =? bv_unsigned b))%Z%bool
then w = (bv_unsigned a - bv_unsigned b)%Z
else strcmp_walk (skipn (S i) (ls ++ [b0])) (skipn (S i) (rs ++ [b0])) = w).
Proof.
intros i a b w Ha Hb H.
destruct (skipn i (ls ++ [b0])) as [|a' l'] eqn:EL.
{ exfalso. apply nth_error_lt in Ha. apply (f_equal (@length byte)) in EL. rewrite length_skipn in EL. cbn in EL. lia. }
destruct (skipn i (rs ++ [b0])) as [|b' r'] eqn:ER.
{ exfalso. apply nth_error_lt in Hb. apply (f_equal (@length byte)) in ER. rewrite length_skipn in ER. cbn in ER. lia. }
apply skipn_cons_nth in EL. apply skipn_cons_nth in ER. destruct EL as [Ha' ->]. destruct ER as [Hb' ->].
rewrite Ha in Ha'. injection Ha' as <-. rewrite Hb in Hb'. injection Hb' as <-.
cbn [strcmp_walk] in H.
destruct ((bv_unsigned a =? 0) || negb (bv_unsigned a =? bv_unsigned b))%Z%bool; [symmetry; exact H | exact H].
Qed.

#[using="CODE BASE4 BASER MI LS RS MU WM"] Lemma strcmp_ret : forall (a b : byte) x10 x11,
v = (bv_unsigned a - bv_unsigned b)%Z ->
evt segs POST (ST (base + 0x30) x10 x11 (Z_to_bv 64 (bv_unsigned a)) (Z_to_bv 64 (bv_unsigned b))).
Proof.
intros a b x10 x11 Hv; pose proof bounds as BD. pose proof (byte_range8 a). pose proof (byte_range8 b).
zstep. zstep. rewrite <- Hv. finish. reflexivity.
Qed.

#[using="CODE BASE4 BASER MI LS RS NL NR MU WM"] Lemma strcmp_loop : forall (k : nat) (i : Z) x12 x13,
Z.to_nat (L - i) = k -> (1 <= i <= L)%Z -> (i <= R)%Z ->
strcmp_walk (skipn (Z.to_nat i) (ls ++ [b0])) (skipn (Z.to_nat i) (rs ++ [b0])) = v ->
evt segs POST (ST (base + 0x18) (Z_to_bv 64 (A + i)) (Z_to_bv 64 (B + i)) x12 x13).
Proof.
induction k as [k IH] using lt_wf_ind; intros i x12 x13 Hk Hi HiR HW; pose proof bounds as BD.
destruct (full_nth ls (Z.to_nat i) NL ltac:(lia)) as (a & Ha & HaZ).
destruct (full_nth rs (Z.to_nat i) NR ltac:(lia)) as (b & Hb & HbZ).
pose proof (byte_range8 a). pose proof (byte_range8 b).
pose proof (walk_at _ _ _ _ Ha Hb HW) as HC.
pose proof (u8ro_read segs m A (ls ++ [b0]) i a _ LS Ha ltac:(lia) eq_refl) as RD1.
pose proof (u8ro_read segs m B (rs ++ [b0]) i b _ RS Hb ltac:(lia) eq_refl) as RD2.
zstep. zstep. zstep. if_cases Kz; zify_cond Kz.
-
rewrite Kz in HC. cbn [Z.eqb orb] in HC. apply (strcmp_ret a b). rewrite Kz. exact HC.
- zstep. zstep. zstep. if_cases Ke; zify_cond Ke.
+
rewrite (proj2 (Z.eqb_neq _ _) Kz), (proj2 (Z.eqb_eq _ _) Ke) in HC. cbn [orb negb] in HC.
assert (Hlt : (Z.to_nat i < length ls)%nat) by (apply HaZ; exact Kz).
assert (HltR : (Z.to_nat i < length rs)%nat) by (apply HbZ; lia).
replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. replace (B + i + 1)%Z with (B + (i + 1))%Z by lia.
apply (IH (Z.to_nat (L - (i + 1)))); try lia.
replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. exact HC.
+ rewrite (proj2 (Z.eqb_neq _ _) Kz), (proj2 (Z.eqb_neq _ _) Ke) in HC. cbn [orb negb] in HC.
apply (strcmp_ret a b). exact HC.
Qed.

#[using="CODE BASE4 BASER MI LS RS NL NR MU WM"] Lemma strcmp_body : evt segs POST (ST (base + 0x0) a0 a1 a2 a3).
Proof.
pose proof bounds as BD.
destruct (full_nth ls 0 NL ltac:(lia)) as (a & Ha & HaZ).
destruct (full_nth rs 0 NR ltac:(lia)) as (b & Hb & HbZ).
pose proof (byte_range8 a). pose proof (byte_range8 b).
pose proof (walk_at 0 _ _ v Ha Hb eq_refl) as HC.
pose proof (u8ro_read segs m A (ls ++ [b0]) 0 a a0 LS Ha ltac:(lia) (eq_sym (Z_to_bv_plus0 a0))) as RD1.
pose proof (u8ro_read segs m B (rs ++ [b0]) 0 b a1 RS Hb ltac:(lia) (eq_sym (Z_to_bv_plus0 a1))) as RD2.
zstep. zstep. zstep. if_cases Kz; zify_cond Kz.
- rewrite Kz in HC. cbn [Z.eqb orb] in HC. apply (strcmp_ret a b). rewrite Kz. exact HC.
- zstep. if_cases Kne; zify_cond Kne.
+ rewrite (proj2 (Z.eqb_neq _ _) Kz), (proj2 (Z.eqb_neq _ _) Kne) in HC. cbn [orb negb] in HC.
apply (strcmp_ret a b). exact HC.
+ rewrite (proj2 (Z.eqb_neq _ _) Kz), (proj2 (Z.eqb_eq _ _) Kne) in HC. cbn [orb negb] in HC.
assert (Hlt : (0 < length ls)%nat) by (apply HaZ; exact Kz).
assert (HltR : (0 < length rs)%nat) by (apply HbZ; lia).
zstep. zstep.
apply (strcmp_loop (Z.to_nat (L - 1)) 1); try lia. exact HC.
Qed.
End Proofs.

#[using="CODE BASE4 BASER"] Lemma strcmp_spec : strcmp_stmt.
Proof. unfold strcmp_stmt. intros until rs. intros LS RS NL NR MI. apply strcmp_body; assumption. Qed.

End G.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.

Import QgoP.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core.
Local Ltac zstep ::= sg_zstep. Local Ltac mkr__zstep_1 := sg_zstep.

Definition strncasecmp_code : list Z :=
[0x08060263; 0xfd010113; 0x02113423; 0x02813023; 0x00913c23; 0x01213823; 0x01313423; 0x00058413; 0x00054583; 0x06058463; 0xfff60993; 0x00150913; 0x0180006f; 0x00094583; 0xfff98993; 0x00140413; 0x00190913; 0x02058c63; 0x00044503; 0x02050863; 0x01303633; 0x02060463; 0xfca58ee3; 0x0ff5f513; 0x064000ef; 0x00044583; 0x00050493; 0x00058513; 0x054000ef; 0xfca480e3; 0xfff94583; 0x0ff5f513; 0x0100006f; 0x00000513; 0x00008067; 0x00000513; 0x034000ef; 0x00044583; 0x00050413; 0x00058513; 0x024000ef; 0x40a4053b; 0x02813083; 0x02013403; 0x01813483; 0x01013903; 0x00813983; 0x03010113; 0x00008067; 0xfbf5059b; 0x01a5b593; 0x00559593; 0x00b56533; 0x00008067]%Z.

Section G.
Variables (segs : list Segment) (base : Z).
Hypothesis CODE : code_at segs base strncasecmp_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 216.

Definition tolower_entry := (base + 0xc4)%Z.
Definition strncasecmp_entry := (base + 0x0)%Z.

#[using="CODE BASE4 BASER"] Lemma tolower_code_ok : forall c, (0 <= c < 256)%Z ->
Z.lor c ((Z.b2z (bv_swrap 32 (c + -65) mod 18446744073709551616 <? 26) ≪ 5) mod 18446744073709551616)%Z = lower8 c.
Proof.
intros c Hc. apply Z.eqb_eq.
apply (brute256_ok (fun c => Z.lor c ((Z.b2z (bv_swrap 32 (c + -65) mod 18446744073709551616 <? 26) ≪ 5) mod 18446744073709551616) =? lower8 c)%Z); [|exact Hc].
vm_compute. reflexivity.
Qed.

Definition tolower_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(c : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lower8 c)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [] m m' /\ wmono segs m m' /\ mem_inv segs m'.

Definition tolower_stmt : Prop :=
forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (c : Z),
(0 <= c < 256)%Z ->
mem_inv segs m ->
evt segs (tolower_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc c m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0xc4)) fc None m (seg_rom segs)).

#[using="CODE BASE4 BASER"] Lemma tolower_spec : tolower_stmt.
Proof.
unfold tolower_stmt. intros until c. intros CR MI.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl segs m) as WM.
do 4 zstep. rewrite tolower_code_ok by lia. zstep. finish.
Qed.

Definition strncasecmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (ls rs : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0' a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ a0' = Z_to_bv 64 (strncasecmp_model ls rs (bv_unsigned a2))
/\ stk segs m' lo (bv_unsigned sp)
/\ bytes_at segs m' (bv_unsigned a0) (ls ++ [b0]) /\ bytes_at segs m' (bv_unsigned a1) (rs ++ [b0]).

Definition strncasecmp_stmt : Prop :=
forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (ls rs : list byte) (lo : Z),
bytes_at segs m (bv_unsigned a0) (ls ++ [b0]) ->
bytes_at segs m (bv_unsigned a1) (rs ++ [b0]) ->
~ In b0 ls -> ~ In b0 rs ->
stk segs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 48)%Z ->
(bv_unsigned a0 + Z.of_nat (length ls) + 1 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
(bv_unsigned a1 + Z.of_nat (length rs) + 1 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
mem_inv segs m ->
evt segs (strncasecmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 ls rs lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).

#[using="CODE BASE4 BASER"] Lemma swrap32_small : forall z, (-2147483648 <= z < 2147483648)%Z -> bv_swrap 32 z = z.
Proof. intros z Hz. rewrite bv_swrap32_eq. rewrite Z.mod_small; lia. Qed.

Section Proofs.

Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (ls rs : list byte) (lo : Z) (junk8 : list byte).
Hypothesis MI : mem_inv segs m.
Hypothesis LS : bytes_at segs m (bv_unsigned a0) (ls ++ [b0]).
Hypothesis RS : bytes_at segs m (bv_unsigned a1) (rs ++ [b0]).
Hypothesis NL : ~ In b0 ls.
Hypothesis NR : ~ In b0 rs.
Hypothesis FR : rw_cells segs m (bv_unsigned sp + -48) [CB 8 junk8; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Hypothesis STK : stk segs m lo (bv_unsigned sp + -48).
Hypothesis LO : (lo <= bv_unsigned sp - 48)%Z.
Hypothesis MU : munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m0 m.
Hypothesis WM : wmono segs m0 m.
Hypothesis N0 : bv_unsigned a2 <> 0%Z.

Notation A := (bv_unsigned a0).
Notation B := (bv_unsigned a1).
Notation n := (bv_unsigned a2).
Notation L := (Z.of_nat (length ls)).
Notation R := (Z.of_nat (length rs)).
Notation v := (strncasecmp_model ls rs (bv_unsigned a2)).
Notation POST := (strncasecmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 ls rs lo m0).
Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -48)).

Notation ST pc x1 x8 x9 x10 x11 x12 x18 x19 :=
(MS (mkR x1 SP' gp tp t0 t1 t2 x8 x9 x10 x11 x12 a3 a4 a5 a6 a7 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom segs)).

#[using="CODE BASE4 BASER ra s0 s1 s2 s3 m junk8 LS RS FR N0"] Lemma bounds : (0 <= A /\ A + L + 1 <= 2^64 /\ 0 <= B /\ B + R + 1 <= 2^64 /\ 48 <= bv_unsigned sp <= 2^64 /\ 0 < n < 2^64)%Z.
Proof.
pose proof (bytes_at_bound _ _ _ _ LS) as H1. pose proof (bytes_at_bound _ _ _ _ RS) as H2.
rewrite length_app in H1, H2. cbn [length] in H1, H2.
pose proof (rw_cells_bound _ _ _ _ FR) as H3. cbn in H3.
pose proof (bv_unsigned_in_range 64 sp) as R1. pose proof (bv_unsigned_in_range 64 a2) as R2.
unfold bv_modulus in R1, R2. cbn in R1, R2. lia.
Qed.

#[using="CODE BASE4 BASER"] Lemma full_nth : forall (s : list byte) i, ~ In b0 s -> (i <= length s)%nat ->
exists b, nth_error (s ++ [b0]) i = Some b /\ (bv_unsigned b <> 0%Z <-> (i < length s)%nat).
Proof.
intros s i Hn Hi. destruct (Nat.lt_ge_cases i (length s)) as [Hlt|Hge].
- destruct (nth_error s i) as [b|] eqn:E. 2:{ apply nth_error_None in E. lia. }
exists b. rewrite nth_error_app1 by lia. split; [exact E|]. split; [intros; lia|].
intros _. eapply notin0_nth; eauto.
- exists b0. rewrite nth_error_app2 by lia. replace (i - length s)%nat with 0%nat by lia. cbn.
split; [reflexivity|]. split; [intros H; exfalso; apply H; reflexivity | lia].
Qed.

Definition stop (a b : byte) (k : nat) : bool :=
((bv_unsigned a =? 0) || (bv_unsigned b =? 0) || Nat.eqb k 0
|| negb ((bv_unsigned a =? bv_unsigned b) || (lower8 (bv_unsigned a) =? lower8 (bv_unsigned b))))%Z%bool.

#[using="CODE BASE4 BASER"] Lemma walk_at : forall i (a b : byte) k w,
nth_error (ls ++ [b0]) i = Some a -> nth_error (rs ++ [b0]) i = Some b ->
strncasecmp_walk (skipn i (ls ++ [b0])) (skipn i (rs ++ [b0])) k = w ->
if stop a b k then w = (lower8 (bv_unsigned a) - lower8 (bv_unsigned b))%Z
else exists k', k = S k' /\ strncasecmp_walk (skipn (S i) (ls ++ [b0])) (skipn (S i) (rs ++ [b0])) k' = w.
Proof.
intros i a b k w Ha Hb H.
destruct (skipn i (ls ++ [b0])) as [|a' l'] eqn:EL.
{ exfalso. apply nth_error_lt in Ha. apply (f_equal (@length byte)) in EL. rewrite length_skipn in EL. cbn in EL. lia. }
destruct (skipn i (rs ++ [b0])) as [|b' r'] eqn:ER.
{ exfalso. apply nth_error_lt in Hb. apply (f_equal (@length byte)) in ER. rewrite length_skipn in ER. cbn in ER. lia. }
apply skipn_cons_nth in EL. apply skipn_cons_nth in ER. destruct EL as [Ha' ->]. destruct ER as [Hb' ->].
rewrite Ha in Ha'. injection Ha' as <-. rewrite Hb in Hb'. injection Hb' as <-.
cbn [strncasecmp_walk] in H. unfold stop.
destruct ((bv_unsigned a =? 0) || (bv_unsigned b =? 0) || Nat.eqb k 0
|| negb ((bv_unsigned a =? bv_unsigned b) || (lower8 (bv_unsigned a) =? lower8 (bv_unsigned b))))%Z%bool eqn:E.
- symmetry; exact H.
- destruct k as [|k']. { cbn [Nat.eqb] in E. rewrite orb_true_r in E. cbn in E. discriminate. }
exists k'. split; [reflexivity| exact H].
Qed.

#[using="CODE BASE4 BASER junk8 MI LS RS FR STK LO MU WM N0"] Lemma ret_seq : forall (i : Z) (a b : byte) x1 x9 x11 x12 x18 x19,
(0 <= i)%Z -> nth_error (rs ++ [b0]) (Z.to_nat i) = Some b ->
v = (lower8 (bv_unsigned a) - lower8 (bv_unsigned b))%Z ->
evt segs POST (ST (base + 0x90) x1 (Z_to_bv 64 (B + i)) x9 (Z_to_bv 64 (bv_unsigned a)) x11 x12 x18 x19).
Proof.
intros i a b x1 x9 x11 x12 x18 x19 Hi Hb Hv; pose proof bounds as BD. pose proof (nth_error_lt _ _ _ Hb) as BL.
rewrite length_app in BL; cbn [length] in BL.
pose proof (byte_range8 a) as Ra. pose proof (byte_range8 b) as Rb.
pose proof (lower8_range _ Ra) as La. pose proof (lower8_range _ Rb) as Lb.

zstep. do 4 zstep. rewrite tolower_code_ok by lia. zstep.
pose proof (u8ro_read segs m B (rs ++ [b0]) i b _ RS Hb ltac:(lia) eq_refl) as RD.
zstep. zstep. zstep. zstep. do 4 zstep. rewrite tolower_code_ok by lia. zstep.
zstep. erewrite (swrap32_small (lower8 (bv_unsigned a) - lower8 (bv_unsigned b))%Z).
2:{ unfold lower8; destruct (_ && _)%bool; destruct (_ && _)%bool; lia. }
do 7 zstep.
pose proof FR as FR'. release_frame FR' STK (bv_unsigned sp).
rewrite <- Hv. finish. reflexivity.
Qed.

#[using="CODE BASE4 BASER"] Lemma land255 : forall x, (0 <= x < 256)%Z -> Z.land x 255 = x.
Proof. intros x Hx. change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

#[using="CODE BASE4 BASER junk8 MI LS RS FR STK LO MU WM N0"] Lemma exit_seq : forall (i : Z) (a b : byte) x1 x9 x10 x12 x18 x19,
(0 <= i)%Z -> nth_error (rs ++ [b0]) (Z.to_nat i) = Some b ->
v = (lower8 (bv_unsigned a) - lower8 (bv_unsigned b))%Z ->
evt segs POST (ST (base + 0x7c) x1 (Z_to_bv 64 (B + i)) x9 x10 (Z_to_bv 64 (bv_unsigned a)) x12 x18 x19).
Proof.
intros i a b x1 x9 x10 x12 x18 x19 Hi Hb Hv; pose proof bounds as BD. pose proof (byte_range8 a) as Ra.
zstep. rewrite land255 by lia. zstep. eapply ret_seq; eauto.
Qed.

#[using="CODE BASE4 BASER junk8 MI LS RS NL NR FR STK LO MU WM N0"] Lemma check_loop : forall (k : nat) (i : Z) (a : byte) x1 x9 x10 x12,
Z.to_nat (L - i) = k -> (0 <= i)%Z -> (i <= R)%Z -> (i <= n - 1)%Z ->
nth_error (ls ++ [b0]) (Z.to_nat i) = Some a -> bv_unsigned a <> 0%Z ->
strncasecmp_walk (skipn (Z.to_nat i) (ls ++ [b0])) (skipn (Z.to_nat i) (rs ++ [b0])) (Z.to_nat (n - 1 - i)) = v ->
evt segs POST (ST (base + 0x48) x1 (Z_to_bv 64 (B + i)) x9 x10 (Z_to_bv 64 (bv_unsigned a)) x12 (Z_to_bv 64 (A + i + 1)) (Z_to_bv 64 (n - 1 - i))).
Proof.
induction k as [k IH] using lt_wf_ind; intros i a x1 x9 x10 x12 Hk Hi HiR Hin Ha Haz HW; pose proof bounds as BD.
pose proof (nth_error_lt _ _ _ Ha) as HaL. rewrite length_app in HaL; cbn [length] in HaL.
assert (HiL : (Z.to_nat i < length ls)%nat).
{ destruct (Nat.lt_ge_cases (Z.to_nat i) (length ls)) as [|Hge]; [assumption|]. exfalso. apply Haz.
rewrite nth_error_app2 in Ha by lia. replace (Z.to_nat i - length ls)%nat with 0%nat in Ha by lia. cbn in Ha.
injection Ha as <-. reflexivity. }
destruct (full_nth rs (Z.to_nat i) NR ltac:(lia)) as (b & Hb & HbZ).
pose proof (byte_range8 a) as Ra. pose proof (byte_range8 b) as Rb.
pose proof (lower8_range _ Ra) as La. pose proof (lower8_range _ Rb) as Lb.
pose proof (walk_at _ _ _ _ _ Ha Hb HW) as HC. unfold stop in HC.
rewrite (proj2 (Z.eqb_neq _ _) Haz) in HC. cbn [orb] in HC.

assert (LT : forall y1 y9 y10 y11 y12 k', (Z.to_nat (n - 1 - i)) = S k' -> bv_unsigned b <> 0%Z ->
strncasecmp_walk (skipn (S (Z.to_nat i)) (ls ++ [b0])) (skipn (S (Z.to_nat i)) (rs ++ [b0])) k' = v ->
evt segs POST (ST (base + 0x34) y1 (Z_to_bv 64 (B + i)) y9 y10 y11 y12 (Z_to_bv 64 (A + i + 1)) (Z_to_bv 64 (n - 1 - i)))).
{ intros y1 y9 y10 y11 y12 k' Hk' Hbz HW'.
assert (HiR' : (Z.to_nat i < length rs)%nat) by (apply HbZ; exact Hbz).
destruct (full_nth ls (S (Z.to_nat i)) NL ltac:(lia)) as (a' & Ha' & Ha'Z).
pose proof (byte_range8 a') as Ra'.
pose proof (u8ro_read segs m A (ls ++ [b0]) (i + 1) a' _ LS ltac:(replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia; exact Ha') ltac:(lia) eq_refl) as RD.
zstep. zstep. zstep. zstep. zstep. if_cases Kz; zify_cond Kz.
-
destruct (full_nth rs (S (Z.to_nat i)) NR ltac:(lia)) as (b' & Hb' & _).
pose proof (walk_at (S (Z.to_nat i)) a' b' k' v Ha' Hb' HW') as HC'. unfold stop in HC'.
rewrite Kz in HC'. cbn [Z.eqb orb] in HC'.
replace (B + i + 1)%Z with (B + (i + 1))%Z by lia.
eapply (exit_seq (i + 1) a' b'); [lia | replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia; exact Hb' | rewrite Kz; exact HC'].
- replace (B + i + 1)%Z with (B + (i + 1))%Z by lia. replace (A + i + 2)%Z with (A + (i + 1) + 1)%Z by lia.
replace (n - 1 - i + -1)%Z with (n - 1 - (i + 1))%Z by lia.
unshelve (eapply (IH (Z.to_nat (L - (i + 1))) _ (i + 1)%Z a')); try lia.
+ replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. exact Ha'.
+ replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. replace (Z.to_nat (n - 1 - (i + 1))) with k' by lia. exact HW'. }
pose proof (u8ro_read segs m B (rs ++ [b0]) i b _ RS Hb ltac:(lia) eq_refl) as RD.
zstep. zstep. if_cases Kbz; zify_cond Kbz.
{  rewrite Kbz in HC. cbn [Z.eqb orb] in HC. eapply (exit_seq i a b); [lia | exact Hb | rewrite Kbz; exact HC]. }
rewrite (proj2 (Z.eqb_neq _ _) Kbz) in HC. cbn [orb] in HC.
zstep. zstep. if_cases Kk; zify_cond Kk.
{  replace (Z.to_nat (n - 1 - i)) with 0%nat in HC by lia. cbn [Nat.eqb orb] in HC.
eapply (exit_seq i a b); [lia | exact Hb | exact HC]. }
destruct (Z.to_nat (n - 1 - i)) as [|k'] eqn:Ek; [exfalso; lia|]. cbn [Nat.eqb orb] in HC.
zstep. if_cases Keq; zify_cond Keq.
{  rewrite (proj2 (Z.eqb_eq _ _) Keq) in HC. cbn [orb negb] in HC.
destruct HC as (k'' & Ek' & HW'). injection Ek' as <-. eapply LT; [reflexivity | exact Kbz | exact HW']. }
rewrite (proj2 (Z.eqb_neq _ _) Keq) in HC. cbn [orb] in HC.

zstep. rewrite land255 by lia. zstep. do 4 zstep. rewrite tolower_code_ok by lia. zstep.

pose proof (u8ro_read segs m B (rs ++ [b0]) i b _ RS Hb ltac:(lia) eq_refl) as RD2.
zstep. zstep. zstep. zstep. do 4 zstep. rewrite tolower_code_ok by lia. zstep.
zstep. if_cases Kleq; zify_cond Kleq.
{ rewrite (proj2 (Z.eqb_eq _ _) Kleq) in HC. cbn [orb negb] in HC.
destruct HC as (k'' & Ek' & HW'). injection Ek' as <-. eapply LT; [reflexivity | exact Kbz | exact HW']. }
rewrite (proj2 (Z.eqb_neq _ _) Kleq) in HC. cbn [orb negb] in HC.

pose proof (u8ro_read segs m A (ls ++ [b0]) i a (Z_to_bv 64 (A + i + 1 + -1)) LS Ha ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD3.
zstep. eapply (exit_seq i a b); [lia | exact Hb | exact HC].
Qed.
End Proofs.

#[using="CODE BASE4 BASER"] Lemma strncasecmp_spec : strncasecmp_stmt.
Proof.
unfold strncasecmp_stmt. intros until lo. intros LS RS NL NR ST LO SEPA SEPB MI.
pose proof (bytes_at_bound _ _ _ _ LS) as H1. pose proof (bytes_at_bound _ _ _ _ RS) as H2.
rewrite length_app in H1, H2. cbn [length] in H1, H2.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof (bv_unsigned_in_range 64 a2) as NR2. unfold bv_modulus in NR2. cbn in NR2.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl segs m) as WM.
zstep. if_cases K0; zify_cond K0.
- zstep. zstep. finish. unfold strncasecmp_model. rewrite K0. reflexivity.
- carve_frame 48%nat ST. do 7 zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
destruct (nth_error (ls ++ [b0]) 0) as [a|] eqn:Ha. 2:{ exfalso. apply nth_error_None in Ha. rewrite length_app in Ha. cbn in Ha. lia. }
destruct (nth_error (rs ++ [b0]) 0) as [b|] eqn:Hb. 2:{ exfalso. apply nth_error_None in Hb. rewrite length_app in Hb. cbn in Hb. lia. }
pose proof (byte_range8 a) as Ra. pose proof (byte_range8 b) as Rb.
pose proof (u8ro_read segs m1 (bv_unsigned a0) (ls ++ [b0]) 0 a a0 LS Ha ltac:(lia) (eq_sym (Z_to_bv_plus0 a0))) as RD.
assert (HW : strncasecmp_walk (skipn (Z.to_nat 0) (ls ++ [b0])) (skipn (Z.to_nat 0) (rs ++ [b0])) (Z.to_nat (bv_unsigned a2 - 1 - 0))
= strncasecmp_model ls rs (bv_unsigned a2)).
{ unfold strncasecmp_model. rewrite (proj2 (Z.eqb_neq _ _) K0). cbn [Z.to_nat skipn]. f_equal. lia. }
zstep. zstep. if_cases Ka; zify_cond Ka.
+
zstep.
pose proof (walk_at ls rs 0 a b _ _ Ha Hb HW) as HC. unfold stop in HC. rewrite Ka in HC. cbn [Z.eqb orb] in HC.
rewrite <- Ka in HC.
eapply evt_eq.
2:{ eapply ret_seq with (i := 0%Z) (a := a) (b := b) (m0 := m);
lazymatch goal with
| |- mem_inv _ _ => exact MI
| |- bytes_at _ _ (bv_unsigned a0) _ => exact LS
| |- bytes_at _ _ (bv_unsigned a1) _ => exact RS
| |- rw_cells _ _ _ _ => exact FR
| |- stk _ _ _ _ => exact ST
| |- munch _ _ _ => exact MU
| |- wmono _ _ _ => exact WM
| |- nth_error _ _ = Some _ => exact Hb
| |- _ = _ => first [exact HC | symmetry; exact HC]
| |- _ => try lia
end. }
unfold mkR. rewrite Ka, Z.add_0_r, Z_to_bv_lit_self. reflexivity.
+ zstep. zstep. zstep.
eapply evt_eq.
2:{ eapply check_loop with (i := 0%Z) (a := a) (m0 := m);
lazymatch goal with
| |- mem_inv _ _ => exact MI
| |- bytes_at _ _ (bv_unsigned a0) _ => exact LS
| |- bytes_at _ _ (bv_unsigned a1) _ => exact RS
| |- ~ In _ ls => exact NL
| |- ~ In _ rs => exact NR
| |- rw_cells _ _ _ _ => exact FR
| |- stk _ _ _ _ => exact ST
| |- munch _ _ _ => exact MU
| |- wmono _ _ _ => exact WM
| |- nth_error _ _ = Some _ => exact Ha
| |- strncasecmp_walk _ _ _ = _ => exact HW
| |- Z.to_nat _ = _ => reflexivity
| |- _ => try lia
end. }
unfold mkR. rewrite !Z.add_0_r, Z.sub_0_r, Z_to_bv_lit_self. reflexivity.
Qed.

End G.
End Mq6.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.

Import ListNotations. Unset Keyed Unification.
Local Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepGen GwCallee.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core.
Local Ltac zstep ::= sg_zstep. Local Ltac mkr__zstep_1 := sg_zstep.

Definition divtf3_code : list Z :=
[0xf9010113; 0x06113423; 0x06813023; 0x04913c23; 0x05213823; 0x05313423; 0x05413023; 0x03513c23; 0x03613823; 0x03713423; 0x03813023; 0x01913c23; 0x01a13823; 0x01b13423; 0x00058713; 0xfff00793; 0x00159593; 0x00169893; 0x00e6c2b3; 0xffff8eb7; 0x0107d813; 0x0315d313; 0x0318d393; 0x03f2d593; 0x001e8e1b; 0x03f59593; 0x010778b3; 0x01c30f33; 0x002e8e9b; 0x0106f2b3; 0x35df6a63; 0x01c38eb3; 0x35de7663; 0x00000e13; 0x000046b7; 0x00100e93; 0x407303b3; 0x00f61f13; 0x03165413; 0x7504ffb7; 0xffffd4b7; 0x03f55313; 0x00151713; 0x00189913; 0xfff00a13; 0xffe68a9b; 0x030e9693; 0x333f8b13; 0x9994899b; 0x012364b3; 0x02075f93; 0x020a5913; 0x00d8e8b3; 0x00d2e6b3; 0x015e02b3; 0x020b1b13; 0x02049493; 0xfff90e13; 0x007282b3; 0x00f69a13; 0x00189393; 0x0204d913; 0x01c77e33; 0x01446a33; 0x0203d413; 0x414b0ab3; 0x035a3b33; 0x41600b33; 0x035b0bb3; 0x035b3ab3; 0x001a9a93; 0x03fbdb13; 0x015b6ab3; 0x034abb33; 0x41600b33; 0x036a8bb3; 0x036abab3; 0x001a9a93; 0x03fbdb13; 0x015b6ab3; 0x034abb33; 0x41600b33; 0x036a8bb3; 0x036abab3; 0x001a9a93; 0x03fbdb13; 0x015b6ab3; 0x034abb33; 0x41600b33; 0x036a8bb3; 0x036abab3; 0x001a9a93; 0x03fbdb13; 0x015b6ab3; 0xfffa8a93; 0x035a3b33; 0x035a0a33; 0x035f3f33; 0x01ea0f33; 0x014f3a33; 0x002f3b93; 0x41ee8eb3; 0x014b0a33; 0x001bcf13; 0x035e8b33; 0x035ebeb3; 0x01ea0f33; 0x001e9a13; 0x03fb5b13; 0x03fede93; 0x41e00f33; 0x014b6a33; 0x03ea8b33; 0x03eabf33; 0x03fb5a93; 0x001f1f13; 0x001b1b13; 0x015f6f33; 0x014b0a33; 0x01df0eb3; 0x016a3f33; 0x013a09b3; 0x01ee8eb3; 0x0149bf33; 0x0209da13; 0x02099993; 0x01ee8ab3; 0x028a0eb3; 0x032a0f33; 0x03fa0bb3; 0x03ca0c33; 0x0209da13; 0x0299b9b3; 0xfffa8c93; 0x028a0b33; 0x03fa0d33; 0x03ca0db3; 0x01798ab3; 0x020cdb93; 0x020c9c93; 0x01ac0d33; 0x013ab9b3; 0x028b8a33; 0x03790933; 0x037f80b3; 0x037e0bb3; 0x020cd793; 0x029cb4b3; 0x018d3c33; 0x020d5c93; 0x020d1d13; 0x02878433; 0x03f78fb3; 0x03c787b3; 0x017b0bb3; 0x020c1c13; 0x01bd0db3; 0x001e80b3; 0x00fa87b3; 0x016bbe33; 0x01eb8f33; 0x01240933; 0x01adbb33; 0x018cec33; 0x01d0beb3; 0x009084b3; 0x0157bab3; 0x017f3bb3; 0x01ff0fb3; 0x00893433; 0x01878c33; 0xfffb4b13; 0x02095c93; 0x02091913; 0x0014bd33; 0x014e8eb3; 0x015989b3; 0x017e0e33; 0x01efbf33; 0x00fc37b3; 0x020fda13; 0x020f9f93; 0x02041413; 0x01ae8eb3; 0x01248933; 0x01ee0e33; 0x01fc0fb3; 0x01946f33; 0x00993433; 0x013909b3; 0x020e1e13; 0x018fb4b3; 0x01fb3ab3; 0x016fcfb3; 0x01ee8eb3; 0x0129bf33; 0x009787b3; 0x001fbf93; 0x01ca6e33; 0x008e8eb3; 0xffff8f93; 0x01ee8eb3; 0x01c98e33; 0x015fff33; 0x013e3fb3; 0x00fe07b3; 0x01fe8eb3; 0x01c7be33; 0x01e78f33; 0x01ce8e33; 0x00ff37b3; 0x00fe0e33; 0x031e5793; 0x00128e93; 0x0c079c63; 0x030e5793; 0x001f5893; 0x0017bf93; 0x01fe1e33; 0x03ffc413; 0x0088d8b3; 0x011e6e33; 0x01ff1f33; 0x00078463; 0x000e8293; 0x0063e8b3; 0x03151513; 0x02df07b3; 0x02cf3333; 0x02ce03b3; 0x00f307b3; 0x02cf0333; 0x40f50533; 0x006037b3; 0x40600333; 0x40750533; 0x40f503b3; 0xfff28e93; 0x00008537; 0xfff5051b; 0xfff00793; 0x0aaede63; 0x0cc0006f; 0x0017de93; 0x07ffff37; 0x01d77e33; 0x024f1f13; 0x0fee0c63; 0x01ee3f33; 0x0e0f0c63; 0x01d6f733; 0x07fffeb7; 0x024e9e93; 0x0fd70c63; 0x01d73eb3; 0x0e0e8c63; 0x07fff6b7; 0x02469693; 0x00de4eb3; 0x01d56eb3; 0x120e9263; 0x00d746b3; 0x00d66633; 0x06061263; 0x00000513; 0x0ffff5b7; 0x02359593; 0x34c0006f; 0x001f5713; 0x03fe1793; 0x001e5e13; 0x03051293; 0x00f76f33; 0x02ce0733; 0x02df07b3; 0x02cf3333; 0x40e28733; 0x02cf02b3; 0x00f307b3; 0x00503333; 0x40f70733; 0x406703b3; 0x40500333; 0x00050713; 0x00008537; 0xfff5051b; 0xfff00793; 0x00aecc63; 0x00000513; 0x07fff637; 0x02461613; 0x00c5e5b3; 0x2e80006f; 0x07d05a63; 0x00ff7533; 0x010e7733; 0x030e9793; 0x03f35813; 0x00139393; 0x00e7e7b3; 0x0103e833; 0x00131713; 0x00157893; 0x00e88733; 0x011738b3; 0x01180833; 0x20d80a63; 0x0106b8b3; 0x2100006f; 0x00153f13; 0xf00f18e3; 0x00100593; 0x02f59593; 0x00b765b3; 0x2900006f; 0x00163e93; 0xf00e98e3; 0x00100513; 0x02f51513; 0x00a6e5b3; 0x00060513; 0x2740006f; 0xf8f00513; 0x03d55a63; 0x00100513; 0x41d507bb; 0x02079513; 0x02055513; 0xfc050293; 0x070e8813; 0x1002c863; 0x00ae5533; 0x11c0006f; 0x00d746b3; 0x00d666b3; 0x00069663; 0x00000513; 0x2340006f; 0x01c566b3; 0x26068463; 0x00e666b3; 0xf20686e3; 0x030e5693; 0x26069663; 0x0018b693; 0x00050e13; 0x00088463; 0x00088e13; 0x001e5e93; 0x55555f37; 0x33333fb7; 0x0f0f1437; 0x01de6e33; 0x555f0e9b; 0x333f8f1b; 0xf0f40f9b; 0x002e5413; 0x008e6e33; 0x020e9413; 0x008e8eb3; 0x020f1413; 0x008f0f33; 0x020f9413; 0x008f8fb3; 0x004e5413; 0x008e6e33; 0x008e5413; 0x008e6e33; 0x010e5413; 0x008e6e33; 0x020e5413; 0x008e6e33; 0xfffe4e13; 0x001e5413; 0x01d47eb3; 0x00669693; 0x41de0e33; 0x01ee7eb3; 0x002e5e13; 0x01ee7e33; 0x01010f37; 0x101f0f1b; 0x01ce8e33; 0x004e5e93; 0x01de0e33; 0x020f1e93; 0x01fe7e33; 0x01df0eb3; 0x03de0e33; 0x038e5e13; 0x00de66b3; 0xff168e13; 0x020e1e93; 0x020edf13; 0xfc0f0e93; 0x1a0ec263; 0x01e518b3; 0x1b00006f; 0x00ff5333; 0xfff54513; 0x001e1393; 0x00a39533; 0x00a36533; 0x00fe57b3; 0x43f2d393; 0x02081293; 0x0202d313; 0xfc030293; 0x00f3f7b3; 0x0002c663; 0x006718b3; 0x0180006f; 0x010898b3; 0x00175393; 0xfff34313; 0x0063d333; 0x0068e8b3; 0x01071733; 0x43f2d813; 0x02f602b3; 0x02a63333; 0x02a683b3; 0x00e87733; 0x02a60833; 0x00730333; 0x00181393; 0x005302b3; 0x00773333; 0x406888b3; 0x03f85813; 0x00129293; 0x0102e833; 0x41088833; 0x40770733; 0x00157893; 0x00e88733; 0x011738b3; 0x01180833; 0xded81ae3; 0x00e638b3; 0x011508b3; 0x07fff2b7; 0x00300313; 0x00169393; 0x00a8be33; 0x02429513; 0x026632b3; 0x01c787b3; 0x00d282b3; 0x00728333; 0x00a7b2b3; 0x00680663; 0x01033333; 0x0100006f; 0x00161313; 0x00c30333; 0x00e33333; 0x0062f2b3; 0x00500313; 0x02663333; 0x00d30333; 0x00269393; 0x005886b3; 0x0116b8b3; 0x011787b3; 0x007308b3; 0x00a7b533; 0x01180663; 0x0108b633; 0x0100006f; 0x00261813; 0x00c80633; 0x00e63633; 0x00c57533; 0x00a68533; 0x00d53633; 0x00c78633; 0x00b665b3; 0x06813083; 0x06013403; 0x05813483; 0x05013903; 0x04813983; 0x04013a03; 0x03813a83; 0x03013b03; 0x02813b83; 0x02013c03; 0x01813c83; 0x01013d03; 0x00813d83; 0x07010113; 0x00008067; 0x00e66633; 0xd80614e3; 0x0ffff5b7; 0x02359593; 0xd7dff06f; 0x00000e13; 0x02c0006f; 0x01c898b3; 0xffff4f13; 0x00155f93; 0x01efdf33; 0x01e8e8b3; 0x01c51533; 0x43fede13; 0x01000e93; 0x00ae7533; 0x40de8e33; 0x03075713; 0x880716e3; 0x0012b693; 0x00060713; 0x00028463; 0x00028713; 0x00175e93; 0x55555f37; 0x33333fb7; 0x0f0f1437; 0x01d76733; 0x555f0e9b; 0x333f8f1b; 0xf0f40f9b; 0x00275413; 0x00876733; 0x020e9413; 0x008e8eb3; 0x020f1413; 0x008f0f33; 0x020f9413; 0x008f8fb3; 0x00475413; 0x00876733; 0x00875413; 0x00876733; 0x01075413; 0x00876733; 0x02075413; 0x00876733; 0xfff74713; 0x00175413; 0x01d47eb3; 0x00669693; 0x41d70733; 0x01e77eb3; 0x00275713; 0x01e77733; 0x01010f37; 0x101f0f1b; 0x00ee8733; 0x00475e93; 0x01d70733; 0x020f1e93; 0x01f77733; 0x01df0eb3; 0x03d70733; 0x03875713; 0x00d766b3; 0xff168713; 0x02071e93; 0x020edf13; 0xfc0f0e93; 0x000ec663; 0x01e612b3; 0x0180006f; 0x00e292b3; 0xffff4f13; 0x00165f93; 0x01efdf33; 0x01e2e2b3; 0x00e61633; 0x43fed713; 0x01c686b3; 0x00c77633; 0xff068e13; 0xf88ff06f]%Z.

Section G.
Variables (segs : list Segment) (base : Z).
Hypothesis CODE : code_at segs base divtf3_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 2308.

Definition divtf3_entry := (base + 0x0)%Z.

Definition divtf3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' (bv_unsigned sp - 112) (bv_unsigned sp).

Definition divtf3_stmt : Prop :=
forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte),
stk segs m (bv_unsigned sp - 112) (bv_unsigned sp) ->
mem_inv segs m ->
(4096 <= bv_unsigned sp)%Z ->
evt segs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
(f128_div (mk128 (bv_unsigned a1) (bv_unsigned a0)) (mk128 (bv_unsigned a3) (bv_unsigned a2))) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).

End G.
