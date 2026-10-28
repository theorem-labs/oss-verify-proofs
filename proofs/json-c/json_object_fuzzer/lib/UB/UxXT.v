(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP.
Import ListNotations.
Open Scope Z_scope.

Definition reserve_entry : Z := 0x468f4.
Definition pushb_entry : Z := 0x46960.

Lemma le1_w : forall v : word, le1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. intros v. unfold le1, word_to_le_bytes. cbn. reflexivity. Qed.

Lemma land1_even : forall n, Z.land (2 * n) 1 = 0.
Proof. intros n. rewrite Z.land_comm. change 1 with (Z.ones 1). rewrite Z.land_comm, Z.land_ones by lia. change (2 ^ 1) with 2. rewrite Z.mul_comm, Z.mod_mul; lia. Qed.

Lemma shiftr1_double : forall n, 0 <= n -> Z.shiftr (2 * n) 1 = n.
Proof. intros n Hn. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. rewrite Z.mul_comm, Z.div_mul; lia. Qed.

Definition reserve_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists a2',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom rsegs)
/\ munch [] m m /\ wmono rsegs m m /\ mem_inv rsegs m.

Definition reserve_stmt : Prop :=
forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (S n r : Z) (szb : byte) (rest : list cell),
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 r -> 0 <= r <= 22 ->
bv_unsigned szb = 2 * n -> 0 <= n ->
rw_cells rsegs m S (C1 szb :: rest) ->
mem_inv rsegs m ->
evt rsegs (reserve_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 reserve_entry) fc None m (seg_rom rsegs)).

Lemma reserve_spec : reserve_stmt.
Proof.
unfold reserve_stmt. intros until rest. intros A0 A1 Hr Hsz Hn OBJ MI. subst a0 a1.
pose proof (bv_unsigned_in_range 8 szb) as SR. unfold bv_modulus in SR. cbn in SR.
pose proof (rw_cells_bound _ _ _ _ OBJ) as OB. cbn [cells_size csize] in OB.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
unfold reserve_entry.
step. step. if_falsex.
step. change (zxb szb) with (Z_to_bv 64 (bv_unsigned szb)). rewrite Hsz.
step. rewrite (unsigned_lit (2 * n)) by lia. rewrite land1_even.
step. if_false.
step. step. if_falsex.
step.
finish.
Qed.

Definition pushb_W (sp S n : Z) : list (Z * Z) := [(sp - 64, sp); (S, S + 1); (S + n + 1, S + n + 3)].

Definition pushb_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a1 : word) (S n lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0' a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (szb' : byte),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch (pushb_W (bv_unsigned sp) S n) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ bv_unsigned szb' = 2 * (n + 1)
/\ rw_cells rsegs m' S [C1 szb']
/\ rw_cells rsegs m' (S + n + 1) [C1 (Z_to_bv 8 (bv_unsigned a1)); C1 b0]
/\ stk rsegs m' lo (bv_unsigned sp).

Definition pushb_stmt : Prop :=
forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (S n lo : Z) (szb x y : byte),
a0 = Z_to_bv 64 S ->
bv_unsigned szb = 2 * n -> 0 <= n <= 21 ->
rw_cells rsegs m S [C1 szb] ->
rw_cells rsegs m (S + n + 1) [C1 x; C1 y] ->
stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 ->
(S + 24 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= S) ->
mem_inv rsegs m ->
evt rsegs (pushb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a1 S n lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pushb_entry) fc None m (seg_rom rsegs)).

Lemma pushb_spec : pushb_stmt.
Proof.
unfold pushb_stmt. intros until y. intros A0 Hsz Hn SZ WIN ST LO SEP MI. subst a0.
pose proof (bv_unsigned_in_range 8 szb) as SR. unfold bv_modulus in SR. cbn in SR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof (bv_unsigned_in_range 64 a1) as CR. unfold bv_modulus in CR. cbn in CR.
pose proof (rw_cells_bound _ _ _ _ SZ) as OB1. cbn [cells_size csize Nat.add] in OB1.
pose proof (rw_cells_bound _ _ _ _ WIN) as OB2. cbn [cells_size csize Nat.add] in OB2.
pose proof (munch_refl (pushb_W (bv_unsigned sp) S n) m) as MU. pose proof (wmono_refl rsegs m) as WM.
unfold pushb_W in MU. unfold pushb_entry.
carve_frame 64%nat ST.
do 9 step.

step. step. change (zxb szb) with (Z_to_bv 64 (bv_unsigned szb)). rewrite Hsz.
step. rewrite (unsigned_lit (2 * n)) by lia. rewrite land1_even.
step. step. if_false.

step. step. if_truex.

step. rewrite (unsigned_lit (2 * n)) by lia. rewrite shiftr1_double by lia.
step. step.
step. rewrite le1_w. rewrite (unsigned_lit (2 * n + 2)) by lia. mem_after_store.
step.

step. replace (S + 1 + n) with (S + n + 1) by lia.
step. rewrite le1_w. mem_after_store.
step. rewrite le1_w. rewrite (unsigned_lit 0) by lia. change (Z_to_bv 8 0) with b0. mem_after_store.

do 10 step.
lazymatch goal with H : rw_cells rsegs ?mx (bv_unsigned sp + -64) _ |- _ => rename H into FR2 end.
lazymatch goal with H : stk rsegs ?mx lo _ |- _ => rename H into ST2 end.
release_frame FR2 ST2 (bv_unsigned sp).
finish.
2: eassumption.
rewrite Z_to_bv_unsigned. change (bv_wrap 8 (2 * n + 2)) with ((2 * n + 2) mod 2 ^ 8). rewrite Z.mod_small; lia.
Qed.
