(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1bs X1c2 X1br X1bq.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1h7 X1go X1hk X1ho X1n8.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1r3 X1nt X1rh X1re.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.

Definition sbctl_armpc (c : Z) : Z :=
if c =? 0 then 0x2e970 else if c =? 3 then 0x2e950 else if c =? 20 then 0x2e8e8 else if c =? 24 then 0x2eb80
else if c =? 25 then 0x2ebd0 else if c =? 39 then 0x2e880 else if c =? 100 then 0x2e7ac else if c =? 101 then 0x2ec90
else if c =? 103 then 0x2ec54 else if c =? 104 then 0x2ec40 else 0x2ec6c.
Definition sbctl_code_ok (c : Z) : Prop :=
c = 0 \/ c = 3 \/ c = 20 \/ c = 24 \/ c = 25 \/ c = 39 \/ c = 100 \/ c = 101 \/ c = 103 \/ c = 104 \/ c = 105.

Definition sbctl_frame (j0 : list byte) (s1 s0 ra : word) : list cell := [CB 8 j0; C8 s1; C8 s0; C8 ra].

Definition sbctl_at_arm (ra sp gp tp t0 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (S P c lo : Z) (m : mem) : machine_state -> Prop :=
fun ms1 => exists (t1 a0 a1 a4 : word) (j0 : list byte) (m1 : mem),
ms1 = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 S)
a0 a1 (Z_to_bv 64 P) (Z_to_bv 64 c) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (sbctl_armpc c)) fc None m1 (seg_rom rsegs)
/\ rw_cells rsegs m1 (bv_unsigned sp + -32) (sbctl_frame j0 s1 s0 ra)
/\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
/\ stk rsegs m1 lo (bv_unsigned sp + -32).

Lemma sbctl_entry : forall (mo : spx_mode) (S P c lo : Z) (hrest : list cell)
(ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
(mo = ModeWB \/ mo = ModeUWB) ->
rw_cells rsegs m S (C8 (Z_to_bv 64 (sb_mode_ptr NB_MODE_PTR A_speex_wb_mode A_speex_uwb_mode mo)) :: hrest) -> Z.of_nat (cells_size hrest) = 152 ->
rtables_pristine m ->
stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> 0x6e000 <= lo ->
(S + 160 <= lo \/ bv_unsigned sp <= S) -> 0 < S -> S mod 8 = 0 -> S + 160 < 2^63 ->
sbctl_code_ok c ->
mem_inv rsegs m ->
evt rsegs (sbctl_at_arm ra sp gp tp t0 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc S P c lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 c) (Z_to_bv 64 P) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_decoder_ctl) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros MO P0 HR TP ST LO GL AP GS S8 SB CODE MI. pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
assert (EWB : A_speex_wb_mode = 0x3bbb8) by reflexivity. assert (EUWB : A_speex_uwb_mode = 0x3bc18) by reflexivity.
pose proof (desc_of_pristine m mo TP) as ND.
destruct MO as [-> | ->]; cbn [sb_mode_ptr desc_cells_of] in P0, ND; unfold wb_desc_cells, uwb_desc_cells in ND.
all: unfold A_speex_decoder_ctl; step; if_false_z; step; step; if_false_z; step; step; if_false_z; step; step; if_false_z; step; step.
all: pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU; pose proof (wmono_refl rsegs m) as WM.
all: step; carve_frame 32%nat ST.
all: step; step; step.
all: step; step; step; step.
all: destruct CODE as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]].
all: step; if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia; try (exfalso; lia).

1-6,12-17: step; step; step; step; step; step; step.

all: try (step; step; step; if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia; try (exfalso; lia); step; step; step; step; step; step; step).
all: apply evt_done; unfold sbctl_at_arm, sbctl_armpc, sbctl_frame; cbn [Z.eqb Pos.eqb];
sf_eexists 6%nat; split; [reflexivity|]; split; [eassumption|]; split; [exact MU|]; split; [exact WM|]; split; [assumption| assumption].
Qed.

Lemma sbctl_exit : forall (SP : Z) (j0 : list byte) (xra xs0 xs1 : word)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
32 <= SP < 2^64 -> sp = Z_to_bv 64 (SP + -32) ->
rw_cells rsegs m (SP + -32) (sbctl_frame j0 xs1 xs0 xra) -> mem_inv rsegs m ->
evt rsegs (fun ms' => ms' = MS (mkR xra (Z_to_bv 64 SP) gp tp t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc xra) fc None m (seg_rom rsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2ed88) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros HSP -> FR MI. unfold sbctl_frame in FR.
step. step. step. step. step.
apply evt_done. rewrite ?unsigned_lit by lia. replace (SP + -32 + 32) with SP by lia. reflexivity.
Qed.

Lemma sbctl_exit_get : forall (SP P : Z) (w : word) (j0 : list byte) (xra xs0 xs1 : word)
(ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
32 <= SP < 2^64 -> sp = Z_to_bv 64 (SP + -32) ->
rw_cells rsegs m (SP + -32) (sbctl_frame j0 xs1 xs0 xra) -> rw_cells rsegs m P [C4 w] ->
(P + 4 <= SP + -32 \/ SP <= P) -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists m', ms' = MS (mkR xra (Z_to_bv 64 SP) gp tp t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc xra) fc None m' (seg_rom rsegs)
/\ m' = write_to_mem m (wa (P + Z.of_nat 0)) (le4 a1) /\ mem_inv rsegs m' /\ rw_cells rsegs m' P [C4 a1])
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 P) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2ed84) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros HSP -> FR ARG AP MI. unfold sbctl_frame in FR.
pose proof (rw_cells_bound _ _ _ _ ARG) as B. cbn [cells_size csize Nat.add] in B.
step.
step. step. step. step. step.
apply evt_done. eexists. rewrite ?unsigned_lit by lia. replace (SP + -32 + 32) with SP by lia.
split; [reflexivity|]. split; [reflexivity|]. split; assumption.
Qed.
