(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1bs X1c2 X1br X1bq.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7 X1h7 X1go X1hk X1ho X1n8 X1ed.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1r3 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.

Definition nbctl_armpc (c : Z) : Z :=
if c =? 0 then 0x1ed38 else if c =? 3 then 0x1ed14 else if c =? 20 then 0x1ed78 else if c =? 24 then 0x1ed48
else if c =? 25 then 0x1ed2c else if c =? 39 then 0x1eca0 else if c =? 100 then 0x1ebc0 else if c =? 101 then 0x1edc8
else if c =? 103 then 0x1ee04 else if c =? 104 then 0x1edf8 else 0x1eda8.
Definition nbctl_code_ok (c : Z) : Prop :=
c = 0 \/ c = 3 \/ c = 20 \/ c = 24 \/ c = 25 \/ c = 39 \/ c = 100 \/ c = 101 \/ c = 103 \/ c = 104 \/ c = 105.

Definition nbctl_frame (j0 : list byte) (v9 v8 s3 s2 s1 s0 ra : word) : list cell :=
[CB 8 j0; C8 v9; C8 v8; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition nbctl_at_arm (ra sp gp tp t0 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (S P c lo : Z) (m : mem) : machine_state -> Prop :=
fun ms1 => exists (t1 a0 a1 a2 : word) (j0 : list byte) (m1 : mem),
ms1 = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 S)
a0 a1 a2 (Z_to_bv 64 c) a4 a5 a6 a7 (Z_to_bv 64 (S + 2168)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (nbctl_armpc c)) fc None m1 (seg_rom rsegs)
/\ rw_cells rsegs m1 (bv_unsigned sp + -64) (nbctl_frame j0 (reg_get F 9) (reg_get F 8) s3 s2 s1 s0 ra)
/\ munch [(bv_unsigned sp + -64, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
/\ stk rsegs m1 lo (bv_unsigned sp + -64).

Lemma nbctl_entry : forall (S P c lo : Z) (hrest : list cell)
(ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells rsegs m S (C8 (Z_to_bv 64 NB_MODE_PTR) :: hrest) -> Z.of_nat (cells_size hrest) = 24 ->
rtables_pristine m ->
stk rsegs m lo (bv_unsigned sp) -> lo + 64 <= bv_unsigned sp -> 0x67000 <= lo ->
(S + 32 <= lo \/ bv_unsigned sp <= S) -> 0 < S -> S + 2968 < 2^63 ->
nbctl_code_ok c ->
mem_inv rsegs m ->
evt rsegs (nbctl_at_arm ra sp gp tp t0 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc S P c lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 c) (Z_to_bv 64 P) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_decoder_ctl) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros P0 HR TP ST LO GL AP GS SB CODE MI. pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
assert (ENB : NB_MODE_PTR = 0x342b8) by reflexivity.
pose proof (nb_desc_of_pristine m TP) as ND. unfold nb_desc_cells in ND.
unfold A_speex_decoder_ctl.
step. step. step.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
step. carve_frame 64%nat ST.
step. step. step. step. step. step. step.
step. step. step. step. step. step.
destruct CODE as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]].
all: step; if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia; try (exfalso; lia).

1-5: step; step; step; step; step; step; step.

6: step; step; step; if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia; try (exfalso; lia); step; step; step; step; step; step; step.

7-11: step; step; step; if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia; try (exfalso; lia);
step; step; step; if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia; try (exfalso; lia); step; step; step; step; step; step; step.
all: apply evt_done; unfold nbctl_at_arm, nbctl_armpc, nbctl_frame; cbn [Z.eqb Pos.eqb];
sf_eexists 6%nat; split; [reflexivity|]; split; [eassumption|]; split; [exact MU|]; split; [exact WM|]; split; [assumption| assumption].
Qed.

Lemma nbctl_exit : forall (SP : Z) (j0 : list byte) (v9 v8 xra xs0 xs1 xs2 xs3 : word)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
64 <= SP < 2^64 -> sp = Z_to_bv 64 (SP + -64) ->
rw_cells rsegs m (SP + -64) (nbctl_frame j0 v9 v8 xs3 xs2 xs1 xs0 xra) -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists F', ms' = MS (mkR xra (Z_to_bv 64 SP) gp tp t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc xra) fc None m (seg_rom rsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1ee24) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros HSP -> FR MI. unfold nbctl_frame in FR.
step. step. step. step. step. step. step. step. step.
apply evt_done. eexists. rewrite ?unsigned_lit by lia. replace (SP + -64 + 64) with SP by lia. reflexivity.
Qed.

Lemma nbctl_exit_get : forall (SP P : Z) (w : word) (j0 : list byte) (v9 v8 xra xs0 xs1 xs2 xs3 : word)
(ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
64 <= SP < 2^64 -> sp = Z_to_bv 64 (SP + -64) ->
rw_cells rsegs m (SP + -64) (nbctl_frame j0 v9 v8 xs3 xs2 xs1 xs0 xra) -> rw_cells rsegs m P [C4 w] ->
(P + 4 <= SP + -64 \/ SP <= P) -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists F' m', ms' = MS (mkR xra (Z_to_bv 64 SP) gp tp t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc xra) fc None m' (seg_rom rsegs)
/\ m' = write_to_mem m (wa (P + Z.of_nat 0)) (le4 a1) /\ mem_inv rsegs m' /\ rw_cells rsegs m' P [C4 a1])
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 P) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1ee20) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros HSP -> FR ARG AP MI. unfold nbctl_frame in FR.
pose proof (rw_cells_bound _ _ _ _ ARG) as B. cbn [cells_size csize Nat.add] in B.
step.
step. step. step. step. step. step. step. step. step.
apply evt_done. sf_eexists 2%nat. rewrite ?unsigned_lit by lia. replace (SP + -64 + 64) with SP by lia.
split; [reflexivity|]. split; [reflexivity|]. split; assumption.
Qed.

Lemma land64_small : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Ltac land_cases K :=
repeat match type of K with context [Z.land ?x 18446744073709551615] =>
let E := fresh "E" in
destruct (Z.eq_dec x (2^64)) as [E|E];
[ rewrite E in K; change (Z.land (2^64) 18446744073709551615) with 0 in K
| rewrite (land64_small x) in K by lia ] end.
Ltac zlits := repeat match goal with |- context [Z.mul (Zpos ?a) (Zpos ?b)] => let v := eval vm_compute in (Z.mul (Zpos a) (Zpos b)) in change (Z.mul (Zpos a) (Zpos b)) with v end.
Ltac kill_branch K := zify_cond K; rewrite ?unsigned_lit in K by lia; try (exfalso; first [lia | congruence | (land_cases K; first [lia | congruence])]).

Section ARMS.
Context {RCEIL : RunCeiling}.
Variables (S P : Z) (ra sp gp tp t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
Let R (c : Z) (xa0 xa1 xa2 xa3 xa4 : word) : bvmap 5 word :=
mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 S) xa0 xa1 xa2 xa3 xa4 a5 a6 a7 (Z_to_bv 64 (S + 2168)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.
Hypothesis MI : mem_inv rsegs m.
Hypothesis SB : 0 < S /\ S + 2968 < 2^63.

#[using="Type"] Lemma nbarm_get_frame_size :
evt rsegs (fun ms' => ms' = MS (R 3 (Z_to_bv 64 0) (Z_to_bv 64 160) a2 (Z_to_bv 64 3) a4) F (Z_to_bv 64 0x1ee20) fc None m (seg_rom rsegs))
(MS (R 3 a0 a1 a2 (Z_to_bv 64 3) a4) F (Z_to_bv 64 (nbctl_armpc 3)) fc None m (seg_rom rsegs)).
Proof. unfold nbctl_armpc, R. cbn [Z.eqb Pos.eqb]. step. step. step. apply evt_done. reflexivity. Qed.

#[using="Type"] Lemma nbarm_get_lookahead :
evt rsegs (fun ms' => ms' = MS (R 39 (Z_to_bv 64 0) (Z_to_bv 64 40) a2 (Z_to_bv 64 39) a4) F (Z_to_bv 64 0x1ee20) fc None m (seg_rom rsegs))
(MS (R 39 a0 a1 a2 (Z_to_bv 64 39) a4) F (Z_to_bv 64 (nbctl_armpc 39)) fc None m (seg_rom rsegs)).
Proof. unfold nbctl_armpc, R. cbn [Z.eqb Pos.eqb]. step. step. step. apply evt_done. reflexivity. Qed.

#[using="Type"] Lemma nbarm_get_sampling_rate : forall (c1 c2 c4 c5 : word) (sr : Z),
rw_cells rsegs m S [C8 (Z_to_bv 64 NB_MODE_PTR); C4 c1; C4 c2; C4 (Z_to_bv 64 sr); C4 c4; C8 c5] -> - 2^31 <= sr < 2^31 ->
evt rsegs (fun ms' => ms' = MS (R 25 (Z_to_bv 64 0) (Z_to_bv 64 sr) a2 (Z_to_bv 64 25) a4) F (Z_to_bv 64 0x1ee20) fc None m (seg_rom rsegs))
(MS (R 25 a0 a1 a2 (Z_to_bv 64 25) a4) F (Z_to_bv 64 (nbctl_armpc 25)) fc None m (seg_rom rsegs)).
Proof.
intros c1 c2 c4 c5 sr P0 SR. unfold nbctl_armpc, R. cbn [Z.eqb Pos.eqb]. step. step. rewrite sx32_lit by lia.
step. apply evt_done. reflexivity.
Qed.

#[using="MI SB"] Lemma nbarm_set_enh : forall (w e1 : word) (pad : list byte) (sm sid lpc : word),
rw_cells rsegs m P [C4 w] -> rw_cells rsegs m (S + 2232) [C4 e1; CB 4 pad; C8 sm; C4 sid; C4 lpc] ->
(P + 4 <= S \/ S + 2968 <= P) ->
evt rsegs (fun ms' => exists m', ms' = MS (R 0 (Z_to_bv 64 0) (sx32 w) a2 (Z_to_bv 64 0) a4) F (Z_to_bv 64 0x1ee24) fc None m' (seg_rom rsegs)
/\ rw_cells rsegs m' (S + 2232) [C4 e1; CB 4 pad; C8 sm; C4 sid; C4 (sx32 w)] /\ rw_cells rsegs m' P [C4 w]
/\ munch [(S + 2252, S + 2256)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
(MS (R 0 a0 a1 a2 (Z_to_bv 64 0) a4) F (Z_to_bv 64 (nbctl_armpc 0)) fc None m (seg_rom rsegs)).
Proof.
intros w e1 pad sm sid lpc ARG CFG AP. unfold nbctl_armpc, R. cbn [Z.eqb Pos.eqb].
pose proof (rw_cells_bound _ _ _ _ ARG) as B. cbn [cells_size csize Nat.add] in B.
pose proof (munch_refl [(S + 2252, S + 2256)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
step. step. step. step. apply evt_done. eexists. split; [reflexivity|]. repeat (split; [assumption|]). assumption.
Qed.

#[using="MI SB"] Lemma nbarm_set_sampling_rate : forall (w c1 c2 c3 c4 c5 : word),
rw_cells rsegs m P [C4 w] -> rw_cells rsegs m S [C8 (Z_to_bv 64 NB_MODE_PTR); C4 c1; C4 c2; C4 c3; C4 c4; C8 c5] ->
(P + 4 <= S \/ S + 2968 <= P) ->
evt rsegs (fun ms' => exists m', ms' = MS (R 24 (Z_to_bv 64 0) (sx32 w) a2 (Z_to_bv 64 24) a4) F (Z_to_bv 64 0x1ee24) fc None m' (seg_rom rsegs)
/\ rw_cells rsegs m' S [C8 (Z_to_bv 64 NB_MODE_PTR); C4 c1; C4 c2; C4 (sx32 w); C4 c4; C8 c5] /\ rw_cells rsegs m' P [C4 w]
/\ munch [(S + 16, S + 20)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
(MS (R 24 a0 a1 a2 (Z_to_bv 64 24) a4) F (Z_to_bv 64 (nbctl_armpc 24)) fc None m (seg_rom rsegs)).
Proof.
intros w c1 c2 c3 c4 c5 ARG P0 AP. unfold nbctl_armpc, R. cbn [Z.eqb Pos.eqb].
pose proof (rw_cells_bound _ _ _ _ ARG) as B. cbn [cells_size csize Nat.add] in B.
pose proof (munch_refl [(S + 16, S + 20)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
step. step. step. step. apply evt_done. eexists. split; [reflexivity|]. repeat (split; [assumption|]). assumption.
Qed.

#[using="MI SB"] Lemma nbarm_set_wideband : forall (w c1 c2 c3 c4 : word) (pad : list byte),
rw_cells rsegs m P [C4 w] -> rw_cells rsegs m (S + 2948) [C4 c1; C4 c2; C4 c3; C4 c4; CB 4 pad] ->
(P + 4 <= S \/ S + 2968 <= P) ->
evt rsegs (fun ms' => exists m', ms' = MS (R 105 (Z_to_bv 64 0) (sx32 w) a2 (Z_to_bv 64 105) a4) F (Z_to_bv 64 0x1ee24) fc None m' (seg_rom rsegs)
/\ rw_cells rsegs m' (S + 2948) [C4 c1; C4 c2; C4 (sx32 w); C4 c4; CB 4 pad] /\ rw_cells rsegs m' P [C4 w]
/\ munch [(S + 2956, S + 2960)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
(MS (R 105 a0 a1 a2 (Z_to_bv 64 105) a4) F (Z_to_bv 64 (nbctl_armpc 105)) fc None m (seg_rom rsegs)).
Proof.
intros w c1 c2 c3 c4 pad ARG TL AP. unfold nbctl_armpc, R. cbn [Z.eqb Pos.eqb].
pose proof (rw_cells_bound _ _ _ _ ARG) as B. cbn [cells_size csize Nat.add] in B.
pose proof (munch_refl [(S + 2956, S + 2960)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
step. step. step. step. apply evt_done. eexists. split; [reflexivity|]. repeat (split; [assumption|]). assumption.
Qed.

#[using="MI SB"] Lemma nbarm_set_handler : forall (pad : word) (SH SD : Z) (cbs : list byte),
rw_cells rsegs m P [C4 (Z_to_bv 64 9); C4 pad; C8 (Z_to_bv 64 SH); C8 (Z_to_bv 64 SD)] ->
rw_cells rsegs m (S + 2256) [CB 640 cbs] ->
(P + 24 <= S \/ S + 2968 <= P) ->
evt rsegs (fun ms' => exists m' xa2, ms' = MS (R 20 (Z_to_bv 64 0) (Z_to_bv 64 9) xa2 (Z_to_bv 64 SH) (Z_to_bv 64 SD)) F (Z_to_bv 64 0x1ee24) fc None m' (seg_rom rsegs)
/\ rw_cells rsegs m' (S + 2256) [CB 360 (firstn 360 cbs); C4 (Z_to_bv 64 9); CB 4 (firstn 4 (skipn 364 cbs));
C8 (Z_to_bv 64 SH); C8 (Z_to_bv 64 SD); CB 256 (skipn 8 (skipn 12 (skipn 364 cbs)))]
/\ rw_cells rsegs m' P [C4 (Z_to_bv 64 9); C4 pad; C8 (Z_to_bv 64 SH); C8 (Z_to_bv 64 SD)]
/\ munch [(S + 2616, S + 2640)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
(MS (R 20 a0 a1 a2 (Z_to_bv 64 20) a4) F (Z_to_bv 64 (nbctl_armpc 20)) fc None m (seg_rom rsegs)).
Proof.
intros pad SH SD cbs ARG BL AP. unfold nbctl_armpc, R. cbn [Z.eqb Pos.eqb].
pose proof (rw_cells_bound _ _ _ _ ARG) as B. cbn [cells_size csize Nat.add] in B.
pose proof BL as BL0. destruct BL0 as [[[LEN _] _] _].
pose proof (munch_refl [(S + 2616, S + 2640)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
step. step. rewrite sx32_lit by lia. step. step. step. step. rewrite ?unsigned_lit by lia. step. step.
step. step. step. step.
apply evt_done. sf_eexists 2%nat. split; [reflexivity|]. repeat (split; [eassumption|]). assumption.
Qed.

#[using="MI SB"] Lemma nbarm_set_innovation_save : forall (old : word),
rw_cells rsegs m (S + 2184) [C8 old] ->
evt rsegs (fun ms' => exists m', ms' = MS (R 104 (Z_to_bv 64 0) a1 a2 (Z_to_bv 64 104) a4) F (Z_to_bv 64 0x1ee24) fc None m' (seg_rom rsegs)
/\ rw_cells rsegs m' (S + 2184) [C8 (Z_to_bv 64 P)]
/\ munch [(S + 2184, S + 2192)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
(MS (R 104 a0 a1 a2 (Z_to_bv 64 104) a4) F (Z_to_bv 64 (nbctl_armpc 104)) fc None m (seg_rom rsegs)).
Proof.
intros old ISV. unfold nbctl_armpc, R. cbn [Z.eqb Pos.eqb].
pose proof (munch_refl [(S + 2184, S + 2192)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
step. step. step. apply evt_done. eexists. split; [reflexivity|]. repeat (split; [assumption|]). assumption.
Qed.

#[using="Type"] Lemma nbarm_get_dtx_status : forall (c1 c3 c4 : word) (pad : list byte) (dtx : Z),
rw_cells rsegs m (S + 2948) [C4 c1; C4 (Z_to_bv 64 dtx); C4 c3; C4 c4; CB 4 pad] -> 0 <= dtx <= 1 ->
evt rsegs (fun ms' => ms' = MS (R 103 (Z_to_bv 64 0) (Z_to_bv 64 dtx) a2 (Z_to_bv 64 103) a4) F (Z_to_bv 64 0x1ee20) fc None m (seg_rom rsegs))
(MS (R 103 a0 a1 a2 (Z_to_bv 64 103) a4) F (Z_to_bv 64 (nbctl_armpc 103)) fc None m (seg_rom rsegs)).
Proof.
intros c1 c3 c4 pad dtx TL HD. unfold nbctl_armpc, R. cbn [Z.eqb Pos.eqb]. step. step. rewrite sx32_lit by lia.
step. apply evt_done. reflexivity.
Qed.

#[using="MI"] Lemma nbarm_get_pi_gain : forall (ws pg : list word),
rw_cells rsegs m P (f32 ws) -> length ws = 4%nat -> rw_cells rsegs m (S + 2168) (f32 pg) -> length pg = 4%nat ->
(P + 16 <= S \/ S + 2968 <= P) ->
evt rsegs (fun ms' => exists m' F' ws',
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (P + 16)) (Z_to_bv 64 S) (Z_to_bv 64 0) a1 a2 (Z_to_bv 64 100) a4 a5 a6 a7
(Z_to_bv 64 (S + 2184)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (Z_to_bv 64 0x1ee24) fc None m' (seg_rom rsegs)
/\ rw_cells rsegs m' P (f32 ws') /\ length ws' = 4%nat /\ rw_cells rsegs m' (S + 2168) (f32 pg)
/\ munch [(P, P + 16)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
(MS (R 100 a0 a1 a2 (Z_to_bv 64 100) a4) F (Z_to_bv 64 (nbctl_armpc 100)) fc None m (seg_rom rsegs)).
Proof.
intros ws pg ARG LW PG LP AP. unfold nbctl_armpc, R. cbn [Z.eqb Pos.eqb].
pose proof (rw_cells_bound _ _ _ _ ARG) as B. rewrite cells_size_f32, LW in B.
destruct ws as [|w0 [|w1 [|w2 [|w3 [|]]]]]; try discriminate LW. destruct pg as [|g0 [|g1 [|g2 [|g3 [|]]]]]; try discriminate LP.
rewrite !f32_cons, ?f32_nil in ARG. rewrite !f32_cons, ?f32_nil in PG. cbn [f32 map] in ARG, PG.
pose proof (munch_refl [(P, P + 16)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
step.
step. step. step. step. step. if_cases K1; kill_branch K1.
step. step. step. step. step. if_cases K2; kill_branch K2.
step. step. step. step. step. if_cases K3; kill_branch K3.
step. step. step. step. step. if_cases K4; kill_branch K4.
step. step. step.
apply evt_done. eexists _, _, [_; _; _; _]. rewrite ?unsigned_lit by lia.
split; [repeat match goal with |- context [Z_to_bv 64 (?a + ?b + ?c)] => replace (a + b + c) with (a + (b + c)) by lia; cbn [Z.add Pos.add Pos.succ] end; reflexivity|].
rewrite !f32_cons, ?f32_nil. cbn [f32 map]. split; [eassumption|]. split; [reflexivity|]. split; [eassumption|]. repeat (split; [assumption|]). assumption.
Qed.

Definition exc_head (i : nat) (so c : Z) (k : iclob) (xra xa0 : word) (Fi : bvmap 5 word) (fci : bv 32) (mi : mem) : machine_state :=
MS (mkR xra sp gp tp (c_t0 k) (c_t1 k) (c_t2 k) (Z_to_bv 64 so) (Z_to_bv 64 S) xa0 (c_a1 k) (c_a2 k) (c_a3 k) (c_a4 k) (c_a5 k) (c_a6 k) (c_a7 k)
(Z_to_bv 64 c) (Z_to_bv 64 640) s4 s5 s6 s7 s8 s9 s10 s11 (c_t3 k) (c_t4 k) (c_t5 k) (c_t6 k)) Fi
(Z_to_bv 64 (if (i <? 4)%nat then 0x1edd0 else 0x1edf0)) fci None mi (seg_rom rsegs).
Definition exc_inv (mi : mem) (fci : bv 32) (eb : list word) : Prop :=
mem_inv rsegs mi /\ frm0 fci /\ (exists wsi, rw_cells rsegs mi P (f32 wsi) /\ length wsi = 4%nat)
/\ rw_cells rsegs mi (S + 2032) [C8 (Z_to_bv 64 (S + 1368))] /\ rw_cells rsegs mi (S + 32) (f32 eb)
/\ munch [(P, P + 16)] m mi /\ wmono rsegs m mi.

#[using="Type"] Lemma nbarm_get_exc_iter : forall (i : nat) (so c : Z) (eb : list word) k xra xa0 Fi fci mi,
(i < 4)%nat -> so = P + 4 * Z.of_nat i -> c = 160 * Z.of_nat i -> length eb = 500%nat -> (P + 16 <= S \/ S + 2968 <= P) -> exc_inv mi fci eb ->
evt rsegs (fun ms' => exists k' xa0' F' fc' m', ms' = exc_head (Datatypes.S i) (P + 4 * (Z.of_nat i + 1)) (160 * (Z.of_nat i + 1)) k' (Z_to_bv 64 0x1ede0) xa0' F' fc' m' /\ exc_inv m' fc' eb)
(exc_head i so c k xra xa0 Fi fci mi).
Proof.
intros i so c eb k xra xa0 Fi fci mi Hi -> -> LE AP sfH_; first [ sf_destruct 7%nat sfH_ as MIi FRMi (wsi & ARGi & LWi) EXi EBi MUi WMi | sf_fb; destruct sfH_ as (MIi & FRMi & (wsi & ARGi & LWi) & EXi & EBi & MUi & WMi) ]. unfold exc_head.
replace (i <? 4)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi).
pose proof (rw_cells_bound _ _ _ _ ARGi) as Bi. rewrite cells_size_f32, LWi in Bi.

pose proof EBi as E0. chunk_split_f32 E0 at (334 + 40 * i)%nat as E1.
apply (rw_cells_f32_split _ _ _ _ 40) in E0. destruct E0 as [XS _].
rewrite firstn_length_le in XS by (rewrite LE; lia).
set (xs := firstn 40 (skipn (334 + 40 * i) eb)) in XS.
assert (LXS : length xs = 40%nat) by (subst xs; rewrite firstn_length_le by (rewrite length_skipn, LE; lia); reflexivity).
replace (S + 32 + Z.of_nat (4 * (334 + 40 * i))) with (S + 1368 + 160 * Z.of_nat i) in XS by lia. clear E1.
step. step. rewrite ?unsigned_lit by lia. step. step.
replace (Z_to_bv 64 40) with (Z_to_bv 64 (Z.of_nat (length xs))) by (rewrite LXS; reflexivity).
eapply evt_cut.
{ eapply (compute_rms16_spec xs (S + 1368 + 160 * Z.of_nat i)); [exact MIi| rewrite LXS; cbn; lia| | exact FRMi].
match goal with |- rw_cells _ _ ?a _ => replace a with (S + 1368 + 160 * Z.of_nat i) by lia end. exact XS. }
cbv beta. intros ms2 sfH_; first [ sf_destruct 24%nat sfH_ as y0 y1 y2 ya0 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 g13 g14 g15 fc2 m2 -> MU2 WM2 MI2 FRM2 | sf_fb; destruct sfH_ as (y0 & y1 & y2 & ya0 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & g13 & g14 & g15 & fc2 & m2 & -> & MU2 & WM2 & MI2 & FRM2) ].
rewrite ret_pc_even by lia. change (mem_inv rsegs m2) in MI2. change (wmono rsegs mi m2) in WM2.
assert (ARG2 : rw_cells rsegs m2 P (f32 wsi)) by (eapply rw_cells_transport; [exact ARGi| exact MU2| exact WM2| exact I]).
assert (EX2 : rw_cells rsegs m2 (S + 2032) [C8 (Z_to_bv 64 (S + 1368))]) by (eapply rw_cells_transport; [exact EXi| exact MU2| exact WM2| exact I]).
assert (EB2 : rw_cells rsegs m2 (S + 32) (f32 eb)) by (eapply rw_cells_transport; [exact EBi| exact MU2| exact WM2| exact I]).
assert (MU2' : munch [(P, P + 16)] m m2).
{ eapply munch_trans; [exact MUi|]. eapply munch_weaken_to; [exact MU2|]. intros x _. exact I. }
assert (WM2' : wmono rsegs m m2) by (eapply wmono_trans; [exact WMi| exact WM2]).
clear ARGi EXi EBi MUi WMi MU2 WM2 XS.
destruct wsi as [|w0 [|w1 [|w2 [|w3 [|]]]]]; try discriminate LWi. rewrite !f32_cons, ?f32_nil in ARG2. cbn [f32 map] in ARG2.

destruct (Nat.eq_dec i 0) as [->|N0]; [| destruct (Nat.eq_dec i 1) as [->|N1]; [| destruct (Nat.eq_dec i 2) as [->|N2]; [| assert (i = 3%nat) as -> by lia]]];
try change (Z.of_nat 0) with 0; try change (Z.of_nat 1) with 1; try change (Z.of_nat 2) with 2; try change (Z.of_nat 3) with 3; zlits; rewrite ?Z.add_0_r.
all: step; step; step; rewrite ?unsigned_lit by lia; step; if_cases K; kill_branch K.
all: apply evt_done; unfold exc_inv; cbn [Nat.ltb Nat.leb];
try change (Z.of_nat 0) with 0; try change (Z.of_nat 1) with 1; try change (Z.of_nat 2) with 2; try change (Z.of_nat 3) with 3; cbn [Z.add Z.mul Pos.add Pos.mul Pos.succ].
all: eexists (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _, _; split;
[ unfold callR; cbn [c_t0 c_t1 c_t2 c_a1 c_a2 c_a3 c_a4 c_a5 c_a6 c_a7 c_t3 c_t4 c_t5 c_t6];
repeat match goal with |- context [Z_to_bv 64 (?a + ?b + ?c)] => replace (a + b + c) with (a + (b + c)) by lia; cbn [Z.add Pos.add Pos.succ] end; reflexivity |].
all: split; [assumption|]. all: split; [assumption|].
all: split; [eexists [_; _; _; _]; rewrite !f32_cons, ?f32_nil; cbn [f32 map]; split; [eassumption| reflexivity]|].
all: split; [assumption|]. all: split; [assumption|]. all: split; assumption.
Qed.

#[using="MI"] Lemma nbarm_get_exc : forall (ws eb : list word),
rw_cells rsegs m P (f32 ws) -> length ws = 4%nat ->
rw_cells rsegs m (S + 2032) [C8 (Z_to_bv 64 (S + 1368))] -> rw_cells rsegs m (S + 32) (f32 eb) -> length eb = 500%nat ->
(P + 16 <= S \/ S + 2968 <= P) -> frm0 fc ->
evt rsegs (fun ms' => exists m' F' fc' (k : iclob),
ms' = MS (mkR (Z_to_bv 64 0x1ede0) sp gp tp (c_t0 k) (c_t1 k) (c_t2 k) (Z_to_bv 64 (P + 16)) (Z_to_bv 64 S) (Z_to_bv 64 0) (c_a1 k) (c_a2 k) (c_a3 k) (c_a4 k) (c_a5 k) (c_a6 k) (c_a7 k)
(Z_to_bv 64 640) (Z_to_bv 64 640) s4 s5 s6 s7 s8 s9 s10 s11 (c_t3 k) (c_t4 k) (c_t5 k) (c_t6 k)) F' (Z_to_bv 64 0x1ee24) fc' None m' (seg_rom rsegs)
/\ exc_inv m' fc' eb)
(MS (R 101 a0 a1 a2 (Z_to_bv 64 101) a4) F (Z_to_bv 64 (nbctl_armpc 101)) fc None m (seg_rom rsegs)).
Proof.
intros ws eb ARG LW EX EB LE AP FRM. unfold nbctl_armpc, R. cbn [Z.eqb Pos.eqb].
assert (I0 : exc_inv m fc eb).
{ unfold exc_inv. split; [exact MI|]. split; [exact FRM|]. split; [exists ws; split; assumption|]. split; [exact EX|]. split; [exact EB|].
split; [apply munch_refl| apply wmono_refl]. }
step. step.
eapply evt_cut. { apply (nbarm_get_exc_iter 0%nat P 0 eb (ICL t0 t1 t2 a1 a2 (Z_to_bv 64 101) a4 a5 a6 a7 t3 t4 t5 t6) ra a0 F fc m); [lia| cbn; lia| reflexivity| exact LE| exact AP| exact I0]. }
cbv beta. intros ms1 sfH_; first [ sf_destruct 7%nat sfH_ as k1 x1 F1 fc1 m1 -> I1 | sf_fb; destruct sfH_ as (k1 & x1 & F1 & fc1 & m1 & -> & I1) ].
eapply evt_cut. { apply (nbarm_get_exc_iter 1%nat _ _ eb k1 _ x1 F1 fc1 m1); [lia| reflexivity| reflexivity| exact LE| exact AP| exact I1]. }
cbv beta. intros ms2 sfH_; first [ sf_destruct 7%nat sfH_ as k2 x2 F2 fc2 m2 -> I2 | sf_fb; destruct sfH_ as (k2 & x2 & F2 & fc2 & m2 & -> & I2) ].
eapply evt_cut. { apply (nbarm_get_exc_iter 2%nat _ _ eb k2 _ x2 F2 fc2 m2); [lia| reflexivity| reflexivity| exact LE| exact AP| exact I2]. }
cbv beta. intros ms3 sfH_; first [ sf_destruct 7%nat sfH_ as k3 x3 F3 fc3 m3 -> I3 | sf_fb; destruct sfH_ as (k3 & x3 & F3 & fc3 & m3 & -> & I3) ].
eapply evt_cut. { apply (nbarm_get_exc_iter 3%nat _ _ eb k3 _ x3 F3 fc3 m3); [lia| reflexivity| reflexivity| exact LE| exact AP| exact I3]. }
cbv beta. intros ms4 sfH_; first [ sf_destruct 7%nat sfH_ as k4 x4 F4 fc4 m4 -> I4 | sf_fb; destruct sfH_ as (k4 & x4 & F4 & fc4 & m4 & -> & I4) ].
unfold exc_head. cbn [Nat.ltb Nat.leb]. change (Z.of_nat 3) with 3. cbn [Z.add Z.mul Pos.add Pos.mul Pos.succ].
pose proof I4 as (MI4 & _).
step. step.
apply evt_done. eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _). split; [cbn [c_t0 c_t1 c_t2 c_a1 c_a2 c_a3 c_a4 c_a5 c_a6 c_a7 c_t3 c_t4 c_t5 c_t6]; reflexivity| exact I4].
Qed.
End ARMS.

