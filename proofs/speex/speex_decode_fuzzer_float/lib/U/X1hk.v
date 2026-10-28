(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bq X1br.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pw X0pt X0qm.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ff X1h7 X1go.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1rh.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.

Notation rsegs := X1ff.rsegs.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Lemma unsigned_zxb : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof.
intros b. unfold zxb. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in *. cbn in R |- *. lia.
Qed.

Definition memcmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(xs ys : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom rsegs)
/\ (a0 = wz 0 <-> xs = ys).

Section Memcmp.
Context {RCEIL : RunCeiling}.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Variables (P Q : Z) (xs ys : list byte).
Hypothesis HX : u8ro rsegs m P xs.
Hypothesis HY : u8ro rsegs m Q ys.
Hypothesis LEN : length xs = length ys.
Hypothesis SMALL : Z.of_nat (length xs) < 2^32.

#[using="HX HY LEN SMALL"] Lemma memcmp_loop : forall (rest : list byte) (done : list byte) (resty : list byte) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
xs = done ++ rest -> ys = done ++ resty -> rest <> [] ->
evt rsegs (memcmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc xs ys m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (P + Z.of_nat (length done))) (wz (Q + Z.of_nat (length done))) (wz (Z.of_nat (length rest)))
a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x39c30) fc None m (seg_rom rsegs)).
Proof.
induction rest as [|x rest IH]; intros done resty t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 EX EY NE; [congruence|].
pose proof (bytes_at_bound _ _ _ _ HX) as BX. pose proof (bytes_at_bound _ _ _ _ HY) as BY.
assert (LR : length resty = S (length rest)).
{ apply (f_equal (@length byte)) in EX. apply (f_equal (@length byte)) in EY. rewrite length_app in EX, EY. cbn [length] in EX. lia. }
destruct resty as [|y resty]; [cbn in LR; lia|]. cbn [length] in LR.
rewrite EX in BX. rewrite EY in BY. rewrite length_app in BX, BY. cbn [length] in BX, BY.
pose proof (u8ro_read rsegs m P xs (Z.of_nat (length done)) x (wa (P + Z.of_nat (length done))) HX
ltac:(rewrite EX, Nat2Z.id, nth_error_app2, Nat.sub_diag by lia; reflexivity) ltac:(lia) eq_refl) as RX.
pose proof (u8ro_read rsegs m Q ys (Z.of_nat (length done)) y (wa (Q + Z.of_nat (length done))) HY
ltac:(rewrite EY, Nat2Z.id, nth_error_app2, Nat.sub_diag by lia; reflexivity) ltac:(lia) eq_refl) as RY.
unfold wz. zstep. zstep. clear RX RY. cbn [length].
zstep. if_cases K; zify_cond K.
all: lazymatch type of K with
| _ <> _ =>

zstep; zstep; apply evt_done; unfold memcmp_post; sf_eexists 15%nat; split; [reflexivity|];
split; intros E;
[ exfalso; apply K;
pose proof (bv_unsigned_in_range 8 x) as R1; pose proof (bv_unsigned_in_range 8 y) as R2; unfold bv_modulus in R1, R2; cbn in R1, R2;
apply (f_equal bv_unsigned) in E; rewrite ?unsigned_zxb in E; rewrite !Z_to_bv_unsigned in E; unfold bv_wrap, bv_modulus in E; cbn [Z.of_N Z.pow_pos Pos.mul] in E;
Z.div_mod_to_equations; lia
| exfalso; apply K; rewrite EX, EY in E; apply app_inv_head in E; inversion E; subst; reflexivity ]
| _ =>

assert (Exy : x = y) by (apply bv_eq; exact K); subst y;
zstep; zstep; zstep; zstep; if_cases K2; zify_cond K2;
[
first
[ destruct rest as [|x2 rest']; [exfalso; cbn [length] in K2; rewrite ?unsigned_lit in K2 by lia; lia|];
replace (Z.of_nat (length (x :: x2 :: rest')) + -1) with (Z.of_nat (length (x2 :: rest'))) by (cbn [length]; lia);
replace (P + Z.of_nat (length done) + 1) with (P + Z.of_nat (length (done ++ [x]))) by (rewrite length_app; cbn [length]; lia);
replace (Q + Z.of_nat (length done) + 1) with (Q + Z.of_nat (length (done ++ [x]))) by (rewrite length_app; cbn [length]; lia);
apply (IH (done ++ [x]) resty); [rewrite EX, <- app_assoc; reflexivity| rewrite EY, <- app_assoc; reflexivity| discriminate]
| destruct rest as [|x2 rest']; [| exfalso; cbn [length] in K2; rewrite ?unsigned_lit in K2 by lia; lia];
destruct resty as [|y2 resty']; [| cbn in LR; lia];
zstep; zstep; apply evt_done; unfold memcmp_post; sf_eexists 15%nat; split; [reflexivity|];
split; intros _; [rewrite EX, EY; reflexivity| reflexivity] ]
| first
[ destruct rest as [|x2 rest']; [| exfalso; cbn [length] in K2; rewrite ?unsigned_lit in K2 by lia; lia];
destruct resty as [|y2 resty']; [| cbn in LR; lia];
zstep; zstep; apply evt_done; unfold memcmp_post; sf_eexists 15%nat; split; [reflexivity|];
split; intros _; [rewrite EX, EY; reflexivity| reflexivity]
| destruct rest as [|x2 rest']; [exfalso; cbn [length] in K2; rewrite ?unsigned_lit in K2 by lia; lia|];
replace (Z.of_nat (length (x :: x2 :: rest')) + -1) with (Z.of_nat (length (x2 :: rest'))) by (cbn [length]; lia);
replace (P + Z.of_nat (length done) + 1) with (P + Z.of_nat (length (done ++ [x]))) by (rewrite length_app; cbn [length]; lia);
replace (Q + Z.of_nat (length done) + 1) with (Q + Z.of_nat (length (done ++ [x]))) by (rewrite length_app; cbn [length]; lia);
apply (IH (done ++ [x]) resty); [rewrite EX, <- app_assoc; reflexivity| rewrite EY, <- app_assoc; reflexivity| discriminate] ] ]
end.
Qed.

#[using="HX HY LEN SMALL"] Lemma memcmp_spec : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
evt rsegs (memcmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc xs ys m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz P) (wz Q) (wz (Z.of_nat (length xs))) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_memcmp) fc None m (seg_rom rsegs)).
Proof.
intros. unfold A_memcmp, wz. pose proof (bytes_at_bound _ _ _ _ HX) as BX.
zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
-
destruct xs as [|x xs']; [| exfalso; cbn [length] in K; lia].
destruct ys; [| cbn in LEN; lia].
zstep. zstep. apply evt_done. unfold memcmp_post. sf_eexists 15%nat. split; [reflexivity|]. split; intros _; reflexivity.
- assert (NE : xs <> []) by (intros E; apply K; rewrite E; reflexivity).
replace P with (P + Z.of_nat (length (@nil byte))) by (cbn; lia). replace Q with (Q + Z.of_nat (length (@nil byte))) by (cbn; lia).
apply (memcmp_loop xs [] ys); [reflexivity| reflexivity| exact NE].
Qed.

#[using="HX HY LEN SMALL"] Lemma bcmp_spec : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
evt rsegs (memcmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc xs ys m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz P) (wz Q) (wz (Z.of_nat (length xs))) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_bcmp) fc None m (seg_rom rsegs)).
Proof. intros. unfold A_bcmp. zstep. apply memcmp_spec. Qed.
End Memcmp.

Lemma rw_cells_of_pristine : forall (m : word -> option byte) A cs,
rtables_pristine m -> cells_wf cs -> RTABLES_LO <= A -> A + Z.of_nat (cells_size cs) <= RTABLES_HI ->
rw_bytes_b rsegs A (cells_bytes cs) = true ->
rw_cells rsegs m A cs.
Proof.
intros m A cs TP WF LO HI RB.
pose proof (cells_bytes_length cs WF) as L.
apply (X0pw.rw_cells_recast rsegs m A [CB (length (cells_bytes cs)) (cells_bytes cs)] cs).
- apply (X0pw.rw_cells_image0 rsegs m A (cells_bytes cs)).
+ intros a Ha. apply TP. unfold RTABLES_LO, RTABLES_HI in *. lia.
+ exact RB.
+ unfold RTABLES_LO in LO. lia.
+ unfold RTABLES_HI in HI. lia.
- exact WF.
- cbn. rewrite app_nil_r. reflexivity.
- cbn. lia.
Qed.

Lemma mode_list_cells : forall m, rtables_pristine m ->
rw_cells rsegs m A_speex_mode_list [C8 (wz A_speex_nb_mode); C8 (wz A_speex_wb_mode); C8 (wz A_speex_uwb_mode)].
Proof. intros m TP. apply rw_cells_of_pristine; [exact TP| cbn; tauto| unfold RTABLES_LO, A_speex_mode_list; lia| unfold A_speex_mode_list, RTABLES_HI; cbn; lia| vm_compute; reflexivity]. Qed.

Lemma got_nb_mode_cell : forall m, rtables_pristine m -> rw_cells rsegs m GOT_speex_nb_mode [C8 (wz A_speex_nb_mode)].
Proof. intros m TP. apply rw_cells_of_pristine; [exact TP| cbn; tauto| unfold RTABLES_LO, GOT_speex_nb_mode; lia| unfold GOT_speex_nb_mode, RTABLES_HI; cbn; lia| vm_compute; reflexivity]. Qed.

Lemma got_stereo_handler_cell : forall m, rtables_pristine m -> rw_cells rsegs m GOT_stereo_handler [C8 (wz A_speex_std_stereo_request_handler)].
Proof. intros m TP. apply rw_cells_of_pristine; [exact TP| cbn; tauto| unfold RTABLES_LO, GOT_stereo_handler; lia| unfold GOT_stereo_handler, RTABLES_HI; cbn; lia| vm_compute; reflexivity]. Qed.

Definition mode_of_id (i : Z) : spx_mode := if i =? 0 then ModeNB else if i =? 1 then ModeWB else ModeUWB.

Definition lib_get_mode_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(i : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (mode_addr (mode_of_id i))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom rsegs).

Lemma speex_lib_get_mode_spec : forall (i : Z) ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
rtables_pristine m -> mem_inv rsegs m -> 0 <= i <= 2 ->
evt rsegs (lib_get_mode_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc i m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz i) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_lib_get_mode) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros TP MI Hi. unfold A_speex_lib_get_mode, wz.
pose proof (mode_list_cells m TP) as ML. unfold A_speex_mode_list in ML.
zstep. zstep. if_true_x.
assert (C : i = 0 \/ i = 1 \/ i = 2) by lia.
destruct C as [-> |[-> | ->]]; cbn [Z.mul Z.add Z.shiftl Pos.mul Pos.add];
(zstep; zstep; zstep; zstep; zstep; if_false_x; zstep; zstep; zstep; zstep; apply evt_done; unfold lib_get_mode_post, mode_of_id; cbn [Z.eqb Pos.eqb]; sf_eexists 14%nat; reflexivity).
Qed.
