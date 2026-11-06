(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1ho X1hm X1ev X1ex X1ey X1ez X1f0.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Plain.M.loaded_segments.

Lemma sub_shift2 : forall base x,
Z_to_bv 64 (base - (Z.shiftl (x mod 18446744073709551616) 2) mod 18446744073709551616) = Z_to_bv 64 (base - 4 * x).
Proof.
intros base x. apply Z_to_bv_eqm. change (2^64) with 18446744073709551616.
rewrite Zminus_mod_idemp_r. rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
rewrite Zminus_mod, Zmult_mod_idemp_l, <- Zminus_mod. f_equal. lia.
Qed.

Lemma swrap32_sub_mod64 : forall a x, bv_swrap 32 (a - x mod 18446744073709551616) = bv_swrap 32 (a - x).
Proof.
intros a x. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 / 2)%Z with 2147483648%Z. f_equal.
rewrite (Z.mod_eq x 18446744073709551616) by lia.
replace (a - (x - 18446744073709551616 * (x / 18446744073709551616)) + 2147483648)
with ((a - x + 2147483648) + (4294967296 * (x / 18446744073709551616)) * 4294967296) by lia.
rewrite Z_mod_plus_full. reflexivity.
Qed.
Lemma row_off : forall x, 0 <= x <= 2 ->
Z.shiftr (Z.shiftl (x mod 18446744073709551616) 32 mod 18446744073709551616) 27
- Z.shiftr (Z.shiftl (x mod 18446744073709551616) 32 mod 18446744073709551616) 30 = 28 * x.
Proof. intros x Hx. assert (x = 0 \/ x = 1 \/ x = 2) as [->|[->| ->]] by lia; reflexivity. Qed.

Definition A_interp_pitch : Z := 0x2188c.
Definition IP_DEPTH : Z := 176.

Lemma interp_pitch_spec : forall (EB eoff p IP lo : Z) (eb ip : list word)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells rsegs m EB (f32 eb) -> length eb = 500%nat ->
0 <= eoff - p - 6 -> eoff - p <= 414 -> eoff + 80 <= 500 -> 0 <= eoff ->
rw_cells rsegs m IP (f32 ip) -> length ip = 80%nat ->
stk rsegs m lo (bv_unsigned sp) -> lo + IP_DEPTH <= bv_unsigned sp -> NB_GLOBALS_TOP <= lo -> bv_unsigned sp < 2^63 ->
NB_GLOBALS_TOP <= IP ->
apart EB 2000 lo (bv_unsigned sp - lo) -> apart IP 320 lo (bv_unsigned sp - lo) -> apart IP 320 EB 2000 ->
a0 = Z_to_bv 64 (EB + 4 * eoff) -> a1 = Z_to_bv 64 IP -> a2 = Z_to_bv 64 p ->
mem_inv rsegs m -> frm0 fc ->
evt rsegs (ip_post IP lo m ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_interp_pitch) fc None m (seg_rom rsegs)).
Proof.
intros EB eoff p IP lo eb ip. intros until m. intros XEB LEB R1 R2 R3 R4 XIP LIP ST LOW GLO SP63 GIP AEB AIP AIE -> -> -> MI FRM.
pose proof AEB as AEB'. pose proof AIP as AIP'. pose proof AIE as AIE'. unfold apart in AEB', AIP', AIE'.
unfold IP_DEPTH in LOW. pose proof GLO as GLO'. unfold NB_GLOBALS_TOP in GLO'. pose proof GIP as GIP'. unfold NB_GLOBALS_TOP in GIP'.
unfold A_interp_pitch.
pose proof (rw_cells_bound _ _ _ _ XEB) as BEB; rewrite cells_size_f32, LEB in BEB.
pose proof (rw_cells_bound _ _ _ _ XIP) as BIP; rewrite cells_size_f32, LIP in BIP.
pose proof (munch_refl [(lo, bv_unsigned sp); (IP, IP + 320)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
zstep. carve_frame 56%nat ST.
destruct (rw_cells_CB_C8s rsegs _ _ 7%nat _ FR) as (fw7 & Lfw & FR'); clear FR.
destruct fw7 as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 [|? ?]]]]]]]]; cbn in Lfw; try lia. cbn [map] in FR'. rename FR' into FR.
carve_frame 28%nat ST. rename FR0 into Q3.
carve_frame 28%nat ST. rename FR0 into Q2.
carve_frame 28%nat ST. rename FR0 into Q1.
carve_frame 28%nat ST. rename FR0 into Q0.
carve_frame 8%nat ST. rename FR0 into PAD.
do 7 zstep. do 4 zstep. do 2 zstep. rewrite sub_shift2. do 2 zstep.

pose (q := bv_unsigned sp + -176). assert (Hq : q + 176 = bv_unsigned sp) by (subst q; lia). clearbody q.
replace (bv_unsigned sp + -176) with q in * by lia.
replace (bv_unsigned sp + -168) with (q + 8) in * by lia.
replace (bv_unsigned sp + -140) with (q + 36) in * by lia.
replace (bv_unsigned sp + -112) with (q + 64) in * by lia.
replace (bv_unsigned sp + -84) with (q + 92) in * by lia.
replace (bv_unsigned sp + -56) with (q + 120) in * by lia.
rewrite <- Hq in LOW, SP63, AEB, AIP, AEB', AIP', MU, SPR.
destruct (rw_cells_CB_f32 rsegs _ _ 7%nat _ Q0) as (c0 & Lc0 & Q0'); clear Q0.
destruct c0 as [|y0 [|y1 [|y2 [|y3 [|y4 [|y5 [|y6 [|? ?]]]]]]]]; cbn in Lc0; try lia.
destruct (rw_cells_CB_f32 rsegs _ _ 7%nat _ Q1) as (r1 & Lr1 & RQ1); clear Q1.
destruct (rw_cells_CB_f32 rsegs _ _ 7%nat _ Q2) as (r2 & Lr2 & RQ2); clear Q2.
destruct (rw_cells_CB_f32 rsegs _ _ 7%nat _ Q3) as (r3 & Lr3 & RQ3); clear Q3.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut; [eapply (corr0_loop EB eoff p IP q lo eb mc gp tp s6 s7 s8 s9 s10 s11 LEB R1 R2 R3 R4) with (k := 6%nat) (done := []) (cw := y0) (rest := [y1; y2; y3; y4; y5; y6]);
[lia | lia | exact AEB | reflexivity | reflexivity | cbn [length]; lia | cbn [length]; lia | exact FRM | exact MI
| apply munch_refl | apply wmono_refl | exact XEB | apply rw_cells_nil; lia | exact Q0'] | clear FRM; post_call rsegs mc ] end.
rename MI0 into MI || idtac.
match goal with H : frm0 _, H2 : rw_cells _ _ (q + 8) (f32 ?c), H3 : length ?c = 7%nat |- _ =>
rename H into FRM; rename H2 into C0; rename H3 into Lc;
destruct c as [|c00 [|c01 [|c02 [|c03 [|c04 [|c05 [|c06 [|? ?]]]]]]]]; cbn in Lc; try lia; clear Lc end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
first [ pose proof (shift_filt_row mc 0 MI ltac:(lia)) as sfP_; sf_destruct 8%nat sfP_ as f00 f01 f02 f03 f04 f05 f06 RW0 | sf_fb; destruct (shift_filt_row mc 0 MI ltac:(lia)) as (f00 & f01 & f02 & f03 & f04 & f05 & f06 & RW0) ];
first [ pose proof (shift_filt_row mc 1 MI ltac:(lia)) as sfP_; sf_destruct 8%nat sfP_ as f10 f11 f12 f13 f14 f15 f16 RW1 | sf_fb; destruct (shift_filt_row mc 1 MI ltac:(lia)) as (f10 & f11 & f12 & f13 & f14 & f15 & f16 & RW1) ];
first [ pose proof (shift_filt_row mc 2 MI ltac:(lia)) as sfP_; sf_destruct 8%nat sfP_ as f20 f21 f22 f23 f24 f25 f26 RW2 | sf_fb; destruct (shift_filt_row mc 2 MI ltac:(lia)) as (f20 & f21 & f22 & f23 & f24 & f25 & f26 & RW2) ] end.
replace (SHIFT_FILT + 28 * 0) with 70492 in RW0 by reflexivity.
replace (SHIFT_FILT + 28 * 1) with 70520 in RW1 by reflexivity.
replace (SHIFT_FILT + 28 * 2) with 70548 in RW2 by reflexivity.
do 8 zstep.
Ltac row q i fq rq RQ RW :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with FRM : frm0 _, MI : mem_inv _ mc, C0 : rw_cells _ mc (q + 8) _ |- _ =>
eapply evt_cut; [eapply (filt_row q i fq rq) with (m := mc);
[lia | lia | lia | | exact FRM | exact MI | exact C0 | exact RQ | exact RW] | clear FRM RQ; post_call rsegs mc ];
[eassumption|];
rename MI0 into MI || idtac;
match goal with H : frm0 _, H2 : rw_cells _ _ rq (f32 ?c), H3 : length ?c = 7%nat |- _ =>
rename H into FRM; rename H2 into RQ end
end end.
row q 0 70492 (q + 36) RQ1 RW0.
do 2 zstep. if_true_x. replace (0 + 1) with 1 by lia.
row q 1 70520 (q + 64) RQ2 RW1.
do 2 zstep. if_true_x. replace (1 + 1) with 2 by lia.
row q 2 70548 (q + 92) RQ3 RW2.
do 2 zstep. if_false_x. clear RW0 RW1 RW2.
chunk_cat C0 RQ1. chunk_cat C0 RQ2. chunk_cat C0 RQ3. rewrite <- !f32_app in C0.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut; [eapply (amax q mc); [ | exact FRM | exact MI | exact C0] | ] end.
{ rewrite !length_app. cbn [length]. lia. }
clear FRM. intros ms' PO; first [ sf_destruct 14%nat PO as mi mj t0' t1' t2' a6' a7' t3' G2 fc2 -> FRM Hmi Hmj | sf_fb; destruct PO as (mi & mj & t0' & t1' & t2' & a6' & a7' & t3' & G2 & fc2 & -> & FRM & Hmi & Hmj) ].
do 16 zstep.
rewrite swrap32_sub_mod64, (swrap32_small (mj - p)), swrap32_mod64_add by lia.
destruct ip as [|i0 iprest]; [cbn in LIP; lia|]. cbn [length] in LIP.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (rw_cells_nil rsegs mc IP ltac:(lia)) as XD end.
destruct (Z.eq_dec mi 0) as [Hmi0|Hmi1].
- lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (floopB EB eoff p IP q lo eb) with (m0 := m) (ra := ra) (s0 := s0) (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (s5 := s5)
(mi := mi) (mj := mj) (k := 79%nat) (done := []) (m := mc) (i := 0) end.
all: try eassumption.
all: try (rewrite ?length_app; cbn [length]; lia).
all: lia.
- rewrite (row_off (mi + -1)) by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
first [ pose proof (shift_filt_row mc (mi - 1) MI ltac:(lia)) as sfP_; sf_destruct 8%nat sfP_ as g0 g1 g2 g3 g4 g5 g6 ROW | sf_fb; destruct (shift_filt_row mc (mi - 1) MI ltac:(lia)) as (g0 & g1 & g2 & g3 & g4 & g5 & g6 & ROW) ];
replace (SHIFT_FILT + 28 * (mi - 1)) with (70492 + 28 * (mi + -1)) in ROW by (unfold SHIFT_FILT; lia);
eapply (floopA EB eoff p IP q lo eb) with (m0 := m) (ra := ra) (s0 := s0) (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (s5 := s5)
(mi := mi) (mj := mj) (k := 79%nat) (done := []) (m := mc) (i := 0) end.
all: try eassumption.
all: try (rewrite ?length_app; cbn [length]; lia).
all: try (unfold NB_GLOBALS_TOP; lia).
all: lia.
Qed.
