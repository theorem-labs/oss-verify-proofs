(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1df X1ck X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X0ae X0ah X071 X06v.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X0yr X110 X112 X0xn.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X112 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xn.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= first [ hsh_store | mem_after_store_fast ].
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Notation mem := (word -> option byte).
Definition e_stack_malloc_h (k : nat) : Z := 0x51c58.
Definition PC_set_shadow_f8 : Z := 0x6a2cc.
Definition PC_set_shadow_00 : Z := 0x6a1ac.
Definition PC_asan_memcpy : Z := 0x66400.
Definition PC_stack_free_8 : Z := 0x51dd4.
Definition A_speex_bits_init_h : Z := 0x97774.
Definition A_STEREO_INIT : Z := 0x232a0.

Definition h_saves (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
[C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma hf_f0a : forall (usp lo : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
stk bsegs m lo usp -> lo <= usp - 368 -> usp < 2^63 -> usp mod 16 = 0 -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (j1 : list byte),
ms = MS (mkR ra (Z_to_bv 64 (usp + -352)) gp tp t0 t1 t2 (Z_to_bv 64 usp) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x96794) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -352, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -352)
/\ rw_cells bsegs m1 (usp + -352) ([C8 (Z_to_bv 64 0); CB 240 j1] ++ h_saves s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_LLVMFuzzerTestOneInput) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ST0 LO SPH SP16 MI.
unfold A_LLVMFuzzerTestOneInput, h_saves.
pose proof ST0 as (STa & STb & _).
pose proof (munch_refl [(usp + -352, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
carve_frame 352%nat ST0.
apply (rw_cells_split_CB bsegs _ _ [] 352 _ [] [8; 240; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
cbn [mk_CB_cells app] in FR.
ato 0x96794.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST0| exact FR].
Qed.

Lemma land_m32 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551584 = x - x mod 32.
Proof.
intros x Hx. change 18446744073709551584 with (Z.ldiff (Z.ones 64) (Z.ones 5)).
rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
change (2^5) with 32. Z.div_mod_to_equations. lia.
Qed.

Lemma h_rw_cells_to_CB : forall segs (m : mem) A cs, rw_cells segs m A cs -> rw_cells segs m A [CB (cells_size cs) (cells_bytes cs)].
Proof.
intros segs m A cs H. apply (rw_cells_recast segs m A cs); [exact H| | cbn [cells_bytes cbytes]; apply app_nil_r].
split; [| exact I]. destruct H as [[Hwf _] _]. exact (cells_bytes_length cs Hwf).
Qed.

Lemma h_rechunk : forall (m : mem) (lo usp S1 : Z) (j1 : list byte) (sv : list cell),
S1 = Z.land (usp + -352) 18446744073709551584 -> 368 <= usp < 2^63 -> usp mod 16 = 0 -> lo <= usp - 368 ->
stk bsegs m lo (usp + -352) -> rw_cells bsegs m (usp + -352) ([C8 (Z_to_bv 64 0); CB 240 j1] ++ sv) -> cells_size sv = 104%nat ->
(S1 mod 32 = 0 /\ usp - 368 <= S1 <= usp - 352) /\
exists w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 (jg : list byte), stk bsegs m lo S1 /\ rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240)
/\ rw_cells bsegs m (S1 + 248) [CB (Z.to_nat (usp - 352 - S1)) jg] /\ rw_cells bsegs m (usp + -104) sv.
Proof.
intros m lo usp S1 j1 sv ES1 UR U16 LO ST FR SV.
rewrite land_m32 in ES1 by lia.
assert (SF : S1 mod 32 = 0 /\ usp - 368 <= S1 <= usp - 352) by (subst S1; Z.div_mod_to_equations; lia).
split; [exact SF|]. destruct SF as (S32 & SR).
apply rw_cells_app in FR. destruct FR as (FR1 & FR2). cbn [cells_size csize Nat.add] in FR2.
replace (usp + -352 + Z.of_nat 248) with (usp + -104) in FR2 by lia.
apply h_rw_cells_to_CB in FR1. cbn [cells_size csize Nat.add cells_bytes cbytes] in FR1.
set (d := Z.to_nat (usp - 352 - S1)).
destruct (stk_carve bsegs m lo (usp + -352) d ST ltac:(unfold d; lia)) as (ST1 & (jd & JD)).
replace (usp + -352 - Z.of_nat d) with S1 in ST1, JD by (unfold d; lia).
assert (J : rw_cells bsegs m S1 ([CB d jd] ++ [CB 248 (le8 (Z_to_bv 64 0) ++ j1 ++ [])])).
{ apply rw_cells_app. split; [exact JD|]. cbn [cells_size csize Nat.add]. replace (S1 + Z.of_nat (d + 0)) with (usp + -352) by (unfold d; lia). exact FR1. }
apply h_rw_cells_to_CB in J. cbn [cells_size csize Nat.add cells_bytes cbytes app] in J.
apply (rw_cells_split_CB bsegs _ _ [] _ _ [] [248; d]%nat) in J; [| cbn; lia].
cbn [mk_CB_cells app] in J. apply (proj1 (rw_cells_app bsegs m S1 [CB 248 _] [CB d _])) in J. destruct J as (J1 & J2). cbn [cells_size csize Nat.add] in J2.
destruct (hsp_of_CB m S1 _ J1) as (w0 & w8 & w16 & w24 & w32 & w40 & w48 & w56 & w64 & w72 & w80 & w88 & w96 & w104 & w112 & w120 & w128 & w136 & w144 & w152 & w160 & w168 & w176 & w184 & w192 & w200 & w208 & w216 & w224 & w232 & w240 & HS).
exists w0, w8, w16, w24, w32, w40, w48, w56, w64, w72, w80, w88, w96, w104, w112, w120, w128, w136, w144, w152, w160, w168, w176, w184, w192, w200, w208, w216, w224, w232, w240. eexists.
split; [exact ST1|]. split; [exact HS|]. split; [| exact FR2].
replace (S1 + 248) with (S1 + Z.of_nat (248 + 0)) by lia. exact J2.
Qed.

Lemma hf_f0b : forall (usp S1 : Z) (ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 F fc (m : mem),
S1 = Z.land (usp + -352) 18446744073709551584 -> 368 <= usp < 2^63 -> IMG_TOP_B <= S1 ->
rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240) -> client_constsB m -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR (Z_to_bv 64 RA_h_smalloc) (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1)
(Z_to_bv 64 HF_SIZE) (Z_to_bv 64 gB_shadow_memory_dynamic_address) (Z_to_bv 64 1) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 (Z_to_bv 64 SHB) a0 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_stack_malloc_h 8)) fc None m1 (seg_rom bsegs)
/\ munch [(S1, S1 + 248)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 a1 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240))
(MS (mkR ra (Z_to_bv 64 (usp + -352)) gp tp t0 t1 t2 (Z_to_bv 64 usp) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x96794) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ES1 UR IMS SP CC MI. unfold hsp in *. unfold IMG_TOP_B in IMS.
destruct CC as (G1 & G2 & G3 & G4).
unfold RA_h_smalloc, HF_SIZE, e_stack_malloc_h, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
pose proof (munch_refl [(S1, S1 + 248)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
astep. rewrite <- ES1.
ato 0x51c58.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact SP].
Qed.

Lemma hf_f1 : forall (usp S1 F sf : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240
(jf : list byte) Fr fc (m : mem),
0 < F -> F mod 64 = 0 -> F + 16384 <= S1 -> S1 + 248 <= usp -> usp < 2^63 -> sf = Z.shiftr F 3 + SHB ->
rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240) -> rw_cells bsegs m F [CB 24 jf] -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR (Z_to_bv 64 RA_h_smalloc) (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1)
(Z_to_bv 64 8384) (Z_to_bv 64 0x41b58ab3) (Z_to_bv 64 HF_DESC) (Z_to_bv 64 A_LLVMFuzzerTestOneInput) (Z_to_bv 64 (-15)) a5 a6 a7
(Z_to_bv 64 (-14)) (Z_to_bv 64 sf) (Z_to_bv 64 F) (Z_to_bv 64 F) (Z_to_bv 64 (-8)) s7 (Z_to_bv 64 SHB) s9 (Z_to_bv 64 (F + 8384)) s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0x9684c) fc None m1 (seg_rom bsegs)
/\ munch [(S1, S1 + 248); (F, F + 24)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 (Z_to_bv 64 F))
/\ rw_cells bsegs m1 F [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 HF_DESC); C8 (Z_to_bv 64 A_LLVMFuzzerTestOneInput)])
(MS (mkR (Z_to_bv 64 RA_h_smalloc) (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1) (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 (Z_to_bv 64 SHB) s9 s10 s11 t3 t4 t5 t6)
Fr (ret_pc (Z_to_bv 64 RA_h_smalloc)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros F0 F64 FS1 SU SPH Esf SP FB MI. unfold hsp in *.
unfold RA_h_smalloc, HF_DESC, A_LLVMFuzzerTestOneInput in *.
replace (ret_pc (Z_to_bv 64 0x967cc)) with (Z_to_bv 64 0x967cc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(S1, S1 + 248); (F, F + 24)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [8; 8; 8]%nat) in FB; [| reflexivity]. cbn [mk_CB_cells app] in FB.
ato 0x967dc. astep. sh_if.
ato 0x9684c.
rewrite <- Esf.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact SP| exact FB].
Qed.

Lemma hf_p1 : forall (sf F : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 : word)
(js : list byte) Fr fc (m : mem),
rw_cells bsegs m sf [CB 16 js] -> mem_inv bsegs m -> 0 <= sf < 2^62 -> 0 <= F < 2^62 ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR (Z_to_bv 64 0x968a0) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sf + 16)) (Z_to_bv 64 1000) a2 a3 (Z_to_bv 64 (-15)) a5 a6 a7
(Z_to_bv 64 (-14)) (Z_to_bv 64 sf) s4 s5 (Z_to_bv 64 (-8)) (Z_to_bv 64 (sf + 16)) s8 s9 (Z_to_bv 64 (F + 8384)) (Z_to_bv 64 (F + 8384 + 784)) t3 t4 t5 t6)
Fr (Z_to_bv 64 PC_set_shadow_f8) fc None m1 (seg_rom bsegs)
/\ munch [(sf, sf + 16)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ rw_cells bsegs m1 sf [CB 16 HSH_P1])
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 (-15)) a5 a6 a7
(Z_to_bv 64 (-14)) (Z_to_bv 64 sf) s4 s5 (Z_to_bv 64 (-8)) s7 s8 s9 (Z_to_bv 64 (F + 8384)) s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0x9684c) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SH MI SFR FR.
unfold PC_set_shadow_f8.
pose proof (munch_refl [(sf, sf + 16)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
hsh_start SH.
ato 0x6a2cc.
hsh_lit SH HSH_P1.
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact SH].
Qed.

Lemma hf_p2 : forall (sf F : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(js : list byte) Fr fc (m : mem),
ra = Z_to_bv 64 0x968a0 ->
rw_cells bsegs m (sf + 1016) [CB 144 js] -> mem_inv bsegs m -> 0 <= sf < 2^62 ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR (Z_to_bv 64 0x96af0) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sf + 16)) (Z_to_bv 64 1000) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (-14)) (Z_to_bv 64 sf) s4 s5 (Z_to_bv 64 (-8)) (Z_to_bv 64 (sf + 16)) s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 PC_set_shadow_00) fc None m1 (seg_rom bsegs)
/\ munch [(sf + 1016, sf + 1160)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ rw_cells bsegs m1 (sf + 1016) [CB 144 HSH_P2])
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (-14)) (Z_to_bv 64 sf) s4 s5 (Z_to_bv 64 (-8)) (Z_to_bv 64 (sf + 16)) s8 s9 s10 s11 t3 t4 t5 t6)
Fr (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> SH MI SFR.
unfold PC_set_shadow_00.
replace (ret_pc (Z_to_bv 64 0x968a0)) with (Z_to_bv 64 0x968a0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(sf + 1016, sf + 1160)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
hsh_start SH.
ato 0x6a1ac.
hsh_lit SH HSH_P2.
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact SH].
Qed.

Definition WS_P3R : list (Z * list byte) :=
[(132, [Z_to_bv 8 0]); (131, [Z_to_bv 8 0]); (130, [Z_to_bv 8 0]); (120, [Z_to_bv 8 0]); (119, [Z_to_bv 8 0]); (118, [Z_to_bv 8 0]);
(113, [Z_to_bv 8 0]); (112, [Z_to_bv 8 0]); (111, [Z_to_bv 8 0]); (110, [Z_to_bv 8 0]); (117, [Z_to_bv 8 0]); (116, [Z_to_bv 8 0]);
(115, [Z_to_bv 8 0]); (114, [Z_to_bv 8 0]); (105, [Z_to_bv 8 0]); (104, [Z_to_bv 8 0]); (103, [Z_to_bv 8 0]); (102, [Z_to_bv 8 0]);
(109, [Z_to_bv 8 0]); (108, [Z_to_bv 8 0]); (107, [Z_to_bv 8 0]); (106, [Z_to_bv 8 0]); (97, [Z_to_bv 8 0]); (96, [Z_to_bv 8 0]);
(95, [Z_to_bv 8 0]); (94, [Z_to_bv 8 0]); (101, [Z_to_bv 8 0]); (100, [Z_to_bv 8 0]); (99, [Z_to_bv 8 0]); (98, [Z_to_bv 8 0]); (89, [Z_to_bv 8 0]);
(88, [Z_to_bv 8 0]); (87, [Z_to_bv 8 0]); (86, [Z_to_bv 8 0]); (93, [Z_to_bv 8 0]); (92, [Z_to_bv 8 0]); (91, [Z_to_bv 8 0]); (90, [Z_to_bv 8 0]);
(81, [Z_to_bv 8 0]); (80, [Z_to_bv 8 0]); (79, [Z_to_bv 8 0]); (78, [Z_to_bv 8 0]); (85, [Z_to_bv 8 0]); (84, [Z_to_bv 8 0]); (83, [Z_to_bv 8 0]);
(82, [Z_to_bv 8 0]); (73, [Z_to_bv 8 0]); (72, [Z_to_bv 8 0]); (71, [Z_to_bv 8 0]); (70, [Z_to_bv 8 0]); (77, [Z_to_bv 8 0]); (76, [Z_to_bv 8 0]);
(75, [Z_to_bv 8 0]); (74, [Z_to_bv 8 0]); (65, [Z_to_bv 8 0]); (64, [Z_to_bv 8 0]); (63, [Z_to_bv 8 0]); (62, [Z_to_bv 8 0]); (61, [Z_to_bv 8 0]);
(60, [Z_to_bv 8 0]); (55, [Z_to_bv 8 0]); (54, [Z_to_bv 8 0]); (53, [Z_to_bv 8 0]); (52, [Z_to_bv 8 0]); (47, [Z_to_bv 8 0]); (46, [Z_to_bv 8 0]);
(45, [Z_to_bv 8 0]); (44, [Z_to_bv 8 0]); (39, [Z_to_bv 8 0]); (38, [Z_to_bv 8 0]); (37, [Z_to_bv 8 0]); (36, [Z_to_bv 8 0]); (35, [Z_to_bv 8 0]);
(34, [Z_to_bv 8 0])].

Lemma hf_p3r : forall (sf : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (m : mem) (c0 : list byte),
rw_cells bsegs m (sf + 1016) [CB 144 c0] -> mem_inv bsegs m -> 0 <= sf -> sf < 2^62 ->
evt bsegs (fun ms => exists m1 : mem,
ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 sf) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x96c24) fc None m1 (seg_rom bsegs)
/\ munch [(sf + 1016, sf + 1160)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ rw_cells bsegs m1 (sf + 1016) [CB 144 (upd_all c0 (rev (map zw WS_P3R)))])
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 sf) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x96afc) fc None m (seg_rom bsegs)).
Proof.
intros until c0. intros SH MI SF0 SF1.
pose proof (munch_refl [(sf + 1016, sf + 1160)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
hsh_start SH.
ato 0x96c24.
rewrite (hsh_hist_eq _ _ _ HH) in SH.
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact SH].
Qed.

Lemma hf_p3 : forall (usp S1 sf F : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s8 s9 s11 t3 t4 t5 t6 : word) w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 (jfs : list byte) (size : word) Fr fc (m : mem),
ra = Z_to_bv 64 0x96af0 ->
rw_cells bsegs m (sf + 1016) [CB 144 HSH_P2] -> rw_cells bsegs m (F + 8384) [CB 4 jfs] -> rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 size w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 (Z_to_bv 64 F)) ->
mem_inv bsegs m -> 0 <= sf -> 0 <= F -> S1 < 2^62 -> sf + 2048 <= S1 -> F + 16384 <= S1 -> (F + 16384 <= sf \/ sf + 2048 <= F) ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR (Z_to_bv 64 0x96c3c) (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1)
(Z_to_bv 64 (F + 9168)) (Z_to_bv 64 A_STEREO_INIT) (Z_to_bv 64 24) a3 a4 a5 a6 a7
(Z_to_bv 64 4) (Z_to_bv 64 sf) (Z_to_bv 64 F) (Z_to_bv 64 F) (Z_to_bv 64 (-8)) (Z_to_bv 64 (sf + 16)) s8 s9 (Z_to_bv 64 (F + 8384)) (Z_to_bv 64 (F + 9168)) t3 t4 t5 t6)
Fr (Z_to_bv 64 PC_asan_memcpy) fc None m1 (seg_rom bsegs)
/\ munch [(sf + 1016, sf + 1160); (F + 8384, F + 8388); (S1, S1 + 248)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 (sf + 1016) [CB 144 HSH_P3] /\ rw_cells bsegs m1 (F + 8384) [C4 (Z_to_bv 64 0)]
/\ rw_cells bsegs m1 S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 size w96 w104 w112 w120 (Z_to_bv 64 (F + 9168)) w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 (Z_to_bv 64 F)))
(MS (mkR ra (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 sf) (Z_to_bv 64 F) (Z_to_bv 64 F) (Z_to_bv 64 (-8)) (Z_to_bv 64 (sf + 16)) s8 s9 (Z_to_bv 64 (F + 8384)) (Z_to_bv 64 (F + 9168)) t3 t4 t5 t6)
Fr (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> SH FS SP MI SF0 F0 S1R SFS FS1 FSF. unfold hsp in *.
unfold PC_asan_memcpy, A_STEREO_INIT.
replace (ret_pc (Z_to_bv 64 0x96af0)) with (Z_to_bv 64 0x96af0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(sf + 1016, sf + 1160); (F + 8384, F + 8388); (S1, S1 + 248)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
hsh_start SH.
ato 0x96afc.
rewrite (hsh_hist_eq _ _ _ HH) in SH. clear HH LB.
call (hf_p3r sf); [ exact SH | exact MI | lia | lia | ].
ato 0x66400.
assert (E3 : upd_all (upd_all HSH_P2 (rev (map zw [(32, [Z_to_bv 8 4])]))) (rev (map zw WS_P3R)) = HSH_P3)
by (unfold HSH_P2, HSH_P3, WS_P3R; cbv [upd_all fold_left upd1 upd_bytes firstn skipn app repeat length fst snd Nat.add Nat.sub rev map zw Z.to_nat Pos.to_nat Pos.iter_op zruns]; reflexivity).
rewrite E3 in POST.
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [exact POST|]. split; [exact FS| exact SP].
Qed.

Lemma hf_p4 : forall (usp S1 sf F size : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s9 s11 t3 t4 t5 t6 : word) w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w96 w104 w112 w120 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 (jr joy : list byte) Fr fc (m : mem),
ra = Z_to_bv 64 0x96c3c -> 0 <= size <= 4096 ->
rw_cells bsegs m (sf + 1016) [CB 144 HSH_P3] -> rw_cells bsegs m (F + 9232) [CB 4 jr] -> rw_cells bsegs m (F + 8480) [CB 32 joy] ->
rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 (Z_to_bv 64 size) w96 w104 w112 w120 (Z_to_bv 64 (F + 9168)) w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 (Z_to_bv 64 F)) ->
mem_inv bsegs m -> 0 <= sf -> 0 < F -> S1 < 2^62 -> sf + 2048 <= S1 -> F + 16384 <= S1 -> (F + 16384 <= sf \/ sf + 2048 <= F) ->
evt bsegs (fun ms => exists (m1 : mem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
ms = MS (mkR (Z_to_bv 64 0x96cbc) (Z_to_bv 64 S1) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 S1)
(Z_to_bv 64 (F + 8400)) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (F + 8400)) (Z_to_bv 64 sf) (Z_to_bv 64 F) (Z_to_bv 64 F) (Z_to_bv 64 (-8)) (Z_to_bv 64 (F + 8688)) (Z_to_bv 64 SHB)
s9 (Z_to_bv 64 (F + 8384)) (Z_to_bv 64 (F + 48)) t3' t4' t5' t6')
Fr (Z_to_bv 64 A_speex_bits_init_h) fc None m1 (seg_rom bsegs)
/\ munch [(sf + 1016, sf + 1160); (F + 9232, F + 9236); (F + 8480, F + 8512); (S1, S1 + 248)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 (sf + 1016) [CB 144 HSH_T] /\ rw_cells bsegs m1 (F + 9232) [C4 (Z_to_bv 64 0)]
/\ sync_rep m1 (F + 8480) 0 ogg_sync_init []
/\ rw_cells bsegs m1 S1 (hsp (Z_to_bv 64 (sf + 16)) (Z_to_bv 64 F) (Z_to_bv 64 F) w24 w32 w40 w48 w56 (Z_to_bv 64 (F + 9232)) w72 w80 (Z_to_bv 64 size) (Z_to_bv 64 (F + 32)) w104 (Z_to_bv 64 (F + 8480)) (Z_to_bv 64 SHB) (Z_to_bv 64 (F + 9168)) w136 (Z_to_bv 64 (F + 8544)) w152 (Z_to_bv 64 (F + 8608)) w168 (Z_to_bv 64 (F + 9248)) (Z_to_bv 64 (F + 8384)) (Z_to_bv 64 (F + 8400)) w200 (Z_to_bv 64 (F + 128)) w216 w224 w232 (Z_to_bv 64 F)))
(MS (mkR ra (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 4) (Z_to_bv 64 sf) (Z_to_bv 64 F) (Z_to_bv 64 F) (Z_to_bv 64 (-8)) (Z_to_bv 64 (sf + 16)) (Z_to_bv 64 SHB) s9 (Z_to_bv 64 (F + 8384)) s11 t3 t4 t5 t6)
Fr (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> SZ SH RT OY SP MI SF0 F0 S1R SFS FS1 FSF. unfold hsp in *.
unfold A_speex_bits_init_h.
replace (ret_pc (Z_to_bv 64 0x96c3c)) with (Z_to_bv 64 0x96c3c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(sf + 1016, sf + 1160); (F + 9232, F + 9236); (F + 8480, F + 8512); (S1, S1 + 248)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
hsh_start SH.
ato 0x96c50. astep. sh_if.
hsh_lit0 SH HSH_T ltac:(unfold HSH_P3, HSH_T).
ato 0x96cac. astep.
call (ogg_sync_init_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc _ (F + 8480) joy); [ unfold wz; f_equal; lia | lia | exact OY | exact MI | ].

destruct POST as (SYc & SYf & SYd & SYj). simpl in SYd. unfold sync_cells in SYc. simpl in SYc.
ato 0x97774.
apply evt_done. do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [exact SH|]. split; [exact RT|]. split; [unfold sync_rep; split; [exact SYc|]; split; [exact SYf|]; split; [exact SYd| exact SYj]| exact SP].
Qed.

Lemma hf_p4b : forall (usp S1 sf F size : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s9 s11 t3 t4 t5 t6 : word) w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w96 w104 w112 w120 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 (jr : list byte) Fr fc (m : mem),
ra = Z_to_bv 64 0x96c3c -> 4096 < size < 2^63 ->
rw_cells bsegs m (sf + 1016) [CB 144 HSH_P3] -> rw_cells bsegs m (F + 9232) [CB 4 jr] ->
rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 (Z_to_bv 64 size) w96 w104 w112 w120 (Z_to_bv 64 (F + 9168)) w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 (Z_to_bv 64 F)) ->
mem_inv bsegs m -> 0 <= sf -> 0 < F -> sf + 2048 <= S1 -> S1 < 2^62 -> (F + 16384 <= sf \/ sf + 2048 <= F) -> F + 16384 <= S1 ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR ra (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1) (Z_to_bv 64 4096) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 4) (Z_to_bv 64 sf) (Z_to_bv 64 F) (Z_to_bv 64 F) (Z_to_bv 64 (-8)) (Z_to_bv 64 (sf + 16)) (Z_to_bv 64 SHB) s9 (Z_to_bv 64 (F + 8384)) s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_EP) fc None m1 (seg_rom bsegs)
/\ munch [(sf + 1016, sf + 1160); (F + 9232, F + 9236)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 (sf + 1016) [CB 144 HSH_T] /\ rw_cells bsegs m1 (F + 9232) [C4 (Z_to_bv 64 0)]
/\ rw_cells bsegs m1 S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 (Z_to_bv 64 size) w96 w104 w112 w120 (Z_to_bv 64 (F + 9168)) w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 (Z_to_bv 64 F)))
(MS (mkR ra (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 4) (Z_to_bv 64 sf) (Z_to_bv 64 F) (Z_to_bv 64 F) (Z_to_bv 64 (-8)) (Z_to_bv 64 (sf + 16)) (Z_to_bv 64 SHB) s9 (Z_to_bv 64 (F + 8384)) s11 t3 t4 t5 t6)
Fr (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> SZ SH RT SP MI SF0 F0 SFS S1R FSF FS1. unfold hsp in *. unfold A_EP.
replace (ret_pc (Z_to_bv 64 0x96c3c)) with (Z_to_bv 64 0x96c3c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(sf + 1016, sf + 1160); (F + 9232, F + 9236)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
hsh_start SH.
ato 0x96c50. astep. sh_if.
hsh_lit0 SH HSH_T ltac:(unfold HSH_P3, HSH_T).
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
split; [exact SH|]. split; [exact RT| exact SP].
Qed.

Lemma hf_p5 : forall (usp S1 sf F size : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s8 s10 t3 t4 t5 t6 : word) w24 w32 w40 w48 w56 w72 w80 w104 w136 w152 w168 w200 w216 w224 w232 (data : word) Fr fc (m : mem),
ra = Z_to_bv 64 0x96cbc -> rw_cells bsegs m S1 (hsp (Z_to_bv 64 (sf + 16)) (Z_to_bv 64 F) (Z_to_bv 64 F) w24 w32 w40 w48 w56 (Z_to_bv 64 (F + 9232)) w72 w80 (Z_to_bv 64 size) (Z_to_bv 64 (F + 32)) w104 (Z_to_bv 64 (F + 8480)) (Z_to_bv 64 SHB) (Z_to_bv 64 (F + 9168)) w136 (Z_to_bv 64 (F + 8544)) w152 (Z_to_bv 64 (F + 8608)) w168 (Z_to_bv 64 (F + 9248)) (Z_to_bv 64 (F + 8384)) (Z_to_bv 64 (F + 8400)) w200 (Z_to_bv 64 (F + 128)) w216 w224 w232 (Z_to_bv 64 F)) -> mem_inv bsegs m -> S1 < 2^62 ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR ra (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1) (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 sf) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (-8)) (Z_to_bv 64 (F + 8688)) (Z_to_bv 64 size)
data (Z_to_bv 64 0) (Z_to_bv 64 (-1)) t3 t4 t5 t6)
Fr (Z_to_bv 64 A_CH) fc None m1 (seg_rom bsegs)
/\ munch [(S1, S1 + 248)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 S1 (hsp (Z_to_bv 64 (sf + 16)) (Z_to_bv 64 F) (Z_to_bv 64 F) data (Z_to_bv 64 (F + 64)) w40 w48 w56 (Z_to_bv 64 (F + 9232)) (Z_to_bv 64 (F + 48)) (Z_to_bv 64 0) (Z_to_bv 64 size) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 0) (Z_to_bv 64 (F + 8480)) (Z_to_bv 64 SHB) (Z_to_bv 64 (F + 9168)) (Z_to_bv 64 0) (Z_to_bv 64 (F + 8544)) (Z_to_bv 64 (F + 8688)) (Z_to_bv 64 (F + 8608)) (Z_to_bv 64 (-1)) (Z_to_bv 64 (F + 9248)) (Z_to_bv 64 (F + 8384)) (Z_to_bv 64 (F + 8400)) (Z_to_bv 64 2) (Z_to_bv 64 (F + 128)) (Z_to_bv 64 0) w224 w232 (Z_to_bv 64 F)))
(MS (mkR ra (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 sf) s4 s5 (Z_to_bv 64 (-8)) (Z_to_bv 64 (F + 8688)) s8 data s10 (Z_to_bv 64 (F + 48)) t3 t4 t5 t6)
Fr (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> SP MI S1R. unfold hsp in *. unfold A_CH.
replace (ret_pc (Z_to_bv 64 0x96cbc)) with (Z_to_bv 64 0x96cbc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(S1, S1 + 248)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
ato 0x96d04.
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact SP].
Qed.

Lemma hx_0 : forall (S1 sf F : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 Fr fc (m : mem),
s1 = Z_to_bv 64 S1 -> rw_cells bsegs m S1 (hsp (Z_to_bv 64 (sf + 16)) (Z_to_bv 64 F) (Z_to_bv 64 F) w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240) -> mem_inv bsegs m -> S1 < 2^62 ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 F) (Z_to_bv 64 F) s6 (Z_to_bv 64 (sf + 16)) s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_EP) fc None m1 (seg_rom bsegs)
/\ munch [] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 S1 (hsp (Z_to_bv 64 (sf + 16)) (Z_to_bv 64 F) (Z_to_bv 64 F) w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_XT) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> SP MI S1R. unfold hsp in *. unfold A_XT, A_EP.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
ato 0x974bc.
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact SP].
Qed.

Definition WS_XR : list (Z * list byte) :=
[(36, [Z_to_bv 8 (-8)]); (35, [Z_to_bv 8 (-8)]); (34, [Z_to_bv 8 (-8)]); (32, [Z_to_bv 8 (-8)]); (44, [Z_to_bv 8 (-8)]); (39, [Z_to_bv 8 (-8)]);
(38, [Z_to_bv 8 (-8)]); (37, [Z_to_bv 8 (-8)]); (52, [Z_to_bv 8 (-8)]); (47, [Z_to_bv 8 (-8)]); (46, [Z_to_bv 8 (-8)]); (45, [Z_to_bv 8 (-8)]);
(64, [Z_to_bv 8 (-8)]); (63, [Z_to_bv 8 (-8)]); (62, [Z_to_bv 8 (-8)]); (61, [Z_to_bv 8 (-8)]); (60, [Z_to_bv 8 (-8)]); (55, [Z_to_bv 8 (-8)]);
(54, [Z_to_bv 8 (-8)]); (53, [Z_to_bv 8 (-8)]); (120, [Z_to_bv 8 (-8)]); (119, [Z_to_bv 8 (-8)]); (118, [Z_to_bv 8 (-8)]); (117, [Z_to_bv 8 (-8)]);
(112, [Z_to_bv 8 (-8)]); (111, [Z_to_bv 8 (-8)]); (110, [Z_to_bv 8 (-8)]); (109, [Z_to_bv 8 (-8)]); (116, [Z_to_bv 8 (-8)]);
(115, [Z_to_bv 8 (-8)]); (114, [Z_to_bv 8 (-8)]); (113, [Z_to_bv 8 (-8)]); (104, [Z_to_bv 8 (-8)]); (103, [Z_to_bv 8 (-8)]);
(102, [Z_to_bv 8 (-8)]); (101, [Z_to_bv 8 (-8)]); (108, [Z_to_bv 8 (-8)]); (107, [Z_to_bv 8 (-8)]); (106, [Z_to_bv 8 (-8)]);
(105, [Z_to_bv 8 (-8)]); (96, [Z_to_bv 8 (-8)]); (95, [Z_to_bv 8 (-8)]); (94, [Z_to_bv 8 (-8)]); (93, [Z_to_bv 8 (-8)]); (100, [Z_to_bv 8 (-8)]);
(99, [Z_to_bv 8 (-8)]); (98, [Z_to_bv 8 (-8)]); (97, [Z_to_bv 8 (-8)]); (88, [Z_to_bv 8 (-8)]); (87, [Z_to_bv 8 (-8)]); (86, [Z_to_bv 8 (-8)]);
(85, [Z_to_bv 8 (-8)]); (92, [Z_to_bv 8 (-8)]); (91, [Z_to_bv 8 (-8)]); (90, [Z_to_bv 8 (-8)]); (89, [Z_to_bv 8 (-8)]); (80, [Z_to_bv 8 (-8)]);
(79, [Z_to_bv 8 (-8)]); (78, [Z_to_bv 8 (-8)]); (77, [Z_to_bv 8 (-8)]); (84, [Z_to_bv 8 (-8)]); (83, [Z_to_bv 8 (-8)]); (82, [Z_to_bv 8 (-8)]);
(81, [Z_to_bv 8 (-8)]); (72, [Z_to_bv 8 (-8)]); (71, [Z_to_bv 8 (-8)]); (70, [Z_to_bv 8 (-8)]); (65, [Z_to_bv 8 (-8)]); (76, [Z_to_bv 8 (-8)]);
(75, [Z_to_bv 8 (-8)]); (74, [Z_to_bv 8 (-8)]); (73, [Z_to_bv 8 (-8)]); (138, [Z_to_bv 8 (-8)]); (132, [Z_to_bv 8 (-8)]); (131, [Z_to_bv 8 (-8)]);
(130, [Z_to_bv 8 (-8)]); (140, [Z_to_bv 8 (-8)])].

Lemma hx_r : forall (sf : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (m : mem) (c0 : list byte),
rw_cells bsegs m (sf + 1016) [CB 144 c0] -> mem_inv bsegs m -> 0 <= sf -> sf < 2^62 ->
evt bsegs (fun ms => exists m1 : mem,
ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 sf) s4 s5 (Z_to_bv 64 (-8)) s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x975f0) fc None m1 (seg_rom bsegs)
/\ munch [(sf + 1016, sf + 1160)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ rw_cells bsegs m1 (sf + 1016) [CB 144 (upd_all c0 (rev (map zw WS_XR)))])
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 sf) s4 s5 (Z_to_bv 64 (-8)) s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_EP) fc None m (seg_rom bsegs)).
Proof.
intros until c0. intros SH MI SF0 SF1. unfold A_EP.
pose proof (munch_refl [(sf + 1016, sf + 1160)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
hsh_start SH.
ato 0x975f0.
rewrite (hsh_hist_eq _ _ _ HH) in SH.
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact SH].
Qed.

Lemma hx_1 : forall (sf : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (m : mem),
mem_inv bsegs m ->
evt bsegs (fun ms => exists m1 : mem,
ms = MS (mkR (Z_to_bv 64 0x975fc) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sf + 16)) (Z_to_bv 64 1000) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 (sf + 16)) s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 PC_set_shadow_f8) fc None m1 (seg_rom bsegs)
/\ munch [] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 (sf + 16)) s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x975f0) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros MI. unfold PC_set_shadow_f8.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
ato 0x6a2cc.
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM| exact MI].
Qed.

Lemma hx_2 : forall (F : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 h0 : word) Fr fc (m : mem),
ra = Z_to_bv 64 0x975fc -> 0 < F < 2^62 -> rw_cells bsegs m F [C8 h0] -> mem_inv bsegs m ->
evt bsegs (fun ms => exists m1 : mem,
ms = MS (mkR (Z_to_bv 64 0x9761c) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) (Z_to_bv 64 HF_SIZE) a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 F) (Z_to_bv 64 F) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 PC_stack_free_8) fc None m1 (seg_rom bsegs)
/\ munch [(F, F + 8)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ rw_cells bsegs m1 F [C8 (Z_to_bv 64 0x45e0360e)])
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 F) (Z_to_bv 64 F) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> FR HD MI. unfold PC_stack_free_8, HF_SIZE.
replace (ret_pc (Z_to_bv 64 0x975fc)) with (Z_to_bv 64 0x975fc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(F, F + 8)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
ato 0x97608. astep. sh_if.
ato 0x51dd4.
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact HD].
Qed.

Lemma hx_3 : forall (usp S1 lo : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(ra' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 (jg : list byte) Fr fc (m : mem),
ra = Z_to_bv 64 0x9761c -> s0 = Z_to_bv 64 usp -> usp - 368 <= S1 <= usp - 352 -> 0 <= lo <= S1 -> usp < 2^63 ->
stk bsegs m lo S1 -> rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240) -> rw_cells bsegs m (S1 + 248) [CB (Z.to_nat (usp - 352 - S1)) jg] ->
rw_cells bsegs m (usp + -104) (h_saves s11' s10' s9' s8' s7' s6' s5' s4' s3' s2' s1' s0' ra') -> mem_inv bsegs m ->
evt bsegs (fun ms => exists m1 : mem,
ms = MS (mkR ra' (Z_to_bv 64 usp) gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6)
Fr (ret_pc ra') fc None m1 (seg_rom bsegs)
/\ munch [] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp)
(MS (mkR ra (Z_to_bv 64 S1) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> -> SR LO0 UT ST SP GP SV MI. unfold h_saves in SV.
replace (ret_pc (Z_to_bv 64 0x9761c)) with (Z_to_bv 64 0x9761c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
ato 0x9766c.

assert (FR : rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 ++ [CB (Z.to_nat (usp - 352 - S1)) jg] ++
[C8 s11'; C8 s10'; C8 s9'; C8 s8'; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra'])).
{ apply rw_cells_app. split; [exact SP|]. rewrite hsp_size. apply rw_cells_app. split.
- replace (S1 + Z.of_nat 248) with (S1 + 248) by lia. exact GP.
- cbn [cells_size csize Nat.add]. replace (S1 + Z.of_nat 248 + Z.of_nat (Z.to_nat (usp - 352 - S1) + 0)) with (usp + -104) by lia. exact SV. }
clear SP GP SV.
pose proof (stk_release bsegs m lo S1 _ ST FR ltac:(lia)) as ST2.
lazymatch type of ST2 with stk _ _ _ ?t => replace t with usp in ST2 by (rewrite !cells_size_app, hsp_size; cbn [cells_size csize]; lia) end. clear ST FR.
astep.
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST2].
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= first [ hsh_store | mem_after_store_fast ].
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Notation mem := (word -> option byte).
Definition e_stack_malloc_h (k : nat) : Z := 0x51b6c.
Definition PC_set_shadow_f8 : Z := 0x6a1e0.
Definition PC_set_shadow_00 : Z := 0x6a0c0.
Definition PC_asan_memcpy : Z := 0x66314.
Definition PC_stack_free_8 : Z := 0x51ce8.
Definition A_speex_bits_init_h : Z := 0x974c0.

Definition h_saves (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
[C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma hf_f0a : forall (usp lo : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
stk asegs m lo usp -> lo <= usp - 336 -> usp < 2^63 -> usp mod 16 = 0 -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (j1 : list byte),
ms = MS (mkR ra (Z_to_bv 64 (usp + -320)) gp tp t0 t1 t2 (Z_to_bv 64 usp) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x966a8) fc None m1 (seg_rom asegs)
/\ munch [(usp + -320, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -320)
/\ rw_cells asegs m1 (usp + -320) ([C8 (Z_to_bv 64 0); CB 208 j1] ++ h_saves s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_LLVMFuzzerTestOneInput) fc None m (seg_rom asegs)).
Proof.
intros until m. intros ST0 LO SPH SP16 MI.
unfold A_LLVMFuzzerTestOneInput, h_saves.
pose proof ST0 as (STa & STb & _).
pose proof (munch_refl [(usp + -320, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 320%nat ST0.
apply (rw_cells_split_CB asegs _ _ [] 320 _ [] [8; 208; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
cbn [mk_CB_cells app] in FR.
ato 0x966a8.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST0| exact FR].
Qed.

Lemma land_m32 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551584 = x - x mod 32.
Proof.
intros x Hx. change 18446744073709551584 with (Z.ldiff (Z.ones 64) (Z.ones 5)).
rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
change (2^5) with 32. Z.div_mod_to_equations. lia.
Qed.

Lemma h_rw_cells_to_CB : forall segs (m : mem) A cs, rw_cells segs m A cs -> rw_cells segs m A [CB (cells_size cs) (cells_bytes cs)].
Proof.
intros segs m A cs H. apply (rw_cells_recast segs m A cs); [exact H| | cbn [cells_bytes cbytes]; apply app_nil_r].
split; [| exact I]. destruct H as [[Hwf _] _]. exact (cells_bytes_length cs Hwf).
Qed.

Lemma h_rechunk : forall (m : mem) (lo usp S1 : Z) (j1 : list byte) (sv : list cell),
S1 = Z.land (usp + -320) 18446744073709551584 -> 336 <= usp < 2^63 -> usp mod 16 = 0 -> lo <= usp - 336 ->
stk asegs m lo (usp + -320) -> rw_cells asegs m (usp + -320) ([C8 (Z_to_bv 64 0); CB 208 j1] ++ sv) -> cells_size sv = 104%nat ->
(S1 mod 32 = 0 /\ usp - 336 <= S1 <= usp - 320) /\
exists w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 (jg : list byte), stk asegs m lo S1 /\ rw_cells asegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208)
/\ rw_cells asegs m (S1 + 216) [CB (Z.to_nat (usp - 320 - S1)) jg] /\ rw_cells asegs m (usp + -104) sv.
Proof.
intros m lo usp S1 j1 sv ES1 UR U16 LO ST FR SV.
rewrite land_m32 in ES1 by lia.
assert (SF : S1 mod 32 = 0 /\ usp - 336 <= S1 <= usp - 320) by (subst S1; Z.div_mod_to_equations; lia).
split; [exact SF|]. destruct SF as (S32 & SR).
apply rw_cells_app in FR. destruct FR as (FR1 & FR2). cbn [cells_size csize Nat.add] in FR2.
replace (usp + -320 + Z.of_nat 216) with (usp + -104) in FR2 by lia.
apply h_rw_cells_to_CB in FR1. cbn [cells_size csize Nat.add cells_bytes cbytes] in FR1.
set (d := Z.to_nat (usp - 320 - S1)).
destruct (stk_carve asegs m lo (usp + -320) d ST ltac:(unfold d; lia)) as (ST1 & (jd & JD)).
replace (usp + -320 - Z.of_nat d) with S1 in ST1, JD by (unfold d; lia).
assert (J : rw_cells asegs m S1 ([CB d jd] ++ [CB 216 (le8 (Z_to_bv 64 0) ++ j1 ++ [])])).
{ apply rw_cells_app. split; [exact JD|]. cbn [cells_size csize Nat.add]. replace (S1 + Z.of_nat (d + 0)) with (usp + -320) by (unfold d; lia). exact FR1. }
apply h_rw_cells_to_CB in J. cbn [cells_size csize Nat.add cells_bytes cbytes app] in J.
apply (rw_cells_split_CB asegs _ _ [] _ _ [] [216; d]%nat) in J; [| cbn; lia].
cbn [mk_CB_cells app] in J. apply (proj1 (rw_cells_app asegs m S1 [CB 216 _] [CB d _])) in J. destruct J as (J1 & J2). cbn [cells_size csize Nat.add] in J2.
destruct (hsp_of_CB m S1 _ J1) as (w0 & w8 & w16 & w24 & w32 & w40 & w48 & w56 & w64 & w72 & w80 & w88 & w96 & w104 & w112 & w120 & w128 & w136 & w144 & w152 & w160 & w168 & w176 & w184 & w192 & w200 & w208 & HS).
exists w0, w8, w16, w24, w32, w40, w48, w56, w64, w72, w80, w88, w96, w104, w112, w120, w128, w136, w144, w152, w160, w168, w176, w184, w192, w200, w208. eexists.
split; [exact ST1|]. split; [exact HS|]. split; [| exact FR2].
replace (S1 + 216) with (S1 + Z.of_nat (216 + 0)) by lia. exact J2.
Qed.

Lemma hf_f0b : forall (usp S1 : Z) (ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 F fc (m : mem),
S1 = Z.land (usp + -320) 18446744073709551584 -> 336 <= usp < 2^63 -> IMG_TOP <= S1 ->
rw_cells asegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208) -> client_consts m -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR (Z_to_bv 64 RA_h_smalloc) (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1)
(Z_to_bv 64 HF_SIZE) (Z_to_bv 64 g_shadow_memory_dynamic_address) (Z_to_bv 64 1) a3 a4 a5 a6 a7
(Z_to_bv 64 SHB) s3 s4 s5 s6 s7 a1 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_stack_malloc_h 8)) fc None m1 (seg_rom asegs)
/\ munch [(S1, S1 + 216)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 a0 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208))
(MS (mkR ra (Z_to_bv 64 (usp + -320)) gp tp t0 t1 t2 (Z_to_bv 64 usp) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x966a8) fc None m (seg_rom asegs)).
Proof.
intros until m. intros ES1 UR IMS SP CC MI. unfold hsp in *. unfold IMG_TOP in IMS.
destruct CC as (G1 & G2 & G3 & G4).
unfold RA_h_smalloc, HF_SIZE, e_stack_malloc_h, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
pose proof (munch_refl [(S1, S1 + 216)] m) as MU. pose proof (wmono_refl asegs m) as WM.
astep. rewrite <- ES1.
ato 0x51b6c.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact SP].
Qed.

Lemma hf_f1 : forall (usp S1 F sf : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208
(jf : list byte) Fr fc (m : mem),
0 < F -> F mod 64 = 0 -> F + 16384 <= S1 -> S1 + 216 <= usp -> usp < 2^63 -> sf = Z.shiftr F 3 + SHB ->
rw_cells asegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208) -> rw_cells asegs m F [CB 24 jf] -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR (Z_to_bv 64 RA_h_smalloc) (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1)
(Z_to_bv 64 8384) (Z_to_bv 64 0x41b58ab3) (Z_to_bv 64 0x227f8) (Z_to_bv 64 0x96668) (Z_to_bv 64 (-15)) (Z_to_bv 64 SHB) a6 a7
(Z_to_bv 64 (-14)) (Z_to_bv 64 sf) (Z_to_bv 64 F) (Z_to_bv 64 F) (Z_to_bv 64 (-8)) s7 s8 (Z_to_bv 64 (F + 8384)) s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0x96768) fc None m1 (seg_rom asegs)
/\ munch [(S1, S1 + 216); (F, F + 24)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 (Z_to_bv 64 SHB) w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 (Z_to_bv 64 F))
/\ rw_cells asegs m1 F [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x227f8); C8 (Z_to_bv 64 0x96668)])
(MS (mkR (Z_to_bv 64 RA_h_smalloc) (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1) (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (ret_pc (Z_to_bv 64 RA_h_smalloc)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros F0 F64 FS1 SU SPH Esf SP FB MI. unfold hsp in *.
unfold RA_h_smalloc in *.
replace (ret_pc (Z_to_bv 64 0x966e0)) with (Z_to_bv 64 0x966e0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(S1, S1 + 216); (F, F + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.
apply (rw_cells_split_CB asegs _ _ [] 24 _ [] [8; 8; 8]%nat) in FB; [| reflexivity]. cbn [mk_CB_cells app] in FB.
ato 0x966f4. astep. sh_if.
ato 0x96768.
rewrite <- Esf.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact SP| exact FB].
Qed.

Lemma hf_p1 : forall (sf F : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s4 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word)
(js : list byte) Fr fc (m : mem),
rw_cells asegs m sf [CB 16 js] -> mem_inv asegs m -> 0 <= sf < 2^62 -> 0 <= F < 2^62 ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR (Z_to_bv 64 0x967bc) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sf + 16)) (Z_to_bv 64 1000) a2 a3 (Z_to_bv 64 (-15)) a5 a6 a7
(Z_to_bv 64 (-14)) (Z_to_bv 64 sf) s4 s5 (Z_to_bv 64 (-8)) (Z_to_bv 64 (sf + 16)) s8 (Z_to_bv 64 (F + 8384)) (Z_to_bv 64 (F + 8384 + 784)) s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 PC_set_shadow_f8) fc None m1 (seg_rom asegs)
/\ munch [(sf, sf + 16)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ rw_cells asegs m1 sf [CB 16 HSH_P1])
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 (-15)) a5 a6 a7
(Z_to_bv 64 (-14)) (Z_to_bv 64 sf) s4 s5 (Z_to_bv 64 (-8)) s7 s8 (Z_to_bv 64 (F + 8384)) s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0x96768) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SH MI SFR FR.
unfold PC_set_shadow_f8.
pose proof (munch_refl [(sf, sf + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
hsh_start SH.
ato 0x6a1e0.
hsh_lit SH HSH_P1.
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact SH].
Qed.

Lemma hf_p2 : forall (sf F : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(js : list byte) Fr fc (m : mem),
ra = Z_to_bv 64 0x967bc ->
rw_cells asegs m (sf + 1016) [CB 144 js] -> mem_inv asegs m -> 0 <= sf < 2^62 ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR (Z_to_bv 64 0x96a0c) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sf + 16)) (Z_to_bv 64 1000) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (-14)) (Z_to_bv 64 sf) s4 s5 (Z_to_bv 64 (-8)) (Z_to_bv 64 (sf + 16)) s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 PC_set_shadow_00) fc None m1 (seg_rom asegs)
/\ munch [(sf + 1016, sf + 1160)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ rw_cells asegs m1 (sf + 1016) [CB 144 HSH_P2])
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (-14)) (Z_to_bv 64 sf) s4 s5 (Z_to_bv 64 (-8)) (Z_to_bv 64 (sf + 16)) s8 s9 s10 s11 t3 t4 t5 t6)
Fr (ret_pc ra) fc None m (seg_rom asegs)).
Proof.
intros until m. intros -> SH MI SFR.
unfold PC_set_shadow_00.
replace (ret_pc (Z_to_bv 64 0x967bc)) with (Z_to_bv 64 0x967bc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(sf + 1016, sf + 1160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
hsh_start SH.
ato 0x6a0c0.
hsh_lit SH HSH_P2.
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact SH].
Qed.
Definition WS_P3R : list (Z * list byte) :=
[(132, [Z_to_bv 8 0]); (131, [Z_to_bv 8 0]); (130, [Z_to_bv 8 0]); (120, [Z_to_bv 8 0]); (119, [Z_to_bv 8 0]); (118, [Z_to_bv 8 0]);
(113, [Z_to_bv 8 0]); (112, [Z_to_bv 8 0]); (111, [Z_to_bv 8 0]); (110, [Z_to_bv 8 0]); (117, [Z_to_bv 8 0]); (116, [Z_to_bv 8 0]);
(115, [Z_to_bv 8 0]); (114, [Z_to_bv 8 0]); (105, [Z_to_bv 8 0]); (104, [Z_to_bv 8 0]); (103, [Z_to_bv 8 0]); (102, [Z_to_bv 8 0]);
(109, [Z_to_bv 8 0]); (108, [Z_to_bv 8 0]); (107, [Z_to_bv 8 0]); (106, [Z_to_bv 8 0]); (97, [Z_to_bv 8 0]); (96, [Z_to_bv 8 0]);
(95, [Z_to_bv 8 0]); (94, [Z_to_bv 8 0]); (101, [Z_to_bv 8 0]); (100, [Z_to_bv 8 0]); (99, [Z_to_bv 8 0]); (98, [Z_to_bv 8 0]); (89, [Z_to_bv 8 0]);
(88, [Z_to_bv 8 0]); (87, [Z_to_bv 8 0]); (86, [Z_to_bv 8 0]); (93, [Z_to_bv 8 0]); (92, [Z_to_bv 8 0]); (91, [Z_to_bv 8 0]); (90, [Z_to_bv 8 0]);
(81, [Z_to_bv 8 0]); (80, [Z_to_bv 8 0]); (79, [Z_to_bv 8 0]); (78, [Z_to_bv 8 0]); (85, [Z_to_bv 8 0]); (84, [Z_to_bv 8 0]); (83, [Z_to_bv 8 0]);
(82, [Z_to_bv 8 0]); (73, [Z_to_bv 8 0]); (72, [Z_to_bv 8 0]); (71, [Z_to_bv 8 0]); (70, [Z_to_bv 8 0]); (77, [Z_to_bv 8 0]); (76, [Z_to_bv 8 0]);
(75, [Z_to_bv 8 0]); (74, [Z_to_bv 8 0]); (65, [Z_to_bv 8 0]); (64, [Z_to_bv 8 0]); (63, [Z_to_bv 8 0]); (62, [Z_to_bv 8 0]); (61, [Z_to_bv 8 0]);
(60, [Z_to_bv 8 0]); (55, [Z_to_bv 8 0]); (54, [Z_to_bv 8 0]); (53, [Z_to_bv 8 0]); (52, [Z_to_bv 8 0]); (47, [Z_to_bv 8 0]); (46, [Z_to_bv 8 0]);
(45, [Z_to_bv 8 0]); (44, [Z_to_bv 8 0]); (39, [Z_to_bv 8 0]); (38, [Z_to_bv 8 0]); (37, [Z_to_bv 8 0]); (36, [Z_to_bv 8 0]); (35, [Z_to_bv 8 0]);
(34, [Z_to_bv 8 0])].

Lemma hf_p3r : forall (sf : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (m : mem) (c0 : list byte),
rw_cells asegs m (sf + 1016) [CB 144 c0] -> mem_inv asegs m -> 0 <= sf -> sf < 2^62 ->
evt asegs (fun ms => exists m1 : mem,
ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 sf) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x96b40) fc None m1 (seg_rom asegs)
/\ munch [(sf + 1016, sf + 1160)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ rw_cells asegs m1 (sf + 1016) [CB 144 (upd_all c0 (rev (map zw WS_P3R)))])
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 sf) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x96a18) fc None m (seg_rom asegs)).
Proof.
intros until c0. intros SH MI SF0 SF1.
pose proof (munch_refl [(sf + 1016, sf + 1160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
hsh_start SH.
ato 0x96b40.
rewrite (hsh_hist_eq _ _ _ HH) in SH.
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact SH].
Qed.

Lemma hf_p3 : forall (usp S1 sf F : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s8 s11 t3 t4 t5 t6 : word) w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 (jfs : list byte) (data : word) Fr fc (m : mem),
ra = Z_to_bv 64 0x96a0c ->
rw_cells asegs m (sf + 1016) [CB 144 HSH_P2] -> rw_cells asegs m (F + 8384) [CB 4 jfs] -> rw_cells asegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 data w80 w88 (Z_to_bv 64 SHB) w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 (Z_to_bv 64 F)) ->
mem_inv asegs m -> 0 <= sf -> 0 <= F -> S1 < 2^62 -> sf + 2048 <= S1 -> F + 16384 <= S1 -> (F + 16384 <= sf \/ sf + 2048 <= F) ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR (Z_to_bv 64 0x96b58) (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1)
(Z_to_bv 64 (F + 9168)) (Z_to_bv 64 0x23260) (Z_to_bv 64 24) a3 a4 a5 a6 a7
(Z_to_bv 64 4) (Z_to_bv 64 sf) (Z_to_bv 64 F) (Z_to_bv 64 F) (Z_to_bv 64 (-8)) (Z_to_bv 64 (sf + 16)) s8 (Z_to_bv 64 (F + 8384)) (Z_to_bv 64 (F + 9168)) s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 PC_asan_memcpy) fc None m1 (seg_rom asegs)
/\ munch [(sf + 1016, sf + 1160); (F + 8384, F + 8388); (S1, S1 + 216)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 (sf + 1016) [CB 144 HSH_P3] /\ rw_cells asegs m1 (F + 8384) [C4 (Z_to_bv 64 0)]
/\ rw_cells asegs m1 S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 data w80 w88 (Z_to_bv 64 SHB) w104 w112 w120 w128 w136 w144 w152 (Z_to_bv 64 (F + 9168)) w168 w176 w184 w192 w200 (Z_to_bv 64 F)))
(MS (mkR ra (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 sf) (Z_to_bv 64 F) (Z_to_bv 64 F) (Z_to_bv 64 (-8)) (Z_to_bv 64 (sf + 16)) s8 (Z_to_bv 64 (F + 8384)) (Z_to_bv 64 (F + 9168)) s11 t3 t4 t5 t6)
Fr (ret_pc ra) fc None m (seg_rom asegs)).
Proof.
intros until m. intros -> SH FS SP MI SF0 F0 S1R SFS FS1 FSF. unfold hsp in *.
unfold PC_asan_memcpy.
replace (ret_pc (Z_to_bv 64 0x96a0c)) with (Z_to_bv 64 0x96a0c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(sf + 1016, sf + 1160); (F + 8384, F + 8388); (S1, S1 + 216)] m) as MU. pose proof (wmono_refl asegs m) as WM.
hsh_start SH.
ato 0x96a18.
rewrite (hsh_hist_eq _ _ _ HH) in SH. clear HH LB.
call (hf_p3r sf); [ exact SH | exact MI | lia | lia | ].
ato 0x66314.
assert (E3 : upd_all (upd_all HSH_P2 (rev (map zw [(32, [Z_to_bv 8 4])]))) (rev (map zw WS_P3R)) = HSH_P3)
by (unfold HSH_P2, HSH_P3, WS_P3R; cbv [upd_all fold_left upd1 upd_bytes firstn skipn app repeat length fst snd Nat.add Nat.sub rev map zw Z.to_nat Pos.to_nat Pos.iter_op zruns]; reflexivity).
rewrite E3 in POST.
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [exact POST|]. split; [exact FS| exact SP].
Qed.

Lemma hf_p4 : forall (usp S1 sf F size : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s11 t3 t4 t5 t6 : word) w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w104 w112 w120 w128 w136 w144 w152 w168 w176 w184 w192 w200 (jr joy : list byte) (data : word) Fr fc (m : mem),
ra = Z_to_bv 64 0x96b58 -> 0 <= size <= 4096 ->
rw_cells asegs m (sf + 1016) [CB 144 HSH_P3] -> rw_cells asegs m (F + 9232) [CB 4 jr] -> rw_cells asegs m (F + 8480) [CB 32 joy] ->
rw_cells asegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 data w80 w88 (Z_to_bv 64 SHB) w104 w112 w120 w128 w136 w144 w152 (Z_to_bv 64 (F + 9168)) w168 w176 w184 w192 w200 (Z_to_bv 64 F)) ->
mem_inv asegs m -> 0 <= sf -> 0 < F -> S1 < 2^62 -> sf + 2048 <= S1 -> F + 16384 <= S1 -> (F + 16384 <= sf \/ sf + 2048 <= F) ->
evt asegs (fun ms => exists (m1 : mem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
ms = MS (mkR (Z_to_bv 64 0x96bc4) (Z_to_bv 64 S1) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 S1)
(Z_to_bv 64 (F + 8400)) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (F + 8608)) (Z_to_bv 64 sf) (Z_to_bv 64 (F + 128)) (Z_to_bv 64 F) (Z_to_bv 64 (-8)) (Z_to_bv 64 (F + 48)) (Z_to_bv 64 size)
(Z_to_bv 64 (F + 8384)) (Z_to_bv 64 (F + 8544)) (Z_to_bv 64 (F + 8400)) t3' t4' t5' t6')
Fr (Z_to_bv 64 A_speex_bits_init_h) fc None m1 (seg_rom asegs)
/\ munch [(sf + 1016, sf + 1160); (F + 9232, F + 9236); (F + 8480, F + 8512); (S1, S1 + 216)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 (sf + 1016) [CB 144 HSH_T] /\ rw_cells asegs m1 (F + 9232) [C4 (Z_to_bv 64 0)]
/\ sync_rep m1 (F + 8480) 0 ogg_sync_init []
/\ rw_cells asegs m1 S1 (hsp w0 w8 w16 (Z_to_bv 64 (sf + 16)) (Z_to_bv 64 F) (Z_to_bv 64 F) (Z_to_bv 64 (F + 9248)) (Z_to_bv 64 (F + 9232)) (Z_to_bv 64 (F + 32)) data w80 w88 (Z_to_bv 64 SHB) w104 w112 (Z_to_bv 64 (F + 8480)) w128 w136 w144 (Z_to_bv 64 (F + 8688)) (Z_to_bv 64 (F + 9168)) (Z_to_bv 64 (F + 8384)) w176 w184 w192 w200 (Z_to_bv 64 F)))
(MS (mkR ra (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 4) (Z_to_bv 64 sf) (Z_to_bv 64 F) (Z_to_bv 64 F) (Z_to_bv 64 (-8)) (Z_to_bv 64 (sf + 16)) (Z_to_bv 64 size) (Z_to_bv 64 (F + 8384)) (Z_to_bv 64 (F + 9168)) s11 t3 t4 t5 t6)
Fr (ret_pc ra) fc None m (seg_rom asegs)).
Proof.
intros until m. intros -> SZ SH RT OY SP MI SF0 F0 S1R SFS FS1 FSF. unfold hsp in *.
unfold A_speex_bits_init_h.
replace (ret_pc (Z_to_bv 64 0x96b58)) with (Z_to_bv 64 0x96b58) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(sf + 1016, sf + 1160); (F + 9232, F + 9236); (F + 8480, F + 8512); (S1, S1 + 216)] m) as MU. pose proof (wmono_refl asegs m) as WM.
hsh_start SH.
ato 0x96b68. astep. sh_if.
hsh_lit0 SH HSH_T ltac:(unfold HSH_P3, HSH_T).
ato 0x96bb8. astep.
call (ogg_sync_init_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc _ (F + 8480) joy); [ unfold wz; f_equal; lia | lia | exact OY | exact MI | ].
ato 0x974c0.
apply evt_done. do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [exact SH|]. split; [exact RT|]. split; [assumption| exact SP].
Qed.

Lemma hf_p4b : forall (usp S1 sf F size : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s11 t3 t4 t5 t6 : word) (jr : list byte) Fr fc (m : mem),
ra = Z_to_bv 64 0x96b58 -> 4096 < size < 2^63 ->
rw_cells asegs m (sf + 1016) [CB 144 HSH_P3] -> rw_cells asegs m (F + 9232) [CB 4 jr] ->
mem_inv asegs m -> 0 <= sf -> 0 < F -> sf + 2048 <= S1 -> (F + 16384 <= sf \/ sf + 2048 <= F) ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR ra (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1) (Z_to_bv 64 4096) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 4) (Z_to_bv 64 sf) (Z_to_bv 64 F) (Z_to_bv 64 F) (Z_to_bv 64 (-8)) (Z_to_bv 64 (sf + 16)) (Z_to_bv 64 size) (Z_to_bv 64 (F + 8384)) (Z_to_bv 64 (F + 9168)) s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0x9720c) fc None m1 (seg_rom asegs)
/\ munch [(sf + 1016, sf + 1160); (F + 9232, F + 9236)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 (sf + 1016) [CB 144 HSH_T] /\ rw_cells asegs m1 (F + 9232) [C4 (Z_to_bv 64 0)])
(MS (mkR ra (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 4) (Z_to_bv 64 sf) (Z_to_bv 64 F) (Z_to_bv 64 F) (Z_to_bv 64 (-8)) (Z_to_bv 64 (sf + 16)) (Z_to_bv 64 size) (Z_to_bv 64 (F + 8384)) (Z_to_bv 64 (F + 9168)) s11 t3 t4 t5 t6)
Fr (ret_pc ra) fc None m (seg_rom asegs)).
Proof.
intros until m. intros -> SZ SH RT MI SF0 F0 SFS FSF.
replace (ret_pc (Z_to_bv 64 0x96b58)) with (Z_to_bv 64 0x96b58) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(sf + 1016, sf + 1160); (F + 9232, F + 9236)] m) as MU. pose proof (wmono_refl asegs m) as WM.
hsh_start SH.
ato 0x96b68. astep. sh_if.
hsh_lit0 SH HSH_T ltac:(unfold HSH_P3, HSH_T).
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
split; [exact SH| exact RT].
Qed.

Lemma hf_p5 : forall (usp S1 sf F size : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s9 t3 t4 t5 t6 : word) w0 w8 w16 w80 w88 w104 w112 w128 w136 w144 w176 w184 w192 w200 (data : word) Fr fc (m : mem),
ra = Z_to_bv 64 0x96bc4 -> rw_cells asegs m S1 (hsp w0 w8 w16 (Z_to_bv 64 (sf + 16)) (Z_to_bv 64 F) (Z_to_bv 64 F) (Z_to_bv 64 (F + 9248)) (Z_to_bv 64 (F + 9232)) (Z_to_bv 64 (F + 32)) data w80 w88 (Z_to_bv 64 SHB) w104 w112 (Z_to_bv 64 (F + 8480)) w128 w136 w144 (Z_to_bv 64 (F + 8688)) (Z_to_bv 64 (F + 9168)) (Z_to_bv 64 (F + 8384)) w176 w184 w192 w200 (Z_to_bv 64 F)) -> mem_inv asegs m -> S1 < 2^62 ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR ra (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1) (Z_to_bv 64 size) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a4 a5 a6 a7
(Z_to_bv 64 (F + 8608)) (Z_to_bv 64 sf) (Z_to_bv 64 (F + 128)) (Z_to_bv 64 F) (Z_to_bv 64 0) (Z_to_bv 64 (F + 64)) (Z_to_bv 64 0)
(Z_to_bv 64 0) (Z_to_bv 64 (F + 8544)) (Z_to_bv 64 (F + 8400)) t3 t4 t5 t6)
Fr (Z_to_bv 64 A_CH) fc None m1 (seg_rom asegs)
/\ munch [(S1, S1 + 216)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 S1 (hsp w0 (Z_to_bv 64 (F + 64)) (Z_to_bv 64 (F + 48)) (Z_to_bv 64 (sf + 16)) (Z_to_bv 64 F) (Z_to_bv 64 F) (Z_to_bv 64 (F + 9248)) (Z_to_bv 64 (F + 9232)) (Z_to_bv 64 (F + 32)) data w80 w88 (Z_to_bv 64 SHB) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (F + 8480)) (Z_to_bv 64 0) (Z_to_bv 64 2) w144 (Z_to_bv 64 (F + 8688)) (Z_to_bv 64 (F + 9168)) (Z_to_bv 64 (F + 8384)) w176 (Z_to_bv 64 (-1)) w192 w200 (Z_to_bv 64 F)))
(MS (mkR ra (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (F + 8608)) (Z_to_bv 64 sf) (Z_to_bv 64 (F + 128)) (Z_to_bv 64 F) s6 (Z_to_bv 64 (F + 48)) (Z_to_bv 64 size)
s9 (Z_to_bv 64 (F + 8544)) (Z_to_bv 64 (F + 8400)) t3 t4 t5 t6)
Fr (ret_pc ra) fc None m (seg_rom asegs)).
Proof.
intros until m. intros -> SP MI S1R. unfold hsp in *. unfold A_CH.
replace (ret_pc (Z_to_bv 64 0x96bc4)) with (Z_to_bv 64 0x96bc4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(S1, S1 + 216)] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0x96c04.
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact SP].
Qed.

Lemma hx_0 : forall (S1 sf F : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) w0 w8 w16 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 Fr fc (m : mem),
s1 = Z_to_bv 64 S1 -> rw_cells asegs m S1 (hsp w0 w8 w16 (Z_to_bv 64 (sf + 16)) (Z_to_bv 64 F) (Z_to_bv 64 F) w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208) -> mem_inv asegs m -> S1 < 2^62 ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 F) (Z_to_bv 64 F) (Z_to_bv 64 (-8)) (Z_to_bv 64 (sf + 16)) s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0x9720c) fc None m1 (seg_rom asegs)
/\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 S1 (hsp w0 w8 w16 (Z_to_bv 64 (sf + 16)) (Z_to_bv 64 F) (Z_to_bv 64 F) w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_XT) fc None m (seg_rom asegs)).
Proof.
intros until m. intros -> SP MI S1R. unfold hsp in *. unfold A_XT.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0x9720c.
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact SP].
Qed.

Definition WS_XR : list (Z * list byte) :=
[(36, [Z_to_bv 8 (-8)]); (35, [Z_to_bv 8 (-8)]); (34, [Z_to_bv 8 (-8)]); (32, [Z_to_bv 8 (-8)]); (44, [Z_to_bv 8 (-8)]); (39, [Z_to_bv 8 (-8)]);
(38, [Z_to_bv 8 (-8)]); (37, [Z_to_bv 8 (-8)]); (52, [Z_to_bv 8 (-8)]); (47, [Z_to_bv 8 (-8)]); (46, [Z_to_bv 8 (-8)]); (45, [Z_to_bv 8 (-8)]);
(64, [Z_to_bv 8 (-8)]); (63, [Z_to_bv 8 (-8)]); (62, [Z_to_bv 8 (-8)]); (61, [Z_to_bv 8 (-8)]); (60, [Z_to_bv 8 (-8)]); (55, [Z_to_bv 8 (-8)]);
(54, [Z_to_bv 8 (-8)]); (53, [Z_to_bv 8 (-8)]); (120, [Z_to_bv 8 (-8)]); (119, [Z_to_bv 8 (-8)]); (118, [Z_to_bv 8 (-8)]); (117, [Z_to_bv 8 (-8)]);
(112, [Z_to_bv 8 (-8)]); (111, [Z_to_bv 8 (-8)]); (110, [Z_to_bv 8 (-8)]); (109, [Z_to_bv 8 (-8)]); (116, [Z_to_bv 8 (-8)]);
(115, [Z_to_bv 8 (-8)]); (114, [Z_to_bv 8 (-8)]); (113, [Z_to_bv 8 (-8)]); (104, [Z_to_bv 8 (-8)]); (103, [Z_to_bv 8 (-8)]);
(102, [Z_to_bv 8 (-8)]); (101, [Z_to_bv 8 (-8)]); (108, [Z_to_bv 8 (-8)]); (107, [Z_to_bv 8 (-8)]); (106, [Z_to_bv 8 (-8)]);
(105, [Z_to_bv 8 (-8)]); (96, [Z_to_bv 8 (-8)]); (95, [Z_to_bv 8 (-8)]); (94, [Z_to_bv 8 (-8)]); (93, [Z_to_bv 8 (-8)]); (100, [Z_to_bv 8 (-8)]);
(99, [Z_to_bv 8 (-8)]); (98, [Z_to_bv 8 (-8)]); (97, [Z_to_bv 8 (-8)]); (88, [Z_to_bv 8 (-8)]); (87, [Z_to_bv 8 (-8)]); (86, [Z_to_bv 8 (-8)]);
(85, [Z_to_bv 8 (-8)]); (92, [Z_to_bv 8 (-8)]); (91, [Z_to_bv 8 (-8)]); (90, [Z_to_bv 8 (-8)]); (89, [Z_to_bv 8 (-8)]); (80, [Z_to_bv 8 (-8)]);
(79, [Z_to_bv 8 (-8)]); (78, [Z_to_bv 8 (-8)]); (77, [Z_to_bv 8 (-8)]); (84, [Z_to_bv 8 (-8)]); (83, [Z_to_bv 8 (-8)]); (82, [Z_to_bv 8 (-8)]);
(81, [Z_to_bv 8 (-8)]); (72, [Z_to_bv 8 (-8)]); (71, [Z_to_bv 8 (-8)]); (70, [Z_to_bv 8 (-8)]); (65, [Z_to_bv 8 (-8)]); (76, [Z_to_bv 8 (-8)]);
(75, [Z_to_bv 8 (-8)]); (74, [Z_to_bv 8 (-8)]); (73, [Z_to_bv 8 (-8)]); (138, [Z_to_bv 8 (-8)]); (132, [Z_to_bv 8 (-8)]); (131, [Z_to_bv 8 (-8)]);
(130, [Z_to_bv 8 (-8)]); (140, [Z_to_bv 8 (-8)])].

Lemma hx_r : forall (sf : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (m : mem) (c0 : list byte),
rw_cells asegs m (sf + 1016) [CB 144 c0] -> mem_inv asegs m -> 0 <= sf -> sf < 2^62 ->
evt asegs (fun ms => exists m1 : mem,
ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 sf) s4 s5 (Z_to_bv 64 (-8)) s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x97340) fc None m1 (seg_rom asegs)
/\ munch [(sf + 1016, sf + 1160)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ rw_cells asegs m1 (sf + 1016) [CB 144 (upd_all c0 (rev (map zw WS_XR)))])
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 sf) s4 s5 (Z_to_bv 64 (-8)) s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x9720c) fc None m (seg_rom asegs)).
Proof.
intros until c0. intros SH MI SF0 SF1.
pose proof (munch_refl [(sf + 1016, sf + 1160)] m) as MU. pose proof (wmono_refl asegs m) as WM.
hsh_start SH.
ato 0x97340.
rewrite (hsh_hist_eq _ _ _ HH) in SH.
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact SH].
Qed.

Lemma hx_1 : forall (sf : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (m : mem),
mem_inv asegs m ->
evt asegs (fun ms => exists m1 : mem,
ms = MS (mkR (Z_to_bv 64 0x9734c) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sf + 16)) (Z_to_bv 64 1000) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 (sf + 16)) s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 PC_set_shadow_f8) fc None m1 (seg_rom asegs)
/\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 (sf + 16)) s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x97340) fc None m (seg_rom asegs)).
Proof.
intros until m. intros MI. unfold PC_set_shadow_f8.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0x6a1e0.
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM| exact MI].
Qed.

Lemma hx_2 : forall (F : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 h0 : word) Fr fc (m : mem),
ra = Z_to_bv 64 0x9734c -> 0 < F < 2^62 -> rw_cells asegs m F [C8 h0] -> mem_inv asegs m ->
evt asegs (fun ms => exists m1 : mem,
ms = MS (mkR (Z_to_bv 64 0x9736c) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) (Z_to_bv 64 HF_SIZE) a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 F) (Z_to_bv 64 F) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 PC_stack_free_8) fc None m1 (seg_rom asegs)
/\ munch [(F, F + 8)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ rw_cells asegs m1 F [C8 (Z_to_bv 64 0x45e0360e)])
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 F) (Z_to_bv 64 F) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (ret_pc ra) fc None m (seg_rom asegs)).
Proof.
intros until m. intros -> FR HD MI. unfold PC_stack_free_8, HF_SIZE.
replace (ret_pc (Z_to_bv 64 0x9734c)) with (Z_to_bv 64 0x9734c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(F, F + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0x97358. astep. sh_if.
ato 0x51ce8.
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact HD].
Qed.

Lemma hx_3 : forall (usp S1 lo : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(ra' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 (jg : list byte) Fr fc (m : mem),
ra = Z_to_bv 64 0x9736c -> s0 = Z_to_bv 64 usp -> usp - 336 <= S1 <= usp - 320 -> 0 <= lo <= S1 -> usp < 2^63 ->
stk asegs m lo S1 -> rw_cells asegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208) -> rw_cells asegs m (S1 + 216) [CB (Z.to_nat (usp - 320 - S1)) jg] ->
rw_cells asegs m (usp + -104) (h_saves s11' s10' s9' s8' s7' s6' s5' s4' s3' s2' s1' s0' ra') -> mem_inv asegs m ->
evt asegs (fun ms => exists m1 : mem,
ms = MS (mkR ra' (Z_to_bv 64 usp) gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6)
Fr (ret_pc ra') fc None m1 (seg_rom asegs)
/\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp)
(MS (mkR ra (Z_to_bv 64 S1) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (ret_pc ra) fc None m (seg_rom asegs)).
Proof.
intros until m. intros -> -> SR LO0 UT ST SP GP SV MI. unfold h_saves in SV.
replace (ret_pc (Z_to_bv 64 0x9736c)) with (Z_to_bv 64 0x9736c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0x973bc.

assert (FR : rw_cells asegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 ++ [CB (Z.to_nat (usp - 320 - S1)) jg] ++
[C8 s11'; C8 s10'; C8 s9'; C8 s8'; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra'])).
{ apply rw_cells_app. split; [exact SP|]. rewrite hsp_size. apply rw_cells_app. split.
- replace (S1 + Z.of_nat 216) with (S1 + 216) by lia. exact GP.
- cbn [cells_size csize Nat.add]. replace (S1 + Z.of_nat 216 + Z.of_nat (Z.to_nat (usp - 320 - S1) + 0)) with (usp + -104) by lia. exact SV. }
clear SP GP SV.
pose proof (stk_release asegs m lo S1 _ ST FR ltac:(lia)) as ST2.
lazymatch type of ST2 with stk _ _ _ ?t => replace t with usp in ST2 by (rewrite !cells_size_app, hsp_size; cbn [cells_size csize]; lia) end. clear ST FR.
astep.
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST2].
Qed.
