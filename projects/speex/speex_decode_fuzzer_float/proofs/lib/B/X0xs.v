(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Znumtheory.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1df X1ck X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1od X1rg X1rh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X09u X071.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X14x X0yr X12b X0z5 X110 X105 X10j X0xn X115 X0ys X0xd.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= first [ hsh_store | mem_after_store_fast ].
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Notation mem := (word -> option byte).

Definition A_HP_h : Z := 0x970e0.
Definition A_p2h_h : Z := 0x99e60.
Definition A_lib_get_mode_h : Z := 0xb5708.
Definition A_decoder_init_h : Z := 0x9896c.
Definition A_ctl_h : Z := 0x98c74.
Definition A_destroy_hp : Z := 0x98a30.
Definition A_free_hp : Z := 0x67f80.
Definition A_bdes_hp : Z := 0x97904.
Definition A_sclr_hp : Z := 0xc1294.
Definition A_yclr_hp : Z := 0xc166c.

Lemma bv_eqb_lit_ne_hb : forall r k, -2^63 <= r < 2^63 -> -2^63 <= k < 2^63 -> r <> k -> bv_eqb (Z_to_bv 64 r) (Z_to_bv 64 k) = false.
Proof.
intros r k Hr Hk NE. unfold bv_eqb. apply Z.eqb_neq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
intros E. Z.div_mod_to_equations. nia.
Qed.
Lemma h_swrap32_eq_hb : forall z, bv_swrap 32 z = (z + 2147483648) mod 4294967296 - 2147483648.
Proof. reflexivity. Qed.
Lemma h_sx32_lit_hb : forall e, (-2^31 <= e < 2^31)%Z -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap, h_swrap32_eq_hb.
change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.
Lemma lts_lit_hb : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_lts. rewrite !signed_lit_small by lia. reflexivity. Qed.
Lemma swrap32_small_hb : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 x = x.
Proof. intros x Hx. rewrite h_swrap32_eq_hb. rewrite Z.mod_small by lia. lia. Qed.

Definition HSH_HA : list byte := map (Z_to_bv 8) [-15; -15; -15; -15; 4; -14; -8; -8; -8; -8; -8; -14; -14; -14; -14; -14].

Lemma hp_w1a : forall (sf : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (m : mem),
0 <= sf < 2^62 -> rw_cells bsegs m sf [CB 16 HSH_P1] -> mem_inv bsegs m ->
evt bsegs (fun ms => exists m1 : mem,
ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 4) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 sf) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0x970e8) fc None m1 (seg_rom bsegs)
/\ munch [(sf, sf + 16)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ rw_cells bsegs m1 sf [CB 16 HSH_HA])
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 sf) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_HP_h) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SFR SH MI. unfold A_HP_h.
pose proof (munch_refl [(sf, sf + 16)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
hsh_start SH.
ato 0x970e8.
hsh_lit0 SH HSH_HA ltac:(unfold HSH_P1, HSH_HA).
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact SH].
Qed.

Lemma hp_w1b : forall (S1 F : Z) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 we Fr fc (m : mem),
0 <= S1 < 2^62 -> 0 < F < 2^62 -> F + 16384 <= S1 ->
rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 (Z_to_bv 64 (F + 32)) w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208
w216 w224 w232 w240) ->
rw_cells bsegs m (F + 32) [C4 we] -> mem_inv bsegs m ->
evt bsegs (fun ms => exists m1 : mem,
ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0x970f4) fc None m1 (seg_rom bsegs)
/\ munch [(F + 32, F + 36)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ rw_cells bsegs m1 (F + 32) [C4 (Z_to_bv 64 1)]
/\ rw_cells bsegs m1 S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 (Z_to_bv 64 (F + 32)) w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208
w216 w224 w232 w240))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x970e8) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros S1R FR FS1 SP EN MI. unfold hsp in *.
pose proof (munch_refl [(F + 32, F + 36)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
ato 0x970f4.
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact EN| exact SP].
Qed.

Lemma hp_w1c : forall (sf : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (m : mem),
0 <= sf < 2^62 -> rw_cells bsegs m sf [CB 16 HSH_HA] -> mem_inv bsegs m ->
evt bsegs (fun ms => exists m1 : mem,
ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 sf) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0x97108) fc None m1 (seg_rom bsegs)
/\ munch [(sf, sf + 16)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ rw_cells bsegs m1 sf [CB 16 HSH_L_HDR])
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 sf) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x970f4) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SFR SH MI.
pose proof (munch_refl [(sf, sf + 16)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
hsh_start SH.
ato 0x97108.
hsh_lit0 SH HSH_L_HDR ltac:(unfold HSH_HA, HSH_L_HDR).
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact SH].
Qed.

Lemma hp_w1d : forall (S1 F Bd bytes : Z) (op : packet) (gw : word) (kc : list cell)
(ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word) Fr fc (m : mem),
0 < F < 2^62 -> bytes = pk_bytes op -> 0 <= bytes < 2^31 ->
rw_cells bsegs m (F + 8608) (op_cells Bd (Some op) gw kc) -> mem_inv bsegs m ->
evt bsegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x97114) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 (Bd + pk_off op)) (Z_to_bv 64 bytes) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (F + 8608)) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 bytes) s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_p2h_h) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (F + 8608)) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 bytes) s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0x97108) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FR EB BR OPC MI. unfold op_cells, wz in OPC. unfold A_p2h_h.
ato 0x99e60. rewrite ?Z.add_0_r, ?swrap32_small_hb by lia.
apply evt_done. reflexivity.
Qed.

Lemma hp_w2n : forall (S1 F : Z) (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w200 w208 w216 w224 w232 w240 Fr fc (m : mem),
ra = Z_to_bv 64 0x97114 -> 0 <= S1 < 2^62 ->
rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 (Z_to_bv 64 (F + 8400))
w200 w208 w216 w224 w232 w240) ->
mem_inv bsegs m ->
evt bsegs (fun ms => ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 (F + 8400)) s11
t3 t4 t5 t6) Fr (Z_to_bv 64 0x9744c) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> S1R SP MI. unfold hsp in SP.
replace (ret_pc (Z_to_bv 64 0x97114)) with (Z_to_bv 64 0x97114) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0x9744c. apply evt_done. reflexivity.
Qed.

Lemma hp_w2 : forall (S1 F v : Z) (junk28 : list byte) (hd : spx_header) (w1 w2 w3 r1 r2 : word)
(ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w128 w136 w144 w152 w160 w168 w176 w200 w208 w216 w224 w232 w240 Fr fc (m : mem),
ra = Z_to_bv 64 0x97114 -> 0 <= S1 < 2^62 -> 0 < v -> v mod 8 = 0 -> v + 80 <= S1 -> 0 <= hd_mode hd < 3 ->
aobj bsegs m v 80 -> rw_cells bsegs m v (spx_header_cells junk28 hd w1 w2 w3 r1 r2) ->
rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 (Z_to_bv 64 SHB) w128 w136 w144 w152 w160 w168 w176
(Z_to_bv 64 (F + 8384)) (Z_to_bv 64 (F + 8400)) w200 w208 w216 w224 w232 w240) ->
lib_consts m -> mem_inv bsegs m ->
evt bsegs (fun ms =>
(hd_mode hd = 0 /\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 A_speex_nb_mode) (Z_to_bv 64 2) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SHB) s3 s4 (Z_to_bv 64 v) s6 s7 s8 (Z_to_bv 64 (F + 8384)) (Z_to_bv 64 (F + 8400)) s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0x9716c) fc None m (seg_rom bsegs))
\/ (hd_mode hd <> 0 /\ ms = MS (mkR (Z_to_bv 64 0x97158) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 (hd_mode hd)) (Z_to_bv 64 2) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SHB) s3 s4 (Z_to_bv 64 v) s6 s7 s8 (Z_to_bv 64 (F + 8384)) (Z_to_bv 64 (F + 8400)) s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_lib_get_mode_h) fc None m (seg_rom bsegs)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> S1R V0 V8 VS HM OB HC SP LC MI. unfold hsp in SP. unfold spx_header_cells, wz in HC. unfold A_lib_get_mode_h.
replace (ret_pc (Z_to_bv 64 0x97114)) with (Z_to_bv 64 0x97114) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [] m) as MU. assert (OF : offsh []) by exact I.
assert (V4 : v mod 4 = 0) by (clear - V8; Z.div_mod_to_equations; lia).
astep. astep. rewrite (bv_eqb_lit_ne_hb v 0) by lia. cbn iota.
bato 0x97144.
ato 0x9714c. rewrite ?h_sx32_lit_hb by lia. astep.
rewrite bv_ltu_Z, (unsigned_lit 2), (unsigned_lit (hd_mode hd)) by lia. replace (2 <? hd_mode hd) with false by (symmetry; apply Z.ltb_ge; lia). cbn iota.
destruct (Z.eq_dec (hd_mode hd) 0) as [M0|MN].
- rewrite M0. pose proof (lib_const m GOT_f41f0 LC_GOT_f41f0 LC ltac:(lc_in)) as G1. unfold GOT_f41f0, LC_GOT_f41f0 in G1.
ato 0x9716c. apply evt_done. left. split; reflexivity.
- astep. rewrite (bv_eqb_lit_ne_hb (hd_mode hd) 0) by lia. cbn iota.
ato 0xb5708. apply evt_done. right. split; [exact MN| reflexivity].
Qed.

Lemma bv_eqb_same_hb : forall x : word, bv_eqb x x = true.
Proof. intros x. unfold bv_eqb. apply Z.eqb_refl. Qed.

Lemma hp_w2g : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (m : mem),
ra = Z_to_bv 64 0x97158 -> mem_inv bsegs m ->
evt bsegs (fun ms => ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0x9716c) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> MI.
replace (ret_pc (Z_to_bv 64 0x97158)) with (Z_to_bv 64 0x97158) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0x9716c. apply evt_done. reflexivity.
Qed.

Lemma hp_w3 : forall (v : Z) (mo : spx_mode) (junk28 : list byte) (hd : spx_header) (w1 w2 w3 r1 r2 : word)
(ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (m : mem),
0 < v -> v mod 8 = 0 -> v + 80 <= 2^62 -> s2 = Z_to_bv 64 SHB ->
-2^31 <= hd_speex_version_id hd < 2^31 -> -2^31 <= hd_mode_bitstream_version hd < 2^31 ->
aobj bsegs m v 80 -> rw_cells bsegs m v (spx_header_cells junk28 hd w1 w2 w3 r1 r2) ->
aobj bsegs m (mode_addr mo) 32 -> lib_consts m -> mem_inv bsegs m ->
evt bsegs (fun ms => exists a1' a2' a3' : word,
((1 < hd_speex_version_id hd \/ hd_mode_bitstream_version hd <> 4)
/\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (mode_addr mo)) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 v) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0x97444) fc None m (seg_rom bsegs))
\/ (hd_speex_version_id hd <= 1 /\ hd_mode_bitstream_version hd = 4
/\ ms = MS (mkR (Z_to_bv 64 0x971d0) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (mode_addr mo)) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 v) s6 s7 s8 s9 s10 s11
t3 t4 t5 t6) Fr (Z_to_bv 64 A_decoder_init_h) fc None m (seg_rom bsegs)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (mode_addr mo)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 v) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0x9716c) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros V0 V8 VS -> VR BR OB HC OBM LC MI. unfold spx_header_cells, wz in HC. unfold A_decoder_init_h.
pose proof (munch_refl [] m) as MU. assert (OF : offsh []) by exact I.
assert (MD : ro_cells bsegs m (mode_addr mo) (match mo with ModeNB => LC_speex_nb_mode | ModeWB => LC_speex_wb_mode | ModeUWB => LC_speex_uwb_mode end)).
{ destruct mo; apply (lib_const m); [exact LC| lc_in| exact LC| lc_in| exact LC| lc_in]. }
assert (M8 : mode_addr mo mod 8 = 0) by (destruct mo; reflexivity).
destruct mo; unfold mode_addr in *; cbn [LC_speex_nb_mode LC_speex_wb_mode LC_speex_uwb_mode] in MD; unfold LC_speex_nb_mode, LC_speex_wb_mode, LC_speex_uwb_mode in MD;
unfold A_speex_nb_mode, A_speex_wb_mode, A_speex_uwb_mode in *.
all: ato 0x97188.
all: rewrite h_sx32_lit_hb by lia; astep; rewrite lts_lit_hb by lia.
all: destruct (Z.ltb_spec 1 (hd_speex_version_id hd)) as [VB|VG];
[ ato 0x97444; apply evt_done; do 3 eexists; left; split; [left; exact VB| reflexivity]
| bato 0x971c8 ].
all: rewrite (h_sx32_lit_hb 4), (h_sx32_lit_hb (hd_mode_bitstream_version hd)) by lia; astep.
all: destruct (Z.eq_dec 4 (hd_mode_bitstream_version hd)) as [EQ|NE];
[ rewrite <- EQ, bv_eqb_same_hb; cbn [negb];
ato 0x9896c; apply evt_done; do 3 eexists; right; split; [lia|]; split; [lia| reflexivity]
| rewrite (bv_eqb_lit_ne_hb 4 (hd_mode_bitstream_version hd)) by lia; cbn [negb];
ato 0x97444; apply evt_done; do 3 eexists; left; split; [right; lia| reflexivity] ].
Qed.

Lemma hp_w4 : forall (S1 F D : Z) (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 Fr fc (m : mem),
ra = Z_to_bv 64 0x971d0 -> 0 <= S1 < 2^62 -> 0 < D < 2^62 ->
rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 (Z_to_bv 64 (F + 32)) w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208
w216 w224 w232 w240) ->
mem_inv bsegs m ->
evt bsegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x971e4) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 D) (Z_to_bv 64 0) (Z_to_bv 64 (F + 32)) a3 a4 a5 a6 a7
(Z_to_bv 64 D) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_ctl_h) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> S1R D0 SP MI. unfold hsp in SP. unfold A_ctl_h.
replace (ret_pc (Z_to_bv 64 0x971d0)) with (Z_to_bv 64 0x971d0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
astep. rewrite (bv_eqb_lit_ne_hb D 0) by lia. cbn iota.
ato 0x98c74. apply evt_done. reflexivity.
Qed.

Lemma hp_w5 : forall (S1 F D : Z) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 Fr fc (m : mem),
ra = Z_to_bv 64 0x971e4 -> 0 <= S1 < 2^62 -> S1 + 248 <= SH_LO \/ SH_HI <= S1 ->
rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208
w216 w224 w232 w240) ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists m1 : mem,
munch [(S1, S1 + 248)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208
(Z_to_bv 64 D) w224 w232 w240)
/\ ms = MS (mkR (Z_to_bv 64 0x971f8) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 D) (Z_to_bv 64 3) (Z_to_bv 64 (F + 8384)) a3 a4 a5 a6 a7
(Z_to_bv 64 D) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (F + 8384)) s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_ctl_h) fc None m1 (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 D) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (F + 8384)) s10 s11 t3 t4 t5 t6)
Fr (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> S1R SSH SP MI. unfold hsp in SP. unfold A_ctl_h.
replace (ret_pc (Z_to_bv 64 0x971e4)) with (Z_to_bv 64 0x971e4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(S1, S1 + 248)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(S1, S1 + 248)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
ato 0x98c74. apply evt_done. eexists. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact SP| reflexivity].
Qed.

Lemma hp_w6 : forall (S1 F D v fs rate0 : Z) (junk28 : list byte) (hd : spx_header) (w1 w2 w3 r1 r2 : word)
(ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w80 w88 w96 w104 w112 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w224 w232 w240 Fr fc (m : mem),
ra = Z_to_bv 64 0x971f8 -> 0 <= S1 < 2^62 -> 0 < F -> F + 16384 <= S1 -> (F + 16384 <= SH_LO \/ SH_HI <= F) -> S1 + 248 <= SH_LO \/ SH_HI <= S1 ->
0 < v -> v mod 8 = 0 -> v + 80 <= S1 ->
-2^31 <= fs < 2^31 -> -2^31 <= rate0 < 2^31 -> -2^31 <= hd_rate hd < 2^31 ->
rw_cells bsegs m (F + 8384) [C4 (Z_to_bv 64 fs)] -> rw_cells bsegs m (F + 9232) [C4 (Z_to_bv 64 rate0)] ->
aobj bsegs m v 80 -> rw_cells bsegs m v (spx_header_cells junk28 hd w1 w2 w3 r1 r2) ->
rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 (Z_to_bv 64 (F + 9232)) (Z_to_bv 64 (F + 48)) w80 w88 w96 w104 w112 (Z_to_bv 64 SHB) w128 w136 w144 w152
w160 w168 w176 w184 w192 w200 w208 (Z_to_bv 64 D) w224 w232 w240) ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (a0' a1' a2' : word),
munch [(S1, S1 + 248); (F + 9232, F + 9236)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 (Z_to_bv 64 (F + 9232)) (Z_to_bv 64 (F + 48)) (Z_to_bv 64 fs) w88 w96 w104 w112 (Z_to_bv 64 SHB)
w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 (Z_to_bv 64 D) w224 w232 w240)
/\ ((~ (0 <= fs <= 640)
/\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0' a1' a2' a3 a4 a5 a6 a7 (Z_to_bv 64 D) s3 s4 (Z_to_bv 64 v) s6 s7 s8 (Z_to_bv 64 (F + 48)) s10 s11
t3 t4 t5 t6) Fr (Z_to_bv 64 0x97438) fc None m1 (seg_rom bsegs))
\/ (0 <= fs <= 640
/\ rw_cells bsegs m1 (F + 9232) [C4 (Z_to_bv 64 (if rate0 =? 0 then hd_rate hd else rate0))]
/\ ms = MS (mkR (Z_to_bv 64 0x97244) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 D) (Z_to_bv 64 24) (Z_to_bv 64 (F + 9232)) a3 a4 a5 a6 a7
(Z_to_bv 64 SHB) s3 s4 (Z_to_bv 64 v) s6 s7 s8 (Z_to_bv 64 (F + 48)) s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_ctl_h) fc None m1 (seg_rom bsegs))))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 D) s3 s4 (Z_to_bv 64 v) s6 s7 s8 (Z_to_bv 64 (F + 8384)) s10 s11 t3 t4 t5 t6)
Fr (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> S1R F0 FS1 FSH SSH V0 V8 VS FR RR HRR FSZ RATE OB HC SP MI. unfold hsp in SP. unfold spx_header_cells, wz in HC. unfold A_ctl_h.
replace (ret_pc (Z_to_bv 64 0x971f8)) with (Z_to_bv 64 0x971f8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(S1, S1 + 248); (F + 9232, F + 9236)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(S1, S1 + 248); (F + 9232, F + 9236)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
ato 0x9720c.
rewrite !(h_sx32_lit_hb fs) in * by lia. astep. rewrite bv_ltu_Z, (unsigned_lit 640) by lia.
destruct (Z_le_dec 0 fs) as [FB0|FBN]; [destruct (Z_le_dec fs 640) as [FB1|FBN]|].
3: { replace (640 <? bv_unsigned (Z_to_bv 64 fs)) with true by (symmetry; apply Z.ltb_lt; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2^64); Z.div_mod_to_equations; lia). cbn iota.
ato 0x97438. apply evt_done. do 4 eexists. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact SP|]. left. split; [lia| reflexivity]. }
2: { replace (640 <? bv_unsigned (Z_to_bv 64 fs)) with true by (symmetry; apply Z.ltb_lt; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2^64); Z.div_mod_to_equations; lia). cbn iota.
ato 0x97438. apply evt_done. do 4 eexists. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact SP|]. left. split; [lia| reflexivity]. }
rewrite (unsigned_lit fs) by lia. replace (640 <? fs) with false by (symmetry; apply Z.ltb_ge; lia). cbn iota.
ato 0x97218. rewrite !(h_sx32_lit_hb rate0) in * by lia. astep.
destruct (Z.eq_dec rate0 0) as [R0|RN].
- subst rate0. rewrite bv_eqb_same_hb. cbn [negb].
ato 0x97234. rewrite !(h_sx32_lit_hb (hd_rate hd)) in * by lia.
ato 0x98c74. apply evt_done. eexists. exists (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0). split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact SP|].
right. split; [lia|]. split; [cbn [Z.eqb]; exact RATE| reflexivity].
- rewrite (bv_eqb_lit_ne_hb rate0 0) by lia. cbn [negb].
ato 0x98c74. apply evt_done. eexists. exists (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0). split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact SP|].
right. split; [lia|]. split; [replace (rate0 =? 0) with false by (symmetry; apply Z.eqb_neq; exact RN); exact RATE| reflexivity].
Qed.

Lemma hp_w7 : forall (S1 F sf D v ch0 : Z) (junk28 : list byte) (hd : spx_header) (w1 w2 w3 r1 r2 : word)
(ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s8 s10 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w224 w232 w240 c48 c52 c56 c64 Fr fc (m : mem),
ra = Z_to_bv 64 0x97244 -> 0 <= S1 < 2^62 -> SEGTOP_A <= F -> F + 16384 <= S1 -> (F + 16384 <= SH_LO \/ SH_HI <= F) -> S1 + 248 <= SH_LO \/ SH_HI <= S1 ->
sf = shad F -> 0 <= sf < 2^62 -> F mod 64 = 0 -> sf + 16 <= S1 -> (sf + 16 <= F \/ F + 16384 <= sf) ->
0 < v -> v mod 8 = 0 -> v + 80 <= S1 ->
-2^31 <= hd_frames_per_packet hd < 2^31 -> -2^31 <= ch0 < 2^31 -> 1 <= hd_nb_channels hd <= 2 ->
aobj bsegs m v 80 -> rw_cells bsegs m v (spx_header_cells junk28 hd w1 w2 w3 r1 r2) ->
rw_cells bsegs m S1 (hsp w0 w8 w16 w24 (Z_to_bv 64 (F + 64)) w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 (Z_to_bv 64 SHB) (Z_to_bv 64 (F + 9168)) w136 w144 w152
w160 w168 w176 w184 w192 w200 w208 (Z_to_bv 64 D) w224 w232 w240) ->
rw_cells bsegs m (F + 48) [C4 c48; C4 c52; C8 c56; C8 c64] -> rw_cells bsegs m sf [CB 16 HSH_L_HDR] ->
lib_consts m -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (a0' a1' a2' : word),
munch [(S1, S1 + 248); (F + 48, F + 72)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 S1 (hsp w0 w8 w16 w24 (Z_to_bv 64 (F + 64)) w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 (Z_to_bv 64 SHB) (Z_to_bv 64 (F + 9168)) w136 w144
w152 w160 w168 w176 w184 w192 (Z_to_bv 64 (hd_frames_per_packet hd)) w208 (Z_to_bv 64 D) w224 w232 w240)
/\ rw_cells bsegs m1 sf [CB 16 HSH_L_HDR]
/\ ((~ (1 <= hd_frames_per_packet hd <= 10) /\ rw_cells bsegs m1 (F + 48) [C4 c48; C4 c52; C8 c56; C8 c64]
/\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0' a1' a2' a3 a4 a5 a6 a7 (Z_to_bv 64 SHB) s3 s4 (Z_to_bv 64 v) s6 s7 s8 (Z_to_bv 64 (F + 48)) s10
(Z_to_bv 64 ch0) t3 t4 t5 t6) Fr (Z_to_bv 64 0x97438) fc None m1 (seg_rom bsegs))
\/ (1 <= hd_frames_per_packet hd <= 10 /\ (if ch0 =? -1 then hd_nb_channels hd else ch0) = 1
/\ rw_cells bsegs m1 (F + 48) [C4 c48; C4 c52; C8 c56; C8 c64]
/\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 1) a1' a2' a3 a4 a5 a6 a7 (Z_to_bv 64 SHB) s3 s4 (Z_to_bv 64 v) s6 s7 s8
(Z_to_bv 64 (F + 48)) s10 (Z_to_bv 64 1) t3 t4 t5 t6) Fr (Z_to_bv 64 0x972e4) fc None m1 (seg_rom bsegs))
\/ (1 <= hd_frames_per_packet hd <= 10 /\ (if ch0 =? -1 then hd_nb_channels hd else ch0) <> 1
/\ rw_cells bsegs m1 (F + 48) [C4 (Z_to_bv 64 9); C4 c52; C8 (Z_to_bv 64 0x991f0); C8 (Z_to_bv 64 (F + 9168))]
/\ ms = MS (mkR (Z_to_bv 64 0x972e0) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 D) (Z_to_bv 64 20) (Z_to_bv 64 (F + 48)) a3 a4 a5 a6 a7
(Z_to_bv 64 SHB) s3 s4 (Z_to_bv 64 v) s6 s7 s8 (Z_to_bv 64 (F + 48)) s10 (Z_to_bv 64 1) t3 t4 t5 t6) Fr (Z_to_bv 64 A_ctl_h) fc None m1 (seg_rom bsegs))))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 SHB) s3 s4 (Z_to_bv 64 v) s6 s7 s8 (Z_to_bv 64 (F + 48)) s10 (Z_to_bv 64 ch0)
t3 t4 t5 t6) Fr (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> S1R F0 FS1 FSH SSH ESF SFR F64 SFS SFF V0 V8 VS FPR CHR NCR OB HC SP CB SH LC MI. unfold SEGTOP_A in F0.
unfold hsp in SP. unfold spx_header_cells, wz in HC. unfold A_ctl_h.
replace (ret_pc (Z_to_bv 64 0x97244)) with (Z_to_bv 64 0x97244) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(S1, S1 + 248); (F + 48, F + 72)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(S1, S1 + 248); (F + 48, F + 72)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
pose proof (lib_const m GOT_f41b8 LC_GOT_f41b8 LC ltac:(lc_in)) as G2. unfold GOT_f41b8, LC_GOT_f41b8 in G2.
assert (EAD : Z.shiftr (F + 64) 3 + SHB = sf + 8).
{ rewrite ESF. unfold shad. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
replace (F + 64) with (F + 8 * 8) by lia. rewrite Z.div_add by lia. lia. }
ato 0x97268.
rewrite !(h_sx32_lit_hb (hd_frames_per_packet hd)) in * by lia. rewrite ?unsigned_lit_wrap.
astep. destruct (Z_le_dec 1 (hd_frames_per_packet hd)) as [FP1|FPN]; [destruct (Z_le_dec (hd_frames_per_packet hd) 10) as [FP2|FPN]|].
2,3: (replace (bv_ltu (Z_to_bv 64 (bv_swrap 32 (hd_frames_per_packet hd mod 18446744073709551616 + -11))) (Z_to_bv 64 (-10))) with true
by (symmetry; rewrite bv_ltu_Z, !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2^64); rewrite h_swrap32_eq_hb; apply Z.ltb_lt; Z.div_mod_to_equations; lia);
cbn iota; ato 0x97438; apply evt_done; do 4 eexists; split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [exact SP|]; split; [exact SH|];
left; split; [lia|]; split; [exact CB| reflexivity]).
rewrite (Z.mod_small (hd_frames_per_packet hd) 18446744073709551616) by lia. rewrite swrap32_small_hb by lia.
replace (bv_ltu (Z_to_bv 64 (hd_frames_per_packet hd + -11)) (Z_to_bv 64 (-10))) with false
by (symmetry; rewrite bv_ltu_Z, !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2^64); apply Z.ltb_ge; Z.div_mod_to_equations; lia).
cbn iota. ato 0x97270. astep.
destruct (Z.eq_dec ch0 (-1)) as [C0|CN].
2: { rewrite (bv_eqb_lit_ne_hb ch0 (-1)) by lia. cbn [negb]. ato 0x97298. astep.
destruct (Z.eq_dec ch0 1) as [C1|C2].
- subst ch0. rewrite bv_eqb_same_hb. cbn iota. ato 0x972e4. apply evt_done. eexists. exists (Z_to_bv 64 0). do 2 eexists. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact SP|]. split; [exact SH|].
right; left. split; [lia|]. split; [reflexivity|]. split; [exact CB| reflexivity].
- rewrite (bv_eqb_lit_ne_hb ch0 1) by lia. cbn iota. ato 0x972c0. rewrite EAD. astep. ato 0x98c74.
apply evt_done. eexists. exists (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0). split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
split; [exact SP|]. split; [exact SH|].
right; right. split; [lia|]. split; [replace (ch0 =? -1) with false by (symmetry; apply Z.eqb_neq; exact CN); exact C2|]. split; [exact CB| reflexivity]. }

subst ch0. rewrite bv_eqb_same_hb. cbn [negb]. ato 0x97290. rewrite !(h_sx32_lit_hb (hd_nb_channels hd)) in * by lia. ato 0x97298. astep.
destruct (Z.eq_dec (hd_nb_channels hd) 1) as [C1|C2].
- rewrite C1 in *. rewrite bv_eqb_same_hb. cbn iota. ato 0x972e4. apply evt_done. eexists. exists (Z_to_bv 64 0). do 2 eexists. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact SP|]. split; [exact SH|].
right; left. split; [lia|]. split; [reflexivity|]. split; [exact CB| reflexivity].
- rewrite (bv_eqb_lit_ne_hb (hd_nb_channels hd) 1) by lia. cbn iota. ato 0x972c0. rewrite EAD. astep. ato 0x98c74.
apply evt_done. eexists. exists (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0). split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
split; [exact SP|]. split; [exact SH|].
right; right. split; [lia|]. split; [cbn [Z.eqb]; exact C2|]. split; [exact CB| reflexivity].
Qed.

Lemma hp_w8r : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (m : mem),
ra = Z_to_bv 64 0x972e0 -> mem_inv bsegs m ->
evt bsegs (fun ms => ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 2) t3 t4 t5 t6)
Fr (Z_to_bv 64 0x972e4) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> MI.
replace (ret_pc (Z_to_bv 64 0x972e0)) with (Z_to_bv 64 0x972e0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0x972e4. apply evt_done. reflexivity.
Qed.

Lemma hp_w8 : forall (S1 v : Z) (junk28 : list byte) (hd : spx_header) (w1 w2 w3 r1 r2 : word)
(ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 Fr fc (m : mem),
0 <= S1 < 2^62 -> S1 + 248 <= SH_LO \/ SH_HI <= S1 ->
0 < v -> v mod 8 = 0 -> v + 80 <= S1 ->
-2^31 <= hd_extra_headers hd < 2^31 ->
aobj bsegs m v 80 -> rw_cells bsegs m v (spx_header_cells junk28 hd w1 w2 w3 r1 r2) ->
rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 (Z_to_bv 64 SHB) w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208
w216 w224 w232 w240) ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (a0' a1' a2' : word),
munch [(S1, S1 + 248)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 (Z_to_bv 64 (hd_extra_headers hd)) w112 (Z_to_bv 64 SHB) w128 w136 w144 w152
w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240)
/\ ((hd_extra_headers hd = 2^31 - 1
/\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0' a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 v) s6 (Z_to_bv 64 0x7fffffff) s8 s9 s10 s11
t3 t4 t5 t6) Fr (Z_to_bv 64 0x97438) fc None m1 (seg_rom bsegs))
\/ (hd_extra_headers hd <> 2^31 - 1
/\ ms = MS (mkR (Z_to_bv 64 0x97310) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 v) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 v) s6
(Z_to_bv 64 0x7fffffff) s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_free_hp) fc None m1 (seg_rom bsegs))))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 v) s6 (Z_to_bv 64 0x7fffffff) s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0x972e4) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros S1R SSH V0 V8 VS XR OB HC SP MI. unfold hsp in SP. unfold spx_header_cells, wz in HC. unfold A_free_hp.
pose proof (munch_refl [(S1, S1 + 248)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(S1, S1 + 248)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
ato 0x97304.
rewrite !(h_sx32_lit_hb (hd_extra_headers hd)) in * by lia.
astep.
destruct (Z.eq_dec (hd_extra_headers hd) (2^31 - 1)) as [XE|XN].
- rewrite XE in *. cbn iota.
ato 0x97438. apply evt_done. do 4 eexists. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact SP|].
left. split; [reflexivity| reflexivity].
- rewrite (bv_eqb_lit_ne_hb (hd_extra_headers hd) 2147483647) by lia. cbn iota.
ato 0x67f80. apply evt_done. eexists. exists (Z_to_bv 64 0). do 2 eexists. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact SP|].
right. split; [exact XN| reflexivity].
Qed.

Lemma hp_w9 : forall (S1 F sf D : Z) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w184 w192 w200 w208 w224 w232 w240 Fr fc (m : mem),
ra = Z_to_bv 64 0x97310 -> 0 <= S1 < 2^62 -> 0 <= sf < 2^62 -> sf + 16 <= S1 ->
rw_cells bsegs m sf [CB 16 HSH_L_HDR] ->
rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 (Z_to_bv 64 (F + 9248)) w184
w192 w200 w208 (Z_to_bv 64 D) w224 w232 w240) ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists m1 : mem,
ms = MS (mkR (Z_to_bv 64 0x97338) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 D) (Z_to_bv 64 39) (Z_to_bv 64 (F + 9248)) a3 a4 a5 a6 a7
s2 (Z_to_bv 64 sf) s4 s5 (Z_to_bv 64 (-8)) s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_ctl_h) fc None m1 (seg_rom bsegs)
/\ munch [(sf, sf + 16)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ rw_cells bsegs m1 sf [CB 16 HSH_P1])
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 sf) s4 s5 (Z_to_bv 64 (-8)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> S1R SFR SFS SH SP MI. unfold hsp in SP. unfold A_ctl_h.
replace (ret_pc (Z_to_bv 64 0x97310)) with (Z_to_bv 64 0x97310) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(sf, sf + 16)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
hsh_start SH.
ato 0x98c74.
hsh_lit0 SH HSH_P1 ltac:(unfold HSH_L_HDR, HSH_P1).
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact SH].
Qed.

Lemma hp_w10 : forall (S1 pc0 os og : Z) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 Fr fc (m : mem),
ra = Z_to_bv 64 0x97338 -> 0 <= S1 < 2^62 -> 0 <= pc0 < 2^31 - 1 ->
rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 (Z_to_bv 64 og) (Z_to_bv 64 os) w160 w168 w176 w184
w192 w200 w208 w216 w224 w232 w240) ->
mem_inv bsegs m ->
evt bsegs (fun ms => ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 (pc0 + 1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (pc0 + 1)) (Z_to_bv 64 0) s6
(Z_to_bv 64 os) s8 (Z_to_bv 64 og) s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_KH) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 pc0) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> S1R PR SP MI. unfold hsp in SP. unfold A_KH.
replace (ret_pc (Z_to_bv 64 0x97338)) with (Z_to_bv 64 0x97338) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0x9734c.
rewrite (swrap32_small_hb (pc0 + 1)) by lia. astep. rewrite lts_lit_hb by lia. replace (pc0 + 1 <? pc0) with false by (symmetry; apply Z.ltb_ge; lia). cbn iota.
ato 0x96f10. apply evt_done. reflexivity.
Qed.

Lemma hp_f1 : forall (S1 D : Z) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w224 w232 w240 Fr fc (m : mem),
0 <= S1 < 2^62 ->
rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208
(Z_to_bv 64 D) w224 w232 w240) ->
mem_inv bsegs m ->
evt bsegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x97440) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6) Fr (Z_to_bv 64 A_destroy_hp) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x97438) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros S1R SP MI. unfold hsp in SP. unfold A_destroy_hp.
ato 0x98a30. apply evt_done. reflexivity.
Qed.

Lemma hp_f2 : forall (S1 bits : Z) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w200 w208 w216 w224 w232 w240 Fr fc (m : mem),
ra = Z_to_bv 64 0x97440 -> 0 <= S1 < 2^62 ->
rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 (Z_to_bv 64 bits)
w200 w208 w216 w224 w232 w240) ->
mem_inv bsegs m ->
evt bsegs (fun ms => ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 bits) s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0x97444) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> S1R SP MI. unfold hsp in SP.
replace (ret_pc (Z_to_bv 64 0x97440)) with (Z_to_bv 64 0x97440) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0x97444. apply evt_done. reflexivity.
Qed.

Lemma hp_f3 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (m : mem),
mem_inv bsegs m ->
evt bsegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x9744c) sp gp tp t0 t1 t2 s0 s1 s5 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_free_hp) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x97444) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros MI. unfold A_free_hp.
ato 0x67f80. apply evt_done. reflexivity.
Qed.

Lemma hp_f4 : forall (sf : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (m : mem),
0 <= sf < 2^62 -> rw_cells bsegs m sf [CB 16 HSH_L_HDR] -> mem_inv bsegs m ->
evt bsegs (fun ms => exists m1 : mem,
ms = MS (mkR (Z_to_bv 64 0x97470) sp gp tp t0 t1 t2 s0 s1 s10 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 sf) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_bdes_hp) fc None m1 (seg_rom bsegs)
/\ munch [(sf, sf + 16)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ rw_cells bsegs m1 sf [CB 16 HSH_P1])
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 sf) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x9744c) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SFR SH MI. unfold A_bdes_hp.
pose proof (munch_refl [(sf, sf + 16)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
hsh_start SH.
ato 0x97904.
hsh_lit0 SH HSH_P1 ltac:(unfold HSH_L_HDR, HSH_P1).
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact SH].
Qed.

Lemma hp_f5 : forall (S1 os : Z) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 Fr fc (m : mem),
ra = Z_to_bv 64 0x97470 -> 0 <= S1 < 2^62 ->
rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 (Z_to_bv 64 os) w160 w168 w176 w184
w192 w200 w208 w216 w224 w232 w240) ->
mem_inv bsegs m ->
evt bsegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x97478) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 os) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6) Fr (Z_to_bv 64 A_sclr_hp) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> S1R SP MI. unfold hsp in SP. unfold A_sclr_hp.
replace (ret_pc (Z_to_bv 64 0x97470)) with (Z_to_bv 64 0x97470) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0xc1294. apply evt_done. reflexivity.
Qed.

Lemma hp_f6 : forall (S1 oy : Z) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 Fr fc (m : mem),
ra = Z_to_bv 64 0x97478 -> 0 <= S1 < 2^62 ->
rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 (Z_to_bv 64 oy) w120 w128 w136 w144 w152 w160 w168 w176 w184
w192 w200 w208 w216 w224 w232 w240) ->
mem_inv bsegs m ->
evt bsegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x97480) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 oy) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6) Fr (Z_to_bv 64 A_yclr_hp) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> S1R SP MI. unfold hsp in SP. unfold A_yclr_hp.
replace (ret_pc (Z_to_bv 64 0x97478)) with (Z_to_bv 64 0x97478) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0xc166c. apply evt_done. reflexivity.
Qed.

Lemma hp_f7 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (m : mem),
ra = Z_to_bv 64 0x97480 -> mem_inv bsegs m ->
evt bsegs (fun ms => ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_XT) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> MI. unfold A_XT.
replace (ret_pc (Z_to_bv 64 0x97480)) with (Z_to_bv 64 0x97480) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0x974b0. apply evt_done. reflexivity.
Qed.
