(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Znumtheory.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1dk X1cs X1dg X1df X1ck X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1od.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X09u X071.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b X0z5 X14x X110 X105 X10j X0xn.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Notation mem := (word -> option byte).
Definition A_KP : Z := 0x96f2c.
Definition A_SS : Z := 0x96f54.
Definition A_HP : Z := 0x970e0.
Definition A_KT : Z := 0x97348.
Definition A_DT : Z := 0x9701c.
Definition A_SPEEX_LIT : Z := 0x232e0.
Definition A_speex_bits_read_from_h : Z := 0x97988.
Definition A_speex_decode_h : Z := 0x98c00.
Definition A_speex_bits_remaining_h : Z := 0x98808.
Definition A_speex_decode_stereo_h : Z := 0x98edc.

Lemma packetout_r_range : forall (os : stream_st bptr) r opo os', ogg_stream_packetout os = Some ((r, opo), os') -> r = 0 \/ r = -1 \/ r = 1.
Proof.
intros os r opo os' E. unfold ogg_stream_packetout, packetout in E.
destruct (ogg_stream_check os); [injection E as <- _ _; left; reflexivity|].
destruct (_ <=? _); [injection E as <- _ _; left; reflexivity|].
destruct (negb _); [injection E as <- _ _; right; left; reflexivity|].
destruct (gather255 _ _ _ _ _) as [[[n eos] bytes]|]; [injection E as <- _ _; right; right; reflexivity| discriminate E].
Qed.

Lemma bv_eqb_lit_ne_k : forall r k, -2^63 <= r < 2^63 -> -2^63 <= k < 2^63 -> r <> k -> bv_eqb (Z_to_bv 64 r) (Z_to_bv 64 k) = false.
Proof.
intros r k Hr Hk NE. unfold bv_eqb. apply Z.eqb_neq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
intros E. Z.div_mod_to_equations. nia.
Qed.
Lemma bv_eqb_same_k : forall x : word, bv_eqb x x = true.
Proof. intros x. unfold bv_eqb. apply Z.eqb_refl. Qed.
Lemma lts_lit_k : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_lts. rewrite !signed_lit_small by lia. reflexivity. Qed.
Lemma swrap32_eq_k : forall z, bv_swrap 32 z = (z + 2147483648) mod 4294967296 - 2147483648.
Proof. reflexivity. Qed.
Lemma sx32_lit_k : forall e, (-2^31 <= e < 2^31)%Z -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap, swrap32_eq_k.
change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.
Lemma swrap32_small_k : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 x = x.
Proof. intros x Hx. rewrite swrap32_eq_k. rewrite Z.mod_small by lia. lia. Qed.

Lemma kh_w0 : forall (S1 F : Z) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 Fr fc (m : mem),
0 <= S1 < 2^62 ->
rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 (Z_to_bv 64 (F + 8608)) w168 w176 w184 w192 w200 w208 w216 w224 w232 w240) ->
mem_inv bsegs m ->
evt bsegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x96f20) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 (F + 8688)) (Z_to_bv 64 (F + 8608)) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (F + 8608)) s3 s4 s5 s6 (Z_to_bv 64 (F + 8688)) s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_ogg_stream_packetout) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 (F + 8688)) s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_KH) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros S1R SP MI. unfold hsp in SP. unfold A_KH, A_ogg_stream_packetout.
ato 0xc1e74. apply evt_done. reflexivity.
Qed.

Lemma kh_w1 : forall (S1 r : Z) (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 Fr fc (m : mem),
ra = Z_to_bv 64 0x96f20 -> (r = 0 \/ r = -1 \/ r = 1) -> 0 <= S1 < 2^62 ->
rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240) ->
mem_inv bsegs m ->
evt bsegs (fun ms =>
(r <> 1 /\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 r) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7
s2 s3 s4 w168 s6 s7 s8 s9 (Z_to_bv 64 0) s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_PN) fc None m (seg_rom bsegs))
\/ (r = 1 /\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 1) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7
s2 s3 s4 w168 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_KP) fc None m (seg_rom bsegs)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> RR S1R SP MI. unfold hsp in SP. unfold A_PN, A_KP.
replace (ret_pc (Z_to_bv 64 0x96f20)) with (Z_to_bv 64 0x96f20) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0x96f28.
destruct RR as [-> | [-> | ->]].
- astep. try sh_if. ato 0x96ee8. apply evt_done. left. split; [lia| reflexivity].
- astep. try sh_if. ato 0x96ee8. apply evt_done. left. split; [lia| reflexivity].
- astep. try sh_if. apply evt_done. right. split; reflexivity.
Qed.

Lemma kh_w2 : forall (S1 F Bd : Z) (op : packet) (gw : word) (kc : list cell) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
Fr fc (m : mem),
0 <= S1 < 2^62 -> 0 <= pk_bytes op < 2^63 ->
rw_cells bsegs m (F + 8608) (op_cells Bd (Some op) gw kc) ->
mem_inv bsegs m ->
evt bsegs (fun ms =>
(pk_bytes op < 5 /\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 5) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (F + 8608)) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (pk_bytes op)) s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_SS) fc None m (seg_rom bsegs))
\/ (5 <= pk_bytes op /\ ms = MS (mkR (Z_to_bv 64 0x96f4c) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 (Bd + pk_off op)) (Z_to_bv 64 A_SPEEX_LIT) (Z_to_bv 64 5)
a3 a4 a5 a6 a7 (Z_to_bv 64 (F + 8608)) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (pk_bytes op)) s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 e_bcmp) fc None m (seg_rom bsegs)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (F + 8608)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_KP) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros S1R PB OPC MI. unfold op_cells, wz in OPC. unfold A_KP, A_SS, A_SPEEX_LIT, e_bcmp.
ato 0x96f34. astep. rewrite lts_lit_k by lia.
destruct (Z.ltb_spec (pk_bytes op) 5) as [LT|GE].
- ato 0x96f54. apply evt_done. left. split; [exact LT| reflexivity].
- ato 0x56ce0. apply evt_done. right. split; [exact GE| reflexivity].
Qed.

Lemma Z_to_le_bytes_app_h : forall n k z, 0 <= z ->
Z_to_le_bytes (n + k) z = Z_to_le_bytes n z ++ Z_to_le_bytes k (Z.shiftr z (8 * Z.of_nat n)).
Proof.
induction n as [|n IH]; intros k z Hz; cbn [Nat.add Z_to_le_bytes app].
- rewrite Z.shiftr_0_r. reflexivity.
- f_equal. rewrite IH by (apply Z.shiftr_nonneg; lia). rewrite Z.shiftr_shiftr by lia.
replace (8 + 8 * Z.of_nat n) with (8 * Z.of_nat (S n)) by lia. reflexivity.
Qed.
Lemma le8_split_hi : forall v : word, le8 v = le4 v ++ le4 (Z_to_bv 64 (Z.shiftr (bv_unsigned v) 32)).
Proof.
intros v. unfold le8, le4, word_to_le_bytes.
pose proof (bv_unsigned_in_range 64 v) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2^64) in R.
rewrite (unsigned_lit (Z.shiftr (bv_unsigned v) 32)).
2:{ rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
change 8%nat with (4 + 4)%nat. rewrite Z_to_le_bytes_app_h by lia. reflexivity.
Qed.
Lemma rw_cells_c8_split_hi : forall (m : mem) A pre post (v : word),
rw_cells bsegs m A (pre ++ C8 v :: post) -> rw_cells bsegs m A (pre ++ C4 v :: C4 (Z_to_bv 64 (Z.shiftr (bv_unsigned v) 32)) :: post).
Proof.
intros m A pre post v [[W B] R]. apply cells_wf_app in W. destruct W as [W1 [_ W2]].
split; [split|].
- apply cells_wf_app. split; [exact W1| split; [exact I| split; [exact I| exact W2]]].
- rewrite cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite le8_split_hi in B.
rewrite <- app_assoc in B. exact B.
- rewrite cells_size_app in *. cbn [cells_size csize] in *. exact R.
Qed.

Lemma kh_w3 : forall (S1 F Bd L Gv : Z) (hdr : list byte) (os : stream_st bptr) (v ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
Fr fc (m : mem),
ra = Z_to_bv 64 0x96f4c -> 0 <= S1 < 2^62 -> 0 < F -> stream_fields_ok os ->
rw_cells bsegs m (F + 8688) (stream_cells Bd L Gv hdr os) ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists s5' : word,
((bv_unsigned v <> 0 /\ s5' = s5) \/ (bv_unsigned v = 0 /\ s5' = Z_to_bv 64 (os_serialno os)))
/\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5' s6 (Z_to_bv 64 (F + 8688)) s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_SS) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 (F + 8688)) s8 s9 s10 s11 t3 t4 t5 t6)
Fr (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> S1R F0 FOK OS MI. unfold stream_cells, wz in OS. unfold A_SS.
replace (ret_pc (Z_to_bv 64 0x96f4c)) with (Z_to_bv 64 0x96f4c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof FOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SNR & _).
lazymatch type of OS with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?cs :: ?post) =>
change (rw_cells bsegs m (F + 8688) ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13] ++ cs :: post)) in OS end.
apply rw_cells_c8_split_hi in OS. cbn [app] in OS.
astep.
destruct (Z.eq_dec (bv_unsigned v) 0) as [V0|VN].
- replace (bv_eqb v (Z_to_bv 64 0)) with true by (symmetry; unfold bv_eqb; apply Z.eqb_eq; rewrite V0; reflexivity). cbn [negb].
ato 0x96f50. astep. rewrite sx32_lit_k by exact SNR.
apply evt_done. exists (Z_to_bv 64 (os_serialno os)). split; [right; split; [exact V0| reflexivity]| reflexivity].
- replace (bv_eqb v (Z_to_bv 64 0)) with false by (symmetry; unfold bv_eqb; apply Z.eqb_neq; rewrite (unsigned_lit 0) by lia; exact VN). cbn [negb].
ato 0x96f54.
apply evt_done. exists s5. split; [left; split; [exact VN| reflexivity]| reflexivity].
Qed.

Lemma swrap_mod64_plus1_k : forall x, -2^31 <= x < 2^31 - 1 -> bv_swrap 32 (x mod 18446744073709551616 + 1) = x + 1.
Proof.
intros x Hx. rewrite swrap32_eq_k.
assert (D : (4294967296 | 18446744073709551616)) by (exists 4294967296; reflexivity).
rewrite (Znumtheory.Zmod_div_mod 4294967296 18446744073709551616 (x mod 18446744073709551616 + 1 + 2147483648)) by (lia || exact D).
replace (x mod 18446744073709551616 + 1 + 2147483648) with (x mod 18446744073709551616 + (1 + 2147483648)) by lia.
rewrite Zplus_mod_idemp_l. replace (x + (1 + 2147483648)) with (x + 1 + 2147483648) by lia.
rewrite <- (Znumtheory.Zmod_div_mod 4294967296 18446744073709551616 (x + 1 + 2147483648)) by (lia || exact D).
rewrite Z.mod_small by lia. lia.
Qed.

Lemma kh_w4 : forall (S1 F Bd L Gv sser pc extra pno : Z) (hdr : list byte) (os : stream_st bptr) (op : packet) (gw : word) (kc : list cell)
(ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w112 w120 w128 w136 w152 w168 w176 w184 w200 w208 w216 w224 w232 w240 Fr fc (m : mem),
0 <= S1 < 2^62 -> 0 < F -> F + 16384 <= S1 -> stream_fields_ok os -> -2^31 <= sser < 2^31 ->
0 <= pc < 2^31 -> -2^31 <= extra < 2^31 - 1 -> 0 <= pno < 2^31 - 1 -> 0 <= pk_bytes op < 2^31 -> 0 <= pk_e_o_s op < 2^63 ->
rw_cells bsegs m (F + 8688) (stream_cells Bd L Gv hdr os) ->
rw_cells bsegs m (F + 8608) (op_cells Bd (Some op) gw kc) ->
rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 (Z_to_bv 64 extra) w112 w120 w128 w136 (Z_to_bv 64 (F + 8544)) w152 (Z_to_bv 64 (F + 8608))
w168 w176 w184 (Z_to_bv 64 (F + 8400)) w200 w208 w216 w224 w232 w240) ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
munch [(S1, S1 + 248)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ ((sser = -1
/\ rw_cells bsegs m1 S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 (Z_to_bv 64 extra) w112 w120 w128 w136 (Z_to_bv 64 (F + 8544)) w152
(Z_to_bv 64 (F + 8608)) (Z_to_bv 64 (-1)) w176 w184 (Z_to_bv 64 (F + 8400)) w200 w208 w216 w224 w232 w240)
/\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
s2 s3 (Z_to_bv 64 pc) (Z_to_bv 64 (-1)) s6 (Z_to_bv 64 (F + 8688)) (Z_to_bv 64 pno) (Z_to_bv 64 (F + 8544)) (Z_to_bv 64 0) s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_PN) fc None m1 (seg_rom bsegs))
\/ (sser <> -1 /\ os_serialno os <> sser
/\ rw_cells bsegs m1 S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 (Z_to_bv 64 extra) w112 w120 w128 w136 (Z_to_bv 64 (F + 8544)) w152
(Z_to_bv 64 (F + 8608)) (Z_to_bv 64 sser) w176 w184 (Z_to_bv 64 (F + 8400)) w200 w208 w216 w224 w232 w240)
/\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 (os_serialno os)) a1 a2 a3 a4 a5 a6 a7
s2 s3 (Z_to_bv 64 pc) (Z_to_bv 64 sser) s6 (Z_to_bv 64 (F + 8688)) (Z_to_bv 64 pno) (Z_to_bv 64 (F + 8544)) (Z_to_bv 64 0) s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_PN) fc None m1 (seg_rom bsegs))
\/ (sser <> -1 /\ os_serialno os = sser /\ pc = 0
/\ rw_cells bsegs m1 S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 (Z_to_bv 64 extra) w112 w120 w128 w136 (Z_to_bv 64 (F + 8544)) w152
(Z_to_bv 64 (F + 8608)) (Z_to_bv 64 sser) w176 w184 (Z_to_bv 64 (F + 8400)) w200 w208 w216 w224 w232 w240)
/\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 sser) a1 a2 a3 a4 a5 a6 a7
s2 s3 (Z_to_bv 64 pc) (Z_to_bv 64 sser) s6 (Z_to_bv 64 0x7fffffff) (Z_to_bv 64 pno) (Z_to_bv 64 (pk_bytes op)) s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_HP) fc None m1 (seg_rom bsegs))
\/ (sser <> -1 /\ os_serialno os = sser /\ pc <> 0 /\ pc <= 1 + extra
/\ rw_cells bsegs m1 S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 (Z_to_bv 64 extra) w112 w120 w128 w136 (Z_to_bv 64 (F + 8544)) w152
(Z_to_bv 64 (F + 8608)) (Z_to_bv 64 sser) w176 w184 (Z_to_bv 64 (F + 8400)) w200 w208 w216 w224 w232 w240)
/\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 (1 + extra)) (Z_to_bv 64 extra) a2 a3 a4 a5 a6 a7
s2 s3 (Z_to_bv 64 pc) (Z_to_bv 64 0) s6 (Z_to_bv 64 0x7fffffff) (Z_to_bv 64 pno) (Z_to_bv 64 (pk_bytes op)) s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_KT) fc None m1 (seg_rom bsegs))
\/ (sser <> -1 /\ os_serialno os = sser /\ pc <> 0 /\ 1 + extra < pc
/\ rw_cells bsegs m1 S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 (Z_to_bv 64 extra) w112 w120 w128 w136 (Z_to_bv 64 (F + 8544)) w152
(Z_to_bv 64 (F + 8608)) (Z_to_bv 64 sser) w176 w184 (Z_to_bv 64 (F + 8400)) w200 w208 w216 w224 w232 w240)
/\ ms = MS (mkR (Z_to_bv 64 0x96fa8) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 (F + 8400)) (Z_to_bv 64 (Bd + pk_off op)) (Z_to_bv 64 (pk_bytes op))
a3 a4 a5 a6 a7 (Z_to_bv 64 (pno + 1)) s3 (Z_to_bv 64 pc) (Z_to_bv 64 (Z.b2z (0 <? pk_e_o_s op))) s6 (Z_to_bv 64 0x7fffffff)
(Z_to_bv 64 pno) (Z_to_bv 64 (pk_bytes op)) s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_speex_bits_read_from_h) fc None m1 (seg_rom bsegs))))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 pc) (Z_to_bv 64 sser) s6
(Z_to_bv 64 (F + 8688)) (Z_to_bv 64 pno) (Z_to_bv 64 (pk_bytes op)) s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_SS) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros S1R F0 FS1 FOK SR PCR EXR PNR BYR EOR OS OPC SP MI. unfold hsp in SP. unfold stream_cells, wz in OS. unfold op_cells, wz in OPC.
unfold A_SS, A_PN, A_HP, A_KT, A_speex_bits_read_from_h.
pose proof FOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SNR & _).
pose proof (munch_refl [(S1, S1 + 248)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
ato 0x96f58. astep.
destruct (Z.eq_dec sser (-1)) as [SM|SN].
- subst sser. rewrite bv_eqb_same_k. cbn iota.
ato 0x96ee8. apply evt_done. eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. left. split; [reflexivity|].
split; [unfold hsp; eassumption| reflexivity].
- rewrite (bv_eqb_lit_ne_k sser (-1)) by lia. cbn iota. ato 0x96f64. astep.
destruct (Z.eq_dec (os_serialno os) sser) as [SE|SNE].
+ rewrite SE, bv_eqb_same_k. cbn [negb]. ato 0x96f70. astep.
destruct (Z.eq_dec pc 0) as [P0|PN].
* subst pc. try sh_if. apply evt_done. eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
right. right. left. split; [exact SN|]. split; [reflexivity|]. split; [reflexivity|]. split; [unfold hsp; eassumption| reflexivity].
* rewrite (bv_eqb_lit_ne_k pc 0) by lia. cbn iota. ato 0x96f7c.
rewrite (swrap_mod64_plus1_k extra) by lia. bato 0x96f80.
astep. rewrite lts_lit_k by lia.
destruct (Z.ltb_spec (extra + 1) pc) as [XL|XG]; cbn [negb].
-- ato 0x96f88. rewrite (swrap32_small_k (pno + 1)) by lia. bato 0x96f8c.
ato 0x97988. rewrite Z.add_0_r, (swrap32_small_k (pk_bytes op)) by lia.
apply evt_done. eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
right. right. right. right. split; [exact SN|]. split; [reflexivity|]. split; [exact PN|]. split; [lia|].
split; [unfold hsp; eassumption| reflexivity].
-- ato 0x97348. apply evt_done. eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
right. right. right. left. split; [exact SN|]. split; [reflexivity|]. split; [exact PN|]. split; [lia|].
split; [unfold hsp; eassumption| replace (1 + extra) with (extra + 1) by lia; reflexivity].
+ rewrite (bv_eqb_lit_ne_k (os_serialno os) sser) by lia. cbn [negb]. ato 0x96ee8.
apply evt_done. eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. right. left. split; [exact SN|]. split; [exact SNE|].
split; [unfold hsp; eassumption| reflexivity].
Qed.

Lemma kd_w1 : forall (S1 nfr skip : Z) (v48 : word) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w208 w216 w224 w232 w240 Fr fc (m : mem),
ra = Z_to_bv 64 0x96fa8 -> 0 <= S1 < 2^62 -> 1 <= nfr <= 10 -> -2^31 < skip < 2^31 -> bv_unsigned v48 mod 2^32 = skip mod 2^32 ->
rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 v48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 (Z_to_bv 64 nfr)
w208 w216 w224 w232 w240) ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (v88 a0' a1' : word),
munch [(S1, S1 + 248)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ (v88 <> Z_to_bv 64 0 -> skip < 0)
/\ rw_cells bsegs m1 S1 (hsp w0 w8 w16 w24 w32 w40 v48 w56 w64 w72 w80 v88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 (Z_to_bv 64 nfr)
w208 w216 w224 w232 w240)
/\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 skip) (Z_to_bv 64 0) s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_DH) fc None m1 (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> S1R NFR SKR SKW SP MI. unfold hsp in SP. unfold A_DH.
replace (ret_pc (Z_to_bv 64 0x96fa8)) with (Z_to_bv 64 0x96fa8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(S1, S1 + 248)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
ato 0x96fac. astep. rewrite (bv_eqb_lit_ne_k nfr 0) by lia. cbn [negb]. ato 0x96fb4.
pose proof SP as SP'.
lazymatch type of SP' with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?cs :: ?post) =>
change (rw_cells bsegs m S1 ([c0; c1; c2; c3; c4; c5] ++ cs :: post)) in SP' end.
apply rw_cells_c8_split_hi in SP'. cbn [app] in SP'.
astep.
assert (SX : sx32 v48 = Z_to_bv 64 skip).
{ unfold sx32. f_equal. rewrite swrap32_eq_k. rewrite <- Zplus_mod_idemp_l. change (2^32) with 4294967296 in SKW. rewrite SKW, Zplus_mod_idemp_l.
rewrite Z.mod_small by lia. lia. }
rewrite SX. clear SP'.
ato 0x96fcc.
ato 0x96fd0.
apply evt_done. do 4 eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [| split; [unfold hsp; eassumption| reflexivity]].
intros NE. destruct (Z_lt_le_dec skip 0) as [LT|GE]; [exact LT|]. exfalso. apply NE. f_equal.
rewrite (Z.mod_small skip) by lia.
replace (Z.lxor skip 9223372036854775808) with (skip + 9223372036854775808) by (change 9223372036854775808 with (2 ^ 63); symmetry; apply zb_lxor_pow2_small; lia).
replace (skip + 9223372036854775808 <? 9223372036854775808) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. apply Z.land_0_r.
Qed.

Lemma dh_w1 : forall (S1 : Z) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 Fr fc (m : mem),
0 <= S1 < 2^62 ->
rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240) ->
mem_inv bsegs m ->
evt bsegs (eq (MS (mkR (Z_to_bv 64 0x96fe8) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) w216 w192 w208 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s11 s9 s10 w192 t3 t4 t5 t6) Fr (Z_to_bv 64 A_speex_decode_h) fc None m (seg_rom bsegs)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_DH) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros S1R SP MI. unfold hsp in SP. unfold A_DH, A_speex_decode_h.
ato 0x98c00. apply evt_done. reflexivity.
Qed.

Lemma dh_w2a : forall (ret : Z) (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (m : mem),
ra = Z_to_bv 64 0x96fe8 -> -2 <= ret <= 0 -> mem_inv bsegs m ->
evt bsegs (fun ms =>
((ret = -1 \/ ret = -2) /\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ret) (Z_to_bv 64 (-3)) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s2 s9 s10 s8 t3 t4 t5 t6) Fr (Z_to_bv 64 A_KT) fc None m (seg_rom bsegs))
\/ (ret = 0 /\ ms = MS (mkR (Z_to_bv 64 0x96ff8) sp gp tp t0 t1 t2 s0 s1 s11 (Z_to_bv 64 (-3)) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_speex_bits_remaining_h) fc None m (seg_rom bsegs)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ret) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> RR MI. unfold A_KT, A_speex_bits_remaining_h.
replace (ret_pc (Z_to_bv 64 0x96fe8)) with (Z_to_bv 64 0x96fe8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0x96fec.
assert (RC : ret = -2 \/ ret = -1 \/ ret = 0) by lia.
destruct RC as [-> | [-> | ->]]; astep; try sh_if.
- ato 0x97348. apply evt_done. left. split; [right; reflexivity| reflexivity].
- ato 0x97348. apply evt_done. left. split; [left; reflexivity| reflexivity].
- ato 0x98808. apply evt_done. right. split; reflexivity.
Qed.

Lemma dh_w2b : forall (S1 F rem chan fs : Z) (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w136 w144 w152 w160 w168 w176 w192 w200 w216 w224 w232 w240 Fr fc (m : mem),
ra = Z_to_bv 64 0x96ff8 -> 0 <= S1 < 2^62 -> -2^63 <= rem < 2^63 -> -2^31 <= chan < 2^31 -> 0 <= fs <= 640 ->
rw_cells bsegs m (F + 8384) [C4 (Z_to_bv 64 fs)] ->
rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 (Z_to_bv 64 (F + 9168)) w136 w144 w152 w160 w168 w176
(Z_to_bv 64 (F + 8384)) w192 w200 (Z_to_bv 64 (F + 128)) w216 w224 w232 w240) ->
mem_inv bsegs m ->
evt bsegs (fun ms =>
(rem < 0 /\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 rem) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s2 s9 s10 (Z_to_bv 64 chan) t3 t4 t5 t6) Fr (Z_to_bv 64 A_KT) fc None m (seg_rom bsegs))
\/ (0 <= rem /\ chan <> 2 /\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 2) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 (Z_to_bv 64 chan) s9 s10 (Z_to_bv 64 chan) t3 t4 t5 t6) Fr (Z_to_bv 64 A_DT) fc None m (seg_rom bsegs))
\/ (0 <= rem /\ chan = 2 /\ ms = MS (mkR (Z_to_bv 64 0x9701c) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 (F + 128)) (Z_to_bv 64 fs) (Z_to_bv 64 (F + 9168))
a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 chan) s9 s10 (Z_to_bv 64 chan) t3 t4 t5 t6) Fr (Z_to_bv 64 A_speex_decode_stereo_h) fc None m (seg_rom bsegs)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 rem) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 chan) s9 s10 s11 t3 t4 t5 t6)
Fr (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> S1R RR CR FSR FSZ SP MI. unfold hsp in SP. unfold A_KT, A_DT, A_speex_decode_stereo_h.
replace (ret_pc (Z_to_bv 64 0x96ff8)) with (Z_to_bv 64 0x96ff8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
astep. rewrite lts_lit_k by lia.
destruct (Z.ltb_spec rem 0) as [RN|RP]; cbn [negb].
- ato 0x97348. apply evt_done. left. split; [exact RN| reflexivity].
- ato 0x97004. astep.
destruct (Z.eq_dec chan 2) as [C2|CN].
+ subst chan. rewrite bv_eqb_same_k. cbn [negb]. ato 0x97010. rewrite sx32_lit_k by lia. ato 0x98edc.
apply evt_done. right. right. split; [exact RP|]. split; [reflexivity| reflexivity].
+ rewrite (bv_eqb_lit_ne_k chan 2) by lia. cbn [negb]. ato 0x9701c.
apply evt_done. right. left. split; [exact RP|]. split; [exact CN| reflexivity].
Qed.

Lemma zbv_add_modr_k : forall x y, Z_to_bv 64 (x + y mod 18446744073709551616) = Z_to_bv 64 (x + y).
Proof. intros x y. apply Z_to_bv_eqm. rewrite Zplus_mod_idemp_r. reflexivity. Qed.
Lemma swrap32_add_modr_k : forall x y, bv_swrap 32 (x + y mod 18446744073709551616) = bv_swrap 32 (x + y).
Proof.
intros x y. rewrite !swrap32_eq_k. f_equal.
assert (D : (4294967296 | 18446744073709551616)) by (exists 4294967296; reflexivity).
replace (x + y mod 18446744073709551616 + 2147483648) with ((x + 2147483648) + y mod 18446744073709551616) by lia.
replace (x + y + 2147483648) with ((x + 2147483648) + y) by lia.
rewrite (Zplus_mod (x + 2147483648) (y mod 18446744073709551616)), (Zplus_mod (x + 2147483648) y).
rewrite <- (Znumtheory.Zmod_div_mod 4294967296 18446744073709551616 y) by (lia || exact D). reflexivity.
Qed.
Lemma zbv_add_modl_k : forall x y, Z_to_bv 64 (x mod 18446744073709551616 + y) = Z_to_bv 64 (x + y).
Proof. intros x y. apply Z_to_bv_eqm. rewrite Zplus_mod_idemp_l. reflexivity. Qed.
Lemma zbv_sub_modr_k : forall x y, Z_to_bv 64 (x - y mod 18446744073709551616) = Z_to_bv 64 (x - y).
Proof. intros x y. apply Z_to_bv_eqm. rewrite Zminus_mod_idemp_r. reflexivity. Qed.
Lemma zbv_sub_modl_k : forall x y, Z_to_bv 64 (x mod 18446744073709551616 - y) = Z_to_bv 64 (x - y).
Proof. intros x y. apply Z_to_bv_eqm. rewrite Zminus_mod_idemp_l. reflexivity. Qed.
Lemma zbv_modM_k : forall x, Z_to_bv 64 (x mod 18446744073709551616) = Z_to_bv 64 x.
Proof. intros x. apply Z_to_bv_eqm. rewrite Zmod_mod. reflexivity. Qed.
Lemma swrap32_modM_k : forall x, bv_swrap 32 (x mod 18446744073709551616) = bv_swrap 32 x.
Proof.
intros x. rewrite !swrap32_eq_k. f_equal.
assert (D : (4294967296 | 18446744073709551616)) by (exists 4294967296; reflexivity).
rewrite (Zplus_mod (x mod 18446744073709551616)), (Zplus_mod x).
rewrite <- (Znumtheory.Zmod_div_mod 4294967296 18446744073709551616 x) by (lia || exact D). reflexivity.
Qed.
Lemma swrap32_modl_k : forall x y, bv_swrap 32 (x mod 18446744073709551616 + y) = bv_swrap 32 (x + y).
Proof. intros x y. rewrite (Z.add_comm (x mod 18446744073709551616) y), (Z.add_comm x y). apply swrap32_add_modr_k. Qed.
Lemma swrap32_sub_modr_k : forall x y, bv_swrap 32 (x - y mod 18446744073709551616) = bv_swrap 32 (x - y).
Proof.
intros x y. rewrite !swrap32_eq_k. f_equal.
assert (D : (4294967296 | 18446744073709551616)) by (exists 4294967296; reflexivity).
replace (x - y mod 18446744073709551616 + 2147483648) with ((x + 2147483648) - y mod 18446744073709551616) by lia.
replace (x - y + 2147483648) with ((x + 2147483648) - y) by lia.
rewrite (Zminus_mod (x + 2147483648) (y mod 18446744073709551616)), (Zminus_mod (x + 2147483648) y).
rewrite <- (Znumtheory.Zmod_div_mod 4294967296 18446744073709551616 y) by (lia || exact D). reflexivity.
Qed.
Lemma swrap32_sub_modl_k : forall x y, bv_swrap 32 (x mod 18446744073709551616 - y) = bv_swrap 32 (x - y).
Proof.
intros x y. rewrite !swrap32_eq_k. f_equal.
assert (D : (4294967296 | 18446744073709551616)) by (exists 4294967296; reflexivity).
replace (x mod 18446744073709551616 - y + 2147483648) with (x mod 18446744073709551616 + (2147483648 - y)) by lia.
replace (x - y + 2147483648) with (x + (2147483648 - y)) by lia.
rewrite (Zplus_mod (x mod 18446744073709551616)), (Zplus_mod x).
rewrite <- (Znumtheory.Zmod_div_mod 4294967296 18446744073709551616 x) by (lia || exact D). reflexivity.
Qed.
Ltac tnorm :=
repeat match goal with
| |- context [bv_swrap 32 (?x + ?y mod 18446744073709551616)] => rewrite (swrap32_add_modr_k x y)
| |- context [bv_swrap 32 (?x mod 18446744073709551616 + ?y)] => rewrite (swrap32_modl_k x y)
| |- context [bv_swrap 32 (?x - ?y mod 18446744073709551616)] => rewrite (swrap32_sub_modr_k x y)
| |- context [bv_swrap 32 (?x mod 18446744073709551616 - ?y)] => rewrite (swrap32_sub_modl_k x y)
| |- context [bv_swrap 32 (?x mod 18446744073709551616)] => rewrite (swrap32_modM_k x)
| |- context [Z_to_bv 64 (?x + ?y mod 18446744073709551616)] => rewrite (zbv_add_modr_k x y)
| |- context [Z_to_bv 64 (?x mod 18446744073709551616 + ?y)] => rewrite (zbv_add_modl_k x y)
| |- context [Z_to_bv 64 (?x - ?y mod 18446744073709551616)] => rewrite (zbv_sub_modr_k x y)
| |- context [Z_to_bv 64 (?x mod 18446744073709551616 - ?y)] => rewrite (zbv_sub_modl_k x y)
| |- context [Z_to_bv 64 (?x mod 18446744073709551616)] => rewrite (zbv_modM_k x)
| |- context [?x + 0] => rewrite (Z.add_0_r x)
| |- context [bv_swrap 32 ?a] => rewrite (swrap32_small_k a) by lia
end.
Lemma bv_eqb_lit_eq_k : forall r k, r = k -> bv_eqb (Z_to_bv 64 r) (Z_to_bv 64 k) = true.
Proof. intros r k ->. apply bv_eqb_same_k. Qed.

Ltac dt_tail jv nfr :=
ato 0x970cc; tnorm; bato 0x970d0; ato 0x970d8; astep;
destruct (Z.eq_dec (jv + 1) nfr) as [JE|JN];
[ erewrite bv_eqb_lit_eq_k by lia; cbn [negb]; ato 0x97348; apply evt_done; do 4 eexists; left; split; [lia| reflexivity]
| erewrite bv_eqb_lit_ne_k by lia; cbn [negb]; ato 0x96fd0; apply evt_done; do 4 eexists; right; split; [lia| reflexivity] ].

Ltac dt_flag jv nfr fs v88 skip FLG :=
ato 0x97074; astep; destruct (bv_eqb v88 (Z_to_bv 64 0)) eqn:FZ; cbn [negb];
[ dt_tail jv nfr
| let SKN := fresh "SKN" in let NF := fresh "NF" in let JF := fresh "JF" in
assert (SKN : skip < 0) by (apply FLG; intros E; rewrite E in FZ; rewrite bv_eqb_same_k in FZ; discriminate FZ);
assert (NF : 0 <= nfr * fs <= 6400) by nia; assert (JF : 0 <= jv * fs <= nfr * fs - fs) by nia;
ato 0x97084; tnorm; bato 0x97088; ato 0x97094; tnorm; bato 0x97098; ato 0x970a4; tnorm; bato 0x970a8; ato 0x970b0; tnorm; bato 0x970b4;
ato 0x970c4; tnorm; bato 0x970c8; dt_tail jv nfr ].

Lemma dh_w2c : forall (S1 F j nfr fs L skip : Z) (v88 : word) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w192 w208 w216 w224 w232 w240 Fr fc (m : mem),
0 <= S1 < 2^62 -> 0 <= j < nfr -> nfr <= 10 -> 0 <= fs <= 640 -> 0 <= L <= 160 -> -2^31 < skip < 2^31 -> (v88 <> Z_to_bv 64 0 -> skip < 0) ->
rw_cells bsegs m (F + 8384) [C4 (Z_to_bv 64 fs)] -> rw_cells bsegs m (F + 9248) [C4 (Z_to_bv 64 L)] ->
rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 v88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168
(Z_to_bv 64 (F + 9248)) (Z_to_bv 64 (F + 8384)) w192 (Z_to_bv 64 nfr) w208 w216 w224 w232 w240) ->
mem_inv bsegs m ->
evt bsegs (fun ms => exists a0' a1' a2' a3' : word,
(j + 1 = nfr /\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0' a1' a2' a3' a4 a5 a6 a7
s2 s3 s4 s5 s6 (Z_to_bv 64 0x7fffffff) s2 (Z_to_bv 64 skip) (Z_to_bv 64 (j + 1)) s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_KT) fc None m (seg_rom bsegs))
\/ (j + 1 < nfr /\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0' a1' a2' a3' a4 a5 a6 a7
s2 s3 s4 s5 s6 (Z_to_bv 64 0x7fffffff) s8 (Z_to_bv 64 skip) (Z_to_bv 64 (j + 1)) s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_DH) fc None m (seg_rom bsegs)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 0x7fffffff) s8 (Z_to_bv 64 skip) (Z_to_bv 64 j) s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_DT) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros S1R JR NFR FSR LR SKR FLG FSZ LOOK SP MI. unfold hsp in SP. unfold A_KT, A_DT, A_DH.
ato 0x97024. rewrite sx32_lit_k by lia.
ato 0x9702c. bato 0x97034. tnorm.
astep. rewrite lts_lit_k by lia.
destruct (Z.ltb_spec skip (2147483647 - L)) as [SL|SG]; cbn [negb].
2:{ dt_tail j nfr. }
ato 0x97044. rewrite sx32_lit_k by lia. astep.
destruct (bv_eqb s2 (Z_to_bv 64 1)) eqn:P1; cbn [negb].
2:{ dt_flag j nfr fs v88 skip FLG. }
destruct (Z.eq_dec j 0) as [J0|JN0].
2:{ astep. erewrite bv_eqb_lit_ne_k by lia. cbn [negb]. dt_flag j nfr fs v88 skip FLG. }
subst j. astep. try (rewrite bv_eqb_same_k; cbn [negb]).
astep. rewrite lts_lit_k by lia.
destruct (Z.ltb_spec 0 skip) as [SP0|SN0]; cbn [negb].
- ato 0x97058. tnorm. bato 0x97068. tnorm. bato 0x970cc. dt_tail 0 nfr.
- dt_flag 0 nfr fs v88 skip FLG.
Qed.

Lemma kt_w : forall (S1 F pc eosf : Z) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 Fr fc (m : mem),
0 <= S1 < 2^62 -> 0 <= pc < 2^31 - 1 -> (eosf = 0 \/ eosf = 1) ->
rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 (Z_to_bv 64 (F + 8544)) (Z_to_bv 64 (F + 8688))
w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240) ->
mem_inv bsegs m ->
evt bsegs (fun ms =>
(eosf = 0 /\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 (pc + 1)) a1 a2 a3 a4 a5 a6 a7
s2 s3 (Z_to_bv 64 (pc + 1)) (Z_to_bv 64 0) s6 (Z_to_bv 64 (F + 8688)) s8 (Z_to_bv 64 (F + 8544)) s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_KH) fc None m (seg_rom bsegs))
\/ (eosf = 1 /\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 (pc + 1)) a1 a2 a3 a4 a5 a6 a7
s2 s3 (Z_to_bv 64 (pc + 1)) (Z_to_bv 64 1) s6 (Z_to_bv 64 (F + 8688)) s8 (Z_to_bv 64 (F + 8544)) (Z_to_bv 64 1) s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_PN) fc None m (seg_rom bsegs)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 pc) (Z_to_bv 64 eosf) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_KT) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros S1R PCR EOR SP MI. unfold hsp in SP. unfold A_KT, A_KH, A_PN.
ato 0x9734c. tnorm. bato 0x97350. ato 0x9735c. astep.
destruct EOR as [-> | ->].
- try (rewrite bv_eqb_same_k; cbn iota). apply evt_done. left. split; reflexivity.
- try (rewrite (bv_eqb_lit_ne_k 1 0) by lia; cbn iota). ato 0x96ee8. apply evt_done. right. split; reflexivity.
Qed.
