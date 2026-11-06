(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Znumtheory.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1df X1ck X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1od.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X0ec X07z X05o X05p X0ae X09i X09u X09x
X071 X06v X077.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Notation mem := (word -> option byte).
Definition A_KP : Z := 0x96d78.
Definition A_SS : Z := 0x96db0.
Definition A_HP : Z := 0x96e58.
Definition A_KT : Z := 0x96e48.
Definition A_SPEEX_LIT : Z := 0x232a0.
Definition A_speex_bits_read_from_h : Z := 0x976b4.
Definition A_speex_decode_h : Z := 0x985e0.
Definition A_DH_h : Z := 0x96dec.

Lemma packetout_r_range : forall (os : stream_st bptr) r opo os', ogg_stream_packetout os = Some ((r, opo), os') -> r = 0 \/ r = -1 \/ r = 1.
Proof.
intros os r opo os' E. unfold ogg_stream_packetout, packetout in E.
destruct (ogg_stream_check os); [injection E as <- _ _; left; reflexivity|].
destruct (_ <=? _); [injection E as <- _ _; left; reflexivity|].
destruct (negb _); [injection E as <- _ _; right; left; reflexivity|].
destruct (gather255 _ _ _ _ _) as [[[n eos] bytes]|]; [injection E as <- _ _; right; right; reflexivity| discriminate E].
Qed.

Lemma kh_w0 : forall (S1 F : Z) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w160 w168 w176 w184 w192 w200 w208 Fr fc (m : mem),
0 <= S1 < 2^62 ->
rw_cells asegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 (Z_to_bv 64 (F + 8688)) w160 w168 w176 w184 w192 w200 w208) ->
mem_inv asegs m ->
evt asegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x96d70) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 (F + 8688)) (Z_to_bv 64 (F + 8608)) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (F + 8608)) s3 s4 s5 s6 (Z_to_bv 64 (F + 8688)) s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_ogg_stream_packetout) fc None m (seg_rom asegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (F + 8608)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_KH) fc None m (seg_rom asegs)).
Proof.
intros until m. intros S1R SP MI. unfold hsp in SP. unfold A_KH, A_ogg_stream_packetout.
ato 0xb9744. apply evt_done. reflexivity.
Qed.

Lemma kh_w1 : forall (S1 F r : Z) (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 Fr fc (m : mem),
ra = Z_to_bv 64 0x96d70 -> (r = 0 \/ r = -1 \/ r = 1) -> 0 <= S1 < 2^62 ->
rw_cells asegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208) ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
munch [(S1, S1 + 216)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ ((r <> 1 /\ rw_cells asegs m1 S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 (Z_to_bv 64 0) w136 w144 w152 w160 w168 w176 w184 w192 w200 w208)
/\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 r) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_PN) fc None m1 (seg_rom asegs))
\/ (r = 1 /\ m1 = m
/\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 1) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_KP) fc None m (seg_rom asegs))))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (ret_pc ra) fc None m (seg_rom asegs)).
Proof.
intros until m. intros -> RR S1R SP MI. unfold hsp in SP. unfold A_PN, A_KP.
replace (ret_pc (Z_to_bv 64 0x96d70)) with (Z_to_bv 64 0x96d70) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(S1, S1 + 216)] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0x96d74.
destruct RR as [-> | [-> | ->]].
- astep. try sh_if. ato 0x9714c. apply evt_done. eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
left. split; [lia|]. split; [unfold hsp; assumption| reflexivity].
- astep. try sh_if. ato 0x9714c. apply evt_done. eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
left. split; [lia|]. split; [unfold hsp; assumption| reflexivity].
- astep. try sh_if. apply evt_done. exists m. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
right. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma kh_w2 : forall (S1 F Bd : Z) (op : packet) (gw : word) (kc : list cell) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 Fr fc (m : mem),
0 <= S1 < 2^62 -> 0 <= pk_bytes op < 2^63 ->
rw_cells asegs m (F + 8608) (op_cells Bd (Some op) gw kc) ->
rw_cells asegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208) ->
mem_inv asegs m ->
evt asegs (fun ms =>
(pk_bytes op < 5 /\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 5) w176 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (F + 8608)) s3 s4 s10 s6 s7 s8 s9 (Z_to_bv 64 (pk_bytes op)) s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_SS) fc None m (seg_rom asegs))
\/ (5 <= pk_bytes op /\ ms = MS (mkR (Z_to_bv 64 0x96d9c) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 (Bd + pk_off op)) (Z_to_bv 64 A_SPEEX_LIT) (Z_to_bv 64 5)
a3 a4 a5 a6 a7 (Z_to_bv 64 (F + 8608)) s3 s4 s10 s6 s7 s8 s9 (Z_to_bv 64 (pk_bytes op)) s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 e_bcmp) fc None m (seg_rom asegs)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (F + 8608)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_KP) fc None m (seg_rom asegs)).
Proof.
intros until m. intros S1R PB OPC SP MI. unfold hsp in SP. unfold op_cells, wz in OPC. unfold A_KP, A_SS, A_SPEEX_LIT, e_bcmp.
ato 0x96d84. astep. rewrite lts_lit by lia.
destruct (Z.ltb_spec (pk_bytes op) 5) as [LT|GE].
- ato 0x96db0. apply evt_done. left. split; [exact LT| reflexivity].
- ato 0x56bf4. apply evt_done. right. split; [exact GE| reflexivity].
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
rw_cells asegs m A (pre ++ C8 v :: post) -> rw_cells asegs m A (pre ++ C4 v :: C4 (Z_to_bv 64 (Z.shiftr (bv_unsigned v) 32)) :: post).
Proof.
intros m A pre post v [[W B] R]. apply cells_wf_app in W. destruct W as [W1 [_ W2]].
split; [split|].
- apply cells_wf_app. split; [exact W1| split; [exact I| split; [exact I| exact W2]]].
- rewrite cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite le8_split_hi in B.
rewrite <- app_assoc in B. exact B.
- rewrite cells_size_app in *. cbn [cells_size csize] in *. exact R.
Qed.

Lemma kh_w3 : forall (S1 F Bd L Gv : Z) (hdr : list byte) (os : stream_st bptr) (v ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 Fr fc (m : mem),
ra = Z_to_bv 64 0x96d9c -> 0 <= S1 < 2^62 -> 0 < F -> stream_fields_ok os ->
rw_cells asegs m (F + 8688) (stream_cells Bd L Gv hdr os) ->
rw_cells asegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208) ->
mem_inv asegs m ->
evt asegs (fun ms => exists a1' : word,
((bv_unsigned v <> 0 /\ a1' = w176) \/ (bv_unsigned v = 0 /\ a1' = Z_to_bv 64 (os_serialno os)))
/\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) v a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 (F + 8688)) s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_SS) fc None m (seg_rom asegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 (F + 8688)) s8 s9 s10 s11 t3 t4 t5 t6)
Fr (ret_pc ra) fc None m (seg_rom asegs)).
Proof.
intros until m. intros -> S1R F0 FOK OS SP MI. unfold hsp in SP. unfold stream_cells, wz in OS. unfold A_SS.
replace (ret_pc (Z_to_bv 64 0x96d9c)) with (Z_to_bv 64 0x96d9c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof FOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SNR & _).
lazymatch type of OS with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?cs :: ?post) =>
change (rw_cells asegs m (F + 8688) ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13] ++ cs :: post)) in OS end.
apply rw_cells_c8_split_hi in OS. cbn [app] in OS.
ato 0x96da0. astep.
destruct (Z.eq_dec (bv_unsigned v) 0) as [V0|VN].
- replace (bv_eqb v (Z_to_bv 64 0)) with true by (symmetry; unfold bv_eqb; apply Z.eqb_eq; rewrite V0; reflexivity). cbn [negb].
ato 0x96da8. rewrite h_sx32_lit by exact SNR. ato 0x96db0.
apply evt_done. exists (Z_to_bv 64 (os_serialno os)). split; [right; split; [exact V0| reflexivity]| reflexivity].
- replace (bv_eqb v (Z_to_bv 64 0)) with false by (symmetry; unfold bv_eqb; apply Z.eqb_neq; rewrite (unsigned_lit 0) by lia; exact VN). cbn [negb].
ato 0x96db0.
apply evt_done. exists w176. split; [left; split; [exact VN| reflexivity]| reflexivity].
Qed.

Lemma kh_w4 : forall (S1 F Bd L Gv sser pc extra1 : Z) (hdr : list byte) (os : stream_st bptr) (op : packet) (gw : word) (kc : list cell)
(ra sp gp tp t0 t1 t2 s0 a0 a2 a3 a4 a5 a6 a7 s3 s4 s5 s9 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 Fr fc (m : mem),
0 <= S1 < 2^62 -> 0 < F -> F + 16384 <= S1 -> stream_fields_ok os -> -2^31 <= sser < 2^31 ->
0 <= pc < 2^31 -> -2^31 <= extra1 < 2^31 -> 0 <= pk_bytes op < 2^31 -> 0 <= pk_e_o_s op < 2^63 ->
rw_cells asegs m (F + 8688) (stream_cells Bd L Gv hdr os) ->
rw_cells asegs m (F + 8608) (op_cells Bd (Some op) gw kc) ->
rw_cells asegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208) ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
munch [(S1, S1 + 216)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ ((sser = -1
/\ rw_cells asegs m1 S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 (Z_to_bv 64 0) w136 w144 w152 w160 w168 (Z_to_bv 64 (-1)) w184 w192 w200 w208)
/\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 (-1)) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (F + 8608)) s3 s4 s5 (Z_to_bv 64 pc) (Z_to_bv 64 (F + 8688)) (Z_to_bv 64 extra1) s9 s5 (Z_to_bv 64 (F + 8400)) t3 t4 t5 t6)
Fr (Z_to_bv 64 A_PN) fc None m1 (seg_rom asegs))
\/ (sser <> -1 /\ os_serialno os <> sser
/\ rw_cells asegs m1 S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 (Z_to_bv 64 0) w136 w144 w152 w160 w168 (Z_to_bv 64 sser) w184 w192 w200 w208)
/\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 (os_serialno os)) (Z_to_bv 64 sser) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (F + 8608)) s3 s4 s5 (Z_to_bv 64 pc) (Z_to_bv 64 (F + 8688)) (Z_to_bv 64 extra1) s9 s5 (Z_to_bv 64 (F + 8400)) t3 t4 t5 t6)
Fr (Z_to_bv 64 A_PN) fc None m1 (seg_rom asegs))
\/ (sser <> -1 /\ os_serialno os = sser /\ pc = 0
/\ rw_cells asegs m1 S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 (Z_to_bv 64 sser) w184 w192 w200 w208)
/\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 sser) (Z_to_bv 64 sser) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (F + 8608)) s3 s4 s5 (Z_to_bv 64 pc) (Z_to_bv 64 (F + 8688)) (Z_to_bv 64 extra1) s9 (Z_to_bv 64 (pk_bytes op)) (Z_to_bv 64 (F + 8400)) t3 t4 t5 t6)
Fr (Z_to_bv 64 A_HP) fc None m1 (seg_rom asegs))
\/ (sser <> -1 /\ os_serialno os = sser /\ pc <> 0 /\ pc <= extra1
/\ rw_cells asegs m1 S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 (Z_to_bv 64 sser) w184 w192 w200 w208)
/\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 sser) (Z_to_bv 64 sser) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (F + 8608)) s3 s4 s5 (Z_to_bv 64 pc) (Z_to_bv 64 0) (Z_to_bv 64 extra1) s9 (Z_to_bv 64 (pk_bytes op)) (Z_to_bv 64 (F + 8400)) t3 t4 t5 t6)
Fr (Z_to_bv 64 A_KT) fc None m1 (seg_rom asegs))
\/ (sser <> -1 /\ os_serialno os = sser /\ pc <> 0 /\ extra1 < pc
/\ rw_cells asegs m1 S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 (Z_to_bv 64 sser) w184 w192 w200 w208)
/\ ms = MS (mkR (Z_to_bv 64 0x96de4) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 (F + 8400)) (Z_to_bv 64 (Bd + pk_off op)) (Z_to_bv 64 (pk_bytes op))
a3 a4 a5 a6 a7 (Z_to_bv 64 (F + 8608)) s3 s4 s5 (Z_to_bv 64 pc) (Z_to_bv 64 (Z.b2z (0 <? pk_e_o_s op))) (Z_to_bv 64 extra1) s9
(Z_to_bv 64 (pk_bytes op)) (Z_to_bv 64 (F + 8400)) t3 t4 t5 t6)
Fr (Z_to_bv 64 A_speex_bits_read_from_h) fc None m1 (seg_rom asegs))))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 (Z_to_bv 64 sser) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (F + 8608)) s3 s4 s5 (Z_to_bv 64 pc)
(Z_to_bv 64 (F + 8688)) (Z_to_bv 64 extra1) s9 (Z_to_bv 64 (pk_bytes op)) (Z_to_bv 64 (F + 8400)) t3 t4 t5 t6)
Fr (Z_to_bv 64 A_SS) fc None m (seg_rom asegs)).
Proof.
intros until m. intros S1R F0 FS1 FOK SR PCR EXR BYR EOR OS OPC SP MI. unfold hsp in SP. unfold stream_cells, wz in OS. unfold op_cells, wz in OPC.
unfold A_SS, A_PN, A_HP, A_KT, A_speex_bits_read_from_h.
pose proof FOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SNR & _).
pose proof (munch_refl [(S1, S1 + 216)] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0x96db4. astep.
destruct (Z.eq_dec sser (-1)) as [SM|SN].
- subst sser. rewrite bv_eqb_same. cbn iota.
ato 0x9714c. apply evt_done. eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. left. split; [reflexivity|].
split; [unfold hsp; eassumption| reflexivity].
- rewrite (bv_eqb_lit_ne_s sser (-1)) by lia. cbn iota. ato 0x96dc0. astep.
destruct (Z.eq_dec (os_serialno os) sser) as [SE|SNE].
+ rewrite SE, bv_eqb_same. cbn [negb]. ato 0x96dc4. astep.
destruct (Z.eq_dec pc 0) as [P0|PN].
* subst pc. try sh_if. apply evt_done. eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
right. right. left. split; [exact SN|]. split; [reflexivity|]. split; [reflexivity|]. split; [unfold hsp; eassumption| reflexivity].
* rewrite (bv_eqb_lit_ne_s pc 0) by lia. cbn iota. ato 0x96dc8. astep. rewrite lts_lit by lia.
destruct (Z.ltb_spec extra1 pc) as [XL|XG]; cbn [negb].
-- ato 0x976b4. rewrite Z.add_0_r, swrap32_small_h by lia.
apply evt_done. eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
right. right. right. right. split; [exact SN|]. split; [reflexivity|]. split; [exact PN|]. split; [exact XL|].
split; [unfold hsp; eassumption| reflexivity].
-- ato 0x96e48. apply evt_done. eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
right. right. right. left. split; [exact SN|]. split; [reflexivity|]. split; [exact PN|]. split; [lia|].
split; [unfold hsp; eassumption| reflexivity].
+ rewrite (bv_eqb_lit_ne_s (os_serialno os) sser) by lia. cbn [negb]. ato 0x9714c.
apply evt_done. eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. right. left. split; [exact SN|]. split; [exact SNE|].
split; [unfold hsp; eassumption| reflexivity].
Qed.

Lemma kd_w1 : forall (S1 nfr : Z) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w144 w152 w160 w168 w176 w184 w192 w200 w208 Fr fc (m : mem),
ra = Z_to_bv 64 0x96de4 -> 0 <= S1 < 2^62 -> 1 <= nfr <= 10 ->
rw_cells asegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 (Z_to_bv 64 nfr) w144 w152 w160 w168 w176 w184 w192 w200 w208) ->
mem_inv asegs m ->
evt asegs (fun ms => ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 nfr) s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_DH_h) fc None m (seg_rom asegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (ret_pc ra) fc None m (seg_rom asegs)).
Proof.
intros until m. intros -> S1R NFR SP MI. unfold hsp in SP. unfold A_DH_h.
replace (ret_pc (Z_to_bv 64 0x96de4)) with (Z_to_bv 64 0x96de4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0x96de8. astep. rewrite (bv_eqb_lit_ne_s nfr 0) by lia. cbn iota. apply evt_done. reflexivity.
Qed.

Lemma dh_w1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (m : mem),
mem_inv asegs m ->
evt asegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x96dfc) sp gp tp t0 t1 t2 s0 s1 s9 s11 s4 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_speex_decode_h) fc None m (seg_rom asegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_DH_h) fc None m (seg_rom asegs)).
Proof.
intros until m. intros MI. unfold A_DH_h, A_speex_decode_h.
ato 0x985e0. apply evt_done. reflexivity.
Qed.

Definition A_speex_bits_remaining_h : Z := 0x982c0.
Definition A_speex_decode_stereo_h : Z := 0x9883c.

Lemma dh_w2a : forall (ret : Z) (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (m : mem),
ra = Z_to_bv 64 0x96dfc -> -2 <= ret <= 0 -> mem_inv asegs m ->
evt asegs (fun ms =>
((ret = -1 \/ ret = -2) /\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ret) (Z_to_bv 64 (-3)) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_KT) fc None m (seg_rom asegs))
\/ (ret = 0 /\ ms = MS (mkR (Z_to_bv 64 0x96e0c) sp gp tp t0 t1 t2 s0 s1 s11 (Z_to_bv 64 (-3)) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_speex_bits_remaining_h) fc None m (seg_rom asegs)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ret) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (ret_pc ra) fc None m (seg_rom asegs)).
Proof.
intros until m. intros -> RR MI. unfold A_KT, A_speex_bits_remaining_h.
replace (ret_pc (Z_to_bv 64 0x96dfc)) with (Z_to_bv 64 0x96dfc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0x96e00.
assert (RC : ret = -2 \/ ret = -1 \/ ret = 0) by lia.
destruct RC as [-> | [-> | ->]]; astep; try sh_if.
- apply evt_done. left. split; [right; reflexivity| reflexivity].
- apply evt_done. left. split; [left; reflexivity| reflexivity].
- ato 0x982c0. apply evt_done. right. split; reflexivity.
Qed.

Definition A_DT : Z := 0x96e30.
Lemma dh_w2b : forall (S1 F rem chan fs : Z) (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w176 w192 w200 w208 Fr fc (m : mem),
ra = Z_to_bv 64 0x96e0c -> 0 <= S1 < 2^62 -> -2^63 <= rem < 2^63 -> -2^31 <= chan < 2^31 -> 0 <= fs <= 640 ->
rw_cells asegs m (F + 8384) [C4 (Z_to_bv 64 fs)] ->
rw_cells asegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 (Z_to_bv 64 (F + 9168))
(Z_to_bv 64 (F + 8384)) w176 (Z_to_bv 64 chan) w192 w200 w208) ->
mem_inv asegs m ->
evt asegs (fun ms =>
(rem < 0 /\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 rem) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_KT) fc None m (seg_rom asegs))
\/ (0 <= rem /\ chan <> 2 /\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 2) (Z_to_bv 64 chan) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_DT) fc None m (seg_rom asegs))
\/ (0 <= rem /\ chan = 2 /\ ms = MS (mkR (Z_to_bv 64 0x96e30) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) s4 (Z_to_bv 64 fs) (Z_to_bv 64 (F + 9168)) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_speex_decode_stereo_h) fc None m (seg_rom asegs)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 rem) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (ret_pc ra) fc None m (seg_rom asegs)).
Proof.
intros until m. intros -> S1R RR CR FSR FSZ SP MI. unfold hsp in SP. unfold A_KT, A_DT, A_speex_decode_stereo_h.
replace (ret_pc (Z_to_bv 64 0x96e0c)) with (Z_to_bv 64 0x96e0c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
astep. rewrite lts_lit by lia.
destruct (Z.ltb_spec rem 0) as [RN|RP]; cbn [negb].
- ato 0x96e48. apply evt_done. left. split; [exact RN| reflexivity].
- ato 0x96e18. astep.
destruct (Z.eq_dec chan 2) as [C2|CN].
+ subst chan. rewrite bv_eqb_same. cbn [negb]. ato 0x96e24. rewrite h_sx32_lit by lia. ato 0x9883c.
apply evt_done. right. right. split; [exact RP|]. split; [reflexivity| reflexivity].
+ rewrite (bv_eqb_lit_ne_s chan 2) by lia. cbn [negb]. ato 0x96e30.
apply evt_done. right. left. split; [exact RP|]. split; [exact CN| reflexivity].
Qed.

Lemma dh_w2c : forall (n : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) Fr fc (m : mem),
1 <= n <= 10 -> mem_inv asegs m ->
evt asegs (fun ms =>
(n = 1 /\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 0) s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_KT) fc None m (seg_rom asegs))
\/ (2 <= n /\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 (n - 1)) s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_DH_h) fc None m (seg_rom asegs)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 n) s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_DT) fc None m (seg_rom asegs)).
Proof.
intros until m. intros NR MI. unfold A_KT, A_DT, A_DH_h.
astep. rewrite swrap32_small_h by lia. ato 0x96e34. astep. destruct (Z.eq_dec n 1) as [-> | NE].
- replace (1 + -1) with 0 by reflexivity. rewrite bv_eqb_same. cbn [negb]. ato 0x96e48. apply evt_done. left. split; reflexivity.
- rewrite (bv_eqb_lit_ne_s (n + -1) 0) by lia. cbn [negb]. ato 0x96dec. apply evt_done. right. split; [lia|].
replace (n + -1) with (n - 1) by lia. reflexivity.
Qed.

Lemma kt_w : forall (S1 pc eosf : Z) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 Fr fc (m : mem),
0 <= S1 < 2^62 -> 0 <= pc < 2^31 - 1 -> (eosf = 0 \/ eosf = 1) ->
rw_cells asegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208) ->
mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
munch [(S1, S1 + 216)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ ((eosf = 0 /\ m1 = m
/\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (pc + 1)) (Z_to_bv 64 0) s8 s9 s5 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_KH) fc None m (seg_rom asegs))
\/ (eosf = 1
/\ rw_cells asegs m1 S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 (Z_to_bv 64 1) w136 w144 w152 w160 w168 w176 w184 w192 w200 w208)
/\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (pc + 1)) w152 s8 s9 s5 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_PN) fc None m1 (seg_rom asegs))))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 pc) (Z_to_bv 64 eosf) s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_KT) fc None m (seg_rom asegs)).
Proof.
intros until m. intros S1R PCR EOR SP MI. unfold hsp in SP. unfold A_KT, A_KH, A_PN.
pose proof (munch_refl [(S1, S1 + 216)] m) as MU. pose proof (wmono_refl asegs m) as WM.
astep. rewrite swrap32_small_h by lia. ato 0x96e50. astep.
destruct EOR as [-> | ->].
- try (rewrite bv_eqb_same; cbn iota). apply evt_done. exists m. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
left. split; [reflexivity|]. split; reflexivity.
- try (rewrite (bv_eqb_lit_ne_s 1 0) by lia; cbn iota). ato 0x9714c. apply evt_done. eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
right. split; [reflexivity|]. split; [unfold hsp; eassumption| reflexivity].
Qed.
