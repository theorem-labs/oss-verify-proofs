(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1df X1ck X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X071 X06v.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X0xn.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xn.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Notation mem := (word -> option byte).
Definition A_destroy_h : Z := 0x98a30.
Definition A_bits_destroy_h : Z := 0x97904.
Definition A_stream_clear_h : Z := 0xc1294.
Definition A_sync_clear_h : Z := 0xc166c.

Lemma bv_eqb_lit_ne_h : forall r k, 0 <= r < 2^64 -> 0 <= k < 2^64 -> r <> k -> bv_eqb (Z_to_bv 64 r) (Z_to_bv 64 k) = false.
Proof.
intros r k Hr Hk NE. unfold bv_eqb. apply Z.eqb_neq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite !Z.mod_small by lia. exact NE.
Qed.

Definition cl_frame (c0 s3 s2 s1 s0 ra : word) : list cell := [C8 c0; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Lemma cl_frame_of_CB : forall (m : mem) A js, rw_cells bsegs m A [CB 48 js] -> exists c0 c1 c2 c3 c4 c5, rw_cells bsegs m A (cl_frame c0 c1 c2 c3 c4 c5).
Proof.
intros m A js H.
assert (L : length js = (8 * 6)%nat) by (destruct H as [[[Hwf _] _] _]; exact Hwf).
destruct (CB_C8s_h 6 js L) as (ws & Lws & E).
destruct ws as [|c0 [|c1 [|c2 [|c3 [|c4 [|c5 [|? ?]]]]]]]; try discriminate Lws.
exists c0, c1, c2, c3, c4, c5.
eapply rw_cells_recast; [exact H| apply (cells_wf_C8s_h [c0; c1; c2; c3; c4; c5])|]. cbn [cells_bytes cbytes app] in *. rewrite app_nil_r. exact E.
Qed.

Lemma cl_w1 : forall (S1 F S : Z) (ra gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 Fr fc (m : mem),
0 <= S < 2^63 -> 48 <= S1 < 2^62 ->
rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 (Z_to_bv 64 (F + 8480)) w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208
w216 w224 w232 w240) ->
rw_cells bsegs m (S1 + -48) (cl_frame c0 c1 c2 c3 c4 c5) -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
((S <> 0 /\ ms = MS (mkR (Z_to_bv 64 0x976d8) (Z_to_bv 64 (S1 + -48)) gp tp t0 t1 t2 (Z_to_bv 64 (F + 8480)) a3 (Z_to_bv 64 S) a1 a2 a3 (Z_to_bv 64 (F + 8480)) a5 a6 a7
a2 a1 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_destroy_h) fc None m1 (seg_rom bsegs))
\/ (S = 0 /\ ms = MS (mkR (Z_to_bv 64 0x976e0) (Z_to_bv 64 (S1 + -48)) gp tp t0 t1 t2 (Z_to_bv 64 (F + 8480)) a3 a1 a1 a2 a3 (Z_to_bv 64 (F + 8480)) a5 a6 a7
a2 a1 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_bits_destroy_h) fc None m1 (seg_rom bsegs)))
/\ munch [(S1 + -48, S1)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 (S1 + -48) (cl_frame c0 s3 s2 (Z_to_bv 64 S1) s0 (Z_to_bv 64 0x974b0)))
(MS (mkR ra (Z_to_bv 64 S1) gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 S) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0x974a8) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SR S1R SP FR MI. unfold hsp, cl_frame in *. unfold A_destroy_h, A_bits_destroy_h.
pose proof (munch_refl [(S1 + -48, S1)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
ato 0x976d0.
destruct (Z.eq_dec S 0) as [-> | NE].
- astep. try sh_if. ato 0x97904. apply evt_done. eexists. split; [right; split; [reflexivity| reflexivity]|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
- astep. rewrite (bv_eqb_lit_ne_h S 0) by lia. cbn [negb]. ato 0x98a30. apply evt_done. eexists. split; [left; split; [exact NE| reflexivity]|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
Qed.

Lemma cl_w2 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (m : mem),
ra = Z_to_bv 64 0x976d8 -> mem_inv bsegs m ->
evt bsegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x976e0) sp gp tp t0 t1 t2 s0 s1 s3 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_bits_destroy_h) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> MI. unfold A_bits_destroy_h.
replace (ret_pc (Z_to_bv 64 0x976d8)) with (Z_to_bv 64 0x976d8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0x97904. apply evt_done. reflexivity.
Qed.

Lemma cl_epi : forall (S1 : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c0 r3 r2 r1 r0 rr : word) Fr fc (m : mem),
48 <= S1 < 2^62 -> rw_cells bsegs m (S1 + -48) (cl_frame c0 r3 r2 r1 r0 rr) -> mem_inv bsegs m ->
evt bsegs (fun ms => ms = MS (mkR rr (Z_to_bv 64 S1) gp tp t0 t1 t2 r0 r1 s0 a1 a2 a3 a4 a5 a6 a7 r2 r3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_sync_clear_h) fc None m (seg_rom bsegs))
(MS (mkR ra (Z_to_bv 64 (S1 + -48)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x976ec) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros S1R FR MI. unfold cl_frame in FR. unfold A_sync_clear_h.
ato 0xc166c. apply evt_done.
replace (S1 + -48 + 48) with S1 by lia. reflexivity.
Qed.

Lemma cl_w3 : forall (sinit : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (m : mem),
ra = Z_to_bv 64 0x976e0 -> 0 <= sinit < 2^63 -> mem_inv bsegs m ->
evt bsegs (fun ms =>
(sinit <> 0 /\ ms = MS (mkR (Z_to_bv 64 0x976ec) sp gp tp t0 t1 t2 s0 s1 s1 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 sinit) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_stream_clear_h) fc None m (seg_rom bsegs))
\/ (sinit = 0 /\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 sinit) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0x976ec) fc None m (seg_rom bsegs)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 sinit) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> SR MI. unfold A_stream_clear_h.
replace (ret_pc (Z_to_bv 64 0x976e0)) with (Z_to_bv 64 0x976e0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
destruct (Z.eq_dec sinit 0) as [-> | NE].
- astep. try sh_if. apply evt_done. right. split; reflexivity.
- astep. rewrite (bv_eqb_lit_ne_h sinit 0) by lia. cbn [negb]. ato 0xc1294. apply evt_done. left. split; [exact NE| reflexivity].
Qed.

Lemma cl_w5 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (m : mem),
ra = Z_to_bv 64 0x974b0 -> mem_inv bsegs m ->
evt bsegs (fun ms => ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_XT) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> MI. unfold A_XT.
replace (ret_pc (Z_to_bv 64 0x974b0)) with (Z_to_bv 64 0x974b0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
apply evt_done. reflexivity.
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Notation mem := (word -> option byte).
Definition A_destroy_h : Z := 0x98480.
Definition A_bits_destroy_h : Z := 0x97640.
Definition A_stream_clear_h : Z := 0xb8b64.
Definition A_sync_clear_h : Z := 0xb8f3c.

Lemma bv_eqb_lit_ne_h : forall r k, 0 <= r < 2^64 -> 0 <= k < 2^64 -> r <> k -> bv_eqb (Z_to_bv 64 r) (Z_to_bv 64 k) = false.
Proof.
intros r k Hr Hk NE. unfold bv_eqb. apply Z.eqb_neq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite !Z.mod_small by lia. exact NE.
Qed.

Definition cl_frame (c0 s3 s2 s1 s0 ra : word) : list cell := [C8 c0; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Lemma cl_frame_of_CB : forall (m : mem) A js, rw_cells asegs m A [CB 48 js] -> exists c0 c1 c2 c3 c4 c5, rw_cells asegs m A (cl_frame c0 c1 c2 c3 c4 c5).
Proof.
intros m A js H.
assert (L : length js = (8 * 6)%nat) by (destruct H as [[[Hwf _] _] _]; exact Hwf).
destruct (CB_C8s_h 6 js L) as (ws & Lws & E).
destruct ws as [|c0 [|c1 [|c2 [|c3 [|c4 [|c5 [|? ?]]]]]]]; try discriminate Lws.
exists c0, c1, c2, c3, c4, c5.
eapply rw_cells_recast; [exact H| apply (cells_wf_C8s_h [c0; c1; c2; c3; c4; c5])|]. cbn [cells_bytes cbytes app] in *. rewrite app_nil_r. exact E.
Qed.

Lemma cl_w1 : forall (S1 F S : Z) (ra gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 Fr fc (m : mem),
0 <= S < 2^63 -> 48 <= S1 < 2^62 ->
rw_cells asegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 (Z_to_bv 64 (F + 8480)) w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208) ->
rw_cells asegs m (S1 + -48) (cl_frame c0 c1 c2 c3 c4 c5) -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
((S <> 0 /\ ms = MS (mkR (Z_to_bv 64 0x97424) (Z_to_bv 64 (S1 + -48)) gp tp t0 t1 t2 (Z_to_bv 64 (F + 8480)) s7 (Z_to_bv 64 S) a1 a2 s7 (Z_to_bv 64 (F + 8480)) a5 a6 a7
a2 a1 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_destroy_h) fc None m1 (seg_rom asegs))
\/ (S = 0 /\ ms = MS (mkR (Z_to_bv 64 0x9742c) (Z_to_bv 64 (S1 + -48)) gp tp t0 t1 t2 (Z_to_bv 64 (F + 8480)) s7 a1 a1 a2 s7 (Z_to_bv 64 (F + 8480)) a5 a6 a7
a2 a1 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_bits_destroy_h) fc None m1 (seg_rom asegs)))
/\ munch [(S1 + -48, S1)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 (S1 + -48) (cl_frame c0 s3 s2 (Z_to_bv 64 S1) s0 (Z_to_bv 64 0x971b0)))
(MS (mkR ra (Z_to_bv 64 S1) gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 S) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0x971a4) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SR S1R SP FR MI. unfold hsp, cl_frame in *. unfold A_destroy_h, A_bits_destroy_h.
pose proof (munch_refl [(S1 + -48, S1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0x9741c.
destruct (Z.eq_dec S 0) as [-> | NE].
- astep. try sh_if. ato 0x97640. apply evt_done. eexists. split; [right; split; [reflexivity| reflexivity]|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
- astep. rewrite (bv_eqb_lit_ne_h S 0) by lia. cbn [negb]. ato 0x98480. apply evt_done. eexists. split; [left; split; [exact NE| reflexivity]|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
Qed.

Lemma cl_w2 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (m : mem),
ra = Z_to_bv 64 0x97424 -> mem_inv asegs m ->
evt asegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x9742c) sp gp tp t0 t1 t2 s0 s1 s3 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_bits_destroy_h) fc None m (seg_rom asegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (ret_pc ra) fc None m (seg_rom asegs)).
Proof.
intros until m. intros -> MI. unfold A_bits_destroy_h.
replace (ret_pc (Z_to_bv 64 0x97424)) with (Z_to_bv 64 0x97424) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0x97640. apply evt_done. reflexivity.
Qed.

Lemma cl_epi : forall (S1 : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c0 r3 r2 r1 r0 rr : word) Fr fc (m : mem),
48 <= S1 < 2^62 -> rw_cells asegs m (S1 + -48) (cl_frame c0 r3 r2 r1 r0 rr) -> mem_inv asegs m ->
evt asegs (fun ms => ms = MS (mkR rr (Z_to_bv 64 S1) gp tp t0 t1 t2 r0 r1 s0 a1 a2 a3 a4 a5 a6 a7 r2 r3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_sync_clear_h) fc None m (seg_rom asegs))
(MS (mkR ra (Z_to_bv 64 (S1 + -48)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x97438) fc None m (seg_rom asegs)).
Proof.
intros until m. intros S1R FR MI. unfold cl_frame in FR. unfold A_sync_clear_h.
ato 0xb8f3c. apply evt_done.
replace (S1 + -48 + 48) with S1 by lia. reflexivity.
Qed.

Lemma cl_w3 : forall (sinit : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (m : mem),
ra = Z_to_bv 64 0x9742c -> 0 <= sinit < 2^63 -> mem_inv asegs m ->
evt asegs (fun ms =>
(sinit <> 0 /\ ms = MS (mkR (Z_to_bv 64 0x97438) sp gp tp t0 t1 t2 s0 s1 s1 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 sinit) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_stream_clear_h) fc None m (seg_rom asegs))
\/ (sinit = 0 /\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 sinit) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0x97438) fc None m (seg_rom asegs)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 sinit) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (ret_pc ra) fc None m (seg_rom asegs)).
Proof.
intros until m. intros -> SR MI. unfold A_stream_clear_h.
replace (ret_pc (Z_to_bv 64 0x9742c)) with (Z_to_bv 64 0x9742c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
destruct (Z.eq_dec sinit 0) as [-> | NE].
- astep. try sh_if. apply evt_done. right. split; reflexivity.
- astep. rewrite (bv_eqb_lit_ne_h sinit 0) by lia. cbn [negb]. ato 0xb8b64. apply evt_done. left. split; [exact NE| reflexivity].
Qed.

Lemma cl_w5 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (m : mem),
ra = Z_to_bv 64 0x971b0 -> mem_inv asegs m ->
evt asegs (fun ms => ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_XT) fc None m (seg_rom asegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (ret_pc ra) fc None m (seg_rom asegs)).
Proof.
intros until m. intros -> MI. unfold A_XT.
replace (ret_pc (Z_to_bv 64 0x971b0)) with (Z_to_bv 64 0x971b0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0x971fc. apply evt_done. reflexivity.
Qed.
