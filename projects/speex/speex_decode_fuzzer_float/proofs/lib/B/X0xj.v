(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1dk X1cs X1dg X1df X1ck X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X071.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X0z5 X110 X112 X10d X0xn.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Notation mem := (word -> option byte).
Definition A_ogg_sync_buffer_h : Z := 0xc16b0.
Definition A_ogg_sync_pageout_h : Z := 0xc19d8.
Definition PC_asan_memcpy_h : Z := 0x66400.
Definition ch_nb (brem : Z) : Z := if 200 <? brem then 200 else brem.
Lemma bv_eqb_lit_ne : forall r k, -2^31 <= r < 2^31 -> 0 <= k < 2^31 -> r <> k -> bv_eqb (Z_to_bv 64 r) (Z_to_bv 64 k) = false.
Proof.
intros r k Hr Hk NE. unfold bv_eqb. apply Z.eqb_neq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
intros E. Z.div_mod_to_equations. nia.
Qed.

Lemma ch_w1 : forall (S1 F brem : Z) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 Fr fc (m : mem),
0 < brem <= 4096 -> rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 (Z_to_bv 64 (F + 8480)) w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240) -> mem_inv bsegs m -> 0 <= S1 < 2^62 ->
evt bsegs (fun ms =>
ms = MS (mkR (Z_to_bv 64 0x96d20) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 (F + 8480)) (Z_to_bv 64 (ch_nb brem)) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (F + 8480)) s3 s4 s5 s6 (Z_to_bv 64 (ch_nb brem)) (Z_to_bv 64 brem) s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_ogg_sync_buffer_h) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 brem) s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_CH) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros BR SP MI S1R. unfold hsp in *. unfold A_CH, A_ogg_sync_buffer_h, ch_nb.
ato 0x96d08.
destruct (Z.ltb_spec 200 brem) as [LT|GE]; astep; sh_if.
- ato 0xc16b0. apply evt_done. reflexivity.
- ato 0xc16b0. rewrite Z.add_0_r, swrap32_small by lia. apply evt_done. reflexivity.
Qed.

Lemma ch_w2 : forall (S1 d nbr : Z) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s10 s11 t3 t4 t5 t6 : word) Fr fc (m : mem),
ra = Z_to_bv 64 0x96d20 -> mem_inv bsegs m ->
evt bsegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x96d2c) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 (Z_to_bv 64 d) (Z_to_bv 64 nbr) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 (Z_to_bv 64 nbr) s8 (Z_to_bv 64 d) s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 PC_asan_memcpy_h) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 nbr) s8 (Z_to_bv 64 d) s10 s11 t3 t4 t5 t6)
Fr (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> MI. unfold PC_asan_memcpy_h.
replace (ret_pc (Z_to_bv 64 0x96d20)) with (Z_to_bv 64 0x96d20) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0x66400. apply evt_done. reflexivity.
Qed.

Lemma ch_w3 : forall (S1 F nbr brem D : Z) (sy : sync_st unit) (bytes : list byte) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w120 w128 w136 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 Fr fc (m : mem),
ra = Z_to_bv 64 0x96d2c -> 0 <= nbr <= brem -> brem <= 4096 -> sy_fill sy + nbr < 2^31 -> 0 < F -> 0 <= S1 < 2^62 -> F + 16384 <= S1 ->
(D + Z.of_nat (length bytes) <= S1 \/ S1 + 248 <= D) ->
sync_rep m (F + 8480) D sy bytes -> rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 (Z_to_bv 64 (F + 8480)) w120 w128 w136 (Z_to_bv 64 (F + 8544)) w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240) -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
ms = MS (mkR (Z_to_bv 64 0x96d5c) sp gp tp t0' t1' t2' s0 (Z_to_bv 64 S1) (Z_to_bv 64 (F + 8480)) (Z_to_bv 64 (F + 8544)) a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (F + 8480)) s3 s4 s5 s6 (Z_to_bv 64 nbr) (Z_to_bv 64 brem) (Z_to_bv 64 (F + 8544)) s10 s11 t3' t4' t5' t6') Fr (Z_to_bv 64 A_ogg_sync_pageout_h) fc None m1 (seg_rom bsegs)
/\ munch [(S1, S1 + 248); (F + 8480, F + 8512)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ sync_rep m1 (F + 8480) D (snd (ogg_sync_wrote sy nbr)) bytes /\ rw_cells bsegs m1 S1 (hsp w0 w8 w16 w24 w32 (Z_to_bv 64 (brem - nbr)) w48 w56 w64 w72 w80 w88 w96 w104 (Z_to_bv 64 (F + 8480)) w120 w128 w136 (Z_to_bv 64 (F + 8544)) w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (F + 8480)) s3 s4 s5 s6 (Z_to_bv 64 nbr) (Z_to_bv 64 brem) s9 s10 s11 t3 t4 t5 t6)
Fr (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> NB BR FILL FP S1R FS1 DSEP SY SP MI. unfold hsp in *. unfold A_ogg_sync_pageout_h.
replace (ret_pc (Z_to_bv 64 0x96d2c)) with (Z_to_bv 64 0x96d2c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(S1, S1 + 248); (F + 8480, F + 8512)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
ato 0x96d34. astep.
call (ogg_sync_wrote_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc _ (F + 8480) D sy bytes nbr); [ unfold wz; reflexivity | unfold wz; reflexivity | lia | exact FILL | exact SY | assumption | ].

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(S1, S1 + 248)] mc) as MU2; pose proof (wmono_refl bsegs mc) as WM2; rename POST into SYW end.
ato 0x96d44.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch type of SYW with sync_rep ?m0 _ _ _ _ =>
apply (sync_rep_transport [(S1, S1 + 248)] m0 mc (F + 8480) D _ bytes MU2 WM2) in SYW; [| cbn [disjoint_from]; split; [lia| exact I] | cbn [disjoint_from]; split; [lia| exact I]] end end.
clear MU2 WM2.

destruct (Z.eq_dec nbr 0) as [E0|NZ]; [subst nbr|];
(bato 0xc19d8;
apply evt_done; do 14 eexists; split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact SYW| exact SP]).
Qed.

Lemma ch_w4 : forall (S1 F r sinit : Z) (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 Fr fc (m : mem),
ra = Z_to_bv 64 0x96d5c -> -2^31 <= r < 2^31 -> (sinit = 0 \/ sinit = 1) ->
rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 (Z_to_bv 64 (F + 8688)) w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240) -> mem_inv bsegs m -> 0 <= S1 < 2^62 ->
evt bsegs (fun ms =>
(r = 1 /\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 r) (Z_to_bv 64 (if sinit =? 0 then 1 else 0)) a2 a3 a4 a5 a6 a7
s2 s3 s4 (Z_to_bv 64 sinit) s6 (Z_to_bv 64 (F + 8688)) s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_PB) fc None m (seg_rom bsegs))
\/ (r <> 1 /\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 r) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7
s2 s3 s4 (Z_to_bv 64 sinit) s6 (Z_to_bv 64 (F + 8688)) s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_PX) fc None m (seg_rom bsegs)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 sinit) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> RR SI SP MI S1R. unfold hsp in *. unfold A_PB, A_PX.
replace (ret_pc (Z_to_bv 64 0x96d5c)) with (Z_to_bv 64 0x96d5c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0x96d60.
destruct (Z.eq_dec r 1) as [-> | NE].
- astep. try sh_if. destruct SI as [-> | ->]; ato 0x96d6c; apply evt_done; left; (split; [reflexivity|]); reflexivity.
- astep. rewrite (bv_eqb_lit_ne r 1) by lia. cbn [negb]. ato 0x97418. apply evt_done. right. split; [exact NE| reflexivity].
Qed.

Lemma pn_w1 : forall (S1 F : Z) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 Fr fc (m : mem),
rw_cells bsegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 (Z_to_bv 64 (F + 8480)) w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240) -> mem_inv bsegs m -> 0 <= S1 < 2^62 ->
evt bsegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x96ef4) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 (F + 8480)) (Z_to_bv 64 (F + 8544)) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (F + 8544)) s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_ogg_sync_pageout_h) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (F + 8544)) s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_PN) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SP MI S1R. unfold hsp in *. unfold A_PN, A_ogg_sync_pageout_h.
ato 0xc19d8. apply evt_done. reflexivity.
Qed.

Lemma pn_w2 : forall (S1 r : Z) (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (m : mem),
ra = Z_to_bv 64 0x96ef4 -> -2^31 <= r < 2^31 -> mem_inv bsegs m ->
evt bsegs (fun ms =>
(r = 1 /\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 r) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
s2 s3 s4 (Z_to_bv 64 1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_PB) fc None m (seg_rom bsegs))
\/ (r <> 1 /\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 r) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
s2 s3 s4 (Z_to_bv 64 1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_PX) fc None m (seg_rom bsegs)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> RR MI. unfold A_PB, A_PX.
replace (ret_pc (Z_to_bv 64 0x96ef4)) with (Z_to_bv 64 0x96ef4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0x96efc.
destruct (Z.eq_dec r 1) as [-> | NE]; astep.
- try sh_if. apply evt_done. left. split; reflexivity.
- rewrite (bv_eqb_lit_ne r 1) by lia. cbn [negb]. ato 0x97418. apply evt_done. right. split; [exact NE| reflexivity].
Qed.
