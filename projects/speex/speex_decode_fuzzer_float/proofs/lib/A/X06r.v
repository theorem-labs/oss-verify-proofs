(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1df X1ck X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X0ae X0ah X09q X071 X06v.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Notation mem := (word -> option byte).
Definition A_ogg_sync_buffer_h : Z := 0xb8f80.
Definition A_ogg_sync_pageout_h : Z := 0xb92a8.
Definition PC_asan_memcpy_h : Z := 0x66314.
Definition ch_nb (brem : Z) : Z := if 200 <? brem then 200 else brem.
Lemma bv_eqb_lit_ne : forall r k, -2^31 <= r < 2^31 -> 0 <= k < 2^31 -> r <> k -> bv_eqb (Z_to_bv 64 r) (Z_to_bv 64 k) = false.
Proof.
intros r k Hr Hk NE. unfold bv_eqb. apply Z.eqb_neq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
intros E. Z.div_mod_to_equations. nia.
Qed.

Lemma ch_w1 : forall (S1 F brem lastg sser : Z) (ra sp gp tp t0 t1 t2 s0 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 Fr fc (m : mem),
0 < brem <= 4096 -> rw_cells asegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 (Z_to_bv 64 (F + 8480)) w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208) -> mem_inv asegs m -> 0 <= S1 < 2^62 ->
evt asegs (fun ms => exists m1 : mem,
ms = MS (mkR (Z_to_bv 64 0x96c2c) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 (F + 8480)) (Z_to_bv 64 (ch_nb brem)) (Z_to_bv 64 lastg) (Z_to_bv 64 sser) a4 a5 a6 a7
s2 s3 s4 (Z_to_bv 64 (ch_nb brem)) s6 (Z_to_bv 64 (F + 8480)) s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_ogg_sync_buffer_h) fc None m1 (seg_rom asegs)
/\ munch [(S1, S1 + 216)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ rw_cells asegs m1 S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 (Z_to_bv 64 brem) w96 w104 w112 (Z_to_bv 64 (F + 8480)) w128 w136 (Z_to_bv 64 lastg) w152 w160 w168 (Z_to_bv 64 sser) w184 w192 w200 w208))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 brem) a1 (Z_to_bv 64 lastg) (Z_to_bv 64 sser) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_CH) fc None m (seg_rom asegs)).
Proof.
intros until m. intros BR SP MI S1R. unfold hsp in *. unfold A_CH, A_ogg_sync_buffer_h, ch_nb.
pose proof (munch_refl [(S1, S1 + 216)] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0x96c14.
destruct (Z.ltb_spec 200 brem) as [LT|GE]; astep; sh_if.
- ato 0xb8f80. apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact SP].
- ato 0xb8f80. rewrite Z.add_0_r, swrap32_small by lia. apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact SP].
Qed.

Lemma ch_w2 : forall (S1 d nbr : Z) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 Fr fc (m : mem),
ra = Z_to_bv 64 0x96c2c -> rw_cells asegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 (Z_to_bv 64 d) w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208) -> mem_inv asegs m -> 0 <= S1 < 2^62 ->
evt asegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x96c38) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 (Z_to_bv 64 d) (Z_to_bv 64 nbr) a3 a4 a5 a6 a7
s2 s3 s4 (Z_to_bv 64 nbr) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 PC_asan_memcpy_h) fc None m (seg_rom asegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 nbr) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (ret_pc ra) fc None m (seg_rom asegs)).
Proof.
intros until m. intros -> SP MI S1R. unfold hsp in *. unfold PC_asan_memcpy_h.
replace (ret_pc (Z_to_bv 64 0x96c2c)) with (Z_to_bv 64 0x96c2c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0x66314. apply evt_done. reflexivity.
Qed.

Lemma ch_w3 : forall (S1 F nbr D : Z) (sy : sync_st unit) (bytes : list byte) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s8 s9 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 Fr fc (m : mem),
ra = Z_to_bv 64 0x96c38 -> 0 <= nbr -> sy_fill sy + nbr < 2^31 -> 0 < F -> 0 <= S1 < 2^62 -> F + 16384 <= S1 ->
(D + Z.of_nat (length bytes) <= S1 \/ S1 + 216 <= D) ->
sync_rep m (F + 8480) D sy bytes -> rw_cells asegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208) -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
ms = MS (mkR (Z_to_bv 64 0x96c54) sp gp tp t0' t1' t2' s0 (Z_to_bv 64 S1) (Z_to_bv 64 (F + 8480)) (Z_to_bv 64 (F + 8544)) a2' a3' a4' a5' a6' a7'
s2 s3 s4 (Z_to_bv 64 nbr) s6 (Z_to_bv 64 (F + 8480)) s8 s9 (Z_to_bv 64 (F + 8544)) s11 t3' t4' t5' t6') Fr (Z_to_bv 64 A_ogg_sync_pageout_h) fc None m1 (seg_rom asegs)
/\ munch [(S1, S1 + 216); (F + 8480, F + 8512)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ sync_rep m1 (F + 8480) D (snd (ogg_sync_wrote sy nbr)) bytes /\ rw_cells asegs m1 S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 (Z_to_bv 64 nbr) w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 nbr) s6 (Z_to_bv 64 (F + 8480)) s8 s9 (Z_to_bv 64 (F + 8544)) s11 t3 t4 t5 t6)
Fr (ret_pc ra) fc None m (seg_rom asegs)).
Proof.
intros until m. intros -> NB FILL FP S1R FS1 DSEP SY SP MI. unfold hsp in *. unfold A_ogg_sync_pageout_h.
replace (ret_pc (Z_to_bv 64 0x96c38)) with (Z_to_bv 64 0x96c38) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(S1, S1 + 216); (F + 8480, F + 8512)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(S1, S1 + 216)] m) as MU2. pose proof (wmono_refl asegs m) as WM2.
ato 0x96c40.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
apply (sync_rep_transport [(S1, S1 + 216)] m mc (F + 8480) D sy bytes MU2 WM2) in SY; [| cbn [disjoint_from]; split; [lia| exact I] | cbn [disjoint_from]; split; [lia| exact I]] end.
clear MU2 WM2.
ato 0x96c44. astep.
call (ogg_sync_wrote_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc _ (F + 8480) D sy bytes nbr); [ unfold wz; reflexivity | unfold wz; reflexivity | exact NB | exact FILL | exact SY | assumption | ].
ato 0xb92a8.
apply evt_done. do 14 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption| exact SP].
Qed.

Lemma ch_w4 : forall (S1 F r sinit lastg : Z) (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w160 w168 w176 w184 w192 w200 w208 Fr fc (m : mem),
ra = Z_to_bv 64 0x96c54 -> -2^31 <= r < 2^31 -> (sinit = 0 \/ sinit = 1) ->
rw_cells asegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 (Z_to_bv 64 lastg) (Z_to_bv 64 (F + 8688)) w160 w168 w176 w184 w192 w200 w208) -> mem_inv asegs m -> 0 <= S1 < 2^62 ->
evt asegs (fun ms =>
(r = 1 /\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 r) (Z_to_bv 64 (if sinit =? 0 then 1 else 0)) (Z_to_bv 64 lastg) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 (Z_to_bv 64 (F + 8688)) (Z_to_bv 64 sinit) s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_PB) fc None m (seg_rom asegs))
\/ (r <> 1 /\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 r) (Z_to_bv 64 1) (Z_to_bv 64 lastg) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 (Z_to_bv 64 (F + 8688)) (Z_to_bv 64 sinit) s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_PX) fc None m (seg_rom asegs)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 sinit) s9 s10 s11 t3 t4 t5 t6)
Fr (ret_pc ra) fc None m (seg_rom asegs)).
Proof.
intros until m. intros -> RR SI SP MI S1R. unfold hsp in *. unfold A_PB, A_PX.
replace (ret_pc (Z_to_bv 64 0x96c54)) with (Z_to_bv 64 0x96c54) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0x96c58.
destruct (Z.eq_dec r 1) as [-> | NE].
- astep. try sh_if. destruct SI as [-> | ->]; ato 0x96c68; apply evt_done; left; (split; [reflexivity|]); reflexivity.
- astep. rewrite (bv_eqb_lit_ne r 1) by lia. cbn [negb]. ato 0x97174. apply evt_done. right. split; [exact NE| reflexivity].
Qed.

Lemma pn_w1 : forall (S1 F : Z) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 Fr fc (m : mem),
rw_cells asegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 (Z_to_bv 64 (F + 8480)) w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208) -> mem_inv asegs m -> 0 <= S1 < 2^62 ->
evt asegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x97158) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 (F + 8480)) (Z_to_bv 64 (F + 8544)) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 (F + 8544)) s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_ogg_sync_pageout_h) fc None m (seg_rom asegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 (F + 8544)) s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_PN) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SP MI S1R. unfold hsp in *. unfold A_PN, A_ogg_sync_pageout_h.
ato 0xb92a8. apply evt_done. reflexivity.
Qed.

Lemma pn_w2 : forall (S1 r lastg : Z) (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w152 w160 w168 w176 w184 w192 w200 w208 Fr fc (m : mem),
ra = Z_to_bv 64 0x97158 -> -2^31 <= r < 2^31 ->
rw_cells asegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 (Z_to_bv 64 lastg) w152 w160 w168 w176 w184 w192 w200 w208) -> mem_inv asegs m -> 0 <= S1 < 2^62 ->
evt asegs (fun ms =>
(r = 1 /\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 r) (Z_to_bv 64 0) (Z_to_bv 64 lastg) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 (Z_to_bv 64 1) s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_PB) fc None m (seg_rom asegs))
\/ (r <> 1 /\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 r) (Z_to_bv 64 0) (Z_to_bv 64 lastg) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 (Z_to_bv 64 1) s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 A_PX) fc None m (seg_rom asegs)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (ret_pc ra) fc None m (seg_rom asegs)).
Proof.
intros until m. intros -> RR SP MI S1R. unfold hsp in *. unfold A_PB, A_PX.
replace (ret_pc (Z_to_bv 64 0x97158)) with (Z_to_bv 64 0x97158) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0x97164.
destruct (Z.eq_dec r 1) as [-> | NE]; astep.
- apply evt_done. left. split; reflexivity.
- rewrite (bv_eqb_lit_ne r 1) by lia. cbn [negb]. ato 0x97174. apply evt_done. right. split; [exact NE| reflexivity].
Qed.
