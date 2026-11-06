(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0j2 X0hi X0j3 X0gi X02b X0j0.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1dg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.PA Require Import X1e9.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19l X183 X19m X173 X0ta X19k.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ta OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19k.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1dg.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.PA.X1e9.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition allocas_unpoison_entry : Z := 0x51f50.

Lemma allocas_unpoison_nop_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (top bottom : Z),
a0 = Z_to_bv 64 top -> a1 = Z_to_bv 64 bottom -> 0 <= top < 2^64 -> 0 <= bottom < 2^64 -> (top = 0 \/ bottom < top) ->
mem_inv bsegs m ->
evt bsegs (fun ms' => exists (a2' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 allocas_unpoison_entry) fc None m (seg_rom bsegs)).
Proof.
intros until bottom. intros -> -> Ht Hb Hc MI. unfold allocas_unpoison_entry.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (EUb : bv_unsigned (Z_to_bv 64 bottom) = bottom) by (apply unsigned_lit; lia).
zstep. zstep.
assert (C : negb (bv_ltu (Z_to_bv 64 (top + -1)) (Z_to_bv 64 bottom)) = true).
{ unfold bv_ltu. rewrite EUb. apply negb_true_iff, Z.ltb_ge.
destruct (Z.eq_dec top 0) as [->|NZ].
- change (bv_unsigned (Z_to_bv 64 (0 + -1))) with 18446744073709551615. lia.
- rewrite unsigned_lit by lia. lia. }
rewrite C; cbv iota.
zstep.
apply evt_done. eexists. reflexivity.
Qed.

Definition allocas_unpoison_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(top bottom lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(shad top, shad top + (bottom - top) / 8); (bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp)
/\ rw_cells bsegs m' (shad top) [CB (Z.to_nat ((bottom - top) / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat ((bottom - top) / 8)))].

Lemma allocas_unpoison_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (top bottom lo : Z) (shj : list byte),
a0 = Z_to_bv 64 top -> a1 = Z_to_bv 64 bottom -> 0 < top -> top <= bottom -> bottom < 2^47 -> addr_in_mem top ->
m2s_cells m -> setshadow_cells m ->
rw_cells bsegs m (shad top) [CB (Z.to_nat ((bottom - top) / 8)) shj] ->
stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 -> 0x65b000 <= lo -> shad top + (bottom - top) / 8 <= lo ->
mem_inv bsegs m ->
evt bsegs (allocas_unpoison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc top bottom lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 allocas_unpoison_entry) fc None m (seg_rom bsegs)).
Proof.
intros until shj. intros -> -> Ht Htb Hb AIM M2S SS SH ST LO ILO SHLO MI. unfold allocas_unpoison_entry.
destruct M2S as (M2a & M2b & M2c). destruct SS as (SS1 & SS2).
unfold g_got_real_memset, g_real_memset, musl_memset_entry in *.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl [(shad top, shad top + (bottom - top) / 8); (bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
pose proof (wmono_refl bsegs m) as WM.
assert (EUb : bv_unsigned (Z_to_bv 64 bottom) = bottom) by (apply unsigned_lit; lia).
assert (EUt : bv_unsigned (Z_to_bv 64 (top + -1)) = top + -1) by (apply unsigned_lit; lia).
assert (SHR : 0x7fff8000 <= shad top) by (unfold shad, SHB; pose proof (Z.div_pos top 8 ltac:(lia) ltac:(lia)); lia).
zstep. zstep. unfold bv_ltu. rewrite EUb, EUt. ifF.
carve_frame 32%nat ST.
do 8 zstep. zstep; fix_lit_store. zstep. zstep.
call (m2s_3d1d8_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ top).
1: reflexivity.
1: exact AIM.
1: exact (conj M2a (conj M2b M2c)).
1: assumption.
do 8 zstep.
release_frame FR ST (bv_unsigned sp).
assert (ESZ : (bottom - top) ≫ 3 = (bottom - top) / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
rewrite ?ESZ.
zstep.
call (memset_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (shad top) 0 ((bottom - top) / 8) shj).
all: try eassumption; try (pose proof (Z.div_pos (bottom - top) 8 ltac:(lia) ltac:(lia)); assert ((bottom - top) / 8 <= 2^44) by (apply Z.div_le_upper_bound; lia); lia).
apply evt_done. unfold allocas_unpoison_post.
do 16 eexists. split; [reflexivity|].
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.
End B_TWIN.

Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition allocas_unpoison_entry : Z := 0x51e64.

Lemma allocas_unpoison_nop_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (top bottom : Z),
a0 = Z_to_bv 64 top -> a1 = Z_to_bv 64 bottom -> 0 <= top < 2^64 -> 0 <= bottom < 2^64 -> (top = 0 \/ bottom < top) ->
mem_inv asegs m ->
evt asegs (fun ms' => exists (a2' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 allocas_unpoison_entry) fc None m (seg_rom asegs)).
Proof.
intros until bottom. intros -> -> Ht Hb Hc MI. unfold allocas_unpoison_entry.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (EUb : bv_unsigned (Z_to_bv 64 bottom) = bottom) by (apply unsigned_lit; lia).
zstep. zstep.
assert (C : negb (bv_ltu (Z_to_bv 64 (top + -1)) (Z_to_bv 64 bottom)) = true).
{ unfold bv_ltu. rewrite EUb. apply negb_true_iff, Z.ltb_ge.
destruct (Z.eq_dec top 0) as [->|NZ].
- change (bv_unsigned (Z_to_bv 64 (0 + -1))) with 18446744073709551615. lia.
- rewrite unsigned_lit by lia. lia. }
rewrite C; cbv iota.
zstep.
apply evt_done. eexists. reflexivity.
Qed.

Definition allocas_unpoison_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(top bottom lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(shad top, shad top + (bottom - top) / 8); (bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' (shad top) [CB (Z.to_nat ((bottom - top) / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat ((bottom - top) / 8)))].

Lemma allocas_unpoison_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (top bottom lo : Z) (shj : list byte),
a0 = Z_to_bv 64 top -> a1 = Z_to_bv 64 bottom -> 0 < top -> top <= bottom -> bottom < 2^47 -> addr_in_mem top ->
m2s_cells m -> setshadow_cells m ->
rw_cells asegs m (shad top) [CB (Z.to_nat ((bottom - top) / 8)) shj] ->
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 -> 0x652000 <= lo -> shad top + (bottom - top) / 8 <= lo ->
mem_inv asegs m ->
evt asegs (allocas_unpoison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc top bottom lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 allocas_unpoison_entry) fc None m (seg_rom asegs)).
Proof.
intros until shj. intros -> -> Ht Htb Hb AIM M2S SS SH ST LO ILO SHLO MI. unfold allocas_unpoison_entry.
destruct M2S as (M2a & M2b & M2c). destruct SS as (SS1 & SS2).
unfold g_got_real_memset, g_real_memset, musl_memset_entry in *.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl [(shad top, shad top + (bottom - top) / 8); (bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
assert (EUb : bv_unsigned (Z_to_bv 64 bottom) = bottom) by (apply unsigned_lit; lia).
assert (EUt : bv_unsigned (Z_to_bv 64 (top + -1)) = top + -1) by (apply unsigned_lit; lia).
assert (SHR : 0x7fff8000 <= shad top) by (unfold shad, SHB; pose proof (Z.div_pos top 8 ltac:(lia) ltac:(lia)); lia).
zstep. zstep. unfold bv_ltu. rewrite EUb, EUt. ifF.
carve_frame 32%nat ST.
do 8 zstep. zstep; fix_lit_store. zstep. zstep.
call (m2s_3d1d8_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ top).
1: reflexivity.
1: exact AIM.
1: exact (conj M2a (conj M2b M2c)).
1: assumption.
do 8 zstep.
release_frame FR ST (bv_unsigned sp).
assert (ESZ : (bottom - top) ≫ 3 = (bottom - top) / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
rewrite ?ESZ.
zstep.
call (memset_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (shad top) 0 ((bottom - top) / 8) shj).
all: try eassumption; try (pose proof (Z.div_pos (bottom - top) 8 ltac:(lia) ltac:(lia)); assert ((bottom - top) / 8 <= 2^44) by (apply Z.div_le_upper_bound; lia); lia).
apply evt_done. unfold allocas_unpoison_post.
do 16 eexists. split; [reflexivity|].
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.
