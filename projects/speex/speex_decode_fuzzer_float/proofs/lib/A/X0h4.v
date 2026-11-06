(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0j2 X0hi X0j3 X0gi X0h2 X0h3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1dg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.PA Require Import X1e9.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19l X183 X19m X173 X17n X17o.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17o.
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

Definition sf5_entry : Z := 0x519c0.
Definition UAR_MAGIC8 : Z := 0xf5f5f5f5f5f5f5f5.

Definition sf5_W (FSB pos usp : Z) : list (Z * Z) :=
[(fl_base FSB 5 + pos, fl_base FSB 5 + pos + 1);
(shad (frame_addr FSB 5 pos), shad (frame_addr FSB 5 pos) + 256);
(usp - 16, usp)].

Definition sf5_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(FSB pos : Z) (fl : list Z) (lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch (sf5_W FSB pos (bv_unsigned sp)) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp)
/\ fs_flags FSB 5 m' (upd fl (Z.to_nat pos) 0)
/\ rw_cells bsegs m' (shad (frame_addr FSB 5 pos)) (repeat (C8 (Z_to_bv 64 UAR_MAGIC8)) 32).

Lemma stack_free_5_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (FSB pos : Z) (fl : list Z) (lo : Z) (shj : list byte),
a0 = Z_to_bv 64 (frame_addr FSB 5 pos) -> 0 <= pos < 512 ->
fs_flags FSB 5 m fl -> flags_ok 5 fl ->
rw_cells bsegs m (frame_addr FSB 5 pos + 2040) [C8 (Z_to_bv 64 (fl_base FSB 5 + pos))] ->
rw_cells bsegs m (shad (frame_addr FSB 5 pos)) [CB 256 shj] ->
m2s_cells m ->
FSB_ok2 FSB -> 0x10007fff8000 <= lo -> FSB + kFakeStackSize <= lo ->
stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 ->
mem_inv bsegs m ->
evt bsegs (sf5_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FSB pos fl lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 sf5_entry) fc None m (seg_rom bsegs)).
Proof.
intros until shj. intros -> Hpos FL OK FRL SHm M2S FSOK HLO FSL ST LO SPH MI.
pose proof OK as (LEN & _). change (NF 5) with 512 in LEN.
pose proof FSOK as (FS1 & FS0 & FS2 & FS3). unfold kHighShadowEnd, kFakeStackSize in *.
rewrite shad_frame in SHm by lia. unfold frame_addr, fsz in FRL, SHm |- *.
change (5 * 2 ^ 20) with 5242880 in *. change (64 * 2 ^ 5) with 2048 in *. change (5 * 2 ^ 17) with 655360 in SHm. change (2048 / 8) with 256 in SHm.
replace (FSB + 36864 + 5242880 + pos * 2048) with (FSB + 5279744 + pos * 2048) in * by lia.
set (F8 := FSB / 8) in *. assert (EF8 : FSB = 8 * F8) by (unfold F8; apply Z.div_exact; lia).
clearbody F8.
replace (SHB + F8 + 4608 + 655360 + pos * 256) with (F8 + pos * 256 + 2148110848) in SHm by (unfold SHB; lia).
unfold fs_flags, fl_base, flags_off in FL, FRL. change (32768 - 2 ^ (15 - 5)) with 31744 in FL, FRL.
replace (FSB + 4096 + 31744) with (FSB + 35840) in FL, FRL by lia.
assert (LENM : Z.of_nat (length (map b8 fl)) = 512) by (rewrite length_map; exact LEN).
destruct M2S as (M2a & M2b & M2c).
unfold sf5_entry in *.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl [(FSB + 35840 + pos, FSB + 35840 + pos + 1); (F8 + pos * 256 + 2148110848, F8 + pos * 256 + 2148110848 + 256);
(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
pose proof (wmono_refl bsegs m) as WM.
carve_frame 16%nat ST.
do 5 zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (u8arr_store_ok bsegs mm (FSB + 35840) (map b8 fl) pos (wa (FSB + 35840 + pos)) FL ltac:(lia) ltac:(f_equal; lia)) as SOK;
pose proof (u8arr_write bsegs mm (FSB + 35840) (map b8 fl) pos (b8 0) FL ltac:(lia)) as FL2 end.
zstep. change (le1 (Z_to_bv 64 0)) with [b8 0]. clear FL. store_done.
zstep.
call (m2s_3d1d8_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (FSB + 5279744 + pos * 2048)).
1: reflexivity.
1: { apply (fsb_in_mem FSB _ FSOK). unfold kFakeStackSize. lia. }
1: exact (conj M2a (conj M2b M2c)).
1: assumption.
assert (ESH : shad (FSB + 5279744 + pos * 2048) = F8 + pos * 256 + 2148110848).
{ unfold shad, SHB. rewrite EF8. replace (8 * F8 + 5279744 + pos * 2048) with ((F8 + 659968 + pos * 256) * 8) by lia.
rewrite Z.div_mul by lia. lia. }
rewrite ESH.
do 2 zstep.
do 32 lstep.
do 3 zstep.
release_frame FR ST (bv_unsigned sp).
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mE end.
apply evt_done. unfold sf5_post.
do 15 eexists. exists mE.
split; [reflexivity|].
assert (EQ8 : FSB / 8 = F8) by (rewrite EF8, Z.mul_comm, Z.div_mul by lia; reflexivity).
assert (ESF : shad (frame_addr FSB 5 pos) = F8 + pos * 256 + 2148110848).
{ rewrite shad_frame by lia. rewrite EQ8. unfold fsz, SHB. change (5 * 2 ^ 17) with 655360. change (64 * 2 ^ 5 / 8) with 256. lia. }
split.
{ unfold sf5_W. rewrite ESF. unfold fl_base, flags_off. change (32768 - 2 ^ (15 - 5)) with 31744.
replace (FSB + 4096 + 31744 + pos) with (FSB + 35840 + pos) by lia. exact MU. }
split; [exact WM|]. split; [assumption|]. split; [exact ST|].
split.
{ unfold fs_flags. rewrite map_b8_upd. replace (fl_base FSB 5) with (FSB + 35840) by (unfold fl_base, flags_off; cbn; lia). exact FL2. }
rewrite ESF. unfold UAR_MAGIC8. cbn [repeat]. eassumption.
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

Definition sf5_entry : Z := 0x518d4.
Definition UAR_MAGIC8 : Z := 0xf5f5f5f5f5f5f5f5.

Definition sf5_W (FSB pos usp : Z) : list (Z * Z) :=
[(fl_base FSB 5 + pos, fl_base FSB 5 + pos + 1);
(shad (frame_addr FSB 5 pos), shad (frame_addr FSB 5 pos) + 256);
(usp - 16, usp)].

Definition sf5_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(FSB pos : Z) (fl : list Z) (lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch (sf5_W FSB pos (bv_unsigned sp)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ fs_flags FSB 5 m' (upd fl (Z.to_nat pos) 0)
/\ rw_cells asegs m' (shad (frame_addr FSB 5 pos)) (repeat (C8 (Z_to_bv 64 UAR_MAGIC8)) 32).

Lemma stack_free_5_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (FSB pos : Z) (fl : list Z) (lo : Z) (shj : list byte),
a0 = Z_to_bv 64 (frame_addr FSB 5 pos) -> 0 <= pos < 512 ->
fs_flags FSB 5 m fl -> flags_ok 5 fl ->
rw_cells asegs m (frame_addr FSB 5 pos + 2040) [C8 (Z_to_bv 64 (fl_base FSB 5 + pos))] ->
rw_cells asegs m (shad (frame_addr FSB 5 pos)) [CB 256 shj] ->
m2s_cells m ->
FSB_ok2 FSB -> 0x10007fff8000 <= lo -> FSB + kFakeStackSize <= lo ->
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 ->
mem_inv asegs m ->
evt asegs (sf5_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FSB pos fl lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 sf5_entry) fc None m (seg_rom asegs)).
Proof.
intros until shj. intros -> Hpos FL OK FRL SHm M2S FSOK HLO FSL ST LO SPH MI.
pose proof OK as (LEN & _). change (NF 5) with 512 in LEN.
pose proof FSOK as (FS1 & FS0 & FS2 & FS3). unfold kHighShadowEnd, kFakeStackSize in *.
rewrite shad_frame in SHm by lia. unfold frame_addr, fsz in FRL, SHm |- *.
change (5 * 2 ^ 20) with 5242880 in *. change (64 * 2 ^ 5) with 2048 in *. change (5 * 2 ^ 17) with 655360 in SHm. change (2048 / 8) with 256 in SHm.
replace (FSB + 36864 + 5242880 + pos * 2048) with (FSB + 5279744 + pos * 2048) in * by lia.
set (F8 := FSB / 8) in *. assert (EF8 : FSB = 8 * F8) by (unfold F8; apply Z.div_exact; lia).
clearbody F8.
replace (SHB + F8 + 4608 + 655360 + pos * 256) with (F8 + pos * 256 + 2148110848) in SHm by (unfold SHB; lia).
unfold fs_flags, fl_base, flags_off in FL, FRL. change (32768 - 2 ^ (15 - 5)) with 31744 in FL, FRL.
replace (FSB + 4096 + 31744) with (FSB + 35840) in FL, FRL by lia.
assert (LENM : Z.of_nat (length (map b8 fl)) = 512) by (rewrite length_map; exact LEN).
destruct M2S as (M2a & M2b & M2c).
unfold sf5_entry in *.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl [(FSB + 35840 + pos, FSB + 35840 + pos + 1); (F8 + pos * 256 + 2148110848, F8 + pos * 256 + 2148110848 + 256);
(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 16%nat ST.
do 5 zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (u8arr_store_ok asegs mm (FSB + 35840) (map b8 fl) pos (wa (FSB + 35840 + pos)) FL ltac:(lia) ltac:(f_equal; lia)) as SOK;
pose proof (u8arr_write asegs mm (FSB + 35840) (map b8 fl) pos (b8 0) FL ltac:(lia)) as FL2 end.
zstep. change (le1 (Z_to_bv 64 0)) with [b8 0]. clear FL. store_done.
zstep.
call (m2s_3d1d8_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (FSB + 5279744 + pos * 2048)).
1: reflexivity.
1: { apply (fsb_in_mem FSB _ FSOK). unfold kFakeStackSize. lia. }
1: exact (conj M2a (conj M2b M2c)).
1: assumption.
assert (ESH : shad (FSB + 5279744 + pos * 2048) = F8 + pos * 256 + 2148110848).
{ unfold shad, SHB. rewrite EF8. replace (8 * F8 + 5279744 + pos * 2048) with ((F8 + 659968 + pos * 256) * 8) by lia.
rewrite Z.div_mul by lia. lia. }
rewrite ESH.
do 2 zstep.
do 32 lstep.
do 3 zstep.
release_frame FR ST (bv_unsigned sp).
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mE end.
apply evt_done. unfold sf5_post.
do 15 eexists. exists mE.
split; [reflexivity|].
assert (EQ8 : FSB / 8 = F8) by (rewrite EF8, Z.mul_comm, Z.div_mul by lia; reflexivity).
assert (ESF : shad (frame_addr FSB 5 pos) = F8 + pos * 256 + 2148110848).
{ rewrite shad_frame by lia. rewrite EQ8. unfold fsz, SHB. change (5 * 2 ^ 17) with 655360. change (64 * 2 ^ 5 / 8) with 256. lia. }
split.
{ unfold sf5_W. rewrite ESF. unfold fl_base, flags_off. change (32768 - 2 ^ (15 - 5)) with 31744.
replace (FSB + 4096 + 31744 + pos) with (FSB + 35840 + pos) by lia. exact MU. }
split; [exact WM|]. split; [assumption|]. split; [exact ST|].
split.
{ unfold fs_flags. rewrite map_b8_upd. replace (fl_base FSB 5) with (FSB + 35840) by (unfold fl_base, flags_off; cbn; lia). exact FL2. }
rewrite ESF. unfold UAR_MAGIC8. cbn [repeat]. eassumption.
Qed.
