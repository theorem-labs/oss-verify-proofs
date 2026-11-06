(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1dg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.PA Require Import X1e9 X1e5.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0j2 X0hi X0j3 X03z X04v X0jg X00b X046.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X057.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require X023.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19l X183 X19m X0ux X0vt X19x X0ra X0v4.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0w5.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0t2.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ux OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v4.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w5.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition fpfr (usp : Z) (junk : list byte) (ra s0 s1 s2 : word) : list cell :=
[CB 8 junk; C8 (Z_to_bv 64 (usp + -48)); C8 (Z_to_bv 64 (usp + -48)); C8 (Z_to_bv 64 (usp + -48)); C8 s2; C8 s1; C8 s0; C8 ra].

Definition fpwA1_post (usp : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 a3 a4 a5 a6 a7 : word)
(F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (m' : mem) (t0 t1 t2 a3' a4' a5' a6' a7' t3 t4 t5 t6 : word) (junk : list byte),
ms' = MS (mkR (Z_to_bv 64 0x5a56c) (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 a1 a0 (Z_to_bv 64 0x20aa1) a1
(Z_to_bv 64 (usp + -48)) a3' a4' a5' a6' a7' (Z_to_bv 64 (usp + -48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x59658) fc None m' (seg_rom bsegs)
/\ munch [(usp - 128, usp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp + -112)
/\ rw_cells bsegs m' (usp + -112) (fpfr usp junk ra s0 s1 s2)
/\ rw_cells bsegs m' (usp + -48) [C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7].

Lemma fprintf_walkA1 : forall (usp lo : Z)
ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
stk bsegs m lo usp -> lo <= usp - 128 -> 0x65b000 <= lo -> usp <= 2^47 -> pfcells m -> mem_inv bsegs m ->
evt bsegs (fpwA1_post usp ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 a3 a4 a5 a6 a7 F fc lo m)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x56d08) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ST LO LOLO SPH PFC MI.
pose proof (munch_refl [(usp - 128, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (EU112 : bv_unsigned (Z_to_bv 64 (usp + -112)) = usp + -112) by (apply unsigned_lit; lia).
destruct PFC as (AI & GCF & CPF & RVP & RVF).
carve_frame 112%nat ST. rename FR into FRp.
apply (rw_cells_split_CB bsegs _ _ [] 112 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRp; [| reflexivity].
cbn [mk_CB_cells app] in FRp.
xsteps_to 0x6f79c%Z.
call try_init_spec; [exact AI | rewrite EU112; exact ST | rewrite EU112; lia | lia | assumption |].
rename POST into ST.
xsteps_to 0x6f79c%Z.
call try_init_spec; [exact AI | exact ST | rewrite EU112; lia | lia | assumption |].
rename POST into ST. rewrite EU112 in ST.
xsteps_to 0x59658%Z.
apply (proj1 (X0t2.rw_cells_app bsegs _ _ [_; _; _; _; _; _; _; _] _)) in FRp. destruct FRp as [FRp1 FRva].
cbn [cells_size csize Nat.add] in FRva. replace (usp + -112 + Z.of_nat 64) with (usp + -48) in FRva by lia.
apply evt_done. unfold fpwA1_post. do 14 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FRp1| exact FRva].
Qed.

Lemma fprintf_walkA2 : forall (usp : Z) (junk : list byte) (ra0 c0 c1 c2 : word)
ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
rw_cells bsegs m (usp + -112) (fpfr usp junk ra0 c0 c1 c2) -> ro_cells bsegs m 0xfdf30 [C8 (Z_to_bv 64 0xedf30)] ->
usp <= 2^47 -> 112 <= usp -> mem_inv bsegs m ->
evt bsegs (fun ms' => exists (a3' : word), ms' =
MS (mkR (Z_to_bv 64 0x5a5ac) (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 s0 s1 s1 s0 (Z_to_bv 64 (usp + -48)) a3' a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xedf30) fc None m (seg_rom bsegs))
(MS (mkR ra (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x5a56c) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros FRp1 RVF SPH SPL MI. unfold fpfr in FRp1.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (EU112 : bv_unsigned (Z_to_bv 64 (usp + -112)) = usp + -112) by (apply unsigned_lit; lia).
do 8 lstep.
apply evt_done. eexists. reflexivity.
Qed.

Lemma fprintf_walkB : forall (usp lo : Z) (junk : list byte) (a2 a3 a4 a5 a6 a7 : word)
(ra' ra gp tp t0 t1 t2 s0 s1 s0' s1' a0 a1 a2' a3' a4' a5' a6' a7' s2 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem),
stk bsegs m lo (usp + -112) -> lo <= usp + -112 -> usp <= 2^47 ->
rw_cells bsegs m (usp + -112) (fpfr usp junk ra s0 s1 s2) ->
rw_cells bsegs m (usp + -48) [C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] ->
mem_inv bsegs m ->
evt bsegs (fun ms' => (exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7'
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m (seg_rom bsegs))
/\ stk bsegs m lo usp)
(MS (mkR ra' (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 s0' s1' a0 a1 a2' a3' a4' a5' a6' a7' s2' s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6)
F (Z_to_bv 64 0x5a5ac) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ST LO UT FRp1 FRva MI. unfold fpfr in FRp1.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (EU112 : bv_unsigned (Z_to_bv 64 (usp + -112)) = usp + -112) by (apply unsigned_lit; lia).
do 6 lstep.
release_frame FRp1 ST (usp + -48).
release_frame FRva ST usp.
apply evt_done. split; [| exact ST]. do 14 eexists. first [reflexivity | f_equal; f_equal; apply Z_to_bv_eqm; lia].
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition fpfr (usp : Z) (junk : list byte) (ra s0 s1 s2 : word) : list cell :=
[CB 8 junk; C8 (Z_to_bv 64 (usp + -48)); C8 (Z_to_bv 64 (usp + -48)); C8 (Z_to_bv 64 (usp + -48)); C8 s2; C8 s1; C8 s0; C8 ra].

Definition fpwA1_post (usp : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 a3 a4 a5 a6 a7 : word)
(F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (m' : mem) (t0 t1 t2 a3' a4' a5' a6' a7' t3 t4 t5 t6 : word) (junk : list byte),
ms' = MS (mkR (Z_to_bv 64 0x5a480) (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 a1 a0 (Z_to_bv 64 0x20a67) a1
(Z_to_bv 64 (usp + -48)) a3' a4' a5' a6' a7' (Z_to_bv 64 (usp + -48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x5956c) fc None m' (seg_rom asegs)
/\ munch [(usp - 128, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -112)
/\ rw_cells asegs m' (usp + -112) (fpfr usp junk ra s0 s1 s2)
/\ rw_cells asegs m' (usp + -48) [C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7].

Lemma fprintf_walkA1 : forall (usp lo : Z)
ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
stk asegs m lo usp -> lo <= usp - 128 -> 0x652000 <= lo -> usp <= 2^47 -> pfcells m -> mem_inv asegs m ->
evt asegs (fpwA1_post usp ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 a3 a4 a5 a6 a7 F fc lo m)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x56c1c) fc None m (seg_rom asegs)).
Proof.
intros until m. intros ST LO LOLO SPH PFC MI.
pose proof (munch_refl [(usp - 128, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (EU112 : bv_unsigned (Z_to_bv 64 (usp + -112)) = usp + -112) by (apply unsigned_lit; lia).
destruct PFC as (AI & GCF & CPF & RVP & RVF).
carve_frame 112%nat ST. rename FR into FRp.
apply (rw_cells_split_CB asegs _ _ [] 112 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRp; [| reflexivity].
cbn [mk_CB_cells app] in FRp.
xsteps_to 0x6f6b0%Z.
call try_init_spec; [exact AI | rewrite EU112; exact ST | rewrite EU112; lia | lia | assumption |].
rename POST into ST.
xsteps_to 0x6f6b0%Z.
call try_init_spec; [exact AI | exact ST | rewrite EU112; lia | lia | assumption |].
rename POST into ST. rewrite EU112 in ST.
xsteps_to 0x5956c%Z.
apply (proj1 (X023.rw_cells_app asegs _ _ [_; _; _; _; _; _; _; _] _)) in FRp. destruct FRp as [FRp1 FRva].
cbn [cells_size csize Nat.add] in FRva. replace (usp + -112 + Z.of_nat 64) with (usp + -48) in FRva by lia.
apply evt_done. unfold fpwA1_post. do 14 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FRp1| exact FRva].
Qed.

Lemma fprintf_walkA2 : forall (usp : Z) (junk : list byte) (ra0 c0 c1 c2 : word)
ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
rw_cells asegs m (usp + -112) (fpfr usp junk ra0 c0 c1 c2) -> ro_cells asegs m 0xf56b0 [C8 (Z_to_bv 64 0xe56bc)] ->
usp <= 2^47 -> 112 <= usp -> mem_inv asegs m ->
evt asegs (fun ms' => exists (a3' : word), ms' =
MS (mkR (Z_to_bv 64 0x5a4c0) (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 s0 s1 s1 s0 (Z_to_bv 64 (usp + -48)) a3' a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xe56bc) fc None m (seg_rom asegs))
(MS (mkR ra (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x5a480) fc None m (seg_rom asegs)).
Proof.
intros until m. intros FRp1 RVF SPH SPL MI. unfold fpfr in FRp1.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (EU112 : bv_unsigned (Z_to_bv 64 (usp + -112)) = usp + -112) by (apply unsigned_lit; lia).
do 8 lstep.
apply evt_done. eexists. reflexivity.
Qed.

Lemma fprintf_walkB : forall (usp lo : Z) (junk : list byte) (a2 a3 a4 a5 a6 a7 : word)
(ra' ra gp tp t0 t1 t2 s0 s1 s0' s1' a0 a1 a2' a3' a4' a5' a6' a7' s2 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem),
stk asegs m lo (usp + -112) -> lo <= usp + -112 -> usp <= 2^47 ->
rw_cells asegs m (usp + -112) (fpfr usp junk ra s0 s1 s2) ->
rw_cells asegs m (usp + -48) [C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] ->
mem_inv asegs m ->
evt asegs (fun ms' => (exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7'
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m (seg_rom asegs))
/\ stk asegs m lo usp)
(MS (mkR ra' (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 s0' s1' a0 a1 a2' a3' a4' a5' a6' a7' s2' s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6)
F (Z_to_bv 64 0x5a4c0) fc None m (seg_rom asegs)).
Proof.
intros until m. intros ST LO UT FRp1 FRva MI. unfold fpfr in FRp1.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (EU112 : bv_unsigned (Z_to_bv 64 (usp + -112)) = usp + -112) by (apply unsigned_lit; lia).
do 6 lstep.
release_frame FRp1 ST (usp + -48).
release_frame FRva ST usp.
apply evt_done. split; [| exact ST]. do 14 eexists. first [reflexivity | f_equal; f_equal; apply Z_to_bv_eqm; lia].
Qed.
