(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bk X1bj X1cf X1bs X1c2 X1bq.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1nq.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section F.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.

#[using="Type"] Lemma noise_loop : forall (k : nat) (i inn seedp pa1 pa2 cnt : Z) (cur : list word) (m0 : mem)
(ra sp gp tp s0 s1 sd s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem),
Z.of_nat k = 40 - i -> 0 <= i < 40 -> 0 < inn -> inn mod 4 = 0 ->
pa1 = inn + 4 * i -> pa2 = inn + 4 * i -> cnt = 40 - i ->
u32arr rsegs m1 inn cur -> length cur = 40%nat ->
munch [(inn, inn + 160)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (t0' t1' t2' a0' sd' a2' a3' a4' a6' a7' t3' : word) (F2 : bvmap 5 word) (fc2 : bv 32) (m2 : mem) (cur' : list word),
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' sd' a2' a3' a4' (Z_to_bv 64 seedp) a6' a7'
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
F2 (Z_to_bv 64 0x2a094) fc2 None m2 (seg_rom rsegs)
/\ munch [(inn, inn + 160)] m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ frm0 fc2
/\ u32arr rsegs m2 inn cur' /\ length cur' = 40%nat)
(MS (mkR ra sp gp tp (Z_to_bv 64 1065353216) (Z_to_bv 64 pa1) (Z_to_bv 64 pa2) s0 s1
(Z_to_bv 64 inn) sd (Z_to_bv 64 cnt) (Z_to_bv 64 1) (Z_to_bv 64 1664525) (Z_to_bv 64 seedp) (Z_to_bv 64 1013904223) (Z_to_bv 64 1)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x2a044) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i inn seedp pa1 pa2 cnt cur m0 ra sp gp tp s0 s1 sd s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F1 fc1 m1
Hk Hi IPOS I4 -> -> -> ARR Lcur MU WM MI FRM; [lia|].
pose proof (u32arr_bound _ _ _ _ ARR) as BA. rewrite Lcur in BA.
zstep. zstep.
zstep. if_false_z.
zstep. zstep.
zstep. if_false_z.
zstep. if_false_z.
do 10 zstep.
pose proof (u32arr_store_ok rsegs m1 inn cur i _ ARR ltac:(lia) eq_refl) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs m1 inn cur i v ARR ltac:(lia)) as ARR' end.
clear ARR. store_done. try clear SOK.
zstep. zstep.
if_cases K; zify_cond K.
- eapply (IH (i + 1) inn seedp _ _ _ _ m0); try eassumption; try lia. rewrite upd_length. exact Lcur.
- apply evt_done.
sf_eexists 15%nat. split; [reflexivity|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. rewrite upd_length. exact Lcur.
Qed.

#[using="Type"] Lemma noise_codebook_unquant_proof : @innov_unquant_stmt ptr InnovNoiseCodebookUnquant.
Proof.
unfold innov_unquant_stmt. intros until m.
intros REP OK INC LIS SEEDC _ _ _ STK LO GLO _ AQ1 AQ2 AQ3 AQ4 AQ5 AQ6 AQ7 AQ8 AQ9 I4 IPOS SDF -> -> -> -> -> -> MI FRM.
destruct SDF as [S4 SPOS].
unfold innov_entry. unfold INNOV_DEPTH, NB_GLOBALS_TOP in *. assert (BS : BITS_SIZEOF = 48) by reflexivity.
pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rsp.
pose proof REP as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE).
pose proof SIDE as sfP_; first [ sf_destruct 6%nat sfP_ as AL Apos Dpos BUFMAX _ SEP | sf_fb; destruct sfP_ as (AL & Apos & Dpos & BUFMAX & _ & SEP) ]. unfold BITS_BUF_MAX in BUFMAX.
unfold bits_cells in OBJ.
pose proof (rw_cells_bound _ _ _ _ OBJ) as GB. cbn [cells_size csize Nat.add length] in GB.
pose proof (u8arr_bound _ _ _ _ DAT) as DB.
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs, zlength_map_unsigned in OK'. lia. }
pose proof (rw_cells_bound _ _ _ _ INC) as GI. rewrite cells_size_f32, LIS in GI.
pose proof (rw_cells_bound _ _ _ _ SEEDC) as GS. cbn [cells_size csize Nat.add] in GS.
pose proof (munch_refl [(lo, bv_unsigned sp); (inn, inn + 160); (seedp, seedp + 4); (A, A + BITS_SIZEOF)] m) as MU.
pose proof (wmono_refl rsegs m) as WM.
unfold A_noise_codebook_unquant. unfold apart in AQ1, AQ2, AQ3, AQ4, AQ5, AQ6, AQ7, AQ8, AQ9.
zstep. if_false_x.
zstep. if_false_z.
zstep. zstep. if_false_z.
do 18 zstep.
cond_prep.
pose proof (u32arr_of_f32 rsegs _ _ _ INC) as ARR. clear INC.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(inn, inn + 160)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (noise_loop 40%nat 0 inn seedp _ _ _ is0 mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try eassumption.
clear MUL WML.
match goal with H : u32arr rsegs _ inn ?c, L : length ?c = 40%nat |- _ => rename H into ARR2; rename L into L2 end.
zstep. zstep.
apply evt_done. unfold innov_unquant_post. cbn [innov_bits].
eexists _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _. sf_eexists 2%nat.
split; [unfold callR; cbn [c_t0 c_t1 c_t2 c_a1 c_a2 c_a3 c_a4 c_a5 c_a6 c_a7 c_t3 c_t4 c_t5 c_t6]; reflexivity|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [apply f32_of_u32arr; exact ARR2|]. split; [exact L2|].
split; [eassumption|].
split; [| exact OK].
split; [exists rj; split; [exact Lrj| exact OBJ]| split; [exists bs; split; [exact DAT| exact Hbs]| exact SIDE]].
Qed.
End F.
