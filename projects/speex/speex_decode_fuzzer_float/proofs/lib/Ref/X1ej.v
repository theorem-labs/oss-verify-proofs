(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bk X1bj X1cf X1bs X1c2 X1bq.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1ho X1hu X1nq.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Plain.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section F.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.

#[using="Type"] Lemma fp_loop : forall (k : nat) (i EB e0 exc e32 start pa0 pa1 pa3 pend : Z) (neb : nat) (cur cur32 : list word) (m0 : mem)
(ra sp gp tp t0 t1 t2 s0 s1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem),
Z.of_nat k = 40 - i -> 0 <= i < 40 ->
exc = EB + 4 * e0 -> 290 <= e0 -> e0 + 40 <= Z.of_nat neb -> 17 <= start <= 144 ->
pa0 = EB + 4 * (e0 + i) -> pa1 = e32 + 4 * i -> pa3 = EB + 4 * (e0 - start + i) -> pend = EB + 4 * (e0 - start + 40) ->
u32arr rsegs m1 EB cur -> length cur = neb -> u32arr rsegs m1 e32 cur32 -> length cur32 = 40%nat ->
apart EB (4 * Z.of_nat neb) e32 160 ->
munch [(exc, exc + 160); (e32, e32 + 160)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (F2 : bvmap 5 word) (fc2 : bv 32) (m2 : mem) (cur' cur32' : list word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (exc + 160)) (Z_to_bv 64 (e32 + 160)) a2
(Z_to_bv 64 pend) (Z_to_bv 64 pend) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F2 (Z_to_bv 64 0x230f4) fc2 None m2 (seg_rom rsegs)
/\ munch [(exc, exc + 160); (e32, e32 + 160)] m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ frm0 fc2
/\ u32arr rsegs m2 EB cur' /\ length cur' = neb /\ u32arr rsegs m2 e32 cur32' /\ length cur32' = 40%nat)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 pa0) (Z_to_bv 64 pa1) a2 (Z_to_bv 64 pa3) (Z_to_bv 64 pend) a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x230d4) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i EB e0 exc e32 start pa0 pa1 pa3 pend neb cur cur32 m0
ra sp gp tp t0 t1 t2 s0 s1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F1 fc1 m1
Hk Hi He0 E0lo E0hi Hst -> -> -> -> EBA Lcur E32A L32 AP MU WM MI FRM; [lia|].
pose proof (u32arr_bound _ _ _ _ EBA) as BE. rewrite Lcur in BE.
pose proof (u32arr_bound _ _ _ _ E32A) as B32. rewrite L32 in B32.
unfold apart in AP. subst exc.

pose proof (u32arr_read_nth rsegs m1 EB cur (e0 - start + i) _ EBA ltac:(lia) eq_refl) as RD.
zstep. clear RD.
zstep. zstep.

pose proof (u32arr_store_ok rsegs m1 e32 cur32 i _ E32A ltac:(lia) eq_refl) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs m1 e32 cur32 i v E32A ltac:(lia)) as E32A' end.
clear E32A. store_done. try clear SOK.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m2 end.

pose proof (u32arr_store_ok rsegs m2 EB cur (e0 + i) _ EBA ltac:(lia) ltac:(f_equal; lia)) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs m2 EB cur (e0 + i) v EBA ltac:(lia)) as EBA' end.
clear EBA. store_done. try clear SOK.
zstep. zstep. zstep.
if_cases K; zify_cond K.
-
eapply (IH (i + 1) EB e0 (EB + 4 * e0) e32 start _ _ _ _ neb _ _ m0); try eassumption; try lia.
all: rewrite upd_length; first [exact Lcur | exact L32].
-
apply evt_done.
replace (EB + 4 * (e0 + i) + 4) with (EB + 4 * e0 + 160) by lia. replace (e32 + 4 * i + 4) with (e32 + 160) by lia.
replace (EB + 4 * (e0 - start + i) + 4) with (EB + 4 * (e0 - start + 40)) by lia.
sf_eexists 5%nat. split; [reflexivity|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. split; [rewrite upd_length; exact Lcur|].
split; [eassumption|]. rewrite upd_length; exact L32.
Qed.

#[using="Type"] Lemma forced_pitch_unquant_proof : @ltp_unquant_stmt ptr LtpForcedPitchUnquant.
Proof.
unfold ltp_unquant_stmt. intros until m.
intros REP OK EBC EB1 EB2 EBm E32C L32 PVC PGC LPG _ _ _ ARGS Hst1 Hst2 Hfin Hoff STK LO GLO
AQ1 AQ2 AQ3 AQ4 AQ5 AQ6 AQ7 AQ8 AQ9 AQ10 AQ11 AQ12 AQ13 AQ14 AQ15 AQ16 AQ17 AQ18 AQ19 AQ20
-> -> -> -> -> -> -> -> MI FRM.
cbn [ltp_pitch_span] in Hst2. unfold ltp_entry.
unfold LTP_DEPTH, NB_GLOBALS_TOP in *. assert (BS : BITS_SIZEOF = 48) by reflexivity.
pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rsp.
pose proof REP as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE).
pose proof SIDE as sfP_; first [ sf_destruct 6%nat sfP_ as AL Apos Dpos BUFMAX _ SEP | sf_fb; destruct sfP_ as (AL & Apos & Dpos & BUFMAX & _ & SEP) ]. unfold BITS_BUF_MAX in BUFMAX.
unfold bits_cells in OBJ.
pose proof (rw_cells_bound _ _ _ _ OBJ) as GB. cbn [cells_size csize Nat.add length] in GB.
pose proof (u8arr_bound _ _ _ _ DAT) as DB.
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs, zlength_map_unsigned in OK'. lia. }
pose proof (rw_cells_bound _ _ _ _ EBC) as GE. rewrite cells_size_f32 in GE.
pose proof (rw_cells_bound _ _ _ _ E32C) as G32. rewrite cells_size_f32, L32 in G32.
pose proof (rw_cells_bound _ _ _ _ PVC) as GPV. cbn [cells_size csize Nat.add] in GPV.
pose proof (rw_cells_bound _ _ _ _ PGC) as GPG. rewrite cells_size_f32, LPG in GPG.
destruct pgs as [|g0 [|g1 [|g2 [|? ?]]]]; try (cbn in LPG; lia).
pose proof (munch_refl [(lo, bv_unsigned sp); (exc, exc + 160); (e32, e32 + 160); (pv, pv + 4); (pg, pg + 12); (A, A + BITS_SIZEOF)] m) as MU.
pose proof (wmono_refl rsegs m) as WM.
unfold A_forced_pitch_unquant.

do 5 zstep.

assert (JOIN : forall (FJ : bvmap 5 word) (x13 : word) (fcj : bv 32), frm0 fcj ->
evt rsegs (ltp_unquant_post LtpForcedPitchUnquant A D b EB exc e32 pv pg start lo (length eb)
ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 exc) (Z_to_bv 64 e32) (Z_to_bv 64 start) x13 (Z_to_bv 64 PAR)
(Z_to_bv 64 40) (Z_to_bv 64 pv) (Z_to_bv 64 pg) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
FJ (Z_to_bv 64 0x230bc) fcj None m (seg_rom rsegs))).
{ intros FJ x13 fcj FRM1.
zstep. if_false_x.
zstep. rewrite (Z.shiftl_mul_pow2 start 2) by lia. change (2^2) with 4. try rewrite (Z.mod_small (start * 4)) by lia.
do 4 zstep. try rewrite (Z.mod_small (start * 4)) by lia.
pose proof (u32arr_of_f32 rsegs _ _ _ EBC) as EBA. pose proof (u32arr_of_f32 rsegs _ _ _ E32C) as E32A.
clear EBC E32C.
set (e0 := (exc - EB) / 4).
assert (He0 : exc = EB + 4 * e0) by (pose proof (Z.div_mod (exc - EB) 4 ltac:(lia)); lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(exc, exc + 160); (e32, e32 + 160)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (fp_loop 40%nat 0 EB e0 exc e32 start _ _ _ _ (length eb) eb e32s mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try exact FRM1. all: try eassumption.
clear MUL WML.
match goal with H : u32arr rsegs _ EB ?c, L : length ?c = length eb |- _ => rename H into EBA2; rename L into Lc end.
match goal with H : u32arr rsegs _ e32 ?c, L : length ?c = 40%nat |- _ => rename H into E32A2; rename L into L32' end.
match goal with H : rw_cells rsegs _ pg _ |- _ => rewrite f32_cons, f32_cons, f32_cons, f32_nil in H end.
zstep. lstep. zstep. lstep. zstep.
apply evt_done. unfold ltp_unquant_post. cbn [ltp_pitch ltp_bits].
eexists _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _. eexists _, _, [_; _; _].
split; [unfold callR; cbn [c_t0 c_t1 c_t2 c_a1 c_a2 c_a3 c_a4 c_a5 c_a6 c_a7 c_t3 c_t4 c_t5 c_t6]; reflexivity|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [apply f32_of_u32arr; exact EBA2|]. split; [exact Lc|].
split; [apply f32_of_u32arr; exact E32A2|]. split; [exact L32'|].
split; [eassumption|].
split; [rewrite f32_cons, f32_cons, f32_cons, f32_nil; eassumption|]. split; [reflexivity|].
split; [| exact OK].
split; [exists rj; split; [exact Lrj| exact OBJ]| split; [exists bs; split; [exact DAT| exact Hbs]| exact SIDE]]. }
if_cases B0.
-   apply JOIN. assumption.
-   zstep. zstep. apply JOIN. assumption.
Qed.
End F.
