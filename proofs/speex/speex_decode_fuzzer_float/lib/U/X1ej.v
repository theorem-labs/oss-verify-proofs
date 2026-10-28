(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bk X1bj X1cf X1bs X1c2 X1bq.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hu X1nq.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import UbDec.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac upto p := repeat (tryif ub_at_pc p then fail else (tryif ub_at_if then ub_dec else ub_step)).
Local Ltac nmod := repeat match goal with |- context [?x mod 18446744073709551616] => rewrite (Z.mod_small x 18446744073709551616) by lia end.
Local Ltac grd := repeat first [
  match goal with |- context [Z.lxor (?p mod 18446744073709551616) 9223372036854775808] => rewrite (lxor_sign_mod p) by lia end
| match goal with |- context [Z.lxor (Z.lxor (Z.b2z (?Y <? ?A)) (Z.b2z (?y + 9223372036854775808 <? 9223372036854775808))) 1] =>
    rewrite (ptr_sgn_guard A y Y) by lia end
| match goal with |- context [Z.land ?x 3] => rewrite (land3_al x) by (Z.to_euclidean_division_equations; lia) end
| match goal with |- context [bv_swrap 32 (?x mod 18446744073709551616 + 1)] => rewrite (swrap_mod64_plus1_k x) by lia end
| match goal with |- context [?a mod 18446744073709551616] => is_Zlit a; let v := eval vm_compute in (a mod 18446744073709551616) in
    change (a mod 18446744073709551616) with v end ].
Local Ltac go p := repeat (tryif ub_at_pc p then fail else (nmod; grd; tryif ub_at_if then ub_dec else ub_step)).

Section F.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.

#[using="Type"] Lemma fp_loop : forall (k : nat) (i q EB e0 exc e32 start : Z) (neb : nat) (cur cur32 : list word) (m0 : mem)
(ra sp gp tp s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word)
(F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem),
Z.of_nat k = 40 - i -> 0 <= i < 40 -> q = 4 * i ->
exc = EB + 4 * e0 -> 290 <= e0 -> e0 + 40 <= Z.of_nat neb -> 17 <= start <= 144 ->
0 < e32 -> e32 mod 4 = 0 -> EB mod 4 = 0 ->
u32arr rsegs m1 EB cur -> length cur = neb -> u32arr rsegs m1 e32 cur32 -> length cur32 = 40%nat ->
apart EB (4 * Z.of_nat neb) e32 160 ->
munch [(exc, exc + 160); (e32, e32 + 160)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (F2 : bvmap 5 word) (fc2 : bv 32) (m2 : mem) (cur' cur32' : list word) (w3 w4 w29 w30 w31 : word),
ms' = MS (mkR ra sp gp tp (Z_to_bv 64 1) (Z_to_bv 64 (18446744073709551615 - exc)) (Z_to_bv 64 1) s0 s1 (Z_to_bv 64 exc) (Z_to_bv 64 e32)
(Z_to_bv 64 start) w3 w4 (Z_to_bv 64 160) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) w29 w30 w31)
F2 (Z_to_bv 64 0x272f0) fc2 None m2 (seg_rom rsegs)
/\ munch [(exc, exc + 160); (e32, e32 + 160)] m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ frm0 fc2
/\ u32arr rsegs m2 EB cur' /\ length cur' = neb /\ u32arr rsegs m2 e32 cur32' /\ length cur32' = 40%nat)
(MS (mkR ra sp gp tp (Z_to_bv 64 1) (Z_to_bv 64 (18446744073709551615 - exc)) (Z_to_bv 64 1) s0 s1 (Z_to_bv 64 exc) (Z_to_bv 64 e32)
(Z_to_bv 64 start) (Z_to_bv 64 q) (Z_to_bv 64 i) (Z_to_bv 64 160) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) t4 t5 t6)
F1 (Z_to_bv 64 0x27274) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i q EB e0 exc e32 start neb cur cur32 m0
ra sp gp tp s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 F1 fc1 m1
Hk Hi -> He0 E0lo E0hi Hst E32P E324 EB4 EBA Lcur E32A L32 AP MU WM MI FRM; [lia|].
pose proof (u32arr_bound _ _ _ _ EBA) as BE. rewrite Lcur in BE.
pose proof (u32arr_bound _ _ _ _ E32A) as B32. rewrite L32 in B32.
unfold apart in AP. subst exc.
upto 0x2728c.
rewrite swrap32_modl_k. rewrite (swrap32_small_k (i - start + 0)) by lia. rewrite Z.add_0_r.
rewrite (addr_shift2 (EB + 4 * e0) (i - start) (EB + 4 * (e0 - start + i))) by lia.
go 0x272cc.
pose proof (u32arr_read_nth rsegs m1 EB cur (e0 - start + i) _ EBA ltac:(lia) eq_refl) as RD.
zstep. clear RD.
zstep.
pose proof (u32arr_store_ok rsegs m1 e32 cur32 i _ E32A ltac:(lia) eq_refl) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs m1 e32 cur32 i v E32A ltac:(lia)) as E32A' end.
clear E32A. store_done. try clear SOK.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m2 end.
go 0x272e4.
replace (EB + 4 * e0 + 4 * i) with (EB + 4 * (e0 + i)) by lia.
pose proof (u32arr_store_ok rsegs m2 EB cur (e0 + i) _ EBA ltac:(lia) eq_refl) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs m2 EB cur (e0 + i) v EBA ltac:(lia)) as EBA' end.
clear EBA. store_done. try clear SOK.
go 0x272ec.
rewrite (swrap32_small_k (i + 1)) by lia.
zstep. if_cases K; zify_cond K.
-
eapply (IH (i + 1) (4 * i + 4) EB e0 (EB + 4 * e0) e32 start neb _ _ m0); try eassumption; try lia.
all: rewrite upd_length; first [exact Lcur | exact L32].
-
apply evt_done.
sf_eexists 10%nat. split; [reflexivity|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. split; [rewrite upd_length; exact Lcur|].
split; [eassumption|]. rewrite upd_length; exact L32.
Qed.

#[using="Type"] Lemma forced_pitch_unquant_proof : @ltp_unquant_stmt ptr LtpForcedPitchUnquant.
Proof.
unfold ltp_unquant_stmt. intros until m.
intros REP OK EBC EB1 EB2 EBm E32C L32 PVC PGC LPG _ _ _ ARGS Hst1 Hst2 Hfin Hoff STK LO GLO
AQ1 AQ2 AQ3 AQ4 AQ5 AQ6 AQ7 AQ8 AQ9 AQ10 AQ11 AQ12 AQ13 AQ14 AQ15 AQ16 AQ17 AQ18 AQ19 AQ20
EXC4 E324 E32P PV4 PVP PG4 PGP PARM
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
FJ (Z_to_bv 64 0x2724c) fcj None m (seg_rom rsegs))).
{ intros FJ x13 fcj FRM1.
zstep. if_false_x.
upto 0x27274.
pose proof (u32arr_of_f32 rsegs _ _ _ EBC) as EBA. pose proof (u32arr_of_f32 rsegs _ _ _ E32C) as E32A.
clear EBC E32C.
set (e0 := (exc - EB) / 4).
assert (He0 : exc = EB + 4 * e0) by (pose proof (Z.div_mod (exc - EB) 4 ltac:(lia)); lia).
assert (EB4 : EB mod 4 = 0) by (Z.to_euclidean_division_equations; lia).
replace (0 <? e32) with true by (symmetry; apply Z.ltb_lt; lia).
replace (0 <? exc) with true by (symmetry; apply Z.ltb_lt; lia).
rewrite (land3_al e32 E324). change (Z.land (Z.b2z (0 <? 1)) (Z.b2z true)) with 1. change (Z.b2z true) with 1.
rewrite (zb_lxor_ones exc) by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(exc, exc + 160); (e32, e32 + 160)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (fp_loop 40%nat 0 0 EB e0 exc e32 start (length eb) eb e32s mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try exact FRM1. all: try eassumption.
clear MUL WML.
match goal with H : u32arr rsegs _ EB ?c, L : length ?c = length eb |- _ => rename H into EBA2; rename L into Lc end.
match goal with H : u32arr rsegs _ e32 ?c, L : length ?c = 40%nat |- _ => rename H into E32A2; rename L into L32' end.
match goal with H : rw_cells rsegs _ pg _ |- _ => rewrite f32_cons, f32_cons, f32_cons, f32_nil in H end.
go 0x27334.
zstep.
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
