(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
Import ListNotations.
Open Scope bv_scope.
Local Notation psegs := Plain.M.loaded_segments.

Local Notation "# x" := (nan_box (low32 x)) (at level 9, format "# x").

Record hpc := HPC { hc_n0 : word; hc_n1 : word; hc_n2 : word; hc_d1 : word; hc_d2 : word }.
Definition hp_coefs (filtID : Z) : hpc :=
if (filtID =? 0)%Z then HPC (Z_to_bv 64 18446744070479208398) (Z_to_bv 64 18446744072635080738) (Z_to_bv 64 18446744070479208398) (Z_to_bv 64 18446744070487581236) (Z_to_bv 64 18446744072625994785)
else if (filtID =? 1)%Z then HPC (Z_to_bv 64 18446744070479341274) (Z_to_bv 64 18446744072635212439) (Z_to_bv 64 18446744070479341274) (Z_to_bv 64 18446744070487712350) (Z_to_bv 64 18446744072626258691)
else if (filtID =? 2)%Z then HPC (Z_to_bv 64 18446744070479387747) (Z_to_bv 64 18446744072635259919) (Z_to_bv 64 18446744070479387747) (Z_to_bv 64 18446744070487767295) (Z_to_bv 64 18446744072626339557)
else if (filtID =? 3)%Z then HPC (Z_to_bv 64 18446744070479710205) (Z_to_bv 64 18446744072635581370) (Z_to_bv 64 18446744070479710205) (Z_to_bv 64 18446744070488093444) (Z_to_bv 64 18446744072626973568)
else HPC (Z_to_bv 64 18446744070477924270) (Z_to_bv 64 18446744072633796526) (Z_to_bv 64 18446744070477924270) (Z_to_bv 64 18446744070483041321) (Z_to_bv 64 18446744072615643578).

Definition hp_v (c : hpc) (st : word * word) (x : word) : word := fmadd_s RNE (hc_n0 c) (# x) (# (fst st)).
Definition hp_next (c : hpc) (st : word * word) (x : word) : word * word :=
(fmadd_s RNE (hc_d1 c) (hp_v c st x) (fmadd_s RNE (hc_n1 c) (# x) (# (snd st))),
fmadd_s RNE (hc_n2 c) (# x) (fmul_s RNE (hp_v c st x) (hc_d2 c))).
Fixpoint hp_st (c : hpc) (st : word * word) (xs : list word) : word * word :=
match xs with [] => st | x :: xs' => hp_st c (hp_next c st x) xs' end.
Fixpoint hp_ys (c : hpc) (st : word * word) (xs : list word) : list word :=
match xs with [] => [] | x :: xs' => hp_v c st x :: hp_ys c (hp_next c st x) xs' end.
Lemma hp_st_app : forall c a b st, hp_st c st (a ++ b) = hp_st c (hp_st c st a) b.
Proof. induction a; intros; cbn; [reflexivity| apply IHa]. Qed.
Lemma hp_ys_app : forall c a b st, hp_ys c st (a ++ b) = hp_ys c st a ++ hp_ys c (hp_st c st a) b.
Proof. induction a; intros; cbn; [reflexivity|]. rewrite IHa. reflexivity. Qed.
Lemma length_hp_ys : forall c xs st, length (hp_ys c st xs) = length xs.
Proof. induction xs; intros; cbn; [reflexivity|]. now rewrite IHxs. Qed.
#[local] Hint Rewrite length_hp_ys : chunk_sizes.

Section S.
Context {RCEIL : RunCeiling}.
Variables (xs : list word) (m0 m1 : word) (p pm : Z).
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variables f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 : word.
Variable mi : word -> option byte.
Local Notation W := ([(p, p + 4 * Z.of_nat (length xs)); (pm, pm + 8)]%Z).

Definition highpass_post (c : hpc) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 g0 g1 g10 fc' m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(mkF g0 g1 f2 f3 f4 f5 f6 f7 f8 f9 g10 (hc_d2 c) (hc_d1 c) (hc_n2 c) (hc_n1 c) (hc_n0 c) f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31)
(ret_pc ra) fc' None m' (seg_rom psegs)
/\ munch W mi m' /\ wmono psegs mi m' /\ mem_inv psegs m'
/\ frm0 fc'
/\ rw_cells psegs m' p (f32 (hp_ys c (m0, m1) xs))
/\ rw_cells psegs m' pm (f32 [fst (hp_st c (m0, m1) xs); snd (hp_st c (m0, m1) xs)]).

#[using="Type"] Lemma hp_loop : forall (c : hpc) rest done x q (xa3 xa5 xa6 g0 g1 g10 t0 t1 t2 a7 t3 t4 t5 t6 : word) fc m,
xs = done ++ x :: rest ->
q = (p + 4 * Z.of_nat (length done))%Z ->
(p + 4 * Z.of_nat (length xs) <= pm \/ pm + 8 <= p)%Z ->
frm0 fc -> mem_inv psegs m -> munch W mi m -> wmono psegs mi m ->
rw_cells psegs m p (f32 (hp_ys c (m0, m1) done)) ->
rw_cells psegs m q (f32 (x :: rest)) ->
rw_cells psegs m pm (f32 [fst (hp_st c (m0, m1) done); snd (hp_st c (m0, m1) done)]) ->
evt psegs (highpass_post c)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 q) (Z_to_bv 64 q) (Z_to_bv 64 (p + 4 * Z.of_nat (length xs))) xa3 (Z_to_bv 64 pm) xa5 xa6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(mkF g0 g1 f2 f3 f4 f5 f6 f7 f8 f9 g10 (hc_d2 c) (hc_d1 c) (hc_n2 c) (hc_n1 c) (hc_n0 c) f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31)
(Z_to_bv 64 0x20774) fc None m (seg_rom psegs)).
Proof.
intros c. induction rest as [|x' rest IH]; intros done x q xa3 xa5 xa6 g0 g1 g10 t0 t1 t2 a7 t3 t4 t5 t6 fc m Hxs Hq SEP FRM MI MU WM DONE X PM;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ PM) as BPM; rewrite cells_size_f32 in BPM; cbn [length] in BPM;
pose proof (f_equal (@length word) Hxs) as HL; rewrite length_app in HL; cbn [length] in HL;
rewrite !f32_cons, ?f32_nil in X; rewrite !f32_cons, f32_nil in PM; cbn [fst snd] in PM.
- do 15 zstep. if_false_x. zstep.
unfold highpass_post. finish.
+ chunk_snoc DONE X. subst xs. rewrite hp_ys_app, f32_app. cbn [hp_ys]. rewrite f32_cons, f32_nil. exact DONE.
+ subst xs. rewrite hp_st_app. cbn [hp_st hp_next fst snd]. rewrite f32_cons, f32_cons, f32_nil. exact PM.
- do 15 zstep. if_true_x.
chunk_uncons X as X1. chunk_snoc DONE X1.
apply (IH (done ++ [x]) x' (q + 4)%Z); try assumption.
+ rewrite Hxs, <- app_assoc. reflexivity.
+ rewrite length_app. cbn [length]. lia.
+ rewrite hp_ys_app, f32_app. cbn [hp_ys]. rewrite f32_cons, f32_nil. exact DONE.
+ rewrite hp_st_app. cbn [hp_st hp_next fst snd]. rewrite f32_cons, f32_cons, f32_nil. exact PM.
Qed.

Ltac hp_entry := zstep; if_false_x; zstep; zstep; first [ if_true_x | if_false_x; zstep ]; do 18 zstep.

#[using="Type"] Lemma highpass_spec : forall (filtID : Z) t0 t1 t2 a2 a3 a5 a6 a7 t3 t4 t5 t6 fc,
rw_cells psegs mi p (f32 xs) -> rw_cells psegs mi pm (f32 [m0; m1]) ->
(p + 4 * Z.of_nat (length xs) <= pm \/ pm + 8 <= p)%Z ->
mem_inv psegs mi -> frm0 fc ->
a2 = Z_to_bv 64 (Z.of_nat (length xs)) -> (1 <= Z.of_nat (length xs) < 2^31)%Z ->
a3 = Z_to_bv 64 filtID -> (filtID = 1 \/ filtID = 3)%Z ->
evt psegs (highpass_post (hp_coefs filtID))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 p) a2 a3 (Z_to_bv 64 pm) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(mkF f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31)
(Z_to_bv 64 0x2071c) fc None mi (seg_rom psegs)).
Proof.
intros filtID t0 t1 t2 a2 a3 a5 a6 a7 t3 t4 t5 t6 fc X PM SEP MI FRM -> LEN -> FID.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX.
pose proof (rw_cells_bound _ _ _ _ PM) as BPM; rewrite cells_size_f32 in BPM; cbn [length] in BPM.
pose proof (munch_refl W mi) as MU. pose proof (wmono_refl psegs mi) as WM.
destruct xs as [|x rest] eqn:Exs; [cbn in LEN; lia|]. rewrite <- Exs in *.
destruct FID as [-> | ->]; hp_entry;
replace (p + Z.shiftl (Z.of_nat (length xs)) 2)%Z with (p + 4 * Z.of_nat (length xs))%Z
by (rewrite Z.shiftl_mul_pow2 by lia; lia);
rewrite Exs in X;
(eapply hp_loop with (done := []); [exact Exs | cbn [length]; lia | lia
| exact FRM | exact MI | exact MU | exact WM
| cbn [hp_ys]; rewrite f32_nil; apply rw_cells_nil; lia | exact X | cbn [hp_st fst snd]; exact PM ]).
Qed.
End S.
