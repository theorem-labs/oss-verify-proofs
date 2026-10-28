(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
Import ListNotations.
Open Scope bv_scope.
Local Notation psegs := Ubsan.M.loaded_segments.

Definition san1 (mn mx x : word) : word :=
let v := nan_box (low32 x) in
if fle_s mn v && fle_s v mx then x
else if flt_s v mn then fmv_s mn
else if flt_s mx v then fmv_s mx
else fzero_s.
Lemma length_map_san1 : forall mn mx xs, length (map (san1 mn mx) xs) = length xs.
Proof. intros. apply length_map. Qed.
#[local] Hint Rewrite length_map_san1 : chunk_sizes.

Ltac san_checks := zstep; if_false_z; zstep; zstep; zstep; if_false_z; zstep; if_false_z.

Section S.
Context {RCEIL : RunCeiling}.
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variables f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 : word.
Variable m0 : word -> option byte.
Variables (p : Z) (xs : list word).
Hypothesis P0 : (0 < p)%Z.
Hypothesis P4 : (p mod 4 = 0)%Z.
Hypothesis LEN : (Z.of_nat (length xs) < 2^31)%Z.
Local Notation mn := f10.
Local Notation mx := f11.
Local Notation W := ([(p, p + 4 * Z.of_nat (length xs))]%Z).

Definition sanitize_values32_post : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 g13 g14 fc' m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(mkF f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 g13 g14 fzero_s f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31)
(ret_pc ra) fc' None m' (seg_rom psegs)
/\ munch W m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
/\ frm0 fc'
/\ rw_cells psegs m' p (f32 (map (san1 mn mx) xs)).

#[using="P0 P4 LEN"] Lemma sanitize_loop : forall rest done x q (a1v a6v g13 g14 t0 t1 t2 a7 t3 t4 t5 t6 : word) fc m,
xs = done ++ x :: rest ->
q = (p + 4 * Z.of_nat (length done))%Z ->
a1v = Z_to_bv 64 (Z.of_nat (S (length rest))) ->
frm0 fc -> mem_inv psegs m -> munch W m0 m -> wmono psegs m0 m ->
rw_cells psegs m p (f32 (map (san1 mn mx) done)) ->
rw_cells psegs m q (f32 (x :: rest)) ->
evt psegs sanitize_values32_post
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1v (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 q) (Z_to_bv 64 q) a6v a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(mkF f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 g13 g14 fzero_s f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31)
(Z_to_bv 64 0x22c9c) fc None m (seg_rom psegs)).
Proof.
induction rest as [|x' rest IH]; intros done x q a1v a6v g13 g14 t0 t1 t2 a7 t3 t4 t5 t6 fc m Hxs Hq Ha1 FRM MI MU WM DONE X; subst a1v;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (f_equal (@length word) Hxs) as HL; rewrite length_app in HL; cbn [length] in HL;
rewrite !f32_cons, ?f32_nil in X.
-
assert (FIN : forall (ya6 h13 : word) fc' m' (w : word),
frm0 fc' -> mem_inv psegs m' -> munch W m0 m' -> wmono psegs m0 m' ->
rw_cells psegs m' p (f32 (map (san1 mn mx) done)) -> rw_cells psegs m' q [C4 w] -> w = san1 mn mx x ->
evt psegs sanitize_values32_post
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 (Z.of_nat (S (length (@nil word))))) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 q) (Z_to_bv 64 q) ya6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(mkF f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 h13 (nan_box (low32 x)) fzero_s f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31)
(Z_to_bv 64 0x22ce4) fc' None m' (seg_rom psegs))).
{ clear FRM MI MU WM DONE X fc m. intros ya6 h13 fc m w FRM MI MU WM DONE X ->.
cbn [length]. do 4 zstep. if_false_x. zstep. unfold sanitize_values32_post. finish.
chunk_snoc DONE X. subst xs. rewrite map_app, f32_app. exact DONE. }
san_checks. zstep. zstep. zstep. if_cases B1; bfact B1.
+
zstep. zstep. zstep. if_cases B3; bfact B3.
* zstep. eapply FIN; try eassumption. unfold san1. rewrite B1, B3. reflexivity.
* zstep. zstep. zstep. if_cases B4; bfact B4.
-- zstep. eapply FIN; try eassumption. unfold san1. rewrite B1, B3, B4. reflexivity.
-- zstep. zstep. eapply FIN; try eassumption. unfold san1. rewrite B1, B3, B4. reflexivity.
+ zstep. zstep. if_cases B2; bfact B2.
* eapply FIN; try eassumption. unfold san1. rewrite B1, B2. reflexivity.
* zstep. zstep. zstep. if_cases B3; bfact B3.
-- zstep. eapply FIN; try eassumption. unfold san1. rewrite B1, B2, B3. reflexivity.
-- zstep. zstep. zstep. if_cases B4; bfact B4.
++ zstep. eapply FIN; try eassumption. unfold san1. rewrite B1, B2, B3, B4. reflexivity.
++ zstep. zstep. eapply FIN; try eassumption. unfold san1. rewrite B1, B2, B3, B4. reflexivity.
-
assert (NXT : forall (ya6 h13 : word) fc' m' (w : word),
frm0 fc' -> mem_inv psegs m' -> munch W m0 m' -> wmono psegs m0 m' ->
rw_cells psegs m' p (f32 (map (san1 mn mx) done)) -> rw_cells psegs m' q [C4 w] -> w = san1 mn mx x ->
rw_cells psegs m' (q + 4) (f32 (x' :: rest)) ->
evt psegs sanitize_values32_post
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 (Z.of_nat (S (length (x' :: rest))))) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 q) (Z_to_bv 64 q) ya6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(mkF f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 h13 (nan_box (low32 x)) fzero_s f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31)
(Z_to_bv 64 0x22ce4) fc' None m' (seg_rom psegs))).
{ clear FRM MI MU WM DONE X fc m. intros ya6 h13 fc m w FRM MI MU WM DONE X -> X'.
pose proof (rw_cells_bound _ _ _ _ X') as BX'. rewrite cells_size_f32 in BX'. cbn [length] in BX'.
cbn [length]. do 4 zstep. if_true_x.
chunk_snoc DONE X.
eapply (IH (done ++ [x]) x' (q + 4)%Z); try eassumption.
all: try (rewrite Hxs, <- app_assoc; reflexivity).
all: try (rewrite length_app; cbn [length]; lia).
all: try (f_equal; lia).
rewrite map_app, f32_app. exact DONE. }
san_checks. zstep. zstep. zstep. if_cases B1; bfact B1.
+ zstep. zstep. zstep. if_cases B3; bfact B3.
* zstep. chunk_uncons X as X1. eapply NXT; try eassumption. unfold san1. rewrite B1, B3. reflexivity.
* zstep. zstep. zstep. if_cases B4; bfact B4.
-- zstep. chunk_uncons X as X1. eapply NXT; try eassumption. unfold san1. rewrite B1, B3, B4. reflexivity.
-- zstep. zstep. chunk_uncons X as X1. eapply NXT; try eassumption. unfold san1. rewrite B1, B3, B4. reflexivity.
+ zstep. zstep. if_cases B2; bfact B2.
* chunk_uncons X as X1. eapply NXT; try eassumption. unfold san1. rewrite B1, B2. reflexivity.
* zstep. zstep. zstep. if_cases B3; bfact B3.
-- zstep. chunk_uncons X as X1. eapply NXT; try eassumption. unfold san1. rewrite B1, B2, B3. reflexivity.
-- zstep. zstep. zstep. if_cases B4; bfact B4.
++ zstep. chunk_uncons X as X1. eapply NXT; try eassumption. unfold san1. rewrite B1, B2, B3, B4. reflexivity.
++ zstep. zstep. chunk_uncons X as X1. eapply NXT; try eassumption. unfold san1. rewrite B1, B2, B3, B4. reflexivity.
Qed.
End S.

Lemma sanitize_values32_spec :
forall (xs : list word) (p : Z)
ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31
fc m,
rw_cells psegs m p (f32 xs) ->
mem_inv psegs m -> frm0 fc ->
a1 = Z_to_bv 64 (Z.of_nat (length xs)) -> (1 <= Z.of_nat (length xs) < 2^31)%Z ->
(0 < p)%Z -> (p mod 4 = 0)%Z ->
evt psegs (sanitize_values32_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 m p xs)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(mkF f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31)
(Z_to_bv 64 0x22c7c) fc None m (seg_rom psegs)).
Proof.
intros until m. intros X MI FRM -> LEN P0 P4.
pose proof (rw_cells_bound _ _ _ _ X) as BX. rewrite cells_size_f32 in BX.
pose proof (munch_refl [(p, p + 4 * Z.of_nat (length xs))]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
destruct xs as [|x rest] eqn:Exs; [cbn in LEN; lia|]. rewrite <- Exs in *.
zstep. if_false_x. do 7 zstep. cond_prep.
rewrite Exs in X.
eapply sanitize_loop with (done := []) (q := p); try eassumption.
all: try exact Exs.
all: try (cbn [length]; lia).
all: try (rewrite Exs; reflexivity).
all: try (cbn [map]; rewrite f32_nil; apply rw_cells_nil; lia).
Qed.
