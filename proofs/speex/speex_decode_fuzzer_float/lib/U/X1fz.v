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

Definition smul (scale x : word) : word := fmul_s RNE scale (nan_box (low32 x)).
Lemma length_map_smul : forall c xs, length (map (smul c) xs) = length xs.
Proof. intros. apply length_map. Qed.
#[local] Hint Rewrite length_map_smul : chunk_sizes.

Definition signal_mul_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(p : Z) (xs : list word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 f15 fc' m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 15 f15 F) (ret_pc ra) fc' None m' (seg_rom psegs)
/\ munch [(p, p + 4 * Z.of_nat (length xs))]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
/\ frm0 fc'
/\ rw_cells psegs m' p (f32 (map (smul (reg_get F 10)) xs)).

Ltac sm_checks := zstep; if_false_z; zstep; zstep; zstep; if_false_z; zstep; if_false_z;
zstep; if_false_z; zstep; zstep; zstep; if_false_z; zstep; if_false_z.

Section Proof.
Context {RCEIL : RunCeiling}.
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word.
Variable F : bvmap 5 word.
Variable m0 : word -> option byte.
Variables (p : Z) (xs : list word).
Hypothesis P0 : (0 < p)%Z.
Hypothesis P4 : (p mod 4 = 0)%Z.
Hypothesis LEN : (Z.of_nat (length xs) < 2^31)%Z.
Local Notation POST := (signal_mul_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F p xs m0).
Local Notation W := ([(p, p + 4 * Z.of_nat (length xs))]%Z).

#[using="P0 P4 LEN"] Lemma signal_mul_loop : forall rest done x q a2v t3v fc m,
xs = done ++ x :: rest ->
q = (p + 4 * Z.of_nat (length done))%Z ->
a2v = Z_to_bv 64 (Z.of_nat (S (length rest))) ->
frm0 fc -> mem_inv psegs m -> munch W m0 m -> wmono psegs m0 m ->
rw_cells psegs m p (f32 (map (smul (reg_get F 10)) done)) ->
rw_cells psegs m q (f32 (x :: rest)) ->
evt psegs POST
(MS (mkR ra sp gp tp (Z_to_bv 64 q) (Z_to_bv 64 q) (Z_to_bv 64 q) s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 p)
a2v (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 q)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v t4 t5 t6)
(bvmap_set 15 (nan_box (low32 x)) F) (Z_to_bv 64 0x22f08) fc None m (seg_rom psegs)).
Proof.
induction rest as [|x' rest IH]; intros done x q a2v t3v fc m Hxs Hq Ha2 FRM MI MU WM DONE X; subst a2v;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX |- *;
pose proof (f_equal (@length word) Hxs) as HL; rewrite length_app in HL; cbn [length] in HL;
rewrite !f32_cons, ?f32_nil in X.
-
do 8 zstep. if_false_x. zstep.
unfold signal_mul_post. finish.
chunk_snoc DONE X. subst xs. rewrite map_app, f32_app. exact DONE.
-
do 8 zstep. if_true_x.
chunk_uncons X as X1. chunk_snoc DONE X1.
sm_checks. zstep.
eapply (IH (done ++ [x]) x' (q + 4)%Z); try eassumption.
all: try (rewrite Hxs, <- app_assoc; reflexivity).
all: try (rewrite length_app; cbn [length]; lia).
all: try (f_equal; lia).
rewrite map_app, f32_app. exact DONE.
Qed.
End Proof.

Lemma signal_mul_spec : forall (xs : list word) (p : Z)
ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m,
rw_cells psegs m p (f32 xs) ->
mem_inv psegs m ->
frm0 fc ->
a2 = Z_to_bv 64 (Z.of_nat (length xs)) ->
(1 <= Z.of_nat (length xs) < 2^31)%Z ->
(0 < p)%Z -> (p mod 4 = 0)%Z ->
evt psegs (signal_mul_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F p xs m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 p) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x22ea8) fc None m (seg_rom psegs)).
Proof.
intros until m. intros X MI FRM -> LEN P0 P4.
pose proof (rw_cells_bound _ _ _ _ X) as BX. rewrite cells_size_f32 in BX.
pose proof (munch_refl [(p, p + 4 * Z.of_nat (length xs))]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
destruct xs as [|x rest] eqn:Exs; [cbn in LEN; lia|]. rewrite <- Exs in *.
zstep. if_false_x. do 12 zstep. cond_prep.
rewrite Exs in X. rewrite !f32_cons in X.
sm_checks. zstep.
eapply signal_mul_loop with (done := []) (q := p); try eassumption.
all: try exact Exs.
all: try (cbn [length]; lia).
all: try (rewrite Exs; reflexivity).
all: try (cbn [map]; rewrite f32_nil; apply rw_cells_nil; lia).
Qed.
