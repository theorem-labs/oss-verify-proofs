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

Fixpoint rms_sum (acc : word) (xs : list word) : word :=
match xs with
| [] => acc
| x :: xs' => rms_sum (fmadd_s RNE (nan_box (low32 x)) (nan_box (low32 x)) acc) xs'
end.
Lemma rms_sum_app : forall a b acc, rms_sum acc (a ++ b) = rms_sum (rms_sum acc a) b.
Proof. induction a; intros; cbn; [reflexivity|]. apply IHa. Qed.

Definition d_0_1 : word := Z_to_bv 64 0x3FB999999999999A.

Definition rms_result (sum lenw : word) : word :=
fcvt_s_d RNE (fsqrt_d RNE (fadd_d RNE (fcvt_d_s RNE (fdiv_s RNE sum (fcvt_s_w RNE lenw))) d_0_1)).

Definition compute_rms16_post (ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(xs : list word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 g13 g14 g15 fc' m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 10 (rms_result (rms_sum fzero_s xs) a1) (bvmap_set 13 g13 (bvmap_set 14 g14 (bvmap_set 15 g15 F))))
(ret_pc ra) fc' None m' (seg_rom psegs)
/\ munch [] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
/\ frm0 fc'.

Ltac rms_checks := zstep; if_false_z; zstep; zstep; zstep; if_false_z; zstep; if_false_z.

Section S.
Context {RCEIL : RunCeiling}.
Variables (xs : list word) (p : Z).
Variables ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Variable F : bvmap 5 word.
Variable m : word -> option byte.
Hypothesis MI : mem_inv psegs m.
Hypothesis LEN : (1 <= Z.of_nat (length xs) < 2^31)%Z.
Local Notation lenw := (Z_to_bv 64 (Z.of_nat (length xs))).
Local Notation POST := (compute_rms16_post ra sp gp tp s0 s1 lenw s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F xs m).

#[using="MI LEN"] Lemma rms_loop : forall rest done x q a4v a7v fc,
(0 < p)%Z -> (p mod 4 = 0)%Z ->
xs = done ++ x :: rest ->
q = (p + 4 * Z.of_nat (length done))%Z ->
a4v = Z_to_bv 64 (Z.of_nat (S (length rest))) ->
frm0 fc ->
rw_cells psegs m q (f32 (x :: rest)) ->
evt psegs POST
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) lenw (Z_to_bv 64 1) (Z_to_bv 64 1) a4v (Z_to_bv 64 q) (Z_to_bv 64 q) a7v
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 14 (nan_box (low32 x)) (bvmap_set 15 (rms_sum fzero_s done) F))
(Z_to_bv 64 0x23000) fc None m (seg_rom psegs)).
Proof.
induction rest as [|x' rest IH]; intros done x q a4v a7v fc P0 P4 Hxs Hq Ha4 FRM X; subst a4v;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX |- *;
pose proof (f_equal (@length word) Hxs) as HL; rewrite length_app in HL; cbn [length] in HL;
rewrite !f32_cons, ?f32_nil in X.
- do 5 zstep. if_false_x. do 10 zstep.
replace (fmadd_s RNE (nan_box (low32 x)) (nan_box (low32 x)) (rms_sum fzero_s done))
with (rms_sum fzero_s xs) by (rewrite Hxs, rms_sum_app; reflexivity).
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl psegs m) as WM.
unfold compute_rms16_post. finish.
- do 5 zstep. if_true_x. chunk_uncons X as X1.
rms_checks. zstep.
replace (fmadd_s RNE (nan_box (low32 x)) (nan_box (low32 x)) (rms_sum fzero_s done))
with (rms_sum fzero_s (done ++ [x])) by (rewrite rms_sum_app; reflexivity).
eapply (IH (done ++ [x]) x' (q + 4)%Z); try eassumption.
all: try (rewrite Hxs, <- app_assoc; reflexivity).
all: try (rewrite length_app; cbn [length]; lia).
all: try (f_equal; lia).
Qed.

#[using="MI LEN"] Lemma compute_rms16_spec : forall a2 fc,
rw_cells psegs m p (f32 xs) -> frm0 fc ->
(0 < p)%Z -> (p mod 4 = 0)%Z ->
evt psegs POST
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) lenw a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x23044) fc None m (seg_rom psegs)).
Proof.
intros a2 fc X FRM P0 P4.
pose proof (rw_cells_bound _ _ _ _ X) as BX. rewrite cells_size_f32 in BX.
destruct xs as [|x rest] eqn:Exs; [cbn in LEN; lia|]. rewrite <- Exs in *.
zstep. zstep. if_false_x. do 8 zstep. cond_prep.
rewrite Exs in X. rewrite !f32_cons in X.
rms_checks. zstep.
eapply (rms_loop rest [] x p); try eassumption.
all: try exact Exs.
all: try (cbn [length]; lia).
all: try (rewrite Exs; reflexivity).
Qed.
End S.
