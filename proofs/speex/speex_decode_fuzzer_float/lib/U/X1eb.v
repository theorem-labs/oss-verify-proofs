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

Fixpoint bw_tmp (gamma : word) (i : nat) : word :=
match i with O => fmv_s gamma | S i' => fmul_s RNE gamma (bw_tmp gamma i') end.
Definition bw_out (gamma : word) (i : nat) (x : word) : word := fmul_s RNE (bw_tmp gamma i) (nan_box (low32 x)).
Fixpoint bw_outs (gamma : word) (i : nat) (xs : list word) : list word :=
match xs with [] => [] | x :: xs' => bw_out gamma i x :: bw_outs gamma (S i) xs' end.

Lemma bw_outs_app : forall g a b i, bw_outs g i (a ++ b) = bw_outs g i a ++ bw_outs g (i + length a) b.
Proof. induction a as [|x a IH]; intros b i; cbn [bw_outs app length]; [rewrite Nat.add_0_r; reflexivity|]. rewrite IH, Nat.add_succ_r. reflexivity. Qed.
Lemma length_bw_outs : forall g xs i, length (bw_outs g i xs) = length xs.
Proof. intros g xs; induction xs; intros; cbn; [reflexivity|]. rewrite IHxs. reflexivity. Qed.
#[local] Hint Rewrite length_bw_outs : chunk_sizes.

Definition bw_lpc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(pin pout : Z) (xs : list word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 f14 f15 fc' m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 14 f14 (bvmap_set 15 f15 F)) (ret_pc ra) fc' None m' (seg_rom psegs)
/\ munch [(pout, pout + 4 * Z.of_nat (length xs))]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
/\ frm0 fc'
/\ rw_cells psegs m' pout (f32 (bw_outs (reg_get F 10) 0 xs))
/\ (pin <> pout -> rw_cells psegs m' pin (f32 xs)).

Ltac bw_checks := zstep; if_false_z; zstep; zstep; zstep; if_false_z; zstep; if_false_z;
zstep; if_false_z; zstep; zstep; zstep; if_false_z; zstep; if_false_z.

Section Proof.
Context {RCEIL : RunCeiling}.
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word.
Variable F : bvmap 5 word.
Variable m0 : word -> option byte.
Variables (pin pout : Z) (xs : list word).
Hypothesis PI0 : (0 < pin)%Z.
Hypothesis PI4 : (pin mod 4 = 0)%Z.
Hypothesis PO0 : (0 < pout)%Z.
Hypothesis PO4 : (pout mod 4 = 0)%Z.
Hypothesis LEN : (Z.of_nat (length xs) < 2^31)%Z.
Local Notation gamma := (reg_get F 10).
Local Notation W := ([(pout, pout + 4 * Z.of_nat (length xs))]%Z).

#[using="PI0 PI4 PO0 PO4 LEN"] Lemma bw_lpc_loop_inplace : forall rest done x q a2v t3v fc m,
pin = pout ->
xs = done ++ x :: rest ->
q = (pout + 4 * Z.of_nat (length done))%Z ->
a2v = Z_to_bv 64 (Z.of_nat (S (length rest))) ->
frm0 fc -> mem_inv psegs m -> munch W m0 m -> wmono psegs m0 m ->
rw_cells psegs m pout (f32 (bw_outs gamma 0 done)) ->
rw_cells psegs m q (f32 (x :: rest)) ->
evt psegs (bw_lpc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F pin pout xs m0)
(MS (mkR ra sp gp tp (Z_to_bv 64 q) (Z_to_bv 64 q) (Z_to_bv 64 q) s0 s1 (Z_to_bv 64 pin) (Z_to_bv 64 pout)
a2v (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 q)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v t4 t5 t6)
(bvmap_set 14 (nan_box (low32 x)) (bvmap_set 15 (bw_tmp gamma (length done)) F))
(Z_to_bv 64 0x22c50) fc None m (seg_rom psegs)).
Proof.
induction rest as [|x' rest IH]; intros done x q a2v t3v fc m Hio Hxs Hq Ha2 FRM MI MU WM DONE X; subst a2v;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX |- *;
pose proof (f_equal (@length word) Hxs) as HL; rewrite length_app in HL; cbn [length] in HL;
rewrite !f32_cons, ?f32_nil in X.
- do 9 zstep. if_false_x. zstep.
unfold bw_lpc_post. finish.
+ chunk_snoc DONE X. subst xs. rewrite bw_outs_app, f32_app. cbn [bw_outs Nat.add]. rewrite f32_cons, f32_nil. exact DONE.
+ intros Hne. exfalso. exact (Hne Hio).
- do 9 zstep. if_true_x.
chunk_uncons X as X1. chunk_snoc DONE X1.
bw_checks. zstep.
replace (fmul_s RNE gamma (bw_tmp gamma (length done))) with (bw_tmp gamma (length (done ++ [x])))
by (rewrite length_app; cbn [length]; rewrite Nat.add_1_r; reflexivity).
eapply (IH (done ++ [x]) x' (q + 4)%Z); try eassumption.
all: try (rewrite Hxs, <- app_assoc; reflexivity).
all: try (rewrite length_app; cbn [length]; lia).
all: try (f_equal; lia).
rewrite bw_outs_app, f32_app. cbn [bw_outs Nat.add]. rewrite f32_cons, f32_nil. exact DONE.
Qed.

#[using="PI0 PI4 PO0 PO4 LEN"] Lemma bw_lpc_loop : forall rest orest done x o q r a2v t3v fc m,
pin <> pout ->
xs = done ++ x :: rest ->
length orest = length rest ->
q = (pin + 4 * Z.of_nat (length done))%Z ->
r = (pout + 4 * Z.of_nat (length done))%Z ->
a2v = Z_to_bv 64 (Z.of_nat (S (length rest))) ->
(pin + 4 * Z.of_nat (length xs) <= pout \/ pout + 4 * Z.of_nat (length xs) <= pin)%Z ->
frm0 fc -> mem_inv psegs m -> munch W m0 m -> wmono psegs m0 m ->
rw_cells psegs m pin (f32 done) -> rw_cells psegs m q (f32 (x :: rest)) ->
rw_cells psegs m pout (f32 (bw_outs gamma 0 done)) -> rw_cells psegs m r (f32 (o :: orest)) ->
evt psegs (bw_lpc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F pin pout xs m0)
(MS (mkR ra sp gp tp (Z_to_bv 64 r) (Z_to_bv 64 r) (Z_to_bv 64 q) s0 s1 (Z_to_bv 64 pin) (Z_to_bv 64 pout)
a2v (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 q)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v t4 t5 t6)
(bvmap_set 14 (nan_box (low32 x)) (bvmap_set 15 (bw_tmp gamma (length done)) F))
(Z_to_bv 64 0x22c50) fc None m (seg_rom psegs)).
Proof.
induction rest as [|x' rest IH]; intros orest done x o q r a2v t3v fc m Hio Hxs Lor Hq Hr Ha2 SEP FRM MI MU WM IDONE X ODONE Y; subst a2v;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX |- *;
pose proof (rw_cells_bound _ _ _ _ Y) as BY; rewrite cells_size_f32 in BY; cbn [length] in BY;
pose proof (f_equal (@length word) Hxs) as HL; rewrite length_app in HL; cbn [length] in HL;
rewrite !f32_cons, ?f32_nil in X; rewrite !f32_cons in Y.
- destruct orest; [|cbn in Lor; lia]. rewrite f32_nil in Y.
do 9 zstep. if_false_x. zstep.
unfold bw_lpc_post. finish.
+ chunk_snoc ODONE Y. subst xs. rewrite bw_outs_app, f32_app. cbn [bw_outs Nat.add]. rewrite f32_cons, f32_nil. exact ODONE.
+ intros _. chunk_snoc IDONE X. subst xs. rewrite f32_app, f32_cons, f32_nil. exact IDONE.
- destruct orest as [|o' orest]; [cbn in Lor; lia|]. cbn [length] in BY, Lor. rewrite f32_cons in Y.
do 9 zstep. if_true_x.
chunk_uncons X as X1. chunk_snoc IDONE X1.
chunk_uncons Y as Y1. chunk_snoc ODONE Y1.
bw_checks. zstep.
replace (fmul_s RNE gamma (bw_tmp gamma (length done))) with (bw_tmp gamma (length (done ++ [x])))
by (rewrite length_app; cbn [length]; rewrite Nat.add_1_r; reflexivity).
eapply (IH orest (done ++ [x]) x' o' (q + 4)%Z (r + 4)%Z); try eassumption.
all: try (rewrite Hxs, <- app_assoc; reflexivity).
all: try (cbn in Lor; lia).
all: try (rewrite length_app; cbn [length]; lia).
all: try (f_equal; lia).
all: try (rewrite f32_app, f32_cons, f32_nil; exact IDONE).
rewrite bw_outs_app, f32_app. cbn [bw_outs Nat.add]. rewrite f32_cons, f32_nil. exact ODONE.
Qed.
End Proof.

Lemma bw_lpc_spec_inplace : forall (xs : list word) (p : Z)
ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m,
rw_cells psegs m p (f32 xs) ->
mem_inv psegs m -> frm0 fc ->
a2 = Z_to_bv 64 (Z.of_nat (length xs)) -> (1 <= Z.of_nat (length xs) < 2^31)%Z ->
(0 < p)%Z -> (p mod 4 = 0)%Z ->
evt psegs (bw_lpc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F p p xs m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 p) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x22bec) fc None m (seg_rom psegs)).
Proof.
intros until m. intros X MI FRM -> LEN P0 P4.
pose proof (rw_cells_bound _ _ _ _ X) as BX. rewrite cells_size_f32 in BX.
pose proof (munch_refl [(p, p + 4 * Z.of_nat (length xs))]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
destruct xs as [|x rest] eqn:Exs; [cbn in LEN; lia|]. rewrite <- Exs in *.
zstep. if_false_x. do 13 zstep. cond_prep.
rewrite Exs in X. rewrite !f32_cons in X.
bw_checks. zstep.
eapply bw_lpc_loop_inplace with (done := []) (q := p); try eassumption.
all: try reflexivity.
all: try exact Exs.
all: try (cbn [length]; lia).
all: try (rewrite Exs; reflexivity).
all: try (cbn [bw_outs]; rewrite f32_nil; apply rw_cells_nil; lia).
Qed.

Lemma bw_lpc_spec : forall (xs olds : list word) (pin pout : Z)
ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m,
rw_cells psegs m pin (f32 xs) ->
rw_cells psegs m pout (f32 olds) -> length olds = length xs ->
(pin + 4 * Z.of_nat (length xs) <= pout \/ pout + 4 * Z.of_nat (length xs) <= pin)%Z ->
mem_inv psegs m -> frm0 fc ->
a2 = Z_to_bv 64 (Z.of_nat (length xs)) -> (1 <= Z.of_nat (length xs) < 2^31)%Z ->
(0 < pin)%Z -> (pin mod 4 = 0)%Z -> (0 < pout)%Z -> (pout mod 4 = 0)%Z ->
evt psegs (bw_lpc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F pin pout xs m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 pin) (Z_to_bv 64 pout) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x22bec) fc None m (seg_rom psegs)).
Proof.
intros until m. intros X Y LO SEP MI FRM -> LEN PI0 PI4 PO0 PO4.
pose proof (rw_cells_bound _ _ _ _ X) as BX. rewrite cells_size_f32 in BX.
pose proof (rw_cells_bound _ _ _ _ Y) as BY. rewrite cells_size_f32 in BY.
pose proof (munch_refl [(pout, pout + 4 * Z.of_nat (length xs))]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
destruct xs as [|x rest] eqn:Exs; [cbn in LEN; lia|]. rewrite <- Exs in *.
destruct olds as [|o orest]; [subst xs; cbn in LO; lia|].
assert (Hne : pin <> pout) by lia.
zstep. if_false_x. do 13 zstep. cond_prep.
rewrite Exs in X. rewrite !f32_cons in X. rewrite !f32_cons in Y.
bw_checks. zstep.
eapply bw_lpc_loop with (done := []) (q := pin) (r := pout); try eassumption.
all: try reflexivity.
all: try exact Exs.
all: try (subst xs; cbn in LO |- *; lia).
all: try (cbn [length]; lia).
all: try (rewrite Exs; reflexivity).
all: try (rewrite f32_nil; apply rw_cells_nil; lia).
all: try (cbn [bw_outs]; rewrite f32_nil; apply rw_cells_nil; lia).
Qed.
