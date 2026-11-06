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

Definition ip_part (x0 x1 x2 x3 y0 y1 y2 y3 : word) : word :=
fmadd_s RNE (# x3) (# y3) (fmadd_s RNE (# x2) (# y2) (fmadd_s RNE (# x1) (# y1) (fmadd_s RNE (# x0) (# y0) fzero_s))).
Fixpoint ip_sum (acc : word) (xs ys : list word) {struct xs} : word :=
match xs, ys with
| x0 :: x1 :: x2 :: x3 :: xs', y0 :: y1 :: y2 :: y3 :: ys' => ip_sum (fadd_s RNE acc (ip_part x0 x1 x2 x3 y0 y1 y2 y3)) xs' ys'
| _, _ => acc
end.
Lemma ip_sum_block : forall acc x0 x1 x2 x3 xs y0 y1 y2 y3 ys,
ip_sum acc (x0 :: x1 :: x2 :: x3 :: xs) (y0 :: y1 :: y2 :: y3 :: ys) = ip_sum (fadd_s RNE acc (ip_part x0 x1 x2 x3 y0 y1 y2 y3)) xs ys.
Proof. reflexivity. Qed.
Lemma ip_sum_app4 : forall k ax ay bx byy acc, length ax = (4 * k)%nat -> length ay = (4 * k)%nat ->
ip_sum acc (ax ++ bx) (ay ++ byy) = ip_sum (ip_sum acc ax ay) bx byy.
Proof.
induction k as [|k IH]; intros ax ay bx byy acc LX LY.
- destruct ax; [|cbn in LX; lia]. destruct ay; [|cbn in LY; lia]. reflexivity.
- destruct ax as [|x0 [|x1 [|x2 [|x3 ax']]]]; try (cbn in LX; lia).
destruct ay as [|y0 [|y1 [|y2 [|y3 ay']]]]; try (cbn in LY; lia).
cbn [app]. rewrite !ip_sum_block. apply IH; cbn in LX, LY; lia.
Qed.

Definition inner_prod_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(xs ys : list word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 g0 g1 g2 g3 g11 g12 g13 g14 fc' m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 0 g0 (bvmap_set 1 g1 (bvmap_set 2 g2 (bvmap_set 3 g3
(bvmap_set 10 (ip_sum fzero_s xs ys) (bvmap_set 11 g11 (bvmap_set 12 g12 (bvmap_set 13 g13 (bvmap_set 14 g14 (bvmap_set 15 fzero_s F))))))))))
(ret_pc ra) fc' None m' (seg_rom psegs)
/\ munch [] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
/\ frm0 fc'.

Section S.
Context {RCEIL : RunCeiling}.
Variables (xs ys : list word) (n px py : Z).
Variables ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Variable F : bvmap 5 word.
Variable m : word -> option byte.
Hypothesis MI : mem_inv psegs m.
Hypothesis N1 : (1 <= n < 2^29)%Z.
Hypothesis LX : Z.of_nat (length xs) = (4 * n)%Z.
Hypothesis LY : Z.of_nat (length ys) = (4 * n)%Z.
Local Notation POST := (inner_prod_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F xs ys m).

#[using="MI N1 LX LY"] Lemma ip_loop : forall (k : nat) (kd : nat) dx dy x0 x1 x2 x3 y0 y1 y2 y3 rx ry qx qy (xa3 : word) fc,
length rx = (4 * k)%nat -> length ry = (4 * k)%nat ->
xs = dx ++ [x0; x1; x2; x3] ++ rx -> ys = dy ++ [y0; y1; y2; y3] ++ ry ->
length dx = (4 * kd)%nat -> length dy = (4 * kd)%nat ->
qx = (px + 4 * Z.of_nat (length dx))%Z -> qy = (py + 4 * Z.of_nat (length dy))%Z ->
frm0 fc ->
rw_cells psegs m qx (f32 ([x0; x1; x2; x3] ++ rx)) -> rw_cells psegs m qy (f32 ([y0; y1; y2; y3] ++ ry)) ->
evt psegs POST
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 qx) (Z_to_bv 64 qy) (Z_to_bv 64 (py + 16 * n)) xa3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 0 (# y0) (bvmap_set 1 (# y1) (bvmap_set 2 (# y2) (bvmap_set 3 (# y3)
(bvmap_set 10 (ip_sum fzero_s dx dy) (bvmap_set 11 (# x3) (bvmap_set 12 (# x2) (bvmap_set 13 (# x1) (bvmap_set 14 (# x0)
(bvmap_set 15 fzero_s F))))))))))
(Z_to_bv 64 0x21b5c) fc None m (seg_rom psegs)).
Proof.
induction k as [|k IH]; intros kd dx dy x0 x1 x2 x3 y0 y1 y2 y3 rx ry qx qy xa3 fc LRX LRY Hxs Hys LDX LDY Hqx Hqy FRM X Y;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length app] in BX;
pose proof (rw_cells_bound _ _ _ _ Y) as BY; rewrite cells_size_f32 in BY; cbn [length app] in BY;
pose proof (f_equal (@length word) Hxs) as HLX; rewrite !length_app in HLX; cbn [length] in HLX;
pose proof (f_equal (@length word) Hys) as HLY; rewrite !length_app in HLY; cbn [length] in HLY.
- destruct rx; [|cbn in LRX; lia]. destruct ry; [|cbn in LRY; lia].
do 9 zstep. if_false_x. zstep.
replace (fadd_s RNE (ip_sum fzero_s dx dy) (fmadd_s RNE (# x3) (# y3) (fmadd_s RNE (# x2) (# y2) (fmadd_s RNE (# x1) (# y1) (fmadd_s RNE (# x0) (# y0) fzero_s)))))
with (ip_sum fzero_s xs ys)
by (rewrite Hxs, Hys, (ip_sum_app4 kd) by assumption; reflexivity).
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl psegs m) as WM.
unfold inner_prod_post. finish.
- destruct rx as [|x0' [|x1' [|x2' [|x3' rx]]]]; try (cbn in LRX; lia).
destruct ry as [|y0' [|y1' [|y2' [|y3' ry]]]]; try (cbn in LRY; lia).
cbn [length] in LRX, LRY, BX, BY, HLX, HLY.
do 9 zstep. if_true_x.
chunk_split_f32 X at 4%nat as X0. chunk_split_f32 Y at 4%nat as Y0.
pose proof (rw_cells_bound _ _ _ _ X) as BX'; rewrite cells_size_f32 in BX'; cbn [length app] in BX'.
pose proof (rw_cells_bound _ _ _ _ Y) as BY'; rewrite cells_size_f32 in BY'; cbn [length app] in BY'.
rewrite !f32_cons in X. rewrite !f32_cons in Y.
do 8 zstep.
replace (fadd_s RNE (ip_sum fzero_s dx dy) (fmadd_s RNE (# x3) (# y3) (fmadd_s RNE (# x2) (# y2) (fmadd_s RNE (# x1) (# y1) (fmadd_s RNE (# x0) (# y0) fzero_s)))))
with (ip_sum fzero_s (dx ++ [x0; x1; x2; x3]) (dy ++ [y0; y1; y2; y3]))
by (rewrite (ip_sum_app4 kd) by assumption; reflexivity).
apply (IH (S kd) (dx ++ [x0; x1; x2; x3]) (dy ++ [y0; y1; y2; y3]) x0' x1' x2' x3' y0' y1' y2' y3' rx ry (qx + 16)%Z (qy + 16)%Z);
try assumption;
[ lia | lia
| rewrite Hxs, <- app_assoc; reflexivity
| rewrite Hys, <- app_assoc; reflexivity
| rewrite length_app; cbn [length]; lia
| rewrite length_app; cbn [length]; lia
| rewrite length_app; cbn [length]; lia
| rewrite length_app; cbn [length]; lia ].
Qed.
End S.

Section E.
Context {RCEIL : RunCeiling}.
Variables (xs ys : list word) (n px py : Z).
Variables ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Variable F : bvmap 5 word.
Variable m : word -> option byte.
Hypothesis MI : mem_inv psegs m.
Hypothesis N1 : (1 <= n < 2^29)%Z.
Hypothesis LX : Z.of_nat (length xs) = (4 * n)%Z.
Hypothesis LY : Z.of_nat (length ys) = (4 * n)%Z.

#[using="MI N1 LX LY"] Lemma inner_prod_spec : forall fc,
rw_cells psegs m px (f32 xs) -> rw_cells psegs m py (f32 ys) -> frm0 fc ->
evt psegs (inner_prod_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F xs ys m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 px) (Z_to_bv 64 py) (Z_to_bv 64 (4 * n)) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x21b18) fc None m (seg_rom psegs)).
Proof.
intros fc X Y FRM.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX.
pose proof (rw_cells_bound _ _ _ _ Y) as BY; rewrite cells_size_f32 in BY.
destruct xs as [|x0 [|x1 [|x2 [|x3 rx]]]]; try (cbn [length] in LX; lia).
destruct ys as [|y0 [|y1 [|y2 [|y3 ry]]]]; try (cbn [length] in LY; lia).
cbn [length] in LX, LY, BX, BY. rewrite !f32_cons in X. rewrite !f32_cons in Y.
zstep. rewrite zb_signed_small by lia.
replace (Z.shiftr (4 * n) 2) with n by (rewrite Z.shiftr_div_pow2 by lia; change (2^2)%Z with 4%Z; rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
zstep. if_false_x. do 7 zstep.
replace (Z.shiftr (Z.shiftl (n + -1) 32 mod 18446744073709551616) 28 + py + 16)%Z with (py + 16 * n)%Z.
2:{ rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
change (2^32)%Z with (268435456 * 16)%Z. change (2^28)%Z with 268435456%Z.
rewrite Z.mod_small by lia.
replace ((n + -1) * (268435456 * 16))%Z with ((n + -1) * 16 * 268435456)%Z by lia.
rewrite Z.div_mul by lia. lia. }
do 8 zstep.
eapply ip_loop with (px := px) (py := py) (dx := []) (dy := []) (kd := 0%nat) (k := Z.to_nat (n - 1));
try eassumption; try reflexivity; try (cbn [length] in *; lia).
- cbn [app]. rewrite !f32_cons. exact X.
- cbn [app]. rewrite !f32_cons. exact Y.
Qed.
End E.
