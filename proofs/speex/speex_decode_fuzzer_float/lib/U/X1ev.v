(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import UbDec X1cc.
Import ListNotations.
Open Scope bv_scope.
Local Notation psegs := Ubsan.M.loaded_segments.

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
(xs ys : list word) (m : word -> option byte) (lo : Z) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 g0 g1 g11 g12 g13 g14 fc' m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 0 g0 (bvmap_set 1 g1
(bvmap_set 10 (ip_sum fzero_s xs ys) (bvmap_set 11 g11 (bvmap_set 12 g12 (bvmap_set 13 g13 (bvmap_set 14 g14 (bvmap_set 15 fzero_s F))))))))
(ret_pc ra) fc' None m' (seg_rom psegs)
/\ munch [(lo, bv_unsigned sp)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
/\ frm0 fc' /\ stk psegs m' lo (bv_unsigned sp).

Section S.
Context {RCEIL : RunCeiling}.
Variables (xs ys : list word) (n px py lo : Z).
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable F : bvmap 5 word.
Variable m0 : word -> option byte.
Hypothesis N1 : (1 <= n < 2^29)%Z.
Hypothesis LX : Z.of_nat (length xs) = (4 * n)%Z.
Hypothesis LY : Z.of_nat (length ys) = (4 * n)%Z.
Hypothesis P0 : (0 < px)%Z.
Hypothesis Q0 : (0 < py)%Z.
Hypothesis PB : (px + 16 * n < 2^63)%Z.
Hypothesis QB : (py + 16 * n < 2^63)%Z.
Hypothesis SPL : (lo + 16 <= bv_unsigned sp)%Z.
Local Notation usp := (bv_unsigned sp).
Local Notation POST := (inner_prod_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F xs ys m0 lo).

#[using="N1 LX LY P0 Q0 PB QB SPL"] Lemma ip_loop : forall (k kd : nat) dx dy x0 x1 x2 x3 y0 y1 y2 y3 rx ry qx qy fc m1,
length rx = (4 * k)%nat -> length ry = (4 * k)%nat ->
xs = dx ++ [x0; x1; x2; x3] ++ rx -> ys = dy ++ [y0; y1; y2; y3] ++ ry ->
length dx = (4 * kd)%nat -> length dy = (4 * kd)%nat ->
qx = (px + 4 * Z.of_nat (length dx))%Z -> qy = (py + 4 * Z.of_nat (length dy))%Z ->
frm0 fc -> munch [(lo, usp)] m0 m1 -> wmono psegs m0 m1 -> mem_inv psegs m1 ->
stk psegs m1 lo (usp + -16)%Z -> rw_cells psegs m1 (usp + -16)%Z [C8 s1; C8 s0] ->
rw_cells psegs m1 qx (f32 ([x0; x1; x2; x3] ++ rx)) -> rw_cells psegs m1 qy (f32 ([y0; y1; y2; y3] ++ ry)) ->
evt psegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -16)) gp tp (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 qx) (Z_to_bv 64 qy) (Z_to_bv 64 (qx + 8)) (Z_to_bv 64 (qy + 8))
(Z_to_bv 64 qx) (Z_to_bv 64 qy) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) (Z_to_bv 64 4) (Z_to_bv 64 5) (Z_to_bv 64 (-5))
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (qx + 4)) (Z_to_bv 64 (qx + 12)) (Z_to_bv 64 (qy + 12)) (Z_to_bv 64 (qy + 4)))
(bvmap_set 0 (# x2) (bvmap_set 1 (# y2) (bvmap_set 10 (ip_sum fzero_s dx dy) (bvmap_set 11 (# y1) (bvmap_set 12 (# x1) (bvmap_set 13 (# x0)
(bvmap_set 14 (# y0) (bvmap_set 15 fzero_s F))))))))
(Z_to_bv 64 0x24ff8) fc None m1 (seg_rom psegs)).
Proof.
induction k as [|k IH]; intros kd dx dy x0 x1 x2 x3 y0 y1 y2 y3 rx ry qx qy fc m1 LRX LRY Hxs Hys LDX LDY Hqx Hqy FRM MU WM MI ST FR X Y;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length app] in BX;
pose proof (rw_cells_bound _ _ _ _ Y) as BY; rewrite cells_size_f32 in BY; cbn [length app] in BY;
pose proof (f_equal (@length word) Hxs) as HLX; rewrite !length_app in HLX; cbn [length] in HLX;
pose proof (f_equal (@length word) Hys) as HLY; rewrite !length_app in HLY; cbn [length] in HLY;
pose proof ST as (STa & STb & _).
- destruct rx; [|cbn in LRX; lia]. destruct ry; [|cbn in LRY; lia].
cbn [app] in X, Y. rewrite !f32_cons, f32_nil in X. rewrite !f32_cons, f32_nil in Y.
bato 0x24f88%Z. bato 0x25030%Z.
do 4 zstep.
replace (fadd_s RNE (ip_sum fzero_s dx dy) (fmadd_s RNE (# x3) (# y3) (fmadd_s RNE (# x2) (# y2) (fmadd_s RNE (# x1) (# y1) (fmadd_s RNE (# x0) (# y0) fzero_s)))))
with (ip_sum fzero_s xs ys)
by (rewrite Hxs, Hys, (ip_sum_app4 kd) by assumption; reflexivity).
release_frame FR ST (bv_unsigned sp).
finish.
- destruct rx as [|x0' [|x1' [|x2' [|x3' rx]]]]; try (cbn in LRX; lia).
destruct ry as [|y0' [|y1' [|y2' [|y3' ry]]]]; try (cbn in LRY; lia).
cbn [length] in LRX, LRY, BX, BY, HLX, HLY.
chunk_split_f32 X at 4%nat as X0. chunk_split_f32 Y at 4%nat as Y0.
rewrite !f32_cons, f32_nil in X0. rewrite !f32_cons, f32_nil in Y0. rewrite !f32_cons in X. rewrite !f32_cons in Y.
bato 0x24f88%Z. bato 0x24ff8%Z.
replace (Z.of_nat (S k) + -1)%Z with (Z.of_nat k) by lia.
replace (qx + 20)%Z with (qx + 16 + 4)%Z by lia. replace (qx + 24)%Z with (qx + 16 + 8)%Z by lia. replace (qx + 28)%Z with (qx + 16 + 12)%Z by lia.
replace (qy + 20)%Z with (qy + 16 + 4)%Z by lia. replace (qy + 24)%Z with (qy + 16 + 8)%Z by lia. replace (qy + 28)%Z with (qy + 16 + 12)%Z by lia.
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
Variables (xs ys : list word) (n px py lo : Z).
Variables ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Variable F : bvmap 5 word.
Variable m : word -> option byte.
Hypothesis MI : mem_inv psegs m.
Hypothesis N1 : (1 <= n < 2^29)%Z.
Hypothesis LX : Z.of_nat (length xs) = (4 * n)%Z.
Hypothesis LY : Z.of_nat (length ys) = (4 * n)%Z.
Hypothesis P0 : (0 < px)%Z.
Hypothesis P4 : (px mod 4 = 0)%Z.
Hypothesis Q0 : (0 < py)%Z.
Hypothesis Q4 : (py mod 4 = 0)%Z.

#[using="MI N1 LX LY P0 P4 Q0 Q4"] Lemma inner_prod_spec : forall fc,
stk psegs m lo (bv_unsigned sp) -> (lo + 16 <= bv_unsigned sp)%Z ->
apart px (16 * n)%Z lo (bv_unsigned sp - lo)%Z -> apart py (16 * n)%Z lo (bv_unsigned sp - lo)%Z ->
rw_cells psegs m px (f32 xs) -> rw_cells psegs m py (f32 ys) -> frm0 fc ->
evt psegs (inner_prod_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F xs ys m lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 px) (Z_to_bv 64 py) (Z_to_bv 64 (4 * n)) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x24f4c) fc None m (seg_rom psegs)).
Proof.
intros fc ST SPL AX AY X Y FRM.
pose proof AX as AX'. pose proof AY as AY'. unfold apart in AX', AY'.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX.
pose proof (rw_cells_bound _ _ _ _ Y) as BY; rewrite cells_size_f32 in BY.
assert (MT : mem_top psegs = TASK_SIZE) by reflexivity.
assert (PB : (px + 16 * n < 2^63)%Z).
{ pose proof (wr_at_below _ _ _ _ MI (rw_cells_wr_at _ _ _ _ (16 * n)%Z X ltac:(rewrite cells_size_f32; lia)) ltac:(lia)) as H.
rewrite MT in H. unfold TASK_SIZE in H. lia. }
assert (QB : (py + 16 * n < 2^63)%Z).
{ pose proof (wr_at_below _ _ _ _ MI (rw_cells_wr_at _ _ _ _ (16 * n)%Z Y ltac:(rewrite cells_size_f32; lia)) ltac:(lia)) as H.
rewrite MT in H. unfold TASK_SIZE in H. lia. }
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl psegs m) as WM.
destruct xs as [|x0 [|x1 [|x2 [|x3 rx]]]]; try (cbn [length] in LX; lia).
destruct ys as [|y0 [|y1 [|y2 [|y3 ry]]]]; try (cbn [length] in LY; lia).
cbn [length] in LX, LY, BX, BY. rewrite !f32_cons in X. rewrite !f32_cons in Y.
carve_frame 16%nat ST.
destruct (rw_cells_CB_C8s psegs _ _ 2%nat _ FR) as (fw & Lfw & FR'); clear FR.
destruct fw as [|w0 [|w1 [|? ?]]]; cbn in Lfw; try lia. cbn [map] in FR'. rename FR' into FR.
zstep. zstep. zstep.
zstep. rewrite zb_signed_small by lia.
replace (Z.shiftr (4 * n) 2) with n by (rewrite Z.shiftr_div_pow2 by lia; change (2^2)%Z with 4%Z; rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
bato 0x24ff8%Z.
replace (n + -1)%Z with (Z.of_nat (Z.to_nat (n - 1))) by lia.
eapply (ip_loop (x0 :: x1 :: x2 :: x3 :: rx) (y0 :: y1 :: y2 :: y3 :: ry) n px py lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m
N1 ltac:(cbn [length]; lia) ltac:(cbn [length]; lia) P0 Q0 PB QB SPL (Z.to_nat (n - 1)) 0 [] [] x0 x1 x2 x3 y0 y1 y2 y3 rx ry px py);
try eassumption.
all: first [ reflexivity | (cbn [length]; lia) ].
Qed.
End E.
