(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1df X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05l.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

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

Definition A_inner_prod : Z := 0xa5f24.

Definition inner_prod_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(usp lo : Z) (xs ys : list word) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 g0 g1 g2 g11 g12 g13 g14 fc' m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 0 g0 (bvmap_set 1 g1 (bvmap_set 2 g2
(bvmap_set 10 (ip_sum fzero_s xs ys) (bvmap_set 11 g11 (bvmap_set 12 g12 (bvmap_set 13 g13 (bvmap_set 14 g14 (bvmap_set 15 fzero_s F)))))))))
(ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(usp + -16, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp
/\ frm0 fc'.

Section S.
Variables (xs ys : list word) (n px py usp lo : Z).
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable F : bvmap 5 word.
Variable m : mem.
Hypothesis N1 : 1 <= n < 2^29.
Hypothesis LX : Z.of_nat (length xs) = 4 * n.
Hypothesis LY : Z.of_nat (length ys) = 4 * n.

Hypothesis OBX : aobj asegs m px (16 * n).
Hypothesis OBY : aobj asegs m py (16 * n).
Hypothesis X4 : px mod 4 = 0.
Hypothesis Y4 : py mod 4 = 0.
Hypothesis LO : lo <= usp - 16.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Local Notation POST := (inner_prod_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F usp lo xs ys m).
Local Notation W := [(usp + -16, usp)].

Lemma ip_block : forall (Q : machine_state -> Prop) (off k : Z) x0 x1 x2 x3 y0 y1 y2 y3 (F0 : bvmap 5 word)
(zra t2 a2 a3 a4 t3 t4 t5 t6 : word) fc m1,
0 <= off -> off + 16 <= 16 * n -> off mod 16 = 0 ->
munch W m m1 -> offsh W ->
rw_cells asegs m1 (px + off) (f32 [x0; x1; x2; x3]) -> rw_cells asegs m1 (py + off) (f32 [y0; y1; y2; y3]) ->
(forall a4' t2' t3' a2',
evt asegs Q
(MS (mkR zra (Z_to_bv 64 (usp + -16)) gp tp (Z_to_bv 64 (Z.shiftr (px + off) 3 + SHB)) (Z_to_bv 64 (Z.shiftr (py + off) 3 + SHB)) t2' s0 s1
(Z_to_bv 64 px) (Z_to_bv 64 py) a2' (Z_to_bv 64 (py + off)) a4' (Z_to_bv 64 k) (Z_to_bv 64 off) (Z_to_bv 64 SHB)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
(bvmap_set 0 (# x2) (bvmap_set 1 (# y2) (bvmap_set 2 (# x3) (bvmap_set 11 (# y1) (bvmap_set 12 (# x1) (bvmap_set 13 (# y0)
(bvmap_set 14 (# x0) F0)))))))
(Z_to_bv 64 0xa6008) fc None m1 (seg_rom asegs))) ->
evt asegs Q
(MS (mkR zra (Z_to_bv 64 (usp + -16)) gp tp (Z_to_bv 64 (Z.shiftr (px + off) 3 + SHB)) (Z_to_bv 64 (Z.shiftr (py + off) 3 + SHB)) t2 s0 s1
(Z_to_bv 64 px) (Z_to_bv 64 py) a2 a3 a4 (Z_to_bv 64 k) (Z_to_bv 64 off) (Z_to_bv 64 SHB)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F0 (Z_to_bv 64 0xa5f5c) fc None m1 (seg_rom asegs)).
Proof using OBX OBY X4 Y4.
clear N1 LX LY LO LOS SPH xs ys.
intros Q off k x0 x1 x2 x3 y0 y1 y2 y3 F0 zra t2 a2 a3 a4 t3 t4 t5 t6 fc m1 O0 O1 O16 MU OF X Y K.
pose proof OBX as (OX0 & OX1 & _). pose proof OBY as (OY0 & OY1 & _). unfold APP_TOP in *.
rewrite !f32_cons in X. rewrite !f32_cons in Y.
do 3 astep. chk_merge OBX 4.
ato 0xa5f74. astep. chk_merge OBY 4.
ato 0xa5f8c. astep. chk_merge OBX 4.
ato 0xa5fa4. astep. chk_merge OBY 4.
ato 0xa5fbc. astep. chk_merge OBX 4.
ato 0xa5fd4. astep. chk_merge OBY 4.
ato 0xa5fec. astep. chk_merge OBX 4.
ato 0xa6004. astep. chk_merge OBY 4.
apply K.
Qed.

Lemma ip_loop : forall (k : nat) (kd : nat) (kz off : Z) dx dy x0 x1 x2 x3 y0 y1 y2 y3 rx ry (j0 : list byte)
(t2 a2 a4 t3 t4 t5 t6 : word) fc m1,
kz = Z.of_nat (S k) -> off = 16 * Z.of_nat kd ->
length rx = (4 * k)%nat -> length ry = (4 * k)%nat ->
xs = dx ++ [x0; x1; x2; x3] ++ rx -> ys = dy ++ [y0; y1; y2; y3] ++ ry ->
length dx = (4 * kd)%nat -> length dy = (4 * kd)%nat ->
frm0 fc -> munch W m m1 -> offsh W -> wmono asegs m m1 -> mem_inv asegs m1 ->
stk asegs m1 lo (usp + -16) -> rw_cells asegs m1 (usp + -16) [CB 8 j0; C8 ra] ->
rw_cells asegs m1 (px + off) (f32 ([x0; x1; x2; x3] ++ rx)) -> rw_cells asegs m1 (py + off) (f32 ([y0; y1; y2; y3] ++ ry)) ->
evt asegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -16)) gp tp (Z_to_bv 64 (Z.shiftr (px + off) 3 + SHB)) (Z_to_bv 64 (Z.shiftr (py + off) 3 + SHB)) t2 s0 s1
(Z_to_bv 64 px) (Z_to_bv 64 py) a2 (Z_to_bv 64 (py + off)) a4 (Z_to_bv 64 kz) (Z_to_bv 64 off) (Z_to_bv 64 SHB)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 0 (# x2) (bvmap_set 1 (# y2) (bvmap_set 2 (# x3) (bvmap_set 10 (ip_sum fzero_s dx dy)
(bvmap_set 11 (# y1) (bvmap_set 12 (# x1) (bvmap_set 13 (# y0) (bvmap_set 14 (# x0) (bvmap_set 15 fzero_s F)))))))))
(Z_to_bv 64 0xa6008) fc None m1 (seg_rom asegs)).
Proof using N1 LX LY OBX OBY X4 Y4 LO SPH.
induction k as [|k IH]; intros kd kz off dx dy x0 x1 x2 x3 y0 y1 y2 y3 rx ry j0 t2 a2 a4 t3 t4 t5 t6 fc m1
Hkz Hoff LRX LRY Hxs Hys LDX LDY FRM MU OF WM MI ST FR X Y;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length app] in BX;
pose proof (rw_cells_bound _ _ _ _ Y) as BY; rewrite cells_size_f32 in BY; cbn [length app] in BY;
pose proof (f_equal (@length word) Hxs) as HLX; rewrite !length_app in HLX; cbn [length] in HLX;
pose proof (f_equal (@length word) Hys) as HLY; rewrite !length_app in HLY; cbn [length] in HLY;
pose proof ST as (STa & STb & _); subst kz.
- destruct rx; [|cbn in LRX; lia]. destruct ry; [|cbn in LRY; lia].
cbn [app] in X, Y. rewrite !f32_cons in X. rewrite !f32_cons in Y.
astep. rewrite swrap32_small by lia.
ato 0xa6030. astep. sh_if. astep.
replace (fadd_s RNE (ip_sum fzero_s dx dy) (fmadd_s RNE (# x3) (# y3) (fmadd_s RNE (# x2) (# y2) (fmadd_s RNE (# x1) (# y1) (fmadd_s RNE (# x0) (# y0) fzero_s)))))
with (ip_sum fzero_s xs ys)
by (rewrite Hxs, Hys, (ip_sum_app4 kd) by assumption; reflexivity).
astep. release_frame FR ST usp. astep. astep.
unfold inner_prod_post. finish.
- destruct rx as [|x0' [|x1' [|x2' [|x3' rx]]]]; try (cbn in LRX; lia).
destruct ry as [|y0' [|y1' [|y2' [|y3' ry]]]]; try (cbn in LRY; lia).
cbn [length] in LRX, LRY, BX, BY, HLX, HLY.
chunk_split_f32 X at 4%nat as X0. chunk_split_f32 Y at 4%nat as Y0.
rewrite !f32_cons in X0. rewrite !f32_cons in Y0.
astep. rewrite swrap32_small by lia.
ato 0xa6030. astep. sh_if.
replace (fadd_s RNE (ip_sum fzero_s dx dy) (fmadd_s RNE (# x3) (# y3) (fmadd_s RNE (# x2) (# y2) (fmadd_s RNE (# x1) (# y1) (fmadd_s RNE (# x0) (# y0) fzero_s)))))
with (ip_sum fzero_s (dx ++ [x0; x1; x2; x3]) (dy ++ [y0; y1; y2; y3]))
by (rewrite (ip_sum_app4 kd) by assumption; reflexivity).
rewrite !shad_step16.
replace (px + off + 16) with (px + (off + 16)) in X by lia. replace (py + off + 16) with (py + (off + 16)) in Y by lia.
pose proof X as XF. pose proof Y as YF. chunk_split_f32 XF at 4%nat as X1. chunk_split_f32 YF at 4%nat as Y1. clear XF YF.
apply (ip_block _ (off + 16) (Z.of_nat (S (S k)) + -1) x0' x1' x2' x3' y0' y1' y2' y3'); [lia | lia | | exact MU | exact OF | exact X1 | exact Y1 | ].
{ subst off. clear. Z.div_mod_to_equations. lia. }
intros a4' t2' t3' a2'. norm_fchain.
apply (IH (S kd) (Z.of_nat (S (S k)) + -1) (off + 16) (dx ++ [x0; x1; x2; x3]) (dy ++ [y0; y1; y2; y3]) x0' x1' x2' x3' y0' y1' y2' y3' rx ry j0);
try assumption;
[ lia | lia | lia | lia
| rewrite Hxs, <- app_assoc; reflexivity
| rewrite Hys, <- app_assoc; reflexivity
| rewrite length_app; cbn [length]; lia
| rewrite length_app; cbn [length]; lia ].
Qed.
End S.

Section E.
Variables (xs ys : list word) (n px py usp lo : Z).
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable F : bvmap 5 word.
Variable m : mem.
Hypothesis N1 : 1 <= n < 2^29.
Hypothesis LX : Z.of_nat (length xs) = 4 * n.
Hypothesis LY : Z.of_nat (length ys) = 4 * n.
Hypothesis OBX : aobj asegs m px (16 * n).
Hypothesis OBY : aobj asegs m py (16 * n).
Hypothesis X4 : px mod 4 = 0.
Hypothesis Y4 : py mod 4 = 0.
Hypothesis LO : lo <= usp - 16.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Local Notation POST := (inner_prod_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F usp lo xs ys m).
Local Notation W := [(usp + -16, usp)].

Lemma inner_prod_walk : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) fc,
rw_cells asegs m px (f32 xs) -> rw_cells asegs m py (f32 ys) -> frm0 fc ->
stk asegs m lo usp -> (px + 16 * n <= lo \/ usp <= px) -> (py + 16 * n <= lo \/ usp <= py) ->
client_consts m -> mem_inv asegs m ->
evt asegs POST
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 px) (Z_to_bv 64 py) (Z_to_bv 64 (4 * n)) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_inner_prod) fc None m (seg_rom asegs)).
Proof.
intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc X Y FRM ST XLO YLO (G1 & G2 & _) MI.
unfold A_inner_prod, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX.
pose proof (rw_cells_bound _ _ _ _ Y) as BY; rewrite cells_size_f32 in BY.
pose proof ST as (STa & STb & _).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh W) by (cbn; unfold SH_LO, SH_HI; lia).
destruct xs as [|x0 [|x1 [|x2 [|x3 rx]]]]; try (cbn [length] in LX; lia).
destruct ys as [|y0 [|y1 [|y2 [|y3 ry]]]]; try (cbn [length] in LY; lia).
cbn [length] in LX, LY, BX, BY.
carve_frame 16%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
astep. astep. astep. rewrite ?signed_small64 by lia.
replace (Z.shiftr (4 * n) 2) with n by (rewrite Z.shiftr_div_pow2 by lia; change (2^2) with 4; rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
astep. sh_if.
ato 0xa5f5c.
replace (SHB + Z.shiftr px 3) with (Z.shiftr (px + 0) 3 + SHB) by (rewrite Z.add_0_r; lia).
replace (SHB + Z.shiftr py 3) with (Z.shiftr (py + 0) 3 + SHB) by (rewrite Z.add_0_r; lia).
pose proof X as XF. pose proof Y as YF.
replace px with (px + 0) in XF, X by lia. replace py with (py + 0) in YF, Y by lia.
chunk_split_f32 XF at 4%nat as X1. chunk_split_f32 YF at 4%nat as Y1. clear XF YF.
apply (ip_block n px py usp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m OBX OBY X4 Y4 _ 0 n x0 x1 x2 x3 y0 y1 y2 y3); [lia | lia | reflexivity | exact MU | exact OF | exact X1 | exact Y1 | ].
intros a4' t2' t3' a2'. norm_fchain.
eapply (ip_loop _ _ n px py usp lo ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m N1) with (k := Z.to_nat (n - 1)) (kd := 0%nat) (dx := []) (dy := []);
try eassumption;
try assumption; try reflexivity; try (cbn [length] in *; lia).
- cbn [app]. exact X.
- cbn [app]. exact Y.
Qed.
End E.
