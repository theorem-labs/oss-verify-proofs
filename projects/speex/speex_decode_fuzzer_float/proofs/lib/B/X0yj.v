(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1df X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05l X07r.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation "# x" := (nan_box (low32 x)) (at level 9, format "# x").

Definition B_inner_prod : Z := 0xa9cbc.

Definition inner_prodB_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(usp lo : Z) (xs ys : list word) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 g0 g1 g2 g11 g12 g13 g14 fc' m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 0 g0 (bvmap_set 1 g1 (bvmap_set 2 g2
(bvmap_set 10 (ip_sum fzero_s xs ys) (bvmap_set 11 g11 (bvmap_set 12 g12 (bvmap_set 13 g13 (bvmap_set 14 g14 (bvmap_set 15 fzero_s F)))))))))
(ret_pc ra) fc' None m' (seg_rom bsegs)
/\ munch [(usp + -48, usp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp
/\ frm0 fc'.

Section S.
Variables (xs ys : list word) (n px py usp lo : Z).
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable F : bvmap 5 word.
Variable m : mem.
Hypothesis N1 : 1 <= n < 2^29.
Hypothesis LX : Z.of_nat (length xs) = 4 * n.
Hypothesis LY : Z.of_nat (length ys) = 4 * n.
Hypothesis OBX : aobj bsegs m px (16 * n).
Hypothesis OBY : aobj bsegs m py (16 * n).
Hypothesis X4 : px mod 4 = 0.
Hypothesis Y4 : py mod 4 = 0.
Hypothesis XP : 0 < px.
Hypothesis YP : 0 < py.
Hypothesis LO : lo <= usp - 48.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Local Notation POST := (inner_prodB_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F usp lo xs ys m).
Local Notation W := [(usp + -48, usp)].

Lemma ipB_block : forall (Q : machine_state -> Prop) (off k : Z) x0 x1 x2 x3 y0 y1 y2 y3 (F0 : bvmap 5 word)
(zra z1 a3 a4 a5 z2 z3 z4 : word) fc m1,
0 <= off -> off + 16 <= 16 * n -> off mod 16 = 0 -> 0 <= k < 2^31 ->
munch W m m1 -> offsh W ->
rw_cells bsegs m1 (px + off) (f32 [x0; x1; x2; x3]) -> rw_cells bsegs m1 (py + off) (f32 [y0; y1; y2; y3]) ->
(forall a2' a5' z2' z4',
evt bsegs Q
(MS (mkR zra (Z_to_bv 64 (usp + -48)) gp tp (Z_to_bv 64 0) (Z_to_bv 64 (-1)) (Z_to_bv 64 SHB) (Z_to_bv 64 (-5)) (Z_to_bv 64 k)
(Z_to_bv 64 px) (Z_to_bv 64 py) a2' (Z_to_bv 64 (py + off + 12)) (Z_to_bv 64 (py + off + 12)) a5' (Z_to_bv 64 off) (Z_to_bv 64 0)
z2' (Z_to_bv 64 (px + off + 12)) z4' s5 s6 s7 s8 s9 s10 s11
(Z_to_bv 64 4) (Z_to_bv 64 5) (Z_to_bv 64 (Z.shiftr (py + off) 3 + SHB)) (Z_to_bv 64 (Z.shiftr (px + off) 3 + SHB)))
(bvmap_set 0 (# x2) (bvmap_set 1 (# y2) (bvmap_set 2 (# x3) (bvmap_set 11 (# y1) (bvmap_set 12 (# x1) (bvmap_set 13 (# y0)
(bvmap_set 14 (# x0) F0)))))))
(Z_to_bv 64 0xa9e14) fc None m1 (seg_rom bsegs))) ->
evt bsegs Q
(MS (mkR zra (Z_to_bv 64 (usp + -48)) gp tp (Z_to_bv 64 0) (Z_to_bv 64 (-1)) (Z_to_bv 64 SHB) (Z_to_bv 64 (-5)) z1
(Z_to_bv 64 px) (Z_to_bv 64 py) (Z_to_bv 64 k) a3 a4 a5 (Z_to_bv 64 off) (Z_to_bv 64 0)
z2 z3 z4 s5 s6 s7 s8 s9 s10 s11
(Z_to_bv 64 4) (Z_to_bv 64 5) (Z_to_bv 64 (Z.shiftr (py + off) 3 + SHB)) (Z_to_bv 64 (Z.shiftr (px + off) 3 + SHB)))
F0 (Z_to_bv 64 0xa9d20) fc None m1 (seg_rom bsegs)).
Proof using OBX OBY X4 Y4 XP YP.
clear N1 LX LY LO LOS SPH xs ys.
intros Q off k x0 x1 x2 x3 y0 y1 y2 y3 F0 zra z1 a3 a4 a5 z2 z3 z4 fc m1 O0 O1 O16 Hk MU OF X Y K.
pose proof OBX as (OX0 & OX1 & _). pose proof OBY as (OY0 & OY1 & _). unfold APP_TOP in *.
rewrite !f32_cons in X. rewrite !f32_cons in Y.
astep. sh_if.
ato 0xa9d30. astep. sh_if. ato 0xa9d34. astep. sh_if.
ato 0xa9d40. astep. chk_merge OBX 4.
ato 0xa9d4c. astep. sh_if. ato 0xa9d50. astep. sh_if.
ato 0xa9d60. astep. chk_merge OBY 4.
ato 0xa9d64. astep. sh_if. ato 0xa9d68. astep. sh_if.
ato 0xa9d7c. astep. chk_merge OBX 4.
ato 0xa9d90. astep. chk_merge OBY 4.
ato 0xa9d98. astep. sh_if. ato 0xa9da0. astep. sh_if.
ato 0xa9db8. astep. chk_merge OBX 4.
ato 0xa9dd0. astep. chk_merge OBY 4.
ato 0xa9dd8. astep. sh_if. ato 0xa9de0. astep. sh_if.
ato 0xa9df8. astep. chk_merge OBX 4.
ato 0xa9e10. astep. chk_merge OBY 4.
apply K.
Qed.

Lemma ipB_loop : forall (k : nat) (kd : nat) (kz off : Z) dx dy x0 x1 x2 x3 y0 y1 y2 y3 rx ry
(a2 a5 z2 z4 : word) fc m1,
kz = Z.of_nat k -> off = 16 * Z.of_nat kd ->
length rx = (4 * k)%nat -> length ry = (4 * k)%nat ->
xs = dx ++ [x0; x1; x2; x3] ++ rx -> ys = dy ++ [y0; y1; y2; y3] ++ ry ->
length dx = (4 * kd)%nat -> length dy = (4 * kd)%nat ->
frm0 fc -> munch W m m1 -> offsh W -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
stk bsegs m1 lo (usp + -48) -> rw_cells bsegs m1 (usp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells bsegs m1 (px + off) (f32 ([x0; x1; x2; x3] ++ rx)) -> rw_cells bsegs m1 (py + off) (f32 ([y0; y1; y2; y3] ++ ry)) ->
evt bsegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -48)) gp tp (Z_to_bv 64 0) (Z_to_bv 64 (-1)) (Z_to_bv 64 SHB) (Z_to_bv 64 (-5)) (Z_to_bv 64 kz)
(Z_to_bv 64 px) (Z_to_bv 64 py) a2 (Z_to_bv 64 (py + off + 12)) (Z_to_bv 64 (py + off + 12)) a5 (Z_to_bv 64 off) (Z_to_bv 64 0)
z2 (Z_to_bv 64 (px + off + 12)) z4 s5 s6 s7 s8 s9 s10 s11
(Z_to_bv 64 4) (Z_to_bv 64 5) (Z_to_bv 64 (Z.shiftr (py + off) 3 + SHB)) (Z_to_bv 64 (Z.shiftr (px + off) 3 + SHB)))
(bvmap_set 0 (# x2) (bvmap_set 1 (# y2) (bvmap_set 2 (# x3) (bvmap_set 10 (ip_sum fzero_s dx dy)
(bvmap_set 11 (# y1) (bvmap_set 12 (# x1) (bvmap_set 13 (# y0) (bvmap_set 14 (# x0) (bvmap_set 15 fzero_s F)))))))))
(Z_to_bv 64 0xa9e14) fc None m1 (seg_rom bsegs)).
Proof using N1 LX LY OBX OBY X4 Y4 XP YP LO SPH.
induction k as [|k IH]; intros kd kz off dx dy x0 x1 x2 x3 y0 y1 y2 y3 rx ry a2 a5 z2 z4 fc m1
Hkz Hoff LRX LRY Hxs Hys LDX LDY FRM MU OF WM MI ST FR X Y;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length app] in BX;
pose proof (rw_cells_bound _ _ _ _ Y) as BY; rewrite cells_size_f32 in BY; cbn [length app] in BY;
pose proof (f_equal (@length word) Hxs) as HLX; rewrite !length_app in HLX; cbn [length] in HLX;
pose proof (f_equal (@length word) Hys) as HLY; rewrite !length_app in HLY; cbn [length] in HLY;
pose proof ST as (STa & STb & _); subst kz.
- destruct rx; [|cbn in LRX; lia]. destruct ry; [|cbn in LRY; lia].
cbn [app] in X, Y. rewrite !f32_cons in X. rewrite !f32_cons in Y.
ato 0xa9e3c. change (Z.of_nat 0) with 0. change (bv_swrap 32 (0 + -1)) with (-1).
astep.
ato 0xa9ec8.
replace (fadd_s RNE (ip_sum fzero_s dx dy) (fmadd_s RNE (# x3) (# y3) (fmadd_s RNE (# x2) (# y2) (fmadd_s RNE (# x1) (# y1) (fmadd_s RNE (# x0) (# y0) fzero_s)))))
with (ip_sum fzero_s xs ys)
by (rewrite Hxs, Hys, (ip_sum_app4 kd) by assumption; reflexivity).
ato 0xa9ee0. release_frame FR ST usp. astep. astep.
unfold inner_prodB_post. finish.
- destruct rx as [|x0' [|x1' [|x2' [|x3' rx]]]]; try (cbn in LRX; lia).
destruct ry as [|y0' [|y1' [|y2' [|y3' ry]]]]; try (cbn in LRY; lia).
cbn [length] in LRX, LRY, BX, BY, HLX, HLY.
chunk_split_f32 X at 4%nat as X0. chunk_split_f32 Y at 4%nat as Y0.
rewrite !f32_cons in X0. rewrite !f32_cons in Y0.
ato 0xa9e3c. rewrite swrap32_small by lia.
astep. sh_if.
replace (fadd_s RNE (ip_sum fzero_s dx dy) (fmadd_s RNE (# x3) (# y3) (fmadd_s RNE (# x2) (# y2) (fmadd_s RNE (# x1) (# y1) (fmadd_s RNE (# x0) (# y0) fzero_s)))))
with (ip_sum fzero_s (dx ++ [x0; x1; x2; x3]) (dy ++ [y0; y1; y2; y3]))
by (rewrite (ip_sum_app4 kd) by assumption; reflexivity).
rewrite !shad_step16.
replace (px + off + 16) with (px + (off + 16)) in X by lia. replace (py + off + 16) with (py + (off + 16)) in Y by lia.
pose proof X as XF. pose proof Y as YF. chunk_split_f32 XF at 4%nat as X1. chunk_split_f32 YF at 4%nat as Y1. clear XF YF.
apply (ipB_block _ (off + 16) (Z.of_nat (S k) + -1) x0' x1' x2' x3' y0' y1' y2' y3'); [lia | lia | | lia | exact MU | exact OF | exact X1 | exact Y1 | ].
{ subst off. clear. Z.div_mod_to_equations. lia. }
intros a2' a5' z2' z4'. norm_fchain.
apply (IH (S kd) (Z.of_nat (S k) + -1) (off + 16) (dx ++ [x0; x1; x2; x3]) (dy ++ [y0; y1; y2; y3]) x0' x1' x2' x3' y0' y1' y2' y3' rx ry);
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
Hypothesis OBX : aobj bsegs m px (16 * n).
Hypothesis OBY : aobj bsegs m py (16 * n).
Hypothesis X4 : px mod 4 = 0.
Hypothesis Y4 : py mod 4 = 0.
Hypothesis XP : 0 < px.
Hypothesis YP : 0 < py.
Hypothesis LO : lo <= usp - 48.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Local Notation W := [(usp + -48, usp)].

Local Notation POST := (inner_prodB_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F usp lo xs ys m).

Lemma inner_prodB_walk : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) fc,
rw_cells bsegs m px (f32 xs) -> rw_cells bsegs m py (f32 ys) -> frm0 fc ->
stk bsegs m lo usp -> (px + 16 * n <= lo \/ usp <= px) -> (py + 16 * n <= lo \/ usp <= py) ->
client_constsB m -> mem_inv bsegs m ->
evt bsegs POST
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 px) (Z_to_bv 64 py) (Z_to_bv 64 (4 * n)) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 B_inner_prod) fc None m (seg_rom bsegs)).
Proof.
intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc X Y FRM ST XLO YLO (G1 & G2 & _) MI.
unfold B_inner_prod, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX.
pose proof (rw_cells_bound _ _ _ _ Y) as BY; rewrite cells_size_f32 in BY.
pose proof ST as (STa & STb & _).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh W) by (cbn; unfold SH_LO, SH_HI; lia).
destruct xs as [|x0 [|x1 [|x2 [|x3 rx]]]]; try (cbn [length] in LX; lia).
destruct ys as [|y0 [|y1 [|y2 [|y3 ry]]]]; try (cbn [length] in LY; lia).
cbn [length] in LX, LY, BX, BY.
carve_frame 48%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xa9d20.
rewrite ?signed_small64 by lia.
replace (Z.shiftr (4 * n) 2) with n by (rewrite Z.shiftr_div_pow2 by lia; change (2^2) with 4; rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
rewrite (Z.mod_small n) by lia. rewrite swrap32_small by lia.
replace (Z.land px 3) with 0 by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2^2) with 4; lia).
replace (Z.land py 3) with 0 by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2^2) with 4; lia).
change (Z_to_bv 64 18446744069414584320) with fzero_s.
replace (SHB + Z.shiftr px 3) with (Z.shiftr (px + 0) 3 + SHB) by (rewrite Z.add_0_r; lia).
replace (SHB + Z.shiftr py 3) with (Z.shiftr (py + 0) 3 + SHB) by (rewrite Z.add_0_r; lia).
pose proof X as XF. pose proof Y as YF.
replace px with (px + 0) in XF, X by lia. replace py with (py + 0) in YF, Y by lia.
chunk_split_f32 XF at 4%nat as X1. chunk_split_f32 YF at 4%nat as Y1. clear XF YF.
apply (ipB_block n px py usp gp tp s5 s6 s7 s8 s9 s10 s11 m OBX OBY X4 Y4 XP YP _ 0 (n + -1) x0 x1 x2 x3 y0 y1 y2 y3); [lia | lia | reflexivity | lia | exact MU | exact OF | exact X1 | exact Y1 | ].
intros a2' a5' z2' z4'. norm_fchain.
eapply (ipB_loop _ _ n px py usp lo ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m N1) with (k := Z.to_nat (n - 1)) (kd := 0%nat) (dx := []) (dy := []);
try eassumption;
try assumption; try reflexivity; try (cbn [length] in *; lia).
- cbn [app]. exact X.
- cbn [app]. exact Y.
Qed.
End E.
