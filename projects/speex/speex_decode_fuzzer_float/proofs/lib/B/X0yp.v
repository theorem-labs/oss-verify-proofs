(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg X1df X1ck X1co.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05q X05l.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b X0z5 X0yq X0ym.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac tlia ::= tlia_one.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Notation mem := (word -> option byte).

Lemma swrap32_mod64_add : forall x k, -2^31 <= x + k < 2^31 ->
bv_swrap 32 (x mod 18446744073709551616 + k) = x + k.
Proof.
intros x k H. rewrite <- (swrap32_small (x + k)) by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 / 2)%Z with 2147483648%Z. f_equal.
rewrite (Z.mod_eq x 18446744073709551616) by lia.
replace (x - 18446744073709551616 * (x / 18446744073709551616) + k + 2147483648)
with ((x + k + 2147483648) + (- 4294967296 * (x / 18446744073709551616)) * 4294967296) by lia.
rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma addr_shift2 : forall base x r, r = base + 4 * x ->
Z_to_bv 64 (base + Z.shiftl (x mod 18446744073709551616) 2) = Z_to_bv 64 r.
Proof.
intros base x r ->. apply Z_to_bv_eqm. rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
rewrite (Z.mod_eq x 18446744073709551616) by lia.
replace (base + (x - 18446744073709551616 * (x / 18446744073709551616)) * 4)
with ((base + 4 * x) + (- 4 * (x / 18446744073709551616)) * 18446744073709551616) by lia.
change (2^64) with 18446744073709551616. rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma ptr_sgn_guard : forall A y Y, Y = A + 4 * y ->
Z.lxor (Z.lxor (Z.b2z (Y <? A)) (Z.b2z (y + 9223372036854775808 <? 9223372036854775808))) 1 = 1.
Proof.
intros A y Y ->. destruct (A + 4 * y <? A) eqn:H1; destruct (y + 9223372036854775808 <? 9223372036854775808) eqn:H2;
try apply Z.ltb_lt in H1; try apply Z.ltb_lt in H2; try apply Z.ltb_ge in H1; try apply Z.ltb_ge in H2; try lia; reflexivity.
Qed.

Lemma swrap32_sub_mod64 : forall a x, bv_swrap 32 (a - x mod 18446744073709551616) = bv_swrap 32 (a - x).
Proof.
intros a x. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 / 2)%Z with 2147483648%Z. f_equal.
rewrite (Z.mod_eq x 18446744073709551616) by lia.
replace (a - (x - 18446744073709551616 * (x / 18446744073709551616)) + 2147483648)
with ((a - x + 2147483648) + (4294967296 * (x / 18446744073709551616)) * 4294967296) by lia.
rewrite Z_mod_plus_full. reflexivity.
Qed.
Lemma zbv_sub_mod : forall a x, Z_to_bv 64 (a - x mod 18446744073709551616) = Z_to_bv 64 (a - x).
Proof.
intros a x. apply Z_to_bv_eqm. change (2^64) with 18446744073709551616.
rewrite Zminus_mod_idemp_r. reflexivity.
Qed.

Lemma f32_snoc l x : f32 l ++ [C4 x] = f32 (l ++ [x]).
Proof. rewrite f32_app, f32_cons, f32_nil. reflexivity. Qed.

Lemma eb_win7 : forall m EB (eb : list word) (n : Z), rw_cells bsegs m EB (f32 eb) -> length eb = 500%nat ->
0 <= n -> n + 7 <= 500 ->
exists y0 y1 y2 y3 y4 y5 y6, rw_cells bsegs m (EB + 4 * n) (f32 [y0; y1; y2; y3; y4; y5; y6]).
Proof.
intros m EB eb n X L Hn Hn2.
pose proof (rw_cells_f32_mid bsegs m EB eb (Z.to_nat n) 7 X ltac:(lia)) as W.
rewrite Z2Nat.id in W by lia.
remember (firstn 7 (skipn (Z.to_nat n) eb)) as w eqn:Hw.
assert (Lw : length w = 7%nat) by (subst w; rewrite firstn_length_le; [reflexivity|]; rewrite skipn_length; lia).
destruct w as [|y0 [|y1 [|y2 [|y3 [|y4 [|y5 [|y6 [|? ?]]]]]]]]; try (cbn in Lw; lia).
exists y0, y1, y2, y3, y4, y5, y6. exact W.
Qed.
Lemma eb_win1 : forall m EB (eb : list word) (n : Z), rw_cells bsegs m EB (f32 eb) -> length eb = 500%nat ->
0 <= n -> n + 1 <= 500 ->
exists y0, rw_cells bsegs m (EB + 4 * n) (f32 [y0]).
Proof.
intros m EB eb n X L Hn Hn2.
pose proof (rw_cells_f32_mid bsegs m EB eb (Z.to_nat n) 1 X ltac:(lia)) as W.
rewrite Z2Nat.id in W by lia.
remember (firstn 1 (skipn (Z.to_nat n) eb)) as w eqn:Hw.
assert (Lw : length w = 1%nat) by (subst w; rewrite firstn_length_le; [reflexivity|]; rewrite skipn_length; lia).
destruct w as [|y0 [|? ?]]; try (cbn in Lw; lia).
exists y0. exact W.
Qed.

Section T.

Variables (m : mem) (EB X fb mi : Z).
Variables ra sp gp tp t0 s0 s1 a2 a3 s2 s4 s6 s7 s11 t6 : word.
Hypothesis OBE : aobj bsegs m EB 2000.
Hypothesis OBF : aobj bsegs m fb 28.
Hypothesis E4 : EB mod 4 = 0.
Hypothesis FB4 : fb mod 4 = 0.
Hypothesis EB0 : 0 < EB.
Hypothesis Hmi : 1 <= mi <= 3.
Hypothesis Hfb : fb = SHIFT_FILT + 28 * (mi - 1).

Definition tap_post : machine_state -> Prop :=
fun ms' => exists (s3 s5 s10 a0 a1 : word) (G' : bvmap 5 word) (fc' : bv 32),
ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 0) (Z_to_bv 64 SHIFT_FILT) s0 s1 a0 a1 a2 a3 (Z_to_bv 64 mi) (Z_to_bv 64 3) (Z_to_bv 64 28) (Z_to_bv 64 0)
s2 s3 s4 s5 s6 s7 (Z_to_bv 64 SHB) (Z_to_bv 64 1) s10 s11 (Z_to_bv 64 (28 * (mi - 1))) (Z_to_bv 64 fb) (Z_to_bv 64 (18446744073709551615 - fb)) t6)
G' (Z_to_bv 64 0xa9ab0) fc' None m (seg_rom bsegs)
/\ frm0 fc'.
Lemma tapk : forall (k : nat) (xrest frest : list word) (x n kk : Z) (xw fw s3 a0 a1 : word) (G : bvmap 5 word) (fc : bv 32),
s2 = Z_to_bv 64 x -> s4 = Z_to_bv 64 X -> X = EB + 4 * (n - x - kk + 3) -> -2^20 <= x <= 2^20 -> EB <= X <= EB + 2000 ->
length xrest = k -> length frest = k ->
0 <= n -> n + 1 + Z.of_nat k <= 500 -> 0 <= kk -> kk + 1 + Z.of_nat k = 7 ->
frm0 fc -> mem_inv bsegs m ->
rw_cells bsegs m (EB + 4 * n) (f32 (xw :: xrest)) -> ro_cells bsegs m (fb + 4 * kk) (f32 (fw :: frest)) ->
evt bsegs tap_post
(MS (mkR ra sp gp tp t0 (Z_to_bv 64 0) (Z_to_bv 64 SHIFT_FILT) s0 s1 a0 a1 a2 a3 (Z_to_bv 64 mi) (Z_to_bv 64 3) (Z_to_bv 64 28) (Z_to_bv 64 0)
s2 s3 s4 (Z_to_bv 64 kk) s6 s7 (Z_to_bv 64 SHB) (Z_to_bv 64 1) (Z_to_bv 64 (4 * kk)) s11 (Z_to_bv 64 (28 * (mi - 1))) (Z_to_bv 64 fb) (Z_to_bv 64 (18446744073709551615 - fb)) t6)
G (Z_to_bv 64 0xa999c) fc None m (seg_rom bsegs)).
Proof using OBE OBF E4 FB4 EB0 Hmi Hfb.
pose proof OBE as (OE0 & OE1 & _). pose proof OBF as (OF0 & OF1 & _). unfold APP_TOP in *. unfold tap_post, SHIFT_FILT in *.
induction k as [|k IH]; intros xrest frest x n kk xw fw s3 a0 a1 G fc -> -> HX Hx HXr LX LF Hn0 Hn Hkk0 Hkk FRM MI XW RO;
pose proof (rw_cells_bound _ _ _ _ XW) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (ro_cells_bound _ _ _ _ RO) as BR; rewrite cells_size_f32 in BR; cbn [length] in BR.
- destruct xrest; [|cbn in LX; lia]. destruct frest; [|cbn in LF; lia]. rewrite f32_cons, f32_nil in XW. rewrite f32_cons, f32_nil in RO.
ato 0xa99a4.
rewrite swrap32_mod64_add by lia.
bato 0xa99b0. rewrite !swrap32_mod64_add by lia. astep. sh_if.
ato 0xa99bc.
rewrite (addr_shift2 X (x + kk + -3) (EB + 4 * n)) by lia.
bato 0xa99d4.
rewrite ?(Z.mod_small X) by lia. rewrite (lxor_sign_mod (x + kk + -3)) by lia. rewrite (ptr_sgn_guard X (x + kk + -3) (EB + 4 * n)) by lia.
assert (A4 : (EB + 4 * n) mod 4 = 0) by (clear - E4; Z.div_mod_to_equations; lia).
bato 0xa99f0. astep. chk_merge OBE 4.
bato 0xa9a18.
astep. chk_merge OBF 4.
bato 0xa9a2c. replace (4 * kk + 4) with 28 by lia. astep. astep.
apply evt_done. do 7 eexists. split; [reflexivity| assumption].
- destruct xrest as [|xw' xrest]; [cbn in LX; lia|]. destruct frest as [|fw' frest]; [cbn in LF; lia|].
cbn [length] in LX, LF, BX, BR. rewrite !f32_cons in XW. rewrite !f32_cons in RO.
ato 0xa99a4. rewrite swrap32_mod64_add by lia.
bato 0xa99b0. rewrite !swrap32_mod64_add by lia. astep. sh_if.
ato 0xa99bc.
rewrite (addr_shift2 X (x + kk + -3) (EB + 4 * n)) by lia.
bato 0xa99d4.
rewrite ?(Z.mod_small X) by lia. rewrite (lxor_sign_mod (x + kk + -3)) by lia. rewrite (ptr_sgn_guard X (x + kk + -3) (EB + 4 * n)) by lia.
assert (A4 : (EB + 4 * n) mod 4 = 0) by (clear - E4; Z.div_mod_to_equations; lia).
bato 0xa99f0. astep. chk_merge OBE 4.
bato 0xa9a18. astep. chk_merge OBF 4.
bato 0xa9a2c. rewrite ?swrap32_small by lia. astep. sh_if.
rewrite <- !f32_cons in XW. rewrite <- !f32_cons in RO.
apply rw_f32_uncons in XW. apply ro_f32_uncons in RO.
replace (EB + 4 * n + 4) with (EB + 4 * (n + 1)) in * by lia. replace (fb + 4 * kk + 4) with (fb + 4 * (kk + 1)) in * by lia.
replace (4 * kk + 4) with (4 * (kk + 1)) by lia.
eapply (IH xrest frest x (n + 1) (kk + 1) xw' fw'); [reflexivity | reflexivity | lia | lia | lia | lia | lia | lia | lia | lia | lia | assumption | exact MI | exact XW | exact RO].
Qed.
End T.
Section D.
Variables (EB eoff p IP mi mj D fb q : Z) (eb : list word).
Variables rav spv gp tp s0v s6v s7v s11v t3w t4w t5w : word.
Hypothesis LEB : length eb = 500%nat.
Hypothesis R1 : 0 <= eoff - p - 6.
Hypothesis R2 : eoff - p <= 414.
Hypothesis R3 : eoff + 80 <= 500.
Hypothesis R4 : 0 <= eoff.
Hypothesis E4 : EB mod 4 = 0.
Hypothesis EB0 : 0 < EB.
Hypothesis IP4 : IP mod 4 = 0.
Hypothesis Hmi : 0 <= mi <= 3.
Hypothesis Hmj : 0 <= mj <= 6.
Hypothesis HD : D = p - mj + 3.
Hypothesis HFB : 1 <= mi -> fb = SHIFT_FILT + 28 * (mi - 1) /\ t3w = Z_to_bv 64 (28 * (mi - 1)) /\ t4w = Z_to_bv 64 fb /\ t5w = Z_to_bv 64 (18446744073709551615 - fb).
Hypothesis SEP : IP + 320 <= EB \/ EB + 2000 <= IP.
Hypothesis IPI : IMG_TOP_B <= IP.
Hypothesis Q0 : 0 <= q.
Hypothesis Q63 : q + 192 < 2^63.
Hypothesis QIP : q + 192 <= IP.

Definition RD (i : Z) (a0v a1v s2v s3v s5v s10v : word) : bvmap 5 word :=
mkR rav spv gp tp (Z_to_bv 64 D) (Z_to_bv 64 0) (Z_to_bv 64 SHIFT_FILT) s0v (Z_to_bv 64 q) a0v a1v (Z_to_bv 64 i) (Z_to_bv 64 (18446744073709551615 - IP))
(Z_to_bv 64 mi) (Z_to_bv 64 3) (Z_to_bv 64 28) (Z_to_bv 64 0)
s2v s3v (Z_to_bv 64 (EB + 4 * eoff)) s5v s6v s7v (Z_to_bv 64 SHB) (Z_to_bv 64 1) s10v s11v t3w t4w t5w (Z_to_bv 64 80).

Definition floop_post (mI : mem) : machine_state -> Prop :=
fun ms' => exists a0' a1' s2' s3' s5' s10' F' fc' m' (ip' : list word),
ms' = MS (RD 80 a0' a1' s2' s3' s5' s10') F' (Z_to_bv 64 0xa9b10) fc' None m' (seg_rom bsegs)
/\ munch [(IP, IP + 320)] mI m' /\ wmono bsegs mI m' /\ mem_inv bsegs m'
/\ frm0 fc'
/\ length ip' = 80%nat /\ rw_cells bsegs m' IP (f32 ip').

Ltac arms K M0 M1 i mI mc OBE OBT OF MU XEB MI FRM :=
astep; destruct (Z_le_gt_dec mi 0) as [M0|M1];
[ sh_if; bato 0xa9a64;
rewrite swrap32_sub_mod64, swrap32_small, zbv_sub_mod by lia;
bato 0xa9a70; rewrite !swrap32_mod64_add by lia; rewrite !Z.add_0_r;
ato 0xa9a74; rewrite (addr_shift2 (EB + 4 * eoff) (i - D) (EB + 4 * (eoff + i - D))) by lia;
bato 0xa9a8c;
rewrite (lxor_sign_mod (i - D)) by lia; rewrite (ptr_sgn_guard (EB + 4 * eoff) (i - D) (EB + 4 * (eoff + i - D))) by lia;
let A4 := fresh "A4" in assert (A4 : (EB + 4 * (eoff + i - D)) mod 4 = 0) by (clear - E4; Z.div_mod_to_equations; lia);
let y0 := fresh "y0" in let WIN := fresh "WIN" in
destruct (eb_win1 mc EB eb (eoff + i - D) XEB LEB ltac:(lia) ltac:(lia)) as (y0 & WIN); rewrite f32_cons, f32_nil in WIN;
bato 0xa9aa8; astep; chk_merge OBE 4;
bato 0xa9ab0; clear WIN A4; apply K; assumption
| sh_if; bato 0xa9980;
rewrite zbv_sub_mod, swrap32_sub_mod64, swrap32_small by lia;
bato 0xa999c; rewrite !swrap32_mod64_add by lia; rewrite !Z.add_0_r;
let Hfb := fresh "Hfb" in let E3 := fresh "E3" in let E4' := fresh "E4'" in let E5 := fresh "E5" in
destruct (HFB ltac:(lia)) as (Hfb & E3 & E4' & E5); rewrite E3, E4', E5; unfold RD in K; rewrite E3, E4', E5 in K;
let y0 := fresh "y0" in let y1 := fresh "y1" in let y2 := fresh "y2" in let y3 := fresh "y3" in let y4 := fresh "y4" in let y5 := fresh "y5" in let y6 := fresh "y6" in
let WIN := fresh "WIN" in
destruct (eb_win7 mc EB eb (eoff + i - D - 3) XEB LEB ltac:(lia) ltac:(lia)) as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & WIN);
let g0 := fresh "g0" in let g1 := fresh "g1" in let g2 := fresh "g2" in let g3 := fresh "g3" in let g4 := fresh "g4" in let g5 := fresh "g5" in let g6 := fresh "g6" in
let ROW := fresh "ROW" in
destruct (shift_filt_row mc (mi - 1) MI ltac:(lia)) as (g0 & g1 & g2 & g3 & g4 & g5 & g6 & ROW);
rewrite <- Hfb in ROW; replace fb with (fb + 4 * 0) in ROW by lia;
lazymatch goal with |- evt _ _ (MS _ ?G0 _ ?fc0 _ _ _) =>
eapply evt_cut; [eapply (tapk mc EB (EB + 4 * eoff) fb mi) with (k := 6%nat) (xrest := [y1; y2; y3; y4; y5; y6]) (frest := [g1; g2; g3; g4; g5; g6])
(x := i - D) (n := eoff + i - D - 3) (kk := 0) (G := G0) (fc := fc0);
[ exact (aobj_munch bsegs _ mI mc EB 2000 OBE MU (shfree_of_aobj bsegs _ mI EB 2000 OF OBE))
| apply (aobj_sub bsegs mc SHIFT_FILT 84); [exact (aobj_munch bsegs _ mI mc SHIFT_FILT 84 OBT MU (shfree_of_aobj bsegs _ mI SHIFT_FILT 84 OF OBT)) | rewrite Hfb; unfold SHIFT_FILT; lia | rewrite Hfb; unfold SHIFT_FILT; lia]
| exact E4 | rewrite Hfb; unfold SHIFT_FILT; clear - Hmi; Z.div_mod_to_equations; lia | exact EB0 | lia | exact Hfb
| reflexivity | reflexivity | lia | lia | lia | reflexivity | reflexivity | lia | cbn; lia | lia | reflexivity | exact FRM | exact MI | exact WIN | exact ROW ] | ] end;
clear WIN ROW; let ms' := fresh "ms" in intros ms' (?s3' & ?s5' & ?s10' & ?a0' & ?a1' & ?G' & ?fc' & -> & ?FRM');
apply K; assumption ].

Lemma floop : forall (mI : mem) (rest done : list word) (cw : word) (i : Z) (a0v a1v s2v s3v s5v s10v : word) F1 fc mc,
i = Z.of_nat (length done) -> i + 1 + Z.of_nat (length rest) = 80 ->
aobj bsegs mI EB 2000 -> aobj bsegs mI IP 320 -> aobj bsegs mI SHIFT_FILT 84 -> offsh [(IP, IP + 320)] ->
frm0 fc -> mem_inv bsegs mc -> munch [(IP, IP + 320)] mI mc -> wmono bsegs mI mc ->
rw_cells bsegs mc EB (f32 eb) -> rw_cells bsegs mc IP (f32 done) -> rw_cells bsegs mc (IP + 4 * i) (f32 (cw :: rest)) ->
rw_cells bsegs mc (q + 56) [C8 (Z_to_bv 64 IP)] ->
evt bsegs (floop_post mI)
(MS (RD i a0v a1v s2v s3v s5v s10v) F1 (Z_to_bv 64 0xa996c) fc None mc (seg_rom bsegs)).
Proof using LEB R1 R2 R3 R4 E4 EB0 IP4 Hmi Hmj HD HFB SEP IPI Q0 Q63 QIP.
intros mI rest.
induction rest as [|cw' rest IH]; intros done cw i a0v a1v s2v s3v s5v s10v F1 fc mc Hi HN OBE OBI OBT OF FRM MI MU WM XEB XD XC SL;
pose proof OBE as (OE0 & OE1 & _); pose proof OBI as (OI0 & OI1 & _); unfold APP_TOP in *;
pose proof IPI as IPI'; unfold IMG_TOP_B in IPI';
pose proof (rw_cells_bound _ _ _ _ XEB) as BEB; rewrite cells_size_f32, LEB in BEB;
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
unfold RD; rewrite !f32_cons in XC.
-
cbn [length] in HN. rewrite f32_nil in XC.
assert (K : forall (a0' a1' s2' s3' s5' s10' : word) (F2 : bvmap 5 word) fc2, frm0 fc2 ->
evt bsegs (floop_post mI) (MS (RD i a0' a1' s2' s3' s5' s10') F2 (Z_to_bv 64 0xa9ab0) fc2 None mc (seg_rom bsegs))).
{ intros a0' a1' s2' s3' s5' s10' F2 fc2 FRM2. unfold RD.
assert (I4 : (IP + 4 * i) mod 4 = 0) by (clear - IP4; Z.div_mod_to_equations; lia).
bato 0xa9ac0. replace (i * 4) with (4 * i) by lia.
bato 0xa9ad4. astep. chk_merge OBI 4.
bato 0xa9ae0. rewrite swrap32_small by lia. replace (i + 1) with 80 by lia.
bato 0xa9b10.
chunk_snoc XD XC. rewrite f32_snoc in XD.
unfold floop_post, RD. finish; [ | exact XD ].
rewrite length_app. cbn [length]. lia. }
arms K M0 M1 i mI mc OBE OBT OF MU XEB MI FRM.
-
cbn [length] in HN, BC.
assert (K : forall (a0' a1' s2' s3' s5' s10' : word) (F2 : bvmap 5 word) fc2, frm0 fc2 ->
evt bsegs (floop_post mI) (MS (RD i a0' a1' s2' s3' s5' s10') F2 (Z_to_bv 64 0xa9ab0) fc2 None mc (seg_rom bsegs))).
{ intros a0' a1' s2' s3' s5' s10' F2 fc2 FRM2. unfold RD.
assert (I4 : (IP + 4 * i) mod 4 = 0) by (clear - IP4; Z.div_mod_to_equations; lia).
bato 0xa9ac0. replace (i * 4) with (4 * i) by lia.
bato 0xa9ad4. astep. chk_merge OBI 4.
bato 0xa9ae0. rewrite swrap32_small by lia. astep. sh_if.
chunk_uncons XC as X1. chunk_snoc XD X1. rewrite f32_snoc in XD. rewrite <- ?f32_cons in XC.
replace (IP + 4 * i + 4) with (IP + 4 * (i + 1)) in * by lia.
eapply (IH _ cw' (i + 1)); try eassumption.
all: try (rewrite length_app; cbn [length] in *; lia).
all: try (cbn [length] in *; lia). }
arms K M0 M1 i mI mc OBE OBT OF MU XEB MI FRM.
Qed.
End D.
