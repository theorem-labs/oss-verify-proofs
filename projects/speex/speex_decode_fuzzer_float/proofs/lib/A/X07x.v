(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg X1df X1ck X1co.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05l X07u.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac tlia ::= tlia_one.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Notation mem := (word -> option byte).

Section T.

Variables (m : mem) (EB fb : Z).
Variables ra sp gp tp t0 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t6 : word.
Hypothesis OBE : aobj asegs m EB 2000.
Hypothesis OBF : aobj asegs m fb 28.
Hypothesis E4 : EB mod 4 = 0.
Hypothesis FB4 : fb mod 4 = 0.

Definition tap_post : machine_state -> Prop :=
fun ms' => exists (t1 t2 a0 a1 t3 t4 t5 : word) (G' : bvmap 5 word) (fc' : bv 32),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 SHB) s10 s11 t3 t4 t5 t6)
G' (Z_to_bv 64 0xa5d3c) fc' None m (seg_rom asegs)
/\ frm0 fc'.

Lemma tapk : forall (k : nat) (xrest frest : list word) (n kf xa fa : Z) (xw fw t4 t5 : word) (G : bvmap 5 word) (fc : bv 32),
xa = EB + 4 * n -> fa = fb + 4 * kf -> length xrest = k -> length frest = k ->
0 <= n -> n + 1 + Z.of_nat k <= 500 -> 0 <= kf -> kf + 1 + Z.of_nat k <= 7 ->
frm0 fc -> mem_inv asegs m ->
rw_cells asegs m (EB + 4 * n) (f32 (xw :: xrest)) -> ro_cells asegs m (fb + 4 * kf) (f32 (fw :: frest)) ->
evt asegs tap_post
(MS (mkR ra sp gp tp t0 (Z_to_bv 64 xa) (Z_to_bv 64 (1 + Z.of_nat k)) s0 s1 (Z_to_bv 64 xa) (Z_to_bv 64 fa)
a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 SHB) s10 s11 (Z_to_bv 64 fa) t4 t5 t6)
G (Z_to_bv 64 0xa5cb4) fc None m (seg_rom asegs)).
Proof using OBE OBF E4 FB4.
pose proof OBE as (OE0 & OE1 & _). pose proof OBF as (OF0 & OF1 & _). unfold APP_TOP in *.
induction k as [|k IH]; intros xrest frest n kf xa fa xw fw t4 t5 G fc -> -> LX LF Hn0 Hn Hkf0 Hkf FRM MI XW RO;
pose proof (rw_cells_bound _ _ _ _ XW) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (ro_cells_bound _ _ _ _ RO) as BR; rewrite cells_size_f32 in BR; cbn [length] in BR.
- destruct xrest; [|cbn in LX; lia]. destruct frest; [|cbn in LF; lia]. rewrite f32_cons, f32_nil in XW. rewrite f32_cons, f32_nil in RO.
do 4 astep. chk_merge OBE 4.
ato 0xa5cd4. astep. chk_merge OBF 4.
ato 0xa5cf4. astep. sh_if. astep.
apply evt_done; unfold tap_post. do 9 eexists. split; [reflexivity| assumption].
- destruct xrest as [|xw' xrest]; [cbn in LX; lia|]. destruct frest as [|fw' frest]; [cbn in LF; lia|].
cbn [length] in LX, LF, BX, BR. rewrite !f32_cons in XW. rewrite !f32_cons in RO.
do 4 astep. chk_merge OBE 4.
ato 0xa5cd4. astep. chk_merge OBF 4.
ato 0xa5cf4. astep. sh_if.
rewrite <- !f32_cons in XW. rewrite <- !f32_cons in RO.
apply rw_f32_uncons in XW. apply ro_f32_uncons in RO.
replace (EB + 4 * n + 4) with (EB + 4 * (n + 1)) in * by lia. replace (fb + 4 * kf + 4) with (fb + 4 * (kf + 1)) in * by lia.
replace (1 + Z.of_nat (S k) + -1) with (1 + Z.of_nat k) by lia.
eapply (IH xrest frest (n + 1) (kf + 1) _ _ xw' fw'); [reflexivity | reflexivity | lia | lia | lia | lia | lia | lia | assumption | exact MI | exact XW | exact RO].
Qed.
End T.

Lemma f32_snoc l x : f32 l ++ [C4 x] = f32 (l ++ [x]).
Proof. rewrite f32_app, f32_cons, f32_nil. reflexivity. Qed.

Lemma eb_win7 : forall m EB (eb : list word) (n : Z), rw_cells asegs m EB (f32 eb) -> length eb = 500%nat ->
0 <= n -> n + 7 <= 500 ->
exists y0 y1 y2 y3 y4 y5 y6, rw_cells asegs m (EB + 4 * n) (f32 [y0; y1; y2; y3; y4; y5; y6]).
Proof.
intros m EB eb n X L Hn Hn2.
pose proof (rw_cells_f32_mid asegs m EB eb (Z.to_nat n) 7 X ltac:(lia)) as W.
rewrite Z2Nat.id in W by lia.
remember (firstn 7 (skipn (Z.to_nat n) eb)) as w eqn:Hw.
assert (Lw : length w = 7%nat) by (subst w; rewrite firstn_length_le; [reflexivity|]; rewrite skipn_length; lia).
destruct w as [|y0 [|y1 [|y2 [|y3 [|y4 [|y5 [|y6 [|? ?]]]]]]]]; try (cbn in Lw; lia).
exists y0, y1, y2, y3, y4, y5, y6. exact W.
Qed.
Lemma eb_win1 : forall m EB (eb : list word) (n : Z), rw_cells asegs m EB (f32 eb) -> length eb = 500%nat ->
0 <= n -> n + 1 <= 500 ->
exists y0, rw_cells asegs m (EB + 4 * n) (f32 [y0]).
Proof.
intros m EB eb n X L Hn Hn2.
pose proof (rw_cells_f32_mid asegs m EB eb (Z.to_nat n) 1 X ltac:(lia)) as W.
rewrite Z2Nat.id in W by lia.
remember (firstn 1 (skipn (Z.to_nat n) eb)) as w eqn:Hw.
assert (Lw : length w = 1%nat) by (subst w; rewrite firstn_length_le; [reflexivity|]; rewrite skipn_length; lia).
destruct w as [|y0 [|? ?]]; try (cbn in Lw; lia).
exists y0. exact W.
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

Section D.
Variables (EB eoff p IP mi mj d a6z : Z) (eb : list word).
Variables rav spv gp tp s0v s1v s2v s5v s6v s7v s8v s10v s11v t6v : word.
Hypothesis LEB : length eb = 500%nat.
Hypothesis R1 : 0 <= eoff - p - 6.
Hypothesis R2 : eoff - p <= 414.
Hypothesis R3 : eoff + 80 <= 500.
Hypothesis R4 : 0 <= eoff.
Hypothesis E4 : EB mod 4 = 0.
Hypothesis IP4 : IP mod 4 = 0.
Hypothesis Hmi : 0 <= mi <= 3.
Hypothesis Hmj : 0 <= mj <= 6.
Hypothesis Hd : d = mj - p - 3.
Hypothesis HA6 : 1 <= mi -> a6z = SHIFT_FILT + 28 * (mi - 1).
Hypothesis SEP : IP + 320 <= EB \/ EB + 2000 <= IP.
Hypothesis IPI : IMG_TOP <= IP.

Definition RD (i di : Z) (t1v t2v a0v a1v t3v t4v t5v : word) : bvmap 5 word :=
mkR rav spv gp tp (Z_to_bv 64 di) t1v t2v s0v s1v a0v a1v (Z_to_bv 64 mi) (Z_to_bv 64 i) (Z_to_bv 64 (EB + 4 * eoff + -12)) (Z_to_bv 64 d) (Z_to_bv 64 a6z) (Z_to_bv 64 80)
s2v (Z_to_bv 64 IP) (Z_to_bv 64 (EB + 4 * eoff)) s5v s6v s7v s8v (Z_to_bv 64 SHB) s10v s11v t3v t4v t5v t6v.

Definition floop_post (mI : mem) : machine_state -> Prop :=
fun ms' => exists t1' t2' a0' a1' t3' t4' t5' F' fc' m' (ip' : list word),
ms' = MS (RD 80 (d + 80) t1' t2' a0' a1' t3' t4' t5') F' (Z_to_bv 64 0xa5d88) fc' None m' (seg_rom asegs)
/\ munch [(IP, IP + 320)] mI m' /\ wmono asegs mI m' /\ mem_inv asegs m'
/\ frm0 fc'
/\ length ip' = 80%nat /\ rw_cells asegs m' IP (f32 ip').

Ltac arms K M0 M1 i di mI mc OBE OBT OF MU XEB MI FRM :=
astep; destruct (Z_le_gt_dec mi 0) as [M0|M1];
[ sh_if; do 3 astep;
rewrite swrap32_mod64_add by lia; rewrite (addr_shift2 (EB + 4 * eoff) (d + i) (EB + 4 * (eoff + d + i))) by lia;
destruct (eb_win1 mc EB eb (eoff + d + i) XEB LEB ltac:(lia) ltac:(lia)) as (y0 & WIN); rewrite f32_cons, f32_nil in WIN;
ato 0xa5d34; astep; chk_merge OBE 4;
ato 0xa5d3c; clear WIN; apply K; assumption
| sh_if; do 7 astep;
rewrite (addr_shift2 (EB + 4 * eoff + -12) di (EB + 4 * (eoff + d + i - 3))) by lia;
destruct (eb_win7 mc EB eb (eoff + d + i - 3) XEB LEB ltac:(lia) ltac:(lia)) as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & WIN);
destruct (shift_filt_row mc (mi - 1) MI ltac:(lia)) as (g0 & g1 & g2 & g3 & g4 & g5 & g6 & ROW);
rewrite <- (HA6 ltac:(lia)) in ROW; replace a6z with (a6z + 4 * 0) in ROW by lia;
lazymatch goal with |- evt _ _ (MS _ ?G0 _ ?fc0 _ _ _) =>
eapply evt_cut; [eapply (tapk mc EB a6z) with (k := 6%nat) (xrest := [y1; y2; y3; y4; y5; y6]) (frest := [g1; g2; g3; g4; g5; g6]) (n := eoff + d + i - 3) (kf := 0) (G := G0) (fc := fc0);
[ exact (aobj_munch asegs _ mI mc EB 2000 OBE MU (shfree_of_aobj asegs _ mI EB 2000 OF OBE))
| apply (aobj_sub asegs mc SHIFT_FILT 84); [exact (aobj_munch asegs _ mI mc SHIFT_FILT 84 OBT MU (shfree_of_aobj asegs _ mI SHIFT_FILT 84 OF OBT)) | rewrite (HA6 ltac:(lia)); unfold SHIFT_FILT; lia | rewrite (HA6 ltac:(lia)); unfold SHIFT_FILT; lia]
| exact E4 | rewrite (HA6 ltac:(lia)); unfold SHIFT_FILT; clear - Hmi; Z.div_mod_to_equations; lia
| reflexivity | lia | reflexivity | reflexivity | lia | cbn; lia | lia | cbn; lia | exact FRM | exact MI | exact WIN | exact ROW ] | ] end;
clear WIN ROW; intros ms' (t1' & t2' & a0' & a1' & t3' & t4' & t5' & G' & fc' & -> & FRM');
apply K; exact FRM' ].

Lemma floop : forall (mI : mem) (rest done : list word) (cw : word) (i di : Z) (t1v t2v a0v a1v t3v t4v t5v : word) F1 fc mc,
i = Z.of_nat (length done) -> di = d + i -> i + 1 + Z.of_nat (length rest) = 80 ->
aobj asegs mI EB 2000 -> aobj asegs mI IP 320 -> aobj asegs mI SHIFT_FILT 84 -> offsh [(IP, IP + 320)] ->
frm0 fc -> mem_inv asegs mc -> munch [(IP, IP + 320)] mI mc -> wmono asegs mI mc ->
rw_cells asegs mc EB (f32 eb) -> rw_cells asegs mc IP (f32 done) -> rw_cells asegs mc (IP + 4 * i) (f32 (cw :: rest)) ->
evt asegs (floop_post mI)
(MS (RD i di t1v t2v a0v a1v t3v t4v t5v) F1 (Z_to_bv 64 0xa5c94) fc None mc (seg_rom asegs)).
Proof using LEB R1 R2 R3 R4 E4 IP4 Hmi Hmj Hd HA6 SEP IPI.
intros mI rest.
induction rest as [|cw' rest IH]; intros done cw i di t1v t2v a0v a1v t3v t4v t5v F1 fc mc Hi Hdi HN OBE OBI OBT OF FRM MI MU WM XEB XD XC;
pose proof OBE as (OE0 & OE1 & _); pose proof OBI as (OI0 & OI1 & _); unfold APP_TOP in *;
pose proof IPI as IPI'; unfold IMG_TOP in IPI';
pose proof (rw_cells_bound _ _ _ _ XEB) as BEB; rewrite cells_size_f32, LEB in BEB;
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
unfold RD; rewrite !f32_cons in XC.
-
cbn [length] in HN. rewrite f32_nil in XC.
assert (K : forall (t1' t2' a0' a1' t3' t4' t5' : word) (F2 : bvmap 5 word) fc2, frm0 fc2 ->
evt asegs (floop_post mI) (MS (RD i di t1' t2' a0' a1' t3' t4' t5') F2 (Z_to_bv 64 0xa5d3c) fc2 None mc (seg_rom asegs))).
{ intros t1' t2' a0' a1' t3' t4' t5' F2 fc2 FRM2. unfold RD.
do 2 astep. replace (IP + Z.shiftl i 2) with (IP + 4 * i) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
ato 0xa5d50. astep. chk_merge OBI 4.
ato 0xa5d60. rewrite swrap32_mod64_add by lia. astep. sh_if. astep.
chunk_snoc XD XC. rewrite f32_snoc in XD.
replace (di + 1) with (d + 80) by lia. replace (i + 1) with 80 by lia.
unfold floop_post, RD. finish; [ | exact XD ].
rewrite length_app. cbn [length]. lia. }
arms K M0 M1 i di mI mc OBE OBT OF MU XEB MI FRM.
-
cbn [length] in HN, BC.
assert (K : forall (t1' t2' a0' a1' t3' t4' t5' : word) (F2 : bvmap 5 word) fc2, frm0 fc2 ->
evt asegs (floop_post mI) (MS (RD i di t1' t2' a0' a1' t3' t4' t5') F2 (Z_to_bv 64 0xa5d3c) fc2 None mc (seg_rom asegs))).
{ intros t1' t2' a0' a1' t3' t4' t5' F2 fc2 FRM2. unfold RD.
do 2 astep. replace (IP + Z.shiftl i 2) with (IP + 4 * i) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
ato 0xa5d50. astep. chk_merge OBI 4.
ato 0xa5d60. rewrite swrap32_mod64_add by lia. astep. sh_if.
chunk_uncons XC as X1. chunk_snoc XD X1. rewrite f32_snoc in XD. rewrite <- ?f32_cons in XC.
replace (IP + 4 * i + 4) with (IP + 4 * (i + 1)) in * by lia.
eapply (IH _ cw' (i + 1) (di + 1)); try eassumption.
all: try (rewrite length_app; cbn [length] in *; lia).
all: try (cbn [length] in *; lia). }
arms K M0 M1 i di mI mc OBE OBT OF MU XEB MI FRM.
Qed.
End D.
