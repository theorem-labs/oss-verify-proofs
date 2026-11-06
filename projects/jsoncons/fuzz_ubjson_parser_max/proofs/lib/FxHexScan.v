(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimString PrimInt63.
From Stdlib Require Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanHexScan FxImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__FxHexScan () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "Corelib.Numbers.Cyclic.Int63.PrimInt63."; "Corelib.Numbers.Cyclic.Int63.Uint63Axioms."; "Corelib.Strings.PrimString."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanHexScan."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.FxHexScan.FXH."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.FxHexScan.FXH.Leaf."; "Stdlib.NArith.BinNat.N."; "Stdlib.ZArith.BinInt.Z."], [["1S"; "1bool"; "1nat"; "1true"; "2and"; "2eq"; "3N"; "3Z"; "3Zpos"; "3positive"; "4int"; "5of_Z"; "5to_Z"; "5wB"; "6string"; "7byte_ok"]; ["7scanN"; "9scanP"; "9scan_pow"; "8byte_zero"; "8leaf_ok"; "8leaf_zero"; "8scanF"; "8scanG"; "8zscanF"; ":add"; ":le"; ":lt"; ":of_nat"; ":pow"; ";add"; ";le"]; [";lt"; ";mul"; ";of_N"; ";of_nat"; ";pow"; "0base"; "0f"; "0i"; "0k"; "0leaf"; "0n"; "0p"; "0s"; "0w"; "0zs"]]).
Module FXH.
Local Notation "'φ' x" := (Uint63.to_Z x) (at level 0).
Local Open Scope Z_scope.
Section Leaf.
Variable leaf : int -> bool.
Fixpoint scan_pow (k : nat) (base w : int) : bool :=
match k with
| O => leaf base
| S k' => let h := PrimInt63.lsr w 1%uint63 in if scan_pow k' base h then scan_pow k' (PrimInt63.add base h) h else false
end.
Fixpoint scanP (p : positive) (k : nat) (base w : int) : bool :=
match p with
| xH => scan_pow k base w
| xO q => scanP q (S k) base (PrimInt63.add w w)
| xI q => if scan_pow k base w then scanP q (S k) (PrimInt63.add base w) (PrimInt63.add w w) else false
end.
Lemma wB63 : ltac2:(TCodec.tc2 tcn__FxHexScan "8'5'7&=&Q4+2+QO%3221%73651"). Proof. reflexivity. Qed.
Lemma pow2_pos : ltac2:(TCodec.tc2 tcn__FxHexScan ";'2&Q0z&Q4+2&Q3r1%211%5241%8271pRB:1"). Proof. intros. apply Z.pow_pos_nonneg; lia. Qed.
Lemma scan_pow_spec : ltac2:(TCodec.tc2 tcn__FxHexScan "QG'2&:'5'7&<r1%211&Q4+2&Q3r3%211%5241%;3:71&O&N%<16r4%911%<2;1%5241+QN%?2>1%9231'1&Br5%231:A(3%K3521'4r6%L11%C21L&Q0r7%K11%N2M1%G261%52Q21%:271vQ9&;r2%211%411%Q<3F1Bp071pR@Q=1p0D1p0K1p0Q61pRLQC1pR<QD1pRBQF1").
Proof.
induction k as [|k IH]; intros base w Hw Hb H i Hi; cbn [scan_pow] in H.
- change (2 ^ Z.of_nat 0) with 1 in Hi. assert (i = φ base) by lia. subst i. rewrite Uint63.of_to_Z. exact H.
- cbv zeta in H. pose proof (pow2_pos k) as Pk.
assert (P2 : 2 ^ Z.of_nat (S k) = 2 * 2 ^ Z.of_nat k) by (rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; reflexivity).
assert (Hh : φ (PrimInt63.lsr w 1%uint63) = 2 ^ Z.of_nat k).
{ rewrite Uint63.lsr_spec, Hw, P2. change (φ 1%uint63) with 1. change (2 ^ 1) with 2. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. }
pose proof (Uint63.to_Z_bounded base) as Bb.
assert (Ha : φ (PrimInt63.add base (PrimInt63.lsr w 1%uint63)) = φ base + 2 ^ Z.of_nat k).
{ rewrite Uint63.add_spec, Hh, wB63. apply Z.mod_small. lia. }
destruct (scan_pow k base (PrimInt63.lsr w 1%uint63)) eqn:E1; [|discriminate].
destruct (Z.lt_ge_cases i (φ base + 2 ^ Z.of_nat k)) as [L|G].
+ apply (IH base _ Hh ltac:(lia) E1). lia.
+ apply (IH _ _ Hh ltac:(rewrite Ha; lia) H). rewrite Ha. lia.
Qed.
Lemma scanP_spec : ltac2:(TCodec.tc2 tcn__FxHexScan "R0'9'2&:'5'7&<r1%211&Q4+2&Q3r3%211%5241%;3:71&O&N%<16&Q1(8r5%211r4%=11%@2?1%7241%:291+QN%D2C1%>231'1&Ar6%241=;F(3%Q03521'4%Q015%G21Q0&Q0r8%F11r7%Q111%Q42Q31%K241%N291%82Q91%<2:1vQ9&;r2%211%411%QC3H1Dp071pR@QD1p0F1p0M1p0Q=1pRLQJ1pR<QK1pRBQM1pRHQO1").
Proof.
induction p as [q IH|q IH|]; intros k base w Hw Hb H i Hi; cbn [scanP] in H; pose proof (pow2_pos k) as Pk;
assert (P2 : 2 ^ Z.of_nat (S k) = 2 * 2 ^ Z.of_nat k) by (rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; reflexivity);
pose proof (Uint63.to_Z_bounded base) as Bb.
- change (Z.pos q~1) with (2 * Z.pos q + 1) in *. pose proof (Z.mul_pos_pos _ _ (Pos2Z.is_pos q) Pk) as QX.
set (X := 2 ^ Z.of_nat k) in *.
destruct (scan_pow k base w) eqn:E1; [|discriminate].
assert (Hww : φ (PrimInt63.add w w) = 2 * X) by (rewrite Uint63.add_spec, Hw, wB63; rewrite Z.mod_small by lia; lia).
assert (Ha : φ (PrimInt63.add base w) = φ base + X) by (rewrite Uint63.add_spec, Hw, wB63; apply Z.mod_small; lia).
destruct (Z.lt_ge_cases i (φ base + X)) as [L|G].
+ apply (scan_pow_spec k base w Hw ltac:(fold X; lia) E1). fold X. lia.
+ apply (IH (S k) (PrimInt63.add base w) (PrimInt63.add w w) ltac:(rewrite P2; exact Hww) ltac:(rewrite Ha, P2; fold X; lia) H). rewrite Ha, P2. fold X. lia.
- change (Z.pos q~0) with (2 * Z.pos q) in *. pose proof (Z.mul_pos_pos _ _ (Pos2Z.is_pos q) Pk) as QX.
set (X := 2 ^ Z.of_nat k) in *. assert (QX1 : X <= Z.pos q * X) by (pose proof (Pos2Z.is_pos q); nia).
assert (Hww : φ (PrimInt63.add w w) = 2 * X) by (rewrite Uint63.add_spec, Hw, wB63; rewrite Z.mod_small by lia; lia).
apply (IH (S k) base (PrimInt63.add w w) ltac:(rewrite P2; exact Hww) ltac:(rewrite P2; fold X; lia) H). rewrite P2. fold X. lia.
- apply (scan_pow_spec k base w Hw ltac:(lia) H). lia.
Qed.
End Leaf.
Definition scanG (leaf : int -> bool) (base n : N) : bool :=
match n with
| N0 => true
| Npos p => match IMGF.z61 (Z.of_N base) with Some b => scanP leaf p 0 b 1%uint63 | None => false end
end.
Lemma scanG_spec : ltac2:(TCodec.tc2 tcn__FxHexScan "Q:&:'1p021'6&O&N&Q2r2%211r1%411%6231&Q4+2+QN%3221%<251'5&Gr4r3%3321>(3%63F21&K%12@6r7&;&Ir6%221G%I11%511%711%A3Q11<p0:1pR@Q11p0>1p0F1pRFQ41pR<Q51pRDQ71").
Proof.
intros leaf base n Hb H i Hi. destruct n as [|p]; [lia|]. cbn [scanG] in H.
destruct (IMGF.z61 (Z.of_N base)) as [b|] eqn:E; [|discriminate]. apply IMGF.z61_spec in E. destruct E as [E1 E2].
apply (scanP_spec leaf p 0 b 1%uint63); [reflexivity|change (2 ^ Z.of_nat 0) with 1; lia|exact H|]. change (2 ^ Z.of_nat 0) with 1. lia.
Qed.
Definition leaf_ok (s : PrimString.string) (o : int) : bool := match IMGF.hex_byte_atI s o with Some _ => true | None => false end.
Definition scanF (s : PrimString.string) (base n : N) : bool := scanG (leaf_ok s) base n.
Lemma leaf_ok_spec : ltac2:(TCodec.tc2 tcn__FxHexScan "N&>'6&Q0&Q2r1%211&Q4+2+QN%3221%8251'5'1&Dr3&;r2%>11%311%6251(3%:3921&?r4%221:%>3=15p051p0A1pR@K1pRJM1").
Proof.
intros s i Hi H. unfold leaf_ok in H. rewrite (IMGF.hex_byte_atI_spec s _ i) in H; [|rewrite Uint63.of_Z_spec, wB63; apply Z.mod_small; lia|exact Hi].
unfold byte_ok. destruct (hex_byte_at s i); [reflexivity|discriminate].
Qed.
Lemma scanN_complete : ltac2:(TCodec.tc2 tcn__FxHexScan "Q8&>'2'6&Jr1&My2&Lr3%211%5241%8271&K%1295'5'1&?r7&Ir5r2%3221%6251(3%:3921p0<1pR@H1&@r6(0%11;r4%54421H%C3B1:p081p0H1pRFQ21pR<Q31pR>Q51pRJQ71").
Proof.
intros s f. induction f as [|f IH]; intros base n Hn H;
[cbn [scanN]|change (scanN s (S (S f)) base n) with (if N.eqb n 0 then true else if N.eqb n 1 then byte_ok s base else (scanN s (S f) base (N.div2 n) && scanN s (S f) (base + N.div2 n) (n - N.div2 n))%bool)].
- change (2 ^ N.of_nat 0)%N with 1%N in Hn. destruct (N.eqb_spec n 0); [reflexivity|]. assert (n = 1%N) by lia. subst n. cbn [N.eqb Pos.eqb].
specialize (H 0%N ltac:(lia)). rewrite N.add_0_r in H. exact H.
- destruct (N.eqb_spec n 0); [reflexivity|]. destruct (N.eqb_spec n 1).
+ subst n. specialize (H 0%N ltac:(lia)). rewrite N.add_0_r in H. exact H.
+ assert (P2 : (2 ^ N.of_nat (S f) = 2 * 2 ^ N.of_nat f)%N) by (rewrite Nat2N.inj_succ, N.pow_succ_r'; reflexivity).
pose proof (N.div2_odd n) as D. rewrite N.div2_div in *. set (h := (n / 2)%N) in *.
assert (Hb : (N.b2n (N.odd n) <= 1)%N) by (destruct (N.odd n); cbn; lia).
rewrite (IH base h) by (try lia; intros i Hi; apply H; lia).
rewrite (IH (base + h)%N (n - h)%N); [reflexivity|lia|]. intros i Hi. rewrite <- N.add_assoc. apply H. lia.
Qed.
Theorem scan_ok : ltac2:(TCodec.tc2 tcn__FxHexScan "Q1&>'6'5'1&Fr3r2r1%43321(3%83721&O&N&Q2%119%219%4221&Q4+2+QN%3221%:251&@r5uR0r4%44321E%I3H1Bp071p0C1pRFM1pR<N1pRJQ01").
Proof.
intros s base n H Hb. apply (scanN_complete s 63 base n).
- apply N2Z.inj_le. rewrite N2Z.inj_pow. change (Z.of_N 2) with 2. change (Z.of_N (N.of_nat 63)) with 63. lia.
- intros i Hi. apply leaf_ok_spec; [lia|]. exact (scanG_spec _ base n Hb H i Hi).
Qed.
Definition byte_zero (s : PrimString.string) (off : N) : bool :=
match hex_byte_at s off with Some b => Z.eqb (bv_unsigned b) 0 | None => false end.
Definition leaf_zero (s : PrimString.string) (o : int) : bool := match IMGF.hex_byte_atI s o with Some Z0 => true | _ => false end.
Definition zscanF (s : PrimString.string) (base n : N) : bool := scanG (leaf_zero s) base n.
Lemma leaf_zero_spec : ltac2:(TCodec.tc2 tcn__FxHexScan "N&>'6&Q0&Q2r1%211&Q4+2+QN%3221%8251'5'1&Er3&;r2%>11%311%6251(3%:3921&Cr4%221:%>3=15p051p0A1pR@K1pRJM1").
Proof.
intros s i Hi H. unfold leaf_zero in H. rewrite (IMGF.hex_byte_atI_spec s _ i) in H; [|rewrite Uint63.of_Z_spec, wB63; apply Z.mod_small; lia|exact Hi].
unfold byte_zero. destruct (hex_byte_at s i) as [b|]; [|discriminate]. cbn [option_map] in H.
destruct (bv_unsigned b); [reflexivity|discriminate|discriminate].
Qed.
Section ZS.
Variable zs : PrimString.string -> nat -> N -> N -> bool.
Variable bz : PrimString.string -> N -> bool.
Hypothesis ZS_eq : forall s f base n, zs s (S f) base n =
if N.eqb n 0 then true else if N.eqb n 1 then bz s base else (zs s f base (N.div2 n) && zs s f (base + N.div2 n) (n - N.div2 n))%bool.
Hypothesis BZ : forall s i, byte_zero s i = true -> bz s i = true.
Lemma zs_complete : ltac2:(TCodec.tc2 tcn__FxHexScan "Q8&>'2'6&Jr1&My2&Lr3%211%5241%8271&K%1295'5'1&Cr7&Ir5r2%3221%6251(3%:3921p0<1pR@H1vQ>r6(0%11;r4%54421H%C3B1:p081p0H1pRFQ21pR<Q31pR>Q51pRJQ71").
Proof.
intros s f. induction f as [|f IH]; intros base n Hn H; rewrite ZS_eq.
- change (2 ^ N.of_nat 0)%N with 1%N in Hn. destruct (N.eqb_spec n 0); [reflexivity|]. assert (n = 1%N) by lia. subst n. cbn [N.eqb Pos.eqb].
apply BZ. specialize (H 0%N ltac:(lia)). rewrite N.add_0_r in H. exact H.
- destruct (N.eqb_spec n 0); [reflexivity|]. destruct (N.eqb_spec n 1).
+ subst n. apply BZ. specialize (H 0%N ltac:(lia)). rewrite N.add_0_r in H. exact H.
+ assert (P2 : (2 ^ N.of_nat (S f) = 2 * 2 ^ N.of_nat f)%N) by (rewrite Nat2N.inj_succ, N.pow_succ_r'; reflexivity).
pose proof (N.div2_odd n) as D. rewrite N.div2_div in *. set (h := (n / 2)%N) in *.
assert (Hb : (N.b2n (N.odd n) <= 1)%N) by (destruct (N.odd n); cbn; lia).
rewrite (IH base h) by (try lia; intros i Hi; apply H; lia).
rewrite (IH (base + h)%N (n - h)%N); [reflexivity|lia|]. intros i Hi. rewrite <- N.add_assoc. apply H. lia.
Qed.
Theorem zscan_ok : ltac2:(TCodec.tc2 tcn__FxHexScan "Q1&>'6'5'1&Hr3r2r1%43321(3%83721&O&N&Q2%119%219%4221&Q4+2+QN%3221%:251vQ>r5uR0r4%44321E%I3H1Bp071p0C1pRFM1pR<N1pRJQ01").
Proof.
intros s base n H Hb. apply (zs_complete s 63 base n).
- apply N2Z.inj_le. rewrite N2Z.inj_pow. change (Z.of_N 2) with 2. change (Z.of_N (N.of_nat 63)) with 63. lia.
- intros i Hi. apply leaf_zero_spec; [lia|]. exact (scanG_spec _ base n Hb H i Hi).
Qed.
End ZS.
End FXH.
