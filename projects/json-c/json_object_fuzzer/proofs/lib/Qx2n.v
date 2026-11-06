(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Fpu Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfYR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfYR.
Import ListNotations. Unset Keyed Unification.
Open Scope Z_scope.

Definition ishexc (c : Z) : bool := (u32 (c - 48) <? 10) || (u32 (Z.lor c 32 - 97) <? 6).

Record st_hex := mkHX { hx_c : Z; hx_f : shfile; hx_x : Z; hx_y : Z; hx_sc : Z; hx_gt : Z; hx_gr : Z; hx_gd : Z; hx_rp : Z; hx_dc : Z }.

Definition hx_dig_cond (s : st_hex) : bool := ishexc (hx_c s) || (hx_c s =? 46).

Definition hx_dig_body (s : st_hex) : st_hex + st_hex :=
let 'mkHX c f x y sc gt gr gd rp dc := s in
if c =? 46 then
if nz gr then inr s
else let '(c', f') := sh_getc f in inl (mkHX c' f' x y sc gt 1 gd dc dc)
else
let d := if c <=? 57 then c - 48 else Z.lor c 32 - 87 in
let '(x, y, sc, gt) :=
if dc <=? 7 then (u32 (x * 16 + d), y, sc, gt)
else if dc <=? 29 then
let df := f128_of_i32 d in
let c16 := f128_of_i32 16 in
let sc := f128_div sc c16 in
let t := f128_mul df sc in
(x, f128_add t y, sc, gt)
else if nz d && negb (nz gt) then
let h := f128_of_d (bv_unsigned D_05) in
let t := f128_mul h sc in
(x, f128_add t y, sc, 1)
else (x, y, sc, gt) in
let '(c', f') := sh_getc f in inl (mkHX c' f' x y sc gt gr 1 rp (dc + 1)).

Fixpoint hx_dig_loop (fuel : nat) (s : st_hex) : option st_hex :=
match fuel with
| O => None
| S fu => if hx_dig_cond s then match hx_dig_body s with inl s' => hx_dig_loop fu s' | inr s' => Some s' end else Some s
end.

Definition hx_norm_body (st : Z * Z * Z) : Z * Z * Z :=
let '(x, y, e2) := st in
let h := f128_of_d (bv_unsigned D_05) in
let ge := f128_ge y h in
let x2 := u32 (2 * x) in
if 0 <=? ge then
let one := f128_of_i32 1 in
let t := f128_sub y one in
(Z.lor x2 1, f128_add y t, e2 - 1)
else (x2, f128_add y y, e2 - 1).
Fixpoint hx_norm_loop (fuel : nat) (st : Z * Z * Z) : option (Z * Z * Z) :=
match fuel with
| O => None
| S fu => let '(x, y, e2) := st in if 2^31 <=? x then Some st else hx_norm_loop fu (hx_norm_body st)
end.

Definition hx_zero (sign : Z) : Z := f128_of_d (bv_unsigned (fmul_d RNE (fcvt_d_w RNE (Z_to_bv 64 sign)) D_ZERO)).

Definition hexfloat_m (fuelc : nat) (f : shfile) (bits emin sign pok : Z) : option (shfile * Z) :=
let y0 := f128_of_i32 0 in
let sc0 := f128_of_i32 1 in
let '(c, f) := sh_getc f in
match df_lz_loop fuelc (0, c, f) with
| None => None
| Some (gd, c, f) =>
match (if c =? 46 then
let '(c, f) := sh_getc f in
match df_rz_loop fuelc (gd, 0, c, f) with
| None => None
| Some (gd, rp, c, f) => Some (gd, 1, rp, c, f)
end
else Some (gd, 0, 0, c, f)) with
| None => None
| Some (gd, gr, rp, c, f) =>
match hx_dig_loop fuelc (mkHX c f 0 y0 sc0 0 gr gd rp 0) with
| None => None
| Some (mkHX c f x y sc gt gr gd rp dc) =>
if negb (nz gd) then
let f := sh_unget f in
let f := if nz pok then (let f := sh_unget f in if nz gr then sh_unget f else f) else sh_lim0 f in
Some (f, hx_zero sign)
else
let rp := if nz gr then rp else dc in
let x := if dc <=? 7 then u32 (x * 16 ^ (8 - dc)) else x in
match (if Z.lor c 32 =? 112 then
match scanexp fuelc f pok with
| None => None
| Some (f, e2) =>
if e2 =? LLONG_MIN_ then
(if nz pok then Some (inl (sh_unget f, 0))
else Some (inr (sh_lim0 f, f128_of_i32 0)))
else Some (inl (f, e2))
end
else Some (inl (sh_unget f, 0))) with
| None => None
| Some (inr r) => Some r
| Some (inl (f, e2)) =>
let e2 := 4 * rp + e2 - 32 in
if x =? 0 then Some (f, hx_zero sign)
else if - emin <? e2 then
Some (f, f128_mul (f128_mul (f128_of_i32 sign) C_LDBL_MAX) C_LDBL_MAX)
else if e2 <? emin - 2 * LDBL_MANT_DIG_ then
Some (f, f128_mul (f128_mul (f128_of_i32 sign) C_LDBL_MIN) C_LDBL_MIN)
else
match hx_norm_loop 33%nat (x, y, e2) with
| None => None
| Some (x, y, e2) =>
let bits := if bits <=? 32 + e2 - emin then bits else Z.max 0 (32 + e2 - emin) in
let '(bias, x, y) :=
if bits <=? 112 then
let d := m_scalbn (fcvt_d_w RNE (Z_to_bv 64 1)) (144 - bits) in
let h := f128_of_d (bv_unsigned d) in
let sf := f128_of_i32 sign in
let bias := m_copysignl h sf in
if bits <=? 31 then
let le := f128_le y 0 in
if negb (Z.odd x) && nz le then (bias, Z.lor x 1, f128_of_i32 0)
else (bias, x, y)
else (bias, x, y)
else (y0, x, y) in
let sf := f128_of_i32 sign in
let xf := f128_of_u32 x in
let t1 := f128_mul sf xf in
let t2 := f128_add t1 bias in
let t3 := f128_mul sf y in
let t4 := f128_add t3 t2 in
let y := f128_sub t4 bias in

Some (f, m_scalbnl y e2)
end end end end end.

Section FS.
Variables (fuelc : nat) (bits emin pok : Z).

Definition FS_zero (sign c2 : Z) (f2 : shfile) : option (shfile * Z) :=
if Z.lor c2 32 =? 120 then hexfloat_m fuelc f2 bits emin sign pok
else decfloat fuelc (sh_unget f2) 48 bits emin sign pok.

Definition FS_tail_h (sign c : Z) (f : shfile) : option (shfile * Z) :=
if c =? 48 then let '(c2, f2) := sh_getc f in FS_zero sign c2 f2
else decfloat fuelc f c bits emin sign pok.

Definition FS_nan (sign i c : Z) (f : shfile) : option (shfile * Z) :=
if i =? 3 then
let '(c2, f) := sh_getc f in
if negb (c2 =? 40) then Some (sh_unget f, C_NAN)
else
match fs_par_loop fuelc (1, f) with
| None => None
| Some (i, c, f) =>
if c =? 41 then Some (f, C_NAN)
else
let f := sh_unget f in
if negb (nz pok) then Some (sh_lim0 f, f128_of_i32 0)
else Some (fs_unget_loop (Z.to_nat i) f, C_NAN)
end
else if nz i then
let f := sh_unget f in Some (sh_lim0 f, f128_of_i32 0)
else FS_tail_h sign c f.

Definition FS_nank (sign k c : Z) (f : shfile) : option (shfile * Z) :=
match fs_nan_loop (Z.to_nat (4 - k)) (k, c, f) with
| None => None
| Some (i, c, f) => FS_nan sign i c f
end.

Definition FS_inf (sign i c : Z) (f : shfile) : option (shfile * Z) :=
if (i =? 3) || (i =? 8) || ((3 <? i) && nz pok) then
let f := if negb (i =? 8) then
let f := sh_unget f in
if nz pok then fs_unget_loop (Z.to_nat (i - 3)) f else f
else f in
Some (f, if 0 <? sign then C_INF else C_NINF)
else
match (if i =? 0 then fs_nan_loop 4%nat (0, c, f) else Some (i, c, f)) with
| None => None
| Some (i, c, f) => FS_nan sign i c f
end.

Definition FS_infk (sign k c : Z) (f : shfile) : option (shfile * Z) :=
match fs_inf_loop (Z.to_nat (9 - k)) (k, c, f) with
| None => None
| Some (i, c, f) => FS_inf sign i c f
end.

Definition FS_sign (c : Z) (f : shfile) : option (shfile * Z) :=
let '(sign, c, f) :=
if (c =? 43) || (c =? 45) then
let sign := 1 - 2 * b2z (c =? 45) in
let '(c, f) := sh_getc f in (sign, c, f)
else (1, c, f) in
FS_infk sign 0 c f.
End FS.

Definition floatscan_h (fuelc : nat) (f : shfile) (prec pok : Z) : option (shfile * Z) :=
match (if prec =? 0 then Some (24, -125 - 24)
else if prec =? 1 then Some (53, -1021 - 53)
else if prec =? 2 then Some (113, -16381 - 113)
else None) with
| None => Some (f, f128_of_i32 0)
| Some (bits, emin) =>
match fs_ws_loop fuelc f with
| None => None
| Some (c, f) => FS_sign fuelc bits emin pok c f
end end.

Definition scan_strtod_h (s : list Z) : option (Z * Z) :=
let f := mkSh s 0 0 0 false false in
match floatscan_h (fuel_of s) f 1 1 with
| None => None
| Some (f, y) => Some (f128_to_d y, sh_cnt f)
end.

Lemma fs_inf_loop_S : forall n st, fs_inf_loop (S n) st = (if fs_inf_cond st then fs_inf_loop n (fs_inf_body st) else Some st).
Proof. reflexivity. Qed.
Lemma fs_nan_loop_S : forall n st, fs_nan_loop (S n) st = (if fs_nan_cond st then fs_nan_loop n (fs_nan_body st) else Some st).
Proof. reflexivity. Qed.
Lemma fs_par_loop_S : forall n st, fs_par_loop (S n) st = match fs_par_body st with inl st' => fs_par_loop n st' | inr r => Some r end.
Proof. reflexivity. Qed.
Lemma fs_ws_loop_S : forall n f, fs_ws_loop (S n) f = (let '(c, f') := sh_getc f in if m_isspace c then fs_ws_loop n f' else Some (c, f')).
Proof. intros. cbn [fs_ws_loop]. destruct (sh_getc f). reflexivity. Qed.
Lemma df_lz_loop_S : forall n g c f, df_lz_loop (S n) (g, c, f) = (if c =? 48 then df_lz_loop n (df_lz_body (g, c, f)) else Some (g, c, f)).
Proof. reflexivity. Qed.
Lemma df_rz_loop_S : forall n g l c f, df_rz_loop (S n) (g, l, c, f) = (if c =? 48 then df_rz_loop n (df_rz_body (g, l, c, f)) else Some (g, l, c, f)).
Proof. reflexivity. Qed.
Lemma hx_dig_loop_S : forall n s, hx_dig_loop (S n) s = (if hx_dig_cond s then match hx_dig_body s with inl s' => hx_dig_loop n s' | inr s' => Some s' end else Some s).
Proof. reflexivity. Qed.
Lemma hx_norm_loop_S : forall n x y e2, hx_norm_loop (S n) (x, y, e2) = (if 2^31 <=? x then Some (x, y, e2) else hx_norm_loop n (hx_norm_body (x, y, e2))).
Proof. reflexivity. Qed.

Section Unroll.
Variables (fuelc : nat) (bits emin pok : Z).
Notation FS_infk' := (FS_infk fuelc bits emin pok).
Notation FS_inf' := (FS_inf fuelc bits emin pok).
Notation FS_nank' := (FS_nank fuelc bits emin pok).
Notation FS_nan' := (FS_nan fuelc bits emin pok).

#[using="Type"] Lemma FS_infk_step : forall sign k c f, 0 <= k <= 7 ->
FS_infk' sign k c f =
(if Z.lor c 32 =? znth str_infinity k
then (if k <? 7 then FS_infk' sign (k + 1) (fst (sh_getc f)) (snd (sh_getc f)) else FS_infk' sign (k + 1) c f)
else FS_inf' sign k c f).
Proof.
intros sign k c f Hk. unfold FS_infk.
replace (Z.to_nat (9 - k)) with (S (Z.to_nat (9 - (k + 1)))) by lia.
rewrite fs_inf_loop_S. unfold fs_inf_cond at 1. replace (k <? 8) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
destruct (Z.lor c 32 =? znth str_infinity k); [|reflexivity].
unfold fs_inf_body. destruct (k <? 7); [rewrite (surjective_pairing (sh_getc f))|]; reflexivity.
Qed.
#[using="Type"] Lemma FS_infk_8 : forall sign c f, FS_infk' sign 8 c f = FS_inf' sign 8 c f.
Proof. intros. unfold FS_infk. change (Z.to_nat (9 - 8)) with 1%nat. rewrite fs_inf_loop_S. unfold fs_inf_cond. cbn [Z.ltb Z.compare Pos.compare andb]. reflexivity. Qed.

#[using="Type"] Lemma FS_nank_step : forall sign k c f, 0 <= k <= 2 ->
FS_nank' sign k c f =
(if Z.lor c 32 =? znth str_nan k
then (if k <? 2 then FS_nank' sign (k + 1) (fst (sh_getc f)) (snd (sh_getc f)) else FS_nank' sign (k + 1) c f)
else FS_nan' sign k c f).
Proof.
intros sign k c f Hk. unfold FS_nank.
replace (Z.to_nat (4 - k)) with (S (Z.to_nat (4 - (k + 1)))) by lia.
rewrite fs_nan_loop_S. unfold fs_nan_cond at 1. replace (k <? 3) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
destruct (Z.lor c 32 =? znth str_nan k); [|reflexivity].
unfold fs_nan_body. destruct (k <? 2); [rewrite (surjective_pairing (sh_getc f))|]; reflexivity.
Qed.
#[using="Type"] Lemma FS_nank_3 : forall sign c f, FS_nank' sign 3 c f = FS_nan' sign 3 c f.
Proof. intros. unfold FS_nank. change (Z.to_nat (4 - 3)) with 1%nat. rewrite fs_nan_loop_S. unfold fs_nan_cond. cbn [Z.ltb Z.compare Pos.compare andb]. reflexivity. Qed.

#[using="Type"] Lemma FS_inf_0 : forall sign c f, FS_inf' sign 0 c f = FS_nank' sign 0 c f.
Proof. intros. unfold FS_inf. cbn [Z.eqb Z.ltb orb andb Z.compare]. unfold FS_nank. change (Z.to_nat (4 - 0)) with 4%nat. reflexivity. Qed.

Definition sINF (sign : Z) : Z := if 0 <? sign then C_INF else C_NINF.
#[using="Type"] Lemma FS_inf_err : forall sign i c f, i = 1 \/ i = 2 -> FS_inf' sign i c f = Some (sh_lim0 (sh_unget f), f128_of_i32 0).
Proof. intros sign i c f [-> | ->]; reflexivity. Qed.
#[using="Type"] Lemma FS_inf_3 : forall sign c f, pok = 1 -> FS_inf' sign 3 c f = Some (sh_unget f, sINF sign).
Proof. intros sign c f ->. reflexivity. Qed.
#[using="Type"] Lemma FS_inf_mid : forall sign i c f, pok = 1 -> 4 <= i <= 7 -> FS_inf' sign i c f = Some (fs_unget_loop (Z.to_nat (i - 3)) (sh_unget f), sINF sign).
Proof.
intros sign i c f -> Hi. unfold FS_inf.
replace ((i =? 3) || (i =? 8) || (3 <? i) && nz 1) with true by (symmetry; rewrite !Bool.orb_true_iff; right; apply andb_true_iff; split; [apply Z.ltb_lt; lia | reflexivity]).
replace (i =? 8) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.
#[using="Type"] Lemma FS_inf_8 : forall sign c f, FS_inf' sign 8 c f = Some (f, sINF sign).
Proof. intros. reflexivity. Qed.

#[using="Type"] Lemma FS_nan_err : forall sign i c f, i = 1 \/ i = 2 -> FS_nan' sign i c f = Some (sh_lim0 (sh_unget f), f128_of_i32 0).
Proof. intros sign i c f [-> | ->]; reflexivity. Qed.
#[using="Type"] Lemma FS_nan_0 : forall sign c f, FS_nan' sign 0 c f = FS_tail_h fuelc bits emin pok sign c f.
Proof. intros. reflexivity. Qed.
End Unroll.

Lemma fs_unget_loop_eq : forall n f, sh_shlim_neg f = false ->
fs_unget_loop n f = mkSh (sh_buf f) (sh_rpos f - Z.of_nat n) (sh_cnt0 f) (sh_n f) (sh_stdio f) false.
Proof.
induction n as [|n IH]; intros f H.
- cbn. destruct f; cbn in *; subst; f_equal; lia.
- cbn [fs_unget_loop]. rewrite IH by (unfold sh_unget; rewrite H; reflexivity).
unfold sh_unget; rewrite H; cbn. f_equal. lia.
Qed.

Lemma floatscan_h_1 : forall fuelc f pok,
floatscan_h fuelc f 1 pok = match fs_ws_loop fuelc f with None => None | Some (c, f') => FS_sign fuelc 53 (-1074) pok c f' end.
Proof. reflexivity. Qed.

Lemma floatscan_h_of_old : forall fuelc f prec pok r,
floatscan fuelc f prec pok = Some r -> floatscan_h fuelc f prec pok = Some r.
Proof.
intros fuelc f prec pok r H. unfold floatscan in H. unfold floatscan_h.
destruct (if prec =? 0 then _ else _) as [[bits emin]|]; [|exact H].
destruct (fs_ws_loop fuelc f) as [[c f1]|]; [|exact H].
unfold FS_sign, FS_infk. change (Z.to_nat (9 - 0)) with 9%nat.
destruct (if (c =? 43) || (c =? 45) then _ else _) as [[sign c2] f2].
destruct (fs_inf_loop 9 (0, c2, f2)) as [[[i c3] f3]|]; [|exact H].
unfold FS_inf.
destruct ((i =? 3) || (i =? 8) || (3 <? i) && nz pok); [exact H|].
destruct (if i =? 0 then _ else _) as [[[i4 c4] f4]|]; [|exact H].
unfold FS_nan.
destruct (i4 =? 3). { destruct (sh_getc f4) as [c5 f5]. exact H. }
destruct (nz i4); [exact H|].
unfold FS_tail_h. destruct (c4 =? 48); [|exact H].
destruct (sh_getc f4) as [c5 f5]. unfold FS_zero. destruct (Z.lor c5 32 =? 120); [discriminate H | exact H].
Qed.

Lemma scan_strtod_h_of_old : forall s r, scan_strtod s = Some r -> scan_strtod_h s = Some r.
Proof.
intros s r H. unfold scan_strtod in H. unfold scan_strtod_h.
destruct (floatscan (fuel_of s) _ 1 1) as [[f y]|] eqn:E; [|discriminate H].
rewrite (floatscan_h_of_old _ _ _ _ _ E). exact H.
Qed.

Section HX.
Variables (fuelc : nat) (bits emin sign pok : Z).
Let y0 : Z := f128_of_i32 0.
Let sc0 : Z := f128_of_i32 1.

Definition HX_fin (f : shfile) (x y e2 : Z) : option (shfile * Z) :=
let bits := if bits <=? 32 + e2 - emin then bits else Z.max 0 (32 + e2 - emin) in
let '(bias, x, y) :=
if bits <=? 112 then
let d := m_scalbn (fcvt_d_w RNE (Z_to_bv 64 1)) (144 - bits) in
let h := f128_of_d (bv_unsigned d) in
let sf := f128_of_i32 sign in
let bias := m_copysignl h sf in
if bits <=? 31 then
let le := f128_le y 0 in
if negb (Z.odd x) && nz le then (bias, Z.lor x 1, f128_of_i32 0)
else (bias, x, y)
else (bias, x, y)
else (y0, x, y) in
let sf := f128_of_i32 sign in
let xf := f128_of_u32 x in
let t1 := f128_mul sf xf in
let t2 := f128_add t1 bias in
let t3 := f128_mul sf y in
let t4 := f128_add t3 t2 in
let y := f128_sub t4 bias in
Some (f, m_scalbnl y e2).

Definition HX_e2 (f : shfile) (x y e2 : Z) : option (shfile * Z) :=
if x =? 0 then Some (f, hx_zero sign)
else if - emin <? e2 then
Some (f, f128_mul (f128_mul (f128_of_i32 sign) C_LDBL_MAX) C_LDBL_MAX)
else if e2 <? emin - 2 * LDBL_MANT_DIG_ then
Some (f, f128_mul (f128_mul (f128_of_i32 sign) C_LDBL_MIN) C_LDBL_MIN)
else
match hx_norm_loop 33%nat (x, y, e2) with
| None => None
| Some (x, y, e2) => HX_fin f x y e2
end.

Definition HX_tail (c : Z) (f : shfile) (x y gr gd rp dc : Z) : option (shfile * Z) :=
if negb (nz gd) then
let f := sh_unget f in
let f := if nz pok then (let f := sh_unget f in if nz gr then sh_unget f else f) else sh_lim0 f in
Some (f, hx_zero sign)
else
let rp := if nz gr then rp else dc in
let x := if dc <=? 7 then u32 (x * 16 ^ (8 - dc)) else x in
match (if Z.lor c 32 =? 112 then
match scanexp fuelc f pok with
| None => None
| Some (f, e2) =>
if e2 =? LLONG_MIN_ then
(if nz pok then Some (inl (sh_unget f, 0))
else Some (inr (sh_lim0 f, f128_of_i32 0)))
else Some (inl (f, e2))
end
else Some (inl (sh_unget f, 0))) with
| None => None
| Some (inr r) => Some r
| Some (inl (f, e2)) => HX_e2 f x y (4 * rp + e2 - 32)
end.

Definition HX_dig (s : st_hex) : option (shfile * Z) :=
match hx_dig_loop fuelc s with
| None => None
| Some (mkHX c f x y sc gt gr gd rp dc) => HX_tail c f x y gr gd rp dc
end.

Definition HX_rz (gd rp c : Z) (f : shfile) : option (shfile * Z) :=
match df_rz_loop fuelc (gd, rp, c, f) with
| None => None
| Some (gd, rp, c, f) => HX_dig (mkHX c f 0 y0 sc0 0 1 gd rp 0)
end.

Definition HX_alz (gd c : Z) (f : shfile) : option (shfile * Z) :=
if c =? 46 then let '(c, f) := sh_getc f in HX_rz gd 0 c f
else HX_dig (mkHX c f 0 y0 sc0 0 0 gd 0 0).

Definition HX_lz (gd c : Z) (f : shfile) : option (shfile * Z) :=
match df_lz_loop fuelc (gd, c, f) with
| None => None
| Some (gd, c, f) => HX_alz gd c f
end.

#[using="Type"] Lemma hexfloat_m_eq : forall f,
hexfloat_m fuelc f bits emin sign pok = (let '(c, f) := sh_getc f in HX_lz 0 c f).
Proof.
intros f. unfold hexfloat_m, HX_lz. destruct (sh_getc f) as [c1 f1].
destruct (df_lz_loop fuelc (0, c1, f1)) as [[[gd c2] f2]|]; [|reflexivity].
unfold HX_alz. destruct (c2 =? 46).
- destruct (sh_getc f2) as [c3 f3]. unfold HX_rz.
destruct (df_rz_loop fuelc (gd, 0, c3, f3)) as [[[[gd4 rp4] c4] f4]|]; [|reflexivity].
unfold HX_dig. destruct (hx_dig_loop fuelc _) as [[c5 f5 x5 y5 sc5 gt5 gr5 gd5 rp5 dc5]|]; [|reflexivity].
unfold HX_tail. destruct (negb (nz gd5)); [reflexivity|].
destruct (if Z.lor c5 32 =? 112 then _ else _) as [[[f6 e6]|r]|]; [|reflexivity|reflexivity].
unfold HX_e2. destruct (_ =? 0); [reflexivity|]. destruct (- emin <? _); [reflexivity|]. destruct (_ <? emin - _); [reflexivity|].
destruct (hx_norm_loop 33 _) as [[[x7 y7] e7]|]; reflexivity.
- unfold HX_dig. destruct (hx_dig_loop fuelc _) as [[c5 f5 x5 y5 sc5 gt5 gr5 gd5 rp5 dc5]|]; [|reflexivity].
unfold HX_tail. destruct (negb (nz gd5)); [reflexivity|].
destruct (if Z.lor c5 32 =? 112 then _ else _) as [[[f6 e6]|r]|]; [|reflexivity|reflexivity].
unfold HX_e2. destruct (_ =? 0); [reflexivity|]. destruct (- emin <? _); [reflexivity|]. destruct (_ <? emin - _); [reflexivity|].
destruct (hx_norm_loop 33 _) as [[[x7 y7] e7]|]; reflexivity.
Qed.

End HX.

