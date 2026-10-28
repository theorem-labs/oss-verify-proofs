(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a YC80 YC1f YC1g YC1h YC81 YC4b YC20 YC44 YC45.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjr ACj1 ACj0 ACja.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACj0 ACj6 ACiy ACj7 ACj8.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC7y YC7x YC85.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AChz ACid.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
Definition xG (cx : flcx) (xx : flxx) : YO07.gcfg := gcfg_of (c_s cx) (x_GPAL xx).
Definition xgen3 (cx : flcx) (xx : flxx) : Z := YI0f.fl_gen3 (xG cx xx) (x_cur xx) (x_bef xx).
Definition xdims (cx : flcx) (xx : flxx) : Z * Z * Z * Z := YI0f.fl_dims (xG cx xx) (x_cur xx) (x_bef xx).
Definition xtmp (cx : flcx) (xx : flxx) : list Z := YI0f.fl_tmp (xG cx xx) (x_cur xx) (x_bef xx).
Definition ximg (cx : flcx) (xx : flxx) : list Z := YI0f.fl_img (xG cx xx) (x_cur xx) (x_bef xx).
Definition xtidx (cx : flcx) (xx : flxx) : Z := YI0f.fl_tidx (xG cx xx) (x_cur xx) (x_bef xx).
Definition xtopt (cx : flcx) (xx : flxx) : Z := YI0f.fl_tOpt (xG cx xx) (x_cur xx).
Definition xhastr (cx : flcx) (xx : flxx) : Z :=
if (YI0f.fl_hasAlpha (xG cx xx) (x_cur xx) || YI0f.fl_trans_on (xG cx xx) (x_cur xx) (x_bef xx) || YI0f.fl_hasSet (x_cur xx))%bool
then 1 else 0.
Section c.
Variable K : asink_syms.
Variable MT : ameter_ops.
Variable XN : xnums.
#[local] Notation INVT := (flcx -> flxx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop).
Definition xmacc (pt n : Z) : Z := if pt =? 0 then 0 else mo_malloc MT n.
Definition INV_DIFFX (B : asyms) : INVT :=
fun cx xx E k ly3 S3 W3 ms3 md3 => INV_DIFF B cx E k ly3 S3 W3 ms3 md3 /\
ew E 621 = Z_to_bv 64 (xgen3 cx xx) /\ YO07.flag (xgen3 cx xx) 2 = true /\ mo_le MT (c_S cx) S3 0.
Definition INV_DIMSX (B : asyms) : INVT :=
fun cx xx E k ly3 S3 W3 ms3 md3 => k <= 0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) /\
(exists gen, ew E 621 = Z_to_bv 64 gen /\ 0 <= gen < 2 ^ 32) /\
ew E 625 = Z_to_bv 64 (ACj6.fl_npal cx) /\
(exists fb, fl_bef cx fb E) /\
(exists w h top left, ew E 861 = Z_to_bv 64 w /\ val_mem SEGS (mrestrict (w_H W3) (ms_mem ms3)) (c_sp1 cx + 160) 8 h /\ ew E 862 = Z_to_bv 64 top /\
ew E 863 = Z_to_bv 64 left /\
1 <= w /\ 0 <= left /\ left + w <= cg_W (c_s cx) /\ 1 <= h /\ 0 <= top /\ top + h <= cg_H (c_s cx) /\
xdims cx xx = (w, h, top, left)) /\
ew E 621 = Z_to_bv 64 (xgen3 cx xx) /\ YO07.flag (xgen3 cx xx) 2 = true /\ mo_le MT (c_S cx) S3 0.
Definition INV_D1X (B : asyms) : INVT :=
fun cx xx E k ly3 S3 W3 ms3 md3 => k <= 0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) /\
(exists gen, ew E 621 = Z_to_bv 64 gen /\ 0 <= gen < 2 ^ 32) /\
ew E 625 = Z_to_bv 64 (ACj6.fl_npal cx) /\
(exists fb, fl_bef cx fb E) /\
(exists w h top left, ew E 887 = Z_to_bv 64 w /\ ew E 888 = Z_to_bv 64 h /\ ew E 889 = Z_to_bv 64 top /\ ew E 890 = Z_to_bv 64 left /\
1 <= w /\ 0 <= left /\ left + w <= cg_W (c_s cx) /\ 1 <= h /\ 0 <= top /\ top + h <= cg_H (c_s cx) /\
xdims cx xx = (w, h, top, left)) /\
ew E 621 = Z_to_bv 64 (xgen3 cx xx) /\ YO07.flag (xgen3 cx xx) 2 = true /\ mo_le MT (c_S cx) S3 0.
Definition INV_DIMSiX (B : asyms) : INVT :=
fun cx xx E k ly3 S3 W3 ms3 md3 => INV_DIMSi B cx E k ly3 S3 W3 ms3 md3 /\ xdims cx xx = (1, 1, 0, 0) /\
ew E 621 = Z_to_bv 64 (xgen3 cx xx) /\ YO07.flag (xgen3 cx xx) 2 = true /\ mo_le MT (c_S cx) S3 0.
Definition INV_T0X (B : asyms) : INVT :=
fun cx xx E k ly3 S3 W3 ms3 md3 =>
(exists gen, ew E 621 = Z_to_bv 64 gen /\ 0 <= gen < 2 ^ 32) /\ ew E 625 = Z_to_bv 64 (ACj6.fl_npal cx) /\
(exists fb, fl_bef cx fb E) /\
(exists pt w h top left,
ew E 682 = Z_to_bv 64 pt /\ ew E 679 = Z_to_bv 64 w /\ ew E 684 = Z_to_bv 64 h /\ ew E 681 = Z_to_bv 64 top /\ ew E 680 = Z_to_bv 64 left /\
0 <= pt < 2 ^ 64 /\
1 <= w /\ 0 <= left /\ left + w <= cg_W (c_s cx) /\ 1 <= h /\ 0 <= top /\ top + h <= cg_H (c_s cx) /\
((pt = 0 /\ w = cg_W (c_s cx) /\ h = cg_H (c_s cx) /\ k <= 0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx)) \/
(pt <> 0 /\ k <= 2 /\ fl_tmpblkX B cx pt (w * h) ly3 S3)) /\
(xdims cx xx = (w, h, top, left) /\
(pt <> 0 -> garr8 SEGS (mrestrict (w_H W3) (ms_mem ms3)) pt (xtmp cx xx)) /\ (pt = 0 -> xtmp cx xx = YO07.f_img (x_cur xx)) /\
Z.of_nat (length (xtmp cx xx)) = w * h /\
mo_le MT (c_S cx) S3 (xmacc pt (w * h)))) /\
ew E 621 = Z_to_bv 64 (xgen3 cx xx).
Definition INV_T1xX (B : asyms) : INVT :=
fun cx xx E k ly3 S3 W3 ms3 md3 => INV_T0X B cx xx E k ly3 S3 W3 ms3 md3 /\
YO07.flag (xgen3 cx xx) 1 = true /\
(exists tv, ew E 741 = Z_to_bv 64 tv /\ 0 <= tv < 2 ^ 64 /\ tv mod 256 = xtopt cx xx).
Definition INV_T3X (B : asyms) : INVT :=
fun cx xx E k ly3 S3 W3 ms3 md3 =>
(exists gen, ew E 621 = Z_to_bv 64 gen /\ 0 <= gen < 2 ^ 32) /\ ew E 625 = Z_to_bv 64 (ACj6.fl_npal cx) /\
(exists fb, fl_bef cx fb E) /\
(exists pt w h top left,
ew E 801 = Z_to_bv 64 pt /\ ew E 679 = Z_to_bv 64 w /\ ew E 684 = Z_to_bv 64 h /\ ew E 681 = Z_to_bv 64 top /\ ew E 680 = Z_to_bv 64 left /\
1 <= w /\ 0 <= left /\ left + w <= cg_W (c_s cx) /\ 1 <= h /\ 0 <= top /\ top + h <= cg_H (c_s cx) /\
k <= 2 /\ fl_tmpblkX B cx pt (w * h) ly3 S3 /\
(xdims cx xx = (w, h, top, left) /\
garr8 SEGS (mrestrict (w_H W3) (ms_mem ms3)) pt (xtmp cx xx) /\ Z.of_nat (length (xtmp cx xx)) = w * h /\
mo_le MT (c_S cx) S3 (mo_malloc MT (w * h)))) /\
ew E 621 = Z_to_bv 64 (xgen3 cx xx) /\ YO07.flag (xgen3 cx xx) 1 = true /\
(exists tv, ew E 741 = Z_to_bv 64 tv /\ 0 <= tv < 2 ^ 64 /\ tv mod 256 = xtopt cx xx).
Definition xR_tail (cx : flcx) (xx : flxx) (W3 : world SEGS) (ms3 : machine_state) (S3 : astate) (pt w h top left tidx : Z) : Prop :=
xdims cx xx = (w, h, top, left) /\ tidx mod 256 = xtidx cx xx /\
(pt <> 0 -> garr8 SEGS (mrestrict (w_H W3) (ms_mem ms3)) pt (ximg cx xx)) /\ (pt = 0 -> ximg cx xx = YO07.f_img (x_cur xx)) /\
Z.of_nat (length (ximg cx xx)) = w * h /\
mo_le MT (c_S cx) S3 (xmacc pt (w * h)).
Definition INV_RX (B : asyms) : INVT :=
fun cx xx E k ly3 S3 W3 ms3 md3 =>
(exists gen, ew E 621 = Z_to_bv 64 gen /\ 0 <= gen < 2 ^ 32) /\ ew E 625 = Z_to_bv 64 (ACj6.fl_npal cx) /\
(exists pt w h top left tidx,
ew E 843 = Z_to_bv 64 pt /\ ew E 839 = Z_to_bv 64 w /\ ew E 845 = Z_to_bv 64 h /\ ew E 841 = Z_to_bv 64 top /\
ew E 840 = Z_to_bv 64 left /\ ew E 842 = Z_to_bv 64 tidx /\ 0 <= pt < 2 ^ 64 /\
1 <= w /\ 0 <= left /\ left + w <= cg_W (c_s cx) /\ 1 <= h /\ 0 <= top /\ top + h <= cg_H (c_s cx) /\ 0 <= tidx < 2 ^ 64 /\
((pt = 0 /\ k <= 0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx)) \/
(pt <> 0 /\ k <= 2 /\ fl_tmpblkX B cx pt (w * h) ly3 S3)) /\
xR_tail cx xx W3 ms3 S3 pt w h top left tidx) /\
ew E 621 = Z_to_bv 64 (xgen3 cx xx).
Definition INV_R2X (B : asyms) : INVT :=
fun cx xx E k ly3 S3 W3 ms3 md3 =>
(exists gen, ew E 621 = Z_to_bv 64 gen /\ 0 <= gen < 2 ^ 32) /\ ew E 625 = Z_to_bv 64 (ACj6.fl_npal cx) /\
(exists pt w h top left tidx img,
ew E 892 = Z_to_bv 64 pt /\ ew E 839 = Z_to_bv 64 w /\ ew E 845 = Z_to_bv 64 h /\ ew E 841 = Z_to_bv 64 top /\
ew E 840 = Z_to_bv 64 left /\ ew E 842 = Z_to_bv 64 tidx /\ ew E 891 = Z_to_bv 64 img /\ 0 <= pt < 2 ^ 64 /\
1 <= w /\ 0 <= left /\ left + w <= cg_W (c_s cx) /\ 1 <= h /\ 0 <= top /\ top + h <= cg_H (c_s cx) /\ 0 <= tidx < 2 ^ 64 /\
((pt = 0 /\ img = fr_img (c_f cx) /\ k <= 0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx)) \/
(pt <> 0 /\ img = pt /\ k <= 2 /\ fl_tmpblkX B cx pt (w * h) ly3 S3)) /\
xR_tail cx xx W3 ms3 S3 pt w h top left tidx) /\
ew E 621 = Z_to_bv 64 (xgen3 cx xx).
Definition INV_R3X (B : asyms) : INVT :=
fun cx xx E k ly3 S3 W3 ms3 md3 =>
(exists gen, ew E 621 = Z_to_bv 64 gen /\ 0 <= gen < 2 ^ 32) /\ ew E 625 = Z_to_bv 64 (ACj6.fl_npal cx) /\
(exists attr, ew E 901 = Z_to_bv 64 attr /\ 0 <= attr <= 1 /\ attr = xhastr cx xx) /\
(exists pt w h top left tidx img,
ew E 892 = Z_to_bv 64 pt /\ ew E 839 = Z_to_bv 64 w /\ ew E 845 = Z_to_bv 64 h /\ ew E 841 = Z_to_bv 64 top /\
ew E 840 = Z_to_bv 64 left /\ ew E 842 = Z_to_bv 64 tidx /\ ew E 891 = Z_to_bv 64 img /\ 0 <= pt < 2 ^ 64 /\
1 <= w /\ 0 <= left /\ left + w <= cg_W (c_s cx) /\ 1 <= h /\ 0 <= top /\ top + h <= cg_H (c_s cx) /\ 0 <= tidx < 2 ^ 64 /\
((pt = 0 /\ img = fr_img (c_f cx) /\ k <= 0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx)) \/
(pt <> 0 /\ img = pt /\ k <= 2 /\ fl_tmpblkX B cx pt (w * h) ly3 S3)) /\
xR_tail cx xx W3 ms3 S3 pt w h top left tidx) /\
ew E 621 = Z_to_bv 64 (xgen3 cx xx).
Definition INV_R4X (B : asyms) : INVT :=
fun cx xx E k ly3 S3 W3 ms3 md3 =>
(exists gen, ew E 621 = Z_to_bv 64 gen /\ 0 <= gen < 2 ^ 32) /\ ew E 625 = Z_to_bv 64 (ACj6.fl_npal cx) /\
(exists attr, ew E 901 = Z_to_bv 64 attr /\ 0 <= attr <= 1 /\ attr = xhastr cx xx) /\ ew E 911 = Z_to_bv 64 (ACj7.fl_slct cx) /\
(exists pt w h top left tidx img,
ew E 892 = Z_to_bv 64 pt /\ ew E 839 = Z_to_bv 64 w /\ ew E 845 = Z_to_bv 64 h /\ ew E 841 = Z_to_bv 64 top /\
ew E 840 = Z_to_bv 64 left /\ ew E 842 = Z_to_bv 64 tidx /\ ew E 891 = Z_to_bv 64 img /\ 0 <= pt < 2 ^ 64 /\
1 <= w /\ 0 <= left /\ left + w <= cg_W (c_s cx) /\ 1 <= h /\ 0 <= top /\ top + h <= cg_H (c_s cx) /\ 0 <= tidx < 2 ^ 64 /\
((pt = 0 /\ img = fr_img (c_f cx) /\ k <= 0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx)) \/
(pt <> 0 /\ img = pt /\ k <= 2 /\ fl_tmpblkX B cx pt (w * h) ly3 S3)) /\
xR_tail cx xx W3 ms3 S3 pt w h top left tidx) /\
ew E 621 = Z_to_bv 64 (xgen3 cx xx).
Definition xdone (cx : flcx) (xx : flxx) (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) (S3 : astate) (res room : Z) : Prop :=
(exists code bytes,
YO07.flush_frame (xG cx xx) (rc_int (rw_cur (c_s cx))) (x_cur xx) (x_bef xx) = (code, bytes) /\
Z_to_bv 64 res = Z_to_bv 64 code /\
val_mem SEGS (mrestrict (w_H W3) (ms_mem ms3)) (cg_raw (c_s cx) + 40) 4 (code mod 2 ^ 32) /\
asink_at SEGS K (mrestrict (w_H W3) (ms_mem ms3)) md3 (x_pf xx) (x_Sg xx ++ bytes) /\
Z.of_nat (length bytes) <= FRAME_OUT (c_N cx)) /\
(exists acc, mo_le MT (c_S cx) S3 acc /\ acc + room <= xm_flush XN (c_N cx) /\ acc + room <= xn_flush XN (c_N cx)).
Definition INV_R5X (B : asyms) : INVT :=
fun cx xx E k ly3 S3 W3 ms3 md3 =>
k <= 2 + EV_RAWADD /\ (exists res, ew E 919 = Z_to_bv 64 res /\ 0 <= res < 2 ^ 64 /\ xdone cx xx W3 ms3 md3 S3 res (mo_free MT)) /\
ew E 621 = Z_to_bv 64 (xgen3 cx xx) /\
exists pt, ew E 892 = Z_to_bv 64 pt /\ 0 <= pt < 2 ^ 64 /\
((pt = 0 /\ Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx))) \/
(pt <> 0 /\ exists n, 0 <= n /\ Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx) ++ [(pt, n)]) /\
aftok (fl_FPX cx xx) (ablocks B (c_ly cx) (c_S cx)) (pt, n))).
Definition INV_XX (B : asyms) : INVT :=
fun cx xx E k ly3 S3 W3 ms3 md3 =>
k <= EV_FLUSH /\ (exists r, ew E 961 = Z_to_bv 64 r /\ 0 <= r < 2 ^ 64 /\ xdone cx xx W3 ms3 md3 S3 r 0) /\
Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx)) /\
ew E 621 = Z_to_bv 64 (xgen3 cx xx) /\ True.
End c.
End b.
End a.
