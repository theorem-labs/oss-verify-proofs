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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbk.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h AC8j ACab.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00 YI0j YI0k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACai.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC7y YC85.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition ss_A2X : sstate :=
(mkSS 2196
[SLit 0; SOff 512 0; SOff 2 (-320); SOff 3 0; SOff 4 0; SOff 513 0; SOff 514 0; SOff 515 0; SOff 2 0; SOff 2 (-320); SOff 11 30; SLit 6; SOff 534 0; SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 30) (SLit 3)) (SOff 40 0); SOff 11 16;
SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 16) (SLit 3)) (SOff 40 0); SLit 18446744073709551603; SOff 523 0; SOff 516 0; SOff 43 0; SOff 529 0; SExt true 32 (SOff 39 0); SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 40) (SLit 3)) (SOff 40 0);
SOff 49 0; SOff 11 0; SOff 10 40; SOff 516 0; SOff 10 0; SOff 524 0; SOff 525 0; SOff 526 0; SOff 527 0]
[{|
r_base := Some 529%nat;
r_lo := 0;
r_hi := 16;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 7; YP09.c_val := CVal 1 (SLit 2) |}; {| c_off := 6; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 5; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 4; YP09.c_val := CVal 1 (SLit 18446744073709551608) |}; {| c_off := 11; YP09.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 10; YP09.c_val := CVal 1 (SLit 0) |};
{| c_off := 9; YP09.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 8; YP09.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 15; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 14; YP09.c_val := CVal 1 (SLit 18446744073709551608) |}; {| c_off := 13; YP09.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 12; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 3; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 2; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 1; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 0; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}]
|};
{|
r_base := Some 516%nat;
r_lo := 0;
r_hi := 49;
r_wlo := 0;
r_whi := 49;
r_chunks := [{| c_off := 16; YP09.c_val := CVal 8 (SOff 240 1820) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 249 0) |}; {| c_off := 0; YP09.c_val := CVal 8 (SLit 1102416563) |}]
|}; {| r_base := Some 516%nat; r_lo := 49; r_hi := 58; r_wlo := 49; r_whi := 58; r_chunks := [] |};
{| r_base := Some 516%nat; r_lo := 58; r_hi := 128; r_wlo := 58; r_whi := 128; r_chunks := [{| c_off := 120; YP09.c_val := CVal 8 (SOff 528 0) |}] |};
{|
r_base := Some 2%nat;
r_lo := -320;
r_hi := 0;
r_wlo := -320;
r_whi := 0;
r_chunks :=
[{| c_off := -136; YP09.c_val := CVal 8 (SOff 40 0) |}; {| c_off := -128; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |}; {| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |};
{| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |}; {| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |}; {| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |}; {| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |};
{| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |}; {| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |}; {| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |}; {| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |};
{| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |}; {| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |}; {| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}; {| c_off := -320; YP09.c_val := CVal 8 (SLit 0) |}]
|}; {| r_base := Some 241%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}] |};
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 40 0) |}] |};
{| r_base := Some 242%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 55 0) |}] |};
{| r_base := Some 55%nat; r_lo := 0; r_hi := 4; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 4 (SLit 1) |}] |};
{| r_base := Some 250%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 240 1820) |}] |};
{|
r_base := Some 10%nat;
r_lo := 0;
r_hi := 48;
r_wlo := 40;
r_whi := 44;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 53 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 32 0) |}; {| c_off := 16; YP09.c_val := CVal 8 (SOff 33 0) |}; {| c_off := 24; YP09.c_val := CVal 4 (SOff 34 0) |};
{| c_off := 28; YP09.c_val := CVal 2 (SOff 35 0) |}; {| c_off := 30; YP09.c_val := CVal 2 (SOff 36 0) |}; {| c_off := 32; YP09.c_val := CVal 2 (SOff 37 0) |}; {| c_off := 34; YP09.c_val := CVal 2 (SOff 38 0) |};
{| c_off := 40; YP09.c_val := CVal 4 (SOff 39 0) |}]
|};
{|
r_base := Some 11%nat;
r_lo := 0;
r_hi := 40;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 41 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 42 0) |}; {| c_off := 16; YP09.c_val := CVal 4 (SOff 43 0) |}; {| c_off := 20; YP09.c_val := CVal 2 (SOff 44 0) |};
{| c_off := 22; YP09.c_val := CVal 2 (SOff 45 0) |}; {| c_off := 24; YP09.c_val := CVal 2 (SOff 46 0) |}; {| c_off := 26; YP09.c_val := CVal 2 (SOff 47 0) |}; {| c_off := 28; YP09.c_val := CVal 2 (SOff 48 0) |};
{| c_off := 30; YP09.c_val := CVal 2 (SOff 49 0) |}; {| c_off := 32; YP09.c_val := CVal 1 (SOff 50 0) |}; {| c_off := 33; YP09.c_val := CVal 1 (SOff 51 0) |}]
|};
{|
r_base := Some 32%nat;
r_lo := 0;
r_hi := 96;
r_wlo := 0;
r_whi := 0;
r_chunks := [{| c_off := 56; YP09.c_val := CVal 8 (SOff 54 0) |}; {| c_off := 64; YP09.c_val := CVal 8 (SOff 52 0) |}; {| c_off := 80; YP09.c_val := CVal 8 (SOff 56 0) |}]
|}]
None
{|
f_atoms :=
[(529%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |}); (528%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |}); (516%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |});
(2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 5 |}); (10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (11%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 3 |});
(32%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (33%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (34%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(35%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (36%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (37%nat, {| af_lo := 0; af_hi := 256; af_al2 := 0 |}); (38%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(39%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (40%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |}); (41%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(42%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (43%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (44%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |});
(45%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |}); (46%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (47%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (48%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(49%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (50%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (51%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (52%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |})];
f_conds := [];
f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 40 0), SOff 529 0)]
|}).
Definition ss_B8X : sstate := Eval vm_compute in ss_havoc_regs (ss_set_pc ss_A2X 2204) 559 [11; 21]%nat.
Definition ss_CX : sstate := Eval vm_compute in
ss_set_fact (ss_set_reg (ss_set_pc ss_B8X 2232) 11 (SLit 257)) 49 (mkAF 0 256 0).
Definition ra_X_memX (n : nat) : smem :=
[ YP09.mkRegion (Some 529%nat) 0 16 0 0 [];
YP09.mkRegion (Some 516%nat) 0 49 0 49 [];
YP09.mkRegion (Some 516%nat) 58 128 58 128 [YP09.mkChunk 120 (CVal 8 (SOff 528 0))];
YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 ra_saved_chunks;
YP09.mkRegion (Some 10%nat) 0 48 40 44 (ra_raw_ro_chunks ++ [YP09.mkChunk 40 (CVal 4 (SOff n 0))]) ].
Definition ss_XX : sstate := Eval vm_compute in
mkSS 4288 [SLit 0; SOff 1389 0; SOff 2 (-320); SOff 3 0; SOff 4 0; SOff 1390 0; SOff 1391 0; SOff 1392 0; SOff 2 0; SOff 2 (-320); SOff 1393 0; SOff 1394 0; SOff 1395 0; SOff 1396 0; SOff 1397 0; SOff 1398 0; SOff 1399 0; SOff 1400 0; SOff 516 0; SOff 1401 0; SOff 529 0; SOff 1402 0; SOff 1403 0; SOff 1404 0; SOff 1405 0; SOff 1406 0; SOff 516 0; SOff 1407 0; SOff 1408 0; SOff 1409 0; SOff 1410 0; SOff 1411 0] (ra_X_memX 1412) None (mkFacts ra_X_atoms [] ra_X_alias).
Definition ss_X1X : sstate := Eval vm_compute in
mkSS 4280 [SLit 0; SOff 1359 0; SOff 2 (-320); SOff 3 0; SOff 4 0; SOff 1360 0; SOff 1361 0; SOff 1362 0; SOff 2 0; SOff 2 (-320); SOff 1363 0; SOff 1364 0; SOff 1365 0; SOff 1366 0; SOff 1367 0; SOff 1368 0; SOff 1369 0; SOff 1370 0; SOff 516 0; SOff 1371 0; SOff 529 0; SOff 1372 0; SOff 1373 0; SOff 1374 0; SOff 1375 0; SOff 1376 0; SOff 516 0; SOff 1377 0; SOff 1378 0; SOff 1379 0; SOff 1380 0; SOff 1381 0] (ra_X_memX 1382) None (mkFacts ra_X_atoms [] ra_X_alias).
Record raxx := mkRAXX { x_pf : Z; x_Sg : list Z; x_IMG : list Z; x_LCT : list Z }.
Definition rx_ganim (cx : racx) : bool := YO07.flag (c_rattr cx) 1.
Definition rx_ne (cx : racx) : Z := num_eff (rx_ganim cx) (c_fattr cx) (c_sgct cx) (c_slct cx) (c_tidx cx).
Definition rx_iclen (cx : racx) : Z := YO07.calcInitCodeLen (rx_ne cx).
Definition rx_idl (cx : racx) : Z := 2 ^ (rx_iclen cx - 1).
Definition rx_pix (cx : racx) (IMG : list Z) : list Z := if YO07.flag (c_fattr cx) 2 then YO07.interlace (c_w cx) IMG else IMG.
Definition rx_gce (cx : racx) : list Z :=
if rx_ganim cx || YO07.flag (c_fattr cx) 1
then [33; 249; 4; (if YO07.flag (c_fattr cx) 1 then Z.lor (c_disp cx mod 256) 1 else c_disp cx mod 256)] ++ YO07.u16le (c_delay cx) ++
[(if YO07.flag (c_fattr cx) 1 then c_tidx cx else 0); 0]
else [].
Definition rx_pkl (cx : racx) : Z := if negb (c_slct cx =? 0) then 128 + (YO07.pal_pow (c_slct cx) - 1) else 0.
Definition rx_packed (cx : racx) : Z := rx_pkl cx + (if YO07.flag (c_fattr cx) 2 then 64 else 0).
Definition rx_hdr (cx : racx) : list Z :=
[44] ++ YO07.u16le (c_left cx) ++ YO07.u16le (c_top cx) ++ YO07.u16le (c_w cx) ++ YO07.u16le (c_h cx) ++ [rx_packed cx].
Definition rx_lctb (cx : racx) (LCT : list Z) : list Z :=
if negb (c_slct cx =? 0) then firstn (Z.to_nat (c_slct cx * 3)) LCT ++ YO07.zeros (((2 ^ YO07.pal_pow (c_slct cx) - c_slct cx) * 3) mod 65536) else [].
Definition rx_model (cx : racx) (xx : raxx) : Z * list Z :=
YO07.raw_addframe (rx_ganim cx) (c_sgct cx) (rc_int (c_rcur cx)) (x_IMG xx) (c_fattr cx) (c_w cx) (c_h cx) (c_top cx) (c_left cx)
(c_delay cx) (c_slct cx) (x_LCT xx) (c_disp cx) (c_tidx cx).
Lemma rx_model_prev : forall cx xx, rc_int (c_rcur cx) <> 0 -> rc_int (c_rcur cx) <> 6 -> rx_model cx xx = (rc_int (c_rcur cx), []).
Proof.
intros cx xx H0 H6. unfold rx_model, YO07.raw_addframe, YO07.R_OK, YO07.R_PENDING.
destruct (Z.eqb_spec (rc_int (c_rcur cx)) 0) as [E|_]; [contradiction|]. destruct (Z.eqb_spec (rc_int (c_rcur cx)) 6) as [E|_]; [contradiction|]. reflexivity.
Qed.
Lemma rx_model_badlct : forall cx xx, (c_rcur cx = 0 \/ c_rcur cx = 6) -> 256 < c_slct cx -> rx_model cx xx = (-1, []).
Proof.
intros cx xx Hr Hs. unfold rx_model, YO07.raw_addframe, YO07.R_OK, YO07.R_PENDING, YO07.R_ERROR.
replace (256 <? c_slct cx) with true by (symmetry; apply Z.ltb_lt; exact Hs). unfold rc_int. destruct Hr as [-> | ->]; reflexivity.
Qed.
Lemma rx_model_lzw : forall cx xx, (c_rcur cx = 0 \/ c_rcur cx = 6) -> c_slct cx <= 256 ->
rx_model cx xx =
match YO07.lzw_stream (rx_idl cx) (rx_iclen cx) (rx_pix cx (x_IMG xx)) with
| None => (5, [])
| Some raster => (0, rx_gce cx ++ rx_hdr cx ++ rx_lctb cx (x_LCT xx) ++ [rx_iclen cx - 1] ++ raster)
end.
Proof.
intros cx xx Hr Hs. unfold rx_model, YO07.raw_addframe.
assert (E1 : negb (rc_int (c_rcur cx) =? YO07.R_OK) && negb (rc_int (c_rcur cx) =? YO07.R_PENDING) = false)
by (unfold rc_int, YO07.R_OK, YO07.R_PENDING; destruct Hr as [-> | ->]; reflexivity).
rewrite E1. replace (256 <? c_slct cx) with false by (symmetry; apply Z.ltb_ge; lia).
unfold rx_idl, rx_iclen, rx_ne, num_eff, rx_pix, rx_gce, rx_hdr, rx_packed, rx_pkl, rx_lctb, rx_ganim.
destruct (YO07.lzw_stream _ _ _); [| reflexivity]. unfold YO07.R_OK, YO07.R_EINDEX. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma rx_gce_length : forall cx, (length (rx_gce cx) <= 8)%nat.
Proof. intros cx. unfold rx_gce. destruct (_ || _); cbn; lia. Qed.
Lemma rx_hdr_length : forall cx, length (rx_hdr cx) = 10%nat.
Proof. intros cx. reflexivity. Qed.
Lemma np2_aux_le8' : forall fuel n p, 0 <= p <= 8 -> n <= 256 -> 0 <= YO07.np2_aux fuel n p <= 8.
Proof.
induction fuel as [|fuel IH]; intros n p Hp Hn; cbn [YO07.np2_aux]; [lia|].
destruct (Z.ltb_spec (2 ^ p) n); [|lia].
assert (p < 8).
{ destruct (Z_lt_le_dec p 8); [lia|]. assert (2 ^ 8 <= 2 ^ p) by (apply Z.pow_le_mono_r; lia). change (2 ^ 8) with 256 in *. lia. }
apply IH; lia.
Qed.
Lemma rx_pal_pow_range : forall s, s <= 256 -> 1 <= YO07.pal_pow s <= 8.
Proof. intros s Hs. unfold YO07.pal_pow, YO07.calcNextPower2Ex. pose proof (np2_aux_le8' 17 s 0 ltac:(lia) Hs). lia. Qed.
Lemma np2_aux_ge' : forall fuel n p, 0 <= p -> n <= 2 ^ (p + Z.of_nat fuel) -> n <= 2 ^ YO07.np2_aux fuel n p.
Proof.
induction fuel as [|fuel IH]; intros n p Hp Hn; cbn [YO07.np2_aux].
- rewrite Z.add_0_r in Hn. exact Hn.
- destruct (Z.ltb_spec (2 ^ p) n); [apply IH; [lia|] | lia].
replace (p + 1 + Z.of_nat fuel) with (p + Z.of_nat (S fuel)) by lia. exact Hn.
Qed.
Lemma rx_pal_pow_bounds : forall s, s <= 256 -> s <= 2 ^ YO07.pal_pow s <= 256.
Proof.
intros s Hs. split.
- unfold YO07.pal_pow, YO07.calcNextPower2Ex.
pose proof (np2_aux_ge' 17 s 0 ltac:(lia) ltac:(cbn; lia)) as G1.
assert (2 ^ YO07.np2_aux 17 s 0 <= 2 ^ Z.max 1 (YO07.np2_aux 17 s 0)) by (apply Z.pow_le_mono_r; lia). lia.
- change 256 with (2 ^ 8). apply Z.pow_le_mono_r; [lia|]. apply rx_pal_pow_range. exact Hs.
Qed.
Lemma rx_lctb_length : forall cx LCT, 0 <= c_slct cx <= 256 -> Z.of_nat (length (rx_lctb cx LCT)) <= 768.
Proof.
intros cx LCT [Hs0 Hs]. unfold rx_lctb. destruct (Z.eqb_spec (c_slct cx) 0) as [E|NE]; cbn [negb]; [cbn; lia|].
rewrite length_app, length_firstn. unfold YO07.zeros. rewrite repeat_length.
pose proof (rx_pal_pow_bounds (c_slct cx) Hs) as [Hp1 Hp2].
rewrite (Z.mod_small) by lia. lia.
Qed.
Definition ra_EX (cx : racx) (xx : raxx) (E : env) : Prop := ra_E cx E /\ ew E 56 = Z_to_bv 64 (x_pf xx).
Lemma ra_EX_E : forall cx xx E, ra_EX cx xx E -> ra_E cx E.
Proof. intros cx xx E [H _]. exact H. Qed.
Lemma ra_EX_havoc : forall cx xx E N vs, (530 <= N)%nat -> ra_EX cx xx E -> ra_EX cx xx (havoc E N vs).
Proof.
intros cx xx E N vs HN [H H56]. split; [exact (ra_E_havoc cx E N vs HN H)|]. rewrite ew_havoc_old by lia. exact H56.
Qed.
Lemma ra_EX_ewset : forall cx xx E n w, (530 <= n)%nat -> ra_EX cx xx E -> ra_EX cx xx (ewset E n w).
Proof.
intros cx xx E n w HN [(AG & EX & E516 & E528 & E529 & HEI) H56]. unfold ra_EX, ra_E. rewrite !ew_ewset_other by lia.
split; [|exact H56]. split; [intros m Hm; rewrite ew_ewset_other by lia; apply AG; exact Hm|].
split; [intros j Hj; rewrite ew_ewset_other by lia; apply EX; exact Hj|].
split; [exact E516|]. split; [exact E528|]. split; [exact E529|]. apply img_env_ewset_hi; [exact HEI | unfold A_LIM; lia].
Qed.
Section c.
Variable K : asink_syms.
Variable MT : ameter_ops.
Variable XN : xnums.
Definition ra_baseX (B : asyms) (CTX : list (list Z)) (cx : racx) (xx : raxx) : Prop :=
afn_pre SEGS B TRAWADD_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) (c_ch cx) /\
spZ (c_regs cx) mod 32 = 0 /\
In (raZ (c_regs cx) :: spine (c_ch cx)) CTX /\ Z.of_nat (length (frames (c_S cx))) <= 8 /\
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (c_W cx)) (c_mem cx)) /\
getr (c_regs cx) 10 = w64 (c_raw cx) /\ getr (c_regs cx) 11 = w64 (c_cfp cx) /\
(In (c_cid cx, c_pos cx) (frames (c_S cx)) /\ 0 <= c_cid cx /\ frame_addr (c_ly cx) (c_cid cx) (c_pos cx) mod 8 = 0 /\
frame_addr (c_ly cx) (c_cid cx) (c_pos cx) <= c_cfp cx /\ c_cfp cx + 40 <= frame_addr (c_ly cx) (c_cid cx) (c_pos cx) + fs_frame_bytes (c_cid cx) /\
c_cfp cx mod 8 = 0 /\ range_addressable (aview SEGS (w_H (c_W cx)) (c_mem cx)) SHADOW_OFF (c_cfp cx) 40) /\
obj_at SEGS (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_cfp cx) LAY_RawFrameConfig
[c_lct cx; c_img cx; c_fattr cx; c_w cx; c_h cx; c_top cx; c_left cx; c_delay cx; c_slct cx; c_disp cx; c_tidx cx] /\
obj_at SEGS (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_raw cx) LAY_Raw
[c_wfn cx; c_g cx; c_gct cx; c_rattr cx; c_Wd cx; c_Hd cx; c_sgct cx; c_loops cx; c_rcur cx] /\
c_sgct cx <= 256 /\
val_mem SEGS (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_g cx + 56) 8 (c_hw cx) /\
val_mem SEGS (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_g cx + 64) 8 (c_ctx cx) /\ 0 <= c_ctx cx < 2 ^ 64 /\
val_mem SEGS (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_g cx + 80) 8 (x_pf xx) /\
1 <= c_w cx /\ 1 <= c_h cx /\ c_w cx * c_h cx <= 100000000 /\ c_w cx * c_h cx <= c_Nimg cx /\
Permutation (ablocks B (c_ly cx) (c_S cx)) ((c_raw cx, RAW_SIZE) :: (c_g cx, CGIF_SIZE) :: (c_img cx, c_Nimg cx) :: c_rest cx) /\
(0 < c_slct cx <= 256 -> exists Nl rest', Permutation (c_rest cx) ((c_lct cx, Nl) :: rest') /\ 3 * c_slct cx <= Nl) /\
st_nev (c_S cx) + EV_RAWADD <= EV_MAX /\ blocks_bytes (c_S cx) + LIVE_RAWADD <= LIVE_MAX /\
(forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (c_E0 cx) n = getr (c_regs cx) r) /\
(forall j, (j < 24)%nat -> ew (c_E0 cx) (32 + j) = Z_to_bv 64 (nth j (ra_vals cx) 0)) /\
bv_unsigned (ew (c_E0 cx) 2) = spZ (c_regs cx) /\
(0 <= c_wfn cx < 2 ^ 64 /\ c_wfn cx mod 2 = 0) /\ 0 <= c_hw cx < 2 ^ 64 /\
twcbF_spec SEGS K B (c_wfn cx) /\ c_uar cx = as_uar_cell B /\
ew (c_E0 cx) 56 = Z_to_bv 64 (x_pf xx) /\ x_pf xx <> 0 /\ In (x_pf xx, FILE_BLOCK) (c_rest cx) /\
asink_at SEGS K (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_md cx) (x_pf xx) (x_Sg xx) /\
Z.of_nat (length (x_Sg xx)) + FRAME_OUT (c_w cx * c_h cx) <= SINK_MAX /\
garr8 SEGS (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_img cx) (x_IMG xx) /\ Z.of_nat (length (x_IMG xx)) = c_w cx * c_h cx /\
(0 < c_slct cx <= 256 -> garr8 SEGS (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_lct cx) (x_LCT xx) /\ 3 * c_slct cx <= Z.of_nat (length (x_LCT xx))) /\
(0 < c_slct cx <= 256 -> x_pf xx + FILE_BLOCK <= c_lct cx \/ c_lct cx + 3 * c_slct cx <= x_pf xx) /\
mo_ok MT (c_S cx) (xm_rawadd XN (c_w cx * c_h cx)).
Definition ra_postX (B : asyms) (cx : racx) (xx : raxx) : world SEGS -> config -> Prop :=
apost_base SEGS B TRAWADD_STK ((c_raw cx + 40, c_raw cx + 44) :: asink_fp (x_pf xx)) (c_regs cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) EV_RAWADD
(fun ly' S' W' regs' mem' md' => exists res rcur' : Z,
getr regs' 10 = w64 res /\ 0 <= res < 2 ^ 64 /\
obj_at SEGS (mrestrict (w_H W') mem') (c_raw cx) LAY_Raw
[c_wfn cx; c_g cx; c_gct cx; c_rattr cx; c_Wd cx; c_Hd cx; c_sgct cx; c_loops cx; rcur'] /\
Permutation (ablocks B ly' S') (ablocks B (c_ly cx) (c_S cx)) /\
(exists code bytes, rx_model cx xx = (code, bytes) /\ Z_to_bv 64 res = Z_to_bv 64 code /\ rcur' = code mod 2 ^ 32 /\
asink_at SEGS K (mrestrict (w_H W') mem') md' (x_pf xx) (x_Sg xx ++ bytes) /\
Z.of_nat (length bytes) <= FRAME_OUT (c_w cx * c_h cx)) /\
mo_le MT (c_S cx) S' (xn_rawadd XN (c_w cx * c_h cx))).
Definition ra_fromX0 (B : asyms) (CTX : list (list Z)) (ss : sstate)
(INV : racx -> raxx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop) : Prop :=
forall (cx : racx) (xx : raxx) (E : env) (k : Z) ly3 S3 W3 (ms3 : machine_state) md3,
ra_baseX B CTX cx xx -> ra_EX cx xx E ->
ajournal SEGS B TRAWADD_STK (spZ (c_regs cx)) [(c_raw cx + 40, c_raw cx + 44)] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(1, c_fpos cx)] ly3 S3 W3 (ms_mem ms3) md3 k ->
frames S3 = (1, c_fpos cx) :: frames (c_S cx) ->
INV cx xx E k ly3 S3 W3 ms3 md3 ->
st_ok_pi SEGS VAL E ss (restrict (w_H W3) ms3) ->
SRr SEGS W3 (mkCfg ms3 md3) (ra_postX B cx xx).
Definition ra_fromX1 (B : asyms) (CTX : list (list Z)) (ss : sstate)
(INV : racx -> raxx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop) : Prop :=
forall (cx : racx) (xx : raxx) (E : env) (k : Z) ly3 S3 W3 (ms3 : machine_state) md3,
ra_baseX B CTX cx xx -> ra_EX cx xx E ->
ajournal SEGS B TRAWADD_STK (spZ (c_regs cx)) ((c_raw cx + 40, c_raw cx + 44) :: asink_fp (x_pf xx)) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(1, c_fpos cx)] ly3 S3 W3 (ms_mem ms3) md3 k ->
frames S3 = (1, c_fpos cx) :: frames (c_S cx) ->
INV cx xx E k ly3 S3 W3 ms3 md3 ->
st_ok_pi SEGS VAL E ss (restrict (w_H W3) ms3) ->
SRr SEGS W3 (mkCfg ms3 md3) (ra_postX B cx xx).
Definition XB (cx : racx) : Prop := c_rcur cx = 0 \/ c_rcur cx = 6.
Definition XC (cx : racx) : Prop := XB cx /\ 0 <= c_slct cx <= 256.
Definition INV_0X (B : asyms) (kmax : Z) : racx -> raxx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx xx E k ly3 S3 W3 ms3 md3 => INV_0 B kmax cx E k ly3 S3 W3 ms3 md3 /\ mo_le MT (c_S cx) S3 0.
Definition INV_B8X (B : asyms) : racx -> raxx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx xx E k ly3 S3 W3 ms3 md3 => INV_0 B 1 cx E k ly3 S3 W3 ms3 md3 /\ XB cx /\ mo_le MT (c_S cx) S3 0.
Definition INV_CX (B : asyms) : racx -> raxx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx xx E k ly3 S3 W3 ms3 md3 => INV_0 B 1 cx E k ly3 S3 W3 ms3 md3 /\ XC cx /\ mo_le MT (c_S cx) S3 0.
Definition INV_XX (B : asyms) (N : nat) : racx -> raxx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx xx E k ly3 S3 W3 ms3 md3 => INV_X B cx E k ly3 S3 W3 ms3 md3 /\
exists code bytes, rx_model cx xx = (code, bytes) /\ ew E (N + 13) = Z_to_bv 64 code /\ bv_unsigned (ew E (N + 23)) mod 2 ^ 32 = code mod 2 ^ 32 /\
asink_at SEGS K (mrestrict (w_H W3) (ms_mem ms3)) md3 (x_pf xx) (x_Sg xx ++ bytes) /\
Z.of_nat (length bytes) <= FRAME_OUT (c_w cx * c_h cx) /\
mo_le MT (c_S cx) S3 (xn_rawadd XN (c_w cx * c_h cx)).
Lemma INV_0X_havoc : forall B kmax cx xx E N vs k ly3 S3 W3 ms3 md3,
INV_0X B kmax cx xx E k ly3 S3 W3 ms3 md3 -> INV_0X B kmax cx xx (havoc E N vs) k ly3 S3 W3 ms3 md3.
Proof. intros; assumption. Qed.
End c.
End b.
End a.
