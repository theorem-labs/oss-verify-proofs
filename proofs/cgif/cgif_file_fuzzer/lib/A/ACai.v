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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition boxed (P : Prop) : Prop := P.
Ltac box H := lazymatch type of H with ?T => change T with (boxed T) in H end.
Ltac unbox := unfold boxed in *.
Ltac rwEFA := repeat match goal with H : forall c p, frame_addr ?l3 c p = frame_addr ?l c p |- context [frame_addr ?l3 _ _] =>
tryif constr_eq l3 l then fail else rewrite !H end.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition ss_set_pc (s : sstate) (pc : Z) : sstate := mkSS pc (ss_regs s) (ss_mem s) (ss_resv s) (ss_facts s).
Fixpoint list_set {A} (l : list A) (i : nat) (x : A) : list A :=
match l, i with [], _ => [] | _ :: t, O => x :: t | h :: t, S j => h :: list_set t j x end.
Definition ss_set_reg (s : sstate) (r : nat) (e : sv) : sstate := mkSS (ss_pc s) (list_set (ss_regs s) r e) (ss_mem s) (ss_resv s) (ss_facts s).
Fixpoint ss_set_regs (s : sstate) (l : list (nat * sv)) : sstate :=
match l with [] => s | (r, e) :: t => ss_set_regs (ss_set_reg s r e) t end.
Fixpoint ss_havoc_regs (s : sstate) (N : nat) (deads : list nat) : sstate :=
match deads with [] => s | r :: t => ss_havoc_regs (ss_set_reg s r (SOff N 0)) (S N) t end.
Fixpoint facts_set (fa : list (nat * afact)) (n : nat) (af : afact) : list (nat * afact) :=
match fa with [] => [(n, af)] | (m, a) :: t => if Nat.eqb m n then (m, af) :: t else (m, a) :: facts_set t n af end.
Definition ss_set_fact (s : sstate) (n : nat) (af : afact) : sstate :=
mkSS (ss_pc s) (ss_regs s) (ss_mem s) (ss_resv s) (mkFacts (facts_set (f_atoms (ss_facts s)) n af) (f_conds (ss_facts s)) (f_alias (ss_facts s))).
Definition ss_set_mem (s : sstate) (m : smem) : sstate := mkSS (ss_pc s) (ss_regs s) m (ss_resv s) (ss_facts s).
Definition ss_clear_conds (s : sstate) : sstate :=
mkSS (ss_pc s) (ss_regs s) (ss_mem s) (ss_resv s) (mkFacts (f_atoms (ss_facts s)) [] (f_alias (ss_facts s))).
Definition ss_set_facts (s : sstate) (fa : list (nat * afact)) : sstate :=
mkSS (ss_pc s) (ss_regs s) (ss_mem s) (ss_resv s) (mkFacts fa (f_conds (ss_facts s)) (f_alias (ss_facts s))).
Definition ss_A2 : sstate :=
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
r_chunks := [{| c_off := 56; YP09.c_val := CVal 8 (SOff 54 0) |}; {| c_off := 64; YP09.c_val := CVal 8 (SOff 52 0) |}; {| c_off := 80; YP09.c_val := CVal 8 (SLit 0) |}]
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
Definition ss_B8 : sstate := Eval vm_compute in ss_havoc_regs (ss_set_pc ss_A2 2204) 559 [11; 21]%nat.
Definition ss_C : sstate := Eval vm_compute in
ss_set_fact (ss_set_reg (ss_set_pc ss_B8 2232) 11 (SLit 257)) 49 (mkAF 0 256 0).
Definition ra_deads_X : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 21; 22; 23; 24; 25; 27; 28; 29; 30; 31]%bv.
Definition ra_saved_chunks : list YP09.chunk :=
[YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0));
YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Definition ra_raw_ro_chunks : list YP09.chunk :=
[YP09.mkChunk 0 (CVal 8 (SOff 53 0)); YP09.mkChunk 8 (CVal 8 (SOff 32 0)); YP09.mkChunk 16 (CVal 8 (SOff 33 0));
YP09.mkChunk 24 (CVal 4 (SOff 34 0)); YP09.mkChunk 28 (CVal 2 (SOff 35 0)); YP09.mkChunk 30 (CVal 2 (SOff 36 0));
YP09.mkChunk 32 (CVal 2 (SOff 37 0)); YP09.mkChunk 34 (CVal 2 (SOff 38 0))].
Definition ra_X_mem : smem :=
[ YP09.mkRegion (Some 529%nat) 0 16 0 0 [];
YP09.mkRegion (Some 516%nat) 0 49 0 49 [];
YP09.mkRegion (Some 516%nat) 58 128 58 128 [YP09.mkChunk 120 (CVal 8 (SOff 528 0))];
YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 ra_saved_chunks;
YP09.mkRegion (Some 10%nat) 0 48 40 44 ra_raw_ro_chunks ].
Definition ra_X_atoms : list (nat * afact) :=
[ (529%nat, mkAF 2147451392 17594333495296 2); (528%nat, HPTR 0); (516%nat, HPTR 5);
(2%nat, mkAF (2^46) (2^47) 5); (10%nat, HPTR 4); (11%nat, HPTR 3); (32%nat, HPTR 4); (40%nat, mkAF SB SB 0) ].
Definition ra_X_alias : list (sv * sv) := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 40 0), SOff 529 0)].
Definition ss_X : sstate := Eval vm_compute in
mkSS 4288 [SLit 0; SOff 1389 0; SOff 2 (-320); SOff 3 0; SOff 4 0; SOff 1390 0; SOff 1391 0; SOff 1392 0; SOff 2 0; SOff 2 (-320); SOff 1393 0; SOff 1394 0; SOff 1395 0; SOff 1396 0; SOff 1397 0; SOff 1398 0; SOff 1399 0; SOff 1400 0; SOff 516 0; SOff 1401 0; SOff 529 0; SOff 1402 0; SOff 1403 0; SOff 1404 0; SOff 1405 0; SOff 1406 0; SOff 516 0; SOff 1407 0; SOff 1408 0; SOff 1409 0; SOff 1410 0; SOff 1411 0] ra_X_mem None (mkFacts ra_X_atoms [] ra_X_alias).
Definition ss_X1 : sstate := Eval vm_compute in
mkSS 4280 [SLit 0; SOff 1359 0; SOff 2 (-320); SOff 3 0; SOff 4 0; SOff 1360 0; SOff 1361 0; SOff 1362 0; SOff 2 0; SOff 2 (-320); SOff 1363 0; SOff 1364 0; SOff 1365 0; SOff 1366 0; SOff 1367 0; SOff 1368 0; SOff 1369 0; SOff 1370 0; SOff 516 0; SOff 1371 0; SOff 529 0; SOff 1372 0; SOff 1373 0; SOff 1374 0; SOff 1375 0; SOff 1376 0; SOff 516 0; SOff 1377 0; SOff 1378 0; SOff 1379 0; SOff 1380 0; SOff 1381 0] ra_X_mem None (mkFacts ra_X_atoms [] ra_X_alias).
Record racx := mkRACX {
c_ly : alayout; c_S : astate; c_W : world SEGS; c_regs : bvmap 5 word; c_mem : word -> option byte; c_md : Model;
c_ch : list (Z * Z * Z);
c_raw : Z; c_g : Z; c_cfp : Z; c_gct : Z; c_rattr : Z; c_Wd : Z; c_Hd : Z; c_sgct : Z; c_loops : Z; c_rcur : Z; c_ctx : Z;
c_lct : Z; c_img : Z; c_fattr : Z; c_w : Z; c_h : Z; c_top : Z; c_left : Z; c_delay : Z; c_slct : Z; c_disp : Z; c_tidx : Z;
c_Nimg : Z; c_rest : list (Z * Z); c_cid : Z; c_pos : Z; c_fpos : Z;
c_wfn : Z; c_hw : Z; c_uar : Z;
c_E0 : env }.
Definition ra_vals (cx : racx) : list Z :=
[c_g cx; c_gct cx; c_rattr cx; c_Wd cx; c_Hd cx; c_sgct cx; c_loops cx; c_rcur cx; SB; c_lct cx; c_img cx; c_fattr cx;
c_w cx; c_h cx; c_top cx; c_left cx; c_delay cx; c_slct cx; c_disp cx; c_tidx cx; c_ctx cx; c_wfn cx; c_hw cx; c_uar cx].
Definition ra_base (B : asyms) (CTX : list (list Z)) (cx : racx) : Prop :=
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
val_mem SEGS (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_g cx + 80) 8 0 /\
1 <= c_w cx /\ 1 <= c_h cx /\ c_w cx * c_h cx <= 100000000 /\ c_w cx * c_h cx <= c_Nimg cx /\
Permutation (ablocks B (c_ly cx) (c_S cx)) ((c_raw cx, RAW_SIZE) :: (c_g cx, CGIF_SIZE) :: (c_img cx, c_Nimg cx) :: c_rest cx) /\
(0 < c_slct cx <= 256 -> exists Nl rest', Permutation (c_rest cx) ((c_lct cx, Nl) :: rest') /\ 3 * c_slct cx <= Nl) /\
st_nev (c_S cx) + EV_RAWADD <= EV_MAX /\ blocks_bytes (c_S cx) + LIVE_RAWADD <= LIVE_MAX /\
(forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (c_E0 cx) n = getr (c_regs cx) r) /\
(forall j, (j < 24)%nat -> ew (c_E0 cx) (32 + j) = Z_to_bv 64 (nth j (ra_vals cx) 0)) /\
bv_unsigned (ew (c_E0 cx) 2) = spZ (c_regs cx) /\
(0 <= c_wfn cx < 2 ^ 64 /\ c_wfn cx mod 2 = 0) /\ (0 <= c_hw cx < 2 ^ 64 /\ c_hw cx mod 2 = 0) /\
twcb_spec SEGS B (c_wfn cx) (c_hw cx) /\ c_uar cx = as_uar_cell B.
Definition ra_F (cx : racx) : Z := frame_addr (c_ly cx) 1 (c_fpos cx).
Definition ra_FL (cx : racx) : Z := flag_addr (c_ly cx) 1 (c_fpos cx).
Definition ra_E (cx : racx) (E : env) : Prop :=
(forall n, (n < 33)%nat -> ew E n = ew (c_E0 cx) n) /\
(forall j, (1 <= j < 24)%nat -> ew E (32 + j) = Z_to_bv 64 (nth j (ra_vals cx) 0)) /\
ew E 516 = Z_to_bv 64 (ra_F cx) /\ ew E 528 = Z_to_bv 64 (ra_FL cx) /\ ew E 529 = Z_to_bv 64 (SB + ra_F cx / 8) /\
img_env VAL A_LIM E.
Definition ra_post (B : asyms) (cx : racx) : world SEGS -> config -> Prop :=
apost_base SEGS B TRAWADD_STK [(c_raw cx + 40, c_raw cx + 44)] (c_regs cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) EV_RAWADD
(fun ly' S' W' regs' mem' md' => exists res rcur' : Z,
getr regs' 10 = w64 res /\ 0 <= res < 2 ^ 64 /\
obj_at SEGS (mrestrict (w_H W') mem') (c_raw cx) LAY_Raw
[c_wfn cx; c_g cx; c_gct cx; c_rattr cx; c_Wd cx; c_Hd cx; c_sgct cx; c_loops cx; rcur'] /\
Permutation (ablocks B ly' S') (ablocks B (c_ly cx) (c_S cx))).
Definition ra_from (B : asyms) (CTX : list (list Z)) (ss : sstate)
(INV : racx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop) : Prop :=
forall (cx : racx) (E : env) (k : Z) ly3 S3 W3 (ms3 : machine_state) md3,
ra_base B CTX cx -> ra_E cx E ->
ajournal SEGS B TRAWADD_STK (spZ (c_regs cx)) [(c_raw cx + 40, c_raw cx + 44)] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(1, c_fpos cx)] ly3 S3 W3 (ms_mem ms3) md3 k ->
frames S3 = (1, c_fpos cx) :: frames (c_S cx) ->
INV cx E k ly3 S3 W3 ms3 md3 ->
st_ok_pi SEGS VAL E ss (restrict (w_H W3) ms3) ->
SRr SEGS W3 (mkCfg ms3 md3) (ra_post B cx).
Definition INV_0 (B : asyms) (kmax : Z) : racx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 => k <= kmax /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx).
Definition INV_X (B : asyms) : racx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 => k <= EV_RAWADD /\ Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx)).
Lemma INV_0_X : forall B kmax cx E k ly3 S3 W3 ms3 md3, kmax <= EV_RAWADD ->
INV_0 B kmax cx E k ly3 S3 W3 ms3 md3 -> INV_X B cx E k ly3 S3 W3 ms3 md3.
Proof. intros B kmax cx E k ly3 S3 W3 ms3 md3 Hk [H1 H2]. split; [lia|]. rewrite H2. apply Permutation_refl. Qed.
Lemma ra_E_havoc : forall cx E N vs, (530 <= N)%nat -> ra_E cx E -> ra_E cx (havoc E N vs).
Proof.
intros cx E N vs HN (AG & EX & E516 & E528 & E529 & HEI). unfold ra_E. rewrite !ew_havoc_old by lia.
split; [|split; [|split; [exact E516 | split; [exact E528 | split; [exact E529 | apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]]]]]].
- intros n Hn. rewrite !ew_havoc_old by lia. apply AG. exact Hn.
- intros j Hj. rewrite !ew_havoc_old by lia. apply EX. exact Hj.
Qed.
Lemma INV_0_havoc : forall B kmax cx E N vs k ly3 S3 W3 ms3 md3,
INV_0 B kmax cx E k ly3 S3 W3 ms3 md3 -> INV_0 B kmax cx (havoc E N vs) k ly3 S3 W3 ms3 md3.
Proof. intros; assumption. Qed.
Lemma INV_X_havoc : forall B cx E N vs k ly3 S3 W3 ms3 md3,
INV_X B cx E k ly3 S3 W3 ms3 md3 -> INV_X B cx (havoc E N vs) k ly3 S3 W3 ms3 md3.
Proof. intros; assumption. Qed.
End d.
End b.
