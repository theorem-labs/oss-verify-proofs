(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes StoreFast FP ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numkit2b Sj_stage2_numkit3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Definition numr_entry_k (E : s2env) (Q : machine_state -> Prop) (CP : Z)  : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs6 xs8 xs9 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; C8 (Z_to_bv 64 (e_TAPE E)); C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_IDX E + 4)); CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304]
         ([]) fc m1 ->
    evt bsegs Q (S2R E 0xb72b4 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (Z.lxor CP 18446744073709551615)) (Z_to_bv 64 (SHA (e_FF E))) xs4 (Z_to_bv 64 (2147450880)) xs6 (Z_to_bv 64 (CP)) xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numr_frac_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) (neg p : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs8 xs9 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; C8 (Z_to_bv 64 (e_TAPE E)); C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_IDX E + 4)); CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304]
         ([]) fc m1 ->
    evt bsegs Q (S2R E 0xb768c xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (CP + p)) (Z_to_bv 64 (CP + neg)) xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA CP)) (Z_to_bv 64 (CP)) xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numr_ftail_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) (neg p d : Z) : Prop :=
  forall xra xt0 xt1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j128 j144 j152 j160 j200 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; C8 (Z_to_bv 64 (e_FF E)); CB 8 j128; C8 (Z_to_bv 64 (CP + p + 1)); CB 8 j144; CB 8 j152; CB 8 j160; C8 (Z_to_bv 64 (SHA CP)); C8 (Z_to_bv 64 (e_TAPE E)); C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_IDX E + 4)); CB 8 j200; C8 (Z_to_bv 64 (CP)); CB 8 j288; CB 8 j304]
         ([]) fc m1 ->
    evt bsegs Q (S2R E 0xb9318 xra xt0 xt1 (Z_to_bv 64 (d)) (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (CP + p)) (Z_to_bv 64 (CP + neg)) xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numr_ftail2_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) (neg p d : Z) : Prop :=
  forall xra xt1 xa2 xa3 xa4 xa5 xa7 xs2 xs4 xs8 xs9 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; C8 (Z_to_bv 64 (e_TAPE E)); C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_IDX E + 4)); CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304]
         ([]) fc m1 ->
    evt bsegs Q (S2R E 0xb93fc xra (Z_to_bv 64 (CP + p + 1)) xt1 (Z_to_bv 64 (d)) (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (CP + p)) (Z_to_bv 64 (CP + neg)) xa2 xa3 xa4 xa5 (Z_to_bv 64 (e_THIS E)) xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA CP)) (Z_to_bv 64 (CP)) xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numr_scan_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) (neg p e0 : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa3 xa5 xa7 xs2 xs4 xs8 xs9 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; C8 (Z_to_bv 64 (e_TAPE E)); C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_IDX E + 4)); CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304]
         ([]) fc m1 ->
    evt bsegs Q (S2R E 0xb94b4 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (CP + p)) (Z_to_bv 64 (CP + neg)) (Z_to_bv 64 (B (crs (rtxt E)) p)) xa3 (Z_to_bv 64 (e0)) xa5 (Z_to_bv 64 (e_THIS E)) xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA CP)) (Z_to_bv 64 (CP)) xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numr_expd_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) (neg q0 e0 : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa3 xa5 xa6 xa7 xs2 xs4 xs8 xs9 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; C8 (Z_to_bv 64 (e_TAPE E)); C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_IDX E + 4)); CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304]
         ([]) fc m1 ->
    evt bsegs Q (S2R E 0xb950c xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 (Z_to_bv 64 (CP + neg)) (Z_to_bv 64 (CP + q0)) xa3 (Z_to_bv 64 (e0)) xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA CP)) (Z_to_bv 64 (CP)) xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numr_eadd_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) (neg p e0 v : Z) : Prop :=
  forall xra xt0 xt2 xa2 xa3 xa5 xa6 xa7 xs2 xs4 xs8 xs9 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; C8 (Z_to_bv 64 (e_TAPE E)); C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_IDX E + 4)); CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304]
         ([]) fc m1 ->
    evt bsegs Q (S2R E 0xb9708 xra xt0 (Z_to_bv 64 (v)) xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (CP + p)) (Z_to_bv 64 (CP + neg)) xa2 xa3 (Z_to_bv 64 (e0)) xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA CP)) (Z_to_bv 64 (CP)) xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numr_flt_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) (neg p : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs8 xs9 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; C8 (Z_to_bv 64 (e_TAPE E)); C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_IDX E + 4)); CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304]
         ([]) fc m1 ->
    evt bsegs Q (S2R E 0xb9720 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (CP + p)) (Z_to_bv 64 (CP + neg)) xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA CP)) (Z_to_bv 64 (CP)) xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numr_int_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) (neg p : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa7 xs2 xs4 xs8 xs9 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; C8 (Z_to_bv 64 (e_TAPE E)); C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_IDX E + 4)); CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304]
         ([]) fc m1 ->
    evt bsegs Q (S2R E 0xb95a8 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (CP + p)) (Z_to_bv 64 (CP + neg)) xa2 xa3 xa4 xa5 (Z_to_bv 64 (e_THIS E)) xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA CP)) (Z_to_bv 64 (CP)) xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numr_range_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) (neg : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs8 xs9 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; C8 (Z_to_bv 64 (e_TAPE E)); C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_IDX E + 4)); CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304]
         ([]) fc m1 ->
    evt bsegs Q (S2R E 0xb97e0 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA CP)) (Z_to_bv 64 (CP)) xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numr_cmp_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) (neg e : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs2 xs4 xs8 xs9 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; C8 (Z_to_bv 64 (e_TAPE E)); C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_IDX E + 4)); CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304]
         ([]) fc m1 ->
    evt bsegs Q (S2R E 0xb9800 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 (Z_to_bv 64 (e)) xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA CP)) (Z_to_bv 64 (CP)) xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numr_cmpslow_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) (neg e : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs2 xs4 xs8 xs9 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; C8 (Z_to_bv 64 (e_TAPE E)); C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_IDX E + 4)); CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304]
         ([]) fc m1 ->
    evt bsegs Q (S2R E 0xba71c xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 (Z_to_bv 64 (e)) xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA CP)) (Z_to_bv 64 (CP)) xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numr_write_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) (neg : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs8 xs9 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; C8 (Z_to_bv 64 (e_TAPE E)); C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_IDX E + 4)); CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304]
         ([]) fc m1 ->
    evt bsegs Q (S2R E 0xbcb48 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA CP)) (Z_to_bv 64 (CP)) xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numr_fin_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) (r tw : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs4 xs8 xs9 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; C8 (Z_to_bv 64 (e_TAPE E)); C8 (Z_to_bv 64 (e_TAPE E + 8 * tw)); C8 (Z_to_bv 64 (e_IDX E + 4)); CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304]
         ([]) fc m1 ->
    evt bsegs Q (S2R E 0xbcbe0 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 (Z_to_bv 64 (r)) xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA CP)) (Z_to_bv 64 (CP)) xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numr_slowcall_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) : Prop :=
  forall xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs8 xs9 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; C8 (Z_to_bv 64 (e_TAPE E)); C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_IDX E + 4)); CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304]
         ([]) fc m1 ->
    evt bsegs Q (S2R E 0xee144 (Z_to_bv 64 (0xbda54)) xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (CP)) (Z_to_bv 64 (e_spa E + 304)) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (CP)) (Z_to_bv 64 (SHA (e_FF E))) xs4 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA CP)) (Z_to_bv 64 (CP)) xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numr_fbcall_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) : Prop :=
  forall xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs8 xs9 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; C8 (Z_to_bv 64 (e_TAPE E)); C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_IDX E + 4)); CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304]
         ([]) fc m1 ->
    evt bsegs Q (S2R E 0xee248 (Z_to_bv 64 (0xbe0fc)) xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (CP)) (Z_to_bv 64 (e_spa E + 304)) xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA CP)) (Z_to_bv 64 (CP)) xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numr_slowret_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) (r : Z) (v : word) : Prop :=
  forall xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs8 xs9 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j200 j272 j288 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; C8 (Z_to_bv 64 (e_TAPE E)); C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_IDX E + 4)); CB 8 j200; CB 8 j272; CB 8 j288; C8 v]
         ([]) fc m1 ->
    evt bsegs Q (S2R E 0xbda54 (Z_to_bv 64 (0xbda54)) xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (r)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (CP)) (Z_to_bv 64 (SHA (e_FF E))) xs4 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA CP)) (Z_to_bv 64 (CP)) xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numr_fbret_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) (r : Z) (v : word) : Prop :=
  forall xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs8 xs9 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j200 j272 j288 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; C8 (Z_to_bv 64 (e_TAPE E)); C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_IDX E + 4)); CB 8 j200; CB 8 j272; CB 8 j288; C8 v]
         ([]) fc m1 ->
    evt bsegs Q (S2R E 0xbe0fc (Z_to_bv 64 (0xbe0fc)) xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (r)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA CP)) (Z_to_bv 64 (CP)) xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

