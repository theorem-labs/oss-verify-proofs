(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes StoreFast FP ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_numkit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Definition numo_frac_k (E : s2env) (Q : machine_state -> Prop) (s : st) (neg p : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs8 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j120 j128 j144 j152 j160 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; C8 (Z_to_bv 64 (SHA (e_BUF E + e_off E (k s)))); CB 8 j120; CB 8 j128; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j144; CB 8 j152; CB 8 j160; C8 (Z_to_bv 64 (depth s)); C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272; CB 8 j288; CB 8 j304]
         (scopes s) fc m1 ->
    evt bsegs Q (S2R E 0xc2c44 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 (Z_to_bv 64 (e_BUF E + p)) xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_BUF E + (e_off E (k s) + neg))) xs5 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numo_ftail_k (E : s2env) (Q : machine_state -> Prop) (s : st) (neg p d : Z) : Prop :=
  forall xra xt0 xt1 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs7 xs8 xs10 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j128 j144 j152 j160 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; C8 (Z_to_bv 64 (SHA (e_BUF E + e_off E (k s)))); C8 (Z_to_bv 64 (e_FF E)); CB 8 j128; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j144; CB 8 j152; CB 8 j160; C8 (Z_to_bv 64 (depth s)); C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_SBUF E + sb s)); C8 (Z_to_bv 64 (e_BUF E + p + 1)); CB 8 j288; CB 8 j304]
         (scopes s) fc m1 ->
    evt bsegs Q (S2R E 0xc2f4c xra xt0 xt1 (Z_to_bv 64 (d)) (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 (Z_to_bv 64 (e_BUF E + p)) xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_BUF E + (e_off E (k s) + neg))) xs5 (Z_to_bv 64 (e_THIS E + 56)) xs7 xs8 (Z_to_bv 64 (e_BUF E)) xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numo_ftail2_k (E : s2env) (Q : machine_state -> Prop) (s : st) (neg p d : Z) : Prop :=
  forall xra xt0 xt1 xa0 xa2 xa3 xa4 xa5 xa7 xs2 xs5 xs7 xs8 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j120 j128 j144 j152 j160 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; C8 (Z_to_bv 64 (SHA (e_BUF E + e_off E (k s)))); CB 8 j120; CB 8 j128; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j144; CB 8 j152; CB 8 j160; C8 (Z_to_bv 64 (depth s)); C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_SBUF E + sb s)); C8 (Z_to_bv 64 (e_BUF E + p + 1)); CB 8 j288; CB 8 j304]
         (scopes s) fc m1 ->
    evt bsegs Q (S2R E 0xc3018 xra xt0 xt1 (Z_to_bv 64 (d)) (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 (Z_to_bv 64 (e_BUF E + p)) xa2 xa3 xa4 xa5 (Z_to_bv 64 (2147450880)) xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_BUF E + (e_off E (k s) + neg))) xs5 (Z_to_bv 64 (e_THIS E + 56)) xs7 xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numo_scan_k (E : s2env) (Q : machine_state -> Prop) (s : st) (neg p e0 : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa3 xa5 xa6 xa7 xs2 xs5 xs8 xs11 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j120 j128 j144 j152 j160 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; C8 (Z_to_bv 64 (SHA (e_BUF E + e_off E (k s)))); CB 8 j120; CB 8 j128; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j144; CB 8 j152; CB 8 j160; C8 (Z_to_bv 64 (depth s)); C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272; CB 8 j288; CB 8 j304]
         (scopes s) fc m1 ->
    evt bsegs Q (S2R E 0xc3324 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 (Z_to_bv 64 (e_BUF E + p)) (Z_to_bv 64 (B (e_bs E) p)) xa3 (Z_to_bv 64 (e0)) xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_BUF E + (e_off E (k s) + neg))) xs5 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 (Z_to_bv 64 (e_BUF E + e_off E (k s))) xt4 xt5 xt6 F fc m1).

Definition numo_expd_k (E : s2env) (Q : machine_state -> Prop) (s : st) (neg q0 e0 : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa1 xa3 xa5 xa6 xa7 xs2 xs5 xs8 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j120 j128 j144 j152 j160 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; C8 (Z_to_bv 64 (SHA (e_BUF E + e_off E (k s)))); CB 8 j120; CB 8 j128; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j144; CB 8 j152; CB 8 j160; C8 (Z_to_bv 64 (depth s)); C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272; CB 8 j288; CB 8 j304]
         (scopes s) fc m1 ->
    evt bsegs Q (S2R E 0xc337c xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 (Z_to_bv 64 (e_BUF E + q0)) xa3 (Z_to_bv 64 (e0)) xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_BUF E + (e_off E (k s) + neg))) xs5 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numo_eadd_k (E : s2env) (Q : machine_state -> Prop) (s : st) (neg p e0 v : Z) : Prop :=
  forall xra xt0 xt2 xa0 xa2 xa3 xa5 xa6 xa7 xs2 xs5 xs8 xs11 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j120 j128 j144 j152 j160 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; C8 (Z_to_bv 64 (SHA (e_BUF E + e_off E (k s)))); CB 8 j120; CB 8 j128; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j144; CB 8 j152; CB 8 j160; C8 (Z_to_bv 64 (depth s)); C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272; CB 8 j288; CB 8 j304]
         (scopes s) fc m1 ->
    evt bsegs Q (S2R E 0xc37c4 xra xt0 (Z_to_bv 64 (v)) xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 (Z_to_bv 64 (e_BUF E + p)) xa2 xa3 (Z_to_bv 64 (e0)) xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_BUF E + (e_off E (k s) + neg))) xs5 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 (Z_to_bv 64 (e_BUF E + e_off E (k s))) xt4 xt5 xt6 F fc m1).

Definition numo_flt_k (E : s2env) (Q : machine_state -> Prop) (s : st) (neg p : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs8 xs11 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j120 j128 j144 j152 j160 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; C8 (Z_to_bv 64 (SHA (e_BUF E + e_off E (k s)))); CB 8 j120; CB 8 j128; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j144; CB 8 j152; CB 8 j160; C8 (Z_to_bv 64 (depth s)); C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272; CB 8 j288; CB 8 j304]
         (scopes s) fc m1 ->
    evt bsegs Q (S2R E 0xc37dc xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 (Z_to_bv 64 (e_BUF E + p)) xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_BUF E + (e_off E (k s) + neg))) xs5 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 (Z_to_bv 64 (e_BUF E + e_off E (k s))) xt4 xt5 xt6 F fc m1).

Definition numo_int_k (E : s2env) (Q : machine_state -> Prop) (s : st) (neg p : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs8 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j120 j128 j144 j152 j160 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; C8 (Z_to_bv 64 (SHA (e_BUF E + e_off E (k s)))); CB 8 j120; CB 8 j128; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j144; CB 8 j152; CB 8 j160; C8 (Z_to_bv 64 (depth s)); C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272; CB 8 j288; CB 8 j304]
         (scopes s) fc m1 ->
    evt bsegs Q (S2R E 0xc3420 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 (Z_to_bv 64 (e_BUF E + p)) xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numo_range_k (E : s2env) (Q : machine_state -> Prop) (s : st) (neg : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs8 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j120 j128 j144 j152 j160 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; C8 (Z_to_bv 64 (SHA (e_BUF E + e_off E (k s)))); CB 8 j120; CB 8 j128; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j144; CB 8 j152; CB 8 j160; C8 (Z_to_bv 64 (depth s)); C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272; CB 8 j288; CB 8 j304]
         (scopes s) fc m1 ->
    evt bsegs Q (S2R E 0xc388c xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numo_cmp_k (E : s2env) (Q : machine_state -> Prop) (s : st) (neg e : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs2 xs4 xs5 xs8 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j120 j128 j144 j152 j160 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; C8 (Z_to_bv 64 (SHA (e_BUF E + e_off E (k s)))); CB 8 j120; CB 8 j128; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j144; CB 8 j152; CB 8 j160; C8 (Z_to_bv 64 (depth s)); C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272; CB 8 j288; CB 8 j304]
         (scopes s) fc m1 ->
    evt bsegs Q (S2R E 0xc394c xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 (Z_to_bv 64 (e)) xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numo_cmpslow_k (E : s2env) (Q : machine_state -> Prop) (s : st) (neg e : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs2 xs4 xs5 xs8 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j120 j128 j144 j152 j160 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; C8 (Z_to_bv 64 (SHA (e_BUF E + e_off E (k s)))); CB 8 j120; CB 8 j128; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j144; CB 8 j152; CB 8 j160; C8 (Z_to_bv 64 (depth s)); C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272; CB 8 j288; CB 8 j304]
         (scopes s) fc m1 ->
    evt bsegs Q (S2R E 0xc39a4 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 (Z_to_bv 64 (e)) xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numo_write_k (E : s2env) (Q : machine_state -> Prop) (s : st) (neg : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs8 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j120 j128 j144 j152 j160 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; C8 (Z_to_bv 64 (SHA (e_BUF E + e_off E (k s)))); CB 8 j120; CB 8 j128; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j144; CB 8 j152; CB 8 j160; C8 (Z_to_bv 64 (depth s)); C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272; CB 8 j288; CB 8 j304]
         (scopes s) fc m1 ->
    evt bsegs Q (S2R E 0xc3be4 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numo_fin_k (E : s2env) (Q : machine_state -> Prop) (s : st) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs2 xs4 xs5 xs8 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j120 j128 j144 j152 j160 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; C8 (Z_to_bv 64 (SHA (e_BUF E + e_off E (k s)))); CB 8 j120; CB 8 j128; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j144; CB 8 j152; CB 8 j160; C8 (Z_to_bv 64 (depth s)); C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_TAPE E + 8 * (W s + 2))); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272; CB 8 j288; CB 8 j304]
         (scopes s) fc m1 ->
    evt bsegs Q (S2R E 0xc3d70 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (SHA (e_THIS E + 56))) xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numo_slowcall_k (E : s2env) (Q : machine_state -> Prop) (s : st) : Prop :=
  forall xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs8 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j120 j128 j144 j152 j160 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; C8 (Z_to_bv 64 (SHA (e_BUF E + e_off E (k s)))); CB 8 j120; CB 8 j128; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j144; CB 8 j152; CB 8 j160; C8 (Z_to_bv 64 (depth s)); C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272; CB 8 j288; CB 8 j304]
         (scopes s) fc m1 ->
    evt bsegs Q (S2R E 0xee144 (Z_to_bv 64 (0xc3cc0)) xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (e_BUF E + e_off E (k s))) (Z_to_bv 64 (e_spa E + 304)) xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numo_fbcall_k (E : s2env) (Q : machine_state -> Prop) (s : st) : Prop :=
  forall xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs8 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j120 j128 j144 j152 j160 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; C8 (Z_to_bv 64 (SHA (e_BUF E + e_off E (k s)))); CB 8 j120; CB 8 j128; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j144; CB 8 j152; CB 8 j160; C8 (Z_to_bv 64 (depth s)); C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272; CB 8 j288; CB 8 j304]
         (scopes s) fc m1 ->
    evt bsegs Q (S2R E 0xee248 (Z_to_bv 64 (0xc400c)) xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (e_BUF E + e_off E (k s))) (Z_to_bv 64 (e_spa E + 304)) xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numo_slowret_k (E : s2env) (Q : machine_state -> Prop) (s : st) (r : Z) (v : word) : Prop :=
  forall xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs8 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j120 j128 j144 j152 j160 j272 j288 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; C8 (Z_to_bv 64 (SHA (e_BUF E + e_off E (k s)))); CB 8 j120; CB 8 j128; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j144; CB 8 j152; CB 8 j160; C8 (Z_to_bv 64 (depth s)); C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272; CB 8 j288; C8 v]
         (scopes s) fc m1 ->
    evt bsegs Q (S2R E 0xc3cc0 (Z_to_bv 64 (0xc3cc0)) xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (r)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numo_fbret_k (E : s2env) (Q : machine_state -> Prop) (s : st) (r : Z) (v : word) : Prop :=
  forall xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs8 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j120 j128 j144 j152 j160 j272 j288 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; C8 (Z_to_bv 64 (SHA (e_BUF E + e_off E (k s)))); CB 8 j120; CB 8 j128; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j144; CB 8 j152; CB 8 j160; C8 (Z_to_bv 64 (depth s)); C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272; CB 8 j288; C8 v]
         (scopes s) fc m1 ->
    evt bsegs Q (S2R E 0xc400c (Z_to_bv 64 (0xc400c)) xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (r)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 (Z_to_bv 64 (e_THIS E + 56)) (Z_to_bv 64 (2147450880)) xs8 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

