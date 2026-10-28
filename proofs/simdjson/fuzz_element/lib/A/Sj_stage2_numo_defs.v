(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_numkit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Definition numo_scan_k (E : s2env) (Q : machine_state -> Prop) (s : st) (neg p : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs9 xs11 xt3 xt4 xt5 xt6
         j64 j72 j80 j96 j104 j112 j120 j128 j136 j144 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272]
         (scopes s) fc m1 ->
    evt asegs Q (S2R E 0xc33e4 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (e_BUF E + (e_off E (k s) + neg))) (Z_to_bv 64 (e_BUF E + p)) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (depth s)) xs6 xs7 (Z_to_bv 64 (e_BUF E)) xs9 (Z_to_bv 64 (e_THIS E + 56)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numo_dot_k (E : s2env) (Q : machine_state -> Prop) (s : st) (neg p : Z) : Prop :=
  forall xra xt0 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs9 xs11 xt4 xt5 xt6
         j64 j72 j80 j96 j104 j112 j120 j128 j136 j144 j168 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); CB 8 j168; C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272]
         (scopes s) fc m1 ->
    evt asegs Q (S2R E 0xc2b88 xra xt0 (Z_to_bv 64 (B (e_bs E) p)) xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (e_BUF E + (e_off E (k s) + neg))) (Z_to_bv 64 (e_BUF E + p)) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (depth s)) xs6 xs7 (Z_to_bv 64 (e_BUF E)) xs9 (Z_to_bv 64 (e_THIS E + 56)) xs11 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))) xt4 xt5 xt6 F fc m1).

Definition numo_frac_k (E : s2env) (Q : machine_state -> Prop) (s : st) (neg p : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs9 xs11 xt3 xt4 xt5 xt6
         j64 j72 j80 j96 j104 j112 j120 j128 j136 j144 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272]
         (scopes s) fc m1 ->
    evt asegs Q (S2R E 0xc2b94 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (e_BUF E + (e_off E (k s) + neg))) (Z_to_bv 64 (e_BUF E + p)) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (depth s)) xs6 xs7 (Z_to_bv 64 (e_BUF E)) xs9 (Z_to_bv 64 (e_THIS E + 56)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numo_ftail_k (E : s2env) (Q : machine_state -> Prop) (s : st) (neg p r : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa2 xa4 xa5 xa6 xa7 xs6 xs7 xs9 xs11 xt3 xt4 xt6
         j64 j72 j80 j96 j104 j112 j120 j128 j136 j144 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272]
         (scopes s) fc m1 ->
    evt asegs Q (S2R E 0xc3278 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (e_BUF E + (e_off E (k s) + neg))) (Z_to_bv 64 (e_BUF E + p)) xa2 (Z_to_bv 64 (e_BUF E + r)) xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (depth s)) xs6 xs7 (Z_to_bv 64 (e_BUF E)) xs9 (Z_to_bv 64 (e_THIS E + 56)) xs11 xt3 xt4 (Z_to_bv 64 (r - p)) xt6 F fc m1).

Definition numo_ftail2_k (E : s2env) (Q : machine_state -> Prop) (s : st) (neg p r : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs9 xs11 xt3 xt4 xt6
         j64 j72 j80 j96 j104 j112 j120 j128 j136 j144 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272]
         (scopes s) fc m1 ->
    evt asegs Q (S2R E 0xc3338 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (e_BUF E + (e_off E (k s) + neg))) (Z_to_bv 64 (e_BUF E + p)) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (depth s)) xs6 xs7 (Z_to_bv 64 (e_BUF E)) xs9 (Z_to_bv 64 (e_THIS E + 56)) xs11 xt3 xt4 (Z_to_bv 64 (r - p)) xt6 F fc m1).

Definition numo_expd_k (E : s2env) (Q : machine_state -> Prop) (s : st) (neg q0 : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa1 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs9 xs11 xt3 xt4 xt5 xt6
         j64 j72 j80 j96 j104 j112 j120 j128 j136 j144 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272]
         (scopes s) fc m1 ->
    evt asegs Q (S2R E 0xc3438 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (e_BUF E + (e_off E (k s) + neg))) xa1 (Z_to_bv 64 (e_BUF E + q0)) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (depth s)) xs6 xs7 (Z_to_bv 64 (e_BUF E)) xs9 (Z_to_bv 64 (e_THIS E + 56)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numo_flt_k (E : s2env) (Q : machine_state -> Prop) (s : st) (neg p : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs9 xs11 xt3 xt4 xt5 xt6
         j64 j72 j80 j96 j104 j112 j120 j128 j136 j144 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272]
         (scopes s) fc m1 ->
    evt asegs Q (S2R E 0xc34f8 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (e_BUF E + (e_off E (k s) + neg))) (Z_to_bv 64 (e_BUF E + p)) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (depth s)) xs6 xs7 (Z_to_bv 64 (e_BUF E)) xs9 (Z_to_bv 64 (e_THIS E + 56)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numo_int_k (E : s2env) (Q : machine_state -> Prop) (s : st) (neg p : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs9 xs11 xt3 xt4 xt5 xt6
         j64 j72 j80 j96 j104 j112 j120 j128 j136 j144 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272]
         (scopes s) fc m1 ->
    evt asegs Q (S2R E 0xc384c xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 (Z_to_bv 64 (e_BUF E + p)) (Z_to_bv 64 (SHA (e_BUF E + p))) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (depth s)) xs6 xs7 (Z_to_bv 64 (e_BUF E)) xs9 (Z_to_bv 64 (e_THIS E + 56)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numo_range_k (E : s2env) (Q : machine_state -> Prop) (s : st) (neg : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs9 xs11 xt3 xt4 xt5 xt6
         j64 j72 j80 j96 j104 j112 j120 j128 j136 j144 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272]
         (scopes s) fc m1 ->
    evt asegs Q (S2R E 0xc3590 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (depth s)) xs6 xs7 (Z_to_bv 64 (e_BUF E)) xs9 (Z_to_bv 64 (e_THIS E + 56)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numo_cmp_k (E : s2env) (Q : machine_state -> Prop) (s : st) (neg e : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs6 xs7 xs9 xs11 xt3 xt4 xt5 xt6
         j64 j72 j80 j96 j104 j112 j120 j128 j136 j144 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272]
         (scopes s) fc m1 ->
    evt asegs Q (S2R E 0xc3620 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 (Z_to_bv 64 (e)) xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (depth s)) xs6 xs7 (Z_to_bv 64 (e_BUF E)) xs9 (Z_to_bv 64 (e_THIS E + 56)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numo_write_k (E : s2env) (Q : machine_state -> Prop) (s : st) (neg : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs11 xt3 xt4 xt5 xt6
         j64 j72 j80 j96 j104 j112 j120 j128 j136 j144 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272]
         (scopes s) fc m1 ->
    evt asegs Q (S2R E 0xc3a00 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (depth s)) xs6 xs7 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (depth s)) (Z_to_bv 64 (e_THIS E + 56)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numo_fin_k (E : s2env) (Q : machine_state -> Prop) (s : st) (neg r : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs11 xt3 xt4 xt5 xt6
         j64 j72 j80 j96 j104 j112 j120 j128 j136 j144 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_TAPE E + 8 * (W s + 2))); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272]
         (scopes s) fc m1 ->
    evt asegs Q (S2R E 0xc3a50 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (r)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (depth s)) xs6 xs7 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (depth s)) (Z_to_bv 64 (e_THIS E + 56)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numo_join_k (E : s2env) (Q : machine_state -> Prop) (s : st) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs11 xt3 xt4 xt5 xt6
         j64 j72 j80 j96 j104 j112 j120 j128 j136 j144 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_TAPE E + 8 * (W s + 2))); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272]
         (scopes s) fc m1 ->
    evt asegs Q (S2R E 0xc3b10 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 (Z_to_bv 64 (1)) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (depth s)) xs6 xs7 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (depth s)) (Z_to_bv 64 (e_THIS E + 56)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numo_slowcall_k (E : s2env) (Q : machine_state -> Prop) (s : st) : Prop :=
  forall xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs11 xt3 xt4 xt5 xt6
         j64 j72 j80 j96 j104 j112 j120 j128 j136 j144 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272]
         (scopes s) fc m1 ->
    evt asegs Q (S2R E 0xe99dc (Z_to_bv 64 (0xc4428)) xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (e_BUF E + e_off E (k s))) (Z_to_bv 64 (e_spa E + 272)) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (depth s)) xs6 xs7 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (depth s)) (Z_to_bv 64 (e_THIS E + 56)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numo_fbcall_k (E : s2env) (Q : machine_state -> Prop) (s : st) : Prop :=
  forall xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs11 xt3 xt4 xt5 xt6
         j64 j72 j80 j96 j104 j112 j120 j128 j136 j144 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_SBUF E + sb s)); CB 8 j272]
         (scopes s) fc m1 ->
    evt asegs Q (S2R E 0xe9abc (Z_to_bv 64 (0xc46c4)) xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (e_BUF E + e_off E (k s))) (Z_to_bv 64 (e_spa E + 272)) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (depth s)) xs6 xs7 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (depth s)) (Z_to_bv 64 (e_THIS E + 56)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numo_slowret_k (E : s2env) (Q : machine_state -> Prop) (s : st) (r : Z) (v : word) : Prop :=
  forall xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs11 xt3 xt4 xt5 xt6
         j64 j72 j80 j96 j104 j112 j120 j128 j136 j144 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_SBUF E + sb s)); C8 v]
         (scopes s) fc m1 ->
    evt asegs Q (S2R E 0xc4428 (Z_to_bv 64 (0xc4428)) xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (r)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (depth s)) xs6 xs7 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (depth s)) (Z_to_bv 64 (e_THIS E + 56)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numo_fbret_k (E : s2env) (Q : machine_state -> Prop) (s : st) (r : Z) (v : word) : Prop :=
  forall xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs11 xt3 xt4 xt5 xt6
         j64 j72 j80 j96 j104 j112 j120 j128 j136 j144 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 (e_BUF E + e_off E (k s))); CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; C8 (Z_to_bv 64 (SHA (e_THIS E + 56))); C8 (Z_to_bv 64 (e_IDX E + 4 * (k s + 1))); C8 (Z_to_bv 64 (e_TAPE E + 8 * W s)); C8 (Z_to_bv 64 (e_SBUF E + sb s)); C8 v]
         (scopes s) fc m1 ->
    evt asegs Q (S2R E 0xc46c4 (Z_to_bv 64 (0xc46c4)) xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (r)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (depth s)) xs6 xs7 (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 (depth s)) (Z_to_bv 64 (e_THIS E + 56)) xs11 xt3 xt4 xt5 xt6 F fc m1).

