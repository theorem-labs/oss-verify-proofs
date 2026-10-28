(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface R_poison.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition g_REAL_cxa_atexit : Z := 0x181ee0.
Definition e_musl_cxa_atexit : Z := 0x160578.
Definition g_REAL_fflush : Z := 0x181e38.
Definition e_musl_fflush : Z := 0x168400.
Definition g_REAL_wcrtomb : Z := 0x181e00.
Definition e_musl_wcrtomb : Z := 0x1673e4.
Definition g_GOT_mbstate_t_sz : Z := 0x17ff60.
Definition g_mbstate_t_sz : Z := 0x183fb4.
Definition g_flags_cio : Z := 0x187178 + 28.
Definition g_icpt_mdmap : Z := 0x1891c0.
Definition g_mdmem : Z := 0x1891c8.
Definition MT_SIZE : Z := 0x38e000.

Definition MT_OFF_OUT : Z := 120 * 1245.
Definition MT_OFF_ERR : Z := 120 * 14932.
Definition Z15 : list cell :=
  [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Definition mtab_at (sp0 T : Z) (m : mem) : Prop :=
  rw_cells bsegs m g_icpt_mdmap [C8 (Z_to_bv 64 g_mdmem)] /\ rw_cells bsegs m g_mdmem [C8 (Z_to_bv 64 T)]
  /\ SEGTOP_A <= T /\ T + MT_SIZE <= sp0 - STACK_WIN /\ T mod 4096 = 0
  /\ rw_cells bsegs m (T + MT_OFF_OUT) Z15 /\ rw_cells bsegs m (T + MT_OFF_ERR) Z15.

Definition g_asan_inited : Z := 0x18a658.
Definition g_GOT_lsan_off : Z := 0x180b28.
Definition LSAN_CTR : Z := 0x6be3e8 + 16.
Definition g_GOT_flags : Z := 0x17fec0.

Definition g_flags_dco : Z := 0x187178 + 96.
Definition g_GOT_verbosity : Z := 0x17ff18.
Definition g_verbosity : Z := 0x219418.

Definition ixit_rt (sp0 : Z) (m : mem) : Prop :=
  rw_cells bsegs m g_asan_inited [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m g_GOT_lsan_off [C8 (Z_to_bv 64 16)] /\ rw_cells bsegs m LSAN_CTR [C4 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m g_GOT_flags [C8 (Z_to_bv 64 0x187178)]
  /\ rw_cells bsegs m g_REAL_cxa_atexit [C8 (Z_to_bv 64 e_musl_cxa_atexit)]
  /\ rw_cells bsegs m g_REAL_fflush [C8 (Z_to_bv 64 e_musl_fflush)]
  /\ rw_cells bsegs m g_REAL_wcrtomb [C8 (Z_to_bv 64 e_musl_wcrtomb)]
  /\ ro_cells bsegs m g_GOT_mbstate_t_sz [C8 (Z_to_bv 64 g_mbstate_t_sz)] /\ rw_cells bsegs m g_mbstate_t_sz [C4 (Z_to_bv 64 8)]
  /\ rw_cells bsegs m g_flags_cio [C1 (Z_to_bv 8 0)]
  /\ (exists T, mtab_at sp0 T m)

  /\ ro_cells bsegs m g_flags_dco [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m g_GOT_verbosity [C8 (Z_to_bv 64 g_verbosity)] /\ rw_cells bsegs m g_verbosity [C4 (Z_to_bv 64 0)]
  /\ ps_cells m.

Lemma Z15_size : Z.of_nat (cells_size Z15) = 120.
Proof. reflexivity. Qed.
