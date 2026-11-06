(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ImageA.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Import Layout Shadow RT_iface R_poison.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition g_REAL_cxa_atexit : Z := 0x174148.
Definition e_musl_cxa_atexit : Z := 0x1528c8.
Definition g_REAL_fflush : Z := 0x1740a0.
Definition e_musl_fflush : Z := 0x15a750.
Definition g_REAL_wcrtomb : Z := 0x174068.
Definition e_musl_wcrtomb : Z := 0x159734.
Definition g_GOT_mbstate_t_sz : Z := 0x1721e0.
Definition g_mbstate_t_sz : Z := 0x17621c.
Definition g_flags_cio : Z := 0x178eb8 + 28.
Definition g_icpt_mdmap : Z := 0x17af00.
Definition g_mdmem : Z := 0x17af08.
Definition MT_SIZE : Z := 0x38e000.

Definition MT_OFF_OUT : Z := 120 * 19001.
Definition MT_OFF_ERR : Z := 120 * 5328.
Definition Z15 : list cell :=
  [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Definition mtab_at (sp0 T : Z) (m : mem) : Prop :=
  rw_cells asegs m g_icpt_mdmap [C8 (Z_to_bv 64 g_mdmem)] /\ rw_cells asegs m g_mdmem [C8 (Z_to_bv 64 T)]
  /\ SEGTOP_A <= T /\ T + MT_SIZE <= sp0 - STACK_WIN /\ T mod 4096 = 0
  /\ rw_cells asegs m (T + MT_OFF_OUT) Z15 /\ rw_cells asegs m (T + MT_OFF_ERR) Z15.

Definition g_asan_inited : Z := 0x17c398.
Definition g_GOT_lsan_off : Z := 0x172da8.
Definition LSAN_CTR : Z := 0x6b0128 + 16.
Definition g_GOT_flags : Z := 0x172140.

Definition g_flags_dco : Z := 0x178eb8 + 96.
Definition g_GOT_verbosity : Z := 0x172198.
Definition g_verbosity : Z := 0x20b158.

Definition ixit_rt (sp0 : Z) (m : mem) : Prop :=
  rw_cells asegs m g_asan_inited [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m g_GOT_lsan_off [C8 (Z_to_bv 64 16)] /\ rw_cells asegs m LSAN_CTR [C4 (Z_to_bv 64 0)]
  /\ rw_cells asegs m g_GOT_flags [C8 (Z_to_bv 64 0x178eb8)]
  /\ rw_cells asegs m g_REAL_cxa_atexit [C8 (Z_to_bv 64 e_musl_cxa_atexit)]
  /\ rw_cells asegs m g_REAL_fflush [C8 (Z_to_bv 64 e_musl_fflush)]
  /\ rw_cells asegs m g_REAL_wcrtomb [C8 (Z_to_bv 64 e_musl_wcrtomb)]
  /\ ro_cells asegs m g_GOT_mbstate_t_sz [C8 (Z_to_bv 64 g_mbstate_t_sz)] /\ rw_cells asegs m g_mbstate_t_sz [C4 (Z_to_bv 64 8)]
  /\ rw_cells asegs m g_flags_cio [C1 (Z_to_bv 8 0)]
  /\ (exists T, mtab_at sp0 T m)

  /\ ro_cells asegs m g_flags_dco [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m g_GOT_verbosity [C8 (Z_to_bv 64 g_verbosity)] /\ rw_cells asegs m g_verbosity [C4 (Z_to_bv 64 0)]
  /\ ps_cells m.

Lemma Z15_size : Z.of_nat (cells_size Z15) = 120.
Proof. reflexivity. Qed.
