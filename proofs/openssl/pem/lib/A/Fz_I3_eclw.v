(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout PLayout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_G_kit Fz_ckit Fz_env Fz_M_malloc Fz_M_free Fz_W5_gsi Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Definition e_eclear : Z := 0x1fd924.        (* [comment removed for export] *)
Definition ECL_LOOP : Z := 0x1fd990.        (* [comment removed for export] *)
Definition ECL_DONE : Z := 0x1fdaf8.        (* [comment removed for export] *)
Definition SITE_ecl_egsi : Z := 0x1fd970.   (* [comment removed for export] *)
Definition SITE_ecr_free1 : Z := 0x1fdab0.  (* [comment removed for export] *)
Definition SITE_ecr_free2 : Z := 0x1fdae0.  (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ECL_LNW : word := Z_to_bv 64 (-1).
(* [comment removed for export] *)
Definition ecl_W (E i : Z) : list (Z * Z) :=
  [(E + 4 * i, E + 4 * i + 4); (E + 4 * i + 64, E + 4 * i + 68); (E + 8 * i + 128, E + 8 * i + 136); (E + 8 * i + 256, E + 8 * i + 264);
   (E + 8 * i + 384, E + 8 * i + 392); (E + 4 * i + 512, E + 4 * i + 516); (E + 8 * i + 576, E + 8 * i + 584); (E + 4 * i + 704, E + 4 * i + 708);
   (E + 8 * i + 768, E + 8 * i + 776)].
(* [comment removed for export] *)
Definition ECL_SITES : list (Z * Z) := [(SITE_ecr_free1, e_eclear); (SITE_ecr_free2, e_eclear)].
Definition ECL_CALLS : list (Z * Z) :=
  [(SITE_ecr_free1, e_CRYPTO_free); (SITE_ecr_free1, e_free); (SITE_ecr_free2, e_CRYPTO_free); (SITE_ecr_free2, e_free)].

(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
