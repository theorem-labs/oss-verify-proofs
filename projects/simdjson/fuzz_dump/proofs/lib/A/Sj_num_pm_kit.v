(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma shz_read_ptr : forall (m : mem) a n Ea adr, shz m a n -> a <= 8 * (Ea - 2147450880) < a + n -> adr = wa Ea ->
  ov_read_bytes asegs m adr 1 = Some [Z_to_bv 8 0].
Proof.
  intros m a n Ea adr H HE ->. pose proof (H (8 * (Ea - 2147450880)) HE) as R.
  replace (8 * (Ea - 2147450880) / 8 + 2147450880) with Ea in R by (rewrite Z.mul_comm, Z.div_mul by lia; lia). exact R.
Qed.

Ltac asan_ptr_hook :=
  match goal with
  | |- context [ov_read_bytes asegs ?m ?a 1] =>
      let Ea := addr_expr a in
      match goal with
      | SHP : (forall m', munch ?W ?m0 m' -> wmono asegs ?m0 m' -> shz m' ?a0 ?n0), MU : munch ?W ?m0 m, WM : wmono asegs ?m0 m |- _ =>
          rewrite (shz_read_ptr m a0 n0 Ea a (SHP m MU WM) ltac:(Z.div_mod_to_equations; lia) ltac:(reflexivity))
      end
  end;
  load_post.
