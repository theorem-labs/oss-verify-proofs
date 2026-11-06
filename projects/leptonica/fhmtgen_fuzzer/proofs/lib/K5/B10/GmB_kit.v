(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit Gm_ropkit
  LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma srai_and_nonpos : forall x, - 2^63 <= x <= 0 ->
  Z.land ((bv_signed (Z_to_bv 64 x) ≫ 63) mod 18446744073709551616) (x mod 18446744073709551616) = x mod 18446744073709551616.
Proof.
  intros x Hx. destruct (Z.eq_dec x 0) as [->|N]; [reflexivity|].
  rewrite srai63_neg by lia. change ((-1) mod 18446744073709551616) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
  change (2^64) with 18446744073709551616. apply Z.mod_mod. lia.
Qed.
Lemma srai_and_nonpos_div : forall x, - 2^63 <= x <= 0 ->
  Z.land ((bv_signed (Z_to_bv 64 x) / 9223372036854775808) mod 18446744073709551616) (x mod 18446744073709551616) = x mod 18446744073709551616.
Proof. intros x Hx. rewrite <- (srai_and_nonpos x Hx) at 2. f_equal. f_equal. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma ztobv_modM : forall e, Z_to_bv 64 (e mod 18446744073709551616) = Z_to_bv 64 e.
Proof. intros e. exact (ZBridge.Z_to_bv_mod64 e). Qed.
(* [comment removed for export] *)
Lemma srliw5_small : forall j, 0 <= j < 2^31 -> bv_swrap 32 (bv_wrap 32 j / 32) = j / 32.
Proof.
  intros j Hj. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small j) by lia.
  apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). split; [apply Z.le_trans with 0; [lia| apply Z.div_pos; lia]| apply Z.div_lt_upper_bound; lia].
Qed.

(* [comment removed for export] *)
Ltac cnb B :=
  rewrite ?Z.add_0_r;
  repeat match goal with |- context [bv_swrap 32 (bv_wrap 32 ?j / ?d) mod 18446744073709551616] =>
    rewrite (srliw_idx j d) by (clear - B; unfold hid in *; lia) end;
  repeat match goal with |- context [bv_swrap 32 ?z] =>
    rewrite (bv_swrap_small 32 z) by (change (bv_half_modulus 32) with (2^31); clear - B; unfold hid in *; lia) end;
  repeat match goal with
  | |- context [Z.land ((bv_signed (Z_to_bv 64 ?x) ≫ 63) mod 18446744073709551616) (?x mod 18446744073709551616)] =>
      rewrite (srai_and_nonpos x) by (clear - B; unfold hid in *; lia)
  | |- context [Z.land ((bv_signed (Z_to_bv 64 ?x) / 9223372036854775808) mod 18446744073709551616) (?x mod 18446744073709551616)] =>
      rewrite (srai_and_nonpos_div x) by (clear - B; unfold hid in *; lia)
  end;
  repeat match goal with |- context [?E mod 18446744073709551616] =>
    rewrite (Z.mod_small E 18446744073709551616) by (clear - B; unfold hid in *; lia) end;
  rewrite ?ztobv_modM.
(* [comment removed for export] *)
Ltac bwalk stops B := repeat (tryif at_stop stops then fail else (cnb B; awalk1)).
Ltac bwalk2 stops B := repeat (tryif at_stop stops then fail else (cnb B; cn B; awalk1)).
