(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeEF.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeSpec.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.TopUbsan.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Glue.Top04.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AMainEntry.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ABoot.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.ShapeAlg.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.SpinAlg.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.BothPlanImages.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS.AsanInit.
From Corelib Require Import PrimInt63 PrimString.
Fixpoint flush_loop (n : nat) (acc : int) : int :=
  match n with
  | O => acc
  | S k => flush_loop k (PrimString.length (PrimString.make 16777211%uint63 acc))
  end.
Lemma gc_flush : flush_loop 150 0%uint63 = 16777211%uint63.
Proof. vm_cast_no_check (@eq_refl int 16777211%uint63). Qed.
