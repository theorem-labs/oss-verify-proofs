(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (G0 takes G0_stmt's new valid_launch premise and passes it to the U and UE registry tables; G0R, the same library node for the certificates of the start state with CONFIG_RSEQ, from their own library run and registry tables). *)
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require RunConst.
(* The CONFIG_RSEQ copies first: their short names are shadowed by the in-place ones below, and are used only
   through the full-path aliases after the imports. *)
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueAsm.RunR Require Registry_Asan2U Registry_Asan2UE.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.LibRunR Require Asan_u_57.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueAsm.Run Require MainAsan Registry_Asan2U Registry_Asan2UE.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.LibRun Require Asan_u_57.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module RgUR := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueAsm.RunR.Registry_Asan2U.
Module RgUER := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueAsm.RunR.Registry_Asan2UE.
Module LU57R := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.LibRunR.Asan_u_57.LibRunAsan_u_57.

Lemma G0 : MainAsan.G0_stmt.
Proof.
  intros rc en inp Hva Hsp Hfit Hvl E0 K HPB HRET.
  exact (Asan_u_57.LibRunAsan_u_57.g0_ok (MainAsan.RAx rc en inp Hva)
           (Registry_Asan2U.ctab_Asan2U inp (en_sp en) (en_draw en) Hva Hsp Hfit Hvl) (Registry_Asan2UE.ctab_Asan2UE inp (en_sp en) (en_draw en) Hva Hsp Hfit Hvl) E0 K HPB HRET).
Qed.

Lemma G0R : MainAsan.G0_stmtR.
Proof.
  intros rc en inp Hva Hsp Hfit Hvl E0 K HPB HRET.
  exact (LU57R.g0_ok (MainAsan.RAx rc en inp Hva)
           (RgUR.ctab_Asan2U inp (en_sp en) (en_draw en) Hva Hsp Hfit Hvl) (RgUER.ctab_Asan2UE inp (en_sp en) (en_draw en) Hva Hsp Hfit Hvl) E0 K HPB HRET).
Qed.
