(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (G0 takes G0_stmt's new valid_launch premise and passes it to the U and UE registry tables; G0R, the same library node for the certificates of the start state with CONFIG_RSEQ, from their own library run and registry tables). *)
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require RunConst.
(* The CONFIG_RSEQ copies first: their short names are shadowed by the in-place ones below, and are used only
   through the full-path aliases after the imports. *)
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueAsmB.RunR Require Registry_Both2U Registry_Both2UE.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.LibRunR Require Both_u_57.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueAsmB.Run Require MainBoth Registry_Both2U Registry_Both2UE.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.LibRun Require Both_u_57.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module RgUR := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueAsmB.RunR.Registry_Both2U.
Module RgUER := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueAsmB.RunR.Registry_Both2UE.
Module LU57R := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.LibRunR.Both_u_57.LibRunBoth_u_57.

Lemma G0 : MainBoth.G0_stmt.
Proof.
  intros rc en inp Hva Hsp Hfit Hvl E0 K HPB HRET.
  exact (Both_u_57.LibRunBoth_u_57.g0_ok (MainBoth.RAx rc en inp Hva)
           (Registry_Both2U.ctab_Both2U inp (en_sp en) (en_draw en) Hva Hsp Hfit Hvl) (Registry_Both2UE.ctab_Both2UE inp (en_sp en) (en_draw en) Hva Hsp Hfit Hvl) E0 K HPB HRET).
Qed.

Lemma G0R : MainBoth.G0_stmtR.
Proof.
  intros rc en inp Hva Hsp Hfit Hvl E0 K HPB HRET.
  exact (LU57R.g0_ok (MainBoth.RAx rc en inp Hva)
           (RgUR.ctab_Both2U inp (en_sp en) (en_draw en) Hva Hsp Hfit Hvl) (RgUER.ctab_Both2UE inp (en_sp en) (en_draw en) Hva Hsp Hfit Hvl) E0 K HPB HRET).
Qed.
