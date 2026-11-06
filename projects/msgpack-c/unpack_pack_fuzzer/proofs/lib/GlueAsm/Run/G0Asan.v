(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require RunConst.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueAsm.Run Require MainAsan Registry_Asan2U Registry_Asan2UE.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.LibRun Require Asan_u_57.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma G0 : MainAsan.G0_stmt.
Proof.
  intros rc en inp Hva Hsp Hfit E0 K HPB HRET.
  exact (Asan_u_57.LibRunAsan_u_57.g0_ok (MainAsan.RAx rc en inp Hva)
           (Registry_Asan2U.ctab_Asan2U inp (en_sp en) (en_draw en) Hva Hsp Hfit) (Registry_Asan2UE.ctab_Asan2UE inp (en_sp en) (en_draw en) Hva Hsp Hfit) E0 K HPB HRET).
Qed.
