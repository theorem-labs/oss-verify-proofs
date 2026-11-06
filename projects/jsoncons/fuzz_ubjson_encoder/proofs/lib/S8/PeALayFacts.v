(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import HeapIface HeapIfaceA IcptIfaceA LibIface LibIfaceAB EarInv.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PEALF.
Definition art_IL : icpt_layout :=
  ICL 0x63cf0
      2304
      0x103b8
      0x103d8
      [(0x231e0, 13); (0x232e0, 16); (0x23300, 23); (0x23340, 13); (0x23360, 60); (0x233c0, 77); (0x23440, 73); (0x234c0, 13); (0x234e0, 38); (0x23540, 70); (0x235c0, 69); (0x23640, 37); (0x236a0, 43); (0x23700, 34); (0x23760, 71); (0x237e0, 28); (0x23820, 7); (0x23880, 1); (0x238a0, 3); (0x238c0, 10); (0x238e0, 13); (0x23900, 14); (0x23920, 45); (0x23ae0, 54); (0x23b40, 52); (0x133920, 104)]
      [(0x231e0, 0x23ba0); (0x133920, 0x1339c0); (0x13dcc0, 0x13e340)]
      0x78614
      0x78610
      0x696f38
      0x63d68
      4320
      [(0x675a50, 8, 0x695d48); (0x695d70, 8, 0)]
      0x10000
      0x13a000.
Lemma art_IL_ok : as0_icpt_layout art_IL.
Proof. constructor; reflexivity. Qed.

Definition BUDGET0 : Z := 2 ^ 41.
Lemma BUDGET0_lo40 : 2 ^ 40 + 2 ^ 20 + EarInv.PRIMCAP <= BUDGET0.  Proof. vm_compute. discriminate. Qed.
Lemma BUDGET0_hi : BUDGET0 <= 2 ^ 41.  Proof. vm_compute. discriminate. Qed.
End PEALF.
