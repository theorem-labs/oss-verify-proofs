(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import HeapIface HeapIfaceA IcptIfaceAB0 LibIface LibIfaceAB EbrInv.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PEBLF.
Definition art_IL : icpt_layout :=
  ICL 0x64518
      2304
      0x103c0
      0x103e0
      [(0x232e0, 13); (0x233e0, 16); (0x23400, 23); (0x23440, 13); (0x23460, 60); (0x234c0, 77); (0x23540, 73); (0x235c0, 13); (0x235e0, 38); (0x23640, 70); (0x236c0, 69); (0x23740, 37); (0x237a0, 43); (0x23800, 34); (0x23860, 71); (0x238e0, 28); (0x23920, 7); (0x23980, 1); (0x239a0, 3); (0x239c0, 10); (0x239e0, 13); (0x23a00, 14); (0x23a20, 45); (0x23be0, 54); (0x23c40, 52)]
      [(0x232e0, 0x23ca0); (0x1423d0, 0x142a10)]
      0x78e3c
      0x78e38
      0x69b638
      0x64590
      4320
      [(0x67a150, 8, 0x69a448); (0x69a470, 8, 0)]
      0x10000
      0x13f000.
Lemma art_IL_ok : as0_icpt_layout art_IL.
Proof. constructor; reflexivity. Qed.

Definition BUDGET0 : Z := 2 ^ 41.
Lemma BUDGET0_lo40 : 2 ^ 40 + 2 ^ 20 + EbrInv.PRIMCAP <= BUDGET0.  Proof. vm_compute. discriminate. Qed.
Lemma BUDGET0_hi : BUDGET0 <= 2 ^ 41.  Proof. vm_compute. discriminate. Qed.
End PEBLF.
