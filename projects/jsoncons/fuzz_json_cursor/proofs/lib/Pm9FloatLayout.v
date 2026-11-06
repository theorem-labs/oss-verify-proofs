(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import HeapIface HeapIfaceA DecIface DecIfaceA Pm9ArtIfaceInst.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma art_float : PDCA.float_layoutA art_L PDCA.cboth.
Proof.
  split; [reflexivity|]. intros a Ha. cbn [PDC.a_TP PDC.a_G PDC.a_img_lo PDC.a_img_hi PDCA.cboth] in Ha.
  cbn [art_L hl_img_lo hl_img_hi hl_rt_static hl_rt_ro hl_tp PDC.a_TP PDC.a_G PDC.a_img_lo PDC.a_img_hi PDCA.asan11 PDCA.cboth]. unfold art_static, art_ro. lia.
Qed.
