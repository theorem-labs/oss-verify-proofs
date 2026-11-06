(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyImg_errnonst.v (commit 4d286b2e618d, file sha256 9f568819d037) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Reply image row img-errnonst-B (a Theorem Labs lane's internal file REPLY-IMG-ROWS.md; the internal file CF-UNIT-HYPS.md:36).
   errno_nstatic_t at reply image B, as a CLOSED lemma over the unit's own TfibSyms tables (lib/B/YD2l.v TfibB:
   as_errno := TFIB_ERRNO :25, as_owned_static := Tfib_owned_static :36, both lib/B/YF0m.v).
   The cf layer's name is not in this tree yet, so the statement is the UNFOLDED text of
     Definition errno_nstatic_t (YGcfInstErrno.v:90, F1)  =
     forall a, as_errno B <= a < as_errno B + 4 -> ~ Exists (in_zr a) (as_owned_static B)   at B := TfibB.
   Proof pattern: cgif's errno_nstatic_cgif (YGcfInstErrnocgif.v:44 @ bdbe5c2a7e55), which destructs the owned list
   entry by entry; here one vm_compute decides "no owned range meets [errno, errno + 4)" for the whole list, with the
   kernel cast recorded (whole-goal vm_compute; reflexivity). Author: a Theorem Labs lane. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0f YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YF0m YD2l.
Import ListNotations.
Local Open Scope Z_scope.

(* r meets the four errno bytes [e, e + 4) *)
Definition meets4 (e : Z) (r : Z * Z) : bool := (fst r <? e + 4) && (e <? fst r + snd r).

Lemma nstatic_of_check : forall (owned : list (Z * Z)) (e : Z),
  existsb (meets4 e) owned = false ->
  forall a, e <= a < e + 4 -> ~ Exists (in_zr a) owned.
Proof.
  intros owned e H a Ha Hx. apply Exists_exists in Hx. destruct Hx as [r [Hin Hz]].
  assert (Hm : meets4 e r = true).
  { unfold meets4, in_zr in *. apply andb_true_intro. split; apply Z.ltb_lt; lia. }
  assert (existsb (meets4 e) owned = true) by (apply existsb_exists; eauto). congruence.
Qed.

Lemma errno_nstatic_check_B : existsb (meets4 (as_errno TfibB)) (as_owned_static TfibB) = false.
Proof. vm_compute. reflexivity. Qed.

Theorem errno_nstatic_B :
  forall a, as_errno TfibB <= a < as_errno TfibB + 4 -> ~ Exists (in_zr a) (as_owned_static TfibB).
Proof. exact (nstatic_of_check _ _ errno_nstatic_check_B). Qed.

Print Assumptions errno_nstatic_B.
