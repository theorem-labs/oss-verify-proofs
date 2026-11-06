(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import Prelim.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import SoftFloat.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import FmtFp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition is_numch (c : Z) : bool :=
  ((48 <=? c) && (c <=? 57)) || (c =? 43) || (c =? 45) || (c =? 46) || (c =? 69) || (c =? 101).

Definition fmt_alpha_fact (d prec : Z) : Prop :=
  forall o r, fmt_g d prec = Some (o, r) -> Forall (fun c => is_numch c = true) o.

Example fmt_alpha_probe1 : exists o r, fmt_g 0x3fb999999999999a 15 = Some (o, r) /\ forallb is_numch o = true.
Proof. eexists _, _. split; [vm_compute; reflexivity | reflexivity]. Qed.
Example fmt_alpha_probe2 : exists o r, fmt_g 0x7e37e43c8800759c 17 = Some (o, r) /\ forallb is_numch o = true.
Proof. eexists _, _. split; [vm_compute; reflexivity | reflexivity]. Qed.
Example fmt_alpha_probe3 : exists o r, fmt_g 0xbe90c6f7a0b5ed8d 15 = Some (o, r) /\ forallb is_numch o = true.
Proof. eexists _, _. split; [vm_compute; reflexivity | reflexivity]. Qed.
Example fmt_alpha_probe4 : exists o r, fmt_g 0xbe90c6f7a0b5ed8d 17 = Some (o, r) /\ forallb is_numch o = true.
Proof. eexists _, _. split; [vm_compute; reflexivity | reflexivity]. Qed.
Example fmt_alpha_probe5 : exists o r, fmt_g 0x437b69b4ba630f34 15 = Some (o, r) /\ forallb is_numch o = true.
Proof. eexists _, _. split; [vm_compute; reflexivity | reflexivity]. Qed.
