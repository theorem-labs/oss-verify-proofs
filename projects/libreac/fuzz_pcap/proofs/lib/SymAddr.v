(* SPDX-License-Identifier: MIT *)
(* [symaddr e] is the address e names, a function, an object or a section of Symbols.v plus an offset, written as
   the numeral itself: [symaddr (Symbols.Plain.s_pcap_source_next + 0x178)%Z] elaborates to 78872, the term the
   walks wrote by hand before.  So a proof sees the same term, and a rebuild that moves the function changes
   Symbols.v and not the proof.  The expected type picks the numeral's form: a [bv n] gets the form a bit vector
   literal elaborates to, an [N] its N numeral, anything else a Z.  Rocq refuses ltac:(...) in a match pattern: there,
   bind the address first ([let a := constr:(symaddr ...) in match ... with ... a ... end]).  A page bound of the
   image is named from ImgPages.v the same way: [symaddr ImgPages.Asan.top] elaborates to 6254592. *)
From Stdlib Require Import ZArith NArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.libreac.fuzz_pcap Require Symbols.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require ImgPages.

Ltac symaddr_of e :=
  let v := eval vm_compute in (e)%Z in
  let T := lazymatch goal with |- ?T => T end in
  let T := eval hnf in T in
  lazymatch T with
  | bv ?n => exact (@BV n v (I <: BvWf n v))
  | N => let w := eval vm_compute in (Z.to_N v) in exact w
  | _ => exact v
  end.

Abbreviation symaddr e := (ltac:(symaddr_of e)) (only parsing).

(* [symwords lo hi] is the number of 4-byte words from address lo to address hi (both named from Symbols.v), written
   as the nat numeral itself: the count a code table built from lo covers.  A count written as a numeral would
   leave out the last functions of the range once a relink moves hi away from lo.  A nat numeral above 5000 parses
   as [Nat.of_num_uint d], so a large count builds that same term. *)
Ltac symwords_of lo hi :=
  let d := eval vm_compute in (hi - lo)%Z in
  let r := eval vm_compute in (d mod 4)%Z in
  lazymatch r with 0%Z => idtac | _ => fail "symwords: the range is not a whole number of words" end;
  let n := eval vm_compute in (Z.to_nat (d / 4)) in
  let big := eval vm_compute in (Nat.ltb 5000 n) in
  lazymatch big with
  | true => let u := eval vm_compute in (Nat.to_num_uint n) in exact (Nat.of_num_uint u)
  | false => exact n
  end.

Abbreviation symwords lo hi := (ltac:(symwords_of lo%Z hi%Z)) (only parsing).
