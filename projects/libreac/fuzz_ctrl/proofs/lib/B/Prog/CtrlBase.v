(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/CtrlBase.v (a working branch 26edf006f53, blob ae7df9fc2b4): the same Requires (all lib/Reusable, none image-specific), the same aliases and the same two definitions afobjb / afobj_any; the dual-copy modules YK11 / YM05 / YI16 are named qualified (lib.Reusable.<X>, the copy A's file resolves); the afobjb comment cites image B's (asan-ubsan) call site, malloc and guard. *)
(* fuzz_ctrl image B (asan-ubsan), PA layer: the frame / heap object predicates and the call post the program walk uses.

   ONE TEXT. The generic part of cgif's lib/YC20.v (in_roP, arodata_okP, ro_below_ofl, ro_spares,
   arodata_ok_journalP, afobj, apost_base) is the planning core's lib/Reusable/APostBase.v. This file re-exports
   APostBase and keeps each old name only as a parsing alias of the core's constant, so a file that writes
   `B.Prog.CtrlBase.arodata_okP` (lib/B/ProgWorld.v) or `CtrlBase.ro_below_ofl` reaches the ONE definition in
   APostBase. No definition is left here except the two that APostBase does not have: afobjb and afobj_any. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Export APostBase.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Open Scope Z_scope.

(* The seven names of APostBase, under their old CtrlBase paths. Aliases, not definitions. *)
Notation in_roP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.APostBase.in_roP (only parsing).
Notation arodata_okP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.APostBase.arodata_okP (only parsing).
Notation ro_below_ofl := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.APostBase.ro_below_ofl (only parsing).
Notation ro_spares := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.APostBase.ro_spares (only parsing).
Notation arodata_ok_journalP :=
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.APostBase.arodata_ok_journalP (only parsing).
Notation afobj := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.APostBase.afobj (only parsing).
Notation apost_base := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.APostBase.apost_base (only parsing).

Section j. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
Section l.
Variable segs : list Segment.
(* The same object as afobj, but carried by a live malloc block instead of a fake-stack frame. fuzz_ctrl needs it: in
   image B (fuzz_ctrl.asan-ubsan, libreac-v190/asan-ubsan/fuzz_ctrl.objdump.txt) at LLVMFuzzerTestOneInput+0x1828
   (0x82840) the argument of reac_ctrl_headamp_record_verify (a0 = s2) is the block returned by
   __interceptor_trampoline_malloc at 0x81f4c (`mv s2, a0` at 0x81f50), guarded by `sltiu a0, s4, 50` (0x82468)
   against the record's 50 bytes, not a frame object. The donor fuzz_grant passes a frame object there, which is why
   its spec says afobj. *)
Definition afobjb (B : asyms) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (p n : Z) : Prop :=
(exists q m, In (q, m) (ablocks B ly S) /\ q <= p /\ p + n <= q + req_size m) /\
p mod 8 = 0 /\ range_addressable (aview segs (w_H W) mem) SHADOW_OFF p n.
(* A record the caller owns, wherever ASan put it. *)
Definition afobj_any (B : asyms) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (p n : Z) : Prop :=
afobj segs B ly S W mem p n \/ afobjb B ly S W mem p n.
End l.
End j.
