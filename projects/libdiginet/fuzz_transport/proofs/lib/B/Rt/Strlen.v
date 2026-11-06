(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of the strlen wrapper of libreac/fuzz_identity.asan (trampoline 0x4218c -> ___interceptor_strlen 0x4221c -> musl strlen 0x94c64 -> the inline range check -> the epilogue), over cgif_file_fuzzer's lib/A/AE6x.v (the memchr wrapper: the entry phase, the lift of a musl msteps walk, the check, the epilogue) and lib/A/AE7d.v (the strnlen wrapper: the 2144-byte frame and its eight saved registers). The walked function is released as proofs/coturn/FuzzStunClient/lib/VAsanIcStrlenWalk.v:819 isl_run at coturn's addresses; this is that walk at fuzz_identity.asan's addresses in this release's engine, and its statement is lib/A/Rt/StrlenDef.v astrlen_realizes (cgif lib/YG0d.v:401-419 astrnlen_realizes without the n bound). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Rt/Strlen.v, with its module paths and module names changed; 15 of its 25 lines of code are new or changed and 495 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Rt/Strlen.v, with its module paths changed; 3 of its 24 lines of code are new or changed and 4 lines of the source are left out. *)
(* Relocated from libreac/fuzz_identity's released proofs/lib/B/Rt/Strlen.v (c3777b3715d0) to libdiginet/fuzz_transport's
   image B, fuzz_transport.asan-ubsan 41113a03c82f (unstripped twin e217cb0a84f1); the donor is proved against
   fuzz_identity.asan-ubsan baf1a4d065e0 (unstripped twin 43b44d50be8a).
   The walked functions (the trampoline, ___interceptor_strlen, __asan_region_is_poisoned,
   __asan::TryAsanInitFromRtl, __sanitizer::mem_is_zero, 0xb2c above the donor's; musl strlen, 0x856c above)
   have the donor's sizes and the donor's words up to pc-relative immediates (cmpkit 86da41d3ef68 strictcmp3 by
   address: EQUAL or EQUAL-mod-pcrel, 0 real, 0 differing targets).
   The theorem states lib/A/Prog/TransportRtCg.v astrlen_realizes (the donor's StrlenDef.v text, verbatim),
   at image B's segments and the trampoline FMstrlen.SL_ENTRY.
   Every image numeral of the donor moved by one table read from the two images (function + offset, object +
   offset, the .got slot a paired auipc / ld reads); the record of each numeral and the byte compare of the walked
   functions are in provenance/evidence/rt-wrappers/. The proof script is the donor's. *)
(* libdiginet/fuzz_transport, image B: the strlen wrapper's contract, lib/A/Prog/TransportRtCg.v astrlen_realizes at
   FMstrlen.SL_ENTRY = 0x42d20, from the strlen walk lib/B/FMstrlen.v strlen_icpt_srr. The text is
   lib/A/Rt/Strlen.v's over the B core. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05.
Require Import
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.YB1v
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.YF0m
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.YE39.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require FMstrlen.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Rt Require Import WrapRoM.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem strlen_icpt_contract : forall B, AR_laws tfibsegs B -> TransportSyms B -> astrlen_realizes tfibsegs B FMstrlen.SL_ENTRY.
Proof.
intros B LAWS TB. unfold astrlen_realizes. intros ly S W regs mem md x k. intros.
apply (FMstrlen.strlen_icpt_srr B LAWS TB ly S W regs mem md x k).
all: first [ assumption | apply (mconsts_of_aro B W mem TB); assumption ].
Qed.
End d.
