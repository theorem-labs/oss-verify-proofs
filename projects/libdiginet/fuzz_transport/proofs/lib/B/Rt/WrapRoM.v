(* Relocated from libreac/fuzz_identity's released proofs/lib/B/Rt/WrapRoM.v (c3777b3715d0) to libdiginet/fuzz_transport's
   image B, fuzz_transport.asan-ubsan 41113a03c82f (unstripped twin e217cb0a84f1); the donor is proved against
   fuzz_identity.asan-ubsan baf1a4d065e0 (unstripped twin 43b44d50be8a).
   The walked functions (the trampoline, ___interceptor_strlen, __asan_region_is_poisoned,
   __asan::TryAsanInitFromRtl, __sanitizer::mem_is_zero, 0xb2c above the donor's; musl strlen, 0x856c above)
   have the donor's sizes and the donor's words up to pc-relative immediates (cmpkit 86da41d3ef68 strictcmp3 by
   address: EQUAL or EQUAL-mod-pcrel, 0 real, 0 differing targets).
   The read-only premise is lib/A/Prog/TransportRtCg.v's aro_unowned (the donor's WrapRo.v text, verbatim).
   Every image numeral of the donor moved by one table read from the two images (function + offset, object +
   offset, the .got slot a paired auipc / ld reads); the record of each numeral and the byte compare of the walked
   functions are in provenance/evidence/rt-wrappers/. The proof script is the donor's. *)
(* libdiginet/fuzz_transport, image B: from the wrappers' read-only premise (lib/A/Prog/TransportRtCg.v aro_unowned)
   to the musl constants the strlen walk reads (lib/B/YE39.v mconsts_view: MC_LO .. MC_HI). The text is
   lib/A/Rt/WrapRoM.v's at the B core. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma mconsts_of_aro : forall B (W : world tfibsegs) mem, TransportSyms B ->
aro_unowned tfibsegs B (aview tfibsegs (w_H W) mem) -> mconsts_view W mem.
Proof.
intros B W mem TB Hro a Ha. pose proof mc_bounds as [M1 M2].
apply Hro.
- exact (mc_in_rom a Ha).
- rewrite (ts_owned B TB). intros Hex. apply Exists_exists in Hex as (r & Hr & Hz).
unfold Tfib_owned_static in Hr. unfold in_zr in Hz.
repeat (destruct Hr as [<- | Hr]; [cbn [fst snd] in Hz; clear - Ha M1 M2 Hz; lia |]). destruct Hr.
- rewrite (ts_errno B TB). unfold TFIB_ERRNO. clear - Ha M1 M2. lia.
Qed.
End b.
