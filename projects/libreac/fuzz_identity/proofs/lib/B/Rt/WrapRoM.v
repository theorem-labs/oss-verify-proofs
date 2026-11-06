(* libreac/fuzz_identity, build asan-ubsan: from the wrappers' read-only premise (lib/B/Rt/WrapRo.v aro_unowned) to
   the musl constants the strlen and memchr walks read (lib/B/AE39.v mconsts_view: 0x10350 .. 0x10370, the same
   addresses as in the asan build). The text is lib/A/Rt/WrapRoM.v's at the B core. *)
(* Modified by Theorem Labs, 2026-10-29: for a Theorem Labs lane's acceptance (a working branch), the record class is TfibSyms, not IdentTfibSyms, and the core modules are Required by full path at the applied B core's names: lib/B/A<x>.v -> lib/ReusableB/Y<x>.v (AB1v AB1w AE20 AE2y AE34 AE39 AE3a AE6y AF0l AF0m AF0x -> YB1v YB1w YE20 YE2y YE34 YE39 YE3a YE6y YF0l YF0m YF0x, qualified names included), lib/Reusable/YA0m, YE08, YE21. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
Require Import
  OSSVerify.Proofs.libreac.fuzz_identity.lib.ReusableB.YB1v
  OSSVerify.Proofs.libreac.fuzz_identity.lib.ReusableB.YF0m
  OSSVerify.Proofs.libreac.fuzz_identity.lib.ReusableB.YE39.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import WrapRo.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma mconsts_of_aro : forall B (W : world tfibsegs) mem, TfibSyms B ->
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
