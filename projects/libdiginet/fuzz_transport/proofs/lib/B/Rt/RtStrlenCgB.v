(* RtStrlenCgB: the strlen wrapper text of fuzz_transport.asan-ubsan (image B, 41113a03c82f), image A's text
   (lib/A/Rt/RtStrlenCg.v transport_strlen_realizes) at image B's segments, record and trampoline:
   lib/A/Prog/TransportRtCg.v astrlen_realizes over tfibsegs (lib/B/YB1v.v) and the applied core's record TransportB
   (lib/B/YD2l.v), at the listing's trampoline transportb_sigma TB___interceptor_trampoline_strlen
   (lib/B/Prog/DgnTransportBAddr.v: __interceptor_trampoline_strlen = __wrap_strlen, `j ___interceptor_strlen`).
   lib/B/Rt/Strlen.v strlen_icpt_contract proves that text at FMstrlen.SL_ENTRY for every record with AR_laws and
   TransportSyms; transportb_sigma of the tag is that address. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK04 YG00 YG0d YG0q YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v YF0m YD2l.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require FMstrlen.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Rt Require Strlen.
Open Scope Z_scope.

Section close.
Local Notation segs := tfibsegs.
Local Notation B := TransportB.

(* The listing's trampoline address is the walk's entry. *)
Lemma transportb_sigma_strlen : transportb_sigma TB___interceptor_trampoline_strlen = FMstrlen.SL_ENTRY.
Proof. reflexivity. Qed.

(* Image A's H_RT_STRLEN (lib/A/TransportClose.v) at image B. *)
Theorem transport_strlen_realizes_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @astrlen_realizes fx rc segs B (transportb_sigma TB___interceptor_trampoline_strlen).
Proof.
intros rc fx. rewrite transportb_sigma_strlen.
exact (Strlen.strlen_icpt_contract TransportB (AR_laws_ok tfibsegs TransportB) TransportB_syms).
Qed.
End close.
