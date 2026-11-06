(* RtStrlenCg: the strlen wrapper text that the image-A closing of fuzz_transport.asan (e89be137db17) takes, stated
   word for word as lib/A/TransportClose.v's Section hypothesis H_RT_STRLEN: lib/A/Prog/TransportRtCg.v
   astrlen_realizes over tfibsegs and the applied core's record TransportB, at the listing's trampoline
   transport_sigma TS___interceptor_trampoline_strlen (lib/A/Prog/DgnTransportAddr.v: __interceptor_trampoline_strlen =
   __wrap_strlen, `j ___interceptor_strlen`). lib/A/Rt/Strlen.v strlen_icpt_contract proves that text at
   FMstrlen.SL_ENTRY for every record with AR_laws and TransportSyms; transport_sigma of the tag is that address. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK04 YG00 YG0d YG0q YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v AF0m AD2l.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require FMstrlen.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Rt Require Strlen.
Open Scope Z_scope.

Section close.
Local Notation segs := tfibsegs.
Local Notation B := TransportB.

(* The listing's trampoline address is the walk's entry. *)
Lemma transport_sigma_strlen : transport_sigma TS___interceptor_trampoline_strlen = FMstrlen.SL_ENTRY.
Proof. reflexivity. Qed.

(* lib/A/TransportClose.v H_RT_STRLEN. *)
Theorem transport_strlen_realizes : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @astrlen_realizes fx rc segs B (transport_sigma TS___interceptor_trampoline_strlen).
Proof.
intros rc fx. rewrite transport_sigma_strlen.
exact (Strlen.strlen_icpt_contract TransportB (AR_laws_ok tfibsegs TransportB) TransportB_syms).
Qed.
End close.
