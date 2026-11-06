(* RtSS00Cg: __asan_set_shadow_00 of fuzz_transport.asan in the text lib/A/TransportClose.v takes as its Section
   hypothesis H_RT_SET_SHADOW_00: lib/A/Prog/TransportRtCg.v aset_shadow_realizes with the fill value 0, at the
   listing's address of the entry (transport_sigma TS___asan_set_shadow_00, lib/A/Prog/DgnTransportAddr.v: 0x55270) and at
   TransportB, for every run ceiling and FP state. RtSetShadow.transport_set_shadow_00 proves the entry form at
   SS00_ENTRY (0x55270); the listing's address converts to the same numeral, so the proof applies that theorem to
   TransportB, Reusable/YG0q.v AR_laws_ok and lib/A/AD2l.v TransportB_syms. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK15 YK18 YM05 YK04 YA0i YA0n
YG00 YG01 YG0f YG0d YG0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v AD2l.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr
  TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Rt Require RtSetShadow.
Open Scope Z_scope.

Section c.
Local Notation segs := tfibsegs.
Local Notation B := TransportB.
Theorem set_shadow_00_realizes : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aset_shadow_realizes fx rc segs B (transport_sigma TS___asan_set_shadow_00) 0.
Proof.
  intros rc fx. exact (RtSetShadow.transport_set_shadow_00 B (AR_laws_ok segs B) TransportB_syms).
Qed.
End c.
