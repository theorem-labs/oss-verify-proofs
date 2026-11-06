(* RtSSF8CgB: __asan_set_shadow_f8 of fuzz_transport.asan-ubsan (image B) in the text of image A's closing hypothesis
   H_RT_SET_SHADOW_F8 (lib/A/TransportClose.v) at image B: lib/A/Prog/TransportRtCg.v aset_shadow_realizes with the fill
   value 0xf8, at image B's listing address of the entry (transportb_sigma TB___asan_set_shadow_f8,
   lib/B/Prog/DgnTransportBAddr.v: 0x553cc), over image B's segments (lib/B/YB1v.v tfibsegs) and record (lib/B/YD2l.v
   TransportB), for every run ceiling and FP state. RtSetShadowB.transportB_set_shadow_f8 proves the entry form at
   SSF8_ENTRY (0x553cc); the listing's address converts to the same numeral, so the proof applies that theorem to
   TransportB, Reusable/YG0q.v AR_laws_ok and lib/B/YD2l.v TransportB_syms. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK15 YK18 YM05 YK04 YA0i YA0n
YG00 YG01 YG0f YG0d YG0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v YD2l.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Rt Require RtSetShadowB.
Open Scope Z_scope.

Section c.
Local Notation segs := tfibsegs.
Local Notation B := TransportB.
Theorem set_shadow_f8_realizes_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aset_shadow_realizes fx rc segs B (transportb_sigma TB___asan_set_shadow_f8) 0xf8.
Proof.
  intros rc fx. exact (RtSetShadowB.transportB_set_shadow_f8 B (AR_laws_ok segs B) TransportB_syms).
Qed.
End c.
