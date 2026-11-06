(* RtStrcmpCgB: the strcmp wrapper text of fuzz_transport.asan-ubsan (image B, 41113a03c82f), image A's text
   (lib/A/Rt/RtStrcmpCg.v transport_strcmp_realizes) at image B's segments, record and trampoline: the image-B
   walks' astrcmp_realizes (lib/B/Prog/diginet_personality_from_name_cg.v, the registry text of record, verbatim)
   over tfibsegs (lib/B/YB1v.v) and the applied core's record TransportB (lib/B/YD2l.v), at the listing's trampoline
   transportb_sigma TB___interceptor_trampoline_strcmp (lib/B/Prog/DgnTransportBAddr.v: __interceptor_trampoline_strcmp
   = __wrap_strcmp, `j ___interceptor_strcmp`). lib/B/Rt/Strcmp.v strcmp_icpt_contract proves that text at its
   STRCMP_TRAMP for every record with AR_laws and TransportSyms; transportb_sigma of the tag is that address. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK04 YG00 YG0d YG0q YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v YF0m YD2l.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require diginet_personality_from_name_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Rt Require Strcmp.
Module PPFB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_personality_from_name_cg.
Open Scope Z_scope.

Section close.
Local Notation segs := tfibsegs.
Local Notation B := TransportB.

(* The listing's trampoline address is the walk's entry. *)
Lemma transportb_sigma_strcmp : transportb_sigma TB___interceptor_trampoline_strcmp = Strcmp.STRCMP_TRAMP.
Proof. reflexivity. Qed.

(* Image A's H_RT_STRCMP (lib/A/TransportClose.v) at image B. *)
Theorem transport_strcmp_realizes_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @PPFB.astrcmp_realizes fx rc segs B (transportb_sigma TB___interceptor_trampoline_strcmp).
Proof.
intros rc fx. rewrite transportb_sigma_strcmp.
exact (Strcmp.strcmp_icpt_contract TransportB (AR_laws_ok tfibsegs TransportB) TransportB_syms).
Qed.
End close.
