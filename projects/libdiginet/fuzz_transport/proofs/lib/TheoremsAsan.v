(* The unit's four ASan tops, in the form of lib/Theorems.v (which holds the plain / UBSan tops and Requires nothing
   of lib/A or lib/B, so a plain / UBSan release ships without them): asan_halts and asan_agrees from image A's
   closing (A/TransportCloseAll.v transport_asan_halts_all, transport_asan_agrees_all), asan_ubsan_halts and
   asan_ubsan_agrees from image B's (B/TransportCloseAllB.v transport_asan_ubsan_halts_all,
   transport_asan_ubsan_agrees_all). Each top takes no premise; its Print Assumptions is the kernel primitives
   (PrimInt63, PrimString, PrimArray), functional_extensionality_dep and Classical_Prop.classic. *)
From OSSVerify.libdiginet.fuzz_transport Require Statements.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require TransportCloseAll.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require TransportCloseAllB.

Module TCA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportCloseAll.
Module TCB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportCloseAllB.

Definition libdiginet_fuzz_transport_asan_halts : Statements.asan_halts :=
  TCA.transport_asan_halts_all.

Definition libdiginet_fuzz_transport_asan_agrees : Statements.asan_agrees :=
  TCA.transport_asan_agrees_all.

Definition libdiginet_fuzz_transport_asan_ubsan_halts : Statements.asan_ubsan_halts :=
  TCB.transport_asan_ubsan_halts_all.

Definition libdiginet_fuzz_transport_asan_ubsan_agrees : Statements.asan_ubsan_agrees :=
  TCB.transport_asan_ubsan_agrees_all.
