(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import PArray Uint63.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_GcFlush03 () := "K47Corelib4Init5Logic2eq01c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9GcFlush03:flush_loopC13~~~I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes3nat02C67Corelib7Numbers6Cyclic5Int639PrimInt633intK47Corelib4Init9Datatypes3nat01".
Fixpoint flush_loop (n : nat) (acc : int) : int :=
  match n with
  | O => acc
  | S k => flush_loop k (PArray.length (PArray.make 4194303 acc))
  end.
Lemma gc_flush : flush_loop 150 0 = 4194303%uint63.
Proof.
ltac2:(KReplay.run1 (kr_t_GcFlush03 ()) [] "p;2p;3p;1g0000j27Tg000Jj25Tg001Yj34Tg0023j10Tf0R0#0#0p=6%00#0#0#0p=3%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=2%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g002RR0p@0?ooo000000R1'7g003?#6#3#2#1#1#1#1p@00000000000'5=401do"). Qed.
