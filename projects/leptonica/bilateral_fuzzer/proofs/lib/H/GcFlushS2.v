(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import PArray Uint63.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_GcFlushS2 () := "K47Corelib4Init5Logic2eq01c59OSSVerify5KrLib1H9GcFlushS2:flush_loopC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes3nat02C67Corelib7Numbers6Cyclic5Int639PrimInt633intK47Corelib4Init9Datatypes3nat01".
Fixpoint flush_loop (n : nat) (acc : int) : int :=
  match n with
  | O => acc
  | S k => flush_loop k (PArray.length (PArray.make 4194303 acc))
  end.
Lemma gc_flush : flush_loop 150 0 = 4194303%uint63.
Proof.
ltac2:(KReplay.run1 (kr_t_GcFlushS2 ()) [] "p;2p;3p;1g0000j27Tg000Jj25Tg001Ej34Tg001_j10Tf0R0#0#0p=6%00#0#0#0p=3%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=2%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g002>R0p@0?ooo000000R1'7g002k#6#3#2#1#1#1#1p@00000000000'5=401do"). Qed.
