(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BSeqExec BStepTac BMemSplit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_BZStores () := "C47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List7existsbK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvC46Stdlib5Lists4List=repeat_lengthI47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01".
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition zeros (n : nat) : list byte := repeat (Z_to_bv 8 0) n.

Fixpoint zstores (m : word -> option byte) (d : word) (ws : list (Z * nat)) : word -> option byte :=
  match ws with
  | [] => m
  | (o, n) :: ws' => zstores (wbytes m (Z_to_bv 64 (bv_unsigned d + o)) (zeros n)) d ws'
  end.

Definition covers_off (i : Z) (on : Z * nat) : bool :=
  (fst on <=? i) && (i <? fst on + Z.of_nat (snd on)).

Definition ws_inb (ws : list (Z * nat)) (N : Z) : bool :=
  forallb (fun on => (0 <=? fst on) && (fst on + Z.of_nat (snd on) <=? N)) ws.

Fixpoint iota_Z (i : Z) (k : nat) : list Z :=
  match k with O => [] | S k' => i :: iota_Z (i + 1) k' end.

Definition ws_cover (ws : list (Z * nat)) (N : nat) : bool :=
  forallb (fun i => existsb (covers_off i) ws) (iota_Z 0 N).

Lemma length_zeros : forall n, length (zeros n) = n.
Proof.
ltac2:(KReplay.run1 (kr_t_BZStores ()) [] "h01np;1p;2p;3p-1R0p10000R1p4p710p8P0P1p4p7210p8P0p1000Mp4p710p8g000ij10Tg001Nj14Tg001lj12Tg002Oj21Tg0035j33Tg003Wg0046#0#0#0#4R0#2g004[,10f033W0o"). Qed.

Section Cover.
  Variable d : word.
  Variable N : Z.
  Hypothesis Hnw : bv_unsigned d + N < 2^64.

End Cover.
