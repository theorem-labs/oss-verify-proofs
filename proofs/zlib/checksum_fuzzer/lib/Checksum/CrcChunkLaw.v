(** The fuzzer's mathematical chunk-combine identity, for its actual chunk
    bound. A machine checksum routine must implement crc_model to use this. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import
  CrcAlgebra CrcLinearBasis CrcLinearLaws CrcModel CrcOp CrcGenModel.
Open Scope Z_scope.
Theorem crc_chunk_combine : forall (bs : list byte) q,
  (List.length bs <= 255)%nat -> 0 <= q < 2^32 ->
  combine_op_model q (crc_model 0 bs) (combine_gen_model (Z.of_nat (List.length bs))) = crc_model q bs.
Proof.
  intros bs q Hlen Hq. unfold combine_op_model.
  rewrite bounded_combine_advance by lia.
  rewrite Nat2Z.id,(crc_model_affine q bs). apply Z.lxor_comm.
Qed.
