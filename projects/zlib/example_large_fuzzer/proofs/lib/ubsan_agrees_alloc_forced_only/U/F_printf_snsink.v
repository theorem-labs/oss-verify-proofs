(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Prelim Monad PrintfModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Printf_lib F_memset F_memcpy F_fwritex Printf_mlib F_printf_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_nd := first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia | lia ].
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Lemma zb_length : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.

Lemma Forall_disjoint_from : forall (W : list (Z * Z)) A N a n,
  Forall (fun iv => snd iv <= A \/ A + N <= fst iv) W -> A <= a -> a + n <= A + N -> 0 <= n -> disjoint_from W a n.
Proof.
  intros W A N a n H Ha Hn Hn0. induction H as [|[lo hi] W' Hiv _ IH]; cbn; [exact I|]. cbn in Hiv. split; [lia | exact IH].
Qed.

(* [comment removed for export] *)

Section SnProofs.
  Variables (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (frest : list cell) (B TOP : Z).
  Let SINK := SINK_sn Fp fl0 j1 j2 lbfw frest B TOP.

  (* [comment removed for export] *)

End SnProofs.
