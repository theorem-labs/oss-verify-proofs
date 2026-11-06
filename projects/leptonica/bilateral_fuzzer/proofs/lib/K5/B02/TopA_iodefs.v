(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0x10c900, [C8 (Z_to_bv 64 0x1065a0); C8 (Z_to_bv 64 0xfd4a4)])              (* [comment removed for export] *)
  ; (0x117630, [C8 (Z_to_bv 64 0)]) ].                                           (* [comment removed for export] *)

Definition io_ro : list (Z * list cell) :=
  [ (0x107720, [C8 (Z_to_bv 64 0x96b2c); C8 (Z_to_bv 64 0x44d64)])              (* [comment removed for export] *)
  ; (0x10aa58, [C8 (Z_to_bv 64 0x10f288)])                                        (* [comment removed for export] *)
  ; (0x10ab30, [C8 (Z_to_bv 64 0xf71d4); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0x10b7c0, [C8 (Z_to_bv 64 0x10aa58); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0x10b7e0, [C8 (Z_to_bv 64 0x10f580); C8 (Z_to_bv 64 0x1166c0)])              (* [comment removed for export] *)
  ; (0x10b868, [C8 (Z_to_bv 64 0x107730); C8 (Z_to_bv 64 0x107720)])              (* [comment removed for export] *)
  ; (0x10c8c0, [C8 (Z_to_bv 64 0x10c8c0)])                                        (* [comment removed for export] *)
  ; (0x10c928, [C8 (Z_to_bv 64 0x1007e8); C8 (Z_to_bv 64 0xfd6d8); C8 (Z_to_bv 64 0x100804)])  (* [comment removed for export] *)
  ; (0x117590, [C4 (Z_to_bv 64 1)])                                              (* [comment removed for export] *)
  ; (0x1ab8fc, [C1 (Z_to_bv 8 1)])                                              (* [comment removed for export] *)
  ; (0x1abc20, [C1 (Z_to_bv 8 0)]) ].                                           (* [comment removed for export] *)

Definition io_acc : list (Z * Z) :=
  [ (0x10db7, 10)     (* [comment removed for export] *)
  ; (0x15265, 4)      (* [comment removed for export] *)
  ; (0x16700, 128)    (* [comment removed for export] *)
  ; (0x1b4c4, 33)     (* [comment removed for export] *)
  ; (0x201ea, 21)     (* [comment removed for export] *)
  ; (0x201ff, 23)     (* [comment removed for export] *)
  ; (0x22c40, 128)    (* [comment removed for export] *)
  ; (0x23ebf, 7)      (* [comment removed for export] *)
  ; (0x2e320, 16)     (* [comment removed for export] *)
  ; (0x63c3c0, 16) ]. (* [comment removed for export] *)

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc asegs m (fst r) (snd r)) io_acc.

(* [comment removed for export] *)
Definition io_rngs : list (Z * Z) :=
  [ (0x10c900, 0x10c910); (0x117630, 0x117638);
    (0x107720, 0x107730); (0x10aa58, 0x10aa60); (0x10ab30, 0x10ab40); (0x10b7c0, 0x10b7d0); (0x10b7e0, 0x10b7f0); (0x10b868, 0x10b878);
    (0x10c8c0, 0x10c8c8); (0x10c928, 0x10c940); (0x117590, 0x117594); (0x1ab8fc, 0x1ab8fd); (0x1abc20, 0x1abc21) ].

Lemma io_rngs_of : io_rngs = map (fun p => (fst p, fst p + Z.of_nat (cells_size (snd p)))) (io_rw ++ io_ro).
Proof. reflexivity. Qed.

Section Get.
Variable m : mem.
Hypothesis H : io_consts m.
Lemma io_rw_at : forall a cs, In (a, cs) io_rw -> rw_cells asegs m a cs.
Proof using m H. intros a cs Hin. destruct H as (X & _ & _). exact (proj1 (Forall_forall _ _) X (a, cs) Hin). Qed.
Lemma io_ro_at : forall a cs, In (a, cs) io_ro -> ro_cells asegs m a cs.
Proof using m H. intros a cs Hin. destruct H as (_ & X & _). exact (proj1 (Forall_forall _ _) X (a, cs) Hin). Qed.
Lemma io_acc_at : forall a n, In (a, n) io_acc -> acc asegs m a n.
Proof using m H. intros a n Hin. destruct H as (_ & _ & X). exact (proj1 (Forall_forall _ _) X (a, n) Hin). Qed.
End Get.

Ltac io_in := cbn [io_rw io_ro io_acc In]; repeat (first [ left; reflexivity | right ]).
