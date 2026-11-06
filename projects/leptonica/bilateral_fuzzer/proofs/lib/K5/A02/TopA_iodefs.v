(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0xff8a0, [C8 (Z_to_bv 64 0xf954c); C8 (Z_to_bv 64 0xf0450)])              (* [comment removed for export] *)
  ; (0x10a530, [C8 (Z_to_bv 64 0)]) ].                                           (* [comment removed for export] *)

Definition io_ro : list (Z * list cell) :=
  [ (0xfa6d0, [C8 (Z_to_bv 64 0x96974); C8 (Z_to_bv 64 0x44bac)])              (* [comment removed for export] *)
  ; (0xfda08, [C8 (Z_to_bv 64 0x102228)])                                        (* [comment removed for export] *)
  ; (0xfdae0, [C8 (Z_to_bv 64 0xea180); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xfe770, [C8 (Z_to_bv 64 0xfda08); C8 (Z_to_bv 64 0)])                    (* [comment removed for export] *)
  ; (0xfe790, [C8 (Z_to_bv 64 0x102520); C8 (Z_to_bv 64 0x1095a0)])              (* [comment removed for export] *)
  ; (0xfe818, [C8 (Z_to_bv 64 0xfa6e0); C8 (Z_to_bv 64 0xfa6d0)])              (* [comment removed for export] *)
  ; (0xff860, [C8 (Z_to_bv 64 0xff860)])                                        (* [comment removed for export] *)
  ; (0xff8c8, [C8 (Z_to_bv 64 0xf3794); C8 (Z_to_bv 64 0xf0684); C8 (Z_to_bv 64 0xf37b0)])  (* [comment removed for export] *)
  ; (0x10a490, [C4 (Z_to_bv 64 1)])                                              (* [comment removed for export] *)
  ; (0x19e7fc, [C1 (Z_to_bv 8 1)])                                              (* [comment removed for export] *)
  ; (0x19eb20, [C1 (Z_to_bv 8 0)]) ].                                           (* [comment removed for export] *)

Definition io_acc : list (Z * Z) :=
  [ (0x10d97, 10)     (* [comment removed for export] *)
  ; (0x1522f, 4)      (* [comment removed for export] *)
  ; (0x166c0, 192)    (* [comment removed for export] *)
  ; (0x1b48e, 33)     (* [comment removed for export] *)
  ; (0x201b4, 21)     (* [comment removed for export] *)
  ; (0x201c9, 23)     (* [comment removed for export] *)
  ; (0x22c00, 128)    (* [comment removed for export] *)
  ; (0x23e89, 7)      (* [comment removed for export] *)
  ; (0x2e240, 16)     (* [comment removed for export] *)
  ; (0x62f2c0, 16) ]. (* [comment removed for export] *)

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc asegs m (fst r) (snd r)) io_acc.

(* [comment removed for export] *)
Definition io_rngs : list (Z * Z) :=
  [ (0xff8a0, 0xff8b0); (0x10a530, 0x10a538);
    (0xfa6d0, 0xfa6e0); (0xfda08, 0xfda10); (0xfdae0, 0xfdaf0); (0xfe770, 0xfe780); (0xfe790, 0xfe7a0); (0xfe818, 0xfe828);
    (0xff860, 0xff868); (0xff8c8, 0xff8e0); (0x10a490, 0x10a494); (0x19e7fc, 0x19e7fd); (0x19eb20, 0x19eb21) ].

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
