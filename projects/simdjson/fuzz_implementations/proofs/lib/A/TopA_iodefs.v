(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import PropExec MState Mem Cells Step ImageA.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0x173ff0, [C8 (Z_to_bv 64 0x16aad4); C8 (Z_to_bv 64 0x15b1c0)])
  ; (0x178f70, [C8 (Z_to_bv 64 0)])
  ; (0x174148, [C8 (Z_to_bv 64 0x1528c8)])
  ; (0x1740a0, [C8 (Z_to_bv 64 0x15a750)])
  ; (0x174068, [C8 (Z_to_bv 64 0x159734)])
  ; (0x17621c, [C4 (Z_to_bv 64 0x8)])
  ; (0x178ed4, [C1 (Z_to_bv 8 0x0)])
  ; (0x16f840, [C8 (Z_to_bv 64 0x8)])
  ; (0x16f960, [C8 (Z_to_bv 64 0x8)])
  ; (0x16fce8, [C8 (Z_to_bv 64 0x114a08)])
  ; (0x16fe18, [C8 (Z_to_bv 64 0x11516c)])
  ; (0x1700a8, [C8 (Z_to_bv 64 0x13cb18)])
  ; (0x170358, [C8 (Z_to_bv 64 0x13c34c)])     ].

Definition io_ro : list (Z * list cell) :=
  [ (0x16bc60, [C8 (Z_to_bv 64 0xbdf28); C8 (Z_to_bv 64 0x5db40)])
  ; (0x172038, [C8 (Z_to_bv 64 0x176988)])
  ; (0x172118, [C8 (Z_to_bv 64 0x1528c4); C8 (Z_to_bv 64 0)])
  ; (0x172db0, [C8 (Z_to_bv 64 0x172038); C8 (Z_to_bv 64 0)])
  ; (0x172e30, [C8 (Z_to_bv 64 0x176c80); C8 (Z_to_bv 64 0x178000)])
  ; (0x172f68, [C8 (Z_to_bv 64 0x16bc70); C8 (Z_to_bv 64 0x16bc60)])
  ; (0x173fa8, [C8 (Z_to_bv 64 0x173fa8)])
  ; (0x174020, [C8 (Z_to_bv 64 0x161d94); C8 (Z_to_bv 64 0x15bab0); C8 (Z_to_bv 64 0x161db0)])
  ; (0x178ed0, [C4 (Z_to_bv 64 1)])
  ; (0x178f18, [C1 (Z_to_bv 8 1)])
  ; (0x20d23c, [C1 (Z_to_bv 8 1)])
  ; (0x20d560, [C1 (Z_to_bv 8 0)])
  ; (0x16c300, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x16c360); C8 (Z_to_bv 64 0xe8440); C8 (Z_to_bv 64 0xe85cc); C8 (Z_to_bv 64 0xe8758); C8 (Z_to_bv 64 0xbf7d8); C8 (Z_to_bv 64 0xc1dc8); C8 (Z_to_bv 64 0xc1f58)])
  ; (0x16c3c0, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x16c440); C8 (Z_to_bv 64 0xe83ec); C8 (Z_to_bv 64 0xbfa34); C8 (Z_to_bv 64 0xc236c); C8 (Z_to_bv 64 0xd4dc4); C8 (Z_to_bv 64 0xe74b0); C8 (Z_to_bv 64 0xe7c64); C8 (Z_to_bv 64 0xe87a0); C8 (Z_to_bv 64 0xe8900); C8 (Z_to_bv 64 0xe8a68); C8 (Z_to_bv 64 0xe8b54)])
  ; (0x172dd0, [C8 (Z_to_bv 64 0x16fb88); C8 (Z_to_bv 64 0x16f9b0); C8 (Z_to_bv 64 0x16f770); C8 (Z_to_bv 64 0x16fb38)])
  ; (0x16fb88, [C8 (Z_to_bv 64 0x16fb50); C8 (Z_to_bv 64 0x16fbc0); C8 (Z_to_bv 64 0x16fbe8); C8 (Z_to_bv 64 0x16fb78); C8 (Z_to_bv 64 0x70)])
  ; (0x16fb38, [C8 (Z_to_bv 64 0x70)])
  ; (0x16fa20, [C8 (Z_to_bv 64 0x112b6c); C8 (Z_to_bv 64 0x113740)])
  ; (0x172e20, [C8 (Z_to_bv 64 0x31ab0)])
  ; (0x173fd0, [C8 (Z_to_bv 64 0x1640a0); C8 (Z_to_bv 64 0x163fd0)])
  ; (0x20d2e6, [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)])
  ; (0x16ff60, [C8 (Z_to_bv 64 0x13b2a4)])
  ; (0x172e28, [C8 (Z_to_bv 64 0x6aec20)])
  ; (0x16f2d8, [C8 (Z_to_bv 64 0x16f4d8); C8 (Z_to_bv 64 0x318c8)])
  ; (0x16f4b0, [C8 (Z_to_bv 64 0x16f528); C8 (Z_to_bv 64 0x31987)])
  ; (0x16f4f8, [C8 (Z_to_bv 64 0x10adb0)])
  ; (0x16f510, [C8 (Z_to_bv 64 0x10b114); C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x16f568)])
  ; (0x16f550, [C8 (Z_to_bv 64 0x10bd88)])
  ; (0x16f560, [C8 (Z_to_bv 64 0x10b190); C8 (Z_to_bv 64 0x16f528); C8 (Z_to_bv 64 0x319a9); C8 (Z_to_bv 64 0x16f4b0)])
  ; (0x171f10, [C8 (Z_to_bv 64 0x14c72c); C8 (Z_to_bv 64 0x14c764); C8 (Z_to_bv 64 0x14c800)])
  ; (0x171f40, [C8 (Z_to_bv 64 0x14c924); C8 (Z_to_bv 64 0x14ca0c); C8 (Z_to_bv 64 0x14ca34)])
  ; (0x171f68, [C8 (Z_to_bv 64 0x14cae0)])
  ; (0x1720f0, [C8 (Z_to_bv 64 0x0)])
  ; (0x172e48, [C8 (Z_to_bv 64 0x1768e8)])
  ; (0x172e50, [C8 (Z_to_bv 64 0x1768e0)])
  ; (0x173fe8, [C8 (Z_to_bv 64 0x156698)])
  ; (0x16ff68, [C8 (Z_to_bv 64 0x13b2ac)])
  ; (0x170b08, [C8 (Z_to_bv 64 0x11fa30)])
  ; (0x170b10, [C8 (Z_to_bv 64 0x11fcc8); C8 (Z_to_bv 64 0x11ff74); C8 (Z_to_bv 64 0x120220); C8 (Z_to_bv 64 0x1204a8); C8 (Z_to_bv 64 0x120730)])
  ; (0x1700f8, [C8 (Z_to_bv 64 0x13e490); C8 (Z_to_bv 64 0x13e4a0); C8 (Z_to_bv 64 0x13e4b0)])
  ; (0x1721e0, [C8 (Z_to_bv 64 0x17621c)])     ].

Definition io_acc : list (Z * Z) :=
  [ (0x10e37, 10)
  ; (0x15022, 4)
  ; (0x163fc, 17)
  ; (0x16400, 128)
  ; (0x1ae97, 33)
  ; (0x1f7a4, 21)
  ; (0x1f7b9, 23)
  ; (0x21f40, 128)
  ; (0x230c8, 7)
  ; (0x230c8, 7)
  ; (0x38250, 16)
  ; (0x69dd00, 16)
  ; (0x13f72, 19)
  ; (0x14a7a, 1)
  ; (0x17ed9, 3)
  ; (0x1a5f0, 3)
  ; (0x201e7, 3)
  ; (0x20e60, 3)     ].

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc asegs m (fst r) (snd r)) io_acc.

Definition io_rngs : list (Z * Z) :=
  [ (0x173ff0, 0x174000); (0x178f70, 0x178f78);   (0x174148, 0x174150); (0x1740a0, 0x1740a8); (0x174068, 0x174070); (0x17621c, 0x176220); (0x178ed4, 0x178ed5); (0x16f840, 0x16f848); (0x16f960, 0x16f968); (0x16fce8, 0x16fcf0); (0x16fe18, 0x16fe20); (0x1700a8, 0x1700b0); (0x170358, 0x170360);
    (0x16bc60, 0x16bc70); (0x172038, 0x172040); (0x172118, 0x172128); (0x172db0, 0x172dc0); (0x172e30, 0x172e40); (0x172f68, 0x172f78);
    (0x173fa8, 0x173fb0); (0x174020, 0x174038); (0x178ed0, 0x178ed4); (0x178f18, 0x178f19); (0x20d23c, 0x20d23d); (0x20d560, 0x20d561);
    (0x16c300, 0x16c340); (0x16c3c0, 0x16c420);   (0x172dd0, 0x172df0);   (0x16fb88, 0x16fbb0);   (0x16fb38, 0x16fb40);   (0x16fa20, 0x16fa30); (0x172e20, 0x172e28); (0x173fd0, 0x173fe0); (0x20d2e6, 0x20d2e8);
      (0x16ff60, 0x16ff68); (0x172e28, 0x172e30);
      (0x16f2d8, 0x16f2e8); (0x16f4b0, 0x16f4c0); (0x16f4f8, 0x16f500); (0x16f510, 0x16f528); (0x16f550, 0x16f558); (0x16f560, 0x16f580); (0x171f10, 0x171f28); (0x171f40, 0x171f58); (0x171f68, 0x171f70); (0x1720f0, 0x1720f8); (0x172e48, 0x172e50); (0x172e50, 0x172e58); (0x173fe8, 0x173ff0);
      (0x16ff68, 0x16ff70);   (0x170b08, 0x170b10); (0x170b10, 0x170b38); (0x1700f8, 0x170110)  ;   (0x1721e0, 0x1721e8) ].

Lemma io_rngs_of : io_rngs = map (fun p => (fst p, fst p + Z.of_nat (cells_size (snd p)))) (io_rw ++ io_ro).
Proof. reflexivity. Qed.

Section Get.
Variable m : mem.
Hypothesis H : io_consts m.
Lemma io_rw_at : forall a cs, In (a, cs) io_rw -> rw_cells asegs m a cs.
Proof. intros a cs Hin. destruct H as (X & _ & _). exact (proj1 (Forall_forall _ _) X (a, cs) Hin). Qed.
Lemma io_ro_at : forall a cs, In (a, cs) io_ro -> ro_cells asegs m a cs.
Proof. intros a cs Hin. destruct H as (_ & X & _). exact (proj1 (Forall_forall _ _) X (a, cs) Hin). Qed.
Lemma io_acc_at : forall a n, In (a, n) io_acc -> acc asegs m a n.
Proof. intros a n Hin. destruct H as (_ & _ & X). exact (proj1 (Forall_forall _ _) X (a, n) Hin). Qed.
End Get.

Ltac io_in := cbn [io_rw io_ro io_acc In]; repeat (first [ left; reflexivity | right ]).

Definition CLI_RO : list (Z * list cell) :=
  [ (0x16c300, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x16c360); C8 (Z_to_bv 64 0xe8440); C8 (Z_to_bv 64 0xe85cc); C8 (Z_to_bv 64 0xe8758); C8 (Z_to_bv 64 0xbf7d8); C8 (Z_to_bv 64 0xc1dc8); C8 (Z_to_bv 64 0xc1f58)])
  ; (0x16c3c0, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x16c440); C8 (Z_to_bv 64 0xe83ec); C8 (Z_to_bv 64 0xbfa34); C8 (Z_to_bv 64 0xc236c); C8 (Z_to_bv 64 0xd4dc4); C8 (Z_to_bv 64 0xe74b0); C8 (Z_to_bv 64 0xe7c64); C8 (Z_to_bv 64 0xe87a0); C8 (Z_to_bv 64 0xe8900); C8 (Z_to_bv 64 0xe8a68); C8 (Z_to_bv 64 0xe8b54)])
  ; (0x172dd0, [C8 (Z_to_bv 64 0x16fb88); C8 (Z_to_bv 64 0x16f9b0); C8 (Z_to_bv 64 0x16f770); C8 (Z_to_bv 64 0x16fb38)])
  ; (0x16fb88, [C8 (Z_to_bv 64 0x16fb50); C8 (Z_to_bv 64 0x16fbc0); C8 (Z_to_bv 64 0x16fbe8); C8 (Z_to_bv 64 0x16fb78); C8 (Z_to_bv 64 0x70)])
  ; (0x16fb38, [C8 (Z_to_bv 64 0x70)])
  ; (0x16fa20, [C8 (Z_to_bv 64 0x112b6c); C8 (Z_to_bv 64 0x113740)])
  ; (0x172e20, [C8 (Z_to_bv 64 0x31ab0)])
  ; (0x173fd0, [C8 (Z_to_bv 64 0x1640a0); C8 (Z_to_bv 64 0x163fd0)])
  ; (0x20d2e6, [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)])
  ; (0x16ff60, [C8 (Z_to_bv 64 0x13b2a4)])
  ; (0x172e28, [C8 (Z_to_bv 64 0x6aec20)])
  ; (0x16f2d8, [C8 (Z_to_bv 64 0x16f4d8); C8 (Z_to_bv 64 0x318c8)])
  ; (0x16f4b0, [C8 (Z_to_bv 64 0x16f528); C8 (Z_to_bv 64 0x31987)])
  ; (0x16f4f8, [C8 (Z_to_bv 64 0x10adb0)])
  ; (0x16f510, [C8 (Z_to_bv 64 0x10b114); C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x16f568)])
  ; (0x16f550, [C8 (Z_to_bv 64 0x10bd88)])
  ; (0x16f560, [C8 (Z_to_bv 64 0x10b190); C8 (Z_to_bv 64 0x16f528); C8 (Z_to_bv 64 0x319a9); C8 (Z_to_bv 64 0x16f4b0)])
  ; (0x171f10, [C8 (Z_to_bv 64 0x14c72c); C8 (Z_to_bv 64 0x14c764); C8 (Z_to_bv 64 0x14c800)])
  ; (0x171f40, [C8 (Z_to_bv 64 0x14c924); C8 (Z_to_bv 64 0x14ca0c); C8 (Z_to_bv 64 0x14ca34)])
  ; (0x171f68, [C8 (Z_to_bv 64 0x14cae0)])
  ; (0x1720f0, [C8 (Z_to_bv 64 0x0)])
  ; (0x172e48, [C8 (Z_to_bv 64 0x1768e8)])
  ; (0x172e50, [C8 (Z_to_bv 64 0x1768e0)])
  ; (0x173fe8, [C8 (Z_to_bv 64 0x156698)])
  ; (0x16ff68, [C8 (Z_to_bv 64 0x13b2ac)])
  ; (0x170b08, [C8 (Z_to_bv 64 0x11fa30)])
  ; (0x170b10, [C8 (Z_to_bv 64 0x11fcc8); C8 (Z_to_bv 64 0x11ff74); C8 (Z_to_bv 64 0x120220); C8 (Z_to_bv 64 0x1204a8); C8 (Z_to_bv 64 0x120730)])
  ; (0x1700f8, [C8 (Z_to_bv 64 0x13e490); C8 (Z_to_bv 64 0x13e4a0); C8 (Z_to_bv 64 0x13e4b0)])
 ].
Definition cli_ro (m : mem) : Prop := Forall (fun p => ro_cells asegs m (fst p) (snd p)) CLI_RO.
Lemma cli_ro_of_io : forall m, io_consts m -> cli_ro m.
Proof.
  intros m (_ & X & _). unfold cli_ro, CLI_RO.
  repeat (apply Forall_cons; [apply (proj1 (Forall_forall _ _) X); io_in|]). apply Forall_nil.
Qed.
Lemma cli_ro_at : forall m a cs, cli_ro m -> In (a, cs) CLI_RO -> ro_cells asegs m a cs.
Proof. intros m a cs H Hin. exact (proj1 (Forall_forall _ _) H (a, cs) Hin). Qed.
Ltac cli_in := cbn [CLI_RO In]; repeat (first [ left; reflexivity | right ]).
