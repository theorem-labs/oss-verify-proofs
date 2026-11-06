(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import PropExec MState Mem Cells Step ImageA.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.A Require Import Shadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
  [ (0x178da8, [C8 (Z_to_bv 64 0x170000); C8 (Z_to_bv 64 0x160970)])
  ; (0x17d6f0, [C8 (Z_to_bv 64 0)]) ].

Definition io_ro : list (Z * list cell) :=
  [ (0x171180, [C8 (Z_to_bv 64 0xba438); C8 (Z_to_bv 64 0x5af9c)])
  ; (0x176e48, [C8 (Z_to_bv 64 0x17bb10)])
  ; (0x176f20, [C8 (Z_to_bv 64 0x158304); C8 (Z_to_bv 64 0)])
  ; (0x177bb8, [C8 (Z_to_bv 64 0x176e48); C8 (Z_to_bv 64 0)])
  ; (0x177c18, [C8 (Z_to_bv 64 0x17be10); C8 (Z_to_bv 64 0x17c750)])
  ; (0x177d10, [C8 (Z_to_bv 64 0x171190); C8 (Z_to_bv 64 0x171180)])
  ; (0x178d60, [C8 (Z_to_bv 64 0x178d60)])
  ; (0x178dd8, [C8 (Z_to_bv 64 0x16706c); C8 (Z_to_bv 64 0x160d88); C8 (Z_to_bv 64 0x167088)])
  ; (0x17d650, [C4 (Z_to_bv 64 1)])
  ; (0x17d698, [C1 (Z_to_bv 8 1)])
  ; (0x2119bc, [C1 (Z_to_bv 8 1)])
  ; (0x211ce0, [C1 (Z_to_bv 8 0)])
  ; (0x171720, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x171780); C8 (Z_to_bv 64 0xefaf0); C8 (Z_to_bv 64 0xefc90); C8 (Z_to_bv 64 0xefe30); C8 (Z_to_bv 64 0xbbfb0); C8 (Z_to_bv 64 0xbf0f0); C8 (Z_to_bv 64 0xbf2d8)])
  ; (0x1717e0, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x171860); C8 (Z_to_bv 64 0xefa9c); C8 (Z_to_bv 64 0xbc250); C8 (Z_to_bv 64 0xbf72c); C8 (Z_to_bv 64 0xd7114); C8 (Z_to_bv 64 0xee9ac); C8 (Z_to_bv 64 0xef250); C8 (Z_to_bv 64 0xefe78); C8 (Z_to_bv 64 0xeffec); C8 (Z_to_bv 64 0xf0160); C8 (Z_to_bv 64 0xf024c)])
  ; (0x177c08, [C8 (Z_to_bv 64 0x302e8)])
  ; (0x178d88, [C8 (Z_to_bv 64 0x169540); C8 (Z_to_bv 64 0x169470)])
  ; (0x211a66, [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)])
  ; (0x1715e8, [C8 (Z_to_bv 64 0x11aafc); C8 (Z_to_bv 64 0xb332c); C8 (Z_to_bv 64 8)])
  ; (0x177bd0, [C8 (Z_to_bv 64 0x174b90); C8 (Z_to_bv 64 0x174c10)])
  ; (0x174d70, [C8 (Z_to_bv 64 0x140ce4)])
  ; (0x177c10, [C8 (Z_to_bv 64 0x6b2b60)])     ].

Definition io_acc : list (Z * Z) :=
  [ (0x10e14, 10)
  ; (0x14fcd, 4)
  ; (0x16358, 17)
  ; (0x16340, 128)
  ; (0x1ace4, 33)
  ; (0x1f401, 21)
  ; (0x1f416, 23)
  ; (0x21b80, 128)
  ; (0x22da6, 7)
  ; (0x22da6, 7)
  ; (0x368b0, 16)
  ; (0x6a2480, 16) ].

Definition io_consts (m : mem) : Prop :=
  Forall (fun p => rw_cells bsegs m (fst p) (snd p)) io_rw
  /\ Forall (fun p => ro_cells bsegs m (fst p) (snd p)) io_ro
  /\ Forall (fun r => acc bsegs m (fst r) (snd r)) io_acc.

Definition io_rngs : list (Z * Z) :=
  [ (0x178da8, 0x178db8); (0x17d6f0, 0x17d6f8);
    (0x171180, 0x171190); (0x176e48, 0x176e50); (0x176f20, 0x176f30); (0x177bb8, 0x177bc8); (0x177c18, 0x177c28); (0x177d10, 0x177d20);
    (0x178d60, 0x178d68); (0x178dd8, 0x178df0); (0x17d650, 0x17d654); (0x17d698, 0x17d699); (0x2119bc, 0x2119bd); (0x211ce0, 0x211ce1);
    (0x171720, 0x171760); (0x1717e0, 0x171840); (0x177c08, 0x177c10); (0x178d88, 0x178d98); (0x211a66, 0x211a68);
    (0x1715e8, 0x171600); (0x177bd0, 0x177be0); (0x174d70, 0x174d78); (0x177c10, 0x177c18) ].

Lemma io_rngs_of : io_rngs = map (fun p => (fst p, fst p + Z.of_nat (cells_size (snd p)))) (io_rw ++ io_ro).
Proof. reflexivity. Qed.

Section Get.
Variable m : mem.
Hypothesis H : io_consts m.
Lemma io_rw_at : forall a cs, In (a, cs) io_rw -> rw_cells bsegs m a cs.
Proof. intros a cs Hin. destruct H as (X & _ & _). exact (proj1 (Forall_forall _ _) X (a, cs) Hin). Qed.
Lemma io_ro_at : forall a cs, In (a, cs) io_ro -> ro_cells bsegs m a cs.
Proof. intros a cs Hin. destruct H as (_ & X & _). exact (proj1 (Forall_forall _ _) X (a, cs) Hin). Qed.
Lemma io_acc_at : forall a n, In (a, n) io_acc -> acc bsegs m a n.
Proof. intros a n Hin. destruct H as (_ & _ & X). exact (proj1 (Forall_forall _ _) X (a, n) Hin). Qed.
End Get.

Ltac io_in := cbn [io_rw io_ro io_acc In]; repeat (first [ left; reflexivity | right ]).

Definition CLI_RO : list (Z * list cell) :=
  [ (0x171720, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x171780); C8 (Z_to_bv 64 0xefaf0); C8 (Z_to_bv 64 0xefc90); C8 (Z_to_bv 64 0xefe30); C8 (Z_to_bv 64 0xbbfb0); C8 (Z_to_bv 64 0xbf0f0); C8 (Z_to_bv 64 0xbf2d8)])
  ; (0x1717e0, [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x171860); C8 (Z_to_bv 64 0xefa9c); C8 (Z_to_bv 64 0xbc250); C8 (Z_to_bv 64 0xbf72c); C8 (Z_to_bv 64 0xd7114); C8 (Z_to_bv 64 0xee9ac); C8 (Z_to_bv 64 0xef250); C8 (Z_to_bv 64 0xefe78); C8 (Z_to_bv 64 0xeffec); C8 (Z_to_bv 64 0xf0160); C8 (Z_to_bv 64 0xf024c)])
  ; (0x177c08, [C8 (Z_to_bv 64 0x302e8)])
  ; (0x178d88, [C8 (Z_to_bv 64 0x169540); C8 (Z_to_bv 64 0x169470)])
  ; (0x211a66, [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)])
  ; (0x1715e8, [C8 (Z_to_bv 64 0x11aafc); C8 (Z_to_bv 64 0xb332c); C8 (Z_to_bv 64 8)])
  ; (0x177bd0, [C8 (Z_to_bv 64 0x174b90); C8 (Z_to_bv 64 0x174c10)])
  ; (0x174d70, [C8 (Z_to_bv 64 0x140ce4)])
  ; (0x177c10, [C8 (Z_to_bv 64 0x6b2b60)])     ].
Definition cli_ro (m : mem) : Prop := Forall (fun p => ro_cells bsegs m (fst p) (snd p)) CLI_RO.
Lemma cli_ro_of_io : forall m, io_consts m -> cli_ro m.
Proof.
  intros m (_ & X & _). unfold cli_ro, CLI_RO.
  repeat (apply Forall_cons; [apply (proj1 (Forall_forall _ _) X); io_in|]). apply Forall_nil.
Qed.
Lemma cli_ro_at : forall m a cs, cli_ro m -> In (a, cs) CLI_RO -> ro_cells bsegs m a cs.
Proof. intros m a cs H Hin. exact (proj1 (Forall_forall _ _) H (a, cs) Hin). Qed.
Ltac cli_in := cbn [CLI_RO In]; repeat (first [ left; reflexivity | right ]).
