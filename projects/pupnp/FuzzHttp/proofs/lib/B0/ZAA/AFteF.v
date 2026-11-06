(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import LJ AEnv ALayout AFsEnv.
Import ListNotations.
Open Scope Z_scope.

Section FTE.
Context {HC : HasCeiling}.
Variables (THR DTV TLSB BLK FSB0 : Z).

Definition fte_apart (W : list (Z * Z)) : Prop :=
  disjoint_from W 0xacb18 8 /\ disjoint_from W 0xaba20 24 /\ disjoint_from W (A0_TP - 8) 8 /\ disjoint_from W (DTV + 8) 8
  /\ disjoint_from W (TLSB - 2048) 8 /\ disjoint_from W 0x1460f1 1 /\ disjoint_from W 0xaad80 8 /\ disjoint_from W 0x143fd8 4
  /\ disjoint_from W (A0_TP + 8) 8 /\ disjoint_from W (BLK + 24) 8 /\ disjoint_from W (THR + 48) 16.

#[using="Type"] Lemma fs_tls_env_frame_m : forall W (m m' : mem),
  fs_tls_env THR DTV TLSB BLK FSB0 m -> munch W m m' -> fte_apart W -> fs_tls_env THR DTV TLSB BLK FSB0 m'.
Proof.
  intros W m m' (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & (e & C10 & ER) & (tb & te & C11) & PURE) MU
    (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11).
  unfold fs_tls_env.
  split; [eapply rw_cells_transport_mo; [exact C1| exact MU| exact D1]|].
  split; [eapply rw_cells_transport_mo; [exact C2| exact MU| exact D2]|].
  split; [eapply rw_cells_transport_mo; [exact C3| exact MU| exact D3]|].
  split; [eapply rw_cells_transport_mo; [exact C4| exact MU| exact D4]|].
  split; [eapply rw_cells_transport_mo; [exact C5| exact MU| exact D5]|].
  split; [eapply rw_cells_transport_mo; [exact C6| exact MU| exact D6]|].
  split; [eapply rw_cells_transport_mo; [exact C7| exact MU| exact D7]|].
  split; [eapply rw_cells_transport_mo; [exact C8| exact MU| exact D8]|].
  split; [eapply rw_cells_transport_mo; [exact C9| exact MU| exact D9]|].
  split; [exists e; split; [eapply rw_cells_transport_mo; [exact C10| exact MU| exact D10]| exact ER]|].
  split; [exists tb, te; eapply rw_cells_transport_mo; [exact C11| exact MU| exact D11]|].
  exact PURE.
Qed.

#[using="Type"] Lemma fs_tls_env_frame_g : forall W (m m' : mem),
  fs_tls_env THR DTV TLSB BLK FSB0 m -> gmunch W m m' -> wmono asegs m m' -> fte_apart W -> fs_tls_env THR DTV TLSB BLK FSB0 m'.
Proof.
  intros W m m' (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & (e & C10 & ER) & (tb & te & C11) & PURE) GM WM
    (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11).
  unfold fs_tls_env.
  split; [eapply rw_cells_gtransport; [exact C1| exact GM| exact WM| exact D1]|].
  split; [eapply rw_cells_gtransport; [exact C2| exact GM| exact WM| exact D2]|].
  split; [eapply rw_cells_gtransport; [exact C3| exact GM| exact WM| exact D3]|].
  split; [eapply rw_cells_gtransport; [exact C4| exact GM| exact WM| exact D4]|].
  split; [eapply rw_cells_gtransport; [exact C5| exact GM| exact WM| exact D5]|].
  split; [eapply rw_cells_gtransport; [exact C6| exact GM| exact WM| exact D6]|].
  split; [eapply rw_cells_gtransport; [exact C7| exact GM| exact WM| exact D7]|].
  split; [eapply rw_cells_gtransport; [exact C8| exact GM| exact WM| exact D8]|].
  split; [eapply rw_cells_gtransport; [exact C9| exact GM| exact WM| exact D9]|].
  split; [exists e; split; [eapply rw_cells_gtransport; [exact C10| exact GM| exact WM| exact D10]| exact ER]|].
  split; [exists tb, te; eapply rw_cells_gtransport; [exact C11| exact GM| exact WM| exact D11]|].
  exact PURE.
Qed.
End FTE.
