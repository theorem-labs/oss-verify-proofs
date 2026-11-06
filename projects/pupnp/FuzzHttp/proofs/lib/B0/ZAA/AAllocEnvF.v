(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ALayout APrim PEnv LJ LJU F_hooks F_alloc_env.
Import ListNotations.
Open Scope Z_scope.
Section ENVF.
  Context {HC : HasCeiling}.

  Definition aenv_out (iv : Z * Z) : Prop := snd iv <= 0x10000 \/ 0x609000 <= fst iv \/ (1598472 <= fst iv /\ snd iv <= 5858360).
  #[using="Type"] Lemma aenv_dj : forall W A k, Forall aenv_out W -> 0x10000 <= A -> ((A + k <= 1598472) \/ (5858360 <= A /\ A + k <= 0x609000)) -> disjoint_from W A k.
  Proof.
    intros W A k FW HA HK. apply dj_of_Forall. eapply Forall_impl; [| exact FW]. intros [a b] Z1. unfold aenv_out in Z1. cbn [fst snd] in *. lia.
  Qed.
  #[using="Type"] Lemma alloc_env_frame_m : forall W (m m' : mem), alloc_env m -> munch W m m' -> Forall aenv_out W -> alloc_env m'.
  Proof.
    intros W m m' AE MU FW. ae_split AE. unfold alloc_env.
    repeat match goal with |- _ /\ _ => split end;
      (eapply rw_cells_transport_mo; [eassumption| exact MU| apply aenv_dj; [exact FW| cbn [cells_size csize Nat.add]; lia| cbn [cells_size csize Nat.add]; lia]]).
  Qed.
  #[using="Type"] Lemma hooks_env_frame_m : forall W (m m' : mem), hooks_env m -> munch W m m' -> Forall aenv_out W -> hooks_env m'.
  Proof.
    intros W m m' HE MU FW. unfold hooks_env in *.
    eapply rw_cells_transport_mo; [exact HE| exact MU| apply aenv_dj; [exact FW| cbn [cells_size csize Nat.add]; lia| cbn [cells_size csize Nat.add]; lia]].
  Qed.
End ENVF.
