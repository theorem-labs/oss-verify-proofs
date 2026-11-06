(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad Stdio Driver Prog.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize Bridge TSim.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require AssembleP0.
From OSSVerify.pupnp.FuzzHttp.images Require AsanUbsan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7 Require Import TSimS.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Notation tsh := (tshape node nstep nexit) (only parsing).

From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Export Segs.
Definition imgA0 : Image := mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.

Definition cfgA0 (en : ExecEntry) (inp : ProcInput) : config :=
  match en with mkEntry sp brk mb rnd =>
    init_config AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mb rnd target_alloc_limit inp
  end.

Definition ASt : Type := stdout_st.
Definition aget_so : ASt -> stdout_st := fun so => so.
Definition aset_so : stdout_st -> ASt -> ASt := fun so _ => so.
Definition ioA : IOStyle ASt := io_S aget_so aset_so.
Definition amalloc0 (n : Z) : Monad.M ASt (option unit) := mret (Some tt).
Definition afree0 (p : unit) : Monad.M ASt unit := mret tt.

Definition drv_preA (rs : Z) (argv : list (list Z)) : Monad.M ASt (at_parser (ptr:=unit)) :=
  drv_pre ioA amalloc0 afree0 rs argv.

Definition KLEAF_A (r : exc (at_parser (ptr:=unit) * ASt)) (mo : Model) : TSet :=
  match r with
  | Ok p => AssembleP0.PSH (Z.to_nat (ap_calls (fst p))) stdout_init (m_fs mo)
  | Unr => t_nil
  end.

Definition T_A0main (rs : Z) (argv : list (list byte)) (moM : Model) : TSet :=
  tsh (drv_preA rs (argv_Z argv) stdout_init) moM KLEAF_A.

Definition LPA (rP : exc (at_parser (ptr:=bptr) * PState)) (moP : Model) (rA : exc (at_parser (ptr:=unit) * ASt)) (moA : Model) : Prop :=
  match rP, rA with
  | Ok (apP, sP), Ok (apA, soA) => ap_calls apP = ap_calls apA /\ m_fs moP = m_fs moA
  | Unr, Unr => True
  | _, _ => False
  end.

Lemma KLEAF_agree : forall rP moP rA moA, LPA rP moP rA moA -> t_eq (AssembleP0.KLEAF rP moP) (KLEAF_A rA moA).
Proof.
  intros [|[apP sP]] moP [|[apA soA]] moA H; cbn in H |- *; try contradiction; [apply t_eq_refl|].
  destruct H as [-> ->]. apply t_eq_refl.
Qed.

Definition fdfs_eq (moP moA : Model) : Prop := m_fds moP = m_fds moA /\ m_fs moP = m_fs moA.

