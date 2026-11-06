(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec StoreOk ShapeAlg AgentLib AsanAcct AsanAcctShape AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxPlanSound2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Definition node_refront (args : list expr) (cs : acs) : option acs :=
  match args with
  | [e; ELit lo; ELit hi] =>
      if existsb (kentry_eqb (KRange e lo hi)) (kn cs) then Some (add_kn cs [KRange e lo hi]) else None
  | _ => None
  end.

Section Sound.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable ISP : Z.
Variable FS0 : Fs.Fs.

Theorem node_refront_sound : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH ISP FS0 always (node_refront args).
Proof.
  intros args cs cs' E R FULL model T HC _ Hn Hk. unfold node_refront in Hn.
  destruct args as [|e [|[lo| | | | | | |] [|[hi| | | | | | |] [|]]]]; try discriminate Hn.
  destruct (existsb (kentry_eqb (KRange e lo hi)) (kn cs)) eqn:Hex; [|discriminate].
  injection Hn as <-.
  apply existsb_exists in Hex as [K [Hin Heq]]. apply kentry_eqb_eq in Heq. subst K.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  assert (Hrefl : forall x, env_agree x E E) by (intros x; split; [intros; reflexivity | reflexivity]).
  apply (Hk E R FULL model (conj (Hrefl _) (Hrefl _))); [|reflexivity].
  unfold add_kn. apply (cs_ok_set_kn SEGS A LIMIT SINV argH ISP FS0); [exact HC|]. constructor; [|exact HK].
  exact (proj1 (Forall_forall _ _) HK _ Hin).
Qed.
End Sound.
