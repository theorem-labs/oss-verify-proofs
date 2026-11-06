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

Definition node_rezero (args : list expr) (cs : acs) : option acs :=
  match args with
  | [b; ELit off; ELit len] =>
      if (Z.leb 1 len && Z.ltb len (2 ^ 63) && kzero_x (kn cs) (kn cs) b off (ELit len))%bool then
        Some (add_kn cs [KZero (SA b off) (ELit len)])
      else None
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

Theorem node_rezero_sound : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH ISP FS0 always (node_rezero args).
Proof.
  intros args cs cs' E R FULL model T HC _ Hn Hk. unfold node_rezero in Hn.
  destruct args as [|b [|[off| | | | | | |] [|[len| | | | | | |] [|]]]]; try discriminate Hn.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Ht; [|discriminate] end.
  apply andb_prop in Ht as [Ht Hz]. apply andb_prop in Ht as [H0 H1].
  apply Z.leb_le in H0. apply Z.ltb_lt in H1.
  injection Hn as <-.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  destruct (kzero_x_sound0 SEGS E _ (kn cs) (kn cs) b off (ELit len) HK HK Hz) as (Hm & F1 & F2).
  assert (Hrefl : forall x, env_agree x E E) by (intros x; split; [intros; reflexivity | reflexivity]).
  apply (Hk E R FULL model (conj (Hrefl _) (Hrefl _))); [|reflexivity].
  unfold add_kn. apply (cs_ok_set_kn SEGS A LIMIT SINV argH ISP FS0); [exact HC|]. constructor; [|exact HK].
  assert (Hlen : elenZ E (ELit len) = len) by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
  cbn [kentry_ok]. split; [rewrite Hlen in *; unfold flat; lia | exact Hm].
Qed.
End Sound.
