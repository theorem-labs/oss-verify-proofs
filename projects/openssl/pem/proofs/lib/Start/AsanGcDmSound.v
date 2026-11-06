(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import PropExec AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import AsanGcDm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

Module GCDS.
Section Sound.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable ISP : Z.
Variable FS0 : Fs.Fs.

Lemma node_filter_sound : forall (f : kentry -> bool),
  node1_stmt SEGS A nx0 LIMIT SINV argH ISP FS0 always (fun cs => Some (set_kn cs (List.filter f (kn cs)))).
Proof.
  intros f cs cs' E R FULL model T HC _ Hn Hk. injection Hn as <-.
  apply (Hk E R FULL model).
  - split; apply env_agree_refl.
  - apply cs_ok_set_kn; [exact HC|]. apply know_ok_filter. exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC).
  - reflexivity.
Qed.

Theorem node_drop_zero_sound : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH ISP FS0 always (fun cs => GCD.node_drop_zero cs args).
Proof.
  intros args cs cs' E R FULL model T HC Hpre Hn Hk. unfold GCD.node_drop_zero in Hn.
  destruct args as [|b [|? ?]]; try discriminate Hn.
  exact (node_filter_sound (GCD.keep_zero b) cs cs' E R FULL model T HC Hpre Hn Hk).
Qed.
Theorem node_drop_vals_sound : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH ISP FS0 always (fun cs => GCD.node_drop_vals cs args).
Proof.
  intros args cs cs' E R FULL model T HC Hpre Hn Hk. unfold GCD.node_drop_vals in Hn.
  destruct args as [|b [|? ?]]; try discriminate Hn.
  exact (node_filter_sound (GCD.keep_vals b) cs cs' E R FULL model T HC Hpre Hn Hk).
Qed.
End Sound.
End GCDS.
