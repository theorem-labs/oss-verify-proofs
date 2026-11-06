(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec FxLin FxCore FxSubst FxSound FxMem FxStep FxEnt FxRgs FxFacts FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXH Require Import HxRebyte.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition hx_psrk (k : positive) (l : lin) (S : sst) : option sst :=
  if (Pos.ltb 32 k && lwf (s_next S) l)%bool
  then Some (SST (s_pc S) (rset (s_regs S) k l) (s_rgs S) (s_facts S) (s_next S) (s_resv S)) else None.

Lemma rkey_ne_big : forall (r : reg) (k : positive), (32 < k)%positive -> rkey r <> k.
Proof.
  intros r k Hk. destruct (decide (r = 0%bv)) as [->|Hr].
  - change (rkey 0%bv) with xH. lia.
  - destruct (rkey_succ r Hr) as (j & Hj & Ej). rewrite Ej. intros Hc.
    assert (X : Pos.to_nat (Pos.of_succ_nat j) = Pos.to_nat k) by (rewrite Hc; reflexivity).
    rewrite SuccNat2Pos.id_succ in X. lia.
Qed.

Section Rule.
Variable segs : list Segment.
#[using="Type"] Theorem hx_psrk_ok : forall k l S K, hx_psrk k l S = Some K ->
  hcall_rule0 segs S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros k l S K H. unfold hx_psrk in H.
  destruct (Pos.ltb 32 k && lwf (s_next S) l)%bool eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [Hk _]. apply Pos.ltb_lt in Hk.
  remember (rset (s_regs S) k l) as R' eqn:ER in H. injection H as <-.
  split; [|split; [cbn [s_next]; lia | reflexivity]].
  intros E ms Hd. exists ms, E. split; [apply ist_refl|]. split; [|split; [intros x Hx; reflexivity | intros x _; reflexivity]].
  intros E' Ha. pose proof (Hd E' Ha) as (Hpc0 & Hsvc0 & Hresv0 & HR0 & HG0 & HD0 & HF0 & Hfrm0).
  unfold sden0. cbn [s_pc s_regs s_rgs s_facts s_resv s_next].
  refine (conj Hpc0 (conj Hsvc0 (conj Hresv0 (conj _ (conj HG0 (conj HD0 (conj HF0 Hfrm0))))))).
  unfold regs_ok. intros r. rewrite ER. rewrite rget_rset_other by (apply rkey_ne_big; exact Hk). exact (HR0 r).
Qed.
End Rule.
(* [comment removed for export] *)
