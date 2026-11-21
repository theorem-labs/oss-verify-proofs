(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Fs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim StoreOk Frame Hoare RefMemcpyLib AgentLib FuzzMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.IK Require Import TSet MstepsGrows ZStep ZMem ZPrune ZTac ZArr ZCall ZCallL ZRegKeys.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.cks Require Import CkModel CkMathCrc CkMathAdler.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Fixpoint zlift (t : tree word) : tree Z :=
  match t with
  | TEmpty => TEmpty
  | TNode l v r => TNode (zlift l) (match v with Some x => Some (bv_unsigned x) | None => None end) (zlift r)
  end.

Lemma zden_zlift : forall t, zden (zlift t) = t.
Proof.
  induction t as [|l IHl v r IHr]; cbn; [reflexivity|].
  rewrite IHl, IHr. destruct v as [x|]; [|reflexivity]. rewrite w64_of_word. reflexivity.
Qed.

Lemma tget_zlift : forall k t,
  tget k (zlift t) = match tget k t with Some x => Some (bv_unsigned x) | None => None end.
Proof. induction k as [k IH|k IH|]; intros [|l v r]; cbn; auto. Qed.

Lemma zget_zlift : forall regs (r : reg), zget (zlift regs) (bv_key r) = bv_unsigned (reg_get regs r).
Proof.
  intros regs r. unfold zget, reg_get, bvmap_get. rewrite tget_zlift.
  destruct (tget (bv_key r) regs); reflexivity.
Qed.

Definition zpick (e : Z) (x : word) : Z := if bv_eqb (w64 e) x then e else bv_unsigned x.


Lemma zpick_hit : forall e, zpick e (w64 e) = e.
Proof. intros e. unfold zpick. rewrite bv_eqb_refl. reflexivity. Qed.

Fixpoint zback (g : positive -> Z) (t : tree word) : tree Z :=
  match t with
  | TEmpty => TEmpty
  | TNode l v r =>
      TNode (zback (fun k => g (xO k)) l)
            (match v with Some x => Some (zpick (g xH) x) | None => None end)
            (zback (fun k => g (xI k)) r)
  end.


Lemma tget_zback : forall t g k,
  tget k (zback g t) = match tget k t with Some x => Some (zpick (g k) x) | None => None end.
Proof.
  induction t as [|l IHl v r IHr]; intros g k; [destruct k; reflexivity|].
  destruct k as [k|k|]; cbn; [rewrite IHr | rewrite IHl |]; reflexivity.
Qed.

Lemma zget_zback : forall t g k,
  zget (zback g t) k = match tget k t with Some x => zpick (g k) x | None => 0 end.
Proof. intros t g k. unfold zget. rewrite tget_zback. destruct (tget k t); reflexivity. Qed.

Lemma getr_zkey : forall R (r : reg), bv_eqb r 0%bv = false -> getr (zden R) r = w64 (zget R (bv_key r)).
Proof. intros R r Hr. rewrite getr_zden. unfold zrd. rewrite <- bv_eqb0_is_x0, Hr. reflexivity. Qed.


Lemma getr_reg_get : forall regs (r : reg), bv_eqb r 0%bv = false -> getr regs r = reg_get regs r.
Proof. intros regs r H. unfold getr. rewrite H. reflexivity. Qed.

Lemma zback_kept : forall R regs' g (r : reg),
  bv_eqb r 0%bv = false -> rkeys (zden R) regs' ->
  getr regs' r = getr (zden R) r -> g (bv_key r) = zget R (bv_key r) ->
  zget (zback g regs') (bv_key r) = zget R (bv_key r).
Proof.
  intros R regs' g r Hr RK EQ Hg. rewrite zget_zback.
  rewrite (getr_reg_get regs' r Hr), (getr_zkey R r Hr) in EQ. unfold reg_get, bvmap_get in EQ.
  destruct (tget (bv_key r) regs') as [x|] eqn:T.
  - subst x. rewrite Hg. apply zpick_hit.
  -
    destruct (tget (bv_key r) (zden R)) as [y|] eqn:T0.
    + exfalso. apply (RK (bv_key r)); [rewrite T0; discriminate | exact T].
    + rewrite tget_zden in T0. unfold zget. destruct (tget (bv_key r) R); [discriminate | reflexivity].
Qed.


Definition gres (R : tree Z) (res : Z) (k : positive) : Z := if (k =? 11)%positive then res else zget R k.




















Fixpoint wranges (rs : list (Z * Z)) : list (word * Z) :=
  match rs with [] => [] | (lo, n) :: rs' => (Z_to_bv 64 lo, n) :: wranges rs' end.

Fixpoint ranges_lt (rs : list (Z * Z)) : Prop :=
  match rs with [] => True | (lo, n) :: rs' => 0 <= lo < two64 /\ ranges_lt rs' end.




Lemma kept_back : forall Rb l regs' res (r : reg) (k : positive),
  bv_eqb r 0%bv = false -> bv_key r = k -> (k =? 11)%positive = false ->
  rkeys (zden (zupd Rb l)) regs' -> getr regs' r = getr (zden (zupd Rb l)) r ->
  zget (zback (gres (zupd Rb l) res) regs') k = zget_l Rb l k.
Proof.
  intros Rb l regs' res r k Hr Hk H11 RK EQ. subst k.
  rewrite (zback_kept (zupd Rb l) regs' _ r Hr RK EQ); [apply zget_zupd|].
  unfold gres. rewrite H11. reflexivity.
Qed.

End FXG.
Ltac key_norm := repeat match goal with |- context [bv_key ?x] => let k := eval cbv in (bv_key x) in change (bv_key x) with k end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.



Lemma kept_back_cs : forall Rb l regs' res (r : reg) (k : positive),
  bv_eqb r 0%bv = false -> bv_key r = k -> (k =? 11)%positive = false -> In r callee_saved ->
  rkeys (zden (zupd Rb l)) regs' -> keeps_cs (zden (zupd Rb l)) regs' ->
  zget (zback (gres (zupd Rb l) res) regs') k = zget_l Rb l k.
Proof.
  intros Rb l regs' res r k Hr Hk H11 Hin RK KC.
  apply (kept_back Rb l regs' res r k Hr Hk H11 RK). apply KC. exact Hin.
Qed.

End FXG.
Ltac kept_cs r := apply (kept_back_cs _ _ _ _ r); [reflexivity | reflexivity | reflexivity | cbv; tauto | assumption | assumption].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.




End FXG.
