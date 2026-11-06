(* reac-pw/fuzz_link, image A: the composition of kernel's walk (link-a/plan/kernel-plan.md (internal record, sha256 440bf3b40ab7)
   section 3). From the phase lemmas, stated here as the premises of `kn_compose` exactly as the segment lanes prove them
   (link-a/plan/kernel-lanes.md (internal record, sha256 18c8d69749d5), its lane table), the whole call: `kstart SK B (kpost SK B)`. The
   three loops go by induction on their measures: chunks (c - ci, at most 3), messages (m - k, at most 5), attributes (the attributes
   left, at most 4). A measure predicate `fun _ v => 1 <= v <= n` with n = 0 holds of nothing, so the loop head at n = 0 is vacuous.
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG00 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkList LinkPa kernel_defs.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
Variable B : asyms.

#[local] Notation KF := (kfrom SK B).
#[local] Notation P := (kpost SK B).

(* the measure predicates *)
Definition kmeas (n : Z) : kcx -> Z -> Prop := fun _ v => 1 <= v <= n.

Section c.
Hypothesis H_entry : forall POST, KF POST (kin_poison B) -> kstart SK B POST.
Hypothesis H_flags : forall POST, KF POST (kin_err B) -> KF POST (kin_poison B).
Hypothesis H_gnl : forall POST, KF POST (kin_setup B) -> KF POST (kin_exit B) -> KF POST (kin_err B).
Hypothesis H_setup : forall POST (Rc : kcx -> Z -> Prop), (forall cx v, 1 <= v <= 3 -> Rc cx v) ->
  KF POST (kin_head B Rc) -> KF POST (kin_setup B).
Hypothesis H_head : forall POST Rc,
  KF POST (kin_raw B Rc) -> KF POST (kin_msg0 B Rc) -> KF POST (kin_mz B Rc) -> KF POST (kin_head B Rc).
Hypothesis H_msg0 : forall POST Rc (Rm : kcx -> Z -> Prop), (forall cx v, 1 <= v <= 5 -> Rm cx v) ->
  KF POST (kin_loop B Rc Rm) -> KF POST (kin_qmsg B Rc) -> KF POST (kin_msg0 B Rc).
Hypothesis H_mz : forall POST Rc, KF POST (kin_qmsg B Rc) -> KF POST (kin_mz B Rc).
Hypothesis H_disp : forall POST Rc Rm, (forall kd, 0 <= kd < 8 -> KF POST (kin_kind B Rc Rm kd)) ->
  KF POST (kin_qmsg B Rc) -> KF POST (kin_loop B Rc Rm).
Hypothesis H_k1 : forall POST Rc Rm, KF POST (kin_next B Rc Rm) -> KF POST (kin_kind B Rc Rm 1).
Hypothesis H_k2 : forall POST Rc Rm, KF POST (kin_next B Rc Rm) -> KF POST (kin_kind B Rc Rm 2).
Hypothesis H_k3 : forall POST Rc Rm, KF POST (kin_next B Rc Rm) -> KF POST (kin_kind B Rc Rm 3).
Hypothesis H_k4 : forall POST Rc Rm, KF POST (kin_next B Rc Rm) -> KF POST (kin_kind B Rc Rm 4).
Hypothesis H_k5 : forall POST Rc Rm, KF POST (kin_next B Rc Rm) -> KF POST (kin_kind B Rc Rm 5).
Hypothesis H_k6 : forall POST Rc Rm, KF POST (kin_next B Rc Rm) -> KF POST (kin_kind B Rc Rm 6).
Hypothesis H_k07 : forall POST Rc Rm (Ra : kcx -> Z -> Prop), (forall cx v, 1 <= v <= 4 -> Ra cx v) ->
  KF POST (kin_attr B Rc Rm Ra) -> KF POST (kin_nlend B Rc Rm) ->
  forall kd, kd = 0 \/ kd = 7 -> KF POST (kin_kind B Rc Rm kd).
Hypothesis H_atxt : forall POST Rc Rm Ra,
  KF POST (kin_txt B Rc Rm Ra) -> KF POST (kin_acase B Rc Rm Ra KP_A0 ka_empty) -> KF POST (kin_attr B Rc Rm Ra).
Hypothesis H_txt : forall POST Rc Rm Ra,
  KF POST (kin_alat B Rc Rm Ra) -> KF POST (kin_acase B Rc Rm Ra KP_A23 ka_23) ->
  KF POST (kin_acase B Rc Rm Ra KP_A5 ka_5) -> KF POST (kin_txt B Rc Rm Ra).
Hypothesis H_a0e : forall POST Rc Rm Ra,
  KF POST (kin_alat B Rc Rm Ra) -> KF POST (kin_acase B Rc Rm Ra KP_A0 ka_empty).
Hypothesis H_a23 : forall POST Rc Rm Ra,
  KF POST (kin_alat B Rc Rm Ra) -> KF POST (kin_acase B Rc Rm Ra KP_A23 ka_23).
Hypothesis H_a5 : forall POST Rc Rm Ra,
  KF POST (kin_alat B Rc Rm Ra) -> KF POST (kin_acase B Rc Rm Ra KP_A5 ka_5).
Hypothesis H_alatch : forall POST Rc Rm Ra (Ra' : kcx -> Z -> Prop),
  (forall cx v, Ra cx v -> 2 <= v -> Ra' cx (v - 1)) ->
  KF POST (kin_attr B Rc Rm Ra') -> KF POST (kin_nlend B Rc Rm) -> KF POST (kin_alat B Rc Rm Ra).
Hypothesis H_nlend : forall POST Rc Rm, KF POST (kin_next B Rc Rm) -> KF POST (kin_nlend B Rc Rm).
Hypothesis H_next : forall POST Rc Rm (Rm' : kcx -> Z -> Prop),
  (forall cx v, Rm cx v -> 2 <= v -> Rm' cx (v - 1)) ->
  KF POST (kin_loop B Rc Rm') -> KF POST (kin_qmsg B Rc) -> KF POST (kin_next B Rc Rm).
Hypothesis H_qmsg : forall POST Rc, KF POST (kin_latch B Rc) -> KF POST (kin_qmsg B Rc).
Hypothesis H_raw : forall POST Rc, KF POST (kin_latch B Rc) -> KF POST (kin_raw B Rc).
Hypothesis H_latch : forall POST Rc (Rc' : kcx -> Z -> Prop),
  (forall cx v, Rc cx v -> 2 <= v -> Rc' cx (v - 1)) ->
  KF POST (kin_head B Rc') -> KF POST (kin_exit B) -> KF POST (kin_latch B Rc).
Hypothesis H_exit : KF P (kin_exit B).

Lemma kmeas_step : forall n cx v, kmeas (Z.of_nat (S n)) cx v -> 2 <= v -> kmeas (Z.of_nat n) cx (v - 1).
Proof. intros n cx v H H2. unfold kmeas in *. lia. Qed.

(* the attribute loop, under a fixed chunk and message measure, given nl_end *)
Lemma kn_attr_loop : forall Rc Rm, KF P (kin_nlend B Rc Rm) ->
  forall n : nat, KF P (kin_attr B Rc Rm (kmeas (Z.of_nat n))).
Proof.
  intros Rc Rm HNL n. induction n as [|n IH].
  - intros cx fpos k2 ly3 S3 W3 ms3 md3 _ _ _ HI.
    destruct HI as (c & ci & j & m & k & n & f & adv & hd & kd & left & _ & _ & HRa & _).
    unfold kmeas in HRa. lia.
  - assert (HAL : KF P (kin_alat B Rc Rm (kmeas (Z.of_nat (S n)))))
      by (apply (H_alatch P Rc Rm _ (kmeas (Z.of_nat n)) (kmeas_step n)); [exact IH | exact HNL]).
    apply H_atxt.
    + apply H_txt; [exact HAL | apply H_a23; exact HAL | apply H_a5; exact HAL].
    + apply H_a0e. exact HAL.
Qed.

(* the message loop, under a fixed chunk measure, given the message path's end *)
Lemma kn_msg_loop : forall Rc, KF P (kin_qmsg B Rc) ->
  forall n : nat, KF P (kin_loop B Rc (kmeas (Z.of_nat n))).
Proof.
  intros Rc HQ n. induction n as [|n IH].
  - intros cx fpos k2 ly3 S3 W3 ms3 md3 _ _ _ HI.
    destruct HI as (c & ci & j & m & k & n & f & adv & _ & HRm & _).
    unfold kmeas in HRm. lia.
  - set (Rm := kmeas (Z.of_nat (S n))).
    assert (HNX : KF P (kin_next B Rc Rm))
      by (apply (H_next P Rc Rm (kmeas (Z.of_nat n)) (kmeas_step n)); [exact IH | exact HQ]).
    apply H_disp; [|exact HQ].
    intros kd Hkd.
    assert (Hc : kd = 0 \/ kd = 1 \/ kd = 2 \/ kd = 3 \/ kd = 4 \/ kd = 5 \/ kd = 6 \/ kd = 7) by lia.
    destruct Hc as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]].
    + apply (H_k07 P Rc Rm (kmeas (Z.of_nat 4))); [unfold kmeas; intros; lia | | | left; reflexivity].
      * apply kn_attr_loop. apply H_nlend. exact HNX.
      * apply H_nlend. exact HNX.
    + apply H_k1. exact HNX.
    + apply H_k2. exact HNX.
    + apply H_k3. exact HNX.
    + apply H_k4. exact HNX.
    + apply H_k5. exact HNX.
    + apply H_k6. exact HNX.
    + apply (H_k07 P Rc Rm (kmeas (Z.of_nat 4))); [unfold kmeas; intros; lia | | | right; reflexivity].
      * apply kn_attr_loop. apply H_nlend. exact HNX.
      * apply H_nlend. exact HNX.
Qed.

(* the chunk loop *)
Lemma kn_chunk_loop : forall n : nat, KF P (kin_head B (kmeas (Z.of_nat n))).
Proof.
  intros n. induction n as [|n IH].
  - intros cx fpos k2 ly3 S3 W3 ms3 md3 _ _ _ HI.
    destruct HI as (c & ci & j & adv & HRc & _). unfold kmeas in HRc. lia.
  - set (Rc := kmeas (Z.of_nat (S n))).
    assert (HLT : KF P (kin_latch B Rc))
      by (apply (H_latch P Rc (kmeas (Z.of_nat n)) (kmeas_step n)); [exact IH | exact H_exit]).
    assert (HQ : KF P (kin_qmsg B Rc)) by (apply H_qmsg; exact HLT).
    apply H_head.
    + apply H_raw. exact HLT.
    + apply (H_msg0 P Rc (kmeas (Z.of_nat 5))); [unfold kmeas; intros; lia | | exact HQ].
      apply kn_msg_loop. exact HQ.
    + apply H_mz. exact HQ.
Qed.

Theorem kn_compose : kstart SK B P.
Proof.
  apply H_entry. apply H_flags. apply H_gnl; [|exact H_exit].
  apply (H_setup P (kmeas (Z.of_nat 3))); [unfold kmeas; intros; lia|].
  apply kn_chunk_loop.
Qed.
End c.
End a.
