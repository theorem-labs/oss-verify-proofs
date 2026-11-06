(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF ITreeA ModelX MmXfer NodesA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AProto.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Unset Lia Cache.

Section CANSEC1. Context {rc : runConstT}.
Section Core.
Variable NMAX : nat.

Definition postT (R : Type) : Type := R -> footprint -> alw -> Model -> Prop.

Fixpoint TS {R} (RNG : footprint) (A : alw) (t : itree node (exc R)) (mo : Model) (Q : postT R) {struct t} : Prop :=
  acct_ok NMAX RNG A mo /\
  match t with
  | Ret Unr => False
  | Ret (Ok r) => Q r RNG A mo
  | Vis n k => nsafeA NMAX n mo /\ (forall code mo', ~ nexitA n mo code mo') /\
      forall rsp mo' evs, nstepA n mo rsp mo' evs ->
        evs = [] /\ exists RNG' A', fstepS n rsp RNG RNG' /\ alw_le A A' /\ TS RNG' A' (k rsp) mo' Q
  end.

Lemma TS_acct : forall {R} RNG A (t : itree node (exc R)) mo Q, TS RNG A t mo Q -> acct_ok NMAX RNG A mo.
Proof. intros R RNG A [[|r]|n k] mo Q H; exact (proj1 H). Qed.

Lemma TS_mono : forall {R} (t : itree node (exc R)) RNG A mo (Q Q' : postT R),
  TS RNG A t mo Q -> (forall r RNG' A' mo', acct_ok NMAX RNG' A' mo' -> Q r RNG' A' mo' -> Q' r RNG' A' mo') -> TS RNG A t mo Q'.
Proof.
  intros R t. induction t as [[|r]|n k IH]; intros RNG A mo Q Q' H HQ; cbn in H |- *.
  - destruct H as [_ []].
  - destruct H as [HA HQ1]. split; [exact HA| apply HQ; assumption].
  - destruct H as (HA & HS & HX & HK). split; [exact HA|]. split; [exact HS|]. split; [exact HX|].
    intros rsp mo' evs Hst. destruct (HK rsp mo' evs Hst) as (E & RNG' & A' & HF & HL & HT).
    split; [exact E|]. exists RNG', A'. split; [exact HF|]. split; [exact HL|]. eapply IH; [exact HT| exact HQ].
Qed.

Lemma TS_ret_ok : forall {X} (x : X) RNG A mo (Q : postT X),
  acct_ok NMAX RNG A mo -> Q x RNG A mo -> TS RNG A (Ret (Ok x)) mo Q.
Proof. intros. cbn. split; assumption. Qed.

Lemma TS_event : forall {R} n (d : resp -> option Z) (f : Z -> itree node (exc R)) RNG A mo Q,
  acct_ok NMAX RNG A mo -> nsafeA NMAX n mo -> (forall code mo', ~ nexitA n mo code mo') ->
  (forall rsp mo' evs, nstepA n mo rsp mo' evs ->
     evs = [] /\ exists z RNG' A', d rsp = Some z /\ fstepS n rsp RNG RNG' /\ alw_le A A' /\ TS RNG' A' (f z) mo' Q) ->
  TS RNG A (ebind (enode n d) f) mo Q.
Proof.
  intros R n d f RNG A mo Q HA HS HX HK. unfold enode. rewrite ebind_vis. cbn [TS]. split; [exact HA|]. split; [exact HS|]. split; [exact HX|].
  intros rsp mo' evs Hst. destruct (HK rsp mo' evs Hst) as (E & z & RNG' & A' & Hd & HF & HL & HT).
  split; [exact E|]. exists RNG', A'. split; [exact HF|]. split; [exact HL|]. rewrite Hd. rewrite ebind_ret_ok. exact HT.
Qed.

Lemma TS_sbind : forall {X Y} (t : AM X) (f : X -> AM Y) RNG A mo (Q1 : postT X) (Q : postT Y),
  TS RNG A (aembed ATOP t) mo Q1 ->
  (forall x RNG' A' mo', acct_ok NMAX RNG' A' mo' -> Q1 x RNG' A' mo' -> TS RNG' A' (aembed ATOP (f x)) mo' Q) ->
  TS RNG A (aembed ATOP (sbind t f)) mo Q.
Proof.
  intros X Y t f. induction t as [x|e k IH]; intros RNG A mo Q1 Q H Hf.
  - rewrite aembed_sbind_ret. rewrite aembed_ret in H. destruct H as [HA HQ]. exact (Hf x RNG A mo HA HQ).
  - rewrite aembed_sbind_vis. rewrite aembed_vis in H.
    destruct e; cbn [aev_tree] in H |- *;
      try (unfold enode in H |- *; rewrite ebind_vis in H |- *; cbn [TS] in H |- *;
           destruct H as (HA & HS & HX & HK); split; [exact HA|]; split; [exact HS|]; split; [exact HX|];
           intros rsp mo' evs Hst; destruct (HK rsp mo' evs Hst) as (Ev & RNG' & A' & HF & HL & HT);
           split; [exact Ev|]; exists RNG', A'; split; [exact HF|]; split; [exact HL|];
           match goal with |- context [match ?d with Some _ => _ | None => _ end] => destruct d end;
           [rewrite ebind_ret_ok in HT |- *; eapply IH; [exact HT| exact Hf] | rewrite ebind_ret_unr in HT; destruct HT as [_ []]]).

    unfold ebind in H. cbn [bind TS] in H. destruct H as [_ []].
Qed.

End Core.

End CANSEC1.
Arguments TS NMAX {R} RNG A t mo Q.

Section CANSEC2. Context {rc : runConstT}.
Definition abud (A : alw) (k : Z) : Prop :=
  exists L : list word, List.NoDup L /\ Z.of_nat (length L) <= k /\ forall p, A p -> In p L.

Lemma abud_mono : forall A k k', abud A k -> k <= k' -> abud A k'.
Proof. intros A k k' (L & N & Hl & HL) Hk. exists L. split; [exact N|]. split; [lia| exact HL]. Qed.

Lemma abud_le : forall (A B : alw) k, abud B k -> alw_le A B -> abud A k.
Proof. intros A B k (L & N & Hl & HL) HAB. exists L. split; [exact N|]. split; [exact Hl|]. intros p Hp. apply HL, HAB, Hp. Qed.

Definition aunion (A : alw) (ps : list word) : alw := fun p => A p \/ In p ps.

Lemma aunion_le : forall A ps, alw_le A (aunion A ps).
Proof. intros A ps p H. left; exact H. Qed.
Lemma aunion_in : forall A ps p, In p ps -> aunion A ps p.
Proof. intros A ps p H. right; exact H. Qed.

Lemma nodup_extend : forall (L ps : list word), List.NoDup L ->
  exists L', List.NoDup L' /\ (length L' <= length L + length ps)%nat /\ (forall p, In p L \/ In p ps -> In p L').
Proof.
  intros L ps N. induction ps as [|q ps IH].
  - exists L. split; [exact N|]. split; [cbn; lia|]. intros p [H|[]]; exact H.
  - destruct IH as (L' & N' & Hlen & HL').
    destruct (in_dec (fun x y => bv_eq_dec _ x y) q L') as [Hin|Hnin].
    + exists L'. split; [exact N'|]. split; [cbn; lia|].
      intros p [H|[<-|H]]; [apply HL'; left; exact H| exact Hin| apply HL'; right; exact H].
    + exists (q :: L'). split; [constructor; [exact Hnin| exact N']|]. split; [cbn; lia|].
      intros p [H|[<-|H]]; [right; apply HL'; left; exact H| left; reflexivity| right; apply HL'; right; exact H].
Qed.

Lemma abud_union : forall A k ps, abud A k -> abud (aunion A ps) (k + Z.of_nat (length ps)).
Proof.
  intros A k ps (L & N & Hl & HL). destruct (nodup_extend L ps N) as (L' & N' & Hlen & HL').
  exists L'. split; [exact N'|]. split; [lia|]. intros p [H|H]; apply HL'; [left; apply HL; exact H| right; exact H].
Qed.

Fixpoint pages_from (p0 : Z) (n : nat) : list word :=
  match n with O => [] | S n' => Z_to_bv 64 p0 :: pages_from (p0 + 4096) n' end.

Lemma pages_from_length : forall p0 n, length (pages_from p0 n) = n.
Proof. intros p0 n. revert p0. induction n; intros; cbn; [reflexivity|]. rewrite IHn. reflexivity. Qed.

Lemma pages_from_in : forall p0 n (i : nat), (i < n)%nat -> In (Z_to_bv 64 (p0 + 4096 * Z.of_nat i)) (pages_from p0 n).
Proof.
  intros p0 n. revert p0. induction n as [|n IH]; intros p0 i Hi; [lia|]. cbn. destruct i as [|i].
  - left. f_equal. lia.
  - right. replace (p0 + 4096 * Z.of_nat (S i)) with (p0 + 4096 + 4096 * Z.of_nat i) by lia. apply IH. lia.
Qed.

Definition range_pages (lo len : Z) : list word :=
  pages_from (lo / 4096 * 4096) (Z.to_nat ((lo + len - 1) / 4096 - lo / 4096 + 1)).

Lemma range_pages_length : forall lo len, 0 <= lo -> 0 < len ->
  Z.of_nat (length (range_pages lo len)) <= len / 4096 + 2.
Proof.
  intros lo len Hlo Hlen. unfold range_pages. rewrite pages_from_length.
  pose proof (Z.div_mod lo 4096 ltac:(lia)). pose proof (Z.mod_pos_bound lo 4096 ltac:(lia)).
  pose proof (Z.div_mod (lo + len - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (lo + len - 1) 4096 ltac:(lia)).
  pose proof (Z.div_mod len 4096 ltac:(lia)). pose proof (Z.mod_pos_bound len 4096 ltac:(lia)). lia.
Qed.

Lemma range_pages_spec : forall lo len z, 0 <= lo -> lo <= z < lo + len ->
  In (page_base_of z) (range_pages lo len).
Proof.
  intros lo len z Hlo Hz. unfold range_pages, page_base_of, page_size.
  pose proof (Z.div_mod lo 4096 ltac:(lia)). pose proof (Z.mod_pos_bound lo 4096 ltac:(lia)).
  pose proof (Z.div_mod z 4096 ltac:(lia)). pose proof (Z.mod_pos_bound z 4096 ltac:(lia)).
  pose proof (Z.div_mod (lo + len - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (lo + len - 1) 4096 ltac:(lia)).
  assert (D1 : lo / 4096 <= z / 4096) by (apply Z.div_le_mono; lia).
  assert (D2 : z / 4096 <= (lo + len - 1) / 4096) by (apply Z.div_le_mono; lia).
  replace (z / 4096 * 4096) with (lo / 4096 * 4096 + 4096 * Z.of_nat (Z.to_nat (z / 4096 - lo / 4096))) by lia.
  apply pages_from_in. lia.
Qed.

Lemma rng_fp_ok_union : forall lz A lo len ps,
  0 <= lo -> lo + len <= 2^64 -> (forall z, lo <= z < lo + len -> In (page_base_of z) ps) ->
  rng (fp_ok lz (aunion A ps)) lo len.
Proof.
  intros lz A lo len ps Hlo Hhi H. apply rng_fp_ok; [exact Hlo| exact Hhi|]. intros z Hz. right. right. apply H. exact Hz.
Qed.

Lemma rng_fp_ok_range : forall lz A lo len, 0 <= lo -> lo + len <= 2^64 ->
  rng (fp_ok lz (aunion A (range_pages lo len))) lo len.
Proof. intros. apply rng_fp_ok_union; auto. intros z Hz. apply range_pages_spec; lia. Qed.

Lemma rng_fp_ok_allowed : forall lz (A : alw) lo len,
  0 <= lo -> lo + len <= 2^64 -> (forall z, lo <= z < lo + len -> A (page_base_of z)) -> rng (fp_ok lz A) lo len.
Proof. intros lz A lo len Hlo Hhi H. apply rng_fp_ok; auto. intros z Hz. right. apply H. exact Hz. Qed.
End CANSEC2.

Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ModelX OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.MmXfer OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.NodesA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Unset Lia Cache.

Section CANSEC1. Context {rc : runConstT}.
Section Core.
Variable NMAX : nat.

Definition postT (R : Type) : Type := R -> footprint -> alw -> Model -> Prop.

Fixpoint TS {R} (RNG : footprint) (A : alw) (t : itree node (exc R)) (mo : Model) (Q : postT R) {struct t} : Prop :=
  acct_ok NMAX RNG A mo /\
  match t with
  | Ret Unr => False
  | Ret (Ok r) => Q r RNG A mo
  | Vis n k => nsafeA NMAX n mo /\ (forall code mo', ~ nexitA n mo code mo') /\
      forall rsp mo' evs, nstepA n mo rsp mo' evs ->
        evs = [] /\ exists RNG' A', fstepS n rsp RNG RNG' /\ alw_le A A' /\ TS RNG' A' (k rsp) mo' Q
  end.

Lemma TS_acct : forall {R} RNG A (t : itree node (exc R)) mo Q, TS RNG A t mo Q -> acct_ok NMAX RNG A mo.
Proof. intros R RNG A [[|r]|n k] mo Q H; exact (proj1 H). Qed.

Lemma TS_mono : forall {R} (t : itree node (exc R)) RNG A mo (Q Q' : postT R),
  TS RNG A t mo Q -> (forall r RNG' A' mo', acct_ok NMAX RNG' A' mo' -> Q r RNG' A' mo' -> Q' r RNG' A' mo') -> TS RNG A t mo Q'.
Proof.
  intros R t. induction t as [[|r]|n k IH]; intros RNG A mo Q Q' H HQ; cbn in H |- *.
  - destruct H as [_ []].
  - destruct H as [HA HQ1]. split; [exact HA| apply HQ; assumption].
  - destruct H as (HA & HS & HX & HK). split; [exact HA|]. split; [exact HS|]. split; [exact HX|].
    intros rsp mo' evs Hst. destruct (HK rsp mo' evs Hst) as (E & RNG' & A' & HF & HL & HT).
    split; [exact E|]. exists RNG', A'. split; [exact HF|]. split; [exact HL|]. eapply IH; [exact HT| exact HQ].
Qed.

Lemma TS_ret_ok : forall {X} (x : X) RNG A mo (Q : postT X),
  acct_ok NMAX RNG A mo -> Q x RNG A mo -> TS RNG A (Ret (Ok x)) mo Q.
Proof. intros. cbn. split; assumption. Qed.

Lemma TS_event : forall {R} n (d : resp -> option Z) (f : Z -> itree node (exc R)) RNG A mo Q,
  acct_ok NMAX RNG A mo -> nsafeA NMAX n mo -> (forall code mo', ~ nexitA n mo code mo') ->
  (forall rsp mo' evs, nstepA n mo rsp mo' evs ->
     evs = [] /\ exists z RNG' A', d rsp = Some z /\ fstepS n rsp RNG RNG' /\ alw_le A A' /\ TS RNG' A' (f z) mo' Q) ->
  TS RNG A (ebind (enode n d) f) mo Q.
Proof.
  intros R n d f RNG A mo Q HA HS HX HK. unfold enode. rewrite ebind_vis. cbn [TS]. split; [exact HA|]. split; [exact HS|]. split; [exact HX|].
  intros rsp mo' evs Hst. destruct (HK rsp mo' evs Hst) as (E & z & RNG' & A' & Hd & HF & HL & HT).
  split; [exact E|]. exists RNG', A'. split; [exact HF|]. split; [exact HL|]. rewrite Hd. rewrite ebind_ret_ok. exact HT.
Qed.

Lemma TS_sbind : forall {X Y} (t : AM X) (f : X -> AM Y) RNG A mo (Q1 : postT X) (Q : postT Y),
  TS RNG A (aembed ATOP t) mo Q1 ->
  (forall x RNG' A' mo', acct_ok NMAX RNG' A' mo' -> Q1 x RNG' A' mo' -> TS RNG' A' (aembed ATOP (f x)) mo' Q) ->
  TS RNG A (aembed ATOP (sbind t f)) mo Q.
Proof.
  intros X Y t f. induction t as [x|e k IH]; intros RNG A mo Q1 Q H Hf.
  - rewrite aembed_sbind_ret. rewrite aembed_ret in H. destruct H as [HA HQ]. exact (Hf x RNG A mo HA HQ).
  - rewrite aembed_sbind_vis. rewrite aembed_vis in H.
    destruct e; cbn [aev_tree] in H |- *;
      try (unfold enode in H |- *; rewrite ebind_vis in H |- *; cbn [TS] in H |- *;
           destruct H as (HA & HS & HX & HK); split; [exact HA|]; split; [exact HS|]; split; [exact HX|];
           intros rsp mo' evs Hst; destruct (HK rsp mo' evs Hst) as (Ev & RNG' & A' & HF & HL & HT);
           split; [exact Ev|]; exists RNG', A'; split; [exact HF|]; split; [exact HL|];
           match goal with |- context [match ?d with Some _ => _ | None => _ end] => destruct d end;
           [rewrite ebind_ret_ok in HT |- *; eapply IH; [exact HT| exact Hf] | rewrite ebind_ret_unr in HT; destruct HT as [_ []]]).

    unfold ebind in H. cbn [bind TS] in H. destruct H as [_ []].
Qed.

End Core.

End CANSEC1.
Arguments TS NMAX {R} RNG A t mo Q.

Section CANSEC2. Context {rc : runConstT}.
Definition abud (A : alw) (k : Z) : Prop :=
  exists L : list word, List.NoDup L /\ Z.of_nat (length L) <= k /\ forall p, A p -> In p L.

Lemma abud_mono : forall A k k', abud A k -> k <= k' -> abud A k'.
Proof. intros A k k' (L & N & Hl & HL) Hk. exists L. split; [exact N|]. split; [lia| exact HL]. Qed.

Lemma abud_le : forall (A B : alw) k, abud B k -> alw_le A B -> abud A k.
Proof. intros A B k (L & N & Hl & HL) HAB. exists L. split; [exact N|]. split; [exact Hl|]. intros p Hp. apply HL, HAB, Hp. Qed.

Definition aunion (A : alw) (ps : list word) : alw := fun p => A p \/ In p ps.

Lemma aunion_le : forall A ps, alw_le A (aunion A ps).
Proof. intros A ps p H. left; exact H. Qed.
Lemma aunion_in : forall A ps p, In p ps -> aunion A ps p.
Proof. intros A ps p H. right; exact H. Qed.

Lemma nodup_extend : forall (L ps : list word), List.NoDup L ->
  exists L', List.NoDup L' /\ (length L' <= length L + length ps)%nat /\ (forall p, In p L \/ In p ps -> In p L').
Proof.
  intros L ps N. induction ps as [|q ps IH].
  - exists L. split; [exact N|]. split; [cbn; lia|]. intros p [H|[]]; exact H.
  - destruct IH as (L' & N' & Hlen & HL').
    destruct (in_dec (fun x y => bv_eq_dec _ x y) q L') as [Hin|Hnin].
    + exists L'. split; [exact N'|]. split; [cbn; lia|].
      intros p [H|[<-|H]]; [apply HL'; left; exact H| exact Hin| apply HL'; right; exact H].
    + exists (q :: L'). split; [constructor; [exact Hnin| exact N']|]. split; [cbn; lia|].
      intros p [H|[<-|H]]; [right; apply HL'; left; exact H| left; reflexivity| right; apply HL'; right; exact H].
Qed.

Lemma abud_union : forall A k ps, abud A k -> abud (aunion A ps) (k + Z.of_nat (length ps)).
Proof.
  intros A k ps (L & N & Hl & HL). destruct (nodup_extend L ps N) as (L' & N' & Hlen & HL').
  exists L'. split; [exact N'|]. split; [lia|]. intros p [H|H]; apply HL'; [left; apply HL; exact H| right; exact H].
Qed.

Fixpoint pages_from (p0 : Z) (n : nat) : list word :=
  match n with O => [] | S n' => Z_to_bv 64 p0 :: pages_from (p0 + 4096) n' end.

Lemma pages_from_length : forall p0 n, length (pages_from p0 n) = n.
Proof. intros p0 n. revert p0. induction n; intros; cbn; [reflexivity|]. rewrite IHn. reflexivity. Qed.

Lemma pages_from_in : forall p0 n (i : nat), (i < n)%nat -> In (Z_to_bv 64 (p0 + 4096 * Z.of_nat i)) (pages_from p0 n).
Proof.
  intros p0 n. revert p0. induction n as [|n IH]; intros p0 i Hi; [lia|]. cbn. destruct i as [|i].
  - left. f_equal. lia.
  - right. replace (p0 + 4096 * Z.of_nat (S i)) with (p0 + 4096 + 4096 * Z.of_nat i) by lia. apply IH. lia.
Qed.

Definition range_pages (lo len : Z) : list word :=
  pages_from (lo / 4096 * 4096) (Z.to_nat ((lo + len - 1) / 4096 - lo / 4096 + 1)).

Lemma range_pages_length : forall lo len, 0 <= lo -> 0 < len ->
  Z.of_nat (length (range_pages lo len)) <= len / 4096 + 2.
Proof.
  intros lo len Hlo Hlen. unfold range_pages. rewrite pages_from_length.
  pose proof (Z.div_mod lo 4096 ltac:(lia)). pose proof (Z.mod_pos_bound lo 4096 ltac:(lia)).
  pose proof (Z.div_mod (lo + len - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (lo + len - 1) 4096 ltac:(lia)).
  pose proof (Z.div_mod len 4096 ltac:(lia)). pose proof (Z.mod_pos_bound len 4096 ltac:(lia)). lia.
Qed.

Lemma range_pages_spec : forall lo len z, 0 <= lo -> lo <= z < lo + len ->
  In (page_base_of z) (range_pages lo len).
Proof.
  intros lo len z Hlo Hz. unfold range_pages, page_base_of, page_size.
  pose proof (Z.div_mod lo 4096 ltac:(lia)). pose proof (Z.mod_pos_bound lo 4096 ltac:(lia)).
  pose proof (Z.div_mod z 4096 ltac:(lia)). pose proof (Z.mod_pos_bound z 4096 ltac:(lia)).
  pose proof (Z.div_mod (lo + len - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (lo + len - 1) 4096 ltac:(lia)).
  assert (D1 : lo / 4096 <= z / 4096) by (apply Z.div_le_mono; lia).
  assert (D2 : z / 4096 <= (lo + len - 1) / 4096) by (apply Z.div_le_mono; lia).
  replace (z / 4096 * 4096) with (lo / 4096 * 4096 + 4096 * Z.of_nat (Z.to_nat (z / 4096 - lo / 4096))) by lia.
  apply pages_from_in. lia.
Qed.

Lemma rng_fp_ok_union : forall lz A lo len ps,
  0 <= lo -> lo + len <= 2^64 -> (forall z, lo <= z < lo + len -> In (page_base_of z) ps) ->
  rng (fp_ok lz (aunion A ps)) lo len.
Proof.
  intros lz A lo len ps Hlo Hhi H. apply rng_fp_ok; [exact Hlo| exact Hhi|]. intros z Hz. right. right. apply H. exact Hz.
Qed.

Lemma rng_fp_ok_range : forall lz A lo len, 0 <= lo -> lo + len <= 2^64 ->
  rng (fp_ok lz (aunion A (range_pages lo len))) lo len.
Proof. intros. apply rng_fp_ok_union; auto. intros z Hz. apply range_pages_spec; lia. Qed.

Lemma rng_fp_ok_allowed : forall lz (A : alw) lo len,
  0 <= lo -> lo + len <= 2^64 -> (forall z, lo <= z < lo + len -> A (page_base_of z)) -> rng (fp_ok lz A) lo len.
Proof. intros lz A lo len Hlo Hhi H. apply rng_fp_ok; auto. intros z Hz. right. apply H. exact Hz. Qed.
End CANSEC2.
End TwinB.
