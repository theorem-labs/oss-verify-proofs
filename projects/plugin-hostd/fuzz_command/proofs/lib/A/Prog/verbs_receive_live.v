(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the live bytes at a state of the verbs_receive walk (verbs_receive_iface.v).
   No recorder callee's post bounds blocks_bytes, so a walk state's live bytes are read off its block list: the blocks
   are the recorder's own (rec_repA: at most 6 per recorded call, 6 in the spill slot, the answer and the reply, each
   at most LMAX + 2 bytes), the walk's own temporary blocks, and the entry's other blocks (`rest`). vr_live_le states
   that bound from vr_core's Permutation; YCbq.v blocks_bytes_bsum turns it into blocks_bytes. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdRep verbs_receive_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Lemma vr_bsum_perm : forall l l', Permutation l l' -> bsum l = bsum l'.
Proof.
intros l l' H. induction H; rewrite ?bsum_cons; try lia.
Qed.

Lemma vr_bsum_nonneg : forall l, Forall (fun b => 0 <= snd b) l -> 0 <= bsum l.
Proof. intros l H. induction H as [|b l Hb _ IH]; [cbn; lia|]. rewrite bsum_cons. lia. Qed.

(* NoDup here is the Stdlib's (stdpp's, with elem_of, is in scope through the semantics' imports) *)
Lemma vr_nodup_app_l : forall (l1 l2 : list (Z * Z)), List.NoDup (l1 ++ l2) -> List.NoDup l1.
Proof.
induction l1 as [|a l1 IH]; intros l2 H; [constructor|]. cbn in H. apply List.NoDup_cons_iff in H as [Hn H].
constructor; [intros Hin; apply Hn; apply in_or_app; left; exact Hin | exact (IH _ H)].
Qed.

Lemma vr_bsum_incl : forall l l', List.NoDup l -> incl l l' -> Forall (fun b => 0 <= snd b) l' -> bsum l <= bsum l'.
Proof.
induction l as [|a l IH]; intros l' Hnd Hinc Hpos.
- change (bsum []) with 0. exact (vr_bsum_nonneg _ Hpos).
- apply List.NoDup_cons_iff in Hnd as [Hna Hnd'].
  assert (Ha : In a l') by (apply Hinc; left; reflexivity).
  apply in_split in Ha as (l1 & l2 & ->).
  assert (Hp : Permutation (l1 ++ a :: l2) (a :: l1 ++ l2)) by (apply Permutation_sym, Permutation_middle).
  rewrite (vr_bsum_perm _ _ Hp). rewrite !bsum_cons.
  assert (Hpos' : Forall (fun b => 0 <= snd b) (l1 ++ l2)).
  { apply Forall_forall. intros x Hx. rewrite Forall_forall in Hpos. apply Hpos.
    apply in_app_or in Hx as [Hx|Hx]; apply in_or_app; [left; exact Hx | right; right; exact Hx]. }
  enough (bsum l <= bsum (l1 ++ l2)) by lia.
  apply (IH _ Hnd'); [|exact Hpos'].
  intros x Hx. assert (Hx' : In x (l1 ++ a :: l2)) by (apply Hinc; right; exact Hx).
  apply in_app_or in Hx' as [Hx'|[<-|Hx']]; [apply in_or_app; left; exact Hx' | exfalso; exact (Hna Hx) |
    apply in_or_app; right; exact Hx'].
Qed.

Lemma vr_bsum_bound : forall l c, Forall (fun b => snd b <= c) l -> bsum l <= Z.of_nat (length l) * c.
Proof.
intros l c H. induction H as [|b l Hb _ IH]; cbn [length]; [cbn; lia|]. rewrite bsum_cons. lia.
Qed.

Lemma vr_concat_bound : forall (Ps : list (list (Z * Z))) c,
  Forall (fun P => (length P <= 6)%nat /\ Forall (fun b => snd b <= c) P) Ps ->
  (length (concat Ps) <= 6 * length Ps)%nat /\ Forall (fun b => snd b <= c) (concat Ps).
Proof.
intros Ps c H. induction H as [|P Ps [HP1 HP2] _ [IH1 IH2]]; cbn [concat length]; [split; [lia | constructor]|].
rewrite length_app. split; [lia|]. apply Forall_app. split; assumption.
Qed.

(* the recorder's own blocks: at most 6 per recorded call, 6 in the spill slot, the answer and the reply, each at
   most LMAX + 2 bytes (CmdRep.v acall_at, aanswer_at, areply_at) *)
Lemma vr_lay_bound : forall bl rd gr sc R Q, arep_at bl rd gr sc R Q ->
  (length (lay_blocks Q) <= 6 * length (r_calls R) + 8)%nat /\ Forall (fun b => snd b <= LMAX + 2) (lay_blocks Q).
Proof.
intros bl rd gr sc R Q (_ & _ & _ & HC & HA & HR & _).
destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
assert (HPs : Forall (fun P => (length P <= 6)%nat /\ Forall (fun b => snd b <= LMAX + 2) P) (l_calls Q)).
{ apply Forall_forall. intros P HP. apply In_nth_error in HP as (i & Hi).
  assert (Hi' : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite Hi; discriminate).
  destruct (nth_error (r_calls R) i) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
  destruct (C4 i c P Ec Hi) as ((A1 & A2 & A3 & _ & _ & _ & A7) & _).
  split; [lia|]. apply Forall_forall. intros pn Hpn. apply In_nth_error in Hpn as (k & Hk).
  assert (Hk' : (k < length (snd c))%nat) by (rewrite <- A3; apply nth_error_Some; rewrite Hk; discriminate).
  destruct (nth_error (snd c) k) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
  destruct (A7 k s pn Es Hk) as (_ & _ & _ & B4 & _). lia. }
destruct (vr_concat_bound _ _ HPs) as [L1 F1].
destruct C5 as (S1 & S2 & S3 & _ & _ & _ & S7).
assert (FS : Forall (fun b => snd b <= LMAX + 2) (l_spill Q)).
{ apply Forall_forall. intros pn Hpn. apply In_nth_error in Hpn as (k & Hk).
  assert (Hk' : (k < length (snd (r_spill R)))%nat) by (rewrite <- S3; apply nth_error_Some; rewrite Hk; discriminate).
  destruct (nth_error (snd (r_spill R)) k) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
  destruct (S7 k s pn Es Hk) as (_ & _ & _ & B4 & _). lia. }
assert (FA : Forall (fun b => snd b <= LMAX + 2) (oblk (l_answer Q)) /\ (length (oblk (l_answer Q)) <= 1)%nat).
{ unfold aanswer_at in HA. destruct (r_answer R), (l_answer Q) as [pn|]; cbn; try contradiction;
  [destruct HA as (_ & _ & _ & H4 & _); split; [constructor; [lia | constructor] | lia] | split; [constructor | lia]]. }
assert (FR : Forall (fun b => snd b <= LMAX + 2) (oblk (l_reply Q)) /\ (length (oblk (l_reply Q)) <= 1)%nat).
{ unfold areply_at in HR. destruct (r_reply R), (l_reply Q) as [pn|]; cbn; try contradiction;
  [destruct HR as (_ & _ & _ & _ & _ & H6 & _); split; [constructor; [lia | constructor] | lia] | split; [constructor | lia]]. }
unfold lay_blocks. rewrite !length_app. split.
- rewrite C2 in L1. destruct FA as [_ LA]. destruct FR as [_ LR]. lia.
- repeat (apply Forall_app; split); first [exact F1 | exact FS | exact (proj1 FA) | exact (proj1 FR)].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section f.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.

Lemma vr_ablocks_pos : forall ly S W mem md, AR segs B ly S W mem md -> Forall (fun b => 0 <= snd b) (ablocks B ly S).
Proof.
intros ly S W mem md HAR. apply Forall_forall. intros [p n] Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn). cbn. lia.
Qed.

Lemma vr_ablocks_nodup : forall ly S W mem md, AR segs B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR. pose proof (vr_ablocks_pos ly S W mem md HAR) as Hpos.
assert (Hpw : pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S))).
{ destruct (ablocks B ly S) as [|[p0 n0] l0] eqn:El; [cbn; exact I|].
  assert (Hin : In (p0, n0) (ablocks B ly S)) by (rewrite El; left; reflexivity).
  pose proof (al_blocks _ _ LAWS _ _ _ _ _ p0 n0 HAR Hin) as (_ & _ & _ & _ & _ & Hpw & _).
  rewrite El in Hpw. exact Hpw. }
apply (List.NoDup_map_inv (fun b => (fst b, req_size (snd b)))).
revert Hpos Hpw. generalize (ablocks B ly S). intros l.
induction l as [|b l IH]; intros Hpos Hpw; cbn in *; [constructor|].
destruct Hpw as [Hf Hp]. apply Forall_cons_iff in Hpos as [Hb Hpos'].
constructor; [|exact (IH Hpos' Hp)].
intros Hin. rewrite Forall_forall in Hf. pose proof (Hf _ Hin) as Hd.
pose proof (req_size_pos (snd b) Hb) as [H1 _]. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* the live bytes at a walk state: the recorder's blocks, the walk's own, and the entry's others *)
Theorem vr_live_le : forall ly S W mem md lyc Sc Wc memc mdc rd Rc O Oc tmps rest,
  AR segs B ly S W mem md -> AR segs B lyc Sc Wc memc mdc ->
  Permutation (ablocks B ly S) (O ++ rest) ->
  Permutation (ablocks B lyc Sc) (Oc ++ tmps ++ rest) ->
  rec_repA B lyc Sc rd Rc Oc ->
  blocks_bytes Sc <= blocks_bytes S + (6 * Z.of_nat (length (r_calls Rc)) + 8) * (LMAX + 2) + bsum tmps.
Proof.
intros ly S W mem md lyc Sc Wc memc mdc rd Rc O Oc tmps rest HAR HARc HP HPc (Q & HQ & HOQ).
rewrite (blocks_bytes_bsum B ly S), (blocks_bytes_bsum B lyc Sc).
rewrite (vr_bsum_perm _ _ HP), (vr_bsum_perm _ _ HPc), !bsum_app.
pose proof (vr_ablocks_pos ly S W mem md HAR) as Hpos. pose proof (vr_ablocks_pos lyc Sc Wc memc mdc HARc) as Hposc.
pose proof (vr_ablocks_nodup lyc Sc Wc memc mdc HARc) as Hndc.
assert (HposO : Forall (fun b => 0 <= snd b) O).
{ apply Forall_forall. intros x Hx. rewrite Forall_forall in Hpos. apply Hpos.
  apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hx. }
assert (HndO : List.NoDup Oc).
{ apply (Permutation_NoDup HPc) in Hndc. exact (vr_nodup_app_l _ _ Hndc). }
assert (HposL : Forall (fun b => 0 <= snd b) (lay_blocks Q)).
{ apply Forall_forall. intros x Hx. rewrite Forall_forall in Hposc. apply Hposc.
  exact (lay_blocks_in_bl _ rd _ _ Rc Q x HQ Hx). }
destruct (vr_lay_bound _ _ _ _ _ _ HQ) as [HL HF].
assert (H1 : bsum Oc <= bsum (lay_blocks Q)).
{ apply (vr_bsum_incl _ _ HndO); [intros x Hx; apply HOQ; exact Hx | exact HposL]. }
pose proof (vr_bsum_bound _ _ HF) as H2. pose proof (vr_bsum_nonneg _ HposO) as H3.
assert (H4 : Z.of_nat (length (lay_blocks Q)) * (LMAX + 2) <= (6 * Z.of_nat (length (r_calls Rc)) + 8) * (LMAX + 2)).
{ apply Z.mul_le_mono_nonneg_r; [unfold LMAX; lia | lia]. }
lia.
Qed.
End f.
End d.
