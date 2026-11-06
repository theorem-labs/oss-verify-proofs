(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0b YQ0i YQ0h YQ09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition env_agree_on (P : nat -> bool) (E E' : env) : Prop :=
forall n, P n = true -> ew E' n = ew E n.


Fixpoint sv_atoms_in (P : nat -> bool) (v : sv) : bool :=
match v with
| SLit _ => true
| SOff n _ => P n
| SAlu _ a b | SAluw _ a b | SMd _ a b | SMdw _ a b => sv_atoms_in P a && sv_atoms_in P b
| SExt _ _ a => sv_atoms_in P a
| SData _ _ _ => false
| SF1 _ a => sv_atoms_in P a
| SF2 _ a b => sv_atoms_in P a && sv_atoms_in P b
| SF3 _ a b c => sv_atoms_in P a && sv_atoms_in P b && sv_atoms_in P c
end.
Lemma sv_denot_agree_on : forall P E E' v,
env_agree_on P E E' -> sv_atoms_in P v = true -> sv_denot E' v = sv_denot E v.
Proof.
intros P E E' v HA. induction v; cbn; intros H; try img_refl; try discriminate H;
repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H; destruct H end.
- rewrite HA by img_exact H. img_refl.
- rewrite IHv1, IHv2 by assumption. img_refl.
- rewrite IHv1, IHv2 by assumption. img_refl.
- rewrite IHv1, IHv2 by assumption. img_refl.
- rewrite IHv1, IHv2 by assumption. img_refl.
- rewrite IHv by assumption. img_refl.
- rewrite IHv by assumption. img_refl.
- rewrite IHv1, IHv2 by assumption. img_refl.
- rewrite IHv1, IHv2, IHv3 by assumption. img_refl.
Qed.
Definition regs_atoms_in (P : nat -> bool) (sr : list sv) : bool := forallb (sv_atoms_in P) sr.
Lemma sr_get_atoms_in : forall P sr r, regs_atoms_in P sr = true -> sv_atoms_in P (sr_get sr r) = true.
Proof.
intros P sr r H. unfold sr_get. destruct (bv_eqb r 0); [img_refl|].
unfold regs_atoms_in in H.
destruct (nth_in_or_default (ridx r) sr (SLit 0)) as [Hin| ->]; [|img_refl].
img_apply (proj1 (forallb_forall _ _) H). img_exact Hin.
Qed.
Lemma regs_ok_agree_on : forall P E E' sr regs,
env_agree_on P E E' -> regs_atoms_in P sr = true -> regs_ok E sr regs -> regs_ok E' sr regs.
Proof.
intros P E E' sr regs HA Hsr Hr r. rewrite (sv_denot_agree_on P E E') by (img_try (auto using sr_get_atoms_in)). img_apply Hr.
Qed.
Definition cval_atoms_in (P : nat -> bool) (cv : cval) : bool :=
match cv with CVal _ v => sv_atoms_in P v | _ => false end.
Definition obase_in (P : nat -> bool) (b : option nat) : bool :=
match b with Some n => P n | None => true end.
Definition region_atoms_in (P : nat -> bool) (r : region) : bool :=
obase_in P (r_base r) && forallb (fun c => cval_atoms_in P (c_val c)) (r_chunks r).
Definition mem_atoms_in (P : nat -> bool) (rs : smem) : bool := forallb (region_atoms_in P) rs.
Lemma base_val_agree_on : forall P E E' b,
env_agree_on P E E' -> obase_in P b = true -> base_val E' b = base_val E b.
Proof.
intros P E E' [x|] HA H; cbn in *; [|img_refl]. rewrite HA by img_exact H. img_refl.
Qed.
Lemma cbyte_agree_on : forall segs P E E' a cv i,
env_agree_on P E E' -> cval_atoms_in P cv = true -> cbyte segs E' a cv i = cbyte segs E a cv i.
Proof.
intros segs P E E' a cv i HA H. destruct cv; cbn in *; try img_refl; try discriminate H.
rewrite (sv_denot_agree_on P E E') by assumption. img_refl.
Qed.
Lemma region_ok_agree_on : forall segs P E E' m r,
env_agree_on P E E' -> region_atoms_in P r = true ->
region_ok segs E m r -> region_ok segs E' m r.
Proof.
intros segs P E E' m r HA H (H1 & H2 & H3 & H4).
unfold region_atoms_in in H. apply andb_prop in H as [Hb Hc].
unfold region_ok. rewrite (base_val_agree_on P E E') by assumption.
split; [img_try (img_exact H1)|]. split; [img_try (img_exact H2)|]. split; [img_try (img_exact H3)|].
rewrite Forall_forall in H4 |- *. intros c Hin i Hi.
destruct (H4 c Hin i Hi) as (b & Hb1 & Hb2). exists b. split; [|img_try (img_exact Hb2)].
rewrite (cbyte_agree_on segs P E E'); [img_try (img_exact Hb1)| img_try (img_exact HA)|].
img_apply (proj1 (forallb_forall _ _) Hc). img_exact Hin.
Qed.
Lemma extent_disjoint_agree_on : forall P E E' r1 r2,
env_agree_on P E E' -> obase_in P (r_base r1) = true -> obase_in P (r_base r2) = true ->
extent_disjoint E r1 r2 -> extent_disjoint E' r1 r2.
Proof.
intros P E E' r1 r2 HA H1 H2 H. unfold extent_disjoint in *.
rewrite !(base_val_agree_on P E E') by assumption. img_exact H.
Qed.
Lemma pairwise_disjoint_agree_on : forall P E E' rs,
env_agree_on P E E' -> mem_atoms_in P rs = true ->
pairwise_disjoint E rs -> pairwise_disjoint E' rs.
Proof.
intros P E E' rs HA. induction rs as [|r rs IH]; cbn; intros H Hp; [img_try (img_exact I)|].
apply andb_prop in H as [Hr Hrs]. destruct Hp as [Ha Hp]. split; [|img_try (img_apply IH; assumption)].
unfold region_atoms_in in Hr. apply andb_prop in Hr as [Hb _].
clear IH Hp. induction rs as [|r' rs IH']; cbn in *; [img_try (img_exact I)|].
apply andb_prop in Hrs as [Hr' Hrs]. destruct Ha as [Hd Ha].
unfold region_atoms_in in Hr'. apply andb_prop in Hr' as [Hb' _].
split; [img_try (eapply extent_disjoint_agree_on; eauto) | img_try (img_apply IH'; assumption)].
Qed.
Lemma mem_ok_agree_on : forall segs P E E' m rs,
env_agree_on P E E' -> mem_atoms_in P rs = true -> mem_ok segs E m rs -> mem_ok segs E' m rs.
Proof.
intros segs P E E' m rs HA H (Hwf & Hok & Hpd). split; [img_try (img_exact Hwf)|]. split.
- rewrite Forall_forall in Hok |- *. intros r Hin. eapply region_ok_agree_on; eauto.
img_apply (proj1 (forallb_forall _ _) H). img_exact Hin.
- eapply pairwise_disjoint_agree_on; eauto.
Qed.
Definition cond_atoms_in (P : nat -> bool) (c : acond) : bool := sv_atoms_in P (ac_a c) && sv_atoms_in P (ac_b c).
Definition facts_atoms_in (P : nat -> bool) (G : facts) : bool :=
forallb (fun p => P (fst p)) (f_atoms G) && forallb (cond_atoms_in P) (f_conds G)
&& forallb (fun p => sv_atoms_in P (fst p) && sv_atoms_in P (snd p)) (f_alias G).
Lemma facts_ok_agree_on : forall P E E' G,
env_agree_on P E E' -> facts_atoms_in P G = true -> facts_ok E G -> facts_ok E' G.
Proof.
intros P E E' G HA H (Hat & Hco & Hal). unfold facts_atoms_in in H.
apply andb_prop in H as [H HL]. apply andb_prop in H as [Ha Hc].
split; [|img_try (split)].
- clear Hco Hc Hal HL. induction (f_atoms G) as [|[n f] l IH]; cbn in *; [img_try (img_exact I)|].
apply andb_prop in Ha as [Hn Hl]. destruct Hat as [Hf Hl'].
split; [|img_try (img_apply IH; assumption)].
unfold afact_ok in *. rewrite HA by img_exact Hn. img_exact Hf.
- clear Hat Ha Hal HL. induction (f_conds G) as [|c l IH]; cbn in *; [img_try (img_exact I)|].
apply andb_prop in Hc as [Hc1 Hl]. destruct Hco as [Hc0 Hl'].
split; [|img_try (img_apply IH; assumption)].
unfold acond_ok, cond_atoms_in in *. apply andb_prop in Hc1 as [H1 H2].
rewrite !(sv_denot_agree_on P E E') by assumption. img_exact Hc0.
- clear Hat Ha Hco Hc. induction (f_alias G) as [|[a b] l IH]; cbn in *; [img_try (img_exact I)|].
apply andb_prop in HL as [Hab HL']. apply andb_prop in Hab as [H1 H2]. destruct Hal as [Heq Hal'].
split; [|img_try (img_apply IH; assumption)].
rewrite !(sv_denot_agree_on P E E') by assumption. img_exact Heq.
Qed.
Definition ss_atoms_in (P : nat -> bool) (ss : sstate) : bool :=
regs_atoms_in P (ss_regs ss) && mem_atoms_in P (ss_mem ss) && facts_atoms_in P (ss_facts ss)
&& match ss_resv ss with Some a => sv_atoms_in P a | None => true end.
Section d.
Variable segs : list Segment.
Context {fx : FPState}.
Lemma st_ok_agree_on : forall P E E' ss ms,
st_ok segs E ss ms -> env_agree_on P E E' -> ss_atoms_in P ss = true -> st_ok segs E' ss ms.
Proof.
intros P E E' ss ms (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HA Hat.
unfold ss_atoms_in in Hat.
apply andb_prop in Hat as [Hat Hrv]. apply andb_prop in Hat as [Hat HG]. apply andb_prop in Hat as [Hr Hm].
unfold st_ok. split; [img_try (img_exact H1)|]. split; [img_try (img_exact H2)|]. split; [img_try (img_exact H3)|]. split.
{ rewrite H4. destruct (ss_resv ss) as [a|]; cbn; [|img_refl].
rewrite (sv_denot_agree_on P E E') by assumption. img_refl. }
split; [img_try (img_exact H5)|]. split; [img_try (img_exact H6)|]. split.
{ eapply regs_ok_agree_on; eauto. }
split.
{ eapply mem_ok_agree_on; eauto. }
eapply facts_ok_agree_on; eauto.
Qed.
End d.
Definition env_merge (P : nat -> bool) (E1 E2 : env) : env :=
mkEnv (fun n => if P n then ew E1 n else ew E2 n) (ed E2).
Lemma env_merge_on : forall P E1 E2, env_agree_on P E1 (env_merge P E1 E2).
Proof. intros P E1 E2 n Hn. unfold env_merge. cbn [ew]. rewrite Hn. img_refl. Qed.
Lemma ew_merge_in : forall P E1 E2 n, P n = true -> ew (env_merge P E1 E2) n = ew E1 n.
Proof. intros P E1 E2 n Hn. unfold env_merge. cbn [ew]. rewrite Hn. img_refl. Qed.
Lemma ew_merge_out : forall P E1 E2 n, P n = false -> ew (env_merge P E1 E2) n = ew E2 n.
Proof. intros P E1 E2 n Hn. unfold env_merge. cbn [ew]. rewrite Hn. img_refl. Qed.
Lemma ed_merge : forall P E1 E2, ed (env_merge P E1 E2) = ed E2.
Proof. img_refl. Qed.
Definition natin (l : list nat) (n : nat) : bool := existsb (Nat.eqb n) l.

Definition conds_atoms_in (P : nat -> bool) (G : facts) : bool :=
forallb (cond_atoms_in P) (f_conds G) && forallb (fun p => sv_atoms_in P (fst p) && sv_atoms_in P (snd p)) (f_alias G).
Lemma atoms_ok_agree : forall k E E' l,
env_agree k E E' -> forallb (fun p => Nat.ltb (fst p) k) l = true -> atoms_ok E l -> atoms_ok E' l.
Proof.
intros k E E' l HA. induction l as [|[n f] l IH]; cbn; intros H Hat; [img_try (img_exact I)|].
apply andb_prop in H as [Hn Hl]. destruct Hat as [Hf Hl']. split; [|img_try (img_apply IH; assumption)].
unfold afact_ok in *. apply Nat.ltb_lt in Hn. rewrite (proj1 HA) by img_exact Hn. img_exact Hf.
Qed.
Lemma conds_alias_ok_agree_on : forall P E E' G,
env_agree_on P E E' -> conds_atoms_in P G = true -> facts_ok E G ->
conds_ok E' (f_conds G) /\ alias_ok E' (f_alias G).
Proof.
intros P E E' G HA H (_ & Hco & Hal). unfold conds_atoms_in in H. apply andb_prop in H as [Hc HL]. split.
- clear Hal HL. induction (f_conds G) as [|c l IH]; cbn in *; [img_try (img_exact I)|].
apply andb_prop in Hc as [Hc1 Hl]. destruct Hco as [Hc0 Hl'].
split; [|img_try (img_apply IH; assumption)].
unfold acond_ok, cond_atoms_in in *. apply andb_prop in Hc1 as [H1 H2].
rewrite !(sv_denot_agree_on P E E') by assumption. img_exact Hc0.
- clear Hco Hc. induction (f_alias G) as [|[a b] l IH]; cbn in *; [img_try (img_exact I)|].
apply andb_prop in HL as [Hab HL']. apply andb_prop in Hab as [H1 H2]. destruct Hal as [Heq Hal'].
split; [|img_try (img_apply IH; assumption)].
rewrite !(sv_denot_agree_on P E E') by assumption. img_exact Heq.
Qed.
Section e.
Variable segs : list Segment.
Context {fx : FPState}.
Lemma st_ok_agree_on2 : forall P E E' ss ms,
st_ok segs E ss ms -> env_agree_on P E E' ->
regs_atoms_in P (ss_regs ss) = true -> mem_atoms_in P (ss_mem ss) = true -> conds_atoms_in P (ss_facts ss) = true ->
ss_resv ss = None -> atoms_ok E' (f_atoms (ss_facts ss)) ->
st_ok segs E' ss ms.
Proof.
intros P E E' ss ms HS HA Hr Hm Hc Hrv Hat. pose proof HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
unfold st_ok. split; [img_try (img_exact H1)|]. split; [img_try (img_exact H2)|]. split; [img_try (img_exact H3)|]. split.
{ rewrite H4, Hrv. img_refl. }
split; [img_try (img_exact H5)|]. split; [img_try (img_exact H6)|]. split.
{ eapply regs_ok_agree_on; eauto. }
split.
{ eapply mem_ok_agree_on; eauto. }
split; [img_try (img_exact Hat)|]. img_exact (conds_alias_ok_agree_on P E E' _ HA Hc H9).
Qed.
End e.
