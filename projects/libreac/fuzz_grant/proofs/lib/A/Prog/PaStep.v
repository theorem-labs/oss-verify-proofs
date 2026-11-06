(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YP07.v for libreac/fuzz_grant's program walk, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section d.
Variable P : nat -> bool.
Definition env_agree_p (E E' : env) : Prop := (forall n, P n = true -> ew E' n = ew E n) /\ ed E' = ed E.
Fixpoint sv_atoms_p (v : sv) : bool :=
match v with
| SLit _ => true
| SOff n _ => P n
| SAlu _ a b | SAluw _ a b | SMd _ a b | SMdw _ a b => sv_atoms_p a && sv_atoms_p b
| SExt _ _ a => sv_atoms_p a
| SData _ _ _ => true
| SF1 _ a => sv_atoms_p a
| SF2 _ a b => sv_atoms_p a && sv_atoms_p b
| SF3 _ a b c => sv_atoms_p a && sv_atoms_p b && sv_atoms_p c
end.
Lemma sv_denot_agree_p : forall E E' v, env_agree_p E E' -> sv_atoms_p v = true -> sv_denot E' v = sv_denot E v.
Proof.
intros E E' v [HA HD]. induction v; cbn; intros H; try reflexivity;
repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H; destruct H end.
- rewrite HA by exact H. reflexivity.
- rewrite IHv1, IHv2 by assumption. reflexivity.
- rewrite IHv1, IHv2 by assumption. reflexivity.
- rewrite IHv1, IHv2 by assumption. reflexivity.
- rewrite IHv1, IHv2 by assumption. reflexivity.
- rewrite IHv by assumption. reflexivity.
- unfold data_word. rewrite HD. reflexivity.
- rewrite IHv by assumption. reflexivity.
- rewrite IHv1, IHv2 by assumption. reflexivity.
- rewrite IHv1, IHv2, IHv3 by assumption. reflexivity.
Qed.
Definition regs_atoms_p (sr : list sv) : bool := forallb sv_atoms_p sr.
Lemma sr_get_atoms_p : forall sr r, regs_atoms_p sr = true -> sv_atoms_p (sr_get sr r) = true.
Proof.
intros sr r H. unfold sr_get. destruct (bv_eqb r 0); [reflexivity|].
unfold regs_atoms_p in H.
destruct (nth_in_or_default (ridx r) sr (SLit 0)) as [Hin| ->]; [|reflexivity].
apply (proj1 (forallb_forall _ _) H). exact Hin.
Qed.
Lemma regs_ok_agree_p : forall E E' sr regs, env_agree_p E E' -> regs_atoms_p sr = true -> regs_ok E sr regs -> regs_ok E' sr regs.
Proof. intros E E' sr regs HA Hsr Hr r. rewrite (sv_denot_agree_p E E') by (auto using sr_get_atoms_p). apply Hr. Qed.
Definition cval_atoms_p (cv : cval) : bool := match cv with CVal _ v => sv_atoms_p v | _ => true end.
Definition obase_p (b : option nat) : bool := match b with Some n => P n | None => true end.
Definition region_atoms_p (r : region) : bool := obase_p (r_base r) && forallb (fun c => cval_atoms_p (c_val c)) (r_chunks r).
Definition mem_atoms_p (rs : smem) : bool := forallb region_atoms_p rs.
Lemma base_val_agree_p : forall E E' b, env_agree_p E E' -> obase_p b = true -> base_val E' b = base_val E b.
Proof. intros E E' [x|] [HA _] H; cbn in *; [|reflexivity]. rewrite HA by exact H. reflexivity. Qed.
Lemma cbyte_agree_p : forall segs E E' a cv i, env_agree_p E E' -> cval_atoms_p cv = true -> cbyte segs E' a cv i = cbyte segs E a cv i.
Proof.
intros segs E E' a cv i HA H. destruct cv; cbn in *; try reflexivity.
- rewrite (sv_denot_agree_p E E') by assumption. reflexivity.
- destruct HA as [_ HD]. rewrite HD. reflexivity.
Qed.
Lemma region_ok_agree_p : forall segs E E' m r, env_agree_p E E' -> region_atoms_p r = true -> region_ok segs E m r -> region_ok segs E' m r.
Proof.
intros segs E E' m r HA H (H1 & H2 & H3 & H4).
unfold region_atoms_p in H. apply andb_prop in H as [Hb Hc].
unfold region_ok. rewrite (base_val_agree_p E E') by assumption.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
rewrite Forall_forall in H4 |- *. intros c Hin i Hi.
destruct (H4 c Hin i Hi) as (b & Hb1 & Hb2). exists b. split; [|exact Hb2].
rewrite (cbyte_agree_p segs E E'); [exact Hb1| exact HA|].
apply (proj1 (forallb_forall _ _) Hc). exact Hin.
Qed.
Lemma extent_disjoint_agree_p : forall E E' r1 r2, env_agree_p E E' -> obase_p (r_base r1) = true -> obase_p (r_base r2) = true ->
extent_disjoint E r1 r2 -> extent_disjoint E' r1 r2.
Proof. intros E E' r1 r2 HA H1 H2 H. unfold extent_disjoint in *. rewrite !(base_val_agree_p E E') by assumption. exact H. Qed.
Lemma pairwise_disjoint_agree_p : forall E E' rs, env_agree_p E E' -> mem_atoms_p rs = true -> pairwise_disjoint E rs -> pairwise_disjoint E' rs.
Proof.
intros E E' rs HA. induction rs as [|r rs IH]; cbn; intros H Hp; [exact I|].
apply andb_prop in H as [Hr Hrs]. destruct Hp as [Ha Hp]. split; [|apply IH; assumption].
unfold region_atoms_p in Hr. apply andb_prop in Hr as [Hb _].
clear IH Hp. induction rs as [|r' rs IH']; cbn in *; [exact I|].
apply andb_prop in Hrs as [Hr' Hrs]. destruct Ha as [Hd Ha].
unfold region_atoms_p in Hr'. apply andb_prop in Hr' as [Hb' _].
split; [eapply extent_disjoint_agree_p; eauto | apply IH'; assumption].
Qed.
Lemma mem_ok_agree_p : forall segs E E' m rs, env_agree_p E E' -> mem_atoms_p rs = true -> mem_ok segs E m rs -> mem_ok segs E' m rs.
Proof.
intros segs E E' m rs HA H (Hwf & Hok & Hpd). split; [exact Hwf|]. split.
- rewrite Forall_forall in Hok |- *. intros r Hin. eapply region_ok_agree_p; eauto.
apply (proj1 (forallb_forall _ _) H). exact Hin.
- eapply pairwise_disjoint_agree_p; eauto.
Qed.
Definition cond_atoms_p (c : acond) : bool := sv_atoms_p (ac_a c) && sv_atoms_p (ac_b c).
Definition facts_atoms_p (G : facts) : bool :=
forallb (fun p => P (fst p)) (f_atoms G) && forallb cond_atoms_p (f_conds G)
&& forallb (fun p => sv_atoms_p (fst p) && sv_atoms_p (snd p)) (f_alias G).
Lemma facts_ok_agree_p : forall E E' G, env_agree_p E E' -> facts_atoms_p G = true -> facts_ok E G -> facts_ok E' G.
Proof.
intros E E' G HA H (Hat & Hco & Hal). unfold facts_atoms_p in H.
apply andb_prop in H as [H HL]. apply andb_prop in H as [Ha Hc].
split; [|split].
- clear Hco Hc Hal HL. induction (f_atoms G) as [|[n f] l IH]; cbn in *; [exact I|].
apply andb_prop in Ha as [Hn Hl]. destruct Hat as [Hf Hl'].
split; [|apply IH; assumption].
unfold afact_ok in *. rewrite (proj1 HA) by exact Hn. exact Hf.
- clear Hat Ha Hal HL. induction (f_conds G) as [|c l IH]; cbn in *; [exact I|].
apply andb_prop in Hc as [Hc1 Hl]. destruct Hco as [Hc0 Hl'].
split; [|apply IH; assumption].
unfold acond_ok, cond_atoms_p in *. apply andb_prop in Hc1 as [H1 H2].
rewrite !(sv_denot_agree_p E E') by assumption. exact Hc0.
- clear Hat Ha Hco Hc. induction (f_alias G) as [|[a b] l IH]; cbn in *; [exact I|].
apply andb_prop in HL as [Hab HL']. apply andb_prop in Hab as [H1 H2]. destruct Hal as [Heq Hal'].
split; [|apply IH; assumption].
rewrite !(sv_denot_agree_p E E') by assumption. exact Heq.
Qed.
Definition ss_atoms_p (ss : sstate) : bool :=
regs_atoms_p (ss_regs ss) && mem_atoms_p (ss_mem ss) && facts_atoms_p (ss_facts ss)
&& match ss_resv ss with Some a => sv_atoms_p a | None => true end
&& match ss_fregs ss with [] => true | _ => false end.
Section e.
Variable segs : list Segment.
Context {fx : FPState}.
Lemma st_ok_agree_p : forall E E' ss ms, st_ok segs E ss ms -> env_agree_p E E' -> ss_atoms_p ss = true -> st_ok segs E' ss ms.
Proof.
intros E E' ss ms (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HA Hat.
unfold ss_atoms_p in Hat. apply andb_prop in Hat as [Hat Hfr]. apply andb_prop in Hat as [Hat Hrv]. apply andb_prop in Hat as [Hat HG]. apply andb_prop in Hat as [Hsr Hrs].
unfold st_ok. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split.
{ rewrite H4. destruct (ss_resv ss) as [a|]; cbn; [|reflexivity]. rewrite (sv_denot_agree_p E E') by assumption. reflexivity. }
split; [exact H5|]. split; [exact H6|]. split; [eapply regs_ok_agree_p; eauto|].
split; [eapply mem_ok_agree_p; eauto | eapply facts_ok_agree_p; eauto].
Qed.
Lemma st_ok_set_regs_mem_p : forall E E' ss regs regs' pc pc' mem mem' rs' upd,
st_ok segs E ss (mkst regs pc mem (seg_rom segs)) ->
env_agree_p E E' -> ss_atoms_p ss = true ->
reg_nodup (map fst upd) = true ->
(forall r, reg_in r (map fst upd) = false -> getr regs' r = getr regs r) ->
Forall (fun p => bv_eqb (fst p) 0 = false /\ getr regs' (fst p) = sv_denot E' (snd p)) upd ->
mem_ok segs E' mem' rs' ->
st_ok segs E' (mkSS pc' (sr_sets (ss_regs ss) upd) rs' None (ss_facts ss))
(mkst regs' (Z_to_bv 64 pc') mem' (seg_rom segs)).
Proof.
intros E E' ss regs regs' pc pc' mem mem' rs' upd HS HA Hat Hnd Hsame Hupd HM.
pose proof (st_ok_agree_p E E' ss _ HS HA Hat) as HS'.
destruct HS' as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
unfold st_ok; cbn. repeat (split; [reflexivity|]). split.
- eapply regs_ok_sets; eauto using reg_nodup_sound.
- split; assumption.
Qed.
End e.
End d.
Definition pband (k K : nat) (n : nat) : bool := (n <? k)%nat || (K <=? n)%nat.
Lemma env_agree_p_havoc : forall k K E ws, (k + length ws <= K)%nat -> env_agree_p (pband k K) E (havoc E k ws).
Proof.
intros k K E ws Hk. split; [|reflexivity]. intros n Hn. unfold pband in Hn. apply Bool.orb_prop in Hn as [Hn|Hn].
- apply Nat.ltb_lt in Hn. apply ew_havoc_old. exact Hn.
- apply Nat.leb_le in Hn. unfold havoc. cbn [ew]. destruct (n <? k)%nat eqn:H; [reflexivity|]. rewrite nth_overflow by lia. reflexivity.
Qed.
Section g.
Variable segs : list Segment.
Context {fx : FPState}.
Lemma st_ok_splice_havoc_p : forall k K E ss regs regs' pc pc' mem mem' rs' upd rl,
st_ok segs E ss (mkst regs pc mem (seg_rom segs)) ->
(k + length rl <= K)%nat ->
ss_atoms_p (pband k K) ss = true ->
reg_nodup (map fst upd ++ rl) = true ->
forallb (fun r : reg => negb (bv_eqb r 0)) rl = true ->
forallb (fun p => sv_atoms_p (pband k K) (snd p)) upd = true ->
mem_atoms_p (pband k K) rs' = true ->
(forall r, reg_in r (map fst upd ++ rl) = false -> getr regs' r = getr regs r) ->
Forall (fun p => bv_eqb (fst p) 0 = false /\ getr regs' (fst p) = sv_denot E (snd p)) upd ->
mem_ok segs E mem' rs' ->
st_ok segs (havoc E k (map (getr regs') rl))
(mkSS pc' (sr_sets (ss_regs ss) (upd ++ junk_upd k rl)) rs' None (ss_facts ss))
(mkst regs' (Z_to_bv 64 pc') mem' (seg_rom segs)).
Proof.
intros k K E ss regs regs' pc pc' mem mem' rs' upd rl HS HkK Hat Hnd Hnz Hupd_at Hrs_at Hsame Hupd HM.
set (E' := havoc E k (map (getr regs') rl)).
assert (HA : env_agree_p (pband k K) E E') by (apply env_agree_p_havoc; rewrite length_map; exact HkK).
eapply (st_ok_set_regs_mem_p (pband k K) segs E E' ss regs regs' pc pc' mem mem' rs' (upd ++ junk_upd k rl) HS HA Hat).
- rewrite map_app, junk_upd_fst. exact Hnd.
- rewrite map_app, junk_upd_fst. exact Hsame.
- apply Forall_app. split.
+ rewrite Forall_forall in Hupd |- *. intros p Hp. specialize (Hupd p Hp). destruct Hupd as [H1 H2].
split; [exact H1|]. rewrite H2. symmetry. apply (sv_denot_agree_p (pband k K) E E'); [exact HA|].
apply (proj1 (forallb_forall _ _) Hupd_at p Hp).
+ subst E'. apply junk_upd_ok0. exact Hnz.
- eapply mem_ok_agree_p; eauto.
Qed.
End g.
