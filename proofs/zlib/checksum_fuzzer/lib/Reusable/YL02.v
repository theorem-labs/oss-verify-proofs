(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition not_in (l : list nat) (d : nat) : bool := negb (existsb (Nat.eqb d) l).
Definition obase_p (p : nat -> bool) (b : option nat) : bool := match b with Some n => p n | None => true end.
Definition env_agree_pd (p q : nat -> bool) (E E' : env) : Prop :=
(forall n, p n = true -> ew E' n = ew E n) /\ (forall d, q d = true -> ed E' d = ed E d).
Fixpoint sv_atoms_pd (p q : nat -> bool) (v : sv) : bool :=
match v with
| SLit _ => true
| SOff n _ => p n
| SAlu _ a b | SAluw _ a b | SMd _ a b | SMdw _ a b => sv_atoms_pd p q a && sv_atoms_pd p q b
| SExt _ _ a => sv_atoms_pd p q a
| SData d _ _ => q d
| SF1 _ a => sv_atoms_pd p q a
| SF2 _ a b => sv_atoms_pd p q a && sv_atoms_pd p q b
| SF3 _ a b c => sv_atoms_pd p q a && sv_atoms_pd p q b && sv_atoms_pd p q c
end.
Lemma sv_denot_agree_pd : forall p q E E' v,
env_agree_pd p q E E' -> sv_atoms_pd p q v = true -> sv_denot E' v = sv_denot E v.
Proof.
intros p q E E' v [HA HD]. induction v; cbn; intros H; try reflexivity;
repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H; destruct H end.
- rewrite HA by exact H. reflexivity.
- rewrite IHv1, IHv2 by assumption. reflexivity.
- rewrite IHv1, IHv2 by assumption. reflexivity.
- rewrite IHv1, IHv2 by assumption. reflexivity.
- rewrite IHv1, IHv2 by assumption. reflexivity.
- rewrite IHv by assumption. reflexivity.
- unfold data_word. rewrite HD by exact H. reflexivity.
- rewrite IHv by assumption. reflexivity.
- rewrite IHv1, IHv2 by assumption. reflexivity.
- rewrite IHv1, IHv2, IHv3 by assumption. reflexivity.
Qed.
Definition regs_atoms_pd (p q : nat -> bool) (sr : list sv) : bool := forallb (sv_atoms_pd p q) sr.
Lemma regs_ok_agree_pd : forall p q E E' sr regs,
env_agree_pd p q E E' -> regs_atoms_pd p q sr = true -> regs_ok E sr regs -> regs_ok E' sr regs.
Proof.
intros p q E E' sr regs HA Hsr Hr r. rewrite (Hr r). symmetry. apply (sv_denot_agree_pd p q E E'); [exact HA|].
unfold sr_get. destruct (bv_eqb r 0); [reflexivity|].
destruct (nth_in_or_default (ridx r) sr (SLit 0)) as [Hin| ->]; [|reflexivity].
exact (proj1 (forallb_forall _ _) Hsr _ Hin).
Qed.
Definition cval_atoms_pd (p q : nat -> bool) (cv : cval) : bool :=
match cv with CVal _ v => sv_atoms_pd p q v | CData d _ _ => q d | _ => true end.
Definition region_atoms_pd (p q : nat -> bool) (r : region) : bool :=
obase_p p (r_base r) && forallb (fun c => cval_atoms_pd p q (c_val c)) (r_chunks r).
Definition mem_atoms_pd (p q : nat -> bool) (rs : smem) : bool := forallb (region_atoms_pd p q) rs.
Lemma base_val_agree_pd : forall p q E E' b,
env_agree_pd p q E E' -> obase_p p b = true -> base_val E' b = base_val E b.
Proof. intros p q E E' [x|] [HA _] H; cbn in *; [rewrite HA by exact H|]; reflexivity. Qed.
Definition cond_atoms_pd (p q : nat -> bool) (c : acond) : bool :=
sv_atoms_pd p q (ac_a c) && sv_atoms_pd p q (ac_b c).
Definition facts_atoms_pd (p q : nat -> bool) (G : facts) : bool :=
forallb (fun nf => p (fst nf)) (f_atoms G) && forallb (cond_atoms_pd p q) (f_conds G)
&& forallb (fun a => sv_atoms_pd p q (fst a) && sv_atoms_pd p q (snd a)) (f_alias G).
Lemma facts_ok_agree_pd : forall p q E E' G,
env_agree_pd p q E E' -> facts_atoms_pd p q G = true -> facts_ok E G -> facts_ok E' G.
Proof.
intros p q E E' G HA H (Hat & Hco & Hal). unfold facts_atoms_pd in H.
apply andb_prop in H as [H HL]. apply andb_prop in H as [Ha Hc].
split; [|split].
- clear Hco Hc Hal HL. induction (f_atoms G) as [|[n f] l IH]; cbn in *; [exact I|].
apply andb_prop in Ha as [Hn Hl]. destruct Hat as [Hf Hl']. split; [|apply IH; assumption].
unfold afact_ok in *. rewrite (proj1 HA) by exact Hn. exact Hf.
- clear Hat Ha Hal HL. induction (f_conds G) as [|c l IH]; cbn in *; [exact I|].
apply andb_prop in Hc as [Hc1 Hl]. destruct Hco as [Hc0 Hl']. split; [|apply IH; assumption].
unfold acond_ok, cond_atoms_pd in *. apply andb_prop in Hc1 as [H1 H2].
rewrite !(sv_denot_agree_pd p q E E') by assumption. exact Hc0.
- clear Hat Ha Hco Hc. induction (f_alias G) as [|[a b] l IH]; cbn in *; [exact I|].
apply andb_prop in HL as [Hab HL']. apply andb_prop in Hab as [H1 H2]. destruct Hal as [Heq Hal'].
split; [|apply IH; assumption].
rewrite !(sv_denot_agree_pd p q E E') by assumption. exact Heq.
Qed.
Definition ss_atoms_pd (p q : nat -> bool) (ss : sstate) : bool :=
regs_atoms_pd p q (ss_regs ss) && mem_atoms_pd p q (ss_mem ss) && facts_atoms_pd p q (ss_facts ss)
&& match ss_resv ss with Some a => sv_atoms_pd p q a | None => true end.
Section g.
Variable segs : list Segment.
Lemma cbyte_agree_pd : forall p q E E' a cv i,
env_agree_pd p q E E' -> cval_atoms_pd p q cv = true -> cbyte segs E' a cv i = cbyte segs E a cv i.
Proof.
intros p q E E' a cv i HA H. destruct cv; cbn in *; try reflexivity.
- rewrite (sv_denot_agree_pd p q E E') by assumption. reflexivity.
- destruct HA as [_ HD]. rewrite HD by exact H. reflexivity.
Qed.
Lemma region_ok_agree_pd : forall p q E E' m r,
env_agree_pd p q E E' -> region_atoms_pd p q r = true ->
region_ok segs E m r -> region_ok segs E' m r.
Proof.
intros p q E E' m r HA H (H1 & H2 & H3 & H4).
unfold region_atoms_pd in H. apply andb_prop in H as [Hb Hc].
unfold region_ok. rewrite (base_val_agree_pd p q E E') by assumption.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
rewrite Forall_forall in H4 |- *. intros c Hin i Hi.
destruct (H4 c Hin i Hi) as (b & Hb1 & Hb2). exists b. split; [|exact Hb2].
rewrite (cbyte_agree_pd p q E E'); [exact Hb1| exact HA|].
apply (proj1 (forallb_forall _ _) Hc). exact Hin.
Qed.
Lemma pairwise_disjoint_agree_pd : forall p q E E' rs,
env_agree_pd p q E E' -> mem_atoms_pd p q rs = true ->
pairwise_disjoint E rs -> pairwise_disjoint E' rs.
Proof.
intros p q E E' rs HA. induction rs as [|r rs IH]; cbn; intros H Hp; [exact I|].
apply andb_prop in H as [Hr Hrs]. destruct Hp as [Ha Hp]. split; [|apply IH; assumption].
unfold region_atoms_pd in Hr. apply andb_prop in Hr as [Hb _].
clear IH Hp. induction rs as [|r' rs IH']; cbn in *; [exact I|].
apply andb_prop in Hrs as [Hr' Hrs]. destruct Ha as [Hd Ha].
unfold region_atoms_pd in Hr'. apply andb_prop in Hr' as [Hb' _].
split; [| apply IH'; assumption].
unfold extent_disjoint in *. rewrite !(base_val_agree_pd p q E E') by assumption. exact Hd.
Qed.
Lemma mem_ok_agree_pd : forall p q E E' m rs,
env_agree_pd p q E E' -> mem_atoms_pd p q rs = true -> mem_ok segs E m rs -> mem_ok segs E' m rs.
Proof.
intros p q E E' m rs HA H (Hwf & Hok & Hpd). split; [exact Hwf|]. split.
- rewrite Forall_forall in Hok |- *. intros r Hin. eapply region_ok_agree_pd; eauto.
apply (proj1 (forallb_forall _ _) H). exact Hin.
- eapply pairwise_disjoint_agree_pd; eauto.
Qed.
Lemma st_ok_agree_pd : forall p q E E' ss ms,
st_ok segs E ss ms -> env_agree_pd p q E E' -> ss_atoms_pd p q ss = true -> st_ok segs E' ss ms.
Proof.
intros p q E E' ss ms (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HA Hat.
unfold ss_atoms_pd in Hat.
apply andb_prop in Hat as [Hat Hrv]. apply andb_prop in Hat as [Hat HG]. apply andb_prop in Hat as [Hr Hm].
unfold st_ok. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split.
{ rewrite H4. destruct (ss_resv ss) as [a|]; cbn; [|reflexivity].
rewrite (sv_denot_agree_pd p q E E') by assumption. reflexivity. }
split; [exact H5|]. split; [exact H6|]. split; [eapply regs_ok_agree_pd; eauto|].
split; [eapply mem_ok_agree_pd; eauto| eapply facts_ok_agree_pd; eauto].
Qed.
Lemma st_ok_edset : forall E d bs ss ms,
st_ok segs E ss ms -> ss_atoms_pd (fun _ => true) (not_in [d]) ss = true ->
st_ok segs (edset E d bs) ss ms.
Proof.
intros E d bs ss ms HS Hat. eapply (st_ok_agree_pd (fun _ => true) (not_in [d])); eauto.
split; [intros; reflexivity|]. intros d' Hd'. unfold not_in in Hd'. cbn in Hd'.
unfold edset; cbn [ed]. destruct (Nat.eqb d' d); [discriminate| reflexivity].
Qed.
Lemma st_ok_redata : forall q E (ed' : nat -> list byte) ss ms,
st_ok segs E ss ms -> (forall d, q d = true -> ed' d = ed E d) ->
ss_atoms_pd (fun _ => true) q ss = true ->
st_ok segs (mkEnv (ew E) ed') ss ms.
Proof.
intros q E ed' ss ms HS Hd Hat. eapply (st_ok_agree_pd (fun _ => true) q); eauto.
split; [intros; reflexivity|]. exact Hd.
Qed.
Lemma st_ok_resume_pd : forall p q E E' ss regs pc (mem' : word -> option byte) rv RET rs G,
regs_ok E (ss_regs ss) regs ->
pc = Z_to_bv 64 (ss_pc ss) ->
env_agree_pd p q E E' -> regs_atoms_pd p q (ss_regs ss) = true ->
sv_denot E' rv = RET ->
mem_ok segs E' mem' rs ->
facts_ok E' G ->
st_ok segs E' (resume ss rv rs G) (mkst (regupd regs 10 RET) (v_addi pc 4) mem' (seg_rom segs)).
Proof.
intros p q E E' ss regs pc mem' rv RET rs G Hregs Hpc HA Hat Hrv Hmem HG.
unfold st_ok, resume, mkst; cbn.
split; [reflexivity|]. split.
{ rewrite Hpc. unfold v_addi. rewrite Z_to_bv_unsigned. apply Z_to_bv64_eq_mod.
unfold bv_wrap. change (bv_modulus 64) with (2^64). apply Zplus_mod_idemp_l. }
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split.
- change (regupd regs 10 RET) with (if bv_eqb (10:reg) 0 then regs else regupd regs 10 RET).
apply regs_ok_set; [|exact Hrv]. eapply regs_ok_agree_pd; eauto.
- exact (conj Hmem HG).
Qed.
End g.
End e.
