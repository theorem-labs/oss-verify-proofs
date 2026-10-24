(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YP0m YP0e YP09 YP0l YP06 YP03 YP05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i YO0f YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN03 YL07 YL01 YL02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition afact_eqb (f g : afact) : bool :=
(af_lo f =? af_lo g) && (af_hi f =? af_hi g) && (af_al2 f =? af_al2 g).
Lemma afact_eqb_eq : forall f g, afact_eqb f g = true -> f = g.
Proof.
intros [a b c] [a' b' c'] H. unfold afact_eqb in H. cbn in H.
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.eqb_eq in H3. subst. reflexivity.
Qed.
Definition bc_eqb (c d : branch_cond) : bool :=
match c, d with
| BC_EQ, BC_EQ | BC_NE, BC_NE | BC_LT, BC_LT | BC_GE, BC_GE | BC_LTU, BC_LTU | BC_GEU, BC_GEU => true
| _, _ => false
end.
Lemma bc_eqb_eq : forall c d, bc_eqb c d = true -> c = d.
Proof. intros [] []; cbn; intros H; try reflexivity; discriminate. Qed.
Definition acond_eqb (c d : acond) : bool :=
bc_eqb (ac_c c) (ac_c d) && sv_eqb (ac_a c) (ac_a d) && sv_eqb (ac_b c) (ac_b d).
Lemma acond_eqb_eq : forall c d, acond_eqb c d = true -> c = d.
Proof.
intros [c a b] [c' a' b'] H. unfold acond_eqb in H. cbn in H.
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply bc_eqb_eq in H1. apply sv_eqb_eq in H2. apply sv_eqb_eq in H3. subst. reflexivity.
Qed.
Definition alias_eqb (p q : sv * sv) : bool := sv_eqb (fst p) (fst q) && sv_eqb (snd p) (snd q).
Lemma alias_eqb_eq : forall p q, alias_eqb p q = true -> p = q.
Proof.
intros [a b] [a' b'] H. unfold alias_eqb in H. cbn in H. apply andb_prop in H as [H1 H2].
apply sv_eqb_eq in H1. apply sv_eqb_eq in H2. subst. reflexivity.
Qed.
Lemma existsb_In {A} : forall (f : A -> bool) l, existsb f l = true -> exists x, In x l /\ f x = true.
Proof.
induction l as [|y l IH]; cbn; intros H; [discriminate|].
apply orb_prop in H as [H|H]; [exists y; auto|]. destruct (IH H) as (x & Hx & Hf). exists x. auto.
Qed.
Lemma atoms_ok_In : forall E l n f, atoms_ok E l -> In (n, f) l -> afact_ok E n f.
Proof.
induction l as [|[n' f'] l IH]; cbn; intros n f H Hin; [destruct Hin|].
destruct H as [H1 H2]. destruct Hin as [Heq|Hin]; [injection Heq as -> ->; exact H1 | apply IH; assumption].
Qed.
Lemma alias_ok_In : forall E l a b, alias_ok E l -> In (a, b) l -> sv_denot E a = sv_denot E b.
Proof.
induction l as [|[a' b'] l IH]; cbn; intros a b H Hin; [destruct Hin|].
destruct H as [H1 H2]. destruct Hin as [Heq|Hin]; [injection Heq as -> ->; exact H1 | apply IH; assumption].
Qed.
Lemma atoms_ok_intro : forall E l, (forall n f, In (n, f) l -> afact_ok E n f) -> atoms_ok E l.
Proof.
induction l as [|[n f] l IH]; cbn; intros H; [exact I|]. split; [apply H; left; reflexivity | apply IH; intros; apply H; right; assumption].
Qed.
Lemma conds_ok_intro : forall E l, (forall c, In c l -> acond_ok E c) -> conds_ok E l.
Proof.
induction l as [|c l IH]; cbn; intros H; [exact I|]. split; [apply H; left; reflexivity | apply IH; intros; apply H; right; assumption].
Qed.
Lemma alias_ok_intro : forall E l, (forall a b, In (a, b) l -> sv_denot E a = sv_denot E b) -> alias_ok E l.
Proof.
induction l as [|[a b] l IH]; cbn; intros H; [exact I|]. split; [apply H; left; reflexivity | apply IH; intros; apply H; right; assumption].
Qed.
Definition R (n : nat) : reg := Z_to_bv 5 (Z.of_nat n).
Section h.
Variable segs : list Segment.
Variable P : nat -> bool.
Definition PT (_ : nat) : bool := true.
Definition reg_reabs_ok (src tgt : sv) : bool :=
match tgt with
| SOff j 0 => if P j then sv_eqb src tgt else true
| _ => sv_eqb src tgt && sv_atoms_pd P PT tgt
end.
Definition all_regs : list reg := map R (seq 1 31).
Definition regs_reabs_ok (src tgt : list sv) : bool :=
forallb (fun r => reg_reabs_ok (sr_get src r) (sr_get tgt r)) all_regs.
Definition reabs_obl (tgt : list sv) : list (reg * nat) :=
flat_map (fun r => match sr_get tgt r with
| SOff j 0 => if P j then [] else [(r, j)]
| _ => []
end) all_regs.
Definition facts_reabs_ok (Gs Gt : facts) : bool :=
forallb (fun nf : nat * afact => if P (fst nf) then existsb (fun mg : nat * afact => Nat.eqb (fst mg) (fst nf) && afact_eqb (snd mg) (snd nf)) (f_atoms Gs) else true) (f_atoms Gt) &&
forallb (fun c => existsb (acond_eqb c) (f_conds Gs) && sv_atoms_pd P PT (ac_a c) && sv_atoms_pd P PT (ac_b c)) (f_conds Gt) &&
forallb (fun ab : sv * sv => existsb (alias_eqb ab) (f_alias Gs) && sv_atoms_pd P PT (fst ab) && sv_atoms_pd P PT (snd ab)) (f_alias Gt).
Definition fact_obls (Gt : facts) : list (nat * afact) := List.filter (fun nf => negb (P (fst nf))) (f_atoms Gt).
Definition reabs_check (ss : sstate) (regs' : list sv) (G' : facts) : bool :=
regs_reabs_ok (ss_regs ss) regs' && facts_reabs_ok (ss_facts ss) G' &&
match ss_resv ss with None => true | Some _ => false end.
Lemma all_regs_In : forall r : reg, r <> 0%bv -> In r all_regs.
Proof.
intros r Hr. unfold all_regs, R. apply in_map_iff. exists (Z.to_nat (bv_unsigned r)).
pose proof (bv_unsigned_in_range 5 r) as Hrg. change (bv_modulus 5) with 32 in Hrg.
split.
- apply bv_eq. rewrite Z_to_bv_unsigned. rewrite Z2Nat.id by lia. unfold bv_wrap. apply Z.mod_small. exact Hrg.
- apply in_seq. assert (bv_unsigned r <> 0). { intros H0. apply Hr. apply bv_eq. rewrite H0. reflexivity. } lia.
Qed.
Theorem st_ok_reabs : forall E E' ss ms regs' rs' G',
st_ok segs E ss ms ->
env_agree_pd P PT E E' ->
reabs_check ss regs' G' = true ->
Forall (fun rj : reg * nat => ew E' (snd rj) = getr (ms_regs ms) (fst rj)) (reabs_obl regs') ->
Forall (fun nf : nat * afact => afact_ok E' (fst nf) (snd nf)) (fact_obls G') ->
mem_ok segs E' (ms_mem ms) rs' ->
st_ok segs E' (mkSS (ss_pc ss) regs' rs' None G') ms.
Proof.
intros E E' ss ms regs' rs' G' HS HA Hck Hobl Hfo HM.
pose proof HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
unfold reabs_check in Hck. apply andb_prop in Hck as [Hck Hrv]. apply andb_prop in Hck as [Hregs Hfacts].
unfold st_ok. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split.
{ rewrite H4. destruct (ss_resv ss) as [a|]; [discriminate | reflexivity]. }
split; [exact H5|]. split; [exact H6|]. split; [| split; [exact HM|]].
-
intros r. destruct (decide (r = 0%bv)) as [->|Hr0].
{ rewrite (H7 0%bv). unfold sr_get. reflexivity. }
pose proof (proj1 (forallb_forall _ _) Hregs r (all_regs_In r Hr0)) as Hr. cbn beta in Hr.
unfold reg_reabs_ok in Hr.
destruct (sr_get regs' r) as [z|j k| | | | | | | | |] eqn:Ht;
try (apply andb_prop in Hr as [He Hp]; apply sv_eqb_eq in He; rewrite (H7 r), He;
symmetry; apply (sv_denot_agree_pd P PT E E'); [exact HA | exact Hp]).
destruct (Z.eq_dec k 0) as [->|Hk].
+ destruct (P j) eqn:HPj.
* apply sv_eqb_eq in Hr. rewrite (H7 r), Hr. cbn [sv_denot]. rewrite (proj1 HA j HPj). reflexivity.
*
assert (Hin : In (r, j) (reabs_obl regs')).
{ unfold reabs_obl. apply in_flat_map. exists r. split; [apply all_regs_In; exact Hr0|]. rewrite Ht, HPj. left. reflexivity. }
pose proof (proj1 (Forall_forall _ _) Hobl _ Hin) as Ho. cbn [fst snd] in Ho.
cbn [sv_denot]. rewrite Z.add_0_r, Ho. symmetry. apply Z_to_bv_bv_unsigned.
+ destruct k; [contradiction| |];
(apply andb_prop in Hr as [He Hp]; apply sv_eqb_eq in He; rewrite (H7 r), He;
symmetry; apply (sv_denot_agree_pd P PT E E'); [exact HA | exact Hp]).
-
unfold facts_reabs_ok in Hfacts. apply andb_prop in Hfacts as [Hfacts Hal]. apply andb_prop in Hfacts as [Hat Hco].
destruct H9 as (G1 & G2 & G3).
split; [| split].
+ apply atoms_ok_intro. intros n f Hin.
pose proof (proj1 (forallb_forall _ _) Hat (n, f) Hin) as Hn. cbn [fst snd] in Hn.
destruct (P n) eqn:HPn.
* apply existsb_In in Hn as ([m g] & Hmg & Hq). cbn [fst snd] in Hq. apply andb_prop in Hq as [Hmn Hfg].
apply Nat.eqb_eq in Hmn. apply afact_eqb_eq in Hfg. subst m g.
pose proof (atoms_ok_In E _ n f G1 Hmg) as Hf.
unfold afact_ok in *. rewrite (proj1 HA n HPn). exact Hf.
* assert (Hin' : In (n, f) (fact_obls G')) by (unfold fact_obls; apply (proj2 (List.filter_In _ _ _)); split; [exact Hin | cbn; rewrite HPn; reflexivity]).
exact (proj1 (Forall_forall _ _) Hfo _ Hin').
+ apply conds_ok_intro. intros c Hin.
pose proof (proj1 (forallb_forall _ _) Hco c Hin) as Hc. apply andb_prop in Hc as [Hc Hpb]. apply andb_prop in Hc as [Hc Hpa].
apply existsb_In in Hc as (d & Hd & Hcd). apply acond_eqb_eq in Hcd. subst d.
pose proof (conds_ok_In E _ c G2 Hd) as Hok. unfold acond_ok in *.
rewrite !(sv_denot_agree_pd P PT E E') by assumption. exact Hok.
+ apply alias_ok_intro. intros a b Hin.
pose proof (proj1 (forallb_forall _ _) Hal (a, b) Hin) as Hab. cbn [fst snd] in Hab.
apply andb_prop in Hab as [Hab Hpb]. apply andb_prop in Hab as [Hab Hpa].
apply existsb_In in Hab as ([a' b'] & Hin' & Heq). apply alias_eqb_eq in Heq. injection Heq as <- <-.
rewrite !(sv_denot_agree_pd P PT E E') by assumption. exact (alias_ok_In E _ a b G3 Hin').
Qed.
End h.
Lemma env_agree_pd_ewset : forall E kg v,
env_agree_pd (fun n => negb (Nat.eqb n kg)) (PT) E (ewset E kg v).
Proof.
intros E kg v. split; [| intros; reflexivity].
intros n Hn. apply ew_ewset_other. intros ->. rewrite Nat.eqb_refl in Hn. discriminate.
Qed.
Section i.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.
Hypothesis AX : AllocExtra B MR.
Let segs := ms_segs B.
Theorem st_ok_statics_pd : forall E ss ms L A md kg i_got i_libc i_guard rs',
st_ok segs E ss ms -> MR L A (ms_mem ms) md ->
ss_atoms_pd (fun n => negb (Nat.eqb n kg)) PT ss = true ->
add_statics B (ss_mem ss) i_got i_libc i_guard kg = Some rs' ->
exists g, 0 <= g < 2 ^ 64 /\
st_ok segs (ewset E kg (Z_to_bv 64 g)) (mkSS (ss_pc ss) (ss_regs ss) rs' (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms L A md kg i_got i_libc i_guard rs' HS HMR Hat Hadd.
destruct (ax_statics AX L A (ms_mem ms) md HMR) as (Hgot & (g & Hg & Hguard) & Hnl).
exists g. split; [exact Hg|].
pose proof (st_ok_agree_pd segs _ _ E (ewset E kg (Z_to_bv 64 g)) ss ms HS (env_agree_pd_ewset E kg _) Hat) as HS'.
destruct HS' as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & HM & H9).
unfold st_ok; cbn. repeat (split; [assumption|]). split; [| exact H9].
unfold add_statics in Hadd.
destruct (add_chunk_at (ss_mem ss) i_got _) as [rs1|] eqn:E1; [|discriminate].
destruct (add_chunk_at rs1 i_libc _) as [rs2|] eqn:E2; [|discriminate].
eapply (add_chunk_at_ok B); [| exact Hadd |].
- eapply (add_chunk_at_ok B); [| exact E2 |].
+ eapply (add_chunk_at_ok B); [exact HM | exact E1 |]. apply word_mem_chunk_ok. exact Hgot.
+ apply byte_chunk_ok; [lia | exact Hnl].
- eapply atom_chunk_ok; [exact Hg | apply ew_ewset_same | exact Hguard].
Qed.
End i.
End e.
