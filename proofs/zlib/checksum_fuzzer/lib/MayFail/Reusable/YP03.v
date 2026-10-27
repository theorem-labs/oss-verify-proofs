(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YP03.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Definition ewset (E : env) (n : nat) (v : word) : env :=
mkEnv (fun i => if Nat.eqb i n then v else ew E i) (ed E).
Definition edset (E : env) (d : nat) (bs : list byte) : env :=
mkEnv (ew E) (fun i => if Nat.eqb i d then bs else ed E i).
Lemma ew_ewset_same : forall E n v, ew (ewset E n v) n = v.
Proof. intros. cbn. rewrite Nat.eqb_refl. reflexivity. Qed.
Lemma ew_ewset_other : forall E n v i, i <> n -> ew (ewset E n v) i = ew E i.
Proof. intros E n v i H. cbn. destruct (Nat.eqb_spec i n); [lia|reflexivity]. Qed.
Lemma ed_ewset : forall E n v, ed (ewset E n v) = ed E.
Proof. reflexivity. Qed.
Lemma env_agree_ewset : forall E n v, env_agree n E (ewset E n v).
Proof.
intros E n v. split; [|reflexivity]. intros i Hi. apply ew_ewset_other. lia.
Qed.
Lemma env_agree_le : forall k k' E E', (k <= k')%nat -> env_agree k' E E' -> env_agree k E E'.
Proof. intros k k' E E' Hle [H1 H2]. split; [|exact H2]. intros n Hn. apply H1. lia. Qed.
Lemma env_agree_trans : forall k E1 E2 E3,
env_agree k E1 E2 -> env_agree k E2 E3 -> env_agree k E1 E3.
Proof.
intros k E1 E2 E3 [A1 D1] [A2 D2]. split; [|congruence].
intros n Hn. rewrite A2, A1 by exact Hn. reflexivity.
Qed.
Lemma env_agree_ewset2 : forall E n v w,
env_agree n E (ewset (ewset E n v) (S n) w).
Proof.
intros. eapply env_agree_trans; [apply env_agree_ewset|].
eapply env_agree_le; [|apply env_agree_ewset]. lia.
Qed.
Section e.
Variable segs : list Segment.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.
Context {fx : FPState}.
Lemma st_ok_agree : forall k E E' ss ms,
st_ok segs E ss ms -> env_agree k E E' -> ss_atoms_lt k ss = true ->
st_ok segs E' ss ms.
Proof.
intros k E E' ss ms (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HA Hat.
unfold ss_atoms_lt in Hat.
apply andb_prop in Hat as [Hat Hrv]. apply andb_prop in Hat as [Hat HG].
apply andb_prop in Hat as [Hr Hm].
unfold st_ok. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split.
{ rewrite H4. destruct (ss_resv ss) as [a|]; cbn; [|reflexivity].
rewrite (sv_denot_agree k E E') by assumption. reflexivity. }
split; [exact H5|]. split; [exact H6|]. split.
{ eapply regs_ok_agree; eauto. }
split.
{ eapply mem_ok_agree; eauto. }
eapply facts_ok_agree; eauto.
Qed.
Definition sym_runN (n : N) (ss : sstate) : sstate * run_status :=
sym_run segs tbl (N.to_nat n) ss.
Definition sym_run_toN (n : N) (stop : Z) (ss : sstate) : sstate * run_status :=
sym_run_to segs tbl (N.to_nat n) stop ss.
Lemma rz_run_gen : forall n E ss ss' st ms model T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_runN n ss = (ss', st) ->
(forall ms',
match st with RS_ecall => st_ok_ecall segs E ss' ms' | _ => st_ok segs E ss' ms' end ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
realizes segs (mkCfg ms' model) T) ->
realizes segs (mkCfg ms model) T.
Proof.
intros n E ss ss' st ms model T Hh Hlz HS Hrun Hk.
destruct (sym_run_sound segs tbl tbl_ok _ E ss ss' st ms HS Hrun) as (ms' & Hms & HS' & _ & Hfr).
apply (rz_msteps segs ms ms' model T Hh Hlz Hms). apply Hk; assumption.
Qed.
Lemma rz_run_stop : forall n E ss ss' why ms model T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_runN n ss = (ss', RS_stopped why) ->
(forall ms', st_ok segs E ss' ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
realizes segs (mkCfg ms' model) T) ->
realizes segs (mkCfg ms model) T.
Proof. intros n E ss ss' why. exact (rz_run_gen n E ss ss' (RS_stopped why)). Qed.
Lemma rz_run_running : forall n E ss ss' ms model T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_runN n ss = (ss', RS_running) ->
(forall ms', st_ok segs E ss' ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
realizes segs (mkCfg ms' model) T) ->
realizes segs (mkCfg ms model) T.
Proof. intros n E ss ss'. exact (rz_run_gen n E ss ss' RS_running). Qed.
Lemma rz_run_ecall : forall n E ss ss' ms model T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_runN n ss = (ss', RS_ecall) ->
(forall ms', st_ok_ecall segs E ss' ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
realizes segs (mkCfg ms' model) T) ->
realizes segs (mkCfg ms model) T.
Proof. intros n E ss ss'. exact (rz_run_gen n E ss ss' RS_ecall). Qed.
Lemma rz_run_to_gen : forall n stop E ss ss' st ms model T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_run_toN n stop ss = (ss', st) ->
(forall ms',
match st with RS_ecall => st_ok_ecall segs E ss' ms' | _ => st_ok segs E ss' ms' end ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
realizes segs (mkCfg ms' model) T) ->
realizes segs (mkCfg ms model) T.
Proof.
intros n stop E ss ss' st ms model T Hh Hlz HS Hrun Hk.
destruct (sym_run_to_sound segs tbl tbl_ok _ stop E ss ss' st ms HS Hrun) as (ms' & Hms & HS' & _ & Hfr).
apply (rz_msteps segs ms ms' model T Hh Hlz Hms). apply Hk; assumption.
Qed.
Lemma msteps_run_gen : forall n E ss ss' st ms,
st_ok segs E ss ms ->
sym_runN n ss = (ss', st) ->
exists ms', msteps segs ms ms'
/\ match st with RS_ecall => st_ok_ecall segs E ss' ms' | _ => st_ok segs E ss' ms' end
/\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof.
intros n E ss ss' st ms HS Hrun.
destruct (sym_run_sound segs tbl tbl_ok _ E ss ss' st ms HS Hrun) as (ms' & Hms & HS' & _ & Hfr).
exists ms'. auto.
Qed.
Lemma msteps_run_to_gen : forall n stop E ss ss' st ms,
st_ok segs E ss ms ->
sym_run_toN n stop ss = (ss', st) ->
exists ms', msteps segs ms ms'
/\ match st with RS_ecall => st_ok_ecall segs E ss' ms' | _ => st_ok segs E ss' ms' end
/\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof.
intros n stop E ss ss' st ms HS Hrun.
destruct (sym_run_to_sound segs tbl tbl_ok _ stop E ss ss' st ms HS Hrun) as (ms' & Hms & HS' & _ & Hfr).
exists ms'. auto.
Qed.
Lemma rz_branch : forall E ss ms model T c a b,
st_ok segs E ss ms ->
(branch_taken c (sv_denot E a) (sv_denot E b) = true ->
st_ok segs E (add_cond ss (mkAC c a b)) ms ->
realizes segs (mkCfg ms model) T) ->
(branch_taken c (sv_denot E a) (sv_denot E b) = false ->
st_ok segs E (add_cond ss (mkAC (neg_bc c) a b)) ms ->
realizes segs (mkCfg ms model) T) ->
realizes segs (mkCfg ms model) T.
Proof.
intros E ss ms model T c a b HS Ht Hf.
destruct (branch_taken c (sv_denot E a) (sv_denot E b)) eqn:Hb.
- apply Ht; [reflexivity|]. apply st_ok_add_cond; assumption.
- apply Hf; [reflexivity|]. apply st_ok_add_cond_neg; assumption.
Qed.
Lemma st_ok_assume : forall E ss ms c a b,
st_ok segs E ss ms ->
branch_taken c (sv_denot E a) (sv_denot E b) = true ->
st_ok segs E (add_cond ss (mkAC c a b)) ms.
Proof. intros. apply st_ok_add_cond; assumption. Qed.
Lemma st_ok_facts_ok : forall E ss ms, st_ok segs E ss ms -> facts_ok E (ss_facts ss).
Proof. intros E ss ms HS. apply HS. Qed.
Lemma st_ok_regs_ok : forall E ss ms, st_ok segs E ss ms -> regs_ok E (ss_regs ss) (ms_regs ms).
Proof. intros E ss ms (_ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma st_ok_mem_ok : forall E ss ms, st_ok segs E ss ms -> mem_ok segs E (ms_mem ms) (ss_mem ss).
Proof. intros E ss ms (_ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma st_ok_pc : forall E ss ms, st_ok segs E ss ms -> ms_pc_val ms = Z_to_bv 64 (ss_pc ss).
Proof. intros E ss ms (_ & H & _). exact H. Qed.
Lemma st_ok_reg : forall E ss ms r,
st_ok segs E ss ms -> getr (ms_regs ms) r = sv_denot E (sr_get (ss_regs ss) r).
Proof. intros E ss ms r HS. apply (st_ok_regs_ok E ss ms HS). Qed.
Lemma st_ok_add_fact : forall E ss ms n f,
st_ok segs E ss ms -> afact_ok E n f -> st_ok segs E (add_atom ss n f) ms.
Proof.
intros E ss ms n f (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) Hf.
unfold st_ok, add_atom; cbn. repeat (split; [assumption|]).
apply facts_ok_add_atom; assumption.
Qed.
Definition add_alias (ss : sstate) (a b : sv) : sstate :=
mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss)
(mkFacts (f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) ((a, b) :: f_alias (ss_facts ss))).
Lemma st_ok_add_alias : forall E ss ms a b,
st_ok segs E ss ms -> sv_denot E a = sv_denot E b -> st_ok segs E (add_alias ss a b) ms.
Proof.
intros E ss ms a b (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) Hab.
unfold st_ok, add_alias; cbn. repeat (split; [assumption|]).
apply facts_ok_add_alias; assumption.
Qed.
Definition set_facts (ss : sstate) (G : facts) : sstate :=
mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss) G.
Lemma st_ok_set_facts : forall E ss ms G,
st_ok segs E ss ms -> facts_ok E G -> st_ok segs E (set_facts ss G) ms.
Proof.
intros E ss ms G (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HG.
unfold st_ok, set_facts; cbn. repeat (split; [assumption|]). exact HG.
Qed.
Fixpoint pick {A} (l : list A) (idx : list nat) : list A :=
match idx with
| [] => []
| i :: idx' => match nth_error l i with Some x => x :: pick l idx' | None => pick l idx' end
end.
Lemma pick_incl {A} : forall (l : list A) idx x, In x (pick l idx) -> In x l.
Proof.
intros l idx. induction idx as [|i idx IH]; intros x H; cbn in H; [destruct H|].
destruct (nth_error l i) eqn:Hn.
- destruct H as [<-|H]; [eapply nth_error_In; eauto | auto].
- auto.
Qed.
Definition prune_facts (G : facts) (ci ai : list nat) : facts :=
mkFacts (f_atoms G) (pick (f_conds G) ci) (pick (f_alias G) ai).
Lemma conds_ok_forall : forall E l, conds_ok E l <-> (forall c, In c l -> acond_ok E c).
Proof.
intros E l. induction l as [|c l IH]; cbn.
- split; [intros _ c []| intros; exact I].
- split.
+ intros [Hc Hl] c' [<-|Hin]; [exact Hc| apply IH; assumption].
+ intros H. split; [apply H; left; reflexivity| apply IH; intros c' Hc'; apply H; right; exact Hc'].
Qed.
Lemma alias_ok_forall : forall E l, alias_ok E l <-> (forall p, In p l -> sv_denot E (fst p) = sv_denot E (snd p)).
Proof.
intros E l. induction l as [|[a b] l IH]; cbn.
- split; [intros _ p []| intros; exact I].
- split.
+ intros [Hc Hl] p [<-|Hin]; [exact Hc| apply IH; assumption].
+ intros H. split; [apply (H (a, b)); left; reflexivity| apply IH; intros p Hp; apply H; right; exact Hp].
Qed.
Lemma facts_ok_prune : forall E G ci ai, facts_ok E G -> facts_ok E (prune_facts G ci ai).
Proof.
intros E G ci ai (Ha & Hc & Hl). unfold prune_facts. split; [exact Ha|]. split.
- apply conds_ok_forall. intros c Hin. apply (proj1 (conds_ok_forall E _) Hc). eapply pick_incl; eauto.
- apply alias_ok_forall. intros p Hin. apply (proj1 (alias_ok_forall E _) Hl). eapply pick_incl; eauto.
Qed.
Definition prune (ss : sstate) (ci ai : list nat) : sstate :=
set_facts ss (prune_facts (ss_facts ss) ci ai).
Lemma st_ok_prune : forall E ss ms ci ai, st_ok segs E ss ms -> st_ok segs E (prune ss ci ai) ms.
Proof.
intros E ss ms ci ai HS. apply st_ok_set_facts; [exact HS|].
apply facts_ok_prune. apply (st_ok_facts_ok E ss ms HS).
Qed.
Definition keep_regions (ss : sstate) (idx : list nat) : sstate :=
mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) (pick (ss_mem ss) idx) (ss_resv ss) (ss_facts ss).
Lemma regions_wf_forall : forall rs, regions_wf rs = true <-> (forall r, In r rs -> region_wf r = true).
Proof.
induction rs as [|r rs IH]; cbn.
- split; [intros _ r []| reflexivity].
- rewrite Bool.andb_true_iff. split.
+ intros [Hr Hrs] r' [<-|Hin]; [exact Hr| apply IH; assumption].
+ intros H. split; [apply H; left; reflexivity| apply IH; intros r' Hin; apply H; right; exact Hin].
Qed.
Fixpoint sr_sets (sr : list sv) (upd : list (reg * sv)) : list sv :=
match upd with
| [] => sr
| (r, v) :: upd' => sr_sets (sr_set sr r v) upd'
end.
Definition set_regs_pc (ss : sstate) (upd : list (reg * sv)) (pc : Z) : sstate :=
mkSST pc (sr_sets (ss_regs ss) upd) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss).
Fixpoint reg_in (r : reg) (l : list reg) : bool :=
match l with [] => false | r' :: l' => bv_eqb r r' || reg_in r l' end.
Fixpoint reg_nodup (l : list reg) : bool :=
match l with [] => true | r :: l' => negb (reg_in r l') && reg_nodup l' end.
Lemma reg_in_false : forall r l, reg_in r l = false -> ~ In r l.
Proof.
induction l as [|r' l IH]; cbn; intros H; [tauto|].
apply Bool.orb_false_iff in H as [H1 H2]. intros [<-|Hin].
- rewrite bv_eqb_refl in H1. discriminate.
- apply IH; assumption.
Qed.
Lemma reg_in_true : forall r l, In r l -> reg_in r l = true.
Proof.
intros r l H. destruct (reg_in r l) eqn:E; [reflexivity|].
exfalso. exact (reg_in_false r l E H).
Qed.
Lemma reg_nodup_sound : forall l, reg_nodup l = true -> NoDup l.
Proof.
induction l as [|r l IH]; cbn; intros H; [constructor|].
apply andb_prop in H as [H1 H2]. apply NoDup_cons_2; [|apply IH; exact H2].
rewrite list_elem_of_In. apply reg_in_false. destruct (reg_in r l); [discriminate|reflexivity].
Qed.
Lemma sr_get_set_same : forall sr r v, bv_eqb r 0 = false -> sr_get (sr_set sr r v) r = v.
Proof.
intros sr r v Hr. unfold sr_get, sr_set. rewrite Hr. rewrite nth_sr_upd, Nat.eqb_refl. reflexivity.
Qed.
Lemma sr_get_set_other : forall sr r r' v, r' <> r -> sr_get (sr_set sr r v) r' = sr_get sr r'.
Proof.
intros sr r r' v Hne. unfold sr_get, sr_set.
destruct (bv_eqb r' 0) eqn:H0; [reflexivity|].
destruct (bv_eqb r 0) eqn:H1; [reflexivity|].
rewrite nth_sr_upd. destruct (Nat.eqb_spec (ridx r') (ridx r)) as [Heq|Hneq]; [|reflexivity].
exfalso. apply Hne. apply ridx_inj. exact Heq.
Qed.
Lemma regs_ok_sets : forall E sr regs regs' upd,
regs_ok E sr regs ->
NoDup (map fst upd) ->
(forall r, reg_in r (map fst upd) = false -> getr regs' r = getr regs r) ->
Forall (fun p => bv_eqb (fst p) 0 = false /\ getr regs' (fst p) = sv_denot E (snd p)) upd ->
regs_ok E (sr_sets sr upd) regs'.
Proof.
intros E sr regs regs' upd. revert sr regs.
induction upd as [|[r v] upd IH]; intros sr regs Hok Hnd Hsame Hupd; cbn.
- intros r. rewrite Hsame by reflexivity. apply Hok.
- inversion Hnd as [|x l Hnotin Hnd']; subst.
apply Forall_cons_iff in Hupd as [[Hr0 Hrv] Hupd]. cbn in Hr0, Hrv, Hnotin.
apply (IH (sr_set sr r v) (regupd regs r (getr regs' r))).
+ intros r'. destruct (decide (r' = r)) as [->|Hne].
* rewrite sr_get_set_same by exact Hr0. unfold getr, regupd. rewrite Hr0.
unfold reg_get. rewrite bvmap_get_set_same. fold (getr regs' r).
unfold getr in Hrv. rewrite Hr0 in Hrv. exact Hrv.
* rewrite sr_get_set_other by exact Hne. rewrite getr_other by exact Hne. apply Hok.
+ exact Hnd'.
+ intros r' Hn. destruct (decide (r' = r)) as [->|Hne].
* unfold getr, regupd. rewrite Hr0. unfold reg_get. rewrite bvmap_get_set_same. reflexivity.
* rewrite getr_other by exact Hne. apply Hsame. cbn. rewrite Hn. rewrite (bv_eqb_neq _ _ Hne). reflexivity.
+ exact Hupd.
Qed.
Lemma st_ok_set_regs : forall k E E' ss regs regs' pc pc' mem upd,
st_ok segs E ss (mkst regs pc mem (seg_rom segs)) ->
env_agree k E E' -> ss_atoms_lt k ss = true -> ss_resv ss = None ->
reg_nodup (map fst upd) = true ->
(forall r, reg_in r (map fst upd) = false -> getr regs' r = getr regs r) ->
Forall (fun p => bv_eqb (fst p) 0 = false /\ getr regs' (fst p) = sv_denot E' (snd p)) upd ->
st_ok segs E' (set_regs_pc ss upd pc') (mkst regs' (Z_to_bv 64 pc') mem (seg_rom segs)).
Proof.
intros k E E' ss regs regs' pc pc' mem upd HS HA Hat Hrv Hnd Hsame Hupd.
pose proof (st_ok_agree k E E' ss _ HS HA Hat) as HS'.
destruct HS' as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
unfold st_ok, set_regs_pc; cbn. rewrite Hrv. cbn.
repeat (split; [reflexivity|]). split.
- eapply regs_ok_sets; eauto using reg_nodup_sound.
- split; assumption.
Qed.
Lemma st_ok_set_regs_mem : forall k E E' ss regs regs' pc pc' mem mem' rs' upd,
st_ok segs E ss (mkst regs pc mem (seg_rom segs)) ->
env_agree k E E' -> ss_atoms_lt k ss = true ->
reg_nodup (map fst upd) = true ->
(forall r, reg_in r (map fst upd) = false -> getr regs' r = getr regs r) ->
Forall (fun p => bv_eqb (fst p) 0 = false /\ getr regs' (fst p) = sv_denot E' (snd p)) upd ->
mem_ok segs E' mem' rs' ->
st_ok segs E' (mkSS pc' (sr_sets (ss_regs ss) upd) rs' None (ss_facts ss))
(mkst regs' (Z_to_bv 64 pc') mem' (seg_rom segs)).
Proof.
intros k E E' ss regs regs' pc pc' mem mem' rs' upd HS HA Hat Hnd Hsame Hupd HM.
pose proof (st_ok_agree k E E' ss _ HS HA Hat) as HS'.
destruct HS' as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
unfold st_ok; cbn. repeat (split; [reflexivity|]). split.
- eapply regs_ok_sets; eauto using reg_nodup_sound.
- split; assumption.
Qed.
Lemma st_ok_abstract_reg : forall n E ss ms r,
st_ok segs E ss ms -> ss_atoms_lt n ss = true -> bv_eqb r 0 = false ->
st_ok segs (ewset E n (getr (ms_regs ms) r))
(mkSS (ss_pc ss) (sr_set (ss_regs ss) r (SOff n 0)) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros n E ss ms r HS Hat Hr.
pose proof (st_ok_agree n E (ewset E n (getr (ms_regs ms) r)) ss ms HS (env_agree_ewset _ _ _) Hat)
as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|split; assumption].
intros r'. destruct (decide (r' = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr. cbn. rewrite Nat.eqb_refl.
rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- rewrite sr_get_set_other by exact Hne. apply H7.
Qed.
Lemma st_ok_ecall_shape : forall E ss ms,
st_ok_ecall segs E ss ms -> ss_resv ss = None ->
exists regs mem,
ms = pend_at regs (Z_to_bv 64 (ss_pc ss)) mem (seg_rom segs)
/\ regs_ok E (ss_regs ss) regs
/\ mem_ok segs E mem (ss_mem ss)
/\ facts_ok E (ss_facts ss).
Proof.
intros E ss ms HS Hrv.
destruct (st_ok_ecall_pend segs E ss ms HS Hrv) as (Hms & Hregs & Hpc & Hmem & HG).
exists (ms_regs ms), (ms_mem ms). rewrite <- Hpc. auto.
Qed.
Lemma st_ok_resume_sv : forall E ss regs mem rv RET,
regs_ok E (ss_regs ss) regs ->
mem_ok segs E mem (ss_mem ss) -> facts_ok E (ss_facts ss) ->
sv_denot E rv = RET ->
st_ok segs E (resume ss rv (ss_mem ss) (ss_facts ss))
(mkst (regupd regs 10 RET) (v_addi (Z_to_bv 64 (ss_pc ss)) 4) mem (seg_rom segs)).
Proof.
intros E ss regs mem rv RET Hregs Hmem HG Hrv.
unfold st_ok, resume, mkst; cbn.
split; [reflexivity|]. split.
{ unfold v_addi. rewrite Z_to_bv_unsigned. apply Z_to_bv64_eq_mod.
unfold bv_wrap. change (bv_modulus 64) with (2^64). apply Zplus_mod_idemp_l. }
repeat (split; [reflexivity|]). split; [|split; assumption].
change (regupd regs 10 RET) with (if bv_eqb (10:reg) 0 then regs else regupd regs 10 RET).
apply regs_ok_set; assumption.
Qed.
Lemma st_ok_resume_atom : forall n f E ss regs mem RET,
regs_ok E (ss_regs ss) regs ->
mem_ok segs E mem (ss_mem ss) -> facts_ok E (ss_facts ss) ->
ss_atoms_lt n ss = true ->
af_lo f <= bv_unsigned RET <= af_hi f -> 0 <= af_al2 f <= 64 -> bv_unsigned RET mod 2 ^ af_al2 f = 0 ->
st_ok segs (ewset E n RET)
(resume ss (SOff n 0) (ss_mem ss)
(mkFacts ((n, f) :: f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) (f_alias (ss_facts ss))))
(mkst (regupd regs 10 RET) (v_addi (Z_to_bv 64 (ss_pc ss)) 4) mem (seg_rom segs)).
Proof.
intros n f E ss regs mem RET Hregs Hmem HG Hat Hrange Hal Hmod.
set (E' := ewset E n RET).
assert (HA : env_agree n E E') by apply env_agree_ewset.
unfold ss_atoms_lt in Hat.
apply andb_prop in Hat as [Hat _]. apply andb_prop in Hat as [Hat HGa].
apply andb_prop in Hat as [Hr Hm].
unfold st_ok, resume, mkst; cbn.
split; [reflexivity|]. split.
{ unfold v_addi. rewrite Z_to_bv_unsigned. apply Z_to_bv64_eq_mod.
unfold bv_wrap. change (bv_modulus 64) with (2^64). apply Zplus_mod_idemp_l. }
repeat (split; [reflexivity|]). split.
- change (regupd regs 10 RET) with (if bv_eqb (10:reg) 0 then regs else regupd regs 10 RET).
apply regs_ok_set; [eapply regs_ok_agree; eauto|].
cbn. rewrite Nat.eqb_refl, Z.add_0_r. apply Z_to_bv_bv_unsigned.
- split; [eapply mem_ok_agree; eauto|].
apply facts_ok_add_atom; [eapply facts_ok_agree; eauto|].
unfold afact_ok. subst E'. rewrite ew_ewset_same. destruct f; cbn in *. lia.
Qed.
Lemma st_ok_resume_mem : forall k E E' ss regs mem' rv RET rs G,
regs_ok E (ss_regs ss) regs ->
env_agree k E E' -> regs_atoms_lt k (ss_regs ss) = true ->
sv_denot E' rv = RET ->
mem_ok segs E' mem' rs -> facts_ok E' G ->
st_ok segs E' (resume ss rv rs G)
(mkst (regupd regs 10 RET) (v_addi (Z_to_bv 64 (ss_pc ss)) 4) mem' (seg_rom segs)).
Proof. intros. eapply st_ok_resume; eauto. Qed.
Lemma rz_sym_exit : forall E ss ms model (code : Z),
m_halted model = None -> m_vm_lazy model = [] ->
st_ok_ecall segs E ss ms -> ss_resv ss = None ->
is_exit_no (sv_denot E (sr_get (ss_regs ss) 17)) ->
sv_denot E (sr_get (ss_regs ss) 10) = Z_to_bv 64 code -> 0 <= code < 256 ->
realizes segs (mkCfg ms model) (t_exit (Z_to_bv 64 code) (m_fs model)).
Proof.
intros E ss ms model code Hh Hlz HS Hrv Hno Ha0 Hc.
destruct (st_ok_ecall_shape E ss ms HS Hrv) as (regs & mem & -> & Hregs & Hmem & HG).
apply rz_exit_small.
- exact Hh.
- exact Hlz.
- rewrite (Hregs 17%bv). exact Hno.
- rewrite (Hregs 10%bv). exact Ha0.
- rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_small; lia.
Qed.
Lemma rz_sym_write : forall E ss ms model fd ch buf T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok_ecall segs E ss ms -> ss_resv ss = None ->
bv_unsigned (sv_denot E (sr_get (ss_regs ss) 17)) = 64 ->
sv_denot E (sr_get (ss_regs ss) 10) = fd ->
fdchan fd ch model -> fd32 fd = fd ->
rdn segs (ms_mem ms) (sv_denot E (sr_get (ss_regs ss) 11))
(word_to_nat (sv_denot E (sr_get (ss_regs ss) 12))) = Some buf ->
buf_modeled buf -> (1 <= length buf)%nat ->
(forall k ms', (1 <= k)%nat -> (k <= length buf)%nat ->
st_ok segs E (resume ss (SLit (Z.of_nat k)) (ss_mem ss) (ss_facts ss)) ms' ->
ms_mem ms' = ms_mem ms ->
realizes segs (mkCfg ms' model) T) ->
realizes segs (mkCfg ms model) (t_write_ch ch buf T).
Proof.
intros E ss ms model fd ch buf T Hh Hlz HS Hrv Hno Ha0 Hch H32 Hbuf Hbm Hnb Hk.
destruct (st_ok_ecall_shape E ss ms HS Hrv) as (regs & mem & Hms & Hregs & Hmem & HG).
subst ms. cbn [ms_mem pend_at] in Hbuf, Hk.
eapply rz_write.
- exact Hh.
- exact Hlz.
- rewrite (Hregs 17%bv). exact Hno.
- exact Hch.
- exact H32.
- rewrite (Hregs 10%bv). exact Ha0.
- rewrite (ms_read_bytes_rdn segs) by reflexivity. cbn [ms_mem pend_at].
rewrite (Hregs 11%bv), (Hregs 12%bv). exact Hbuf.
- exact Hbm.
- exact Hnb.
- intros n Hn1 Hn2. apply (Hk n); [exact Hn1|exact Hn2| |reflexivity].
replace (len_word (firstn n buf)) with (sv_denot E (SLit (Z.of_nat n))).
+ apply st_ok_resume_sv; auto.
+ cbn [sv_denot]. unfold len_word. rewrite length_firstn.
rewrite Nat.min_l by exact Hn2. reflexivity.
Qed.
Lemma st_ok_mkst : forall E ss ms,
st_ok segs E ss ms -> ss_resv ss = None ->
ms = mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs).
Proof.
intros E ss ms (Hfr & Hpc & Hpend & Hresv & Hfcsr & Hrom & _) Hrv.
destruct ms as [regs fregs pcv pend resv fcsr mem rom]; cbn in *.
rewrite Hrv in Hresv. cbn in Hresv. subst. reflexivity.
Qed.
Definition bytes_at (m : word -> option byte) (a : Z) (bs : list byte) : Prop :=
forall j, (j < length bs)%nat -> m (Z_to_bv 64 (a + Z.of_nat j)) = nth_error bs j.
Definition runs_at (spv : Z) (m : word -> option byte) (l : list (Z * list byte)) : Prop :=
Forall (fun ab => spv <= fst ab
/\ fst ab + Z.of_nat (length (snd ab)) <= 2 ^ 64
/\ bytes_at m (fst ab) (snd ab)) l.
Fixpoint cond_caps_whi (l : list acond) (n : nat) (whi lo hi : Z) : bool :=
match l with
| [] => false
| c :: l' =>
(match ac_c c, ac_a c, ac_b c with
| BC_GEU, SOff O 0, SOff m K =>
Nat.eqb m n && (whi <=? K) && (0 <=? lo + K) && (hi + K <? 2 ^ 64)
| _, _, _ => false
end) || cond_caps_whi l' n whi lo hi
end.
Definition wr_below_sp (G : facts) (rs : smem) : bool :=
match atom_lookup (f_atoms G) 0 with
| None => false
| Some f0 =>
forallb (fun r =>
(r_whi r <=? r_wlo r) ||
match r_base r with
| None => r_whi r <=? af_lo f0
| Some O => r_whi r <=? 0
| Some n => match atom_lookup (f_atoms G) n with
| Some f => (af_hi f + r_whi r <=? af_lo f0)
|| cond_caps_whi (f_conds G) n (r_whi r) (af_lo f) (af_hi f)
| None => false
end
end) rs
end.
Lemma acond_geu_sp_intro : forall E n K,
0 <= bv_unsigned (ew E n) + K <= bv_unsigned (ew E 0) ->
branch_taken BC_GEU (sv_denot E (SOff 0 0)) (sv_denot E (SOff n K)) = true.
Proof.
intros E n K HK. pose proof (u64_range (ew E 0)) as H0.
cbn [branch_taken sv_denot]. unfold bv_ltu. rewrite Z.add_0_r, !Z_to_bv_unsigned.
change (bv_wrap 64 ?x) with (x mod 2^64). rewrite !Z.mod_small by lia.
apply negb_true_iff. apply Z.ltb_ge. lia.
Qed.
Lemma cond_caps_whi_sound : forall E l n whi lo hi,
conds_ok E l -> cond_caps_whi l n whi lo hi = true ->
lo <= bv_unsigned (ew E n) <= hi ->
bv_unsigned (ew E n) + whi <= bv_unsigned (ew E 0).
Proof.
intros E l n whi lo hi. induction l as [|c l IH]; cbn [cond_caps_whi conds_ok]; intros Hok H Hn;
[discriminate|].
destruct Hok as [Hc Hl]. apply orb_prop in H as [H|H]; [|exact (IH Hl H Hn)]. clear IH Hl.
destruct c as [cc ca cb]; cbn [ac_c ac_a ac_b] in H. unfold acond_ok in Hc; cbn [ac_c ac_a ac_b] in Hc.
destruct cc; try discriminate H.
destruct ca as [|n0 z0| | | | | | | | |]; try discriminate H.
destruct n0; [|discriminate H]. destruct z0; try discriminate H.
destruct cb as [|m K| | | | | | | | |]; try discriminate H.
rewrite !andb_true_iff in H. destruct H as [[[Hm Hw] Hlo] Hhi].
apply Nat.eqb_eq in Hm. subst m. apply Z.leb_le in Hw. apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
pose proof (u64_range (ew E 0)) as H0.
cbn [branch_taken sv_denot] in Hc. unfold bv_ltu in Hc. rewrite Z.add_0_r, !Z_to_bv_unsigned in Hc.
change (bv_wrap 64 ?x) with (x mod 2^64) in Hc. rewrite !Z.mod_small in Hc by lia.
apply negb_true_iff in Hc. apply Z.ltb_ge in Hc. lia.
Qed.
Lemma wr_below_sp_sound : forall E G rs x,
facts_ok E G -> wr_below_sp G rs = true -> in_wrange E rs x -> x < bv_unsigned (ew E 0).
Proof.
intros E G rs x HG H (r & Hin & Hx). unfold wr_below_sp in H.
destruct (atom_lookup (f_atoms G) 0) as [f0|] eqn:H0; [|discriminate].
pose proof (atom_lookup_ok E _ _ _ (proj1 HG) H0) as (Hf0 & _).
pose proof (proj1 (forallb_forall _ _) H r Hin) as Hr. cbn beta in Hr.
apply orb_prop in Hr as [Hr|Hr]; [apply Z.leb_le in Hr; lia|].
destruct (r_base r) as [[|n]|] eqn:Hb; cbn [base_val] in Hx.
- apply Z.leb_le in Hr. lia.
- destruct (atom_lookup (f_atoms G) (S n)) as [f|] eqn:Hn; [|discriminate].
pose proof (atom_lookup_ok E _ _ _ (proj1 HG) Hn) as (Hf & _).
apply orb_prop in Hr as [Hr|Hr]; [apply Z.leb_le in Hr; lia|].
pose proof (cond_caps_whi_sound E (f_conds G) (S n) (r_whi r) (af_lo f) (af_hi f)
(proj1 (proj2 HG)) Hr Hf). lia.
- apply Z.leb_le in Hr. lia.
Qed.
Lemma bytes_at_frame : forall (m m' : word -> option byte) a bs,
(forall x : word, a <= bv_unsigned x < a + Z.of_nat (length bs) -> m' x = m x) ->
0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
bytes_at m a bs -> bytes_at m' a bs.
Proof.
intros m m' a bs Hfr Ha Hnw H j Hj. rewrite Hfr; [apply H; exact Hj|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite Z.mod_small by lia. lia.
Qed.
Lemma runs_at_frame : forall E G rs m m' spv l,
facts_ok E G -> wr_below_sp G rs = true -> frame_of E rs m m' ->
bv_unsigned (ew E 0) <= spv ->
runs_at spv m l -> runs_at spv m' l.
Proof.
intros E G rs m m' spv l HG Hw Hfr Hsp H. unfold runs_at in *.
rewrite Forall_forall in *. intros [a bs] Hin. specialize (H _ Hin). cbn in *.
destruct H as (Ha & Hnw & Hb). split; [exact Ha|]. split; [exact Hnw|].
pose proof (u64_range (ew E 0)).
apply (bytes_at_frame m m' a bs); [|lia|exact Hnw|exact Hb].
intros x Hx. apply Hfr. intros Hin'. pose proof (wr_below_sp_sound E G rs _ HG Hw Hin'). lia.
Qed.
Lemma runs_at_eqmem : forall spv m m' l, m' = m -> runs_at spv m l -> runs_at spv m' l.
Proof. intros; subst; assumption. Qed.
Lemma runs_at_nth : forall spv m l i a bs,
runs_at spv m l -> nth_error l i = Some (a, bs) -> bytes_at m a bs.
Proof.
intros spv m l i a bs H Hn. unfold runs_at in H. rewrite Forall_forall in H.
apply nth_error_In in Hn. specialize (H _ Hn). cbn in H. tauto.
Qed.
Lemma runs_at_bounds : forall spv m l i a bs,
runs_at spv m l -> nth_error l i = Some (a, bs) -> spv <= a /\ a + Z.of_nat (length bs) <= 2 ^ 64.
Proof.
intros spv m l i a bs H Hn. unfold runs_at in H. rewrite Forall_forall in H.
apply nth_error_In in Hn. specialize (H _ Hn). cbn in H. tauto.
Qed.
Lemma bytes_at_rdn : forall m a bs,
bytes_at m a bs -> rdn segs m (Z_to_bv 64 a) (length bs) = Some bs.
Proof.
intros m a bs H. apply (proj2 (rdn_mbytes segs m (length bs) a bs)).
split; [reflexivity|]. intros i Hi. unfold mbyte. rewrite (H i Hi).
destruct (nth_error bs i) eqn:Hn; [reflexivity|].
exfalso. apply nth_error_None in Hn. lia.
Qed.
Lemma bytes_at_mbyte : forall m a bs j,
bytes_at m a bs -> (j < length bs)%nat ->
mbyte segs m (a + Z.of_nat j) = nth_error bs j.
Proof.
intros m a bs j H Hj. unfold mbyte. rewrite (H j Hj).
destruct (nth_error bs j) eqn:Hn; [reflexivity|].
exfalso. apply nth_error_None in Hn. lia.
Qed.
Lemma bytes_at_app_l : forall m a l1 l2, bytes_at m a (l1 ++ l2) -> bytes_at m a l1.
Proof.
intros m a l1 l2 H j Hj. rewrite <- (nth_error_app1 l1 l2 Hj). apply H. rewrite length_app. lia.
Qed.
Lemma bytes_at_app_r : forall m a l1 l2,
bytes_at m a (l1 ++ l2) -> bytes_at m (a + Z.of_nat (length l1)) l2.
Proof.
intros m a l1 l2 H j Hj.
replace (a + Z.of_nat (length l1) + Z.of_nat j) with (a + Z.of_nat (length l1 + j)) by lia.
rewrite (H (length l1 + j)%nat) by (rewrite length_app; lia).
rewrite nth_error_app2 by lia. f_equal. lia.
Qed.
Lemma runs_at_after : forall E ss' ms' rs m spv l,
st_ok segs E ss' ms' -> wr_below_sp (ss_facts ss') rs = true ->
frame_of E rs m (ms_mem ms') -> bv_unsigned (ew E 0) <= spv ->
runs_at spv m l -> runs_at spv (ms_mem ms') l.
Proof.
intros E ss' ms' rs m spv l HS Hw Hfr Hsp H.
eapply runs_at_frame; [apply (st_ok_facts_ok E ss' ms' HS) | exact Hw | exact Hfr | exact Hsp | exact H].
Qed.
Lemma runs_at_after_ecall : forall E ss' ms' rs m spv l,
st_ok_ecall segs E ss' ms' -> wr_below_sp (ss_facts ss') rs = true ->
frame_of E rs m (ms_mem ms') -> bv_unsigned (ew E 0) <= spv ->
runs_at spv m l -> runs_at spv (ms_mem ms') l.
Proof.
intros E ss' ms' rs m spv l HS Hw Hfr Hsp H.
destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & HG).
eapply runs_at_frame; [exact HG | exact Hw | exact Hfr | exact Hsp | exact H].
Qed.
End e.
Lemma unsigned_lit_small : forall z, 0 <= z < 2^64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn [Z.of_N]. lia. Qed.
Lemma word_to_nat_lit : forall z, 0 <= z < 2^64 -> word_to_nat (Z_to_bv 64 z) = Z.to_nat z.
Proof. intros z Hz. unfold word_to_nat. rewrite unsigned_lit_small by lia. reflexivity. Qed.
Definition FUEL : N := 200000%N.
Ltac sym_eval_run segs tbl ss :=
eval vm_compute in (sym_runN segs tbl FUEL ss).
Ltac sym_transport segs E ss ss' ms' HS HF :=
cbn [ms_mem mkst pend_at] in HF;
repeat match goal with
| HR : runs_at ?spv ?m ?l |- _ =>
lazymatch m with
| ms_mem ms' => fail
| _ => first
[ apply (runs_at_after segs E ss' ms' (ss_mem ss) m spv l HS
ltac:(vm_compute; reflexivity) HF ltac:(cbn; lia)) in HR
| fail 1 ]
end
end;
try clear HF;
try match type of HS with st_ok _ _ _ ?ms' =>
repeat match goal with
| old : machine_state |- _ => lazymatch old with ms' => fail | _ => clear old end
end
end.
Ltac sym_transport_ecall segs E ss ss' ms' HS HF :=
cbn [ms_mem mkst pend_at] in HF;
repeat match goal with
| HR : runs_at ?spv ?m ?l |- _ =>
lazymatch m with
| ms_mem ms' => fail
| _ => first
[ apply (runs_at_after_ecall segs E ss' ms' (ss_mem ss) m spv l HS
ltac:(vm_compute; reflexivity) HF ltac:(cbn; lia)) in HR
| fail 1 ]
end
end;
try clear HF;
repeat match goal with
| old : machine_state |- _ => lazymatch old with ms' => fail | _ => clear old end
end.
Ltac sym_run_with tblok HS :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_runN segs tbl FUEL ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
let ms' := fresh "ms" in let HF := fresh "HF" in
lazymatch st with
| RS_ecall =>
eapply (rz_run_ecall segs tbl tblok FUEL E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport_ecall segs E ss ss' ms' HS HF
| RS_stopped ?why =>
eapply (rz_run_stop segs tbl tblok FUEL E ss ss' why ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport segs E ss ss' ms' HS HF
| RS_running =>
eapply (rz_run_running segs tbl tblok FUEL E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport segs E ss ss' ms' HS HF
end
end
end
end.
Ltac sym_why segs tbl ss :=
let r := eval vm_compute in (sym_step segs tbl ss) in
match r with
| SStop ?why => why
| SEcall _ => constr:(SR_unsupported)
| SRun _ => constr:(SR_unsupported)
end.
Ltac sym_branch_with tblok HS :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let why := sym_why segs tbl ss in
lazymatch why with
| SR_branch ?c ?a ?b =>
apply (rz_branch segs E ss ms _ _ c a b HS);
clear HS;
let Hc := fresh "Hc" in
intros Hc HS
| _ => fail "sym_branch: state is not stuck at a branch:" why
end
end
end.
Ltac sym_assume_with tblok HS dir :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let why := sym_why segs tbl ss in
lazymatch why with
| SR_branch ?c ?a ?b =>
lazymatch dir with
| true =>
let H := fresh in
assert (H : branch_taken c (sv_denot E a) (sv_denot E b) = true);
[| apply (st_ok_add_cond segs E ss ms c a b) in HS; [clear H | exact H] ]
| false =>
let H := fresh in
assert (H : branch_taken c (sv_denot E a) (sv_denot E b) = false);
[| apply (st_ok_add_cond_neg segs E ss ms c a b) in HS; [clear H | exact H] ]
end
| _ => fail "sym_assume: state is not stuck at a branch:" why
end
end
end.
Ltac sym_ecall_open HS :=
lazymatch type of HS with
| st_ok_ecall ?segs ?E ?ss ?ms =>
let regs := fresh "regs" in let mem := fresh "mem" in
let Hms := fresh "Hms" in
let Hregs := fresh "Hregs" in let Hmem := fresh "Hmem" in let HG := fresh "HG" in
destruct (st_ok_ecall_shape segs E ss ms HS eq_refl) as (regs & mem & Hms & Hregs & Hmem & HG);
clear HS; subst ms; cbn [ss_pc ss_regs ss_mem ss_facts] in Hregs, Hmem, HG
end.
Ltac reg_eval Hregs r :=
rewrite (Hregs r); cbn [sr_get bv_eqb ridx nth Z.to_nat Pos.to_nat bv_unsigned Z.eqb].
Ltac sym_norm HS :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
let ss' := eval vm_compute in ss in
change (st_ok segs E ss' ms) in HS
| st_ok_ecall ?segs ?E ?ss ?ms =>
let ss' := eval vm_compute in ss in
change (st_ok_ecall segs E ss' ms) in HS
end.
Ltac sym_where tbl HS :=
lazymatch type of HS with
| st_ok ?segs _ ?ss _ =>
let pc := eval vm_compute in (ss_pc ss) in
let w := sym_why segs tbl ss in idtac "st_ok at" pc w
| st_ok_ecall _ _ ?ss _ =>
let pc := eval vm_compute in (ss_pc ss) in idtac "ecall at" pc
end.
Ltac st_mem_ok HS :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms => constr:(st_ok_mem_ok segs E ss ms HS)
| st_ok_ecall ?segs ?E ?ss ?ms =>
constr:(match HS with conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj Hm _))))))) => Hm end)
end.
Ltac rdn_of_chunk HS :=
lazymatch goal with
| |- rdn ?segs ?m (sv_denot ?E ?av) (word_to_nat (sv_denot _ ?nv)) = Some _ =>
let a := eval vm_compute in (match sv_lit av with Some z => z | None => 0 end) in
let n := eval vm_compute in (match sv_lit nv with Some z => Z.to_nat z | None => 0%nat end) in
let Hm := st_mem_ok HS in
lazymatch type of Hm with mem_ok _ _ _ ?rs =>
apply (mem_ok_read segs E m rs None a n _ _ Hm
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) I)
end
end.
Ltac sym_write_with HS Hch :=
lazymatch type of HS with
| st_ok_ecall ?segs ?E ?ss ?ms =>
lazymatch goal with |- realizes _ (mkCfg _ ?model) _ =>
lazymatch type of Hch with fdchan ?fd ?ch _ =>
eapply (rz_sym_write segs E ss ms model fd ch);
[ assumption | assumption | exact HS | reflexivity | reflexivity | reflexivity | exact Hch | reflexivity
|
|
|
| clear HS;
let k := fresh "k" in let ms' := fresh "ms" in let Hmm := fresh "Hmm" in
let Hk1 := fresh "Hk1" in let Hk2 := fresh "Hk2" in
intros k ms' Hk1 Hk2 HS Hmm;
repeat match goal with HR : runs_at ?spv (ms_mem ms) ?l |- _ => rewrite <- Hmm in HR end;
clear Hmm; try clear ms; sym_norm HS ]
end
end
end.
Ltac sym_exit_with HS :=
lazymatch type of HS with
| st_ok_ecall ?segs ?E ?ss ?ms =>
lazymatch goal with |- realizes _ (mkCfg _ ?model) (t_exit (Z_to_bv 64 ?code) _) =>
apply (rz_sym_exit segs E ss ms model code);
[ assumption | assumption | exact HS | reflexivity
| first [left; reflexivity | right; reflexivity]
| reflexivity | lia ]
end
end.
Ltac eval_sr_get_in H :=
repeat match type of H with context [sr_get ?a ?b] =>
let v := eval vm_compute in (sr_get a b) in change (sr_get a b) with v in H end.
Ltac eval_sr_get :=
repeat match goal with |- context [sr_get ?a ?b] =>
let v := eval vm_compute in (sr_get a b) in change (sr_get a b) with v end.
Tactic Notation "sym_reg" constr(HS) constr(r) "as" ident(Hr) :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
pose proof (st_ok_reg segs E ss ms r HS) as Hr;
eval_sr_get_in Hr; cbn in Hr; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hr
end.
Ltac sym_splice HS Hms k E' Hagree upd :=
lazymatch type of HS with st_ok ?segs ?E ?ss ?ms =>
lazymatch type of Hms with msteps _ _ (mkst ?regs' (Z_to_bv 64 ?pc') _ _) =>
let Hshape := fresh "Hshape" in
pose proof (st_ok_mkst segs E ss ms HS eq_refl) as Hshape;
rewrite Hshape; eapply rz_msteps; [assumption | assumption | exact Hms | ];
rewrite Hshape in HS; clear Hshape;
unshelve epose proof (st_ok_set_regs segs k E E' ss _ regs' _ pc' _ upd HS Hagree _ _ _ _ _);
[ vm_compute; reflexivity
| reflexivity
| vm_compute; reflexivity
|
|
| clear HS Hms;
match goal with Hn : st_ok _ _ (set_regs_pc _ _ _) _ |- _ => rename Hn into HS end;
sym_norm HS ]
end end.
Ltac sym_splice_frame Hfr :=
let r := fresh "r" in let Hr := fresh "Hr" in
intros r Hr; apply Hfr; intros ->; vm_compute in Hr; discriminate Hr.
Ltac sym_splice1 HS Hms k v upd :=
lazymatch type of HS with st_ok _ ?E _ _ =>
sym_splice HS Hms k (ewset E k v) (env_agree_ewset E k v) upd
end.
Ltac sym_splice0 HS Hms upd :=
lazymatch type of HS with st_ok _ ?E _ _ =>
sym_splice HS Hms 0%nat E (env_agree_refl 0%nat E) upd
end.
Ltac sym_add_fact HS n f :=
lazymatch type of HS with st_ok ?segs ?E ?ss ?ms =>
let Hf := fresh "Hf" in
assert (Hf : afact_ok E n f);
[ unfold afact_ok; cbn [af_lo af_hi af_al2 ew ewset edset nth Nat.eqb]
| apply (st_ok_add_fact segs E ss ms n f HS) in Hf; clear HS; rename Hf into HS; sym_norm HS ]
end.
