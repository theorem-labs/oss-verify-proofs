(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YQ05.v, with its module paths changed. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Run Specs RiscvSemantics MemImageType.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import SyscallTable.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YQ00 YQ03 YQ01 YQ04 YQ06.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope. Open Scope bv_scope. Open Scope sys_scope.
Set Default Proof Mode "Classic".
Section b.
Variable L0 L : Z.
Hypothesis HLE : L <= L0.
Definition ARM_OK (a : SpecArm) : Prop :=
forall (d : bool) i m, bv_unsigned (in_sysno i) = sa_no a -> MOK L0 m ->
alloc_budget_refused_b i (relim L m) = false -> (d = false -> MV_OK m) ->
DIR L0 L d i m (sa_spec a) (sa_spec a).
Lemma lookup_arm_In : forall t n a, lookup_arm t n = Some a -> In a t /\ sa_no a = n.
Proof.
induction t as [|x t IH]; intros n a H; [discriminate H|]. cbn in H.
destruct (Z.eqb (sa_no x) n) eqn:E.
- injection H as <-. split; [left; reflexivity | apply Z.eqb_eq; exact E].
- destruct (IH n a H) as [Hin Hno]. split; [right; exact Hin | exact Hno].
Qed.
Lemma dispatch_dir : forall t, (forall a, In a t -> ARM_OK a) ->
forall (d : bool) i m, MOK L0 m -> alloc_budget_refused_b i (relim L m) = false -> (d = false -> MV_OK m) ->
DIR L0 L d i m (dispatch t) (dispatch t).
Proof.
intros t Ht d i m HM G1 G2.
destruct (lookup_arm t (bv_unsigned (in_sysno i))) as [a|] eqn:E.
- destruct (lookup_arm_In _ _ _ E) as [Hin Hno].
pose proof (Ht a Hin d i m (eq_sym Hno) HM G1 G2) as H.
destruct d; intros o Ho; unfold dispatch in Ho |- *; rewrite E in Ho |- *; exact (H o Ho).
- destruct d; intros o Ho; unfold dispatch in Ho |- *; rewrite E in Ho |- *;
[ exact (dir_unmodeled L0 L true i m o Ho) | exact (dir_unmodeled L0 L false i m o Ho) ].
Qed.
Lemma spec_table_ok : forall a, In a spec_table -> ARM_OK a.
Proof.
intros a Hin d i m Hno HM G1 G2.
unfold spec_table in Hin.
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_17 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_19 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_20 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_21 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_22 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_23 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_24 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_25 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_29 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_32 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_35 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_46 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_48 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_56 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_57 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_59 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_61 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_62 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_63 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_64 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_65 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_66 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_67 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_68 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_72 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_73 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_78 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_79 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_80 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_82 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_83 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_85 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_93 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_94 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_96 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_98 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_101 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_113 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_119 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_123 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_124 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_130 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_131 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_132 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_134 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_135 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_144 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_146 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_147 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_149 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_157 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_158 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_159 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_160 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_167 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_169 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_172 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_174 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_175 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_176 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_177 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_178 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_198 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_199 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_200 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_201 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_202 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_203 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_204 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_205 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_206 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_207 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_208 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_209 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_210 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_211 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_212 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; assert (Gb : d = false -> brk_budget_refused_b (relim L m) (in_arg i 0) = false) by (intros Hd; unfold alloc_budget_refused_b in G1; rewrite Hno in G1; exact G1); apply (dir_table_form L0 L d i m (fun i0 => brk_spec (in_arg i 0)) (fun i0 => brk_spec (in_arg i 0))); lazy beta; exact (sim_brk L0 L HLE d i m HM Gb) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_215 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; assert (Gb : d = false -> mremap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (relim L m) = false) by (intros Hd; unfold alloc_budget_refused_b in G1; rewrite Hno in G1; exact G1); apply (dir_table_form L0 L d i m (fun i0 => mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)) (fun i0 => mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3))); lazy beta; exact (sim_mremap L0 L HLE d i m HM G2 Gb) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_220 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; assert (Gb : mmap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) (relim L m) = false) by (unfold alloc_budget_refused_b in G1; rewrite Hno in G1; exact G1); apply (dir_table_form L0 L d i m (fun i0 => mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5)) (fun i0 => mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5))); lazy beta; exact (sim_mmap L0 L HLE d i m HM Gb) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; assert (Gb : mprotect_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (relim L m) = false) by (unfold alloc_budget_refused_b in G1; rewrite Hno in G1; exact G1); apply (dir_table_form L0 L d i m (fun i0 => mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2)) (fun i0 => mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2))); lazy beta; exact (sim_mprotect L0 L HLE d i m HM Gb) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_233 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_242 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_260 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_261 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_278 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_435 L0 L d i m HM) |].
destruct Hin as [<-|Hin]; [cbn [sa_spec sa_no] in Hno |- *; exact (sim_arm_439 L0 L d i m HM) |].
destruct Hin.
Qed.
Theorem syscall_spec_dir : forall (d : bool) i m, MOK L0 m ->
alloc_budget_refused_b i (relim L m) = false -> (d = false -> MV_OK m) ->
DIR L0 L d i m syscall_spec syscall_spec.
Proof. exact (dispatch_dir spec_table spec_table_ok). Qed.
End b.
Section e.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable L0 L : Z.
Hypothesis HLE : L <= L0.
Definition MOKc (c : config) : Prop := MOK L0 (cfg_model c).
Ltac halt_tac H := first [ exact H | rewrite relim_halted; exact H | cbn [cfg_model cfg_ms]; rewrite relim_halted; exact H ].
Ltac kill_tac H := first [ exact H | rewrite relim_killed; exact H | cbn [cfg_model cfg_ms]; rewrite relim_killed; exact H ].
Lemma refusal_b_relim : forall i m r, refusal_b i (relim L m) r = refusal_b i m r.
Proof. intros. reflexivity. Qed.
Lemma spurious_relim_up : forall i m eff, MOK L0 m -> alloc_budget_refused_b i (relim L m) = false -> MV_OK m ->
spurious_refusal_cfg cfg i m eff -> spurious_refusal_cfg cfg i (relim L m) eff.
Proof.
intros i m eff HM G MV (Hoff & Hr & (eff' & m' & evs' & Hs & Hnr)). split; [exact Hoff|]. split; [rewrite refusal_b_relim; exact Hr|].
destruct (syscall_spec_dir L0 L HLE false i m HM G (fun _ => MV) _ Hs) as ([e0 m0 ev0|] & Hs' & R); cbn in R; [|contradiction].
destruct R as (-> & -> & -> & _). exists eff', (relim L m'), evs'. split; [exact Hs' | rewrite refusal_b_relim; exact Hnr].
Qed.
Lemma spurious_relim_down : forall i m eff, MOK L0 m -> alloc_budget_refused_b i (relim L m) = false ->
spurious_refusal_cfg cfg i (relim L m) eff -> spurious_refusal_cfg cfg i m eff.
Proof.
intros i m eff HM G (Hoff & Hr & (eff' & m' & evs' & Hs & Hnr)). split; [exact Hoff|]. split; [rewrite <- (refusal_b_relim i m); exact Hr|].
destruct (syscall_spec_dir L0 L HLE true i m HM G ltac:(discriminate) _ Hs) as ([e0 m0 ev0|] & Hs' & R); cbn in R; [|contradiction].
destruct R as (<- & -> & <- & _). exists eff', m0, evs'. split; [exact Hs' | rewrite <- (refusal_b_relim i m); exact Hnr].
Qed.
Lemma not_refused_mark : forall ms m x8,
~ budget_refused_at segs (mkCfg ms (relim L m)) -> m_halted m = None -> ms_svc_pending ms = Some x8 ->
alloc_budget_refused_b (sys_input segs ms x8) (relim L m) = false.
Proof.
intros ms m x8 NB Hh Hp. destruct (alloc_budget_refused_b (sys_input segs ms x8) (relim L m)) eqn:E; [|reflexivity].
exfalso. apply NB. split; [exact Hh|]. right. exists x8. split; [exact Hp|]. left. exact E.
Qed.
Lemma step_up : forall ms m evs st,
MOK L0 m -> MV_OK m -> ~ budget_refused_at segs (mkCfg ms (relim L m)) ->
sstep_cfg segs cfg (mkCfg ms (relim L m)) evs st ->
match st with
| SNext c' => exists ms' m0, sstep_cfg segs cfg (mkCfg ms m) evs (SNext (mkCfg ms' m0)) /\ c' = mkCfg ms' (relim L m0) /\ MOK L0 m0
| SError => sstep_cfg segs cfg (mkCfg ms m) evs SError
end.
Proof.
intros ms m evs st HM MV NB Hs.
remember (mkCfg ms (relim L m)) as c eqn:Ec.
destruct Hs as [ms0 mm ms' mm' Hh Hp Ha | ms0 mm Hh Hp Ha | ms0 mm Hh Hp Ha | ms0 mm x8 eff mm' mm'' evs0 Hh Hp Hsp Hnsp Hh' Hmat
| ms0 mm x8 eff mm' evs0 Hh Hp Hsp Hnsp Hh' Hmat | ms0 mm x8 eff mm' evs0 code Hh Hp Hsp Hh' Hk | ms0 mm x8 eff mm' evs0 sig Hh Hp Hsp Hk | ms0 mm x8 Hh Hp Hsp];
injection Ec as -> ->; rewrite relim_halted in Hh.
-
unfold mi_account_step in Ha.
destruct (step_accesses segs ms) as [report| |] eqn:Est; [|discriminate|discriminate].
destruct (materialize_model_accesses (relim L m) (@accessed_ranges _ report)) as [m1|] eqn:Emat; [|discriminate].
injection Ha as <- <-.
assert (HLE' : L <= vm_limit (m_vmmaps m)) by (unfold MOK in HM; rewrite HM; exact HLE).
destruct (materialize_relim_up L m _ _ HLE' Emat) as (m0 & Emat0 & ->).
exists (@access_value _ report), m0. split; [|split; [reflexivity| unfold MOK; rewrite (materialize_limit _ _ _ Emat0); exact HM]].
apply sstep_cfg_instr; [exact Hh | exact Hp |]. unfold mi_account_step. rewrite Est, Emat0. reflexivity.
-
unfold mi_account_step in Ha.
destruct (step_accesses segs ms) as [report| |] eqn:Est; [|apply sstep_cfg_instr_fault; [exact Hh | exact Hp | unfold mi_account_step; rewrite Est; reflexivity]|discriminate].
destruct (materialize_model_accesses (relim L m) (@accessed_ranges _ report)) as [m1|] eqn:Emat; [discriminate|].
exfalso. apply NB. split; [exact Hh|]. left. split; [exact Hp|]. exists report. split; [exact Est | exact Emat].
-
unfold mi_account_step in Ha.
destruct (step_accesses segs ms) as [report| |] eqn:Est; [|discriminate|].
+ destruct (materialize_model_accesses (relim L m) (@accessed_ranges _ report)); discriminate.
+ apply sstep_cfg_instr_unmodeled; [exact Hh | exact Hp | unfold mi_account_step; rewrite Est; reflexivity].
-
destruct (syscall_spec_dir L0 L HLE true _ m HM (not_refused_mark _ _ _ NB Hh Hp) ltac:(discriminate) _ Hsp) as ([e0 m0 ev0|] & Hsp0 & R); cbn in R; [|contradiction].
destruct R as (<- & -> & <- & HM0).
rewrite relim_halted in Hh'.
assert (HLE' : L <= vm_limit (m_vmmaps m0)) by (unfold MOK in HM0; rewrite HM0; exact HLE).
destruct (materialize_relim_up L m0 _ _ HLE' Hmat) as (m0' & Hmat0 & ->).
exists (advance_past_svc (apply_effect ms eff)), m0'. split; [|split; [reflexivity | unfold MOK; rewrite (materialize_limit _ _ _ Hmat0); exact HM0]].
eapply sstep_cfg_syscall; [exact Hh | exact Hp | exact Hsp0 | | exact Hh' | exact Hmat0].
intros SP. apply Hnsp. apply spurious_relim_up; [exact HM | apply (not_refused_mark _ _ _ NB Hh Hp) | exact MV | exact SP].
-
exfalso. apply NB. split; [exact Hh|]. right. exists x8. split; [exact Hp|]. right.
exists eff, mm', evs0. split; [exact Hsp | split; [exact Hh' | exact Hmat]].
-
destruct (syscall_spec_dir L0 L HLE true _ m HM (not_refused_mark _ _ _ NB Hh Hp) ltac:(discriminate) _ Hsp) as ([e0 m0 ev0|] & Hsp0 & R); cbn in R; [|contradiction].
destruct R as (<- & -> & <- & HM0).
rewrite relim_halted in Hh'. rewrite relim_killed in Hk. rewrite relim_fs.
exists ms, m0. split; [|split; [reflexivity | exact HM0]].
eapply sstep_cfg_exit; [exact Hh | exact Hp | exact Hsp0 | exact Hh' | exact Hk].
-
destruct (syscall_spec_dir L0 L HLE true _ m HM (not_refused_mark _ _ _ NB Hh Hp) ltac:(discriminate) _ Hsp) as ([e0 m0 ev0|] & Hsp0 & R); cbn in R; [|contradiction].
destruct R as (<- & -> & <- & HM0).
rewrite relim_killed in Hk. rewrite relim_fs.
exists ms, m0. split; [|split; [reflexivity | exact HM0]].
eapply sstep_cfg_killed; [exact Hh | exact Hp | exact Hsp0 | exact Hk].
-
destruct (syscall_spec_dir L0 L HLE true _ m HM (not_refused_mark _ _ _ NB Hh Hp) ltac:(discriminate) _ Hsp) as ([|] & Hsp0 & R); cbn in R; [contradiction|].
eapply sstep_cfg_syscall_unmodeled; [exact Hh | exact Hp | exact Hsp0].
Qed.
Lemma step_down : forall ms m evs st,
MOK L0 m -> MV_OK m -> ~ budget_refused_at segs (mkCfg ms (relim L m)) ->
sstep_cfg segs cfg (mkCfg ms m) evs st ->
exists evs' st', sstep_cfg segs cfg (mkCfg ms (relim L m)) evs' st'.
Proof.
intros ms m evs st HM MV NB Hs.
remember (mkCfg ms m) as c eqn:Ec.
destruct Hs as [ms0 mm ms' mm' Hh Hp Ha | ms0 mm Hh Hp Ha | ms0 mm Hh Hp Ha | ms0 mm x8 eff mm' mm'' evs0 Hh Hp Hsp Hnsp Hh' Hmat
| ms0 mm x8 eff mm' evs0 Hh Hp Hsp Hnsp Hh' Hmat | ms0 mm x8 eff mm' evs0 code Hh Hp Hsp Hh' Hk | ms0 mm x8 eff mm' evs0 sig Hh Hp Hsp Hk | ms0 mm x8 Hh Hp Hsp];
injection Ec as -> ->.
-
unfold mi_account_step in Ha.
destruct (step_accesses segs ms) as [report| |] eqn:Est; [|discriminate|discriminate].
destruct (materialize_model_accesses m (@accessed_ranges _ report)) as [m0|] eqn:Emat; [|discriminate].
destruct (materialize_model_accesses (relim L m) (@accessed_ranges _ report)) as [m1|] eqn:Emat1.
+ eexists [], _. apply sstep_cfg_instr; [halt_tac Hh | exact Hp |]. unfold mi_account_step. rewrite Est, Emat1. reflexivity.
+ exfalso. apply NB. split; [halt_tac Hh|]. left. split; [exact Hp|]. exists report. split; [exact Est | exact Emat1].
-
unfold mi_account_step in Ha.
destruct (step_accesses segs ms) as [report| |] eqn:Est; [|  |discriminate].
+ destruct (materialize_model_accesses m (@accessed_ranges _ report)) as [m0|] eqn:Emat; [discriminate|].
destruct (materialize_model_accesses (relim L m) (@accessed_ranges _ report)) as [m1|] eqn:Emat1.
* eexists [], _. apply sstep_cfg_instr; [halt_tac Hh | exact Hp |]. unfold mi_account_step. rewrite Est, Emat1. reflexivity.
* exfalso. apply NB. split; [halt_tac Hh|]. left. split; [exact Hp|]. exists report. split; [exact Est | exact Emat1].
+ eexists [], SError. apply sstep_cfg_instr_fault; [halt_tac Hh | exact Hp | unfold mi_account_step; rewrite Est; reflexivity].
-
unfold mi_account_step in Ha.
destruct (step_accesses segs ms) as [report| |] eqn:Est; [destruct (materialize_model_accesses m (@accessed_ranges _ report)); discriminate|discriminate|].
eexists [], SError. apply sstep_cfg_instr_unmodeled; [halt_tac Hh | exact Hp | unfold mi_account_step; rewrite Est; reflexivity].
-
pose proof (not_refused_mark _ _ _ NB Hh Hp) as G.
destruct (syscall_spec_dir L0 L HLE false _ m HM G (fun _ => MV) _ Hsp) as ([e0 m0 ev0|] & Hsp0 & R); cbn in R; [|contradiction].
destruct R as (-> & -> & -> & HM0).
destruct (materialize_model_accesses (relim L mm') (syscall_effect_accesses eff)) as [m1|] eqn:Emat1.
+ eexists evs0, _. eapply sstep_cfg_syscall; [halt_tac Hh | exact Hp | exact Hsp0 | | halt_tac Hh' | exact Emat1].
intros SP. apply Hnsp. exact (spurious_relim_down _ _ _ HM G SP).
+ exfalso. apply NB. split; [halt_tac Hh|]. right. exists x8. split; [exact Hp|]. right.
exists eff, (relim L mm'), evs0. split; [exact Hsp0 | split; [halt_tac Hh' | exact Emat1]].
-
pose proof (not_refused_mark _ _ _ NB Hh Hp) as G.
destruct (syscall_spec_dir L0 L HLE false _ m HM G (fun _ => MV) _ Hsp) as ([e0 m0 ev0|] & Hsp0 & R); cbn in R; [|contradiction].
destruct R as (-> & -> & -> & HM0).
destruct (materialize_model_accesses (relim L mm') (syscall_effect_accesses eff)) as [m1|] eqn:Emat1.
+ assert (HLE' : L <= vm_limit (m_vmmaps mm')) by (unfold MOK in HM0; rewrite HM0; exact HLE).
destruct (materialize_relim_up L mm' _ _ HLE' Emat1) as (m0' & Hmat0 & _). rewrite Hmat0 in Hmat. discriminate Hmat.
+ exfalso. apply NB. split; [halt_tac Hh|]. right. exists x8. split; [exact Hp|]. right.
exists eff, (relim L mm'), evs0. split; [exact Hsp0 | split; [halt_tac Hh' | exact Emat1]].
-
pose proof (not_refused_mark _ _ _ NB Hh Hp) as G.
destruct (syscall_spec_dir L0 L HLE false _ m HM G (fun _ => MV) _ Hsp) as ([e0 m0 ev0|] & Hsp0 & R); cbn in R; [|contradiction].
destruct R as (-> & -> & -> & HM0).
eexists _, _. eapply sstep_cfg_exit; [halt_tac Hh | exact Hp | exact Hsp0 | halt_tac Hh' | kill_tac Hk].
-
pose proof (not_refused_mark _ _ _ NB Hh Hp) as G.
destruct (syscall_spec_dir L0 L HLE false _ m HM G (fun _ => MV) _ Hsp) as ([e0 m0 ev0|] & Hsp0 & R); cbn in R; [|contradiction].
destruct R as (-> & -> & -> & HM0).
eexists _, _. eapply sstep_cfg_killed; [halt_tac Hh | exact Hp | exact Hsp0 | kill_tac Hk].
-
pose proof (not_refused_mark _ _ _ NB Hh Hp) as G.
destruct (syscall_spec_dir L0 L HLE false _ m HM G (fun _ => MV) _ Hsp) as ([|] & Hsp0 & R); cbn in R; [contradiction|].
eexists [], SError. eapply sstep_cfg_syscall_unmodeled; [halt_tac Hh | exact Hp | exact Hsp0].
Qed.
Definition MREMAP_MOVE_OK (c : config) : Prop :=
forall tr c', star_cfg segs cfg c tr c' -> MV_OK (cfg_model c').
Lemma MREMAP_MOVE_OK_here : forall c, MREMAP_MOVE_OK c -> MV_OK (cfg_model c).
Proof. intros c H. apply (H []). apply star_cfg_refl. Qed.
Lemma MREMAP_MOVE_OK_step : forall c evs c', MREMAP_MOVE_OK c -> sstep_cfg segs cfg c evs (SNext c') -> MREMAP_MOVE_OK c'.
Proof. intros c evs c' H Hs tr c'' Hstar. apply (H (evs ++ tr)). eapply star_cfg_step; [exact Hs | exact Hstar]. Qed.
Lemma not_reaches_here : forall c, ~ reaches_budget_refused_cfg segs cfg c -> ~ budget_refused_at segs c.
Proof. intros c H B. apply H. exists [], c. split; [apply star_cfg_refl | exact B]. Qed.
Lemma not_reaches_step : forall c evs c', ~ reaches_budget_refused_cfg segs cfg c -> sstep_cfg segs cfg c evs (SNext c') ->
~ reaches_budget_refused_cfg segs cfg c'.
Proof.
intros c evs c' H Hs (tr & c'' & Hstar & B). apply H. exists (evs ++ tr), c''. split; [eapply star_cfg_step; [exact Hs | exact Hstar] | exact B].
Qed.
Theorem must_exit_relim_at : forall S c,
must_exit_in_at_cfg cfg segs S c ->
MOKc c -> ~ reaches_budget_refused_cfg segs cfg (relim_cfg L c) -> MREMAP_MOVE_OK c ->
must_exit_in_at_cfg cfg segs S (relim_cfg L c).
Proof.
intros S c Hme. induction Hme as [c code Hh Hin Hk | c Hnone Hprog Hnoerr Hnext IH]; intros HM NR MV.
- apply (must_exit_in_at_cfg_halted _ _ _ _ code); [cbn; halt_tac Hh | exact Hin | cbn; kill_tac Hk].
- destruct c as [ms m]. unfold MOKc in HM; cbn in HM. unfold relim_cfg; cbn.
pose proof (not_reaches_here _ NR) as NB. pose proof (MREMAP_MOVE_OK_here _ MV) as MVH. cbn in MVH.
apply must_exit_in_at_cfg_running.
+ cbn. rewrite relim_halted. exact Hnone.
+ destruct Hprog as (evs & st & Hs). exact (step_down ms m evs st HM MVH NB Hs).
+ intros evs Hs. exact (Hnoerr evs (step_up ms m evs SError HM MVH NB Hs)).
+ intros evs c' Hs. destruct (step_up ms m evs (SNext c') HM MVH NB Hs) as (ms' & m0 & Hs0 & -> & HM0).
apply (IH evs (mkCfg ms' m0) Hs0).
* exact HM0.
* exact (not_reaches_step _ _ _ NR Hs).
* exact (MREMAP_MOVE_OK_step _ _ _ MV Hs0).
Qed.
End e.
Theorem must_exit_relim :
forall segs cfg S (c : config) (L : Z),
L <= vm_limit (m_vmmaps (cfg_model c)) ->
~ reaches_budget_refused_cfg segs cfg (relim_cfg L c) ->
MREMAP_MOVE_OK segs cfg c ->
must_exit_in_at_cfg cfg segs S c ->
must_exit_in_at_cfg cfg segs S (relim_cfg L c).
Proof.
intros segs cfg S c L HLE NR MV Hme.
exact (must_exit_relim_at segs cfg (vm_limit (m_vmmaps (cfg_model c))) L HLE S c Hme eq_refl NR MV).
Qed.
Lemma init_config_relim : forall segs pc ph sp brk0 mbase rnd Lbig Lsmall inp,
init_config segs pc ph sp brk0 mbase rnd Lsmall inp = relim_cfg Lsmall (init_config segs pc ph sp brk0 mbase rnd Lbig inp).
Proof. intros. reflexivity. Qed.
Lemma init_config_limit : forall segs pc ph sp brk0 mbase rnd lim inp,
vm_limit (m_vmmaps (cfg_model (init_config segs pc ph sp brk0 mbase rnd lim inp))) = lim.
Proof. intros. reflexivity. Qed.
Corollary must_exit_in_scfg_relim : forall cfg S img (Lbig Lsmall : Z) en inp,
Lsmall <= Lbig ->
source_within_budget_scfg cfg Lsmall img en inp ->
(match img, en with mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
MREMAP_MOVE_OK segs cfg (init_config segs pc ph sp brk0 mbase rnd Lbig inp) end) ->
must_exit_in_scfg cfg S img Lbig en inp ->
must_exit_in_scfg cfg S img Lsmall en inp.
Proof.
intros cfg S [segs pc ph] Lbig Lsmall [sp brk0 mbase rnd] inp HLE NB MV Hme.
unfold must_exit_in_scfg in *. unfold source_within_budget_scfg, run_scfg_budget_refused in NB.
rewrite (init_config_relim segs pc ph sp brk0 mbase rnd Lbig Lsmall inp) in NB |- *.
apply must_exit_relim; [rewrite init_config_limit; exact HLE | exact NB | exact MV | exact Hme].
Qed.
Theorem MREMAP_MOVE_OK_of_WF : forall segs cfg c, WF (cfg_model c) -> MREMAP_MOVE_OK segs cfg c.
Proof. intros segs cfg c Hwf tr c' Hstar. apply MV_OK_wf. exact (star_cfg_WF segs cfg _ _ _ Hstar Hwf). Qed.
Theorem MREMAP_MOVE_OK_init : forall segs cfg pc ph sp brk0 mbase rnd lim inp,
MREMAP_MOVE_OK segs cfg (init_config segs pc ph sp brk0 mbase rnd lim inp).
Proof. intros. apply MREMAP_MOVE_OK_of_WF. apply init_config_WF. Qed.
Theorem must_exit_relim_closed :
forall segs cfg S (c : config) (L : Z),
L <= vm_limit (m_vmmaps (cfg_model c)) ->
WF (cfg_model c) ->
~ reaches_budget_refused_cfg segs cfg (relim_cfg L c) ->
must_exit_in_at_cfg cfg segs S c ->
must_exit_in_at_cfg cfg segs S (relim_cfg L c).
Proof. intros segs cfg S c L HLE Hwf NR Hme. exact (must_exit_relim segs cfg S c L HLE NR (MREMAP_MOVE_OK_of_WF segs cfg c Hwf) Hme). Qed.
Corollary must_exit_in_scfg_relim_closed : forall cfg S img (Lbig Lsmall : Z) en inp,
Lsmall <= Lbig ->
source_within_budget_scfg cfg Lsmall img en inp ->
must_exit_in_scfg cfg S img Lbig en inp ->
must_exit_in_scfg cfg S img Lsmall en inp.
Proof.
intros cfg S img Lbig Lsmall en inp HLE NB Hme.
apply (must_exit_in_scfg_relim cfg S img Lbig Lsmall en inp HLE NB); [|exact Hme].
destruct img, en. apply MREMAP_MOVE_OK_init.
Qed.
