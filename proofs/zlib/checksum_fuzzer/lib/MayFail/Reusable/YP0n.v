(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YP0n.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: handled unrestricted mmap and mprotect refusals and all fixed-mapping results; changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK16.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable.Z Require Import Placement.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable.R Require Import Place.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable.R Require Import Cfg.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Section f.
Context {fx : FPState}.
Definition pend_at (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte)
: machine_state :=
{| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
ms_mem := mem; ms_rom := rom |}.
Definition effmem (mem : word -> option byte) (eff : SyscallEffect) : word -> option byte :=
apply_writes (apply_copies mem
(apply_zeros (apply_unmaps mem (eff_unmaps eff)) (eff_zeros eff))
(eff_copies eff))
(eff_writes eff).
Lemma effmem_ret_only : forall mem r, effmem mem (mkEffect r [] []) = mem.
Proof. reflexivity. Qed.
Lemma effmem_zeros : forall mem r zs, effmem mem (mkEffect r [] zs) = apply_zeros mem zs.
Proof. reflexivity. Qed.
Lemma effmem_unmaps : forall mem r us,
effmem mem (mkEffectU r [] [] us [] []) = apply_unmaps mem us.
Proof. intros mem r us. unfold effmem. cbn [eff_unmaps eff_zeros eff_writes eff_copies apply_writes apply_copies].
destruct us; reflexivity. Qed.
Lemma effmem_write1 : forall mem r a bs,
effmem mem (mkEffect r [(a, bs)] []) = write_to_mem mem a bs.
Proof. reflexivity. Qed.
Lemma adv_pend : forall regs pc mem rom eff,
advance_past_svc (apply_effect (pend_at regs pc mem rom) eff)
= mkst (regupd regs 10 (eff_ret eff)) (v_addi pc 4) (effmem mem eff) rom.
Proof.
intros regs pc mem rom eff.
unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc, pend_at.
change (bv_eqb (10 : reg) 0) with false.
cbv beta iota zeta.
cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom ms_fregs ms_fcsr].
unfold mkst, regupd, effmem.
rewrite b_npc4. reflexivity.
Qed.
Lemma adv_pend_set : forall regs pc mem rom v,
advance_past_svc (set_gpr0 (pend_at regs pc mem rom) v)
= mkst (regupd regs 10 v) (v_addi pc 4) mem rom.
Proof. intros. unfold pend_at. apply adv_set. Qed.
Lemma pend_svc : forall regs pc mem rom,
ms_svc_pending (pend_at regs pc mem rom) = Some (getr regs 17).
Proof. reflexivity. Qed.
Lemma arg_reg_3 : Z_to_bv 5 (10 + Z.of_nat 3) = (13 : reg).
Proof. apply bv_eq. reflexivity. Qed.
Lemma arg_reg_4 : Z_to_bv 5 (10 + Z.of_nat 4) = (14 : reg).
Proof. apply bv_eq. reflexivity. Qed.
Lemma arg_reg_5 : Z_to_bv 5 (10 + Z.of_nat 5) = (15 : reg).
Proof. apply bv_eq. reflexivity. Qed.
Lemma pend_gpr0 : forall regs pc mem rom, ms_gpr (pend_at regs pc mem rom) 0 = getr regs 10.
Proof. intros. unfold ms_gpr. cbn [ms_regs pend_at]. rewrite arg_reg_0. reflexivity. Qed.
Lemma pend_gpr1 : forall regs pc mem rom, ms_gpr (pend_at regs pc mem rom) 1 = getr regs 11.
Proof. intros. unfold ms_gpr. cbn [ms_regs pend_at]. rewrite arg_reg_1. reflexivity. Qed.
Lemma pend_gpr2 : forall regs pc mem rom, ms_gpr (pend_at regs pc mem rom) 2 = getr regs 12.
Proof. intros. unfold ms_gpr. cbn [ms_regs pend_at]. rewrite arg_reg_2. reflexivity. Qed.
Lemma pend_gpr3 : forall regs pc mem rom, ms_gpr (pend_at regs pc mem rom) 3 = getr regs 13.
Proof. intros. unfold ms_gpr. cbn [ms_regs pend_at]. rewrite arg_reg_3. reflexivity. Qed.
Lemma pend_gpr4 : forall regs pc mem rom, ms_gpr (pend_at regs pc mem rom) 4 = getr regs 14.
Proof. intros. unfold ms_gpr. cbn [ms_regs pend_at]. rewrite arg_reg_4. reflexivity. Qed.
Lemma pend_gpr5 : forall regs pc mem rom, ms_gpr (pend_at regs pc mem rom) 5 = getr regs 15.
Proof. intros. unfold ms_gpr. cbn [ms_regs pend_at]. rewrite arg_reg_5. reflexivity. Qed.
Lemma si_sysno : forall segs regs pc mem rom,
in_sysno (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) = getr regs 17.
Proof. reflexivity. Qed.
Lemma si_arg0 : forall segs regs pc mem rom,
in_arg (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) 0 = getr regs 10.
Proof. intros. exact (pend_gpr0 regs pc mem rom). Qed.
Lemma si_arg1 : forall segs regs pc mem rom,
in_arg (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) 1 = getr regs 11.
Proof. intros. exact (pend_gpr1 regs pc mem rom). Qed.
Lemma si_arg2 : forall segs regs pc mem rom,
in_arg (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) 2 = getr regs 12.
Proof. intros. exact (pend_gpr2 regs pc mem rom). Qed.
Lemma si_arg3 : forall segs regs pc mem rom,
in_arg (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) 3 = getr regs 13.
Proof. intros. exact (pend_gpr3 regs pc mem rom). Qed.
Lemma si_arg4 : forall segs regs pc mem rom,
in_arg (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) 4 = getr regs 14.
Proof. intros. exact (pend_gpr4 regs pc mem rom). Qed.
Lemma si_arg5 : forall segs regs pc mem rom,
in_arg (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) 5 = getr regs 15.
Proof. intros. exact (pend_gpr5 regs pc mem rom). Qed.
Lemma si_mem : forall segs regs pc mem rom,
in_mem (sys_input segs (pend_at regs pc mem rom) (getr regs 17))
= ms_read_byte (pend_at regs pc mem rom).
Proof. reflexivity. Qed.
Lemma si_wmem : forall segs regs pc mem rom,
in_wmem (sys_input segs (pend_at regs pc mem rom) (getr regs 17))
= wview segs mem.
Proof. reflexivity. Qed.
Section g.
Variable segs : list Segment.
Lemma node_chk_cfg : forall ms model x8 (I : Type) (i0 : I)
(ef : I -> SyscallEffect) (md : I -> Model) (ev : I -> list event),
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
(forall i, check_syscall (sys_input segs ms x8) (ef i) model = CheckOk (md i) (ev i)) ->
(forall i, m_halted (md i) = None) ->
(forall i, m_vm_lazy (md i) = []) ->
(forall eff m' evs, check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
(exists i, eff = ef i /\ m' = md i /\ evs = ev i)
\/ (spurious_refusal_cfg ACFG (sys_input segs ms x8) model eff /\ m_halted m' = None)) ->
(forall i, ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model (ef i)) ->
node_ok segs (mkCfg ms model) I ev
(fun i => mkCfg (advance_past_svc (apply_effect ms (ef i))) (md i)).
Proof.
intros ms model x8 I i0 ef md ev Hh Hsvc Hok Hhl Hlz Hinv Hns. split.
- intro i. apply (sstep_cfg_syscall segs ACFG ms model x8 (ef i) (md i) (md i) (ev i) Hh Hsvc).
+ apply check_syscall_ok_iff. apply Hok.
+ apply Hns.
+ apply Hhl.
+ apply materialize_model_accesses_no_lazy. apply Hlz.
- intros e st Hss. inversion Hss; subst; try congruence.
+
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H4 : ~ spurious_refusal_cfg _ _ _ _,
H5 : materialize_model_accesses ?model' _ = Some ?model'' |- _ =>
assert (Hx : x = x8) by congruence; subst x;
apply check_syscall_ok_iff in H3;
destruct (Hinv eff model' evs0 H3) as [(i & -> & -> & ->) | [Hsp _]]; [| exfalso; exact (H4 Hsp)];
rewrite (materialize_model_accesses_no_lazy _ _ (Hlz i)) in H5;
injection H5 as <-;
exists i; split; reflexivity
end.
+
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H4 : ~ spurious_refusal_cfg _ _ _ _,
H5 : materialize_model_accesses ?model' _ = None |- _ =>
assert (Hx : x = x8) by congruence; subst x;
apply check_syscall_ok_iff in H3;
destruct (Hinv eff model' evs0 H3) as [(i & _ & Hm & _) | [Hsp _]]; [| exact (H4 Hsp)];
rewrite Hm, (materialize_model_accesses_no_lazy _ _ (Hlz i)) in H5; discriminate
end.
+
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_halted ?model' = Some ?code |- _ =>
assert (Hx : x = x8) by congruence; subst x;
apply check_syscall_ok_iff in H3;
destruct (Hinv eff model' evs0 H3) as [(i & _ & Hm & _) | [_ Hm]];
[rewrite Hm, (Hhl i) in H6 | rewrite Hm in H6]; discriminate
end.
+
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_killed ?model' = Some ?sig |- _ =>
assert (Hx : x = x8) by congruence; subst x;
apply check_syscall_ok_iff in H3;
destruct (Hinv eff model' evs0 H3) as [(i & _ & Hm & _) | [_ Hm]];
[rewrite Hm, (m_killed_of_m_halted_none _ (Hhl i)) in H6 | rewrite (m_killed_of_m_halted_none _ Hm) in H6]; discriminate
end.
+
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
assert (Hx : x = x8) by congruence; subst x;
apply (check_syscall_complete_unmodeled _ _ (ef i0)) in H3;
rewrite (Hok i0) in H3; discriminate
end.
Qed.
Lemma node_chk : forall ms model x8 (I : Type) (i0 : I)
(ef : I -> SyscallEffect) (md : I -> Model) (ev : I -> list event),
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
(forall i, check_syscall (sys_input segs ms x8) (ef i) model = CheckOk (md i) (ev i)) ->
(forall i, m_halted (md i) = None) ->
(forall i, m_vm_lazy (md i) = []) ->
(forall eff m' evs, check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
exists i, eff = ef i /\ m' = md i /\ evs = ev i) ->
(forall i, ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model (ef i)) ->
node_ok segs (mkCfg ms model) I ev
(fun i => mkCfg (advance_past_svc (apply_effect ms (ef i))) (md i)).
Proof.
intros ms model x8 I i0 ef md ev Hh Hsvc Hok Hhl Hlz Hinv Hns.
apply (node_chk_cfg ms model x8 I i0 ef md ev Hh Hsvc Hok Hhl Hlz); [|exact Hns].
intros eff m' evs Hk. left. exact (Hinv eff m' evs Hk).
Qed.
Lemma rz_silent : forall c (I : Type) (i0 : I) (nx : I -> config) T,
node_ok segs c I (fun _ => []) nx ->
(forall i, realizes segs (nx i) T) ->
realizes segs c T.
Proof.
intros c I i0 nx T Hnode Hc.
assert (HT0 : T []) by (eapply realizes_nonempty; apply (Hc i0)).
apply (rz_conseq segs c (t_alt (fun _ : I => t_emit [] T))).
- apply (rz_node segs c I (fun _ => []) nx (fun _ => T) i0 Hnode). exact Hc.
- intro tr. split.
+ intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
+ intro HT. exists i0. exact (proj2 (t_emit_nil_eq T HT0 tr) HT).
Qed.
Lemma rz_alt3 : forall c (IA IB IC : Type) (nx : IA + (IB + IC) -> config)
(A B C : TSet) (a0 : IA) (b0 : IB) (c0 : IC),
node_ok segs c (IA + (IB + IC)) (fun _ => []) nx ->
(forall i, realizes segs (nx (inl i)) A) ->
(forall i, realizes segs (nx (inr (inl i))) B) ->
(forall i, realizes segs (nx (inr (inr i))) C) ->
realizes segs c (t_alt2 A (t_alt2 B C)).
Proof.
intros c IA IB IC nx A B C a0 b0 c0 Hnode HA HB HC.
assert (HA0 : A []) by (eapply realizes_nonempty; apply (HA a0)).
assert (HB0 : B []) by (eapply realizes_nonempty; apply (HB b0)).
assert (HC0 : C []) by (eapply realizes_nonempty; apply (HC c0)).
pose (sh := fun i : IA + (IB + IC) =>
match i with inl _ => A | inr (inl _) => B | inr (inr _) => C end).
apply (rz_conseq segs c (t_alt (fun i => t_emit [] (sh i)))).
- apply (rz_node segs c (IA + (IB + IC)) (fun _ => []) nx sh (inl a0) Hnode).
intros [i | [i | i]]; cbn; [apply HA | apply HB | apply HC].
- intro tr. unfold t_alt2. split.
+ intros [[i | [i | i]] Hi]; cbn in Hi;
[ left; exact (proj1 (t_emit_nil_eq A HA0 tr) Hi)
| right; left; exact (proj1 (t_emit_nil_eq B HB0 tr) Hi)
| right; right; exact (proj1 (t_emit_nil_eq C HC0 tr) Hi) ].
+ intros [H | [H | H]];
[ exists (inl a0); exact (proj2 (t_emit_nil_eq A HA0 tr) H)
| exists (inr (inl b0)); exact (proj2 (t_emit_nil_eq B HB0 tr) H)
| exists (inr (inr c0)); exact (proj2 (t_emit_nil_eq C HC0 tr) H) ].
Qed.
Lemma rz_chk1 : forall regs pc mem rom model eff m' evs T,
m_halted model = None -> m_vm_lazy model = [] ->
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= CheckOk m' evs ->
m_halted m' = None -> m_vm_lazy m' = [] ->
(forall eff2 m2 evs2,
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff2 model
= CheckOk m2 evs2 -> eff2 = eff /\ m2 = m' /\ evs2 = evs) ->
realizes segs (mkCfg (mkst (regupd regs 10 (eff_ret eff)) (v_addi pc 4)
(effmem mem eff) rom) m') T ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) (t_emit evs T).
Proof.
intros regs pc mem rom model eff m' evs T Hh Hlz Hok Hh' Hlz' Huniq Hc.
eapply rz_emit1.
- apply (node_chk (pend_at regs pc mem rom) model (getr regs 17) unit tt
(fun _ => eff) (fun _ => m') (fun _ => evs) Hh eq_refl
(fun _ => Hok) (fun _ => Hh') (fun _ => Hlz')).
+ intros eff2 m2 evs2 H2. exists tt. apply Huniq. exact H2.
+ intros []. apply nonspurious_of_unique. intros eff2 m2 evs2 Hs2.
apply check_syscall_ok_iff in Hs2. apply Huniq in Hs2 as (-> & _ & _). reflexivity.
- cbn. rewrite adv_pend. exact Hc.
Qed.
Lemma rz_chk1_silent : forall regs pc mem rom model eff m' T,
m_halted model = None -> m_vm_lazy model = [] ->
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= CheckOk m' [] ->
m_halted m' = None -> m_vm_lazy m' = [] ->
(forall eff2 m2 evs2,
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff2 model
= CheckOk m2 evs2 -> eff2 = eff /\ m2 = m' /\ evs2 = []) ->
realizes segs (mkCfg (mkst (regupd regs 10 (eff_ret eff)) (v_addi pc 4)
(effmem mem eff) rom) m') T ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model eff m' T Hh Hlz Hok Hh' Hlz' Huniq Hc.
eapply rz_conseq.
- eapply rz_chk1; eassumption.
- apply t_emit_nil_eq. eapply realizes_nonempty. exact Hc.
Qed.
Lemma check_ret_only_uniq : forall eff2 r m1 evs1 m2 evs2,
check_ret_only eff2 r m1 evs1 = CheckOk m2 evs2 ->
eff2 = mkEffect r [] [] /\ m2 = m1 /\ evs2 = evs1.
Proof. intros. apply check_ret_only_ok_iff. assumption. Qed.
Lemma check_ret_only_self : forall r m evs,
check_ret_only (mkEffect r [] []) r m evs = CheckOk m evs.
Proof. intros. apply check_ret_only_ok_iff. auto. Qed.
Lemma rz_ret_only : forall regs pc mem rom model r m' evs T,
m_halted model = None -> m_vm_lazy model = [] ->
(forall eff, check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= check_ret_only eff r m' evs) ->
m_halted m' = None -> m_vm_lazy m' = [] ->
realizes segs (mkCfg (mkst (regupd regs 10 r) (v_addi pc 4) mem rom) m') T ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) (t_emit evs T).
Proof.
intros regs pc mem rom model r m' evs T Hh Hlz Hchk Hh' Hlz' Hc.
apply (rz_chk1 regs pc mem rom model (mkEffect r [] []) m' evs T Hh Hlz).
- rewrite Hchk. apply check_ret_only_self.
- exact Hh'.
- exact Hlz'.
- intros eff2 m2 evs2 H2. rewrite Hchk in H2. apply check_ret_only_uniq. exact H2.
- cbn [eff_ret]. rewrite effmem_ret_only. exact Hc.
Qed.
Lemma rz_ret_only_silent : forall regs pc mem rom model r m' T,
m_halted model = None -> m_vm_lazy model = [] ->
(forall eff, check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= check_ret_only eff r m' []) ->
m_halted m' = None -> m_vm_lazy m' = [] ->
realizes segs (mkCfg (mkst (regupd regs 10 r) (v_addi pc 4) mem rom) m') T ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model r m' T Hh Hlz Hchk Hh' Hlz' Hc.
eapply rz_conseq.
- eapply rz_ret_only; eassumption.
- apply t_emit_nil_eq. eapply realizes_nonempty. exact Hc.
Qed.
Lemma effmem_copyins_ret_only : forall mem reads r,
effmem mem (with_copyins reads (mkEffect r [] [])) = mem.
Proof. reflexivity. Qed.
Lemma rz_ret_only_copyins : forall regs pc mem rom model reads r m' evs T,
m_halted model = None -> m_vm_lazy model = [] ->
(forall eff, check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= check_ret_only_copyins reads eff r m' evs) ->
m_halted m' = None -> m_vm_lazy m' = [] ->
realizes segs (mkCfg (mkst (regupd regs 10 r) (v_addi pc 4) mem rom) m') T ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) (t_emit evs T).
Proof.
intros regs pc mem rom model reads r m' evs T Hh Hlz Hchk Hh' Hlz' Hc.
apply (rz_chk1 regs pc mem rom model (with_copyins reads (mkEffect r [] [])) m' evs T Hh Hlz).
- rewrite Hchk. apply check_ret_only_copyins_refl.
- exact Hh'.
- exact Hlz'.
- intros eff2 m2 evs2 H2. rewrite Hchk in H2. apply check_ret_only_copyins_ok_iff. exact H2.
- cbn [eff_ret with_copyins]. rewrite effmem_copyins_ret_only. exact Hc.
Qed.
Lemma rz_ret_only_copyins_silent : forall regs pc mem rom model reads r m' T,
m_halted model = None -> m_vm_lazy model = [] ->
(forall eff, check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= check_ret_only_copyins reads eff r m' []) ->
m_halted m' = None -> m_vm_lazy m' = [] ->
realizes segs (mkCfg (mkst (regupd regs 10 r) (v_addi pc 4) mem rom) m') T ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model reads r m' T Hh Hlz Hchk Hh' Hlz' Hc.
eapply rz_conseq.
- eapply rz_ret_only_copyins; eassumption.
- apply t_emit_nil_eq. eapply realizes_nonempty. exact Hc.
Qed.
Lemma rz_exit_at : forall regs pc mem rom model,
m_halted model = None -> m_vm_lazy model = [] ->
is_exit_no (getr regs 17) ->
realizes segs (mkCfg (pend_at regs pc mem rom) model)
(t_exit (bv_and (getr regs 10) (Z_to_bv 64 255)) (m_fs model)).
Proof.
intros regs pc mem rom model Hh Hlz Hx8.
rewrite <- (pend_gpr0 regs pc mem rom).
apply (rz_exit segs (pend_at regs pc mem rom) model (getr regs 17) Hh eq_refl Hx8).
Qed.
Lemma rz_exit_small : forall regs pc mem rom model (c : word),
m_halted model = None -> m_vm_lazy model = [] ->
is_exit_no (getr regs 17) ->
getr regs 10 = c -> (bv_unsigned c < 256)%Z ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) (t_exit c (m_fs model)).
Proof.
intros regs pc mem rom model c Hh Hlz Hx8 Hc Hsmall.
rewrite <- (land_255_small c Hsmall), <- Hc. apply rz_exit_at; assumption.
Qed.
Lemma rz_write : forall regs pc mem rom model fd ch buf T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 64%Z ->
fdchan fd ch model -> fd32 fd = fd ->
getr regs 10 = fd ->
ms_read_bytes (pend_at regs pc mem rom) (getr regs 11) (getr regs 12) = Some buf ->
buf_modeled buf -> (1 <= length buf)%nat ->
(forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
realizes segs (mkCfg (mkst (regupd regs 10 (len_word (firstn n buf))) (v_addi pc 4) mem rom)
model) T) ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) (t_write_ch ch buf T).
Proof.
intros regs pc mem rom model fd ch buf T Hh Hlz Hno Hfdc H32 Hfd Hr Hbm Hnb Hc.
apply (rz_write_ch segs (pend_at regs pc mem rom) model fd ch (getr regs 17) buf T
Hh Hlz Hfdc H32 eq_refl Hno).
- rewrite pend_gpr0. exact Hfd.
- rewrite pend_gpr1, pend_gpr2. exact Hr.
- exact Hbm.
- exact Hnb.
- intros n Hn1 Hn2. rewrite adv_pend_set. apply Hc; assumption.
Qed.
Lemma chk96 : forall regs pc mem rom model eff,
bv_unsigned (getr regs 17) = 96%Z ->
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= check_set_tid_address eff model.
Proof.
intros regs pc mem rom model eff Hno.
rewrite (DispatchCompute.check_syscall_set_tid_address _ eff model) by (rewrite si_sysno; exact Hno).
rewrite ?si_arg0, ?si_arg1, ?si_arg2, ?si_arg3, ?si_arg4, ?si_arg5. reflexivity.
Qed.
Lemma PID_MAX_ENVELOPE_val : PID_MAX_ENVELOPE = 4194304%Z.
Proof. reflexivity. Qed.
Lemma rz_set_tid_first : forall regs pc mem rom model T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 96%Z ->
m_tid model = None ->
(forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
realizes segs (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom)
(with_tid tid model)) T) ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model T Hh Hlz Hno Htid Hc.
pose (I := {tid : word | (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z}).
assert (H1 : (0 < bv_unsigned (Z_to_bv 64 1) < PID_MAX_ENVELOPE)%Z).
{ rewrite PID_MAX_ENVELOPE_val. change (bv_unsigned (Z_to_bv 64 1)) with 1%Z. lia. }
eapply (rz_silent (mkCfg (pend_at regs pc mem rom) model) I (exist _ (Z_to_bv 64 1) H1)).
- apply (node_chk (pend_at regs pc mem rom) model (getr regs 17) I (exist _ (Z_to_bv 64 1) H1)
(fun i => mkEffect (proj1_sig i) [] [])
(fun i => with_tid (proj1_sig i) model)
(fun _ => []) Hh eq_refl).
+ intros [tid Ht]. cbn [proj1_sig]. rewrite chk96 by exact Hno.
unfold check_set_tid_address. rewrite Htid.
rewrite (proj2 (Z.ltb_lt _ _) (proj1 Ht)), (proj2 (Z.ltb_lt _ _) (proj2 Ht)).
reflexivity.
+ intros [tid Ht]. cbn. exact Hh.
+ intros [tid Ht]. cbn. exact Hlz.
+ intros [r ws zs us cs ci] m' evs Hk. rewrite chk96 in Hk by exact Hno.
unfold check_set_tid_address in Hk. rewrite Htid in Hk.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct ((0 <? bv_unsigned r)%Z) eqn:E1; [|discriminate].
destruct ((bv_unsigned r <? PID_MAX_ENVELOPE)%Z) eqn:E2; [|discriminate].
cbn [andb] in Hk. inversion Hk; subst.
apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
exists (exist _ r (conj E1 E2)). cbn [proj1_sig]. auto.
+ exact (fun _ => acfg_nonspurious_no _ _ _ _ _ _ Hno eq_refl).
- intros [tid Ht]. cbn [proj1_sig]. rewrite adv_pend. cbn [eff_ret].
rewrite effmem_ret_only. apply Hc. exact Ht.
Qed.
Lemma rz_set_tid_again : forall regs pc mem rom model t T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 96%Z ->
m_tid model = Some t ->
realizes segs (mkCfg (mkst (regupd regs 10 t) (v_addi pc 4) mem rom) model) T ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model t T Hh Hlz Hno Htid Hc.
apply (rz_chk1_silent regs pc mem rom model (mkEffect t [] []) model T Hh Hlz).
- rewrite chk96 by exact Hno. unfold check_set_tid_address. rewrite Htid, bv_eqb_refl.
reflexivity.
- exact Hh.
- exact Hlz.
- intros [r ws zs us cs ci] m2 evs2 Hk. rewrite chk96 in Hk by exact Hno.
unfold check_set_tid_address in Hk. rewrite Htid in Hk.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (bv_eqb r t) eqn:E; [|discriminate]. apply bv_eqb_eq in E. subst r.
inversion Hk; subst. auto.
- cbn [eff_ret]. rewrite effmem_ret_only. exact Hc.
Qed.
Lemma chk57 : forall regs pc mem rom model eff,
bv_unsigned (getr regs 17) = 57%Z ->
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= check_close (fd32 (getr regs 10)) eff model.
Proof.
intros regs pc mem rom model eff Hno.
rewrite (DispatchCompute.check_syscall_close _ eff model) by (rewrite si_sysno; exact Hno).
rewrite ?si_arg0, ?si_arg1, ?si_arg2, ?si_arg3, ?si_arg4, ?si_arg5. reflexivity.
Qed.
Lemma rz_close : forall regs pc mem rom model fd e T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 57%Z ->
getr regs 10 = fd -> fd32 fd = fd ->
fd_lookup (m_fds model) fd = Some e ->
realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem rom)
(with_fds (fd_remove (m_fds model) fd) model)) T ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model fd e T Hh Hlz Hno Hfd H32 Hlk Hc.
apply (rz_ret_only_silent regs pc mem rom model (Z_to_bv 64 0)
(with_fds (fd_remove (m_fds model) fd) model) T Hh Hlz).
- intro eff. rewrite chk57 by exact Hno. rewrite Hfd, H32. unfold check_close.
rewrite Hlk. reflexivity.
- exact Hh.
- exact Hlz.
- exact Hc.
Qed.
Lemma rz_close_badf : forall regs pc mem rom model fd T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 57%Z ->
getr regs 10 = fd -> fd32 fd = fd ->
fd_lookup (m_fds model) fd = None ->
realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret EBADF)) (v_addi pc 4) mem rom) model) T ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model fd T Hh Hlz Hno Hfd H32 Hlk Hc.
apply (rz_ret_only_silent regs pc mem rom model (errno_ret EBADF) model T Hh Hlz).
- intro eff. rewrite chk57 by exact Hno. rewrite Hfd, H32. unfold check_close.
rewrite Hlk. reflexivity.
- exact Hh.
- exact Hlz.
- exact Hc.
Qed.
Lemma chk29 : forall regs pc mem rom model eff,
bv_unsigned (getr regs 17) = 29%Z ->
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= check_ioctl (fd32 (getr regs 10)) (cmd32 (getr regs 11)) eff model.
Proof.
intros regs pc mem rom model eff Hno.
rewrite (DispatchCompute.check_syscall_ioctl _ eff model) by (rewrite si_sysno; exact Hno).
rewrite ?si_arg0, ?si_arg1, ?si_arg2, ?si_arg3, ?si_arg4, ?si_arg5. reflexivity.
Qed.
Lemma cmd32_small : forall w : word, (bv_unsigned w < 2 ^ 32)%Z -> cmd32 w = w.
Proof. intros w H. unfold cmd32. apply fd32_id. exact H. Qed.
Lemma rz_ioctl_winsz : forall regs pc mem rom model fd e T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 29%Z ->
getr regs 10 = fd -> fd32 fd = fd ->
fd_lookup (m_fds model) fd = Some e ->
(forall rd wr : bool, e <> FdUrandom) ->
cmd32 (getr regs 11) = TIOCGWINSZ ->
realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOTTY)) (v_addi pc 4) mem rom) model) T ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model fd e T Hh Hlz Hno Hfd H32 Hlk Hnd Hcmd Hc.
apply (rz_ret_only_silent regs pc mem rom model (errno_ret ENOTTY) model T Hh Hlz).
- intro eff. rewrite chk29 by exact Hno. rewrite Hfd, H32, Hcmd. unfold check_ioctl.
rewrite Hlk. change (tty_only_request TIOCGWINSZ) with true. destruct e; try reflexivity. exfalso; eapply (Hnd true true); reflexivity.
- exact Hh.
- exact Hlz.
- exact Hc.
Qed.
Lemma chk56 : forall regs pc mem rom model eff,
bv_unsigned (getr regs 17) = 56%Z ->
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= check_openat (sys_input segs (pend_at regs pc mem rom) (getr regs 17))
(fd32 (getr regs 10)) (getr regs 11) (getr regs 12) eff model.
Proof.
intros regs pc mem rom model eff Hno.
rewrite (DispatchCompute.check_syscall_openat _ eff model) by (rewrite si_sysno; exact Hno).
rewrite ?si_arg0, ?si_arg1, ?si_arg2, ?si_arg3, ?si_arg4, ?si_arg5. reflexivity.
Qed.
Lemma fd32_AT_FDCWD : fd32 AT_FDCWD = AT_FDCWD32.
Proof. reflexivity. Qed.
Lemma fd32_alloc_fd : forall fds, fd32 (alloc_fd fds) = alloc_fd fds.
Proof. intro fds. apply fd32_id. pose proof (alloc_fd_le fds). lia. Qed.
Lemma alloc_fd_std3 : forall e0 e1 e2,
alloc_fd [(Z_to_bv 64 0, e0); (Z_to_bv 64 1, e1); (Z_to_bv 64 2, e2)] = Z_to_bv 64 3.
Proof. intros. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma fd_lookup_std3 : forall e0 e1 e2,
fd_lookup [(Z_to_bv 64 0, e0); (Z_to_bv 64 1, e1); (Z_to_bv 64 2, e2)] (Z_to_bv 64 3) = None.
Proof. reflexivity. Qed.
Lemma rz_openat_toolong : forall regs pc mem rom model T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 56%Z ->
modeled_open_flags (getr regs 12) = true ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrTooLong ->
realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret ENAMETOOLONG)) (v_addi pc 4) mem rom)
model) T ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model T Hh Hlz Hno Hfl Hp Hc.
apply (rz_ret_only_copyins_silent regs pc mem rom model (open_copyins (pend_at regs pc mem rom))
(errno_ret ENAMETOOLONG) model T Hh Hlz).
- intro eff. apply (openat_toolong_check segs (pend_at regs pc mem rom) (getr regs 17) model Hno).
+ rewrite pend_gpr2. exact Hfl.
+ rewrite pend_gpr1. exact Hp.
- exact Hh.
- exact Hlz.
- exact Hc.
Qed.
Lemma rz_openat_fault : forall regs pc mem rom model T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 56%Z ->
modeled_open_flags (getr regs 12) = true ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrFault ->
realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret EFAULT)) (v_addi pc 4) mem rom)
model) T ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model T Hh Hlz Hno Hfl Hp Hc.
apply (rz_ret_only_copyins_silent regs pc mem rom model (open_copyins (pend_at regs pc mem rom))
(errno_ret EFAULT) model T Hh Hlz).
- intro eff. rewrite chk56 by exact Hno. unfold check_openat.
rewrite Hfl. cbn [negb]. unfold Prelude.check_copyins_after, Open.check_openat_body.
rewrite si_mem, Hp. unfold check_ret_only_copyins, check_copyins, open_copyins.
rewrite pend_gpr1. cbn [ms_read_byte pend_at ms_mem ms_rom].
destruct (check_ret_only (clear_copyins eff) (errno_ret EFAULT) model []) eqn:Hq;
[reflexivity| |reflexivity].
destruct (access_ranges_eqb _ _); reflexivity.
- exact Hh.
- exact Hlz.
- exact Hc.
Qed.
Lemma rz_openat_empty : forall regs pc mem rom model T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 56%Z ->
modeled_open_flags (getr regs 12) = true ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk [] ->
realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOENT)) (v_addi pc 4) mem rom)
model) T ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model T Hh Hlz Hno Hfl Hp Hc.
apply (rz_ret_only_copyins_silent regs pc mem rom model (open_copyins (pend_at regs pc mem rom))
(errno_ret ENOENT) model T Hh Hlz).
- intro eff. rewrite chk56 by exact Hno. unfold check_openat.
rewrite Hfl. cbn [negb]. unfold Prelude.check_copyins_after, Open.check_openat_body.
rewrite si_mem, Hp. change (path_eqb [] []) with true. cbv beta iota.
unfold check_ret_only_copyins, check_copyins, open_copyins.
rewrite pend_gpr1. cbn [ms_read_byte pend_at ms_mem ms_rom].
destruct (check_ret_only (clear_copyins eff) (errno_ret ENOENT) model []) eqn:Hq;
[reflexivity| |reflexivity].
destruct (access_ranges_eqb _ _); reflexivity.
- exact Hh.
- exact Hlz.
- exact Hc.
Qed.
Lemma rz_openat_absent : forall regs pc mem rom model p T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 56%Z ->
getr regs 10 = AT_FDCWD ->
Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk p ->
p <> [] -> openat_plain_name p = true ->
fs_lookup (m_fs model) p = None ->
realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOENT)) (v_addi pc 4) mem rom)
model) T ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model p T Hh Hlz Hno Hdir Hfl Hp Hne Hnd Hfs Hc.
pose proof (openat_plain_name_noslash _ Hnd) as Hsl.
apply openat_plain_name_nodirref in Hnd.
apply (rz_ret_only_copyins_silent regs pc mem rom model (open_copyins (pend_at regs pc mem rom))
(errno_ret ENOENT) model T Hh Hlz).
- intro eff. rewrite chk56 by exact Hno. unfold check_openat.
rewrite (modeled_open_flags_rd _ Hfl). cbn [negb].
unfold Prelude.check_copyins_after, Open.check_openat_body. rewrite si_mem, Hp.
rewrite (path_eqb_neq _ _ Hne). rewrite Hdir, fd32_AT_FDCWD, bv_eqb_refl. cbn [negb].
unfold Open.check_openat_resolved. rewrite Hsl.
rewrite Hfl. cbn [Z.eqb]. unfold Open.check_openat_read.
rewrite Hnd, Hfs.
unfold check_ret_only_copyins, check_copyins, open_copyins.
rewrite pend_gpr1. cbn [ms_read_byte pend_at ms_mem ms_rom].
destruct (check_ret_only (clear_copyins eff) (errno_ret ENOENT) model []) eqn:Hq;
[reflexivity| |reflexivity].
destruct (access_ranges_eqb _ _); reflexivity.
- exact Hh.
- exact Hlz.
- exact Hc.
Qed.
Lemma rz_open_core : forall regs pc mem rom model reads (mk : word -> Model) A B,
m_halted model = None -> m_vm_lazy model = [] ->
(forall eff, check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= check_open_result_copyins reads eff model mk) ->
(forall fd, m_halted (mk fd) = None) -> (forall fd, m_vm_lazy (mk fd) = []) ->
fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
(forall e, In e openat_errnos ->
realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model) A) ->
realizes segs (mkCfg (mkst (regupd regs 10 (alloc_fd (m_fds model))) (v_addi pc 4) mem rom)
(mk (alloc_fd (m_fds model)))) B ->
alloc_no_b (bv_unsigned (getr regs 17)) = false ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) (t_alt2 A B).
Proof.
intros regs pc mem rom model reads mk A B Hh Hlz Hchk Hmk Hmkl Hfree HA HB Hna.
pose (IA := {e : Z | In e openat_errnos}).
pose (ef := fun i : IA + unit =>
match i with
| inl e => with_copyins reads (mkEffect (errno_ret (proj1_sig e)) [] [])
| inr _ => with_copyins reads (mkEffect (alloc_fd (m_fds model)) [] [])
end).
pose (md := fun i : IA + unit =>
match i with inl _ => model | inr _ => mk (alloc_fd (m_fds model)) end).
apply (rz_alt2 segs (mkCfg (pend_at regs pc mem rom) model) IA unit
(fun i => mkCfg (advance_past_svc (apply_effect (pend_at regs pc mem rom) (ef i))) (md i))
A B (exist _ ENOMEM ENOMEM_in_openat_errnos) tt).
- apply (node_chk (pend_at regs pc mem rom) model (getr regs 17) (IA + unit) (inr tt)
ef md (fun _ => []) Hh eq_refl).
+ intros [[e He] | []]; unfold ef, md; cbn [proj1_sig]; rewrite Hchk; apply check_open_result_copyins_ok_iff.
* left. exists e. auto.
* right. exists (alloc_fd (m_fds model)). auto.
+ intros [[e He] | []]; unfold md; [exact Hh | apply Hmk].
+ intros [[e He] | []]; unfold md; [exact Hlz | apply Hmkl].
+ intros eff m' evs Hk. rewrite Hchk in Hk. apply check_open_result_copyins_ok_iff in Hk.
destruct Hk as [(e & He & -> & -> & ->) | (fd & _ & -> & -> & -> & ->)].
* exists (inl (exist _ e He)). unfold ef, md; cbn [proj1_sig]. auto.
* exists (inr tt). unfold ef, md. auto.
+ exact (fun _ => acfg_nonspurious_no _ _ _ _ _ _ eq_refl Hna).
- intros [e He]. unfold ef, md; cbn [proj1_sig]. rewrite adv_pend. cbn [eff_ret with_copyins].
rewrite effmem_copyins_ret_only. apply HA. exact He.
- intros []. unfold ef, md. rewrite adv_pend. cbn [eff_ret with_copyins].
rewrite effmem_copyins_ret_only. exact HB.
Qed.
Lemma rz_openat_file : forall regs pc mem rom model p d A B,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 56%Z ->
getr regs 10 = AT_FDCWD ->
Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk p ->
p <> [] -> openat_plain_name p = true ->
fs_lookup (m_fs model) p = Some d ->
fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
(forall e, In e openat_errnos ->
realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model) A) ->
realizes segs (mkCfg (mkst (regupd regs 10 (alloc_fd (m_fds model))) (v_addi pc 4) mem rom)
(with_fds (fd_insert (m_fds model) (alloc_fd (m_fds model))
(FdFile p (Z_to_bv 64 0))) model)) B ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) (t_alt2 A B).
Proof.
intros regs pc mem rom model p d A B Hh Hlz Hno Hdir Hfl Hp Hne Hnd Hfs Hfree HA HB.
apply (rz_open_core regs pc mem rom model (open_copyins (pend_at regs pc mem rom))
(fun fd => with_fds (fd_insert (m_fds model) fd (FdFile p (Z_to_bv 64 0))) model)
A B Hh Hlz).
- intro eff.
apply (openat_rd_check segs (pend_at regs pc mem rom) (getr regs 17) model p d Hno).
+ rewrite pend_gpr0. exact Hdir.
+ rewrite pend_gpr1. exact Hp.
+ apply path_eqb_neq. exact Hne.
+ rewrite pend_gpr2. exact Hfl.
+ exact Hnd.
+ exact Hfs.
- intro fd. exact Hh.
- intro fd. exact Hlz.
- exact Hfree.
- exact HA.
- exact HB.
- rewrite Hno; reflexivity.
Qed.
Lemma rz_openat_dir : forall regs pc mem rom model A B,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 56%Z ->
getr regs 10 = AT_FDCWD ->
Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z ->
read_cstr (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) = CstrOk dot_path ->
fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
(forall e, In e openat_errnos ->
realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model) A) ->
realizes segs (mkCfg (mkst (regupd regs 10 (alloc_fd (m_fds model))) (v_addi pc 4) mem rom)
(with_fds (fd_insert (m_fds model) (alloc_fd (m_fds model)) FdDir) model)) B ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) (t_alt2 A B).
Proof.
intros regs pc mem rom model A B Hh Hlz Hno Hdir Hfl Hp Hfree HA HB.
apply (rz_open_core regs pc mem rom model (open_copyins (pend_at regs pc mem rom))
(fun fd => with_fds (fd_insert (m_fds model) fd FdDir) model) A B Hh Hlz).
- intro eff. rewrite chk56 by exact Hno. unfold check_openat.
rewrite (modeled_open_flags_rd _ Hfl). cbn [negb].
unfold Prelude.check_copyins_after, Open.check_openat_body. rewrite si_mem, Hp.
change (path_eqb dot_path []) with false.
rewrite Hdir, fd32_AT_FDCWD, bv_eqb_refl. cbn [negb].
unfold Open.check_openat_resolved.
rewrite Hfl. cbn [Z.eqb]. unfold Open.check_openat_read.
change (path_eqb dot_path dot_path) with true. cbv beta iota.
unfold check_open_result_copyins, open_copyins.
rewrite pend_gpr1. cbn [ms_read_byte pend_at ms_mem ms_rom].
destruct (check_open_result (clear_copyins eff) model _) eqn:Hq; try reflexivity.
exfalso. exact (check_open_result_never_unmodeled _ _ _ Hq).
- intro fd. exact Hh.
- intro fd. exact Hlz.
- exact Hfree.
- exact HA.
- exact HB.
- rewrite Hno; reflexivity.
Qed.
Lemma chk63 : forall regs pc mem rom model eff,
bv_unsigned (getr regs 17) = 63%Z ->
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= check_read (sys_input segs (pend_at regs pc mem rom) (getr regs 17))
(fd32 (getr regs 10)) (getr regs 11) (getr regs 12) eff model.
Proof.
intros regs pc mem rom model eff Hno.
rewrite (DispatchCompute.check_syscall_read _ eff model) by (rewrite si_sysno; exact Hno).
rewrite ?si_arg0, ?si_arg1, ?si_arg2, ?si_arg3, ?si_arg4, ?si_arg5. reflexivity.
Qed.
Lemma rz_read_file : forall regs pc mem rom model fd p off data bs w T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 63%Z ->
getr regs 10 = fd -> fd32 fd = fd ->
fd_lookup (m_fds model) fd = Some (FdFile p off) ->
fs_lookup (m_fs model) p = Some data ->
modeled_rw_count (getr regs 12) = true ->
file_read data off (getr regs 12) = bs ->
read_bytes_map (wview segs mem) (getr regs 11) (len_word bs) = Some w ->
access_okb (getr regs 11) (bv_unsigned (getr regs 12)) = true ->
realizes segs (mkCfg (mkst (regupd regs 10 (len_word bs)) (v_addi pc 4)
(match bs with
| [] => mem
| _ :: _ => write_to_mem mem (getr regs 11) bs
end) rom)
(with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs)))
model)) T ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model fd p off data bs w T Hh Hlz Hno Hfd H32 Hlk Hfs Hcnt Hbs Hw Hz Hc.
set (m' := with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model) in Hc.
assert (Hchk : forall eff,
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= match bs, eff with
| [], _ => check_ret_only eff (Z_to_bv 64 0) m' []
| _ :: _, mkEffectU ret [(a, bs')] [] [] [] [] =>
if bv_eqb a (getr regs 11) && listN_eqb bs' bs && bv_eqb ret (len_word bs)
then CheckOk m' [] else CheckReject
| _, _ => CheckReject
end).
{ intro eff. rewrite chk63 by exact Hno. unfold check_read.
assert (HcntZ : (bv_unsigned (getr regs 12) <= rw_bytes_max)%Z)
by (unfold modeled_rw_count in Hcnt; apply Z.leb_le; exact Hcnt).
rewrite Hfd, H32, Hlk, Hz. cbn [negb]. rewrite Hfs. cbv zeta.
rewrite (rw_count_clamp_of_rw _ HcntZ), Z_to_bv_bv_unsigned.
rewrite Hbs, si_wmem, Hw.
destruct bs as [|b bs']; reflexivity. }
destruct bs as [|b bs'].
- apply (rz_ret_only_silent regs pc mem rom model (Z_to_bv 64 0) m' T Hh Hlz Hchk).
+ exact Hh.
+ exact Hlz.
+ exact Hc.
- apply (rz_chk1_silent regs pc mem rom model
(mkEffect (len_word (b :: bs')) [(getr regs 11, b :: bs')] []) m' T Hh Hlz).
+ rewrite Hchk. rewrite !bv_eqb_refl, (proj2 (listN_eqb_eq _ _) eq_refl). reflexivity.
+ exact Hh.
+ exact Hlz.
+ intros [r ws zs us cs ci] m2 evs2 Hk. rewrite Hchk in Hk.
destruct ws as [|[a bsx] [|? ?]]; try discriminate.
destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (bv_eqb a (getr regs 11)) eqn:E1; [|discriminate].
destruct (listN_eqb bsx (b :: bs')) eqn:E2; [|discriminate].
destruct (bv_eqb r (len_word (b :: bs'))) eqn:E3; [|discriminate].
cbn [andb] in Hk. inversion Hk; subst.
apply bv_eqb_eq in E1. apply listN_eqb_eq in E2. apply bv_eqb_eq in E3. subst. auto.
+ cbn [eff_ret]. rewrite effmem_write1. exact Hc.
Qed.
Lemma wview_overlay : forall mem (x : word) b, mem x = Some b -> wview segs mem x = Some b.
Proof. intros mem x b H. unfold wview. rewrite H. reflexivity. Qed.
Lemma read_bytes_aux_defined : forall mp n (a : word),
(forall i, (0 <= i < Z.of_nat n)%Z -> mp (Z_to_bv 64 (bv_unsigned a + i)) <> None) ->
exists w, read_bytes_aux mp a n = Some w.
Proof.
intros mp n. induction n as [|n IH]; intros a Hdef.
- exists []. reflexivity.
- cbn [read_bytes_aux].
assert (Ha : mp a <> None).
{ specialize (Hdef 0%Z ltac:(lia)). rewrite Z.add_0_r, Z_to_bv_bv_unsigned in Hdef. exact Hdef. }
destruct (mp a) as [b|]; [|congruence].
destruct (IH (a + 1)) as [w Hw].
{ intros i Hi.
replace (Z_to_bv 64 (bv_unsigned (a + 1) + i)) with (Z_to_bv 64 (bv_unsigned a + (i + 1))).
- apply Hdef. lia.
- apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
change (bv_unsigned (1 : word)) with 1%Z.
rewrite Zplus_mod_idemp_l. f_equal. lia. }
rewrite Hw. exists (b :: w). reflexivity.
Qed.
Lemma read_dest_ok : forall mem (buf : word) (bs : list byte),
(forall i, (0 <= i < Z.of_nat (length bs))%Z ->
mem (Z_to_bv 64 (bv_unsigned buf + i)) <> None) ->
exists w, read_bytes_map (wview segs mem) buf (len_word bs) = Some w.
Proof.
intros mem buf bs Hdef. rewrite read_bytes_map_eq.
apply read_bytes_aux_defined. intros i Hi.
assert (Hlen : (Z.of_nat (word_to_nat (len_word bs)) <= Z.of_nat (length bs))%Z).
{ unfold word_to_nat, len_word. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
pose proof (Z.mod_le (Z.of_nat (length bs)) (2 ^ 64) ltac:(lia) ltac:(lia)).
rewrite Z2Nat.id by (apply Z.mod_pos_bound; lia). lia. }
specialize (Hdef i ltac:(lia)).
destruct (mem (Z_to_bv 64 (bv_unsigned buf + i))) as [b|] eqn:E; [|congruence].
rewrite (wview_overlay mem _ b E). discriminate.
Qed.
Lemma rz_read_dir : forall regs pc mem rom model fd T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 63%Z ->
getr regs 10 = fd -> fd32 fd = fd ->
fd_lookup (m_fds model) fd = Some FdDir ->
access_okb (getr regs 11) (bv_unsigned (getr regs 12)) = true ->
realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem rom) model) T ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model fd T Hh Hlz Hno Hfd H32 Hlk Hdr Hc.
apply (rz_ret_only_silent regs pc mem rom model (errno_ret EISDIR) model T Hh Hlz).
- intro eff. rewrite chk63 by exact Hno. unfold check_read. rewrite Hfd, H32, Hlk, Hdr. reflexivity.
- exact Hh.
- exact Hlz.
- exact Hc.
Qed.
Lemma chk66 : forall regs pc mem rom model eff,
bv_unsigned (getr regs 17) = 66%Z ->
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= check_writev (sys_input segs (pend_at regs pc mem rom) (getr regs 17))
(fd32 (getr regs 10)) (getr regs 11) (getr regs 12) eff model.
Proof.
intros regs pc mem rom model eff Hno.
rewrite (DispatchCompute.check_syscall_writev _ eff model) by (rewrite si_sysno; exact Hno).
rewrite ?si_arg0, ?si_arg1, ?si_arg2, ?si_arg3, ?si_arg4, ?si_arg5. reflexivity.
Qed.
Lemma read_u64_ms : forall ms a, read_u64 (ms_read_byte ms) a = ms_read_u64 ms a.
Proof. intros. unfold read_u64, ms_read_u64. rewrite read_bytes_map_read_byte. reflexivity. Qed.
Lemma word_add_BV : forall (x : word) (k : Z) (Hk : BvWf 64 k),
x + @BV 64 k Hk = Z_to_bv 64 (bv_unsigned x + k).
Proof.
intros x k Hk. apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. reflexivity.
Qed.
Lemma Z_to_bv_unsigned_add : forall (a k : Z),
Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a) + k) = Z_to_bv 64 (a + k).
Proof.
intros a k. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
apply Zplus_mod_idemp_l.
Qed.
Lemma writev_gate_off : forall (t : Z) (bs : list byte),
Z.of_nat (length bs) = t -> negb (t =? 0)%Z && (length bs =? 0)%nat = false.
Proof.
intros t bs H. destruct bs; cbn [length] in *; subst; [reflexivity|].
cbn [Nat.eqb]. apply andb_false_r.
Qed.
Lemma cap_iovecs_aux_id : forall iovs left,
(iovs_total iovs <= left)%Z -> cap_iovecs_aux iovs left = iovs.
Proof.
induction iovs as [|[b l] r IH]; intros left Hle; cbn in *; [reflexivity|].
pose proof (iovs_total_nonneg r). pose proof (u64_range l).
rewrite Z.min_r by lia. rewrite Z_to_bv_bv_unsigned. f_equal. apply IH. lia.
Qed.
Lemma cap_iovecs_id : forall iovs,
(iovs_total iovs <= MAX_RW_COUNT)%Z -> cap_iovecs iovs = iovs.
Proof. intros. unfold cap_iovecs. apply cap_iovecs_aux_id. assumption. Qed.
Lemma rw_bytes_max_lt_MAX_RW_COUNT : (rw_bytes_max < MAX_RW_COUNT)%Z.
Proof. unfold rw_bytes_max, MAX_RW_COUNT. lia. Qed.
Definition writev_copyins (mp : word -> option byte) (iov cnt : word)
(iovs : list (word * word)) (n : nat) : list (word * nat) :=
import_iovecs_accesses mp iov (iovcnt32 cnt) ++ iov_prefix_accesses iovs n.
Definition writev_eff (mp : word -> option byte) (iov cnt : word)
(iovs : list (word * word)) (n : nat) : SyscallEffect :=
mkEffectU (Z_to_bv 64 (Z.of_nat n)) [] [] [] [] (writev_copyins mp iov cnt iovs n).
Lemma effmem_writev_eff : forall mem mp iov cnt iovs n,
effmem mem (writev_eff mp iov cnt iovs n) = mem.
Proof. reflexivity. Qed.
Lemma iovcnt32_small : forall w : word, (bv_unsigned w < 2 ^ 32)%Z -> iovcnt32 w = w.
Proof. intros w H. unfold iovcnt32. apply fd32_id. exact H. Qed.
Lemma writev_chk_canon : forall regs pc mem rom model fd ch iovs bs,
bv_unsigned (getr regs 17) = 66%Z ->
fdchan fd ch model -> fd32 fd = fd -> getr regs 10 = fd ->
w_is0 (iovcnt32 (getr regs 12)) = false ->
(bv_unsigned (getr regs 12) <= IOV_MAX)%Z ->
copy_iovecs_aux (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11)
(word_to_nat (iovcnt32 (getr regs 12))) = ImpOk iovs ->
access_okb (getr regs 11) (16 * bv_unsigned (getr regs 12)) = true ->
iovs_access_okb iovs = true ->
gather_iovecs (ms_read_byte (pend_at regs pc mem rom)) iovs = Some bs ->
(iovs_total iovs <= MAX_RW_COUNT)%Z ->
(1 <= length bs)%nat ->
forall eff,
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= match eff with
| mkEffectU ret [] [] [] [] ci =>
if ((1 <=? bv_unsigned ret) && (bv_unsigned ret <=? Z.of_nat (length bs)))%Z
&& negb (addr_is_error_b ret)
&& access_ranges_eqb ci
(writev_copyins (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11)
(getr regs 12) iovs (Z.to_nat (bv_unsigned ret)))
then CheckOk model (map (WriteEv ch) (firstn (Z.to_nat (bv_unsigned ret)) bs))
else CheckReject
| _ => CheckReject
end.
Proof.
intros regs pc mem rom model fd ch iovs bs Hno [Hlk Hch] H32 Hfd Hcnt Hmax Himp Hiok Hbok Hg Htot Hnb eff.
pose proof (gather_iovecs_length _ _ _ Hg) as Hlen.
assert (HMv : MAX_RW_COUNT = 0x7ffff000%Z) by reflexivity.
assert (Hiov : (IOV_MAX <? bv_unsigned (getr regs 12))%Z = false) by (apply Z.ltb_ge; lia).
assert (E32 : iovcnt32 (getr regs 12) = getr regs 12)
by (apply iovcnt32_small; unfold IOV_MAX in Hmax; lia).
rewrite E32 in Hcnt, Himp.
assert (Himp' : import_iovecs (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) (getr regs 12) = ImpOk iovs).
{ unfold import_iovecs.
destruct (bv_eqb (getr regs 12) (Z_to_bv 64 1)) eqn:E1.
- apply bv_eqb_eq in E1. rewrite E1 in Himp, Hiok.
change (16 * bv_unsigned (Z_to_bv 64 1))%Z with 16%Z in Hiok. rewrite Hiok. cbn [negb].
change (word_to_nat (Z_to_bv 64 1)) with 1%nat in Himp. cbn [copy_iovecs_aux] in Himp.
destruct (read_iovec_entry (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11)) as [base len| |] eqn:Er;
try discriminate.
injection Himp as <-. cbn [iovs_access_okb forallb fst snd] in Hbok. rewrite andb_true_r in Hbok.
cbn [iovs_total] in Htot.
rewrite Z.min_l by lia. rewrite Hbok. reflexivity.
- destruct (bv_eqb (getr regs 12) (Z_to_bv 64 0)) eqn:E0.
+ apply bv_eqb_eq in E0. rewrite E0 in Hcnt. discriminate.
+ rewrite Hiov, Hiok. cbn [negb]. rewrite Himp, Hbok. reflexivity. }
rewrite chk66 by exact Hno. rewrite Hfd, H32. unfold check_writev.
rewrite ?E32, Hlk, Hch, si_mem, Himp'.
rewrite cap_iovecs_id by lia. cbv zeta.
replace (iovs_total iovs =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
unfold writev_gathered. rewrite cap_iovecs_id by lia. rewrite (gather_prefix_full _ _ _ Hg).
replace (Nat.eqb (length bs) 0) with false by (symmetry; apply Nat.eqb_neq; lia).
assert (Herr : addr_is_error_b (len_word bs) = false).
{ unfold addr_is_error_b. apply Z.ltb_ge. rewrite len_word_unsigned; unfold two_pow_64; lia. }
rewrite Herr. unfold writev_copyins. rewrite ?E32.
destruct eff as [ret ws zs us cs ci].
destruct ws; [|reflexivity]. destruct zs; [|reflexivity].
destruct us; [|reflexivity]. destruct cs; [|reflexivity].
destruct (((1 <=? bv_unsigned ret)%Z && (bv_unsigned ret <=? Z.of_nat (length bs))%Z) &&
negb (addr_is_error_b ret)); reflexivity.
Qed.
Lemma rz_writev : forall regs pc mem rom model fd ch iovs bs T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 66%Z ->
fdchan fd ch model -> fd32 fd = fd -> getr regs 10 = fd ->
w_is0 (iovcnt32 (getr regs 12)) = false ->
(bv_unsigned (getr regs 12) <= IOV_MAX)%Z ->
copy_iovecs_aux (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11)
(word_to_nat (iovcnt32 (getr regs 12))) = ImpOk iovs ->
access_okb (getr regs 11) (16 * bv_unsigned (getr regs 12)) = true ->
iovs_access_okb iovs = true ->
gather_iovecs (ms_read_byte (pend_at regs pc mem rom)) iovs = Some bs ->
(iovs_total iovs <= MAX_RW_COUNT)%Z ->
(1 <= length bs)%nat ->
(forall n, (1 <= n)%nat -> (n <= length bs)%nat ->
realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat n))) (v_addi pc 4) mem rom)
model) T) ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) (t_write_ch ch bs T).
Proof.
intros regs pc mem rom model fd ch iovs bs T Hh Hlz Hno Hfdc H32 Hfd Hcnt Hmax Himp Hiok Hbok Hg Htot Hnb Hc.
pose proof (writev_chk_canon regs pc mem rom model fd ch iovs bs Hno Hfdc H32 Hfd Hcnt Hmax Himp Hiok Hbok Hg Htot Hnb)
as Hchk.
pose proof (gather_iovecs_length _ _ _ Hg) as Hlen.
assert (HMv : MAX_RW_COUNT = 0x7ffff000%Z) by reflexivity.
set (mp := ms_read_byte (pend_at regs pc mem rom)) in *.
pose (ef := fun i : wr_index bs => writev_eff mp (getr regs 11) (getr regs 12) iovs (proj1_sig i)).
unfold t_write_ch.
apply (rz_node segs (mkCfg (pend_at regs pc mem rom) model) (wr_index bs)
(fun i => map (WriteEv ch) (firstn (proj1_sig i) bs))
(fun i => mkCfg (advance_past_svc (apply_effect (pend_at regs pc mem rom) (ef i))) model)
(fun _ => T) (wr_full bs Hnb)).
- apply (node_chk (pend_at regs pc mem rom) model (getr regs 17) (wr_index bs) (wr_full bs Hnb)
ef (fun _ => model) (fun i => map (WriteEv ch) (firstn (proj1_sig i) bs)) Hh eq_refl).
+ intros [n [Hn1 Hn2]]. unfold ef, writev_eff; cbn [proj1_sig]. rewrite Hchk.
assert (Hu : bv_unsigned (Z_to_bv 64 (Z.of_nat n)) = Z.of_nat n).
{ rewrite Z_to_bv_unsigned, bv_wrap64_mod. apply Z.mod_small. lia. }
rewrite Hu, Nat2Z.id.
rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia.
replace (addr_is_error_b (Z_to_bv 64 (Z.of_nat n))) with false
by (symmetry; unfold addr_is_error_b; apply Z.ltb_ge; rewrite Hu; unfold two_pow_64; lia).
rewrite (proj2 (access_ranges_eqb_eq _ _) eq_refl). reflexivity.
+ intros _. exact Hh.
+ intros _. exact Hlz.
+ intros [ret ws zs us cs ci] m' evs Hk. rewrite Hchk in Hk.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate].
destruct (((1 <=? bv_unsigned ret)%Z && (bv_unsigned ret <=? Z.of_nat (length bs))%Z) &&
negb (addr_is_error_b ret) && access_ranges_eqb ci _) eqn:E; [|discriminate].
injection Hk as <- <-.
apply andb_prop in E as [E Hci]. apply andb_prop in E as [E _]. apply andb_prop in E as [E1 E2].
apply Z.leb_le in E1. apply Z.leb_le in E2. apply access_ranges_eqb_eq in Hci.
assert (Hr : (1 <= Z.to_nat (bv_unsigned ret))%nat /\ (Z.to_nat (bv_unsigned ret) <= length bs)%nat) by lia.
exists (exist _ (Z.to_nat (bv_unsigned ret)) Hr). unfold ef, writev_eff; cbn [proj1_sig].
rewrite Z2Nat.id by lia. rewrite Z_to_bv_bv_unsigned, Hci. auto.
+ exact (fun _ => acfg_nonspurious_no _ _ _ _ _ _ Hno eq_refl).
- intros [n [Hn1 Hn2]]. unfold ef; cbn [proj1_sig]. rewrite adv_pend.
rewrite effmem_writev_eff. unfold writev_eff; cbn [eff_ret]. apply Hc; assumption.
Qed.
Lemma read_iovec_entry_of : forall ms (a b l : word),
ms_read_u64 ms a = Some b ->
ms_read_u64 ms (Z_to_bv 64 (bv_unsigned a + 8)) = Some l ->
(bv_unsigned l < 2 ^ 63)%Z ->
read_iovec_entry (ms_read_byte ms) a = IovEntry b l.
Proof.
intros ms a b l Hb Hl Hs. unfold read_iovec_entry. rewrite !read_u64_ms, word_add_BV, Hb, Hl.
rewrite (proj2 (Z.leb_gt _ _) Hs). reflexivity.
Qed.
Lemma copy_iovecs_1 : forall ms (iov b0 l0 : word),
ms_read_u64 ms iov = Some b0 ->
ms_read_u64 ms (Z_to_bv 64 (bv_unsigned iov + 8)) = Some l0 ->
(bv_unsigned l0 < 2 ^ 63)%Z ->
copy_iovecs_aux (ms_read_byte ms) iov 1 = ImpOk [(b0, l0)].
Proof.
intros ms iov b0 l0 Hb0 Hl0 Hs. cbn [copy_iovecs_aux].
rewrite (read_iovec_entry_of ms iov b0 l0 Hb0 Hl0 Hs). reflexivity.
Qed.
Lemma copy_iovecs_2 : forall ms (iov b0 l0 b1 l1 : word),
ms_read_u64 ms iov = Some b0 ->
ms_read_u64 ms (Z_to_bv 64 (bv_unsigned iov + 8)) = Some l0 ->
ms_read_u64 ms (Z_to_bv 64 (bv_unsigned iov + 16)) = Some b1 ->
ms_read_u64 ms (Z_to_bv 64 (bv_unsigned iov + 24)) = Some l1 ->
(bv_unsigned l0 < 2 ^ 63)%Z -> (bv_unsigned l1 < 2 ^ 63)%Z ->
copy_iovecs_aux (ms_read_byte ms) iov 2 = ImpOk [(b0, l0); (b1, l1)].
Proof.
intros ms iov b0 l0 b1 l1 Hb0 Hl0 Hb1 Hl1 Hs0 Hs1. cbn [copy_iovecs_aux].
rewrite (read_iovec_entry_of ms iov b0 l0 Hb0 Hl0 Hs0).
rewrite word_add_BV.
rewrite (read_iovec_entry_of ms (Z_to_bv 64 (bv_unsigned iov + 16)) b1 l1 Hb1).
- reflexivity.
- rewrite Z_to_bv_unsigned_add. replace (bv_unsigned iov + 16 + 8)%Z with (bv_unsigned iov + 24)%Z by lia.
exact Hl1.
- exact Hs1.
Qed.
Lemma gather_iovecs_1 : forall mp b0 l0 bs0,
read_bytes_map mp b0 l0 = Some bs0 -> gather_iovecs mp [(b0, l0)] = Some bs0.
Proof. intros mp b0 l0 bs0 H. cbn [gather_iovecs]. rewrite H, app_nil_r. reflexivity. Qed.
Lemma gather_iovecs_2 : forall mp b0 l0 b1 l1 bs0 bs1,
read_bytes_map mp b0 l0 = Some bs0 -> read_bytes_map mp b1 l1 = Some bs1 ->
gather_iovecs mp [(b0, l0); (b1, l1)] = Some (bs0 ++ bs1).
Proof. intros mp b0 l0 b1 l1 bs0 bs1 H0 H1. cbn [gather_iovecs]. rewrite H0, H1, app_nil_r. reflexivity. Qed.
Lemma rz_writev2 : forall regs pc mem rom model fd ch (b0 l0 b1 l1 : word) bs0 bs1 T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 66%Z ->
fdchan fd ch model -> fd32 fd = fd ->
getr regs 10 = fd ->
getr regs 12 = Z_to_bv 64 2 ->
ms_read_u64 (pend_at regs pc mem rom) (getr regs 11) = Some b0 ->
ms_read_u64 (pend_at regs pc mem rom) (Z_to_bv 64 (bv_unsigned (getr regs 11) + 8)) = Some l0 ->
ms_read_u64 (pend_at regs pc mem rom) (Z_to_bv 64 (bv_unsigned (getr regs 11) + 16)) = Some b1 ->
ms_read_u64 (pend_at regs pc mem rom) (Z_to_bv 64 (bv_unsigned (getr regs 11) + 24)) = Some l1 ->
ms_read_bytes (pend_at regs pc mem rom) b0 l0 = Some bs0 ->
ms_read_bytes (pend_at regs pc mem rom) b1 l1 = Some bs1 ->
access_okb (getr regs 11) 32 = true ->
access_okb b0 (bv_unsigned l0) = true -> access_okb b1 (bv_unsigned l1) = true ->
(1 <= bv_unsigned l0 + bv_unsigned l1 <= MAX_RW_COUNT)%Z ->
(forall n, (1 <= n)%nat -> (n <= length (bs0 ++ bs1))%nat ->
realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat n))) (v_addi pc 4) mem rom)
model) T) ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) (t_write_ch ch (bs0 ++ bs1) T).
Proof.
intros regs pc mem rom model fd ch b0 l0 b1 l1 bs0 bs1 T
Hh Hlz Hno Hfdc H32 Hfd Hcnt Hb0 Hl0 Hb1 Hl1 Hbs0 Hbs1 Hiok Hok0 Hok1 Htot Hc.
rewrite <- read_bytes_map_read_byte in Hbs0, Hbs1.
pose proof (gather_iovecs_2 _ _ _ _ _ _ _ Hbs0 Hbs1) as Hg.
pose proof (gather_iovecs_length _ _ _ Hg) as Hlen. cbn [iovs_total] in Hlen.
pose proof (read_bytes_map_length _ _ _ _ Hbs0). pose proof (read_bytes_map_length _ _ _ _ Hbs1).
unfold MAX_RW_COUNT in Htot.
eapply (rz_writev regs pc mem rom model fd ch [(b0, l0); (b1, l1)] (bs0 ++ bs1) T Hh Hlz Hno Hfdc H32 Hfd).
- rewrite Hcnt. reflexivity.
- rewrite Hcnt. cbv. discriminate.
- rewrite Hcnt. change (word_to_nat (iovcnt32 (Z_to_bv 64 2))) with 2%nat.
apply copy_iovecs_2; try assumption; lia.
- rewrite Hcnt. exact Hiok.
- cbn [iovs_access_okb forallb fst snd]. rewrite Hok0, Hok1. reflexivity.
- exact Hg.
- cbn [iovs_total]. unfold MAX_RW_COUNT. lia.
- lia.
- exact Hc.
Qed.
Lemma rz_writev1 : forall regs pc mem rom model fd ch (b0 l0 : word) bs0 T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 66%Z ->
fdchan fd ch model -> fd32 fd = fd ->
getr regs 10 = fd ->
getr regs 12 = Z_to_bv 64 1 ->
ms_read_u64 (pend_at regs pc mem rom) (getr regs 11) = Some b0 ->
ms_read_u64 (pend_at regs pc mem rom) (Z_to_bv 64 (bv_unsigned (getr regs 11) + 8)) = Some l0 ->
ms_read_bytes (pend_at regs pc mem rom) b0 l0 = Some bs0 ->
access_okb (getr regs 11) 16 = true ->
access_okb b0 (bv_unsigned l0) = true ->
(1 <= bv_unsigned l0 <= MAX_RW_COUNT)%Z ->
(forall n, (1 <= n)%nat -> (n <= length bs0)%nat ->
realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat n))) (v_addi pc 4) mem rom)
model) T) ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) (t_write_ch ch bs0 T).
Proof.
intros regs pc mem rom model fd ch b0 l0 bs0 T Hh Hlz Hno Hfdc H32 Hfd Hcnt Hb0 Hl0 Hbs0 Hiok Hok0 Htot Hc.
rewrite <- read_bytes_map_read_byte in Hbs0.
pose proof (gather_iovecs_1 _ _ _ _ Hbs0) as Hg.
pose proof (gather_iovecs_length _ _ _ Hg) as Hlen. cbn [iovs_total] in Hlen.
pose proof (read_bytes_map_length _ _ _ _ Hbs0).
unfold MAX_RW_COUNT in Htot.
eapply (rz_writev regs pc mem rom model fd ch [(b0, l0)] bs0 T Hh Hlz Hno Hfdc H32 Hfd).
- rewrite Hcnt. reflexivity.
- rewrite Hcnt. cbv. discriminate.
- rewrite Hcnt. change (word_to_nat (iovcnt32 (Z_to_bv 64 1))) with 1%nat.
apply copy_iovecs_1; try assumption; lia.
- rewrite Hcnt. exact Hiok.
- cbn [iovs_access_okb forallb fst snd]. rewrite Hok0. reflexivity.
- exact Hg.
- cbn [iovs_total]. unfold MAX_RW_COUNT. lia.
- lia.
- exact Hc.
Qed.
Lemma brk_model_lazy : forall req r model,
m_vm_lazy model = [] -> m_vm_lazy (brk_model req r model) = [].
Proof.
intros req r model Hlz. unfold brk_model, with_brk_next. cbv zeta.
apply (proj2 (proj2 (proj2 (forget_vm_ranges_frame _ _)))).
unfold with_vmmaps. cbn [m_vm_lazy]. exact Hlz.
Qed.
Lemma brk_model_halted : forall req r model,
m_halted (brk_model req r model) = m_halted model.
Proof.
intros req r model. unfold brk_model, with_brk_next. cbv zeta.
rewrite (proj1 (forget_vm_ranges_frame _ _)). reflexivity.
Qed.
Lemma brk_resolution_ok_keep : forall model req,
brk_resolution_ok model req (vm_brk (m_vmmaps model)).
Proof.
intros model req. unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta.
destruct (w_is0 req || Z.ltb (bv_unsigned req) (bv_unsigned (min_brk (m_vmmaps model)))).
- apply bv_eqb_refl.
- destruct (Z.ltb (bv_unsigned req) (bv_unsigned (vm_brk (m_vmmaps model)))).
+ rewrite bv_eqb_refl, orb_true_r. reflexivity.
+ rewrite bv_eqb_refl, orb_true_r, andb_true_l.
unfold Mmap.brk_grow_ok. now rewrite Z.ltb_irrefl, andb_false_r.
Qed.
Lemma bv_sub_unsigned_nowrap : forall a b : word,
(bv_unsigned b <= bv_unsigned a)%Z -> bv_unsigned (a - b) = (bv_unsigned a - bv_unsigned b)%Z.
Proof.
intros a b H. rewrite bv_sub_unsigned. apply bv_wrap_small.
pose proof (u64_range a). pose proof (u64_range b).
unfold bv_modulus. change (Z.of_N 64) with 64%Z. lia.
Qed.
Lemma brk_model_keep : forall req m,
brk_model req (vm_brk (m_vmmaps m)) m
= with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
(vm_noaccess (m_vmmaps m)) (vm_start_brk (m_vmmaps m))
(vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
Proof.
intros req m. unfold brk_model, with_brk_next. cbv zeta.
rewrite brk_unmaps_keep. cbn [forget_vm_ranges].
unfold brk_model_next, brk_maps_next. rewrite Z.ltb_irrefl, andb_false_r, brk_grants_keep.
rewrite brk_unmaps_keep. reflexivity.
Qed.
Lemma brk_resolution_ok_grow_iff : forall model req r,
let b := vm_brk (m_vmmaps model) in
(bv_unsigned (vm_start_brk (m_vmmaps model)) <= bv_unsigned b)%Z ->
(bv_unsigned b < bv_unsigned req)%Z ->
brk_resolution_ok model req r <->
(r = b \/ (r = req /\ Mmap.brk_grow_ok model req req = true)).
Proof.
intros model req r b Hs Hlt. subst b. unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta.
remember (vm_brk (m_vmmaps model)) as b eqn:Eb.
pose proof (u64_range b) as Hb.
assert (E0 : w_is0 req = false).
{ unfold w_is0. apply bv_eqb_neq. intros E. rewrite E in Hlt.
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hlt. lia. }
rewrite E0. cbn [orb]. unfold min_brk.
rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia.
assert (Gb : Mmap.brk_grow_ok model req b = true).
{ unfold Mmap.brk_grow_ok. cbv zeta. rewrite <- Eb. rewrite (Z.ltb_irrefl (bv_unsigned b)), andb_false_r. reflexivity. }
split.
- intros H. apply andb_prop in H as [H1 H2]. apply orb_prop in H1.
destruct H1 as [H1|H1]; apply bv_eqb_eq in H1; subst; auto.
- intros [-> | [-> G]].
+ rewrite bv_eqb_refl, orb_true_r, Gb. reflexivity.
+ rewrite bv_eqb_refl, G. reflexivity.
Qed.
Lemma brk_model_grow : forall req m (n : Z),
let h := m_vmmaps m in
req <> Z_to_bv 64 0 ->
(0 < bv_unsigned (vm_brk h))%Z -> (bv_unsigned req = bv_unsigned (vm_brk h) + n)%Z -> (0 < n)%Z ->
brk_model req req m
= with_vmmaps (mkVmMapsFull (vm_reserved h) ((vm_brk h, Z_to_bv 64 n) :: vm_maps h)
(vm_noaccess h) (vm_start_brk h) req (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m.
Proof.
intros req m n h Hreq0 Hb Hreq Hn. subst h. unfold brk_model, with_brk_next. cbv zeta.
remember (m_vmmaps m) as h eqn:Eh.
rewrite (brk_unmaps_grow req (vm_brk h)) by lia. cbn [forget_vm_ranges].
unfold brk_model_next, brk_maps_next.
rewrite (proj2 (Z.ltb_ge (bv_unsigned req) (bv_unsigned (vm_brk h)))) by lia.
rewrite andb_false_r. rewrite brk_grants_grow; [| exact Hreq0 | lia | lia].
rewrite (brk_unmaps_grow req (vm_brk h)) by lia. cbn [maps_subtract_ranges fold_left app].
replace (req - vm_brk h) with (Z_to_bv 64 n); [reflexivity|].
apply bv_eq. rewrite bv_sub_unsigned_nowrap by lia. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
pose proof (u64_range req). rewrite Z.mod_small; lia.
Qed.
Lemma brk_grow_ok_unfold : forall m req (n : Z),
let h := m_vmmaps m in
req <> Z_to_bv 64 0 ->
(0 < bv_unsigned (vm_brk h))%Z -> (bv_unsigned (vm_brk h) mod page_size = 0)%Z ->
(bv_unsigned req = bv_unsigned (vm_brk h) + n)%Z -> (0 < n)%Z -> (n mod page_size = 0)%Z ->
Mmap.brk_grow_ok m req req
= ((bv_unsigned (vm_brk h) + n <=? alloc_top h)%Z
&& region_free (vm_reserved h ++ vm_maps h) (vm_brk h) (Z_to_bv 64 (n + page_size))
&& (vm_backing_used m + n <=? vm_limit h)%Z)%bool.
Proof.
intros m req n h Hreq0 Hb Hbal Hreq Hn Hnal. subst h. unfold Mmap.brk_grow_ok, Mmap.brk_budget_ok. cbv zeta.
remember (m_vmmaps m) as h eqn:Eh.
rewrite (proj2 (Z.ltb_lt 0 _) Hb), (proj2 (Z.ltb_lt _ _)) by lia. cbn [andb].
assert (Hru : page_round_up_Z (bv_unsigned req) = (bv_unsigned (vm_brk h) + n)%Z).
{ rewrite Hreq. apply page_round_up_Z_aligned; [lia|].
unfold page_size in *. rewrite Z.add_mod, Hnal, Hbal by lia. reflexivity. }
rewrite (page_round_up_Z_aligned (bv_unsigned (vm_brk h))) by lia. rewrite Hru.
rewrite (proj2 (Z.ltb_lt _ _)) by lia.
replace (bv_unsigned (vm_brk h) + n + page_size - bv_unsigned (vm_brk h))%Z with (n + page_size)%Z by lia.
rewrite Z_to_bv_bv_unsigned. rewrite bv_sub_unsigned_nowrap by lia. rewrite Hreq.
replace (bv_unsigned (vm_brk h) + n - bv_unsigned (vm_brk h))%Z with n by lia. reflexivity.
Qed.
Definition mmap_rw_J04 (hint : word) (model : Model) (nZ : Z) : Type :=
({e : Z | In e mmap_errnos}
+ {a : word | grant_ok hint model a nZ = true})%type.
Lemma mmap_rw_wit04 : forall hint model nZ, mmap_rw_J04 hint model nZ.
Proof. intros hint model nZ. left. exists ENOMEM. apply ENOMEM_in_mmap_errnos. Qed.
Definition mmap_rw_ef04 (regs : bvmap 5 word) (model : Model)
(i : mmap_rw_J04 (getr regs 10) model (page_round_up_Z (bv_unsigned (getr regs 11)))) : SyscallEffect :=
match i with
| inl e => mkEffect (errno_ret (proj1_sig e)) [] []
| inr a => mkEffect (proj1_sig a) [] [(proj1_sig a, page_round_up (getr regs 11))]
end.
Definition mmap_rw_md04 (regs : bvmap 5 word) (model : Model)
(i : mmap_rw_J04 (getr regs 10) model (page_round_up_Z (bv_unsigned (getr regs 11)))) : Model :=
match i with
| inl _ => model
| inr a => mmap_model (proj1_sig a) (page_round_up (getr regs 11)) model
end.
Lemma node_mmap_rw04 : forall regs pc mem rom model,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 222%Z ->
getr regs 11 <> Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 3 ->
getr regs 13 = Z_to_bv 64 34 -> getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
node_ok segs (mkCfg (pend_at regs pc mem rom) model)
(mmap_rw_J04 (getr regs 10) model (page_round_up_Z (bv_unsigned (getr regs 11)))) (fun _ => [])
(fun i => mkCfg (advance_past_svc (apply_effect (pend_at regs pc mem rom) (mmap_rw_ef04 regs model i)))
(mmap_rw_md04 regs model i)).
Proof.
intros regs pc mem rom model Hh Hlz Hno Hlen Hprot Hflags Hfdm Hoff.
assert (Hargs : mmap_args_ok (pend_at regs pc mem rom)).
{ unfold mmap_args_ok. rewrite pend_gpr1, pend_gpr2, pend_gpr3, pend_gpr4, pend_gpr5. auto. }
split.
- intros [[e He] | [a Ha]]; unfold mmap_rw_ef04, mmap_rw_md04; cbn [proj1_sig].
+ apply (sstep_cfg_syscall segs ACFG (pend_at regs pc mem rom) model (getr regs 17) (mkEffect (errno_ret e) [] []) model model []);
[exact Hh | reflexivity | | | exact Hh | apply materialize_model_accesses_no_lazy; exact Hlz].
* destruct (mmap_args_ok_gates _ Hargs) as [Ho [Han [Hl Hmb]]].
apply (proj2 (syscall_spec_mmap segs _ _ _ _ Hno)). apply check_mmap_sound_ok.
unfold check_mmap. cbv beta. rewrite Ho, Han, Hl, Hmb. cbn [negb]. cbv beta iota zeta.
rewrite (errno_ret_in_intro _ _ He). reflexivity.
* apply spurious_refusal_may_fail.
+ rewrite <- (pend_gpr1 regs pc mem rom) in Ha |- *.
apply (sstep_cfg_syscall segs ACFG (pend_at regs pc mem rom) model (getr regs 17) _
(mmap_model a (page_round_up (ms_gpr (pend_at regs pc mem rom) 1)) model)
(mmap_model a (page_round_up (ms_gpr (pend_at regs pc mem rom) 1)) model) []);
[exact Hh | reflexivity | apply mmap_succ_ok; [exact Hno | exact Hargs | rewrite pend_gpr0; exact Ha]
| apply mmap_grant_nonspurious; [exact Hno | rewrite pend_gpr0; exact Ha]
| rewrite mmap_model_halted; exact Hh
| apply materialize_model_accesses_no_lazy; exact (eq_trans (mmap_model_lazy _ _ _) Hlz)].
- intros e st Hst.
destruct (sstep_mmap_inv segs (pend_at regs pc mem rom) model (getr regs 17) e st Hh Hlz eq_refl Hno Hargs Hst)
as (-> & [(err & Herr & ->) | (a & Ha & ->)]).
+ exists (inl (exist _ err Herr)). split; [reflexivity|].
unfold mmap_rw_ef04, mmap_rw_md04; cbn [proj1_sig]. rewrite apply_effect_no_write. reflexivity.
+ rewrite pend_gpr0, pend_gpr1 in Ha. exists (inr (exist _ a Ha)). split; [reflexivity|].
unfold mmap_rw_ef04, mmap_rw_md04; cbn [proj1_sig]. rewrite pend_gpr1. reflexivity.
Qed.
Lemma rz_mmap_rw_ok : forall regs pc mem rom model B,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 222%Z ->
getr regs 11 <> Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 3 ->
getr regs 13 = Z_to_bv 64 34 -> getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
(forall e, In e mmap_errnos ->
realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model) B) ->
(forall a, grant_ok (getr regs 10) model a (page_round_up_Z (bv_unsigned (getr regs 11))) = true ->
realizes segs (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4)
(apply_zeros mem [(a, page_round_up (getr regs 11))]) rom)
(mmap_model a (page_round_up (getr regs 11)) model)) B) ->
(exists a, grant_ok (getr regs 10) model a (page_round_up_Z (bv_unsigned (getr regs 11))) = true) ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) B.
Proof.
intros regs pc mem rom model B Hh Hlz Hno Hlen Hprot Hflags Hfdm Hoff HA HB [a0 Ha0].
apply (rz_silent (mkCfg (pend_at regs pc mem rom) model) _ (inr (exist _ a0 Ha0)) _ B
(node_mmap_rw04 regs pc mem rom model Hh Hlz Hno Hlen Hprot Hflags Hfdm Hoff)).
intros [[e He] | [a Ha]]; unfold mmap_rw_ef04, mmap_rw_md04; cbn [proj1_sig].
- rewrite adv_pend. cbn [eff_ret]. rewrite effmem_ret_only. apply HA. exact He.
- rewrite adv_pend. cbn [eff_ret]. rewrite effmem_zeros. apply HB. exact Ha.
Qed.
Lemma rz_munmap_exact : forall regs pc mem rom model T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 215%Z ->
(bv_unsigned (getr regs 10) mod page_size = 0)%Z ->
getr regs 11 <> Z_to_bv 64 0 ->
(bv_unsigned (getr regs 10) + page_round_up_Z (bv_unsigned (getr regs 11)) <= TASK_SIZE)%Z ->
map_has (vm_maps (m_vmmaps model)) (getr regs 10) (page_round_up (getr regs 11)) = true ->
realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
(apply_unmaps mem [(getr regs 10, page_round_up (getr regs 11))]) rom)
(munmap_model (getr regs 10) (page_round_up (getr regs 11)) model)) T ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model T Hh Hlz Hno Hal Hlen Hnw Hhas Hc.
apply (rz_munmap segs (pend_at regs pc mem rom) model (getr regs 17) T Hh Hlz eq_refl Hno).
- unfold munmap_args_ok. rewrite pend_gpr0, pend_gpr1. auto.
- unfold munmap_eff. rewrite pend_gpr0, pend_gpr1, adv_pend. cbn [eff_ret].
rewrite effmem_unmaps. exact Hc.
Qed.
Lemma page_round_up_id : forall l : word,
(bv_unsigned l mod page_size = 0)%Z -> page_round_up l = l.
Proof.
intros l H. unfold page_round_up.
rewrite page_round_up_Z_aligned; [apply Z_to_bv_bv_unsigned | pose proof (u64_range l); lia | exact H].
Qed.
Lemma chk222 : forall regs pc mem rom model eff,
bv_unsigned (getr regs 17) = 222%Z ->
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= check_mmap (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
(getr regs 15) eff model.
Proof.
intros regs pc mem rom model eff Hno.
rewrite (DispatchCompute.check_syscall_mmap _ eff model) by (rewrite si_sysno; exact Hno).
rewrite ?si_arg0, ?si_arg1, ?si_arg2, ?si_arg3, ?si_arg4, ?si_arg5. reflexivity.
Qed.
Lemma chk226 : forall regs pc mem rom model eff,
bv_unsigned (getr regs 17) = 226%Z ->
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= check_mprotect (getr regs 10) (getr regs 11) (getr regs 12) eff model.
Proof.
intros regs pc mem rom model eff Hno.
rewrite (DispatchCompute.check_syscall_mprotect _ eff model) by (rewrite si_sysno; exact Hno).
rewrite ?si_arg0, ?si_arg1, ?si_arg2. reflexivity.
Qed.
Definition mmap_none_model (a n : word) (m : Model) : Model :=
with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
((a, n) :: vm_maps (m_vmmaps m))
((a, n) :: vm_noaccess (m_vmmaps m))
(vm_start_brk (m_vmmaps m))
(vm_brk (m_vmmaps m))
(vm_limit (m_vmmaps m))
(vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
Lemma mmap_none_model_halted : forall a n m, m_halted (mmap_none_model a n m) = m_halted m.
Proof. reflexivity. Qed.
Lemma mmap_none_model_lazy : forall a n m, m_vm_lazy (mmap_none_model a n m) = m_vm_lazy m.
Proof. reflexivity. Qed.
Lemma mmap_none_model_fds : forall a n m, m_fds (mmap_none_model a n m) = m_fds m.
Proof. reflexivity. Qed.
Lemma mmap_none_model_fs : forall a n m, m_fs (mmap_none_model a n m) = m_fs m.
Proof. reflexivity. Qed.
Definition place_ok (hint : word) (m : Model) (a : word) (nZ : Z) : bool :=
(bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
&& (bv_unsigned a + nZ <=? alloc_top (m_vmmaps m))%Z
&& region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ).
Lemma place_not_errno : forall hint m a nZ,
(0 <= nZ)%Z -> place_ok hint m a nZ = true -> errno_ret_in mmap_errnos a = false.
Proof.
intros hint m a nZ Hn H. unfold place_ok in H.
apply andb_prop in H as [H _]. apply andb_prop in H as [H Hc]. apply Z.leb_le in Hc.
apply errno_ret_in_below; [reflexivity|]. alloc_top_bounds. unfold two_pow_64 in *. lia.
Qed.
Lemma grant_ok_place_ok : forall hint m a nZ, grant_ok hint m a nZ = true -> place_ok hint m a nZ = true.
Proof.
intros hint m a nZ H. unfold grant_ok in H. unfold place_ok.
apply andb_prop in H as [H _]. exact H.
Qed.
Lemma place_ok_not_refusable : forall hint m a nZ,
place_ok hint m a nZ = true -> mmap_reserve_refusable m nZ = false.
Proof.
intros hint m a nZ H. unfold place_ok in H. rewrite !andb_true_iff in H. destruct H as [[[H1 H2] H3] H4].
unfold mmap_reserve_refusable. rewrite (vm_find_base_complete (m_vmmaps m) nZ a); [reflexivity|].
unfold vm_base_ok. rewrite H1, H2, H3, H4. reflexivity.
Qed.
Definition mmap_none_J04 (hint : word) (model : Model) (nZ : Z) : Type :=
({e : Z | In e mmap_errnos}
+ {a : word | place_ok hint model a nZ = true})%type.
Lemma mmap_none_wit04 : forall hint model nZ, mmap_none_J04 hint model nZ.
Proof. intros hint model nZ. left. exists ENOMEM. apply ENOMEM_in_mmap_errnos. Qed.
Definition mmap_none_ef04 (regs : bvmap 5 word) (model : Model)
(i : mmap_none_J04 (getr regs 10) model (page_round_up_Z (bv_unsigned (getr regs 11)))) : SyscallEffect :=
match i with
| inl e => mkEffect (errno_ret (proj1_sig e)) [] []
| inr a => mkEffectU (proj1_sig a) [] [] [(proj1_sig a, page_round_up (getr regs 11))] [] []
end.
Definition mmap_none_md04 (regs : bvmap 5 word) (model : Model)
(i : mmap_none_J04 (getr regs 10) model (page_round_up_Z (bv_unsigned (getr regs 11)))) : Model :=
match i with
| inl _ => model
| inr a => mmap_none_model (proj1_sig a) (page_round_up (getr regs 11)) model
end.
Lemma chk_mmap_none04 : forall regs pc mem rom model,
bv_unsigned (getr regs 17) = 222%Z ->
getr regs 11 <> Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 34 ->
getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
forall eff,
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= match eff with
| mkEffectU r [] [] us [] [] =>
if errno_ret_in mmap_errnos r
then match us with [] => CheckOk model [] | _ => CheckReject end
else if place_ok (getr regs 10) model r (page_round_up_Z (bv_unsigned (getr regs 11)))
&& listNN_eqb us [(r, page_round_up (getr regs 11))]
then CheckOk (mmap_none_model r (page_round_up (getr regs 11)) model) [] else CheckReject
| _ => CheckReject
end.
Proof.
intros regs pc mem rom model Hno H1 H2 H3 H4 H5 eff.
rewrite chk222 by exact Hno. unfold check_mmap.
rewrite H2, H3, ?H4, H5.
change (negb (mmap_off_aligned_b (Z_to_bv 64 0))) with false.
change (negb (mmap_anon_b (Z_to_bv 64 34))) with false.
replace (w_is0 (getr regs 11)) with false by (symmetry; unfold w_is0; apply bv_eqb_neq; exact H1).
change (mmap_modeled_b (Z_to_bv 64 0) (Z_to_bv 64 34) (Z_to_bv 64 0)) with false.
change (mmap_noaccess_b (Z_to_bv 64 0) (Z_to_bv 64 34) (Z_to_bv 64 0)) with true.
cbv beta iota. destruct eff as [r ws zs us cs ci].
destruct ws; [|reflexivity]. destruct zs; [|reflexivity].
destruct cs; [|reflexivity]. destruct ci; [|reflexivity]. cbv zeta.
change (with_mmap_backing (Z_to_bv 64 34)) with (fun (_ _ : word) (m : Model) => m). cbv beta.
unfold place_ok, mmap_none_model, page_round_up. reflexivity.
Qed.
Lemma node_mmap_none04 : forall regs pc mem rom model,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 222%Z ->
getr regs 11 <> Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 34 ->
getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
node_ok segs (mkCfg (pend_at regs pc mem rom) model)
(mmap_none_J04 (getr regs 10) model (page_round_up_Z (bv_unsigned (getr regs 11)))) (fun _ => [])
(fun i => mkCfg (advance_past_svc (apply_effect (pend_at regs pc mem rom) (mmap_none_ef04 regs model i)))
(mmap_none_md04 regs model i)).
Proof.
intros regs pc mem rom model Hh Hlz Hno H1 H2 H3 H4 H5.
set (nZ := page_round_up_Z (bv_unsigned (getr regs 11))) in *.
set (n := page_round_up (getr regs 11)) in *.
assert (HnZ : (0 <= nZ)%Z).
{ unfold nZ. apply page_round_up_Z_nonneg. pose proof (u64_range (getr regs 11)). lia. }
pose proof (chk_mmap_none04 regs pc mem rom model Hno H1 H2 H3 H4 H5) as Hchk. fold nZ n in Hchk.
assert (Hbelow : forall a, place_ok (getr regs 10) model a nZ = true -> errno_ret_in mmap_errnos a = false).
{ intros a Ha. apply errno_ret_in_below; [reflexivity|].
unfold place_ok in Ha; rewrite !andb_true_iff in Ha; destruct Ha as [[[_ _] Hc] _].
apply Z.leb_le in Hc; alloc_top_bounds; unfold two_pow_64 in *; lia. }
assert (Hgrant : forall a, place_ok (getr regs 10) model a nZ = true ->
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) (mkEffectU a [] [] [(a, n)] [] []) model
= CheckOk (mmap_none_model a n model) []).
{ intros a Ha. rewrite Hchk, (Hbelow a Ha), Ha, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity. }
assert (Hrb : forall r, refusal_b (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) model r
= errno_ret_in mmap_errnos r).
{ intros r. rewrite (refusal_b_222 (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) model _ Hno). reflexivity. }
apply (node_chk_cfg (pend_at regs pc mem rom) model (getr regs 17) (mmap_none_J04 (getr regs 10) model nZ)
(mmap_none_wit04 (getr regs 10) model nZ) (mmap_none_ef04 regs model) (mmap_none_md04 regs model)
(fun _ => []) Hh eq_refl).
- intros [[e He] | [a Ha]]; unfold mmap_none_ef04, mmap_none_md04; cbn [proj1_sig].
+ rewrite Hchk. rewrite (errno_ret_in_intro _ _ He). reflexivity.
+ apply Hgrant. exact Ha.
- intros [[e He] | [a Ha]]; unfold mmap_none_md04; [exact Hh | rewrite mmap_none_model_halted; exact Hh].
- intros [[e He] | [a Ha]]; unfold mmap_none_md04; [exact Hlz | rewrite mmap_none_model_lazy; exact Hlz].
- intros [r ws zs us cs ci] m' evs Hk. rewrite Hchk in Hk.
destruct ws; [|discriminate]. destruct zs; [|discriminate].
destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
destruct (errno_ret_in mmap_errnos r) eqn:Her.
+ destruct us; [|discriminate].
apply errno_ret_in_true in Her. destruct Her as (e & He & ->).
injection Hk as <- <-.
left. exists (inl (exist _ e He)). unfold mmap_none_ef04, mmap_none_md04; cbn [proj1_sig]. auto.
+ destruct (place_ok (getr regs 10) model r nZ) eqn:Hg; [|discriminate].
destruct (listNN_eqb us [(r, n)]) eqn:Hus; [|discriminate].
apply listNN_eqb_eq in Hus. subst us. cbn [andb] in Hk. inversion Hk; subst.
left. exists (inr (exist _ r Hg)). unfold mmap_none_ef04, mmap_none_md04; cbn [proj1_sig]. auto.
- intros i. apply spurious_refusal_may_fail.
Qed.
Lemma rz_mmap_none_ok : forall regs pc mem rom model B,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 222%Z ->
getr regs 11 <> Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 34 ->
getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
(forall e, In e mmap_errnos ->
realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model) B) ->
(forall a, place_ok (getr regs 10) model a (page_round_up_Z (bv_unsigned (getr regs 11))) = true ->
realizes segs
(mkCfg (mkst (regupd regs 10 a) (v_addi pc 4)
(apply_unmaps mem [(a, page_round_up (getr regs 11))]) rom)
(mmap_none_model a (page_round_up (getr regs 11)) model)) B) ->
(exists a, place_ok (getr regs 10) model a (page_round_up_Z (bv_unsigned (getr regs 11))) = true) ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) B.
Proof.
intros regs pc mem rom model B Hh Hlz Hno H1 H2 H3 H4 H5 HA HB [a0 Ha0].
apply (rz_silent (mkCfg (pend_at regs pc mem rom) model) _ (inr (exist _ a0 Ha0)) _ B
(node_mmap_none04 regs pc mem rom model Hh Hlz Hno H1 H2 H3 H4 H5)).
intros [[e He] | [a Ha]]; unfold mmap_none_ef04, mmap_none_md04; cbn [proj1_sig].
- rewrite adv_pend. cbn [eff_ret]. rewrite effmem_ret_only. apply HA. exact He.
- rewrite adv_pend. cbn [eff_ret]. rewrite effmem_unmaps. apply HB. exact Ha.
Qed.
Definition mmap_fixed_model (a n : word) (m : Model) : Model :=
with_mmap_replacement (Z_to_bv 64 50) a n
(with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
(vm_maps (m_vmmaps m))
((a, n) :: maps_subtract (vm_noaccess (m_vmmaps m))
(bv_unsigned a) (bv_unsigned a + bv_unsigned n))
(vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m))
(vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m).
Definition mmap_fixed_destroyed_model (a n : word) (m : Model) : Model :=
with_mmap_destroyed a n
(mkVmMapsFull (vm_reserved (m_vmmaps m))
(maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
(maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
(vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
Lemma vm_forget_range_halted : forall lo hi m, m_halted (vm_forget_range lo hi m) = m_halted m.
Proof. reflexivity. Qed.
Lemma vm_forget_range_lazy : forall lo hi m,
m_vm_lazy m = [] -> m_vm_lazy (vm_forget_range lo hi m) = [].
Proof. intros lo hi m H. unfold vm_forget_range, with_vm_backing. cbn [m_vm_lazy]. unfold m_vm_lazy in H |- *. cbn. rewrite H. reflexivity. Qed.
Lemma vm_forget_range_fds : forall lo hi m, m_fds (vm_forget_range lo hi m) = m_fds m.
Proof. reflexivity. Qed.
Lemma vm_forget_range_fs : forall lo hi m, m_fs (vm_forget_range lo hi m) = m_fs m.
Proof. reflexivity. Qed.
Lemma vm_forget_range_vmmaps : forall lo hi m, m_vmmaps (vm_forget_range lo hi m) = m_vmmaps m.
Proof. reflexivity. Qed.
Lemma mmap_fixed_model_halted : forall a n m, m_halted (mmap_fixed_model a n m) = m_halted m.
Proof. reflexivity. Qed.
Lemma mmap_fixed_model_lazy : forall a n m, m_vm_lazy m = [] -> m_vm_lazy (mmap_fixed_model a n m) = [].
Proof. intros a n m H. unfold mmap_fixed_model, with_mmap_replacement. cbn. apply vm_forget_range_lazy. exact H. Qed.
Lemma mmap_fixed_model_fds : forall a n m, m_fds (mmap_fixed_model a n m) = m_fds m.
Proof. reflexivity. Qed.
Lemma mmap_fixed_model_fs : forall a n m, m_fs (mmap_fixed_model a n m) = m_fs m.
Proof. reflexivity. Qed.
Lemma mmap_fixed_model_vmmaps : forall a n m,
m_vmmaps (mmap_fixed_model a n m)
= mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
((a, n) :: maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
(vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m))
(vm_init_sp (m_vmmaps m)).
Proof. reflexivity. Qed.
Lemma mmap_fixed_destroyed_model_halted : forall a n m,
m_halted (mmap_fixed_destroyed_model a n m) = m_halted m.
Proof. reflexivity. Qed.
Lemma mmap_fixed_destroyed_model_lazy : forall a n m,
m_vm_lazy m = [] -> m_vm_lazy (mmap_fixed_destroyed_model a n m) = [].
Proof. intros a n m H. unfold mmap_fixed_destroyed_model, with_mmap_destroyed. apply vm_forget_range_lazy. exact H. Qed.
Lemma mmap_fixed_destroyed_model_fds : forall a n m, m_fds (mmap_fixed_destroyed_model a n m) = m_fds m.
Proof. reflexivity. Qed.
Lemma mmap_fixed_destroyed_model_fs : forall a n m, m_fs (mmap_fixed_destroyed_model a n m) = m_fs m.
Proof. reflexivity. Qed.
Lemma mmap_fixed_destroyed_model_vmmaps : forall a n m,
m_vmmaps (mmap_fixed_destroyed_model a n m)
= mkVmMapsFull (vm_reserved (m_vmmaps m))
(maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
(maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
(vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m))
(vm_init_sp (m_vmmaps m)).
Proof. reflexivity. Qed.
Lemma chk_mmap_fixed_none04 : forall regs pc mem rom model,
bv_unsigned (getr regs 17) = 222%Z ->
getr regs 11 <> Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 50 ->
getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
(bv_unsigned (getr regs 10) mod page_size = 0)%Z -> (0 < bv_unsigned (getr regs 10))%Z ->
(bv_unsigned (getr regs 10) + page_round_up_Z (bv_unsigned (getr regs 11)) <= alloc_top (m_vmmaps model))%Z ->
region_free (vm_reserved (m_vmmaps model)) (getr regs 10) (page_round_up (getr regs 11)) = true ->
map_contains (vm_maps (m_vmmaps model)) (getr regs 10) (page_round_up (getr regs 11)) = true ->
forall eff,
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= match eff with
| mkEffectU r [] [] us [] [] =>
if errno_ret_in mmap_errnos r
then match us with
| [] => CheckOk model []
| _ => if listNN_eqb us [(getr regs 10, page_round_up (getr regs 11))]
then CheckOk (mmap_fixed_destroyed_model (getr regs 10) (page_round_up (getr regs 11)) model) []
else CheckReject
end
else if bv_eqb r (getr regs 10) && listNN_eqb us [(getr regs 10, page_round_up (getr regs 11))]
then CheckOk (mmap_fixed_model (getr regs 10) (page_round_up (getr regs 11)) model) []
else CheckReject
| _ => CheckReject
end.
Proof.
intros regs pc mem rom model Hno H1 H2 H3 H4 H5 Hal Hpos Hceil Hfree Hcont eff.
set (addr := getr regs 10) in *.
set (nZ := page_round_up_Z (bv_unsigned (getr regs 11))) in *.
pose proof (alloc_top_room (m_vmmaps model)) as Hroom. pose proof stack_max_size_val as Hsms.
rewrite chk222 by exact Hno. fold addr. unfold check_mmap.
rewrite H2, H3, ?H4, H5.
change (negb (mmap_off_aligned_b (Z_to_bv 64 0))) with false.
change (negb (mmap_anon_b (Z_to_bv 64 50))) with false.
replace (w_is0 (getr regs 11)) with false by (symmetry; unfold w_is0; apply bv_eqb_neq; exact H1).
change (mmap_modeled_b (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 0)) with false.
change (mmap_noaccess_b (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 0)) with false.
change (mmap_fixed_noaccess_b (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 0)) with true.
cbv beta iota zeta. fold nZ.
rewrite (proj2 (Z.leb_gt _ _)) by (unfold two_pow_64 in *; lia).
rewrite (proj2 (Z.leb_le _ _) Hceil). cbn [negb].
rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb].
unfold page_round_up in Hfree, Hcont |- *. fold nZ in Hfree. fold nZ in Hcont. fold nZ.
rewrite Hfree, Hcont. cbn [andb].
destruct eff as [r ws zs us cs ci].
destruct ws; [|reflexivity]. destruct zs; [|reflexivity].
destruct cs; [|destruct us; reflexivity]. destruct ci; [|destruct us; reflexivity].
unfold mmap_fixed_model, mmap_fixed_destroyed_model. reflexivity.
Qed.
Definition mmap_fixed_J04 : Type :=
  ({e : Z | In e mmap_errnos} + (unit + {e : Z | In e mmap_errnos}))%type.
Definition mmap_fixed_ef04 (regs : bvmap 5 word)
    (i : mmap_fixed_J04) : SyscallEffect :=
  match i with
  | inl e => mkEffect (errno_ret (proj1_sig e)) [] []
  | inr (inl _) => mkEffectU (getr regs 10) [] []
      [(getr regs 10, page_round_up (getr regs 11))] [] []
  | inr (inr e) => mkEffectU (errno_ret (proj1_sig e)) [] []
      [(getr regs 10, page_round_up (getr regs 11))] [] []
  end.
Definition mmap_fixed_md04 (regs : bvmap 5 word) (model : Model)
    (i : mmap_fixed_J04) : Model :=
  match i with
  | inl _ => model
  | inr (inl _) => mmap_fixed_model (getr regs 10) (page_round_up (getr regs 11)) model
  | inr (inr _) => mmap_fixed_destroyed_model (getr regs 10) (page_round_up (getr regs 11)) model
  end.
Lemma node_mmap_fixed_none04 : forall regs pc mem rom model,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 222%Z ->
getr regs 11 <> Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 50 ->
getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
(bv_unsigned (getr regs 10) mod page_size = 0)%Z -> (0 < bv_unsigned (getr regs 10))%Z ->
(bv_unsigned (getr regs 10) + page_round_up_Z (bv_unsigned (getr regs 11)) <= alloc_top (m_vmmaps model))%Z ->
region_free (vm_reserved (m_vmmaps model)) (getr regs 10) (page_round_up (getr regs 11)) = true ->
map_contains (vm_maps (m_vmmaps model)) (getr regs 10) (page_round_up (getr regs 11)) = true ->
node_ok segs (mkCfg (pend_at regs pc mem rom) model) mmap_fixed_J04 (fun _ => [])
(fun i => mkCfg (advance_past_svc (apply_effect (pend_at regs pc mem rom) (mmap_fixed_ef04 regs i)))
(mmap_fixed_md04 regs model i)).
Proof.
intros regs pc mem rom model Hh Hlz Hno H1 H2 H3 H4 H5 Hal Hpos Hceil Hfree Hcont.
pose proof (chk_mmap_fixed_none04 regs pc mem rom model Hno H1 H2 H3 H4 H5 Hal Hpos Hceil Hfree Hcont) as Hchk.
assert (Hnot : errno_ret_in mmap_errnos (getr regs 10) = false).
{ apply errno_ret_in_below; [reflexivity|].
  pose proof (page_round_up_Z_nonneg (bv_unsigned (getr regs 11)) ltac:(pose proof (u64_range (getr regs 11)); lia)).
  alloc_top_bounds. unfold two_pow_64 in *. lia. }
apply (node_chk_cfg (pend_at regs pc mem rom) model (getr regs 17)
  mmap_fixed_J04 (inr (inl tt)) (mmap_fixed_ef04 regs)
  (mmap_fixed_md04 regs model) (fun _ => []) Hh eq_refl).
- intros [[e He] | [[] | [e He]]]; unfold mmap_fixed_ef04, mmap_fixed_md04; cbn [proj1_sig]; rewrite Hchk.
  + rewrite (errno_ret_in_intro _ _ He). reflexivity.
  + rewrite Hnot, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
  + rewrite (errno_ret_in_intro _ _ He), (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
- intros [[e He] | [[] | [e He]]]; unfold mmap_fixed_md04;
    rewrite ?mmap_fixed_model_halted, ?mmap_fixed_destroyed_model_halted; exact Hh.
- intros [[e He] | [[] | [e He]]]; unfold mmap_fixed_md04;
    [exact Hlz | apply mmap_fixed_model_lazy | apply mmap_fixed_destroyed_model_lazy]; exact Hlz.
- intros [r ws zs us cs ci] m' evs Hk. rewrite Hchk in Hk.
  destruct ws; [|discriminate]. destruct zs; [|discriminate].
  destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
  destruct (errno_ret_in mmap_errnos r) eqn:Her.
  + apply errno_ret_in_true in Her. destruct Her as (e & He & ->).
    destruct us as [|u us].
    * inversion Hk; subst. left. exists (inl (exist _ e He)).
      unfold mmap_fixed_ef04, mmap_fixed_md04; cbn [proj1_sig]. auto.
    * destruct (listNN_eqb (u :: us) [(getr regs 10, page_round_up (getr regs 11))]) eqn:Hu; [|discriminate].
      apply listNN_eqb_eq in Hu. inversion Hu; subst u us.
      inversion Hk; subst. left. exists (inr (inr (exist _ e He))).
      unfold mmap_fixed_ef04, mmap_fixed_md04; cbn [proj1_sig]. auto.
  + destruct (bv_eqb r (getr regs 10)) eqn:Hr; [|discriminate].
    destruct (listNN_eqb us [(getr regs 10, page_round_up (getr regs 11))]) eqn:Hu; [|discriminate].
    apply bv_eqb_eq in Hr. apply listNN_eqb_eq in Hu. subst.
    cbn [andb] in Hk. inversion Hk; subst. left. exists (inr (inl tt)).
    unfold mmap_fixed_ef04, mmap_fixed_md04; cbn [proj1_sig]. auto.
- intros i. apply spurious_refusal_may_fail.
Qed.
Lemma rz_mmap_fixed_none_ok : forall regs pc mem rom model B,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 222%Z ->
getr regs 11 <> Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 50 ->
getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
(bv_unsigned (getr regs 10) mod page_size = 0)%Z -> (0 < bv_unsigned (getr regs 10))%Z ->
(bv_unsigned (getr regs 10) + page_round_up_Z (bv_unsigned (getr regs 11)) <= alloc_top (m_vmmaps model))%Z ->
region_free (vm_reserved (m_vmmaps model)) (getr regs 10) (page_round_up (getr regs 11)) = true ->
map_contains (vm_maps (m_vmmaps model)) (getr regs 10) (page_round_up (getr regs 11)) = true ->
(forall e, In e mmap_errnos ->
realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model) B) ->
(forall e, In e mmap_errnos ->
realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4)
(apply_unmaps mem [(getr regs 10, page_round_up (getr regs 11))]) rom)
(mmap_fixed_destroyed_model (getr regs 10) (page_round_up (getr regs 11)) model)) B) ->
realizes segs
(mkCfg (mkst (regupd regs 10 (getr regs 10)) (v_addi pc 4)
(apply_unmaps mem [(getr regs 10, page_round_up (getr regs 11))]) rom)
(mmap_fixed_model (getr regs 10) (page_round_up (getr regs 11)) model)) B ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) B.
Proof.
intros regs pc mem rom model B Hh Hlz Hno H1 H2 H3 H4 H5 Hal Hpos Hceil Hfree Hcont HA HC HB.
apply (rz_silent (mkCfg (pend_at regs pc mem rom) model) _ (inr (inl tt)) _ B
(node_mmap_fixed_none04 regs pc mem rom model Hh Hlz Hno H1 H2 H3 H4 H5 Hal Hpos Hceil Hfree Hcont)).
intros [[e He] | [[] | [e He]]]; unfold mmap_fixed_ef04, mmap_fixed_md04; cbn [proj1_sig];
rewrite adv_pend; cbn [eff_ret].
- rewrite effmem_ret_only. apply HA. exact He.
- rewrite effmem_unmaps. exact HB.
- rewrite effmem_unmaps. apply HC. exact He.
Qed.
Definition mprotect_model (a n : word) (m : Model) : Model := mprotect_model_next m a n.
Lemma mprotect_model_halted : forall a n m, m_halted (mprotect_model a n m) = m_halted m.
Proof. reflexivity. Qed.
Lemma mprotect_model_lazy : forall a n m, m_vm_lazy (mprotect_model a n m) = m_vm_lazy m.
Proof. reflexivity. Qed.
Lemma mprotect_model_fds : forall a n m, m_fds (mprotect_model a n m) = m_fds m.
Proof. reflexivity. Qed.
Lemma mprotect_model_fs : forall a n m, m_fs (mprotect_model a n m) = m_fs m.
Proof. reflexivity. Qed.
Lemma mprotect_model_vmmaps : forall a n m,
m_vmmaps (mprotect_model a n m)
= mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
(maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
(vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m))
(vm_init_sp (m_vmmaps m)).
Proof. reflexivity. Qed.
Lemma ENOMEM_in_mprotect_errnos : In ENOMEM mprotect_errnos.
Proof. left. reflexivity. Qed.
Definition mprotect_J04 (model : Model) (addr n : word) : Type :=
({e : Z | In e mprotect_errnos}
+ {_ : unit | mprotect_budget_ok model addr n = true})%type.
Lemma mprotect_wit04 : forall model addr n, mprotect_J04 model addr n.
Proof. intros model addr n. left. exists ENOMEM. apply ENOMEM_in_mprotect_errnos. Qed.
Definition mprotect_ef04 (regs : bvmap 5 word) (model : Model)
(i : mprotect_J04 model (getr regs 10) (page_round_up (getr regs 11))) : SyscallEffect :=
match i with
| inl e => mkEffect (errno_ret (proj1_sig e)) [] []
| inr _ => mkEffect (Z_to_bv 64 0) [] [(getr regs 10, page_round_up (getr regs 11))]
end.
Definition mprotect_md04 (regs : bvmap 5 word) (model : Model)
(i : mprotect_J04 model (getr regs 10) (page_round_up (getr regs 11))) : Model :=
match i with
| inl _ => model
| inr _ => mprotect_model (getr regs 10) (page_round_up (getr regs 11)) model
end.
Lemma chk_mprotect_rw04 : forall regs pc mem rom model,
bv_unsigned (getr regs 17) = 226%Z ->
(bv_unsigned (getr regs 10) mod page_size = 0)%Z ->
getr regs 11 <> Z_to_bv 64 0 ->
(bv_unsigned (getr regs 10) + page_round_up_Z (bv_unsigned (getr regs 11)) < two_pow_64)%Z ->
getr regs 12 = Z_to_bv 64 3 ->
map_contains (vm_noaccess (m_vmmaps model)) (getr regs 10) (page_round_up (getr regs 11)) = true ->
map_contains (vm_maps (m_vmmaps model)) (getr regs 10) (page_round_up (getr regs 11)) = true ->
forall eff,
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= match eff with
| mkEffectU r [] zs [] [] [] =>
if errno_ret_in mprotect_errnos r
then match zs with [] => CheckOk model [] | _ => CheckReject end
else if mprotect_budget_ok model (getr regs 10) (page_round_up (getr regs 11))
&& w_is0 r && listNN_eqb zs [(getr regs 10, page_round_up (getr regs 11))]
then CheckOk (mprotect_model (getr regs 10) (page_round_up (getr regs 11)) model) []
else CheckReject
| _ => CheckReject
end.
Proof.
intros regs pc mem rom model Hno Hal Hlen Hnw Hprot Hna Hma eff.
set (addr := getr regs 10) in *.
set (nZ := page_round_up_Z (bv_unsigned (getr regs 11))) in *.
rewrite chk226 by exact Hno. fold addr. rewrite Hprot. unfold check_mprotect.
change (mprotect_grows_conflict_b (Z_to_bv 64 3)) with false.
change (mprotect_modeled_b (Z_to_bv 64 3)) with true.
rewrite (proj2 (Z.eqb_eq _ _) Hal). unfold w_is0 at 1. rewrite (bv_eqb_neq _ _ Hlen).
cbn [negb]. fold nZ. rewrite (proj2 (Z.leb_gt _ _) Hnw). cbv beta iota zeta. fold nZ.
unfold page_round_up in Hna, Hma |- *. fold nZ in Hna. fold nZ in Hma. fold nZ.
rewrite Hna, Hma. cbn [andb].
destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
destruct us; [|reflexivity]. destruct cs; [|reflexivity]. destruct ci; [|reflexivity].
unfold mprotect_model. reflexivity.
Qed.
Lemma node_mprotect_rw04 : forall regs pc mem rom model,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 226%Z ->
(bv_unsigned (getr regs 10) mod page_size = 0)%Z ->
getr regs 11 <> Z_to_bv 64 0 ->
(bv_unsigned (getr regs 10) + page_round_up_Z (bv_unsigned (getr regs 11)) < two_pow_64)%Z ->
getr regs 12 = Z_to_bv 64 3 ->
map_contains (vm_noaccess (m_vmmaps model)) (getr regs 10) (page_round_up (getr regs 11)) = true ->
map_contains (vm_maps (m_vmmaps model)) (getr regs 10) (page_round_up (getr regs 11)) = true ->
node_ok segs (mkCfg (pend_at regs pc mem rom) model)
(mprotect_J04 model (getr regs 10) (page_round_up (getr regs 11))) (fun _ => [])
(fun i => mkCfg (advance_past_svc (apply_effect (pend_at regs pc mem rom) (mprotect_ef04 regs model i)))
(mprotect_md04 regs model i)).
Proof.
intros regs pc mem rom model Hh Hlz Hno Hal Hlen Hnw Hprot Hna Hma.
pose proof (chk_mprotect_rw04 regs pc mem rom model Hno Hal Hlen Hnw Hprot Hna Hma) as Hchk.
assert (Hrb : forall r, refusal_b (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) model r
= errno_ret_in mprotect_errnos r).
{ intros r. rewrite (refusal_b_226 (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) model _ Hno). reflexivity. }
assert (Hz : errno_ret_in mprotect_errnos (Z_to_bv 64 0) = false) by reflexivity.
assert (Hsucc : mprotect_budget_ok model (getr regs 10) (page_round_up (getr regs 11)) = true ->
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17))
(mkEffect (Z_to_bv 64 0) [] [(getr regs 10, page_round_up (getr regs 11))]) model
= CheckOk (mprotect_model (getr regs 10) (page_round_up (getr regs 11)) model) []).
{ intros Hb. rewrite Hchk, Hz, Hb. change (w_is0 (Z_to_bv 64 0)) with true.
rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity. }
apply (node_chk_cfg (pend_at regs pc mem rom) model (getr regs 17) _
(mprotect_wit04 model (getr regs 10) (page_round_up (getr regs 11)))
(mprotect_ef04 regs model) (mprotect_md04 regs model) (fun _ => []) Hh eq_refl).
- intros [[e He] | [[] Hb]]; unfold mprotect_ef04, mprotect_md04; cbn [proj1_sig].
+ rewrite Hchk. rewrite (errno_ret_in_intro _ _ He). reflexivity.
+ apply Hsucc. exact Hb.
- intros [[e He] | [[] Hb]]; unfold mprotect_md04; [exact Hh | rewrite mprotect_model_halted; exact Hh].
- intros [[e He] | [[] Hb]]; unfold mprotect_md04; [exact Hlz | rewrite mprotect_model_lazy; exact Hlz].
- intros [r ws zs us cs ci] m' evs Hk. rewrite Hchk in Hk.
destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
destruct (errno_ret_in mprotect_errnos r) eqn:Her.
+ destruct zs; [|discriminate].
apply errno_ret_in_true in Her. destruct Her as (e & He & ->).
injection Hk as <- <-.
left. exists (inl (exist _ e He)). unfold mprotect_ef04, mprotect_md04; cbn [proj1_sig]. auto.
+ cbv beta iota in Hk.
destruct (mprotect_budget_ok model (getr regs 10) (page_round_up (getr regs 11))) eqn:Hb;
[|cbn [andb] in Hk; discriminate Hk].
cbn [andb] in Hk.
destruct (w_is0 r) eqn:Hr; [|discriminate].
destruct (listNN_eqb zs [(getr regs 10, page_round_up (getr regs 11))]) eqn:Hzs; [|discriminate].
unfold w_is0 in Hr. apply bv_eqb_eq in Hr. apply listNN_eqb_eq in Hzs. subst.
cbn [andb] in Hk. inversion Hk; subst. left. exists (inr (exist _ tt Hb)). unfold mprotect_ef04, mprotect_md04. auto.
- intros i. apply spurious_refusal_may_fail.
Qed.
Lemma rz_mprotect_rw_ok : forall regs pc mem rom model B,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 226%Z ->
(bv_unsigned (getr regs 10) mod page_size = 0)%Z ->
getr regs 11 <> Z_to_bv 64 0 ->
(bv_unsigned (getr regs 10) + page_round_up_Z (bv_unsigned (getr regs 11)) < two_pow_64)%Z ->
getr regs 12 = Z_to_bv 64 3 ->
map_contains (vm_noaccess (m_vmmaps model)) (getr regs 10) (page_round_up (getr regs 11)) = true ->
map_contains (vm_maps (m_vmmaps model)) (getr regs 10) (page_round_up (getr regs 11)) = true ->
mprotect_budget_ok model (getr regs 10) (page_round_up (getr regs 11)) = true ->
(forall e, In e mprotect_errnos ->
realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model) B) ->
realizes segs
(mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
(apply_zeros mem [(getr regs 10, page_round_up (getr regs 11))]) rom)
(mprotect_model (getr regs 10) (page_round_up (getr regs 11)) model)) B ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) B.
Proof.
intros regs pc mem rom model B Hh Hlz Hno Hal Hlen Hnw Hprot Hna Hma Hbud HA HB.
apply (rz_silent (mkCfg (pend_at regs pc mem rom) model) _ (inr (exist _ tt Hbud)) _ B
(node_mprotect_rw04 regs pc mem rom model Hh Hlz Hno Hal Hlen Hnw Hprot Hna Hma)).
intros [[e He] | [[] Hb]]; unfold mprotect_ef04, mprotect_md04; cbn [proj1_sig].
- rewrite adv_pend. cbn [eff_ret]. rewrite effmem_ret_only. apply HA. exact He.
- rewrite adv_pend. cbn [eff_ret]. rewrite effmem_zeros. exact HB.
Qed.
End g.
Lemma pend_read_byte_mrb : forall segs regs pc mem,
ms_read_byte (pend_at regs pc mem (seg_rom segs)) = mrb segs mem.
Proof. reflexivity. Qed.
Lemma pend_read_bytes_rdn : forall segs regs pc mem a n,
ms_read_bytes (pend_at regs pc mem (seg_rom segs)) a n = rdn segs mem a (word_to_nat n).
Proof. intros. apply ms_read_bytes_rdn. reflexivity. Qed.
Lemma pend_read_u64_rdn : forall segs regs pc mem a,
ms_read_u64 (pend_at regs pc mem (seg_rom segs)) a
= match rdn segs mem a 8 with Some bs => Some (le_bytes_to_word bs) | None => None end.
Proof.
intros. unfold ms_read_u64. rewrite pend_read_bytes_rdn.
change (word_to_nat (Z_to_bv 64 8)) with 8%nat. reflexivity.
Qed.
Lemma apply_zeros1_in : forall mem (a n x : word),
(bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n)%Z ->
apply_zeros mem [(a, n)] x = Some (Z_to_bv 8 0).
Proof.
intros mem a n x Hx. cbn [apply_zeros zeros_cover existsb fst snd].
rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.
Lemma apply_zeros1_out : forall mem (a n x : word),
(bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
apply_zeros mem [(a, n)] x = mem x.
Proof.
intros mem a n x Hx. cbn [apply_zeros zeros_cover existsb fst snd].
destruct Hx as [Hx | Hx].
- rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
- rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite andb_false_r. reflexivity.
Qed.
Lemma apply_unmaps1_in : forall mem (a n x : word),
(bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n)%Z ->
apply_unmaps mem [(a, n)] x = None.
Proof.
intros mem a n x Hx. cbn [apply_unmaps zeros_cover existsb fst snd].
rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.
Lemma apply_unmaps1_out : forall mem (a n x : word),
(bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
apply_unmaps mem [(a, n)] x = mem x.
Proof.
intros mem a n x Hx. cbn [apply_unmaps zeros_cover existsb fst snd].
destruct Hx as [Hx | Hx].
- rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
- rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite andb_false_r. reflexivity.
Qed.
Lemma apply_zeros_one' : forall mem (a n : word), apply_zeros mem [(a, n)] = zmem mem a n.
Proof. intros. apply apply_zeros_one. Qed.
Lemma apply_unmaps_one : forall mem (a n : word), apply_unmaps mem [(a, n)] = unfill a n mem.
Proof.
intros mem a n. apply functional_extensionality. intro x.
unfold apply_unmaps, zeros_cover, unfill. cbn [existsb fst snd].
rewrite orb_false_r. reflexivity.
Qed.
Lemma page_round_up_unsigned : forall len : word,
(page_round_up_Z (bv_unsigned len) < 2 ^ 64)%Z ->
bv_unsigned (page_round_up len) = page_round_up_Z (bv_unsigned len).
Proof.
intros len H. unfold page_round_up. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
apply Z.mod_small. split; [|exact H].
apply page_round_up_Z_nonneg. pose proof (u64_range len). lia.
Qed.
Lemma page_round_up_Z_pos : forall len : word,
len <> Z_to_bv 64 0 -> (0 < page_round_up_Z (bv_unsigned len))%Z.
Proof.
intros len H. pose proof (u64_range len) as Hr.
assert (Hnz : bv_unsigned len <> 0%Z).
{ intro E. apply H. apply bv_eq. rewrite E. reflexivity. }
pose proof (page_round_up_Z_bounds (bv_unsigned len) ltac:(lia)). lia.
Qed.
End f.
