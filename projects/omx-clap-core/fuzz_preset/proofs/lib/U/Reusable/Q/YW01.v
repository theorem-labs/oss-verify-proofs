(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK15 YK0n YK0v YK02 YP0n YM06 YM02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable.Q Require Import YW00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YN02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section b.
Variable segs : list Segment.
Lemma knode_mremap : forall regs pc mem rom model snap (r : nat) (ol nl : Z) (Kont : Z -> config -> Prop),
m_halted model = None ->
mremap_args regs model ->
(forall e, In e mremap_errnos ->
Kont 0 (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model)) ->
(forall eff m',
mremap_chk_body (getr regs 10) (getr regs 11) (getr regs 12) model eff = CheckOk m' [] ->
errno_ret_in mremap_errnos (eff_ret eff) = false ->
Kont 1 (mkCfg (mkst (regupd regs 10 (eff_ret eff)) (v_addi pc 4) (effmem mem eff) rom) m')) ->
knode segs (mkCfg (pend_at regs pc mem rom) model) (KMremap r ol nl) snap Kont.
Proof.
intros regs pc mem rom model snap r ol nl Kont Hh HA HK0 HK1.
destruct (mremap_J_inh segs regs pc mem rom model HA) as [j0].
apply (knode_fallible segs _ (KMremap r ol nl) snap Kont _
(mremap_nx segs regs pc mem rom model) (mremap_bit segs regs pc mem rom model) j0).
- reflexivity.
- reflexivity.
- apply node_mremap; assumption.
- apply mremap_bit_01.
- intros Hm. exfalso. exact Hm.
- intros [[eff m'] [Hk Hns0]]. unfold mremap_bit, mremap_nx. cbn [proj1_sig fst snd] in *.
destruct (errno_ret_in mremap_errnos (eff_ret eff)) eqn:Her.
+
destruct (mremap_ok_cases (getr regs 10) (getr regs 11) (getr regs 12) model eff m' (ma_neq _ _ HA) Hk)
as [(e & He & -> & ->) | (Hno & _)].
* cbn [eff_ret]. rewrite effmem_unmaps. cbn [apply_unmaps]. apply HK0. exact He.
* cbn [fst] in Hno. congruence.
+ apply HK1; assumption.
Qed.
Lemma knode_mremap_cases : forall regs pc mem rom model snap (r : nat) (ol nl : Z) (Kont : Z -> config -> Prop),
m_halted model = None ->
mremap_args regs model ->
let old := getr regs 10 in let old_n := getr regs 11 in let new_n := getr regs 12 in
(forall e, In e mremap_errnos ->
Kont 0 (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model)) ->
(forall mem',
mremap_post_mem mem mem' (bv_unsigned old) (bv_unsigned old_n) (bv_unsigned old) (bv_unsigned new_n) ->
bv_unsigned old + bv_unsigned new_n <= alloc_top (m_vmmaps model) ->
region_free (vm_reserved (m_vmmaps model) ++ map_remove (vm_maps (m_vmmaps model)) old) old new_n = true
\/ bv_unsigned new_n < bv_unsigned old_n ->
Kont 1 (mkCfg (mkst (regupd regs 10 old) (v_addi pc 4) mem' rom)
(mremap_model_next model old old_n old new_n))) ->
(forall dst mem',
bv_unsigned old_n < bv_unsigned new_n ->
mremap_fresh_b model (bv_unsigned old_n) (bv_unsigned new_n) old old_n dst new_n = true ->
mremap_post_mem mem mem' (bv_unsigned old) (bv_unsigned old_n) (bv_unsigned dst) (bv_unsigned new_n) ->
Kont 1 (mkCfg (mkst (regupd regs 10 dst) (v_addi pc 4) mem' rom)
(mremap_model_next model old old_n dst new_n))) ->
knode segs (mkCfg (pend_at regs pc mem rom) model) (KMremap r ol nl) snap Kont.
Proof.
intros regs pc mem rom model snap r ol nl Kont Hh HA old old_n new_n HK0 HKin HKmv.
apply knode_mremap; [exact Hh | exact HA | exact HK0 |].
intros eff m' Hk Hno.
destruct (mremap_ok_cases old old_n new_n model eff m' (ma_neq _ _ HA) Hk)
as [(e & He & -> & ->) | (_ & [(Hlt & -> & ->) | [(Hlt & Hg & -> & ->) | (dst & Hlt & Hne & Hf & -> & ->)]])].
- exfalso. cbn [eff_ret] in Hno. rewrite (errno_ret_in_intro _ _ He) in Hno. discriminate.
- cbn [eff_ret]. apply HKin.
+ apply (mremap_mem_shrink (m_vmmaps model)); [exact Hlt | exact (ma_ceiling _ _ HA)].
+ pose proof (ma_ceiling _ _ HA). unfold old, new_n, old_n in *. lia.
+ right. exact Hlt.
- cbn [eff_ret]. destruct (mremap_inplace_grow_facts model old old_n new_n Hg) as (Hce & Hrf & _).
apply HKin.
+ apply (mremap_mem_grow (m_vmmaps model)); [exact Hlt | exact Hce].
+ exact Hce.
+ left. exact Hrf.
- cbn [eff_ret]. destruct (mremap_fresh_facts model old old_n dst new_n Hf) as (_ & _ & _ & Hce & _ & _).
apply HKmv; [exact Hlt | exact Hf |].
apply (mremap_mem_move (m_vmmaps model)); [exact Hlt | exact (ma_ceiling _ _ HA) | exact Hce |].
apply (mremap_fresh_disjoint model old old_n dst new_n (ma_has _ _ HA) (ma_oldn_pos _ _ HA) (ma_newn_pos _ _ HA) Hf).
Qed.
End b.
End a.
