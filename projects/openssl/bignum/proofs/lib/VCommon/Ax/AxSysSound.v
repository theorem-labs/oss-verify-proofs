(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import PropExec FastWord FastWordSem ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxLin AxVal AxBytes AxMem AxZZ AxState AxEntryRel AxSys AxOcc AxFresh AsanWAcc AsanWLazy AxSysNode.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxModelRel.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Definition eff_mem (m : word -> option byte) (eff : SyscallEffect) : word -> option byte :=
  apply_writes (apply_copies m (apply_zeros (apply_unmaps m (eff_unmaps eff)) (eff_zeros eff)) (eff_copies eff)) (eff_writes eff).

Lemma adv_effect (ms : machine_state) (eff : SyscallEffect) :
  advance_past_svc (apply_effect (latch ms) eff)
  = setx ms (Z_to_bv 5 10) (eff_ret eff) (ms_pc_val ms + Z_to_bv 64 4)%bv (ms_resv ms) (eff_mem (ms_mem ms) eff).
Proof. reflexivity. Qed.

Lemma eff_mem_ret (m : word -> option byte) (r : word) : eff_mem m (mkEffect r [] []) = m.
Proof. reflexivity. Qed.

Lemma eff_mem_zeros (m : word -> option byte) (r : word) (zs : list (word * word)) : eff_mem m (mkEffect r [] zs) = apply_zeros m zs.
Proof. reflexivity. Qed.

Lemma eff_mem_unmaps (m : word -> option byte) (r : word) (us : list (word * word)) : eff_mem m (mkEffectU r [] [] us [] []) = apply_unmaps m us.
Proof. reflexivity. Qed.

Section Post.
Variable segs : list Segment.
Variable LIM : Z.
Variable fs0 : Fs.Fs.

Notation MRm := (MR segs fs0).
Notation RR ρ := (R segs amodel (MRm ρ) LIM ρ).

Lemma R_sys_post (ρ : valuation) (A B : AST) (ms : machine_state) (model m' : Model) (ret : word) (rv : xv) (mem' : word -> option byte) :
  RR ρ A (mkCfg ms model) ->
  a_pc B = npc A -> pc_ok (npc A) = true -> a_regs B = aset (a_regs A) reg_a0 rv -> a_resv B = a_resv A ->
  xv_val ρ rv ret -> sat ρ (a_facts B) -> MRm ρ (a_model B) m' -> m_halted m' = None ->
  vm_backing_used m' <= a_budget B -> vm_limit (m_vmmaps m') = LIM ->
  RMem segs ρ (a_mem B) mem' -> hs_ok ρ (a_mem B) mem' -> mem_cov segs m' mem' -> comp_inv segs ρ (a_mem B) m' -> na_ok segs ρ (a_mem B) m' mem' ->
  RR ρ B (mkCfg (setx ms (Z_to_bv 5 10) ret (ms_pc_val ms + Z_to_bv 64 4)%bv (ms_resv ms) mem') m').
Proof.
  intros HR Epc Hok Eregs Eresv Hv Hsat HM Hh Hb Hl HRM Hhs Hcov Hcomp Hna.
  destruct HR as [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15]. cbn [cfg_ms cfg_model] in *.
  constructor; cbn [cfg_ms cfg_model setx ms_pc_val ms_svc_pending ms_rom ms_mem ms_resv]; try assumption.
  - rewrite Epc. unfold npc. rewrite wbv_add, H1, wbv_four. reflexivity.
  - rewrite Epc. exact (pc_ok_spec _ Hok).
  - reflexivity.
  - rewrite Eregs. change reg_a0 with (ri (Z_to_bv 5 10)). apply RRegs_set; assumption.
  - rewrite Eresv. exact H5.
  - split; assumption.
Qed.

Lemma R_reg_sys (ρ : valuation) (A B : AST) (ms : machine_state) (model m' : Model) (ret : word) (rv : xv) :
  RR ρ A (mkCfg ms model) ->
  a_pc B = npc A -> pc_ok (npc A) = true -> a_regs B = aset (a_regs A) reg_a0 rv -> a_resv B = a_resv A -> a_mem B = a_mem A ->
  xv_val ρ rv ret -> sat ρ (a_facts B) -> MRm ρ (a_model B) m' -> m_halted m' = None ->
  vm_backing_used m' <= a_budget B -> vm_limit (m_vmmaps m') = LIM -> m_vmmaps m' = m_vmmaps model ->
  RR ρ B (mkCfg (advance_past_svc (apply_effect (latch ms) (mkEffect ret nil nil))) m').
Proof.
  intros HR Epc Hok Eregs Eresv Emem Hv Hsat HM Hh Hb Hl Ev. rewrite adv_effect, eff_mem_ret. cbn [eff_ret].
  pose proof HR as [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15]. cbn [cfg_ms cfg_model] in *.
  apply (R_sys_post ρ A B ms model m' ret rv (ms_mem ms) HR); try assumption; rewrite ?Emem; try assumption.
  - unfold mem_cov in *. rewrite Ev. exact H13.
  - unfold comp_inv in *. rewrite Ev. exact H14.
  - unfold na_ok in *. rewrite Ev. exact H15.
Qed.

End Post.

Section SetTid.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIM : Z.
Variable fs0 : Fs.Fs.
Variable KT : valuation -> list byte -> TSet.
Hypothesis KT_agree : forall ρ ρ' o, (forall x, entry_var x = true -> ρ' x = ρ x) -> KT ρ' o = KT ρ o.

Notation MRm := (MR segs fs0).
Notation RR ρ := (R segs amodel (MRm ρ) LIM ρ).
Notation Snd B := (forall ρ c, RR ρ B c -> forall o, out_val ρ B o -> realizes_cfg segs cfg c (KT ρ o)).

Lemma R_agree_h : forall v ρ ρ' (A : AST) c, (forall x, x <> v -> ρ' x = ρ x) -> state_occ v A = false -> RR ρ A c -> RR ρ' A c.
Proof. intros v ρ ρ' A c Hag Ho HR. exact (R_agree segs LIM MRm (MR_agree segs fs0) v ρ ρ' A c Hag Ho HR). Qed.

Lemma with_tid_fields (y : word) (m : Model) :
  m_vmmaps (with_tid y m) = m_vmmaps m /\ m_halted (with_tid y m) = m_halted m /\ vm_backing_used (with_tid y m) = vm_backing_used m.
Proof. repeat split; reflexivity. Qed.

Theorem sys_set_tid_sound (A : AST) (l : list AST) :
  pc_ok (npc A) = true -> xlit (aget (a_regs A) 17%uint63) = Some 96 -> state_occ (am_next (a_model A)) A = false ->
  sys_set_tid A = Some l -> (forall B, In B l -> Snd B) ->
  forall ρ c, RR ρ A c -> (exists w, fetch_word segs (ms_pc_val (cfg_ms c)) = Some w /\ is_ecall w = true) ->
  forall o, out_val ρ A o -> realizes_cfg segs cfg c (KT ρ o).
Proof.
  intros Hpc H17x Hfresh Hs HS ρ [ms model] HR [w [Hf He]] o Ho. unfold sys_set_tid in Hs.
  destruct (am_tid (a_model A)) as [t0|] eqn:Etid; [discriminate Hs|]. injection Hs as <-.
  set (t := am_next (a_model A)) in *. set (v := XS [(t, 1)] w_zero).
  pose proof HR as [Hpc0 Hal Hsvc Hregs Hres Hrom Hmem HM Hh [Hb Hl] Hsat Hhs Hcov Hcomp Hna]. cbn [cfg_ms cfg_model] in *.
  assert (H17 : bv_unsigned (rg ms (Z_to_bv 5 17)) = 96) by exact (reg_lit ρ _ ms (Z_to_bv 5 17) 17%uint63 96 Hregs eq_refl H17x).
  assert (Hmt : m_tid model = None) by (pose proof (mr_tid segs fs0 ρ _ _ HM) as X; rewrite Etid in X; exact X).
  apply (rzc_latch segs cfg ms model w _ Hh Hsvc Hf He).
  apply (rzc_sys_silent segs cfg (latch ms) model (rg ms (Z_to_bv 5 17)) (KT ρ o) Hh eq_refl).
  - rewrite (check_syscall_96 segs _ _ _ _ H17). unfold check_set_tid_address. rewrite Hmt. cbn. discriminate.
  - intros eff m' evs Hc. rewrite (check_syscall_96 segs _ _ _ _ H17) in Hc. unfold check_set_tid_address in Hc. rewrite Hmt in Hc.
    destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate Hc]. destruct zs; [|discriminate Hc]. destruct us; [|discriminate Hc].
    destruct cs; [|discriminate Hc]. destruct ci; [|discriminate Hc].
    match type of Hc with (if ?c then _ else _) = _ => destruct c; [|discriminate Hc] end. injection Hc as <- <-.
    split; [reflexivity | exact Hh].
  - exists (mkEffect (Z_to_bv 64 1) [] []), (with_tid (Z_to_bv 64 1) model). split.
    + rewrite (check_syscall_96 segs _ _ _ _ H17). unfold check_set_tid_address. rewrite Hmt. reflexivity.
    + apply refusal_b_uninjected; [rewrite H17; lia | rewrite H17; reflexivity].
  - intros eff m' Hc _. rewrite (check_syscall_96 segs _ _ _ _ H17) in Hc. unfold check_set_tid_address in Hc. rewrite Hmt in Hc.
    destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate Hc]. destruct zs; [|discriminate Hc]. destruct us; [|discriminate Hc].
    destruct cs; [|discriminate Hc]. destruct ci; [|discriminate Hc].
    match type of Hc with (if ?c then _ else _) = _ => destruct c eqn:Er; [|discriminate Hc] end. injection Hc as <-.
    apply andb_prop in Er as [R1 R2]. apply Z.ltb_lt in R1. apply Z.ltb_lt in R2.
    exists (with_tid r model). split; [apply AxSysMmap.materialize_nil|].
    set (ρ' := upd_val ρ t (bv_unsigned r)).
    assert (Hag : forall x, x <> t -> ρ' x = ρ x) by exact (upd_val_agree ρ t (bv_unsigned r)).
    pose proof (R_agree_h t ρ ρ' A _ Hag Hfresh HR) as HR'.
    pose proof HR' as [_ _ _ _ _ _ _ HM' _ _ Hsat' _ _ _ _]. cbn [cfg_ms cfg_model] in *.
    destruct (with_tid_fields r model) as (Ev & Eh & Eb).
    rewrite <- (KT_agree ρ ρ' o (agree_entry t ρ ρ' Hag (occ_entry t A Hfresh))).
    refine (HS _ (or_introl eq_refl) ρ' _ _ o (out_agree t ρ ρ' A o Hag Hfresh Ho)).
    assert (Et : ρ' t = bv_unsigned r) by (unfold ρ'; apply upd_val_same).
    assert (Hv : xv_val ρ' v r).
    { unfold v. cbn [xv_val]. unfold smod. cbn [teval]. rewrite Et. change (wZ w_zero) with 0.
      pose proof (bv_unsigned_in_range 64 r) as Hr. change (bv_modulus 64) with two64 in Hr. rewrite Z.mod_small by lia. lia. }
    apply (R_reg_sys segs LIM fs0 ρ' A _ ms model (with_tid r model) r v HR'); try reflexivity; try assumption.
    + cbn [with_model a_facts]. apply sat_sadd; [exact Hsat'|]. rewrite leval_lvar, Et.
      unfold PIDMAX. change PID_MAX_ENVELOPE with 4194304 in R2. lia.
    + cbn [with_model a_model]. apply MR_tid; [exact HM' | exact Hv].
Qed.

End SetTid.
