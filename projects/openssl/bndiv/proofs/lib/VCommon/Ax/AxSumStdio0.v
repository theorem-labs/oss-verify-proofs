(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxAcct.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import
  PropExec SimInv ExitSim CatSim CatExec SeqExec StreamExec FileSim ShapeAlg ShapeAlgCfg Nodes AgentLib AgentNodes
  Hoare StoreOk LibWritev NodesCfg LibWritevCfg FastWord FastWordSem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Cli Require Import CliSpecG.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxLazy AxLin AxRel AxVal AxBytes AxMem AxZZ AxBg AxState AxStep AxSys AxJoinSound AxEntryRel AxEntryAg AsanWLazy AsanWAcc AsanWBase AsanWSys AsanWWritev AxSysNode AxSum.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxModelRel AxFd AxSysSound AxSumLibc AxSumStr AxSumMem AxSumStdio.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Spec.
Context {asanreflect_fx : PropExec.FPState}.
Variable segs : list Segment.

Lemma writev_check_zero : forall ms x8 model (fd : Z) (iov : word) iovs,
  ms_rom ms = seg_rom segs ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (0 < fd < 2^31)%Z ->
  bv_unsigned x8 = 66%Z ->
  ms_gpr ms 0 = Z_to_bv 64 fd ->
  ms_gpr ms 1 = iov ->
  ms_gpr ms 2 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
  (1 <= length iovs <= 1024)%nat ->
  (bv_unsigned iov + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
  iov_array segs (ms_mem ms) iov iovs ->
  iov_bufs_ok iovs ->
  iovs_total iovs = 0 ->
  forall eff, check_syscall (sys_input segs ms x8) eff model
    = check_ret_only_copyins (import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs)))) eff (Z_to_bv 64 0) model [].
Proof.
  intros ms x8 model fd iov iovs Hrom Hfd Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Htot eff.
  rewrite (check_syscall_writev (sys_input segs ms x8) eff model) by (rewrite in_sysno_si; exact Hno).
  rewrite in_arg0_si, in_arg1_si, in_arg2_si, H0, H1, H2.
  rewrite fd32_id by (rewrite u64_lit; lia).
  assert (Hcnt32 : iovcnt32 (Z_to_bv 64 (Z.of_nat (length iovs))) = Z_to_bv 64 (Z.of_nat (length iovs))).
  { unfold iovcnt32, abi_low32. rewrite u64_lit by lia. rewrite Z.mod_small by lia. reflexivity. }
  unfold check_writev. rewrite Hfd.
  replace (w_is0 (Z_to_bv 64 fd)) with false by (symmetry; apply w_is0_pos; rewrite u64_lit; lia).
  rewrite in_mem_si, Hcnt32.
  rewrite (import_iovecs_of_array segs ms iovs iov Hrom Hcnt Hiok Harr Hbok).
  assert (Hcap : cap_iovecs iovs = iovs) by (unfold cap_iovecs; apply cap_iovecs_id; unfold MAX_RW_COUNT; lia).
  cbv beta iota zeta. rewrite Hcap, Htot. reflexivity.
Qed.

End Spec.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sum_stdio0 (segs : list Segment) (A : AST) : option (list AST) :=
  let s := a_facts A in
  let regs := a_regs A in
  match xlit (aget regs 17%uint63), xlit (aget regs 10%uint63), aget regs 11%uint63, xlit (aget regs 12%uint63), find_entry (a_mem A) with
  | Some a7, Some fd, XS ts o, Some cnt, Some ph =>
      if (a7 =? 66) &&& (fd =? 2) &&& (cnt =? 1) &&& teqb ts sp_terms &&& (- 8388608 <=? wS o) &&& (wS o + 16 <=? 0)
         &&& atop_is_sp (a_model A) &&& pc_ok (npc A) &&& words_ok_f segs (wZ (a_pc A)) [(0, 0x73)] then
        match ent_words segs s (a_mem A) (XS ts o) 0 with
        | Some (vb, XL w) =>
            match xaddr vb with
            | Some (tb, ob) =>
                if (wZ w =? 0) &&& rbetween 2 s (wS ob, tb) 0 140737488355328 then
                  Some [with_model A (npc A) (aset regs reg_a0 (XL w_zero)) (a_mem A) s (a_model A) (a_budget A)]
                else None
            | None => None
            end
        | _ => None
        end
      else None
  | _, _, _, _, _ => None
  end.

Section Stdio0Sound.
Context {asanreflect_fx : PropExec.FPState}.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIM : Z.
Variable fs0 : Fs.Fs.
Variable KT : valuation -> list byte -> TSet.
Hypothesis Hlow : segs_low segs.

Notation Snd := (Sound segs cfg LIM (MR segs fs0) KT).

Theorem sum_stdio0_sound (A : AST) (l : list AST) : sum_stdio0 segs A = Some l -> (forall B, In B l -> Snd B) -> Snd A.
Proof.
  intros Hs HS ρ [ms model] HR o' Ho. unfold sum_stdio0 in Hs. cbv zeta in Hs.
  destruct (xlit (aget (a_regs A) 17%uint63)) as [a7|] eqn:E17; [|discriminate].
  destruct (xlit (aget (a_regs A) 10%uint63)) as [fd|] eqn:E10; [|discriminate].
  destruct (aget (a_regs A) 11%uint63) as [| ts o | | | |] eqn:E11; try discriminate.
  destruct (xlit (aget (a_regs A) 12%uint63)) as [cnt|] eqn:E12; [|discriminate].
  destruct (find_entry (a_mem A)) as [ph|] eqn:Efe; [|discriminate].
  destruct (a7 =? 66) eqn:Ea7; [|discriminate]. apply Z.eqb_eq in Ea7. subst a7.
  destruct (fd =? 2) eqn:Efd; [|discriminate]. apply Z.eqb_eq in Efd. subst fd.
  destruct (cnt =? 1) eqn:Ecnt; [|discriminate]. apply Z.eqb_eq in Ecnt. subst cnt.
  destruct (teqb ts sp_terms) eqn:Ets; [|discriminate]. apply teqb_eq in Ets. subst ts.
  destruct (- 8388608 <=? wS o) eqn:Eo1; [|discriminate]. apply Z.leb_le in Eo1.
  destruct (wS o + 16 <=? 0) eqn:Eo2; [|discriminate]. apply Z.leb_le in Eo2.
  destruct (atop_is_sp (a_model A)) eqn:Eat; [|discriminate].
  destruct (pc_ok (npc A)) eqn:Epc; [|discriminate].
  destruct (words_ok_f segs (wZ (a_pc A)) [(0, 0x73)]) eqn:HW; [|discriminate]. apply words_ok_f_eq in HW.
  destruct (ent_words segs (a_facts A) (a_mem A) (XS sp_terms o) 0) as [[vb vn]|] eqn:Ew; [|discriminate].
  destruct vn as [w| | | | |]; try discriminate.
  destruct (xaddr vb) as [[tb ob]|] eqn:Ea; [|discriminate].
  destruct (wZ w =? 0) eqn:Ew0; [|discriminate]. apply Z.eqb_eq in Ew0.
  destruct (rbetween 2 (a_facts A) (wS ob, tb) 0 140737488355328) eqn:Erb; [|discriminate]. injection Hs as <-.
  pose proof HR as [Hpc Hal0 Hsvc Hregs Hres Hrom Hmem Hmod Hh [Hb Hl] Hsat Hhs Hcov Hcomp Hnaok]. cbn [cfg_ms cfg_model] in *.
  destruct (eb_of_R segs ρ (a_mem A) (ms_mem ms) ph Hmem Efe) as [nR Heb]. pose proof (eb_rel_facts ph ρ _ _ _ Heb) as HF.
  pose proof (eb_layout ρ HF) as (Hs1 & Hargc & Henvc & Hl0 & Hq0 & _ & Hs2). unfold sp_window_lo, sp_window_hi in Hs1, Hs2.
  pose proof (atop_is_sp_sound segs fs0 ρ _ _ Hmod Eat) as Hatop.
  set (iovp := sp_val ρ + wS o) in *.
  assert (Hu : bv_unsigned (Z_to_bv 64 iovp) = iovp) by (apply u_wz; unfold iovp; lia).
  assert (Hv : xv_val ρ (XS sp_terms o) (Z_to_bv 64 iovp)).
  { cbn [xv_val]. rewrite Hu. unfold smod. change (teval ρ sp_terms) with (sp_val ρ). rewrite <- (wS_mod o), Zplus_mod_idemp_r.
    symmetry. apply Z.mod_small. unfold FastWord.two64, iovp in *. lia. }
  destruct (ent_words_sound segs Hlow ρ (a_facts A) (a_mem A) (ms_mem ms) _ _ 0 vb (XL w) Hsat Hmem Hhs Hv ltac:(discriminate) Ew)
    as (b0 & n0 & Hrb0 & Hrn0 & Hvb0 & Hvn0).
  rewrite Hu in Hrb0, Hrn0. replace (iovp + 16 * 0) with iovp in Hrb0 by lia. replace (iovp + (16 * 0 + 8)) with (iovp + 8) in Hrn0 by lia.
  cbn [xv_val] in Hvn0. rewrite Ew0 in Hvn0.
  pose proof (rbetween_sound ρ _ 2 _ _ _ Hsat Erb) as Hbr.
  assert (Hbv : bv_unsigned b0 = leval ρ (wS ob, tb)) by (apply (addr_form_val' ρ vb b0 tb ob 140737488355328 Hvb0 Ea Hbr); unfold FastWord.two64; lia).
  (* [comment removed for export] *)
  assert (G : forall (r : reg) (k : int) (z : Z), ri r = k -> xlit (aget (a_regs A) k) = Some z -> rg ms r = Z_to_bv 64 z).
  { intros r k z Hk E. apply word_lit_w. exact (reg_lit ρ _ ms r k z Hregs Hk E). }
  assert (H17 : bv_unsigned (rg ms (Z_to_bv 5 17)) = 66) by exact (reg_lit ρ _ ms (Z_to_bv 5 17) 17%uint63 66 Hregs eq_refl E17).
  assert (H11 : rg ms 11%bv = Z_to_bv 64 iovp).
  { apply word_lit_w. change 11%uint63 with (ri 11%bv) in E11. rewrite <- Hu. pose proof (Hregs 11%bv) as X. rewrite E11 in X. cbn [xv_val] in *. lia. }
  (* [comment removed for export] *)
  assert (Hf : fetch_word segs (ms_pc_val ms) = Some (Z_to_bv 32 0x73)).
  { rewrite Hpc. pose proof (words_get segs _ _ 0 0x73 HW ltac:(left; reflexivity) ltac:(split; [discriminate | reflexivity])) as X.
    rewrite Z.add_0_r in X. exact X. }
  set (ents := [(b0, n0)]).
  set (CA := import_iovecs_accesses (ms_read_byte (latch ms)) (Z_to_bv 64 iovp) (Z_to_bv 64 (Z.of_nat (length ents)))).
  assert (Hchk : forall eff, check_syscall (sys_input segs (latch ms) (rg ms (Z_to_bv 5 17))) eff model
                             = check_ret_only_copyins CA eff (Z_to_bv 64 0) model []).
  { apply (writev_check_zero segs (latch ms) (rg ms (Z_to_bv 5 17)) model 2 (Z_to_bv 64 iovp) ents).
    - exact Hrom.
    - exact (fd_rel_lookup2 fs0 ρ _ _ (mr_fds segs fs0 ρ _ _ Hmod)).
    - lia.
    - exact H17.
    - rewrite lg0. exact (G 10%bv 10%uint63 2 eq_refl E10).
    - rewrite lg1. exact H11.
    - rewrite lg2. exact (G 12%bv 12%uint63 1 eq_refl E12).
    - cbn [ents length]. lia.
    - rewrite Hu. cbn [ents length]. unfold TASK_SIZE, iovp. lia.
    - cbn [ents iov_array]. rewrite Hu. repeat split; first [exact Hrb0 | exact Hrn0 | lia].
    - cbn [ents iov_bufs_ok]. unfold TASK_SIZE. split; [lia | exact I].
    - cbn [ents iovs_total]. lia. }
  assert (Hacc : acc_ok model CA).
  { pose proof (acc_ok_writev model (ms_read_byte (latch ms)) (Z_to_bv 64 iovp) ents 0) as X. cbn [iov_prefix_accesses ents] in X.
    rewrite app_nil_r in X. apply X; unfold ents.
    - cbn [length]. lia.
    - rewrite Hu. cbn [length]. unfold TASK_SIZE, iovp. lia.
    - cbn [iov_bufs_ok]. unfold TASK_SIZE. split; [lia | exact I].
    - rewrite Hu. apply (no_lazy_above segs fs0 ρ _ model _ _ Hmod). rewrite Hatop. unfold iovp. lia.
    - cbn [iov_nl]. split; [|exact I]. intros p z _ Hz. lia. }
  apply (rzc_latch segs cfg ms model _ _ Hh Hsvc Hf AsanWSw.E_88).
  apply (rzc_sys_silent segs cfg (latch ms) model (rg ms (Z_to_bv 5 17)) (KT ρ o') Hh eq_refl).
  - rewrite Hchk. apply check_ret_only_copyins_no_unmodeled.
  - intros eff m' evs Hc. rewrite Hchk in Hc. apply check_ret_only_copyins_ok_iff in Hc as (_ & -> & ->). split; [reflexivity | exact Hh].
  - exists (with_copyins CA (mkEffect (Z_to_bv 64 0) [] [])), model. split.
    + rewrite Hchk. apply check_ret_only_copyins_ok_iff. repeat split.
    + apply refusal_b_uninjected; [rewrite H17; lia | rewrite H17; reflexivity].
  - intros eff m' Hc _. rewrite Hchk in Hc. apply check_ret_only_copyins_ok_iff in Hc as (-> & -> & _).
    exists model. split.
    + unfold syscall_effect_accesses. cbn [eff_copyins eff_writes with_copyins write_accesses]. rewrite app_nil_r. exact (materialize_acc_ok model CA Hacc).
    + rewrite apply_effect_copyins_no_write.
      refine (HS _ (or_introl eq_refl) ρ _ _ o' Ho).
      change (set_gpr0 (latch ms) (Z_to_bv 64 0)) with (apply_effect (latch ms) (mkEffect (Z_to_bv 64 0) [] [])).
      apply (R_reg_sys segs LIM fs0 ρ A _ ms model model (Z_to_bv 64 0) (XL w_zero) HR); try reflexivity; try assumption.
Qed.

End Stdio0Sound.
