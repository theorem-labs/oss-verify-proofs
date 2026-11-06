(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling PropExec MState Mem Cells Frame Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages LazyModel NodesA Shadow BackingAlgebraA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep AsanFakeStack AsanPS AsanKern AsanClient AsanDepot AsanBudget AsanBudget2 AsanGap AsanSlack.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_base B_alloc_iface B_live B_policy5 B_budget5 B_slack5 BI_shadow BI_lowshadow BI_globals2 BYajlRep BF_fakestack_rep BF_statics BX_Exit B_bundle B_benv5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.      (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
Definition stdio_rep (so : stdout_st) (m : mem) : Prop :=
  exists guard cdt thr sec tm1, stdio_state m so guard cdt thr sec tm1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition athr5 (PL0 : fs_plumb) (E : aenv) (m : mem) : Prop :=
  rw_cells bsegs m (ae_thread E) [C8 (Z_to_bv 64 (fp_ctx PL0))] /\ rw_cells bsegs m (fp_ctx PL0 + 8) [C4 (Z_to_bv 64 0)].
Definition rt_misc5 (FSB0 : Z) (PL0 : fs_plumb) (E : aenv) (m : mem) : Prop :=
  icp_globals2 bsegs m /\ (exists t, exit_statics m t) /\ FSEnv bsegs E FSB0 PL0 m /\ amalloc_statics m /\ athr5 PL0 E m.

(* [comment removed for export] *)
Record main_facts5 (FULL : mem) (model : Model) (E0 : aenv) (FSB0 : Z) (PL0 : fs_plumb)
       (HR0 : list (Z * Z)) (L0 RES0 : list (word * word)) (EB0 : Z) : Prop := mkMainFacts5 {
  (* [comment removed for export] *)
  mf_hr0    : Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192;
  mf_eb0    : 0 <= EB0 <= 2^32;
  mf_envdepot : zlen (ae_keys0 E0) <= 1000 /\ 0 <= ae_frames0 E0 <= 4096;
  mf_hstot  : gw_sizes (RES0 ++ L0) <= 2^46 /\ (length (RES0 ++ L0) <= 256)%nat;
  (* [comment removed for export] *)
  mf_arep   : ARep bsegs E0 (DepotR bsegs E0) (astate0 E0) FULL;
  mf_wfenv  : wf_env E0;
  mf_keys0  : List.NoDup (map depot_hash (ae_keys0 E0)) /\ zlen (ae_keys0 E0) < kDepotNodesPerBlock;
  mf_akern  : AKern E0 (astate0 E0) model;
  mf_kvm    : KVM L0 RES0 model (astate0 E0);
  (* [comment removed for export] *)
  mf_fsrep  : FSRep bsegs E0 FSB0 fsstate0 [] FULL;
  (* [comment removed for export] *)
  mf_icp    : icp_globals bsegs FULL A_SB;
  mf_yst    : ay_statics FULL;
  mf_low    : low_shadow_ok FULL;
  mf_rt     : rt_misc5 FSB0 PL0 E0 FULL;
  mf_stdio  : stdio_rep stdout_init FULL;
  mf_ycl    : ay_cells FULL;
  (* [comment removed for export] *)
  mf_halted : m_halted model = None;
  mf_minv   : minvA model;
  mf_limit  : vm_limit (m_vmmaps model) = 2^39;
  mf_meminv : mem_inv bsegs FULL;
  (* [comment removed for export] *)
  mf_mat    : Forall (fun w => bv_unsigned w mod 4096 = 0 /\ in_ivs_Z (S0_ivs5 E0 FSB0 ++ HR0) (bv_unsigned w)) (m_vm_materialized model)
              /\ List.NoDup (m_vm_materialized model);
  mf_eager  : eager_used model <= EB0;
  (* [comment removed for export] *)
  mf_envok  : app_mem (ae_store_blk E0) (2^23) /\ ae_store_blk E0 + 2^23 <= alloc_ceiling
              /\ app_mem FSB0 kFsBytes /\ FSB0 + kFsBytes <= alloc_ceiling
              /\ kHighMemBeg <= ae_resv_beg E0
              /\ (FSB0 + kFsBytes <= ae_store_blk E0 \/ ae_store_blk E0 + 2^23 <= FSB0)
              /\ In (FSB0, kFsBytes) (ae_reserved E0)
              /\ ae_fs_beg E0 = FSB0 /\ ae_fs_len E0 = kFsBytes
              /\ fst (ae_img E0) = 0x10000 /\ 0x5f3000 <= snd (ae_img E0);
  (* [comment removed for export] *)
  mf_l0ok   : l0_ok5 E0 L0 RES0
}.

(* [comment removed for export] *)
Section Birth.
Variables (FULL : mem) (model : Model) (E0 : aenv) (FSB0 : Z) (PL0 : fs_plumb) (HR0 : list (Z * Z)) (L0 RES0 : list (word * word)) (EB0 : Z).
Hypothesis MF : main_facts5 FULL model E0 FSB0 PL0 HR0 L0 RES0 EB0.

#[local] Notation AHKc := (AHK stdio_rep (rt_misc5 FSB0 PL0) E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation s0 := (aps_init E0 FSB0).

(* [comment removed for export] *)
Lemma MF_HR0_ok : Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192.
Proof. exact (mf_hr0 _ _ _ _ _ _ _ _ _ MF). Qed.
Lemma MF_EB0_ok : 0 <= EB0 <= 2^32.
Proof. exact (mf_eb0 _ _ _ _ _ _ _ _ _ MF). Qed.
Lemma MF_ENV_depot : zlen (ae_keys0 E0) <= 1000 /\ 0 <= ae_frames0 E0 <= 4096.
Proof. exact (mf_envdepot _ _ _ _ _ _ _ _ _ MF). Qed.
Lemma MF_HS_tot : gw_sizes (RES0 ++ L0) <= 2^46 /\ (length (RES0 ++ L0) <= 256)%nat.
Proof. exact (mf_hstot _ _ _ _ _ _ _ _ _ MF). Qed.
Lemma MF_L0_ok : l0_ok5 E0 L0 RES0.
Proof. exact (mf_l0ok _ _ _ _ _ _ _ _ _ MF). Qed.

Lemma AHK_birth5 :
  AHKc s0 [] [] FULL model /\ aps_so s0 = stdout_init /\ aps_credit s0 = kInitialCredit.
Proof.
  destruct MF.
  split; [| split; reflexivity].
  unfold AHK. cbn [aps_env aps_alloc aps_fs aps_fsbase aps_so aps_credit aps_init].
  split; [exact mf_arep0|].
  split; [apply AWf_init; [exact mf_wfenv0| rewrite app_nil_r; exact (proj1 mf_keys1)]|].
  split; [exact mf_akern0|].
  split; [exact mf_kvm0|].
  split; [apply res_ok_init|].
  split; [unfold AQbound, tq_bytes, gq_bytes; cbn; unfold kThreadQuarantineMax, kQuarantineMax; lia|].
  split; [apply depot_inv_init; [pose proof (proj2 mf_envdepot0); lia| exact (proj2 mf_keys1)]|].
  split; [apply binv_init|].
  split; [apply blocks_match_init|].
  split; [exact mf_fsrep0|].
  split; [exact mf_icp0|]. split; [exact mf_yst0|]. split; [exact mf_low0|]. split; [exact mf_rt0|].
  split; [exact mf_stdio0|].
  split; [split; [exact mf_halted0| split; [exact mf_minv0| exact mf_limit0]]|].
  split.
  { (* [comment removed for export] *) destruct mf_mat0 as [MS MN]. constructor.
    - exact MN.
    - apply Forall_impl with (2 := MS). intros w Hw.
      unfold B_bundle.aS, B_policy5.aS, aSa, A0. cbn [aps_alloc aps_init]. destruct Hw as [Hw1 Hw2].
      split; [exact Hw1| left; exact Hw2].
    - intros l ND HF. exact (B_policy5.aS_card (A0 E0 FSB0 HR0) _ l ND HF).
    - rewrite aEB_init; [exact mf_eager0|..]; assumption.
    - rewrite mf_limit0. change page_size with 4096. apply li_budget_init; assumption. }
  split; [apply BUDGET_init5|].
  split; [exact mf_meminv0|].
  split; [| split; [exact mf_ycl0| split; [apply sstats_ok_init| apply csmall_init]]].      (* [comment removed for export] *)
  (* [comment removed for export] *) unfold ENVOK. cbn [aps_env aps_fsbase aps_init]. pose proof mf_envok0 as X. repeat (split; [tauto|]); tauto.
Qed.
End Birth.
End RC__1.
