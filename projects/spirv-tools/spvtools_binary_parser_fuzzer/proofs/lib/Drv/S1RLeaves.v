(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SRealizes AllocCeil RunRandom LibIface LibBudget S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import RunsLib S1CxxTable StaticsGen S1Statics S1SpecConsts S1Spec S1Cells S1AddrFacts S1RBase S1RKn DrvMallocT
  S1ReadErr_defs S1ReadErr S1Refused.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Abbreviation RSEGS := Plain.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FXALL.
Context {fx : FPState}.
Section Leaves.
  Context {AC : AllocCeiling} {RRND : RunRandom} {AMB : Amb}.
  Variable MI : MallocIface SEGS L.
  Hypothesis MC : mi_constsG MI.
  Variables (sp0 tid p1 : Z) (path : list byte) (fs0 : Fs).
  Hypothesis Hsp : 0x7fff80000000 <= sp0 <= 0x800000000000 /\ sp0 mod 16 = 0.
  Hypothesis Htid : 0 < tid < 2 ^ 22.

  Let spw : word := Z_to_bv 64 sp0.
  Lemma spw_u : bv_unsigned spw = sp0. Proof. subst spw. apply u64_lit. lia. Qed.
  Lemma spw_valid : valid_sp spw.
  Proof. unfold valid_sp, sp_window_lo, sp_window_hi. rewrite spw_u. lia. Qed.

  Lemma static_cell : forall A M mo (a : Z) (zs : list Z) (n : nat) (v : Z),
    ainv MI A M mo -> In (a, zs) (static_cells MI) -> length zs = n ->
    map (Z_to_bv 8) zs = word_to_le_bytes n (Z_to_bv 64 v) -> cell M a n v.
  Proof.
    intros A M mo a zs n v AI Hin Hl He. unfold cell. rewrite <- He, <- Hl.
    exact (ai_static_cells MI A M mo a zs AI Hin).
  Qed.

  Section FromPre.
    Variables (A : AS MI) (R : bvmap 5 word) (M : word -> option byte) (mo : Model).
    Hypothesis PRE : oom_pre MI sp0 tid p1 path fs0 A R M mo.

    Let RM := op_mem _ _ _ _ _ _ _ _ _ _ PRE.
    Let RA := op_abs _ _ _ _ _ _ _ _ _ _ PRE.

    Lemma pre_stack : stack_writable M spw.
    Proof. intros d m Hd Hm. rewrite spw_u. apply (rm_stack _ _ _ _ _ RM); assumption. Qed.
    Lemma pre_img : Forall (fun iv => img_clear M (fst iv) (snd iv)) re_ivs.
    Proof. rewrite re_ivs_eq. exact (rm_img _ _ _ _ _ RM). Qed.
    Lemma pre_canary : cell M 0x120928 8 rr_canary.
    Proof.
      eapply (static_cell A M mo); [exact (ra_ainv _ _ _ _ RA) | exact (mcg_guard _ MC) | apply length_map; reflexivity |].
      rewrite map_map. erewrite map_ext; [apply map_id|]. intros b. apply Z_to_bv_bv_unsigned.
    Qed.
    Lemma pre_pagesz : cell M 0x120978 8 4096.
    Proof. eapply (static_cell A M mo); [exact (ra_ainv _ _ _ _ RA) | exact (mcg_pgsz _ MC) | reflexivity | apply byte_list_eq; vm_compute; reflexivity]. Qed.
    Lemma pre_nlocks : cell M 0x12094b 1 0.
    Proof. eapply (static_cell A M mo); [exact (ra_ainv _ _ _ _ RA) | exact (mcg_nlock _ MC) | reflexivity | apply byte_list_eq; vm_compute; reflexivity]. Qed.

    Theorem refused_leaf :
      srealizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x65830) M (seg_rom RSEGS)) mo) (t_die msg_refused fs0).
    Proof.
      pose proof (op_sp _ _ _ _ _ _ _ _ _ _ PRE) as Q2. pose proof (op_gp _ _ _ _ _ _ _ _ _ _ PRE) as Q3.
      pose proof (op_tp _ _ _ _ _ _ _ _ _ _ PRE) as Q4. pose proof RM as QM. destruct (ra_mstd _ _ _ _ RA) as [Hh Hlz Hmat].
      rewrite <- (op_fs _ _ _ _ _ _ _ _ _ _ PRE).
      apply (ref_refused_tail spw [] mo spw_valid Hh Hlz (op_fd2 _ _ _ _ _ _ _ _ _ _ PRE) tid rr_canary R M); try assumption.
      - rewrite spw_u. exact Q2.
      - apply pre_stack.
      - apply pre_img.
      - exact (rm_tid _ _ _ _ _ QM).
      - exact (rm_self _ _ _ _ _ QM).
      - apply pre_canary.
      - apply pre_pagesz.
      - apply pre_nlocks.
      - exact (rmem_drv_cells _ _ _ _ _ QM).
    Qed.
  End FromPre.
End Leaves.
End FXALL.
