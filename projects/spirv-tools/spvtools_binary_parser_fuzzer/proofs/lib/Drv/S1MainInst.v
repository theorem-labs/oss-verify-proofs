(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the revised entry stack block, with the strings at its top, and the launch facts; the run's mmap base; the model's channel reader as a premise of the writes; the walk over the image's own segments lifted to the run's segment list (run_segments, with the vDSO pair)). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom Amb PropExec ShapeAlg ArgvEnv SRealizes FPSteps RefMemcpyLib
  LibIface LibBudget S1Layout MmapSim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.R Require Import RMallocRep RBridge.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ Require Import MallocInstS1 MallocDrvIface MallocDrv.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import S1Statics DrvLibContract DrvMallocT S1Cells S1Spec S1BootDefs S1Start
  S1UsageTop S1Main LibContractS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Common.Cfg Require SRomStable.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Abbreviation RSEGS := Plain.M.loaded_segments.

Lemma canary_range : forall r, 0 <= bv_unsigned (canary r) < 2 ^ 64.
Proof. intros r. pose proof (bv_unsigned_in_range _ (canary r)) as H. unfold bv_modulus in H. exact H. Qed.

Lemma canary_byte1 : forall r, Z.land (bv_unsigned (canary r)) 0xff00 = 0.
Proof.
  intros r. unfold canary, canary_bytes.
  set (b0 := nth 0 (at_random_bytes (ed_random r)) (Z_to_bv 8 0)).
  set (rest := firstn 6 (skipn 2 (at_random_bytes (ed_random r)))).
  pose proof (bv_unsigned_in_range _ b0) as Hb0. change (bv_modulus 8) with 256 in Hb0.
  assert (HR : 0 <= lez rest).
  { clear. induction rest as [|b l IH]; cbn [bytes_le_to_Z]; [lia|].
    apply Z.lor_nonneg. split; [apply (bv_unsigned_in_range _ b) | apply Z.shiftl_nonneg; exact IH]. }
  assert (Hy : lez (b0 :: Z_to_bv 8 0 :: rest) = Z.lor (bv_unsigned b0) (Z.shiftl (lez rest) 16)).
  { cbn [bytes_le_to_Z]. change (bv_unsigned (Z_to_bv 8 0)) with 0. rewrite Z.lor_0_l, Z.shiftl_shiftl by lia. reflexivity. }
  set (y := lez (b0 :: Z_to_bv 8 0 :: rest)) in *.
  assert (Hy0 : 0 <= y) by (rewrite Hy; apply Z.lor_nonneg; split; [lia | apply Z.shiftl_nonneg; exact HR]).
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. change (Z.land (Z.ones 64) 0xff00) with (Z.land (Z.ones 16) 0xff00).
  rewrite Z.land_assoc, Z.land_ones by lia.
  assert (Hm : y mod 2 ^ 16 = bv_unsigned b0).
  { rewrite <- Z.land_ones by lia. rewrite Hy, Z.land_lor_distr_l.
    rewrite (Z.land_ones (Z.shiftl _ _)) by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z_mod_mult, Z.lor_0_r.
    rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
  rewrite Hm.
  replace (bv_unsigned b0) with (Z.land (bv_unsigned b0) (Z.ones 8)) by (rewrite Z.land_ones by lia; apply Z.mod_small; lia).
  rewrite <- Z.land_assoc. change (Z.land (Z.ones 8) 0xff00) with 0. apply Z.land_0_r.
Qed.

Definition rr_of_draw (r : EntryDraw) : RunRandom :=
  mkRunRandom (bv_unsigned (canary r)) (rr_secret_of (ed_random r)) (canary_range r) (rr_secret_of_range (ed_random r)) (canary_byte1 r).

Section Inst.
  Context {AC : AllocCeiling} {RRND : RunRandom} {AMB : Amb}.

  Lemma main_mem_conv : forall M, drv_main_mem M -> mng_main_mem M.
  Proof.
    intros M H. destruct H. constructor; try assumption.
  Qed.

  Lemma main_model_conv : forall mo, drv_main_model mo -> mng_main_model mo.
  Proof.
    intros mo H. destruct H. constructor; try assumption.
  Qed.

  Lemma auxv_conv : forall M sp, drv_auxv M sp -> mng_auxv M sp.
  Proof. intros M sp H. exact H. Qed.

  Lemma static_conv : forall a, R.RBridge.mng_static a -> S1Cells.mng_static a.
  Proof.
    intros a H. unfold R.RBridge.mng_static in H. unfold S1Cells.mng_static.
    unfold R.RMallocRep.RMLOCK, R.RMallocRep.RCTX, R.RMallocRep.RNEED_LOCKS, R.RMallocRep.RPAGE_SIZE,
      R.RMallocRep.RSSP_GUARD, R.RMallocRep.RVMLOCK in H. lia.
  Qed.

  Theorem DM_S1 : drv_mallocT MI_S1 a_inv0 a_tight a_fresh44.
  Proof.
    pose proof mng_consts_drv as (C1 & C2 & C3 & C4 & C5 & C6).
    constructor.
    - constructor; try assumption. cbn. auto.
    - intros M mo HM Hmo.
      destruct (ainv_init_proof M mo (main_mem_conv M HM) (main_model_conv mo Hmo)) as (A & H0 & H1 & H2 & H3 & H4 & H5 & H6).
      exists A. split; [exact H0|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
      split; [|split; [exact H5|exact H6]]. intros a Ho Hi. apply static_conv. exact (H4 a Ho Hi).
    - exact a_inv0_frame_proof.
    - exact ainv0_owned_proof.
    (* LPS 727298f3: [ainv MI] is [a_inv] with the channel reader ([a_invR]); malloc and
       free keep the reader, and the first malloc gets it from the launch. *)
    - intros fx A R M mo n sp ret Ksucc AI AUX T En F44 LIVE0 SM RD RO CR A0 SPC SR SOW KS.
      apply (mi_malloc_first_proof fx A R M mo n sp ret Ksucc AI (auxv_conv M sp AUX) T En F44 LIVE0 SM RO CR A0 SPC SR SOW).
      intros A' R' M' mo' q AI' T' SM' FS' FDS' RD'.
      exact (KS A' R' M' mo' q (conj AI' (eq_trans RD' RD)) T' SM' FS' FDS' RD').
    - intros fx A R M mo n sp ret Ksucc AI T CASE SM RO CR A0 HN SPC SR SOW ROOM KS.
      apply (mi_malloc_T_proof fx A R M mo n sp ret Ksucc (proj1 AI) T CASE SM RO CR A0 HN SPC SR SOW ROOM).
      intros A' R' M' mo' q AI' T' SM' FS' FDS' RD'.
      exact (KS A' R' M' mo' q (conj AI' (eq_trans RD' (proj2 AI))) T' SM' FS' FDS' RD').
    - intros fx A R M mo p n sp ret K AI T SM RO CR A0 HP SPC SR SOW HK.
      apply (mi_free_T_proof fx A R M mo p n sp ret K (proj1 AI) T SM RO CR A0 HP SPC SR SOW).
      intros A' R' M' mo' AI' T' SM' FS' FDS' RD'.
      exact (HK A' R' M' mo' (conj AI' (eq_trans RD' (proj2 AI))) T' SM' FS' FDS' RD').
  Qed.
End Inst.

Theorem s1_main_inst : forall (sp brk mbase : word) (rnd : EntryDraw) (inp : ProcInput),
  lib_contract_S1 ->
  valid_sp sp -> valid_brk RSEGS brk -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  (* LPS 727298f3: the start-up's launch facts and the launch's channel reader, three
     clauses of [Run.valid_input] ([valid_launch], the entry's launch conjunct, the reader) *)
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> in_channel_reader inp = true ->
  srealizes RSEGS (init_config RSEGS Plain.M.init_pc
                     Plain.M.phdrs sp brk mbase rnd source_alloc_limit inp)
            (spec (in_argv inp) (in_fs inp)).
Proof.
  intros sp brk mbase rnd inp LIB Hsp Hbrk Hva Hve Hfit Hvl Hlau Hrd.
  destruct (Nat.eq_dec (length (in_argv inp)) 2) as [H2|Hn2].
  2:{ replace (spec (in_argv inp) (in_fs inp)) with (t_die (msg_usage (hd [] (in_argv inp))) (in_fs inp)).
      - exact (s1_usage_top sp brk mbase rnd source_alloc_limit inp Hsp Hva Hve Hfit Hvl Hlau Hrd Hn2).
      - unfold spec. destruct (in_argv inp) as [|x [|y [|z l]]]; try reflexivity. exfalso. apply Hn2. reflexivity. }
  apply s1_startup; try assumption.
  intros tid regs mem Htid ME0.
  rewrite (init_model_seed _ _ _ _ _ inp).
  pose proof (main_entry_C sp rnd inp mbase tid regs mem ME0) as ME. clear ME0.
  set (AMB := amb_of inp) in *.
  destruct (in_argv inp) as [|a0s [|path [|z l]]] eqn:EA; rewrite ?EA in *; try discriminate H2.
  set (AC := ac_of_sp sp Hsp). set (RRND := rr_of_draw rnd).
  exact (@main_body AC RRND AMB MI_S1 a_inv0 a_tight a_fresh44 (@DM_S1 AC RRND AMB) (LIB AC RRND)
           sp a0s path (in_envp inp) tid rnd regs mem brk mbase (in_fs inp) (in_stdin inp)
           Hva Hve Hsp ltac:(unfold PID_MAX_ENVELOPE in Htid; lia) ME Hrd Hbrk eq_refl eq_refl eq_refl).
Qed.

(** LPS 08b1429: the run reads the binary against [run_segments] (its segments and the vDSO
    pair), from the run's own start; [SRomStable.srun_init] lifts the walk over the binary's
    own segments ([vdso_image RSEGS = None] by computation). *)
Theorem s1_main_run : forall (sp brk mbase : word) (rnd : EntryDraw) (inp : ProcInput),
  lib_contract_S1 ->
  valid_sp sp -> valid_brk RSEGS brk -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> in_channel_reader inp = true ->
  srealizes (run_segments RSEGS inp sp mbase)
    (init_config (run_segments RSEGS inp sp mbase) Plain.M.init_pc
       Plain.M.phdrs sp brk mbase rnd source_alloc_limit inp)
    (spec (in_argv inp) (in_fs inp)).
Proof.
  intros sp brk mbase rnd inp LIB Hsp Hbrk Hva Hve Hfit Hvl Hlau Hrd.
  apply (SRomStable.srun_init RSEGS inp sp mbase Plain.M.init_pc Plain.M.phdrs brk rnd
           source_alloc_limit _ eq_refl).
  exact (s1_main_inst sp brk mbase rnd inp LIB Hsp Hbrk Hva Hve Hfit Hvl Hlau Hrd).
Qed.
