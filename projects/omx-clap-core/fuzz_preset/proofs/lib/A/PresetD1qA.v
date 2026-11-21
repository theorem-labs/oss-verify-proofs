(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from tfib_srealizesX of proofs/cgif/cgif_file_fuzzer/lib/A/AD1q.v:39-100
   (the donor's asan image; its lib/YD1q.v twin is the asan-ubsan one) for fuzz_preset's asan image. This file and
   lib/AU/PresetD1qB.v are the same text except for the image module and the per-image atable TFIB.
   It states START-UP + DRIVER: from the start-up certificate and the driver walk's conclusion, the asan build
   realizes SPECX from every valid start. Nothing in this file is a proof of a function (rule 24: no function proved;
   this is the composition / driver layer of a port).
   Changes from the donor:
   (1) the no-refusal premise of preset's TFIB_T (lib/A/PresetTFIB.v:28), with its own entry en_p, is added and
       handed to the driver;
   (2) cgif's sink is dropped: ff_unl_has_nil / ff_libk_has_nil (AD1q.v:25-36) and the YI0a import are gone; at
       ZTraceSpec.checksum_shape they collapse into libk_has_nil (lib/A/PresetCfnA.v:401), and this file needs neither:
       CLOSEDX_has_nil (lib/Reusable/YO01.v:91) holds at every shape;
   (3) the library shape is passed EXPLICITLY at its full path (ZTraceSpec.checksum_shape), never inferred;
   (4) the donor's Section d hypotheses (B HB AMALLOC .. EXS, AD1q.v:41-63) are not repeated here. The donor's proof of
       tfib_srealizesX uses them only to build DRV_MAINX : drv_mainX_stmt (AD1q.v:77-78), so this file takes the
       driver as that one statement, drv_mainX_stmt_A, and the composition (PresetD2oA) supplies it from the driver
       walk tfib_drv_main_A (PresetD1pA, lane CwD1pA), whose Section carries the restated hypotheses (AR -> ARcf below
       the loop, preset_lib_contract_x_all, PF1 / PFN / EXS over ARcf);
   (5) the hand-off table HS (the donor's HS_tfib, A/AB01.v:597) is a parameter: the start-up states are being
       regenerated, so no statement here names one of them; the composition passes the regenerated HS_tfib. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PresetD1qA.v, with its module paths changed; 46 of its 118 lines of code are new or changed and 10 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: made from tfib_srealizesX of proofs/cgif/cgif_file_fuzzer/lib/A/AD1q.v:39-100
   (the donor's asan image; its lib/YD1q.v twin is the asan-ubsan one) for fuzz_preset's asan image. This file and
   lib/AU/PresetD1qB.v are the same text except for the image module and the per-image atable TFIB.
   It states START-UP + DRIVER: from the start-up certificate and the driver walk's conclusion, the asan build
   realizes SPECX from every valid start. Nothing in this file is a proof of a function (rule 24: no function proved;
   this is the composition / driver layer of a port).
   Changes from the donor:
   (1) the no-refusal premise of preset's TFIB_T (lib/A/PresetTFIB.v:28), with its own entry en_p, is added and
       handed to the driver;
   (2) cgif's sink is dropped: ff_unl_has_nil / ff_libk_has_nil (AD1q.v:25-36) and the YI0a import are gone; at
       ZTraceSpec.checksum_shape they collapse into libk_has_nil (lib/A/PresetCfnA.v:401), and this file needs neither:
       CLOSEDX_has_nil (lib/Reusable/YO01.v:91) holds at every shape;
   (3) the library shape is passed EXPLICITLY at its full path (ZTraceSpec.checksum_shape), never inferred;
   (4) the donor's Section d hypotheses (B HB AMALLOC .. EXS, AD1q.v:41-63) are not repeated here. The donor's proof of
       tfib_srealizesX uses them only to build DRV_MAINX : drv_mainX_stmt (AD1q.v:77-78), so this file takes the
       driver as that one statement, drv_mainX_stmt_A, and the composition (PresetD2oA) supplies it from the driver
       walk tfib_drv_main_A (PresetD1pA, lane CwD1pA), whose Section carries the restated hypotheses (AR -> ARcf below
       the loop, preset_lib_contract_x_all, PF1 / PFN / EXS over ARcf);
   (5) the hand-off table HS (the donor's HS_tfib, A/AB01.v:597) is a parameter: the start-up states are being
       regenerated, so no statement here names one of them; the composition passes the regenerated HS_tfib. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the revision's launch (CONFIG_RSEQ-sized auxv, execfn, group id, launch premises); the input-owned, top-anchored launch stack). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Shapes.
From OSSVerify.omx_clap_core.fuzz_preset Require Images.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK15 YK18 YK0c YK0e YK09 YA0c YA0e YA01 YA02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB12.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO05 YO09 YO06 YO01 YM05.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

(* ---------------------------------------------------------------------- *)
(* 0. LPS 727298f3: the launch reads the whole input, so the start-up invariant, the hidden stack bytes, the entry
      environment and the loader's stack bytes (lib/Reusable/YA02.v, Section c) take the input's fields, the mmap
      base and the entry pc; these notations spell them at an input [inp]. *)
Notation SINV_A sp rdraw brk mbase inp :=
(YA02.SINV0 Asan.M.loaded_segments Asan.M.phdrs sp rdraw brk mbase (in_argv inp) (in_envp inp) (in_image_fs inp)
  (in_stdin inp) (in_uid inp) (in_gid inp) (in_hwcap inp) (in_groups inp) (in_net inp) (in_nofile inp)
  (in_sigmask inp) (in_urandom inp) (in_tmp inp) (in_kernel inp) (in_execfn inp) (in_sigpipe_default inp)
  Asan.M.init_pc) (only parsing).
Notation argH_A sp rdraw inp :=
(YA02.argH0 sp rdraw (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp)
  (in_hwcap inp) (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp)
  (in_kernel inp) (in_execfn inp) (in_sigpipe_default inp)) (only parsing).
Notation E0_A sp rdraw brk inp :=
(YA02.E0 sp rdraw brk (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp)
  (in_hwcap inp) (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp)
  (in_kernel inp) (in_execfn inp) (in_sigpipe_default inp)) (only parsing).
Notation FULL0_A sp rdraw mbase inp :=
(wrap_mem inp mbase Asan.M.phdrs (Z_to_bv 64 (Z.of_N Asan.M.init_pc)) sp rdraw) (only parsing).

(* ---------------------------------------------------------------------- *)
(* 1. The start-up certificate. Donor: A/AB1n.v (HS_ok, tfib_startup_T1), the same text over the hand-off table
      HS (one table per value of the run's CONFIG_RSEQ flag) in place of AB01r.HS_tfib_r; the segments and program
      headers are the image's own (Asan.M.loaded_segments / phdrs, which A/AB1h.v's TSEGS / TPH abbreviate). *)
Definition HS_ok_A (HS : Z -> nat -> option acs) (h : nat) (sp : word) (rdraw : EntryDraw) (brk0 mbase : word)
(argv envp : list (list byte)) (fs0 : Fs.Fs) (stdin : InputStream) (uid gid hw : word)
(groups : list word) (net : NetQueue) (nofile sigmask : word) (urnd : InputStream) (tmp : Fs.Fs)
(kb : KernelBuild) (execfn : list byte) (sdef : bool) (fsq : Fs.Fs) (c : config) : Prop :=
exists ch E R FULL model,
HS (rseq_z (kb_rseq kb)) h = Some ch
/\ c = cfg_of Asan.M.loaded_segments R (pc ch) FULL model
/\ cs_ok Asan.M.loaded_segments TFIB YA02.LIMIT (YA02.TOP sp)
(YA02.SINV0 Asan.M.loaded_segments Asan.M.phdrs sp rdraw brk0 mbase argv envp fs0 stdin uid gid hw groups net nofile
  sigmask urnd tmp kb execfn sdef Asan.M.init_pc)
(YA02.argH0 sp rdraw argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) fsq E ch R FULL model.

Definition tfib_startup_T1_A (HS : Z -> nat -> option acs) : Prop :=
forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)) (fs : Fs.Fs) (stdin : InputStream)
(uid gid hw : word) (groups : list word) (net : NetQueue) (nofile sigmask : word) (urnd : InputStream) (tmp : Fs.Fs)
(kb : KernelBuild) (execfn : list byte) (sdef : bool),
valid_sp sp -> valid_brk Asan.M.loaded_segments brk0 -> valid_mmap_base mbase -> valid_argv argv -> valid_envp envp ->
entry_stack_fits sp argv envp -> valid_id uid -> valid_hwcap hw -> valid_nofile nofile ->
valid_sigmask (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) ->
valid_launch (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) ->
entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw)
(YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) ->
forall T : TSet, T [] ->
(forall h c, HS_ok_A HS h sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef
(fs_seed_tmp fs tmp) c -> srealizes Asan.M.loaded_segments c T) ->
srealizes Asan.M.loaded_segments (init_config Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs sp brk0 mbase rdraw YA02.LIMIT
(YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef)) T.

(* ---------------------------------------------------------------------- *)
(* 2. The driver's conclusion. Donor: A/AD1q.v (drv_mainX_stmt), with the no-refusal premise after the launch facts,
      the hand-off table HS for HS_tfib_r, the start-up invariant of section 0 at the input, and CLOSEDX at
      checksum_shape. tfib_drv_main_A (lib/A/PresetD1pA.v) concludes @drv_mainX_stmt_A rc HS_tfib_r after its
      Section arguments. The launch's fifth [valid_entry] conjunct [entry_launch_ok_va] is given (the statements'
      valid_entry carries it). *)
Definition drv_mainX_stmt_A (rc : YM05.RunCeil) (HS : Z -> nat -> option acs) : Prop :=
forall (sp : word) (rdraw : EntryDraw) (brk mbase : word) (inp : ProcInput) (en_p : ExecEntry)
(h : nat) (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model),
valid_sp sp -> valid_brk Asan.M.loaded_segments brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
~ run_scfg_budget_refused OSSVerify.Core.Shapes.Env.alloc_forced_only
    OSSVerify.omx_clap_core.fuzz_preset.Images.plain
    OSSVerify.Core.Shapes.Budgets.Asan.lim_source en_p inp ->
@YM05.ceil_of_top rc (bv_unsigned sp - stack_max_size) ->
HS (rseq_z (kb_rseq (in_kernel inp))) h = Some ch ->
cs_ok Asan.M.loaded_segments TFIB YA02.LIMIT (YA02.TOP sp) (SINV_A sp rdraw brk mbase inp) (argH_A sp rdraw inp)
(in_fs inp) E ch R FULL model ->
(forall n, (n < NX0G)%nat -> ev E n = ev (E0_A sp rdraw brk inp) n) ->
(forall a, argH_A sp rdraw inp E a = true -> FULL a = FULL0_A sp rdraw mbase inp a) ->
srealizes Asan.M.loaded_segments (cfg_of Asan.M.loaded_segments R (pc ch) FULL model)
(CLOSEDX (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape) inp).

(* ---------------------------------------------------------------------- *)
(* 3. The statement. Donor: A/AD1q.v (tfib_srealizesX), with the no-refusal premise of TFIB_T and the launch's
      fifth [valid_entry] conjunct. *)
Definition tfib_srealizesX_A : Prop :=
forall (rc : YM05.RunCeil) (HS : Z -> nat -> option acs),
tfib_startup_T1_A HS -> drv_mainX_stmt_A rc HS ->
forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput) (en_p : ExecEntry),
valid_sp sp -> valid_brk Asan.M.loaded_segments brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
entry_launch_ok_va Sv48 (mkEntry sp brk mb rdraw) inp ->
~ run_scfg_budget_refused OSSVerify.Core.Shapes.Env.alloc_forced_only
    OSSVerify.omx_clap_core.fuzz_preset.Images.plain
    OSSVerify.Core.Shapes.Budgets.Asan.lim_source en_p inp ->
@YM05.ceil_of_top rc (bv_unsigned sp - stack_max_size) ->
srealizes Asan.M.loaded_segments (init_config Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs sp brk mb rdraw YA02.LIMIT inp)
(SPECX (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape) inp).

(* ---------------------------------------------------------------------- *)
(* 4. The proof. Donor: A/AB1n.v (HS_ok_open, over HS) and A/AD1q.v (tfib_srealizesX, with DRV in place of
      DRV_MAINX and the no-refusal premise handed to it). *)
Lemma HS_ok_open_A : forall HS h sp rdraw brk0 mbase argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp
kb execfn sdef fsq c,
HS_ok_A HS h sp rdraw brk0 mbase argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef fsq c ->
exists ch E R FULL model,
HS (rseq_z (kb_rseq kb)) h = Some ch /\ c = cfg_of Asan.M.loaded_segments R (pc ch) FULL model
/\ cs_ok Asan.M.loaded_segments TFIB YA02.LIMIT (YA02.TOP sp)
(YA02.SINV0 Asan.M.loaded_segments Asan.M.phdrs sp rdraw brk0 mbase argv envp fs0 stdin uid gid hw groups net nofile
  sigmask urnd tmp kb execfn sdef Asan.M.init_pc)
(YA02.argH0 sp rdraw argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) fsq E ch R FULL model
/\ (forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 sp rdraw brk0 argv envp fs0 stdin uid gid hw groups net nofile
  sigmask urnd tmp kb execfn sdef) n)
/\ (forall a, YA02.argH0 sp rdraw argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef E a = true ->
FULL a = wrap_mem (YA02.inp argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) mbase
Asan.M.phdrs (Z_to_bv 64 (Z.of_N Asan.M.init_pc)) sp rdraw a)
/\ eb E = eb (YA02.E0 sp rdraw brk0 argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef).
Proof.
intros HS h sp rdraw brk0 mbase argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef fsq c
(ch & E & R & FULL & model & Hh & Hc & HC).
exists ch, E, R, FULL, model. split; [exact Hh|]. split; [exact Hc|]. split; [exact HC|].
destruct (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC) as (S1 & S2 & S3 & _). exact (conj S1 (conj S2 S3)).
Qed.

(* The input is taken apart into its fields; [Run.valid_input] fixes the abort and terminal-SIGPIPE declarations, the
   address size and the channel reader, and says the kernel record is its own [recorded_kernel], so the input is
   [YA02.inp] at that record, the exec file name and the SIGPIPE disposition (A/AD1q.v's tfib_srealizesX). *)
Theorem tfib_srealizesX_A_holds : tfib_srealizesX_A.
Proof.
intros rc HS HST DRV sp rdraw brk mb inp en_p Hsp Hbrk Hmb Hfit Hinp Hlau HNR Hceil.
pose proof Hinp as (Hva & Hve & _ & _ & _ & [Huid _] & Hnof & Hsig & Hhw & Hab & Hmmu & _ & Hvl & Hcr & Hspt & Hkern).
destruct inp as [argv envp fs stdin uid gid groups net nofile sigmask hw ab mmu urnd tmp kern execfn cr spd spt].
cbn [in_argv in_envp in_uid in_hwcap in_nofile in_abort_terminal in_va_size in_channel_reader in_sigpipe_terminal in_kernel]
in Hva, Hve, Hfit, Huid, Hhw, Hnof, Hab, Hmmu, Hcr, Hspt, Hkern.
subst ab mmu cr spt.
rewrite Hkern in Hinp, Hsig, Hvl, Hlau, HNR |- *.
change (mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw false Sv48 urnd tmp (recorded_kernel kern) execfn true spd false)
with (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd) in *.
apply (srz_conseq Asan.M.loaded_segments _
(CLOSEDX (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape)
(YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd)));
[| apply t_eq_sym; apply (specx_closedx_eq (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape))].
apply (HST sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd
Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hnof Hsig Hvl Hlau
(CLOSEDX (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape)
(YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd))
(CLOSEDX_has_nil (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape) _)).
intros h c Hok.
destruct (HS_ok_open_A HS h sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd
(fs_seed_tmp fs tmp) c Hok) as (ch & E & R & FULL & model & Hch & -> & HC & HE & HM & _).
exact (DRV sp rdraw brk mb (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd) en_p
h ch E R FULL model Hsp Hbrk Hmb Hfit Hinp Hlau HNR Hceil Hch HC HE HM).
Qed.
