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
       ZTraceSpec.checksum_shape they collapse into libk_has_nil (lib/A/PresetCfnA.v:400), and this file needs neither:
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
       ZTraceSpec.checksum_shape they collapse into libk_has_nil (lib/A/PresetCfnA.v:400), and this file needs neither:
       CLOSEDX_has_nil (lib/Reusable/YO01.v:91) holds at every shape;
   (3) the library shape is passed EXPLICITLY at its full path (ZTraceSpec.checksum_shape), never inferred;
   (4) the donor's Section d hypotheses (B HB AMALLOC .. EXS, AD1q.v:41-63) are not repeated here. The donor's proof of
       tfib_srealizesX uses them only to build DRV_MAINX : drv_mainX_stmt (AD1q.v:77-78), so this file takes the
       driver as that one statement, drv_mainX_stmt_A, and the composition (PresetD2oA) supplies it from the driver
       walk tfib_drv_main_A (PresetD1pA, lane CwD1pA), whose Section carries the restated hypotheses (AR -> ARcf below
       the loop, preset_lib_contract_x_all, PF1 / PFN / EXS over ARcf);
   (5) the hand-off table HS (the donor's HS_tfib, A/AB01.v:597) is a parameter: the start-up states are being
       regenerated, so no statement here names one of them; the composition passes the regenerated HS_tfib. *)
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
(* 1. The start-up certificate. Donor: A/AB1n.v:45-60 (HS_ok, tfib_startup_T1), the same text over the hand-off table
      HS in place of HS_tfib.
      PROVISIONAL: statement owned by a Theorem Labs lane (the asan start-up walk); replace by the import of its sha.
      Its atable TFIB is the core copy's (lib/A/AB12.v, still cgif's values: that relocation is in progress); the
      segments and program headers are the image's own (Asan.M.loaded_segments / phdrs, which the core's TSEGS / TPH
      of lib/A/AB1h.v abbreviate; AB1h.v does not compile on this base, AB1h.v:38). *)
Definition HS_ok_A (HS : nat -> option acs) (h : nat) (sp : word) (rdraw : EntryDraw) (brk0 : word)
(argv envp : list (list byte)) (uid hw : word) (fs : Fs.Fs) (c : config) : Prop :=
exists ch E R FULL model,
HS h = Some ch
/\ c = cfg_of Asan.M.loaded_segments R (pc ch) FULL model
/\ cs_ok Asan.M.loaded_segments TFIB YA02.LIMIT (YA02.TOP sp)
(YA02.SINV0 Asan.M.loaded_segments Asan.M.phdrs sp rdraw brk0 argv envp uid hw) (YA02.argH0 Asan.M.phdrs sp rdraw argv envp uid hw) fs E ch R FULL model.

Definition tfib_startup_T1_A (HS : nat -> option acs) : Prop :=
forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)) (fs : Fs.Fs) (stdin : InputStream)
(uid gid hw : word) (groups : list word) (net : NetQueue) (nofile sigmask : word) (urnd : InputStream) (tmp : Fs.Fs),
valid_sp sp -> valid_brk Asan.M.loaded_segments brk0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
valid_id uid -> valid_hwcap hw ->
forall T : TSet, T [] ->
(forall h c, HS_ok_A HS h sp rdraw brk0 argv envp uid hw (fs_seed_tmp fs tmp) c -> srealizes Asan.M.loaded_segments c T) ->
srealizes Asan.M.loaded_segments (init_config Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs sp brk0 mbase rdraw YA02.LIMIT
(YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp)) T.

(* ---------------------------------------------------------------------- *)
(* 2. The driver's conclusion. Donor: A/AD1q.v:64-76 (drv_mainX_stmt), with the no-refusal premise after valid_input,
      the hand-off table HS for HS_tfib, and CLOSEDX at checksum_shape. tfib_drv_main_A (lib/A/PresetD1pA.v) concludes
      @drv_mainX_stmt_A rc HS_tfib after its Section arguments. *)
Definition drv_mainX_stmt_A (rc : YM05.RunCeil) (HS : nat -> option acs) : Prop :=
forall (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput) (en_p : ExecEntry)
(h : nat) (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model),
valid_sp sp -> valid_brk Asan.M.loaded_segments brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
~ run_scfg_budget_refused OSSVerify.Core.Shapes.Env.alloc_forced_only
    OSSVerify.omx_clap_core.fuzz_preset.Images.plain
    OSSVerify.Core.Shapes.Budgets.Asan.lim_source en_p inp ->
@YM05.ceil_of_top rc (bv_unsigned sp - stack_max_size) ->
HS h = Some ch ->
cs_ok Asan.M.loaded_segments TFIB YA02.LIMIT (YA02.TOP sp)
(YA02.SINV0 Asan.M.loaded_segments Asan.M.phdrs sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(YA02.argH0 Asan.M.phdrs sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model ->
(forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 Asan.M.phdrs sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) n) ->
(forall a, YA02.argH0 Asan.M.phdrs sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) E a = true ->
FULL a = wrap_mem Asan.M.phdrs sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw a) ->
srealizes Asan.M.loaded_segments (cfg_of Asan.M.loaded_segments R (pc ch) FULL model)
(CLOSEDX (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape) inp).

(* ---------------------------------------------------------------------- *)
(* 3. The statement. Donor: A/AD1q.v:79-83 (tfib_srealizesX), with the no-refusal premise of TFIB_T. *)
Definition tfib_srealizesX_A : Prop :=
forall (rc : YM05.RunCeil) (HS : nat -> option acs),
tfib_startup_T1_A HS -> drv_mainX_stmt_A rc HS ->
forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput) (en_p : ExecEntry),
valid_sp sp -> valid_brk Asan.M.loaded_segments brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
~ run_scfg_budget_refused OSSVerify.Core.Shapes.Env.alloc_forced_only
    OSSVerify.omx_clap_core.fuzz_preset.Images.plain
    OSSVerify.Core.Shapes.Budgets.Asan.lim_source en_p inp ->
@YM05.ceil_of_top rc (bv_unsigned sp - stack_max_size) ->
srealizes Asan.M.loaded_segments (init_config Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs sp brk mb rdraw YA02.LIMIT inp)
(SPECX (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape) inp).

(* ---------------------------------------------------------------------- *)
(* 4. The proof. Donor: A/AB1n.v:74-87 (HS_ok_open, over HS) and A/AD1q.v:84-98 (tfib_srealizesX, with DRV in place of
      DRV_MAINX and the no-refusal premise handed to it). *)
Lemma HS_ok_open_A : forall HS h sp rdraw brk0 argv envp uid hw fs c,
HS_ok_A HS h sp rdraw brk0 argv envp uid hw fs c ->
exists ch E R FULL model,
HS h = Some ch /\ c = cfg_of Asan.M.loaded_segments R (pc ch) FULL model
/\ cs_ok Asan.M.loaded_segments TFIB YA02.LIMIT (YA02.TOP sp)
(YA02.SINV0 Asan.M.loaded_segments Asan.M.phdrs sp rdraw brk0 argv envp uid hw) (YA02.argH0 Asan.M.phdrs sp rdraw argv envp uid hw) fs E ch R FULL model
/\ (forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 Asan.M.phdrs sp rdraw brk0 argv envp uid hw) n)
/\ (forall a, YA02.argH0 Asan.M.phdrs sp rdraw argv envp uid hw E a = true -> FULL a = wrap_mem Asan.M.phdrs sp argv envp uid hw rdraw a)
/\ eb E = eb (YA02.E0 Asan.M.phdrs sp rdraw brk0 argv envp uid hw).
Proof.
intros HS h sp rdraw brk0 argv envp uid hw fs c (ch & E & R & FULL & model & Hh & Hc & HC).
exists ch, E, R, FULL, model. split; [exact Hh|]. split; [exact Hc|]. split; [exact HC|].
destruct (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC) as (S1 & S2 & S3 & _). exact (conj S1 (conj S2 S3)).
Qed.

Theorem tfib_srealizesX_A_holds : tfib_srealizesX_A.
Proof.
intros rc HS HST DRV sp rdraw brk mb inp en_p Hsp Hbrk Hmb Hfit Hinp HNR Hceil.
pose proof Hinp as (Hva & Hve & Hvfs & _ & [Huid Hgid] & Hnof & Hsig & Hhw & Hab & Hmmu & _).
destruct inp as [argv envp fs stdin uid gid groups net nofile sigmask hw ab mmu urnd tmp].
cbn in Hab, Hmmu. subst ab mmu.
change (mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw false Sv48 urnd tmp)
with (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp) in *.
apply (srz_conseq Asan.M.loaded_segments _
(CLOSEDX (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape)
(YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp)));
[| apply t_eq_sym; apply (specx_closedx_eq (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape))].
apply (HST sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp Hsp Hbrk Hva Hve Hfit Huid Hhw
(CLOSEDX (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape)
(YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp))
(CLOSEDX_has_nil (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape) _)).
intros h c Hok.
destruct (HS_ok_open_A HS h sp rdraw brk argv envp uid hw (fs_seed_tmp fs tmp) c Hok)
as (ch & E & R & FULL & model & Hch & -> & HC & HE & HM & _).
exact (DRV sp rdraw brk (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp) en_p h ch E R FULL model
Hsp Hbrk Hfit Hinp HNR Hceil Hch HC HE HM).
Qed.
