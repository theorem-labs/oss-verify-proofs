(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AD2o.v, AD2p.v and AD1q.v (asan) and
   lib/YD2o.v, YD2p.v and YD1q.v (asan-ubsan), ossv/recipes c8557374ad2e, for libreac/fuzz_knock: the closing of
   KnockAsanTop.ASAN_T and ASAN_UBSAN_T from named parts; module paths changed, shape AgreeKnock.ag_sil_shape
   (KnockAsanTop.knock_shape), fuzz_knock's images. Modelled on fuzz_pcap's lib/A/PcapClose.v (cold/port-pcap-comp
   fe3d720b4c7). *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/KnockClose.v at origin/ossv/recipes 6ebe35ba632;
   taken for reac-pw/fuzz_pin image A: shape PinAsanTop.pin_shape (= ag_shape checksum_shape, lib/AgreePin.v's AGS),
   fuzz_pin's images, names knock_* -> pin_*, the parts' owners are the steps of fuzz_pin's image-A route; in BOTH
   Sections the trace tables (knock's lib/A/ACej.v / ACejTfib.v and lib/AU/YCej.v / YCejTfib.v) are Section Variables
   and Hypotheses of the same types, which the joins pass, so this file Requires no file of either image's frame;
   module paths changed. *)
(* The closing side of fuzz_pin's four ASan statements (rule 24: no function proved; this file is assembly).

   The donor closes TFIB_T in two steps: AD2o.v:63-84 applies AD1q.v:79-98 tfib_srealizesX. tfib_srealizesX joins
   the start-up (AB1n.v:52 tfib_startup_T1), the hand-off (AB1n.v:74 HS_ok_open), the driver main (AD1q.v:64-78:
   AD1p.v:84 tfib_drv_main over the parts AD1q.v:41-63) and the spec link (Reusable/YO01 specx_closedx_eq). This file
   does the same over named Section variables and hypotheses, each with the donor statement it stands for and the step
   of fuzz_pin's image-A route that supplies it. Image A (Section asan): P2 (the generated start-up files lib/A/AB01.v,
   AB12.v), P3 (the relocated frame: AB1n, AD2l, AF0w, AF0q, AD2m, ACej, ACejTfib, AD1q and the stdio sites), P4 (the
   program contract lib/A/PPgLib.v and the walks that prove it) and P5 (the join, lib/A/AD2o.v, with the allocator parts
   of lib/A/PinAllocClose.v). Image B (Section asan_ubsan): its lib/AU files and its join.

   Both Sections take the image's allocation-trace tables (universe, its universe_ok, B's universe equation, the
   driver's traces and their inclusion) as Section Variables and Hypotheses, so this file Requires no file of either
   image's frame: the joins pass ACej / ACejTfib (image A) and YCej / YCejTfib (image B).

   The program slot stays inside H_DRIVER, as in fuzz_knock's KnockClose.v; lib/A/AD2o.v supplies it. fuzz_pin's
   entry function ALLOCATES (one malloc(n + 1) and one free per call): its program contract takes the allocator's free
   and malloc facts at B as premises, in the form of libreac/fuzz_ctrl's released walk top (origin/ossv/recipes
   7097a4593001 proofs/libreac/fuzz_ctrl/lib/A/ACtl.v:1184-1185, discharged by the same AF0q / AF0w theorems that feed
   the driver), and lib/A/AD2o.v feeds it the per-FPState allocator facts H_DRIVER receives, which ASAN_T_of_parts
   takes from H_ALLOC_MALLOC / H_ALLOC_FREE. So the allocation adds no Section hypothesis: beyond fuzz_knock's, this
   file adds only the five trace-table Variables and Hypotheses of each Section (above).
   No instance of the plain build's sink (Reusable/YI5b src0_sink_head) is used: this file takes no sink-head argument. *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_pw.fuzz_pin Require Statements.
From OSSVerify.reac_pw.fuzz_pin.images Require Asan AsanUbsan.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK15 YK18 YK09 YK0c YK0e YA01 YA0c YA0e YA02.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG01 YG0f YG0d YC5d YI16 YE00.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YO05 YO09 YO06 YO01 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import PinAsanTop.
Import ListNotations.
Import APC. Import AX2. Import AX2S. Import APG. Import APSG.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.

Local Notation LS := PinAsanTop.pin_shape.

Lemma valid_sp_windowP : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.

(* ===================================================================================================== *)
(* ASan image                                                                                              *)
(* ===================================================================================================== *)
Section asan.
Local Notation segs := OSSVerify.reac_pw.fuzz_pin.images.Asan.M.loaded_segments.
Local Notation ph := OSSVerify.reac_pw.fuzz_pin.images.Asan.M.phdrs.

(* START-UP. Owner: P2 (start-up tables generated from fuzz_pin.asan's own collector run) and P3 (the certificate). *)
(* HS_TBL: the start-up's hand-off states, donor lib/A/AB01.v:597 HS_tfib (per-binary data; pin's lib/A/AB01.v). *)
Variable HS_TBL : nat -> option acs.
(* TFIB_TBL: the image table of the start-up certificate, donor lib/A/AB12.v:10 TFIB (per-binary data; pin's
   lib/A/AB12.v). *)
Variable TFIB_TBL : atable.
(* donor lib/A/AB1n.v:45-51 HS_ok, at HS_TBL / TFIB_TBL and fuzz_pin's ASan image. *)
Definition HS_okA (h : nat) (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (uid hw : word)
    (fs : Fs.Fs) (c : config) : Prop :=
  exists ch E R FULL model,
    HS_TBL h = Some ch
    /\ c = cfg_of segs R (pc ch) FULL model
    /\ cs_ok segs TFIB_TBL YA02.LIMIT (YA02.TOP sp)
         (YA02.SINV0 ph sp rdraw brk0 argv envp uid hw) (YA02.argH0 ph sp rdraw argv envp uid hw) fs E ch R FULL model.
(* H_STARTUP: donor lib/A/AB1n.v:52-60 tfib_startup_T1 (the start-up certificate, closed by AB1n.v:61-73 over
   tfib_startup_closed). Owner: P3 (lib/A/AB1n.v). *)
Hypothesis H_STARTUP :
  forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)) (fs : Fs.Fs) (stdin : InputStream)
    (uid gid hw : word) (groups : list word) (net : NetQueue) (nofile sigmask : word) (urnd : InputStream) (tmp : Fs.Fs),
  valid_sp sp -> valid_brk segs brk0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  valid_id uid -> valid_hwcap hw ->
  forall T : TSet, T [] ->
  (forall h c, HS_okA h sp rdraw brk0 argv envp uid hw (fs_seed_tmp fs tmp) c -> srealizes segs c T) ->
  srealizes segs (init_config segs OSSVerify.reac_pw.fuzz_pin.images.Asan.M.init_pc ph sp brk0 mbase rdraw YA02.LIMIT
    (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp)) T.

(* THE PARTS THE DRIVER CONSUMES (donor lib/A/AD1q.v:41-63, the Section of tfib_srealizesX). *)
(* B: the image's symbol and trace table, donor lib/A/AD2l.v:14 TfibB. Owner: P3 (lib/A/AD2l.v). *)
Variable B : asyms.
(* H_ALLOC_MALLOC: donor lib/A/AD1q.v:43 AMALLOC (closed by lib/A/AF0w.v tfib_amalloc_realizes, through
   lib/A/PinAllocClose.v). Owner: P3 (allocator model, depot-true donor). *)
Hypothesis H_ALLOC_MALLOC : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @amalloc_realizes fx rc segs B.
(* H_ALLOC_FREE: donor lib/A/AD1q.v:44 AFREE (closed by lib/A/AF0q.v afree_realizes_closed, through
   lib/A/PinAllocClose.v). Owner: P3. *)
Hypothesis H_ALLOC_FREE : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_realizes fx rc segs B.
(* H_RT_MEMCPY: donor lib/A/AD1q.v:45 AICPY, the memcpy interceptor (closed by lib/A/AD2m.v tfib_AICPY). Owner:
   P3 (runtime). *)
Hypothesis H_RT_MEMCPY : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc segs B OCpy (pc_wrap_memcpy (as_code B)).
(* donor lib/A/AD1q.v:64-76 drv_mainX_stmt, at HS_TBL / TFIB_TBL, fuzz_pin's ASan image and LS. *)
Definition drv_mainA (rc : YM05.RunCeil) : Prop :=
  forall (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput) (h : nat) (ch : acs) (E : env) (R : bvmap 5 word)
    (FULL : word -> option byte) (model : Model),
  valid_sp sp -> valid_brk segs brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  @YM05.ceil_of_top rc (bv_unsigned sp - stack_max_size) ->
  HS_TBL h = Some ch ->
  cs_ok segs TFIB_TBL YA02.LIMIT (YA02.TOP sp)
    (YA02.SINV0 ph sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (YA02.argH0 ph sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model ->
  (forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 ph sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) n) ->
  (forall a, YA02.argH0 ph sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) E a = true ->
    FULL a = wrap_mem ph sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw a) ->
  srealizes segs (cfg_of segs R (pc ch) FULL model) (CLOSEDX (LS:=LS) inp).
(* THE ASAN TRACE TABLES, Variables and Hypotheses of the types of Section asan_ubsan's (fuzz_knock's lib/A/ACej.v /
   ACejTfib.v names), in this order; lib/A/AD2o.v passes ACej.Tfib_universe, ACej.Tfib_universe_ok, eq_refl,
   ACejTfib.Tfib_drv_traces, ACejTfib.Tfib_universe_drv:
     Tfib_universe      : list (list Z)                                       knock A/ACej.v Tfib_universe
     Tfib_universe_ok   : universe_ok Tfib_universe                           knock A/ACej.v Tfib_universe_ok
     H_TRACES_B         : as_universe B = Tfib_universe                       donor lib/A/AD2l.v:37 (eq_refl at TfibB)
     Tfib_drv_traces    : list (list Z)                                       knock A/ACejTfib.v Tfib_drv_traces
     Tfib_universe_drv  : forall t, In t Tfib_drv_traces -> In t Tfib_universe
                                                                              knock A/ACejTfib.v Tfib_universe_drv
   With them, TfibSyms' fields ts_universe and ts_universe_drv (donor lib/A/AF0m.v:313-314) hold of B. The driver's
   traces are proved, not assumed: pin's lib/A/ACejTfib.v states pin's list and proves each is in pin's universe by
   vm_compute. Owner: P3 (ACej, ACejTfib, AD2l.TfibB). *)
Variable Tfib_universe : list (list Z).
Hypothesis Tfib_universe_ok : universe_ok Tfib_universe.
Hypothesis H_TRACES_B : as_universe B = Tfib_universe.
Variable Tfib_drv_traces : list (list Z).
Hypothesis Tfib_universe_drv : forall t, In t Tfib_drv_traces -> In t Tfib_universe.
Local Notation DRV_TRACES := Tfib_drv_traces.
(* H_DRIVER: donor lib/A/AD1p.v:84 tfib_drv_main (the core's driver walk, AD1q.v:77-78 DRV_MAINX), as a function of
   the parts above. Its other donor premises stay inside this hypothesis, as in fuzz_knock's KnockClose.v: LIBX :
   tfib_lib_contract_x_all (AD1q.v:50; pin: lib/A/PPgLib.pin_lib_contract_x_all_tfib over PPgLib.pin_lib_x_all,
   with the wrapper contracts of lib/A/PinWrapBinders.v and the free / malloc facts of the second and first arguments
   below), HB : TfibSyms B less its two trace fields (AF0m.v:292), ARDCHK : aread_check_stmt B (AD1i.v:18),
   MT_FREE / RO_IN (AD1q.v:48-49; in_ro_tfa ACeg.v:42), and the driver's stdio sites xst/XFR/PF1/PFN and
   est/ESTI/ESTF/FWS/RFS/FPO/FPR/FPU/EXS (AD1w.v:119-151, AD1x.v:36-93). lib/A/AD2o.v discharges it. Owners: P3
   (core), P4 (LIBX), P5 (the join, lib/A/AD2o.v). *)
Hypothesis H_DRIVER : forall (rc : YM05.RunCeil),
  (forall fx : YK11.FPState, @amalloc_realizes fx rc segs B) ->
  (forall fx : YK11.FPState, @afree_realizes fx rc segs B) ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc segs B OCpy (pc_wrap_memcpy (as_code B))) ->
  universe_ok (as_universe B) ->
  (forall t, In t DRV_TRACES -> In t (as_universe B)) ->
  drv_mainA rc.

(* donor lib/A/AB1n.v:74-87 HS_ok_open, the same proof (cs_ok's co_sinv field, Reusable/YA0e.v). *)
Lemma HS_ok_openA : forall h sp rdraw brk0 argv envp uid hw fs c,
  HS_okA h sp rdraw brk0 argv envp uid hw fs c ->
  exists ch E R FULL model,
    HS_TBL h = Some ch /\ c = cfg_of segs R (pc ch) FULL model
    /\ cs_ok segs TFIB_TBL YA02.LIMIT (YA02.TOP sp)
         (YA02.SINV0 ph sp rdraw brk0 argv envp uid hw) (YA02.argH0 ph sp rdraw argv envp uid hw) fs E ch R FULL model
    /\ (forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 ph sp rdraw brk0 argv envp uid hw) n)
    /\ (forall a, YA02.argH0 ph sp rdraw argv envp uid hw E a = true -> FULL a = wrap_mem ph sp argv envp uid hw rdraw a)
    /\ eb E = eb (YA02.E0 ph sp rdraw brk0 argv envp uid hw).
Proof.
  intros h sp rdraw brk0 argv envp uid hw fs c (ch & E & R & FULL & model & Hh & Hc & HC).
  exists ch, E, R, FULL, model. split; [exact Hh|]. split; [exact Hc|]. split; [exact HC|].
  exact (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC).
Qed.

Section RC. Context {rc : YM05.RunCeil}.
(* donor lib/A/AD1q.v:77-78 DRV_MAINX, from H_DRIVER and the parts. *)
Lemma DRV_MAINA : drv_mainA rc.
Proof.
  apply (H_DRIVER rc (H_ALLOC_MALLOC rc) (H_ALLOC_FREE rc) (H_RT_MEMCPY rc)).
  - rewrite H_TRACES_B. exact Tfib_universe_ok.
  - intros t Ht. rewrite H_TRACES_B. exact (Tfib_universe_drv t Ht).
Qed.
(* donor lib/A/AD1q.v:79-98 tfib_srealizesX, the same proof. *)
Lemma pin_srealizesX_rc : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
  valid_sp sp -> valid_brk segs brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  srealizes segs (init_config segs OSSVerify.reac_pw.fuzz_pin.images.Asan.M.init_pc ph sp brk mb rdraw YA02.LIMIT inp)
    (SPECX (LS:=LS) inp).
Proof.
  intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil.
  pose proof Hinp as (Hva & Hve & Hvfs & _ & [Huid Hgid] & Hnof & Hsig & Hhw & Hab & Hmmu & _).
  destruct inp as [argv envp fs stdin uid gid groups net nofile sigmask hw ab mmu urnd tmp]. cbn in *. subst ab mmu.
  change (mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw false Sv48 urnd tmp)
    with (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp) in *.
  apply (srz_conseq segs _ (CLOSEDX (LS:=LS) (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp)));
    [| apply t_eq_sym; apply (specx_closedx_eq (LS:=LS))].
  apply (H_STARTUP sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp Hsp Hbrk Hva Hve Hfit Huid Hhw
    (CLOSEDX (LS:=LS) (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp))
    (CLOSEDX_has_nil (LS:=LS) _)).
  intros h c Hok.
  destruct (HS_ok_openA h sp rdraw brk argv envp uid hw (fs_seed_tmp fs tmp) c Hok) as (ch & E & R & FULL & model & Hch & -> & HC & HE & HM & _).
  exact (DRV_MAINA sp rdraw brk (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp) h ch E R FULL model
    Hsp Hbrk Hfit Hinp Hceil Hch HC HE HM).
Qed.
End RC.

(* donor lib/A/AD2o.v:75-84 tfib_srealizesX_top and TFIB_T_of_partsXF; this kit's YM05.RunCeilOf takes the lim argument. *)
Theorem ASAN_T_of_parts : PinAsanTop.ASAN_T.
Proof.
  intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp.
  change target_alloc_limit with YA02.LIMIT.
  exact (@pin_srealizesX_rc (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowP sp Hsp) YA02.LIMIT) sp rnd brk mbase inp
    Hsp Hbrk Hmb Hfit Hinp (YM05.ceil_of_top_run _)).
Qed.

(* The two ASan statements, given only the named parts above. *)
Theorem pin_asan_agrees_of_parts : Statements.asan_agrees.
Proof. exact (PinAsanTop.asan_agrees_of_asan_side ASAN_T_of_parts). Qed.
Theorem pin_asan_halts_of_parts : Statements.asan_halts.
Proof. exact (PinAsanTop.asan_halts_of_asan_side ASAN_T_of_parts). Qed.
(* Inside the Section, Print Assumptions lists the named parts these two statements rest on. *)
Print Assumptions pin_asan_agrees_of_parts.
Print Assumptions pin_asan_halts_of_parts.
End asan.

(* ===================================================================================================== *)
(* ASan+UBSan image (donor lib/YD2o.v, YD2p.v, YD1q.v)                                                      *)
(* ===================================================================================================== *)
Section asan_ubsan.
Local Notation segs := OSSVerify.reac_pw.fuzz_pin.images.AsanUbsan.M.loaded_segments.
Local Notation ph := OSSVerify.reac_pw.fuzz_pin.images.AsanUbsan.M.phdrs.

(* START-UP (asan-ubsan). HS_TBL_U: donor lib/YB01.v:597 HS_tfib; TFIB_TBL_U: donor lib/YB12.v:10 TFIB (pin's
   lib/AU/YB12.v). Owner: image B. *)
Variable HS_TBL_U : nat -> option acs.
Variable TFIB_TBL_U : atable.
(* donor lib/YB1n.v:44-50 HS_ok. *)
Definition HS_okU (h : nat) (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (uid hw : word)
    (fs : Fs.Fs) (c : config) : Prop :=
  exists ch E R FULL model,
    HS_TBL_U h = Some ch
    /\ c = cfg_of segs R (pc ch) FULL model
    /\ cs_ok segs TFIB_TBL_U YA02.LIMIT (YA02.TOP sp)
         (YA02.SINV0 ph sp rdraw brk0 argv envp uid hw) (YA02.argH0 ph sp rdraw argv envp uid hw) fs E ch R FULL model.
(* H_STARTUP_U: donor lib/YB1n.v:51-59 tfib_startup_T1. Owner: image B. *)
Hypothesis H_STARTUP_U :
  forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)) (fs : Fs.Fs) (stdin : InputStream)
    (uid gid hw : word) (groups : list word) (net : NetQueue) (nofile sigmask : word) (urnd : InputStream) (tmp : Fs.Fs),
  valid_sp sp -> valid_brk segs brk0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  valid_id uid -> valid_hwcap hw ->
  forall T : TSet, T [] ->
  (forall h c, HS_okU h sp rdraw brk0 argv envp uid hw (fs_seed_tmp fs tmp) c -> srealizes segs c T) ->
  srealizes segs (init_config segs OSSVerify.reac_pw.fuzz_pin.images.AsanUbsan.M.init_pc ph sp brk0 mbase rdraw YA02.LIMIT
    (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp)) T.

(* THE PARTS (donor lib/YD1q.v Section d, the twin of AD1q.v:41-63). *)
(* B_U: donor lib/YD2l.v:11 TfibB. Owner: image B (lib/AU/YD2l.v). *)
Variable B_U : asyms.
(* H_ALLOC_MALLOC_U / H_ALLOC_FREE_U: donor lib/YF0w.v:43, lib/YF0q.v:9. Owner: image B (AU core twins). *)
Hypothesis H_ALLOC_MALLOC_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @amalloc_realizes fx rc segs B_U.
Hypothesis H_ALLOC_FREE_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_realizes fx rc segs B_U.
(* H_RT_MEMCPY_U: donor lib/YD2m.v:15 tfib_AICPY. Owner: image B (AU core twin). *)
Hypothesis H_RT_MEMCPY_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc segs B_U OCpy (pc_wrap_memcpy (as_code B_U)).
(* donor lib/YD1q.v drv_mainX_stmt (the twin of AD1q.v:64-76). *)
Definition drv_mainU (rc : YM05.RunCeil) : Prop :=
  forall (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput) (h : nat) (ch : acs) (E : env) (R : bvmap 5 word)
    (FULL : word -> option byte) (model : Model),
  valid_sp sp -> valid_brk segs brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  @YM05.ceil_of_top rc (bv_unsigned sp - stack_max_size) ->
  HS_TBL_U h = Some ch ->
  cs_ok segs TFIB_TBL_U YA02.LIMIT (YA02.TOP sp)
    (YA02.SINV0 ph sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (YA02.argH0 ph sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model ->
  (forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 ph sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) n) ->
  (forall a, YA02.argH0 ph sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) E a = true ->
    FULL a = wrap_mem ph sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw a) ->
  srealizes segs (cfg_of segs R (pc ch) FULL model) (CLOSEDX (LS:=LS) inp).
(* THE ASAN-UBSAN TRACE TABLES. fuzz_knock's KnockClose.v names them from lib/AU/YCej.v and lib/AU/YCejTfib.v; on
   fuzz_pin those image-B files are not on image A's branches, so this Section takes them as Variables and
   Hypotheses of exactly the types of knock's names, in this order (image B's lib/AU/YD2o.v passes its own):
     Tfib_universe_U      : list (list Z)                                     knock AU/YCej.v:30 Tfib_universe
     Tfib_universe_ok_U   : universe_ok Tfib_universe_U                       knock AU/YCej.v:74 Tfib_universe_ok
     H_TRACES_B_U         : as_universe B_U = Tfib_universe_U                 knock KnockClose.v:250 (eq_refl at YD2l)
     Tfib_drv_traces_U    : list (list Z)                                     knock AU/YCejTfib.v:25 Tfib_drv_traces
     Tfib_universe_drv_U  : forall t, In t Tfib_drv_traces_U -> In t Tfib_universe_U
                                                                              knock AU/YCejTfib.v:28 Tfib_universe_drv *)
Variable Tfib_universe_U : list (list Z).
Hypothesis Tfib_universe_ok_U : universe_ok Tfib_universe_U.
(* H_TRACES_B_U: donor lib/YD2l.v as_universe := Tfib_universe. Owner: image B (YD2l); closes by reflexivity. *)
Hypothesis H_TRACES_B_U : as_universe B_U = Tfib_universe_U.
(* As on the ASan side, the driver's traces are proved, not assumed, by image B's lib/AU/YCejTfib.v. *)
Variable Tfib_drv_traces_U : list (list Z).
Hypothesis Tfib_universe_drv_U : forall t, In t Tfib_drv_traces_U -> In t Tfib_universe_U.
Local Notation DRV_TRACES_U := Tfib_drv_traces_U.
(* H_DRIVER_U: donor lib/YD1p.v:77 tfib_drv_main (YD1q's DRV_MAINX); its LIBX is lib/YCfn.v's (pin: image B's
   program contract), with the same absorbed core parts as H_DRIVER. Owner: image B (AU core, join lib/AU/YD2o.v). *)
Hypothesis H_DRIVER_U : forall (rc : YM05.RunCeil),
  (forall fx : YK11.FPState, @amalloc_realizes fx rc segs B_U) ->
  (forall fx : YK11.FPState, @afree_realizes fx rc segs B_U) ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc segs B_U OCpy (pc_wrap_memcpy (as_code B_U))) ->
  universe_ok (as_universe B_U) ->
  (forall t, In t DRV_TRACES_U -> In t (as_universe B_U)) ->
  drv_mainU rc.

Lemma HS_ok_openU : forall h sp rdraw brk0 argv envp uid hw fs c,
  HS_okU h sp rdraw brk0 argv envp uid hw fs c ->
  exists ch E R FULL model,
    HS_TBL_U h = Some ch /\ c = cfg_of segs R (pc ch) FULL model
    /\ cs_ok segs TFIB_TBL_U YA02.LIMIT (YA02.TOP sp)
         (YA02.SINV0 ph sp rdraw brk0 argv envp uid hw) (YA02.argH0 ph sp rdraw argv envp uid hw) fs E ch R FULL model
    /\ (forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 ph sp rdraw brk0 argv envp uid hw) n)
    /\ (forall a, YA02.argH0 ph sp rdraw argv envp uid hw E a = true -> FULL a = wrap_mem ph sp argv envp uid hw rdraw a)
    /\ eb E = eb (YA02.E0 ph sp rdraw brk0 argv envp uid hw).
Proof.
  intros h sp rdraw brk0 argv envp uid hw fs c (ch & E & R & FULL & model & Hh & Hc & HC).
  exists ch, E, R, FULL, model. split; [exact Hh|]. split; [exact Hc|]. split; [exact HC|].
  exact (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC).
Qed.

Section RCU. Context {rc : YM05.RunCeil}.
Lemma DRV_MAINU : drv_mainU rc.
Proof.
  apply (H_DRIVER_U rc (H_ALLOC_MALLOC_U rc) (H_ALLOC_FREE_U rc) (H_RT_MEMCPY_U rc)).
  - rewrite H_TRACES_B_U. exact Tfib_universe_ok_U.
  - intros t Ht. rewrite H_TRACES_B_U. exact (Tfib_universe_drv_U t Ht).
Qed.
(* donor lib/YD1q.v:75 tfib_srealizesX, the same proof. *)
Lemma pin_srealizesXU_rc : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
  valid_sp sp -> valid_brk segs brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  srealizes segs (init_config segs OSSVerify.reac_pw.fuzz_pin.images.AsanUbsan.M.init_pc ph sp brk mb rdraw YA02.LIMIT inp)
    (SPECX (LS:=LS) inp).
Proof.
  intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil.
  pose proof Hinp as (Hva & Hve & Hvfs & _ & [Huid Hgid] & Hnof & Hsig & Hhw & Hab & Hmmu & _).
  destruct inp as [argv envp fs stdin uid gid groups net nofile sigmask hw ab mmu urnd tmp]. cbn in *. subst ab mmu.
  change (mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw false Sv48 urnd tmp)
    with (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp) in *.
  apply (srz_conseq segs _ (CLOSEDX (LS:=LS) (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp)));
    [| apply t_eq_sym; apply (specx_closedx_eq (LS:=LS))].
  apply (H_STARTUP_U sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp Hsp Hbrk Hva Hve Hfit Huid Hhw
    (CLOSEDX (LS:=LS) (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp))
    (CLOSEDX_has_nil (LS:=LS) _)).
  intros h c Hok.
  destruct (HS_ok_openU h sp rdraw brk argv envp uid hw (fs_seed_tmp fs tmp) c Hok) as (ch & E & R & FULL & model & Hch & -> & HC & HE & HM & _).
  exact (DRV_MAINU sp rdraw brk (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp) h ch E R FULL model
    Hsp Hbrk Hfit Hinp Hceil Hch HC HE HM).
Qed.
End RCU.

Theorem ASAN_UBSAN_T_of_parts : PinAsanTop.ASAN_UBSAN_T.
Proof.
  intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp.
  change target_alloc_limit with YA02.LIMIT.
  exact (@pin_srealizesXU_rc (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowP sp Hsp) YA02.LIMIT) sp rnd brk mbase inp
    Hsp Hbrk Hmb Hfit Hinp (YM05.ceil_of_top_run _)).
Qed.

Theorem pin_asan_ubsan_agrees_of_parts : Statements.asan_ubsan_agrees.
Proof. exact (PinAsanTop.asan_ubsan_agrees_of_asan_side ASAN_UBSAN_T_of_parts). Qed.
Theorem pin_asan_ubsan_halts_of_parts : Statements.asan_ubsan_halts.
Proof. exact (PinAsanTop.asan_ubsan_halts_of_asan_side ASAN_UBSAN_T_of_parts). Qed.
Print Assumptions pin_asan_ubsan_agrees_of_parts.
Print Assumptions pin_asan_ubsan_halts_of_parts.
End asan_ubsan.

(* Outside the Sections the named parts are arguments of each theorem; Print Assumptions then lists only global axioms. *)
Print Assumptions pin_asan_agrees_of_parts.
Print Assumptions pin_asan_halts_of_parts.
Print Assumptions pin_asan_ubsan_agrees_of_parts.
Print Assumptions pin_asan_ubsan_halts_of_parts.
(* The argument order the joins pass (lib/A/AD2o.v for image A, image B's join for image B): 13 arguments each. *)
Check ASAN_T_of_parts.
Check ASAN_UBSAN_T_of_parts.
