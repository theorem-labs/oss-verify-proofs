(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AD2o.v, AD2p.v and AD1q.v (asan) and
   lib/YD2o.v, YD2p.v and YD1q.v (asan-ubsan), ossv/recipes c8557374ad2e, for libreac/fuzz_knock: the closing of
   KnockAsanTop.ASAN_T and ASAN_UBSAN_T from named parts; module paths changed, shape AgreeKnock.ag_sil_shape
   (KnockAsanTop.knock_shape), fuzz_knock's images. Modelled on
   fuzz_pcap's lib/A/PcapClose.v. *)
(* The closing side of fuzz_knock's four ASan statements (rule 24: no function proved; this file is assembly).

   The donor closes TFIB_T in two steps: AD2o.v:63-84 applies AD1q.v:79-98 tfib_srealizesX. tfib_srealizesX joins
   the start-up (AB1n.v:52 tfib_startup_T1), the hand-off (AB1n.v:74 HS_ok_open), the driver main (AD1q.v:64-78:
   AD1p.v:84 tfib_drv_main over the parts AD1q.v:41-63) and the spec link (Reusable/YO01 specx_closedx_eq). This file
   does the same at the level whose TYPES are on knock's trunk (a working branch). Every input is a named Section
   variable or hypothesis below, with the donor statement it stands for and the lane that supplies it.

   The program contract (donor A/ACfn.v:71 tfib_lib_contract_x_all; knock's is a Theorem Labs lane's APgLib.knock_lib_contract_x_all)
   is not on the trunk yet, so the program slot stays inside H_DRIVER / H_DRIVER_U, as fuzz_pcap's asan-ubsan side does.
   No instance of the plain build's sink (Reusable/YI5b src0_sink_head) is used: this file takes no sink-head argument. *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_knock Require Statements.
From OSSVerify.libreac.fuzz_knock.images Require Asan AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require AgreeKnock.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK11 YK15 YK18 YK09 YK0c YK0e YA01 YA0c YA0e YA02.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG00 YG01 YG0f YG0d YC5d YI16 YE00.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YO05 YO09 YO06 YO01 YM05.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require ACej ACejTfib.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require YCej YCejTfib.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import KnockAsanTop.
Import ListNotations.
Import APC. Import AX2. Import AX2S. Import APG. Import APSG.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.

Local Notation LS := KnockAsanTop.knock_shape.

Lemma valid_sp_windowK : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.

(* ===================================================================================================== *)
(* ASan image                                                                                              *)
(* ===================================================================================================== *)
Section asan.
Local Notation segs := OSSVerify.libreac.fuzz_knock.images.Asan.M.loaded_segments.
Local Notation ph := OSSVerify.libreac.fuzz_knock.images.Asan.M.phdrs.

(* START-UP. Owner: a Theorem Labs lane (start-up certificate; per-binary tables generated from knock's asan pin). *)
(* HS_TBL: the start-up's hand-off states, donor lib/A/AB01.v:597 HS_tfib (per-binary data). *)
Variable HS_TBL : nat -> option acs.
(* TFIB_TBL: the image table of the start-up certificate, donor lib/A/AB12.v:10 TFIB (per-binary data; knock's
   lib/A/AB12.v on the trunk). *)
Variable TFIB_TBL : atable.
(* donor lib/A/AB1n.v:45-51 HS_ok, at HS_TBL / TFIB_TBL and fuzz_knock's ASan image. *)
Definition HS_okA (h : nat) (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (uid hw : word)
    (fs : Fs.Fs) (c : config) : Prop :=
  exists ch E R FULL model,
    HS_TBL h = Some ch
    /\ c = cfg_of segs R (pc ch) FULL model
    /\ cs_ok segs TFIB_TBL YA02.LIMIT (YA02.TOP sp)
         (YA02.SINV0 ph sp rdraw brk0 argv envp uid hw) (YA02.argH0 ph sp rdraw argv envp uid hw) fs E ch R FULL model.
(* H_STARTUP: donor lib/A/AB1n.v:52-60 tfib_startup_T1 (the start-up certificate, closed by AB1n.v:61-73 over
   tfib_startup_closed). Owner: a Theorem Labs lane. *)
Hypothesis H_STARTUP :
  forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)) (fs : Fs.Fs) (stdin : InputStream)
    (uid gid hw : word) (groups : list word) (net : NetQueue) (nofile sigmask : word) (urnd : InputStream) (tmp : Fs.Fs),
  valid_sp sp -> valid_brk segs brk0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  valid_id uid -> valid_hwcap hw ->
  forall T : TSet, T [] ->
  (forall h c, HS_okA h sp rdraw brk0 argv envp uid hw (fs_seed_tmp fs tmp) c -> srealizes segs c T) ->
  srealizes segs (init_config segs OSSVerify.libreac.fuzz_knock.images.Asan.M.init_pc ph sp brk0 mbase rdraw YA02.LIMIT
    (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp)) T.

(* THE PARTS THE DRIVER CONSUMES (donor lib/A/AD1q.v:41-63, the Section of tfib_srealizesX), as far as their types
   are on the trunk. *)
(* B: the image's symbol and trace table, donor lib/A/AD2l.v:14 TfibB. Owner: the relocated A core (a Theorem Labs lane,
   AD2l on a working branch). *)
Variable B : asyms.
(* H_ALLOC_MALLOC: donor lib/A/AD1q.v:43 AMALLOC (closed in the donor by lib/A/AF0w.v:44 tfib_amalloc_realizes). Owner: the
   allocator model of the relocated A core (a Theorem Labs lane). *)
Hypothesis H_ALLOC_MALLOC : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @amalloc_realizes fx rc segs B.
(* H_ALLOC_FREE: donor lib/A/AD1q.v:44 AFREE (closed in the donor by lib/A/AF0q.v:12 afree_realizes_closed). Owner: a Theorem Labs lane. *)
Hypothesis H_ALLOC_FREE : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_realizes fx rc segs B.
(* H_RT_MEMCPY: donor lib/A/AD1q.v:45 AICPY, the memcpy interceptor (closed in the donor by lib/A/AD2m.v:16 tfib_AICPY). Owner:
   the runtime of the relocated A core (a Theorem Labs lane). *)
Hypothesis H_RT_MEMCPY : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc segs B OCpy (pc_wrap_memcpy (as_code B)).
(* donor lib/A/AD1q.v:64-76 drv_mainX_stmt, at HS_TBL / TFIB_TBL, fuzz_knock's ASan image and LS. *)
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
(* H_TRACES_B: B's allocation-trace universe is knock's (donor lib/A/AD2l.v:37 as_universe := Tfib_universe); with it,
   TfibSyms' field ts_universe (donor lib/A/AF0m.v:313) is knock's lib/A/ACej.v:73 Tfib_universe_ok. Owner:
   a Theorem Labs lane (TfibB); closes by reflexivity once TfibB is on the trunk. *)
Hypothesis H_TRACES_B : as_universe B = ACej.Tfib_universe.
(* The driver's allocation traces (donor lib/A/AF0m.v:18-20 DRV_TRACES; field ts_universe_drv, AF0m.v:314) are PROVED
   here, not assumed: lib/A/ACejTfib.v states knock's list (the one knock's AF0m.v:23-31 defines) and proves each is in
   knock's universe by vm_compute, as fuzz_pcap's lib/A/ACejTfib.v does. *)
Local Notation DRV_TRACES := ACejTfib.Tfib_drv_traces.
(* H_DRIVER: donor lib/A/AD1p.v:84 tfib_drv_main (the core's driver walk, AD1q.v:77-78 DRV_MAINX), as a function of
   the parts above whose types are on the trunk. Its other donor premises are typed by files not yet on the trunk, so
   they stay inside this hypothesis until then: LIBX : tfib_lib_contract_x_all (AD1q.v:50; knock: a Theorem Labs lane's
   lib/A/APgLib.knock_lib_contract_x_all with ameter_triv, XL0, RO 0x96070..0x972c8), HB : TfibSyms B less its two trace
   fields (AF0m.v:292), ARDCHK : aread_check_stmt B (AD1i.v:18), MT_FREE / RO_IN (AD1q.v:48-49; in_ro_tfa ACeg.v:42),
   and the driver's stdio sites xst/XFR/PF1/PFN and est/ESTI/ESTF/FWS/RFS/FPO/FPR/FPU/EXS (AD1w.v:119-151, AD1x.v:36-93;
   knock's strings 0x1d5bb / 0x1d5d0 / 0x157bd). Owners: a Theorem Labs lane (core), a Theorem Labs lane (LIBX), a Theorem Labs lane (the join,
   lib/A/AD2o.v / AD2p.v). *)
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
  - rewrite H_TRACES_B. exact ACej.Tfib_universe_ok.
  - intros t Ht. rewrite H_TRACES_B. exact (ACejTfib.Tfib_universe_drv t Ht).
Qed.
(* donor lib/A/AD1q.v:79-98 tfib_srealizesX, the same proof. *)
Lemma knock_srealizesX_rc : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
  valid_sp sp -> valid_brk segs brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  srealizes segs (init_config segs OSSVerify.libreac.fuzz_knock.images.Asan.M.init_pc ph sp brk mb rdraw YA02.LIMIT inp)
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

(* donor lib/A/AD2o.v:75-84 tfib_srealizesX_top and TFIB_T_of_partsXF; knock's YM05.RunCeilOf takes the lim argument. *)
Theorem ASAN_T_of_parts : KnockAsanTop.ASAN_T.
Proof.
  intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp.
  change target_alloc_limit with YA02.LIMIT.
  exact (@knock_srealizesX_rc (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowK sp Hsp) YA02.LIMIT) sp rnd brk mbase inp
    Hsp Hbrk Hmb Hfit Hinp (YM05.ceil_of_top_run _)).
Qed.

(* The two ASan statements, given only the named parts above. *)
Theorem knock_asan_agrees_of_parts : Statements.asan_agrees.
Proof. exact (KnockAsanTop.asan_agrees_of_asan_side ASAN_T_of_parts). Qed.
Theorem knock_asan_halts_of_parts : Statements.asan_halts.
Proof. exact (KnockAsanTop.asan_halts_of_asan_side ASAN_T_of_parts). Qed.
(* Inside the Section, Print Assumptions lists the named parts these two statements rest on. *)
Print Assumptions knock_asan_agrees_of_parts.
Print Assumptions knock_asan_halts_of_parts.
End asan.

(* ===================================================================================================== *)
(* ASan+UBSan image (donor lib/YD2o.v, YD2p.v, YD1q.v)                                                      *)
(* ===================================================================================================== *)
Section asan_ubsan.
Local Notation segs := OSSVerify.libreac.fuzz_knock.images.AsanUbsan.M.loaded_segments.
Local Notation ph := OSSVerify.libreac.fuzz_knock.images.AsanUbsan.M.phdrs.

(* START-UP (asan-ubsan). HS_TBL_U: donor lib/YB01.v:597 HS_tfib; TFIB_TBL_U: donor lib/YB12.v:10 TFIB (knock's
   lib/AU/YB12.v on the trunk). Owner: a Theorem Labs lane. *)
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
(* H_STARTUP_U: donor lib/YB1n.v:51-59 tfib_startup_T1. Owner: a Theorem Labs lane. *)
Hypothesis H_STARTUP_U :
  forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)) (fs : Fs.Fs) (stdin : InputStream)
    (uid gid hw : word) (groups : list word) (net : NetQueue) (nofile sigmask : word) (urnd : InputStream) (tmp : Fs.Fs),
  valid_sp sp -> valid_brk segs brk0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  valid_id uid -> valid_hwcap hw ->
  forall T : TSet, T [] ->
  (forall h c, HS_okU h sp rdraw brk0 argv envp uid hw (fs_seed_tmp fs tmp) c -> srealizes segs c T) ->
  srealizes segs (init_config segs OSSVerify.libreac.fuzz_knock.images.AsanUbsan.M.init_pc ph sp brk0 mbase rdraw YA02.LIMIT
    (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp)) T.

(* THE PARTS (donor lib/YD1q.v Section d, the twin of AD1q.v:41-63). *)
(* B_U: donor lib/YD2l.v:11 TfibB. Owner: a Theorem Labs lane (lib/AU/YD2l.v on a working branch). *)
Variable B_U : asyms.
(* H_ALLOC_MALLOC_U / H_ALLOC_FREE_U: donor lib/YF0w.v:43, lib/YF0q.v:9. Owner: a Theorem Labs lane (AU core twins). *)
Hypothesis H_ALLOC_MALLOC_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @amalloc_realizes fx rc segs B_U.
Hypothesis H_ALLOC_FREE_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_realizes fx rc segs B_U.
(* H_RT_MEMCPY_U: donor lib/YD2m.v:15 tfib_AICPY. Owner: a Theorem Labs lane (AU core twin). *)
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
(* H_TRACES_B_U: donor lib/YD2l.v as_universe := Tfib_universe; knock's lib/AU/YCej.v:74 Tfib_universe_ok. Owner:
   a Theorem Labs lane (YD2l); closes by reflexivity. *)
Hypothesis H_TRACES_B_U : as_universe B_U = YCej.Tfib_universe.
(* As on the ASan side, the driver's traces are PROVED, not assumed: lib/AU/YCejTfib.v. *)
Local Notation DRV_TRACES_U := YCejTfib.Tfib_drv_traces.
(* H_DRIVER_U: donor lib/YD1p.v:77 tfib_drv_main (YD1q's DRV_MAINX); its LIBX is lib/YCfn.v's (knock: a Theorem Labs lane's
   lib/AU/APgLib.knock_lib_contract_x_all, RO 0x960b8..0x97310), with the same absorbed core parts as H_DRIVER. Owners:
   a Theorem Labs lane (AU core, join lib/AU/YD2o.v / YD2p.v), a Theorem Labs lane (LIBX). *)
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
  - rewrite H_TRACES_B_U. exact YCej.Tfib_universe_ok.
  - intros t Ht. rewrite H_TRACES_B_U. exact (YCejTfib.Tfib_universe_drv t Ht).
Qed.
(* donor lib/YD1q.v:75 tfib_srealizesX, the same proof. *)
Lemma knock_srealizesXU_rc : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
  valid_sp sp -> valid_brk segs brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  srealizes segs (init_config segs OSSVerify.libreac.fuzz_knock.images.AsanUbsan.M.init_pc ph sp brk mb rdraw YA02.LIMIT inp)
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

Theorem ASAN_UBSAN_T_of_parts : KnockAsanTop.ASAN_UBSAN_T.
Proof.
  intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp.
  change target_alloc_limit with YA02.LIMIT.
  exact (@knock_srealizesXU_rc (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowK sp Hsp) YA02.LIMIT) sp rnd brk mbase inp
    Hsp Hbrk Hmb Hfit Hinp (YM05.ceil_of_top_run _)).
Qed.

Theorem knock_asan_ubsan_agrees_of_parts : Statements.asan_ubsan_agrees.
Proof. exact (KnockAsanTop.asan_ubsan_agrees_of_asan_side ASAN_UBSAN_T_of_parts). Qed.
Theorem knock_asan_ubsan_halts_of_parts : Statements.asan_ubsan_halts.
Proof. exact (KnockAsanTop.asan_ubsan_halts_of_asan_side ASAN_UBSAN_T_of_parts). Qed.
Print Assumptions knock_asan_ubsan_agrees_of_parts.
Print Assumptions knock_asan_ubsan_halts_of_parts.
End asan_ubsan.

(* Outside the Sections the named parts are arguments of each theorem; Print Assumptions then lists only global axioms. *)
Print Assumptions knock_asan_agrees_of_parts.
Print Assumptions knock_asan_halts_of_parts.
Print Assumptions knock_asan_ubsan_agrees_of_parts.
Print Assumptions knock_asan_ubsan_halts_of_parts.
