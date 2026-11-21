(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AD2o.v, AD2p.v and AD1q.v (asan) and
   lib/YD2o.v, YD2p.v and YD1q.v (asan-ubsan), for libreac/fuzz_knock: the closing of
   KnockAsanTop.ASAN_T and ASAN_UBSAN_T from named parts; module paths changed, shape AgreeKnock.ag_sil_shape
   (KnockAsanTop.knock_shape), fuzz_knock's images. Modelled on fuzz_pcap's lib/A/PcapClose.v.
   *)
(* Modified by Theorem Labs, 2026-10: taken for reac-pw/fuzz_qdisc image A from proofs/libreac/fuzz_knock/lib/A/KnockClose.v:
   shape QdiscAsanTop.qdisc_shape (= AgreeQdisc.ag_sil_shape), fuzz_qdisc's images,
   names knock_* -> qdisc_*, the parts' owners are the lanes of fuzz_qdisc; in Section asan_ubsan the trace tables of
   knock's lib/AU/YCej.v / YCejTfib.v are Section Variables and Hypotheses of the same types; module paths changed. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_qdisc/lib/A/QdiscClose.v, for reac-pw/fuzz_role image A
   (Section asan) and image B (Section asan_ubsan): shape RoleAsanTop.role_shape, fuzz_role's images, names qdisc_* ->
   role_*; Section asan also takes its trace tables as Section Variables and Hypotheses of the types of Section
   asan_ubsan's (so this file Requires no lib/A file of the image A frame); the role agreement statements take
   RoleAsanTop.PLAIN_SLOT_AG; module paths changed. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RoleClose.v, for reac-pw/fuzz_rate image A
   (Section asan) and image B (Section asan_ubsan): shape RateAsanTop.rate_shape, fuzz_rate's images, names role_* ->
   rate_*, the same Section Variables and Hypotheses in the same order; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (fdchan's third conjunct, the launch's channel-reader flag, carried in cs_ok (co_rdr) and threaded to the fd sites; the auxiliary vector sized by the run's CONFIG_RSEQ flag; the launch's ProcInput, mmap base and entry draw; the launch input with its SIGPIPE default free; the mmap base kept by every step; the launch's string area with the exec file name); internal commit ids in comments replaced by public commits or removed. *)
(* The closing side of fuzz_rate's four ASan statements (rule 24: no function proved; this file is assembly).

   The donor closes TFIB_T in two steps: AD2o.v:63-84 applies AD1q.v:79-98 tfib_srealizesX. tfib_srealizesX joins
   the start-up (AB1n.v:52 tfib_startup_T1), the hand-off (AB1n.v:74 HS_ok_open), the driver main (AD1q.v:64-78:
   AD1p.v:84 tfib_drv_main over the parts AD1q.v:41-63) and the spec link (Reusable/YO01 specx_closedx_eq). This file
   does the same over named Section variables and hypotheses, each with the donor statement it stands for and the part
   of fuzz_rate's tree that supplies it. Image A (Section asan): the generated start-up files lib/A/AB01.v, AB12.v, the
   relocated frame (AB1n, AD2l, AF0w, AF0q, AD2m, ACej, ACejTfib, AD1p and the stdio sites), the program contract
   (lib/A/RtPgLib.v) and the join (lib/A/AD2o.v). Image B (Section asan_ubsan): its lib/AU files and its join
   lib/AU/YD2o.v.

   Both Sections take the image's allocation-trace tables (universe, its universe_ok, B's universe equation, the
   driver's traces and their inclusion) as Section Variables and Hypotheses, so this file Requires no file of either
   image's frame: the joins pass ACej / ACejTfib (image A) and YCej / YCejTfib (image B).

   fuzz_rate's entry function ALLOCATES (three blocks: 19744 bytes, then len ? len : 1, then buflen ? buflen : 1; freed
   in reverse order). Its program contract takes the allocator's free and malloc facts at B as explicit premises, in
   the form of libreac/fuzz_ctrl's released walk top (
   proofs/libreac/fuzz_ctrl/lib/A/ACtl.v:1184-1185, discharged at ACtlAll.v:110-111 by the same AF0q / AF0w theorems
   CtrlClose.v:144-145 gives the driver). Here the program contract stays inside H_DRIVER, as in fuzz_knock's
   KnockClose.v, and the join feeds it the per-FPState allocator facts H_DRIVER receives, which ASAN_T_of_parts takes
   from H_ALLOC_MALLOC / H_ALLOC_FREE. The entry function's other runtime calls (__asan_memset, the snprintf and
   vsnprintf wrappers, the side-stack frames) are proved in the program contract too, as libreac/fuzz_disco's released
   closing takes its snprintf walk (proofs/libreac/fuzz_disco/lib/A/DiscoAsanT.v: beside
   the allocator the only runtime parts are the memcpy entry AICPY and the read check ARDCHK; lib/A/Prog/DiscoLibX.v
   consumes the snprintf walk inside the program contract). So this file has no Section
   hypothesis beyond fuzz_knock's and fuzz_role's.
   No instance of the plain build's sink (Reusable/YI5b src0_sink_head) is used: this file takes no sink-head argument. *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_pw.fuzz_rate Require Statements.
From OSSVerify.reac_pw.fuzz_rate.images Require Asan AsanUbsan.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK15 YK18 YK09 YK0c YK0e YA01 YA0c YA0e YA02.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG01 YG0f YG0d YC5d YI16 YE00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YO05 YO09 YO06 YO01 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RateAsanTop.
Import ListNotations.
Import APC. Import AX2. Import AX2S. Import APG. Import APSG.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.

Local Notation LS := RateAsanTop.rate_shape.

Lemma valid_sp_windowR : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.

(* ===================================================================================================== *)
(* ASan image                                                                                              *)
(* ===================================================================================================== *)
Section asan.
Local Notation segs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.
Local Notation ph := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.phdrs.

(* START-UP. Owner: the start-up tables generated from fuzz_rate.asan's own collector run (lib/A/AB01.v, AB12.v) and
   the certificate (lib/A/AB1n.v). *)
(* HS_TBL: the start-up's hand-off states, donor lib/A/AB01.v:598 HS_tfib (per-binary data; rate's lib/A/AB01.v). *)
(* 727298f3: the hand-off states of the run's own CONFIG_RSEQ flag (AB01r.HS_tfib_r). *)
Variable HS_TBL : Z -> nat -> option acs.
(* TFIB_TBL: the image table of the start-up certificate, donor lib/A/AB12.v:11 TFIB (per-binary data; rate's
   lib/A/AB12.v). *)
Variable TFIB_TBL : atable.
(* donor lib/A/AB1n.v:45-51 HS_ok, at HS_TBL / TFIB_TBL and fuzz_rate's ASan image. *)
Definition HS_okA (h : nat) (sp : word) (rdraw : EntryDraw) (brk0 mbase : word)
    (argv envp : list (list byte)) (fs0 : Fs.Fs) (stdin : InputStream) (uid gid hw : word)
    (groups : list word) (net : NetQueue) (nofile sigmask : word) (urnd : InputStream) (tmp : Fs.Fs)
    (kb : KernelBuild) (execfn : list byte) (sdef : bool) (fsq : Fs.Fs) (c : config) : Prop :=
  exists ch E R FULL model,
    HS_TBL (rseq_z (kb_rseq kb)) h = Some ch
    /\ c = cfg_of segs R (pc ch) FULL model
    /\ cs_ok segs TFIB_TBL YA02.LIMIT (YA02.TOP sp)
         (YA02.SINV0 ph sp rdraw brk0 mbase argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef OSSVerify.reac_pw.fuzz_rate.images.Asan.M.init_pc)
         (YA02.argH0 sp rdraw argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) fsq E ch R FULL model.
(* H_STARTUP: donor lib/A/AB1n.v:52-60 tfib_startup_T1 (the start-up certificate, closed by AB1n.v:61-73 over
   tfib_startup_closed). Owner: lib/A/AB1n.v. *)
Hypothesis H_STARTUP :
  forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)) (fs : Fs.Fs) (stdin : InputStream)
    (uid gid hw : word) (groups : list word) (net : NetQueue) (nofile sigmask : word) (urnd : InputStream) (tmp : Fs.Fs)
    (kb : KernelBuild) (execfn : list byte) (sdef : bool),
  valid_sp sp -> valid_brk segs brk0 -> valid_mmap_base mbase -> valid_argv argv -> valid_envp envp ->
  entry_stack_fits sp argv envp -> valid_id uid -> valid_hwcap hw -> valid_nofile nofile ->
  valid_sigmask (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) ->
  valid_launch (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) ->
  entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) ->
  forall T : TSet, T [] ->
  (forall h c, HS_okA h sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef
     (fs_seed_tmp fs tmp) c -> srealizes segs c T) ->
  srealizes segs (init_config segs OSSVerify.reac_pw.fuzz_rate.images.Asan.M.init_pc ph sp brk0 mbase rdraw YA02.LIMIT
    (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef)) T.

(* THE PARTS THE DRIVER CONSUMES (donor lib/A/AD1q.v:41-63, the Section of tfib_srealizesX). *)
(* B: the image's symbol and trace table, donor lib/A/AD2l.v:14 TfibB. Owner: lib/A/AD2l.v. *)
Variable B : asyms.
(* H_ALLOC_MALLOC: donor lib/A/AD1q.v:43 AMALLOC (closed by lib/A/AF0w.v tfib_amalloc_realizes, through
   lib/A/RateAllocClose.v). *)
Hypothesis H_ALLOC_MALLOC : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @amalloc_realizes fx rc segs B.
(* H_ALLOC_FREE: donor lib/A/AD1q.v:44 AFREE (closed by lib/A/AF0q.v afree_realizes_closed, through
   lib/A/RateAllocClose.v). *)
Hypothesis H_ALLOC_FREE : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_realizes fx rc segs B.
(* H_RT_MEMCPY: donor lib/A/AD1q.v:45 AICPY, the memcpy interceptor (closed by lib/A/AD2m.v tfib_AICPY, through
   lib/A/RateAllocClose.v). *)
Hypothesis H_RT_MEMCPY : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc segs B OCpy (pc_wrap_memcpy (as_code B)).
(* donor lib/A/AD1q.v:64-76 drv_mainX_stmt, at HS_TBL / TFIB_TBL, fuzz_rate's ASan image and LS. *)
Definition drv_mainA (rc : YM05.RunCeil) : Prop :=
  forall (sp : word) (rdraw : EntryDraw) (brk mbase : word) (inp : ProcInput) (h : nat) (ch : acs) (E : env) (R : bvmap 5 word)
    (FULL : word -> option byte) (model : Model) (SINV : env -> (word -> option byte) -> Prop),
  valid_sp sp -> valid_brk segs brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
  @YM05.ceil_of_top rc (bv_unsigned sp - stack_max_size) ->
  HS_TBL (rseq_z (kb_rseq (in_kernel inp))) h = Some ch ->
  (forall E' M, SINV E' M -> uE E' e_sp0 = YA02.TOP sp + 8388608) ->
  cs_ok segs TFIB_TBL YA02.LIMIT (YA02.TOP sp) SINV
    (YA02.argH0 sp rdraw (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp) (in_hwcap inp)
      (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp) (in_kernel inp)
      (in_execfn inp) (in_sigpipe_default inp)) (in_fs inp) E ch R FULL model ->
  (forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 sp rdraw brk (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp) (in_hwcap inp)
      (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp) (in_kernel inp)
      (in_execfn inp) (in_sigpipe_default inp)) n) ->
  (forall a, YA02.argH0 sp rdraw (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp) (in_hwcap inp)
      (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp) (in_kernel inp)
      (in_execfn inp) (in_sigpipe_default inp) E a = true ->
    FULL a = wrap_mem inp mbase ph (Z_to_bv 64 (Z.of_N OSSVerify.reac_pw.fuzz_rate.images.Asan.M.init_pc)) sp rdraw a) ->
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
   With them, TfibSyms' fields ts_universe and ts_universe_drv (donor lib/A/AF0m.v:314-315) hold of B. Owner: the
   relocated frame (ACej, ACejTfib, AD2l.TfibB). *)
Variable Tfib_universe : list (list Z).
Hypothesis Tfib_universe_ok : universe_ok Tfib_universe.
Hypothesis H_TRACES_B : as_universe B = Tfib_universe.
Variable Tfib_drv_traces : list (list Z).
Hypothesis Tfib_universe_drv : forall t, In t Tfib_drv_traces -> In t Tfib_universe.
Local Notation DRV_TRACES := Tfib_drv_traces.
(* H_DRIVER: donor lib/A/AD1p.v:84 tfib_drv_main (the core's driver walk, AD1q.v:77-78 DRV_MAINX), as a function of
   the parts above; fuzz_rate's join applies the float-state form (libreac/fuzz_grant's lib/A/AD1p.v:93 tfib_drv_main at
   P := a zero rounding mode). Its other donor premises stay inside this hypothesis, as in fuzz_knock's KnockClose.v:
   LIBX : the entry function's contract (fuzz_rate: lib/A/RtPgLib.rate_lib_contract_x_all_tfib over rate_lib_x_all, whose
   free / malloc premises the join feeds from the second and first arguments below), HB : TfibSyms B (the join passes
   the whole record, AD2l.TfibB_syms), ARDCHK : aread_check_stmt B (AD1i.v:18), MT_FREE / RO_IN (AD1q.v:48-49;
   in_ro_tfa ACeg.v:42), and the driver's stdio sites xst/XFR/PF1/PFN and est/ESTI/ESTF/FWS/RFS/FPO/FPR/FPU/EXS
   (AD1w.v:119-151, AD1x.v:36-93). lib/A/AD2o.v discharges it. *)
Hypothesis H_DRIVER : forall (rc : YM05.RunCeil),
  (forall fx : YK11.FPState, @amalloc_realizes fx rc segs B) ->
  (forall fx : YK11.FPState, @afree_realizes fx rc segs B) ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc segs B OCpy (pc_wrap_memcpy (as_code B))) ->
  universe_ok (as_universe B) ->
  (forall t, In t DRV_TRACES -> In t (as_universe B)) ->
  drv_mainA rc.

(* donor lib/A/AB1n.v:74-87 HS_ok_open, the same proof (cs_ok's co_sinv field, Reusable/YA0e.v). *)
Lemma HS_ok_openA : forall h sp rdraw brk0 mbase argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef fsq c,
  HS_okA h sp rdraw brk0 mbase argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef fsq c ->
  exists ch E R FULL model,
    HS_TBL (rseq_z (kb_rseq kb)) h = Some ch /\ c = cfg_of segs R (pc ch) FULL model
    /\ cs_ok segs TFIB_TBL YA02.LIMIT (YA02.TOP sp)
         (YA02.SINV0 ph sp rdraw brk0 mbase argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef OSSVerify.reac_pw.fuzz_rate.images.Asan.M.init_pc)
         (YA02.argH0 sp rdraw argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) fsq E ch R FULL model
    /\ (forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 sp rdraw brk0 argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) n)
    /\ (forall a, YA02.argH0 sp rdraw argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef E a = true ->
         FULL a = wrap_mem (YA02.inp argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) mbase ph (Z_to_bv 64 (Z.of_N OSSVerify.reac_pw.fuzz_rate.images.Asan.M.init_pc)) sp rdraw a)
    /\ eb E = eb (YA02.E0 sp rdraw brk0 argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef).
Proof.
  intros h sp rdraw brk0 mbase argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef fsq c
    (ch & E & R & FULL & model & Hh & Hc & HC).
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
Lemma rate_srealizesX_rc : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
  valid_sp sp -> valid_brk segs brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk mb rdraw) inp ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  srealizes segs (init_config segs OSSVerify.reac_pw.fuzz_rate.images.Asan.M.init_pc ph sp brk mb rdraw YA02.LIMIT inp)
    (SPECX (LS:=LS) inp).
Proof.
  intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hlau Hceil.
  (* 727298f3: the input taken apart into its fields; [Run.valid_input] fixes the abort and terminal-SIGPIPE
     declarations, the address size and the channel reader, and says the kernel record is its own
     [recorded_kernel], so the input is [YA02.inp] at that record (as libreac/fuzz_boxreg's A/AD1q.v). *)
  pose proof Hinp as (Hva & Hve & _ & _ & _ & [Huid _] & Hnof & Hsig & Hhw & Hab & Hmmu & _ & Hvl & Hcr & Hspt & Hkern).
  destruct inp as [argv envp fs stdin uid gid groups net nofile sigmask hw ab mmu urnd tmp kern execfn cr spd spt].
  cbn [in_argv in_envp in_uid in_hwcap in_nofile in_abort_terminal in_va_size in_channel_reader in_sigpipe_terminal in_kernel]
    in Hva, Hve, Hfit, Huid, Hhw, Hnof, Hab, Hmmu, Hcr, Hspt, Hkern.
  subst ab mmu cr spt.
  rewrite Hkern in Hinp, Hsig, Hvl, Hlau |- *.
  change (mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw false Sv48 urnd tmp (recorded_kernel kern) execfn true spd false)
    with (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd) in *.
  apply (srz_conseq segs _ (CLOSEDX (LS:=LS) (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd)));
    [| apply t_eq_sym; apply (specx_closedx_eq (LS:=LS))].
  apply (H_STARTUP sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd
    Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hnof Hsig Hvl Hlau
    (CLOSEDX (LS:=LS) (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd)) (CLOSEDX_has_nil (LS:=LS) _)).
  intros h c Hok.
  destruct (HS_ok_openA h sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd
    (fs_seed_tmp fs tmp) c Hok) as (ch & E & R & FULL & model & Hch & -> & HC & HE & HM & _).
  assert (SP0 : forall E' M, YA02.SINV0 ph sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp
    kern execfn spd OSSVerify.reac_pw.fuzz_rate.images.Asan.M.init_pc E' M -> uE E' e_sp0 = YA02.TOP sp + 8388608).
  { intros E' M HSv. eapply YA02.SINV0_sp0; try eassumption. Unshelve. all: first [assumption | exact segs]. }
  exact (DRV_MAINA sp rdraw brk mb (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd) h ch E R FULL model _
    Hsp Hbrk Hfit Hinp Hlau Hceil Hch SP0 HC HE HM).
Qed.
End RC.

(* donor lib/A/AD2o.v:75-84 tfib_srealizesX_top and TFIB_T_of_partsXF; this kit's YM05.RunCeilOf takes the lim argument. *)
Theorem ASAN_T_of_parts : RateAsanTop.ASAN_T.
Proof.
  intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp Hlau.
  change target_alloc_limit with YA02.LIMIT.
  exact (@rate_srealizesX_rc (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowR sp Hsp) YA02.LIMIT) sp rnd brk mbase inp
    Hsp Hbrk Hmb Hfit Hinp Hlau (YM05.ceil_of_top_run _)).
Qed.

(* The two ASan statements, given only the named parts above (the agreement also the plain slot, PLAIN_SLOT_AG). *)
Theorem rate_asan_agrees_of_parts : PLAIN_SLOT_AG -> Statements.asan_agrees.
Proof. intros PS. exact (RateAsanTop.asan_agrees_of_asan_side PS ASAN_T_of_parts). Qed.
Theorem rate_asan_halts_of_parts : Statements.asan_halts.
Proof. exact (RateAsanTop.asan_halts_of_asan_side ASAN_T_of_parts). Qed.
(* Inside the Section, Print Assumptions lists the named parts these two statements rest on. *)
Print Assumptions rate_asan_agrees_of_parts.
Print Assumptions rate_asan_halts_of_parts.
End asan.

(* ===================================================================================================== *)
(* ASan+UBSan image (donor lib/YD2o.v, YD2p.v, YD1q.v)                                                      *)
(* ===================================================================================================== *)
Section asan_ubsan.
Local Notation segs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.
Local Notation ph := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.phdrs.

(* START-UP (asan-ubsan). HS_TBL_U: donor lib/YB01.v:597 HS_tfib; TFIB_TBL_U: donor lib/YB12.v:10 TFIB (rate's
   lib/AU/YB12.v). Owner: image B. *)
(* 727298f3: the hand-off states of the run's own CONFIG_RSEQ flag (AB01r.HS_tfib_r). *)
Variable HS_TBL_U : Z -> nat -> option acs.
Variable TFIB_TBL_U : atable.
(* donor lib/YB1n.v:44-50 HS_ok. *)
Definition HS_okU (h : nat) (sp : word) (rdraw : EntryDraw) (brk0 mbase : word)
    (argv envp : list (list byte)) (fs0 : Fs.Fs) (stdin : InputStream) (uid gid hw : word)
    (groups : list word) (net : NetQueue) (nofile sigmask : word) (urnd : InputStream) (tmp : Fs.Fs)
    (kb : KernelBuild) (execfn : list byte) (sdef : bool) (fsq : Fs.Fs) (c : config) : Prop :=
  exists ch E R FULL model,
    HS_TBL_U (rseq_z (kb_rseq kb)) h = Some ch
    /\ c = cfg_of segs R (pc ch) FULL model
    /\ cs_ok segs TFIB_TBL_U YA02.LIMIT (YA02.TOP sp)
         (YA02.SINV0 ph sp rdraw brk0 mbase argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.init_pc)
         (YA02.argH0 sp rdraw argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) fsq E ch R FULL model.
(* H_STARTUP_U: donor lib/YB1n.v:51-59 tfib_startup_T1. Owner: image B. *)
Hypothesis H_STARTUP_U :
  forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)) (fs : Fs.Fs) (stdin : InputStream)
    (uid gid hw : word) (groups : list word) (net : NetQueue) (nofile sigmask : word) (urnd : InputStream) (tmp : Fs.Fs)
    (kb : KernelBuild) (execfn : list byte) (sdef : bool),
  valid_sp sp -> valid_brk segs brk0 -> valid_mmap_base mbase -> valid_argv argv -> valid_envp envp ->
  entry_stack_fits sp argv envp -> valid_id uid -> valid_hwcap hw -> valid_nofile nofile ->
  valid_sigmask (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) ->
  valid_launch (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) ->
  entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) ->
  forall T : TSet, T [] ->
  (forall h c, HS_okU h sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef
     (fs_seed_tmp fs tmp) c -> srealizes segs c T) ->
  srealizes segs (init_config segs OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.init_pc ph sp brk0 mbase rdraw YA02.LIMIT
    (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef)) T.

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
  forall (sp : word) (rdraw : EntryDraw) (brk mbase : word) (inp : ProcInput) (h : nat) (ch : acs) (E : env) (R : bvmap 5 word)
    (FULL : word -> option byte) (model : Model) (SINV : env -> (word -> option byte) -> Prop),
  valid_sp sp -> valid_brk segs brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
  @YM05.ceil_of_top rc (bv_unsigned sp - stack_max_size) ->
  HS_TBL_U (rseq_z (kb_rseq (in_kernel inp))) h = Some ch ->
  (forall E' M, SINV E' M -> uE E' e_sp0 = YA02.TOP sp + 8388608) ->
  cs_ok segs TFIB_TBL_U YA02.LIMIT (YA02.TOP sp) SINV
    (YA02.argH0 sp rdraw (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp) (in_hwcap inp)
      (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp) (in_kernel inp)
      (in_execfn inp) (in_sigpipe_default inp)) (in_fs inp) E ch R FULL model ->
  (forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 sp rdraw brk (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp) (in_hwcap inp)
      (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp) (in_kernel inp)
      (in_execfn inp) (in_sigpipe_default inp)) n) ->
  (forall a, YA02.argH0 sp rdraw (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp) (in_hwcap inp)
      (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp) (in_kernel inp)
      (in_execfn inp) (in_sigpipe_default inp) E a = true ->
    FULL a = wrap_mem inp mbase ph (Z_to_bv 64 (Z.of_N OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.init_pc)) sp rdraw a) ->
  srealizes segs (cfg_of segs R (pc ch) FULL model) (CLOSEDX (LS:=LS) inp).
(* THE ASAN-UBSAN TRACE TABLES. fuzz_knock's KnockClose.v names them from lib/AU/YCej.v and lib/AU/YCejTfib.v; this
   Section takes them as Variables and Hypotheses of exactly the types of knock's names, in this order (image B's
   lib/AU/YD2o.v passes its own):
     Tfib_universe_U      : list (list Z)                                     knock AU/YCej.v:31 Tfib_universe
     Tfib_universe_ok_U   : universe_ok Tfib_universe_U                       knock AU/YCej.v:75 Tfib_universe_ok
     H_TRACES_B_U         : as_universe B_U = Tfib_universe_U                 knock KnockClose.v:250 (eq_refl at YD2l)
     Tfib_drv_traces_U    : list (list Z)                                     knock AU/YCejTfib.v:26 Tfib_drv_traces
     Tfib_universe_drv_U  : forall t, In t Tfib_drv_traces_U -> In t Tfib_universe_U
                                                                              knock AU/YCejTfib.v:29 Tfib_universe_drv *)
Variable Tfib_universe_U : list (list Z).
Hypothesis Tfib_universe_ok_U : universe_ok Tfib_universe_U.
(* H_TRACES_B_U: donor lib/YD2l.v as_universe := Tfib_universe. Owner: image B (YD2l); closes by reflexivity. *)
Hypothesis H_TRACES_B_U : as_universe B_U = Tfib_universe_U.
(* As on the ASan side, the driver's traces are proved, not assumed, by image B's lib/AU/YCejTfib.v. *)
Variable Tfib_drv_traces_U : list (list Z).
Hypothesis Tfib_universe_drv_U : forall t, In t Tfib_drv_traces_U -> In t Tfib_universe_U.
Local Notation DRV_TRACES_U := Tfib_drv_traces_U.
(* H_DRIVER_U: donor lib/YD1p.v:77 tfib_drv_main (YD1q's DRV_MAINX); image B's join applies its core's float-state form
   (fuzz_grant's lib/B/YD1p.v at P := a zero rounding mode; boxreg's lib/B/AD1p.v P_FRM form has the same conclusion).
   Its LIBX is lib/YCfn.v's (image B's program contract, whose free / malloc premises image B's join feeds from the
   second and first arguments below), with the same absorbed core parts as H_DRIVER. Owner: image B (join lib/AU/YD2o.v). *)
Hypothesis H_DRIVER_U : forall (rc : YM05.RunCeil),
  (forall fx : YK11.FPState, @amalloc_realizes fx rc segs B_U) ->
  (forall fx : YK11.FPState, @afree_realizes fx rc segs B_U) ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc segs B_U OCpy (pc_wrap_memcpy (as_code B_U))) ->
  universe_ok (as_universe B_U) ->
  (forall t, In t DRV_TRACES_U -> In t (as_universe B_U)) ->
  drv_mainU rc.

Lemma HS_ok_openU : forall h sp rdraw brk0 mbase argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef fsq c,
  HS_okU h sp rdraw brk0 mbase argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef fsq c ->
  exists ch E R FULL model,
    HS_TBL_U (rseq_z (kb_rseq kb)) h = Some ch /\ c = cfg_of segs R (pc ch) FULL model
    /\ cs_ok segs TFIB_TBL_U YA02.LIMIT (YA02.TOP sp)
         (YA02.SINV0 ph sp rdraw brk0 mbase argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.init_pc)
         (YA02.argH0 sp rdraw argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) fsq E ch R FULL model
    /\ (forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 sp rdraw brk0 argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) n)
    /\ (forall a, YA02.argH0 sp rdraw argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef E a = true ->
         FULL a = wrap_mem (YA02.inp argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) mbase ph (Z_to_bv 64 (Z.of_N OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.init_pc)) sp rdraw a)
    /\ eb E = eb (YA02.E0 sp rdraw brk0 argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef).
Proof.
  intros h sp rdraw brk0 mbase argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef fsq c
    (ch & E & R & FULL & model & Hh & Hc & HC).
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
Lemma rate_srealizesXU_rc : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
  valid_sp sp -> valid_brk segs brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk mb rdraw) inp ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  srealizes segs (init_config segs OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.init_pc ph sp brk mb rdraw YA02.LIMIT inp)
    (SPECX (LS:=LS) inp).
Proof.
  intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hlau Hceil.
  (* 727298f3: the input taken apart into its fields; [Run.valid_input] fixes the abort and terminal-SIGPIPE
     declarations, the address size and the channel reader, and says the kernel record is its own
     [recorded_kernel], so the input is [YA02.inp] at that record (as libreac/fuzz_boxreg's A/AD1q.v). *)
  pose proof Hinp as (Hva & Hve & _ & _ & _ & [Huid _] & Hnof & Hsig & Hhw & Hab & Hmmu & _ & Hvl & Hcr & Hspt & Hkern).
  destruct inp as [argv envp fs stdin uid gid groups net nofile sigmask hw ab mmu urnd tmp kern execfn cr spd spt].
  cbn [in_argv in_envp in_uid in_hwcap in_nofile in_abort_terminal in_va_size in_channel_reader in_sigpipe_terminal in_kernel]
    in Hva, Hve, Hfit, Huid, Hhw, Hnof, Hab, Hmmu, Hcr, Hspt, Hkern.
  subst ab mmu cr spt.
  rewrite Hkern in Hinp, Hsig, Hvl, Hlau |- *.
  change (mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw false Sv48 urnd tmp (recorded_kernel kern) execfn true spd false)
    with (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd) in *.
  apply (srz_conseq segs _ (CLOSEDX (LS:=LS) (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd)));
    [| apply t_eq_sym; apply (specx_closedx_eq (LS:=LS))].
  apply (H_STARTUP_U sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd
    Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hnof Hsig Hvl Hlau
    (CLOSEDX (LS:=LS) (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd)) (CLOSEDX_has_nil (LS:=LS) _)).
  intros h c Hok.
  destruct (HS_ok_openU h sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd
    (fs_seed_tmp fs tmp) c Hok) as (ch & E & R & FULL & model & Hch & -> & HC & HE & HM & _).
  assert (SP0 : forall E' M, YA02.SINV0 ph sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp
    kern execfn spd OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.init_pc E' M -> uE E' e_sp0 = YA02.TOP sp + 8388608).
  { intros E' M HSv. eapply YA02.SINV0_sp0; try eassumption. Unshelve. all: first [assumption | exact segs]. }
  exact (DRV_MAINU sp rdraw brk mb (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd) h ch E R FULL model _
    Hsp Hbrk Hfit Hinp Hlau Hceil Hch SP0 HC HE HM).
Qed.
End RCU.

Theorem ASAN_UBSAN_T_of_parts : RateAsanTop.ASAN_UBSAN_T.
Proof.
  intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp Hlau.
  change target_alloc_limit with YA02.LIMIT.
  exact (@rate_srealizesXU_rc (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowR sp Hsp) YA02.LIMIT) sp rnd brk mbase inp
    Hsp Hbrk Hmb Hfit Hinp Hlau (YM05.ceil_of_top_run _)).
Qed.

Theorem rate_asan_ubsan_agrees_of_parts : PLAIN_SLOT_AG -> Statements.asan_ubsan_agrees.
Proof. intros PS. exact (RateAsanTop.asan_ubsan_agrees_of_asan_side PS ASAN_UBSAN_T_of_parts). Qed.
Theorem rate_asan_ubsan_halts_of_parts : Statements.asan_ubsan_halts.
Proof. exact (RateAsanTop.asan_ubsan_halts_of_asan_side ASAN_UBSAN_T_of_parts). Qed.
Print Assumptions rate_asan_ubsan_agrees_of_parts.
Print Assumptions rate_asan_ubsan_halts_of_parts.
End asan_ubsan.

(* Outside the Sections the named parts are arguments of each theorem; Print Assumptions then lists only global axioms. *)
Print Assumptions rate_asan_agrees_of_parts.
Print Assumptions rate_asan_halts_of_parts.
Print Assumptions rate_asan_ubsan_agrees_of_parts.
Print Assumptions rate_asan_ubsan_halts_of_parts.
