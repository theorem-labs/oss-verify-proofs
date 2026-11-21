(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AD2o.v, AD2p.v and AD1q.v (asan) and
   lib/YD2o.v, YD2p.v and YD1q.v (asan-ubsan), for libreac/fuzz_knock: the closing of
   KnockAsanTop.ASAN_T and ASAN_UBSAN_T from named parts; module paths changed, shape AgreeKnock.ag_sil_shape
   (KnockAsanTop.knock_shape), fuzz_knock's images. Modelled on
   fuzz_pcap's lib/A/PcapClose.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_knock/lib/A/KnockClose.v, with its module paths and module names changed; 11 of its 228 lines of code are new or changed and 23 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's ProcInput and its premises; the CONFIG_RSEQ auxv layout; the channel-reader premise of fdchan; the mmap-base premise); internal commit ids in comments replaced by public commits or removed. *)
(* The closing of CodecAsanTop.ASAN_T (Section asan) and ASAN_UBSAN_T (Section asan_ubsan) from named parts, in the form of
   projects/libreac/fuzz_knock/proofs/lib/A/KnockClose.v: the start-up (HS_TBL, TFIB_TBL, H_STARTUP), the start-up record B and
   its allocator parts, and the driver main H_DRIVER, which carries the program contract. lib/A/AD2o.v and lib/AU/YD2o.v
   instantiate the two Sections. *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libdiginet.fuzz_codec Require Statements.
From OSSVerify.libdiginet.fuzz_codec.images Require Asan AsanUbsan.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require AgreeCodec.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK15 YK18 YK09 YK0c YK0e YA01 YA0c YA0e YA02.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG01 YG0f YG0d YC5d YI16 YE00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO05 YO09 YO06 YO01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require ACej ACejTfib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require YCej YCejTfib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import CodecAsanTop.
Import ListNotations.
Import APC. Import AX2. Import AX2S. Import APG. Import APSG.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.

Local Notation LS := CodecAsanTop.codec_shape.

Lemma valid_sp_windowC : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.

Section asan.
Local Notation segs := OSSVerify.libdiginet.fuzz_codec.images.Asan.M.loaded_segments.
Local Notation ph := OSSVerify.libdiginet.fuzz_codec.images.Asan.M.phdrs.

(* START-UP. Owner: A2 (start-up tables generated from fuzz_codec.asan's own collector run) and A3 (the certificate). *)
(* HS_TBL: the start-up's hand-off states, donor lib/A/AB01.v:597 HS_tfib (per-binary data; this unit's lib/A/AB01.v). *)
(* 727298f3: the hand-off states of the run's own CONFIG_RSEQ flag (AB01r.HS_tfib_r). *)
Variable HS_TBL : Z -> nat -> option acs.
(* TFIB_TBL: the image table of the start-up certificate, donor lib/A/AB12.v:11 TFIB (per-binary data; this unit's
   lib/A/AB12.v). *)
Variable TFIB_TBL : atable.
(* donor lib/A/AB1n.v:45-51 HS_ok, at HS_TBL / TFIB_TBL and fuzz_codec's ASan image. *)
Definition HS_okA (h : nat) (sp : word) (rdraw : EntryDraw) (brk0 mbase : word)
    (argv envp : list (list byte)) (fs0 : Fs.Fs) (stdin : InputStream) (uid gid hw : word)
    (groups : list word) (net : NetQueue) (nofile sigmask : word) (urnd : InputStream) (tmp : Fs.Fs)
    (kb : KernelBuild) (execfn : list byte) (sdef : bool) (fsq : Fs.Fs) (c : config) : Prop :=
  exists ch E R FULL model,
    HS_TBL (rseq_z (kb_rseq kb)) h = Some ch
    /\ c = cfg_of segs R (pc ch) FULL model
    /\ cs_ok segs TFIB_TBL YA02.LIMIT (YA02.TOP sp)
         (YA02.SINV0 ph sp rdraw brk0 mbase argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef OSSVerify.libdiginet.fuzz_codec.images.Asan.M.init_pc)
         (YA02.argH0 sp rdraw argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) fsq E ch R FULL model.
(* H_STARTUP: donor lib/A/AB1n.v:52-60 tfib_startup_T1 (the start-up certificate, closed by AB1n.v:61-73 over
   tfib_startup_closed). Owner: A3 (lib/A/AB1n.v). *)
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
  srealizes segs (init_config segs OSSVerify.libdiginet.fuzz_codec.images.Asan.M.init_pc ph sp brk0 mbase rdraw YA02.LIMIT
    (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef)) T.

Variable B : asyms.

Hypothesis H_ALLOC_MALLOC : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @amalloc_realizes fx rc segs B.

Hypothesis H_ALLOC_FREE : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_realizes fx rc segs B.

Hypothesis H_RT_MEMCPY : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc segs B OCpy (pc_wrap_memcpy (as_code B)).

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
    FULL a = wrap_mem inp mbase ph (Z_to_bv 64 (Z.of_N OSSVerify.libdiginet.fuzz_codec.images.Asan.M.init_pc)) sp rdraw a) ->
  srealizes segs (cfg_of segs R (pc ch) FULL model) (CLOSEDX (LS:=LS) inp).

Hypothesis H_TRACES_B : as_universe B = ACej.Tfib_universe.

Local Notation DRV_TRACES := ACejTfib.Tfib_drv_traces.

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
         (YA02.SINV0 ph sp rdraw brk0 mbase argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef OSSVerify.libdiginet.fuzz_codec.images.Asan.M.init_pc)
         (YA02.argH0 sp rdraw argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) fsq E ch R FULL model
    /\ (forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 sp rdraw brk0 argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) n)
    /\ (forall a, YA02.argH0 sp rdraw argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef E a = true ->
         FULL a = wrap_mem (YA02.inp argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) mbase ph (Z_to_bv 64 (Z.of_N OSSVerify.libdiginet.fuzz_codec.images.Asan.M.init_pc)) sp rdraw a)
    /\ eb E = eb (YA02.E0 sp rdraw brk0 argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef).
Proof.
  intros h sp rdraw brk0 mbase argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef fsq c
    (ch & E & R & FULL & model & Hh & Hc & HC).
  exists ch, E, R, FULL, model. split; [exact Hh|]. split; [exact Hc|]. split; [exact HC|].
  exact (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC).
Qed.

Section RC. Context {rc : YM05.RunCeil}.

Lemma DRV_MAINA : drv_mainA rc.
Proof.
  apply (H_DRIVER rc (H_ALLOC_MALLOC rc) (H_ALLOC_FREE rc) (H_RT_MEMCPY rc)).
  - rewrite H_TRACES_B. exact ACej.Tfib_universe_ok.
  - intros t Ht. rewrite H_TRACES_B. exact (ACejTfib.Tfib_universe_drv t Ht).
Qed.

Lemma codec_srealizesX_rc : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
  valid_sp sp -> valid_brk segs brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk mb rdraw) inp ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  srealizes segs (init_config segs OSSVerify.libdiginet.fuzz_codec.images.Asan.M.init_pc ph sp brk mb rdraw YA02.LIMIT inp)
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
    kern execfn spd OSSVerify.libdiginet.fuzz_codec.images.Asan.M.init_pc E' M -> uE E' e_sp0 = YA02.TOP sp + 8388608).
  { intros E' M HSv. eapply YA02.SINV0_sp0; try eassumption. Unshelve. all: first [assumption | exact segs]. }
  exact (DRV_MAINA sp rdraw brk mb (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd) h ch E R FULL model _
    Hsp Hbrk Hfit Hinp Hlau Hceil Hch SP0 HC HE HM).
Qed.
End RC.

Theorem ASAN_T_of_parts : CodecAsanTop.ASAN_T.
Proof.
  intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp Hlau.
  change target_alloc_limit with YA02.LIMIT.
  exact (@codec_srealizesX_rc (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowC sp Hsp) YA02.LIMIT) sp rnd brk mbase inp
    Hsp Hbrk Hmb Hfit Hinp Hlau (YM05.ceil_of_top_run _)).
Qed.

Theorem codec_asan_agrees_of_parts : Statements.asan_agrees.
Proof. exact (CodecAsanTop.asan_agrees_of_asan_side ASAN_T_of_parts). Qed.
Theorem codec_asan_halts_of_parts : Statements.asan_halts.
Proof. exact (CodecAsanTop.asan_halts_of_asan_side ASAN_T_of_parts). Qed.

End asan.

Section asan_ubsan.
Local Notation segs := OSSVerify.libdiginet.fuzz_codec.images.AsanUbsan.M.loaded_segments.
Local Notation ph := OSSVerify.libdiginet.fuzz_codec.images.AsanUbsan.M.phdrs.

(* START-UP (asan-ubsan). HS_TBL_U: donor lib/YB01.v:597 HS_tfib; TFIB_TBL_U: donor lib/YB12.v:10 TFIB (this unit's
   lib/AU/YB12.v). *)
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
         (YA02.SINV0 ph sp rdraw brk0 mbase argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef OSSVerify.libdiginet.fuzz_codec.images.AsanUbsan.M.init_pc)
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
  srealizes segs (init_config segs OSSVerify.libdiginet.fuzz_codec.images.AsanUbsan.M.init_pc ph sp brk0 mbase rdraw YA02.LIMIT
    (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef)) T.

Variable B_U : asyms.

Hypothesis H_ALLOC_MALLOC_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @amalloc_realizes fx rc segs B_U.
Hypothesis H_ALLOC_FREE_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_realizes fx rc segs B_U.

Hypothesis H_RT_MEMCPY_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc segs B_U OCpy (pc_wrap_memcpy (as_code B_U)).

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
    FULL a = wrap_mem inp mbase ph (Z_to_bv 64 (Z.of_N OSSVerify.libdiginet.fuzz_codec.images.AsanUbsan.M.init_pc)) sp rdraw a) ->
  srealizes segs (cfg_of segs R (pc ch) FULL model) (CLOSEDX (LS:=LS) inp).

Hypothesis H_TRACES_B_U : as_universe B_U = YCej.Tfib_universe.

Local Notation DRV_TRACES_U := YCejTfib.Tfib_drv_traces.

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
         (YA02.SINV0 ph sp rdraw brk0 mbase argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef OSSVerify.libdiginet.fuzz_codec.images.AsanUbsan.M.init_pc)
         (YA02.argH0 sp rdraw argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) fsq E ch R FULL model
    /\ (forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 sp rdraw brk0 argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) n)
    /\ (forall a, YA02.argH0 sp rdraw argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef E a = true ->
         FULL a = wrap_mem (YA02.inp argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) mbase ph (Z_to_bv 64 (Z.of_N OSSVerify.libdiginet.fuzz_codec.images.AsanUbsan.M.init_pc)) sp rdraw a)
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
  - rewrite H_TRACES_B_U. exact YCej.Tfib_universe_ok.
  - intros t Ht. rewrite H_TRACES_B_U. exact (YCejTfib.Tfib_universe_drv t Ht).
Qed.

Lemma codec_srealizesXU_rc : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
  valid_sp sp -> valid_brk segs brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk mb rdraw) inp ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  srealizes segs (init_config segs OSSVerify.libdiginet.fuzz_codec.images.AsanUbsan.M.init_pc ph sp brk mb rdraw YA02.LIMIT inp)
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
    kern execfn spd OSSVerify.libdiginet.fuzz_codec.images.AsanUbsan.M.init_pc E' M -> uE E' e_sp0 = YA02.TOP sp + 8388608).
  { intros E' M HSv. eapply YA02.SINV0_sp0; try eassumption. Unshelve. all: first [assumption | exact segs]. }
  exact (DRV_MAINU sp rdraw brk mb (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd) h ch E R FULL model _
    Hsp Hbrk Hfit Hinp Hlau Hceil Hch SP0 HC HE HM).
Qed.
End RCU.

Theorem ASAN_UBSAN_T_of_parts : CodecAsanTop.ASAN_UBSAN_T.
Proof.
  intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp Hlau.
  change target_alloc_limit with YA02.LIMIT.
  exact (@codec_srealizesXU_rc (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowC sp Hsp) YA02.LIMIT) sp rnd brk mbase inp
    Hsp Hbrk Hmb Hfit Hinp Hlau (YM05.ceil_of_top_run _)).
Qed.

Theorem codec_asan_ubsan_agrees_of_parts : Statements.asan_ubsan_agrees.
Proof. exact (CodecAsanTop.asan_ubsan_agrees_of_asan_side ASAN_UBSAN_T_of_parts). Qed.
Theorem codec_asan_ubsan_halts_of_parts : Statements.asan_ubsan_halts.
Proof. exact (CodecAsanTop.asan_ubsan_halts_of_asan_side ASAN_UBSAN_T_of_parts). Qed.
End asan_ubsan.

