(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AD2o.v, AD2p.v and AD1q.v (asan) and
   lib/YD2o.v, YD2p.v and YD1q.v (asan-ubsan), ossv/recipes c8557374ad2e, for libreac/fuzz_knock: the closing of
   KnockAsanTop.ASAN_T and ASAN_UBSAN_T from named parts; module paths changed, shape AgreeKnock.ag_sil_shape
   (KnockAsanTop.knock_shape), fuzz_knock's images. Modelled on
   fuzz_pcap's lib/A/PcapClose.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_knock/lib/A/KnockClose.v, with its module paths and module names changed; 11 of its 228 lines of code are new or changed and 23 lines of the source are left out. *)
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

Variable HS_TBL : nat -> option acs.

Variable TFIB_TBL : atable.

Definition HS_okA (h : nat) (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (uid hw : word)
    (fs : Fs.Fs) (c : config) : Prop :=
  exists ch E R FULL model,
    HS_TBL h = Some ch
    /\ c = cfg_of segs R (pc ch) FULL model
    /\ cs_ok segs TFIB_TBL YA02.LIMIT (YA02.TOP sp)
         (YA02.SINV0 ph sp rdraw brk0 argv envp uid hw) (YA02.argH0 ph sp rdraw argv envp uid hw) fs E ch R FULL model.

Hypothesis H_STARTUP :
  forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)) (fs : Fs.Fs) (stdin : InputStream)
    (uid gid hw : word) (groups : list word) (net : NetQueue) (nofile sigmask : word) (urnd : InputStream) (tmp : Fs.Fs),
  valid_sp sp -> valid_brk segs brk0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  valid_id uid -> valid_hwcap hw ->
  forall T : TSet, T [] ->
  (forall h c, HS_okA h sp rdraw brk0 argv envp uid hw (fs_seed_tmp fs tmp) c -> srealizes segs c T) ->
  srealizes segs (init_config segs OSSVerify.libdiginet.fuzz_codec.images.Asan.M.init_pc ph sp brk0 mbase rdraw YA02.LIMIT
    (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp)) T.

Variable B : asyms.

Hypothesis H_ALLOC_MALLOC : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @amalloc_realizes fx rc segs B.

Hypothesis H_ALLOC_FREE : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_realizes fx rc segs B.

Hypothesis H_RT_MEMCPY : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc segs B OCpy (pc_wrap_memcpy (as_code B)).

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

Hypothesis H_TRACES_B : as_universe B = ACej.Tfib_universe.

Local Notation DRV_TRACES := ACejTfib.Tfib_drv_traces.

Hypothesis H_DRIVER : forall (rc : YM05.RunCeil),
  (forall fx : YK11.FPState, @amalloc_realizes fx rc segs B) ->
  (forall fx : YK11.FPState, @afree_realizes fx rc segs B) ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc segs B OCpy (pc_wrap_memcpy (as_code B))) ->
  universe_ok (as_universe B) ->
  (forall t, In t DRV_TRACES -> In t (as_universe B)) ->
  drv_mainA rc.

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

Lemma DRV_MAINA : drv_mainA rc.
Proof.
  apply (H_DRIVER rc (H_ALLOC_MALLOC rc) (H_ALLOC_FREE rc) (H_RT_MEMCPY rc)).
  - rewrite H_TRACES_B. exact ACej.Tfib_universe_ok.
  - intros t Ht. rewrite H_TRACES_B. exact (ACejTfib.Tfib_universe_drv t Ht).
Qed.

Lemma codec_srealizesX_rc : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
  valid_sp sp -> valid_brk segs brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  srealizes segs (init_config segs OSSVerify.libdiginet.fuzz_codec.images.Asan.M.init_pc ph sp brk mb rdraw YA02.LIMIT inp)
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

Theorem ASAN_T_of_parts : CodecAsanTop.ASAN_T.
Proof.
  intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp.
  change target_alloc_limit with YA02.LIMIT.
  exact (@codec_srealizesX_rc (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowC sp Hsp) YA02.LIMIT) sp rnd brk mbase inp
    Hsp Hbrk Hmb Hfit Hinp (YM05.ceil_of_top_run _)).
Qed.

Theorem codec_asan_agrees_of_parts : Statements.asan_agrees.
Proof. exact (CodecAsanTop.asan_agrees_of_asan_side ASAN_T_of_parts). Qed.
Theorem codec_asan_halts_of_parts : Statements.asan_halts.
Proof. exact (CodecAsanTop.asan_halts_of_asan_side ASAN_T_of_parts). Qed.

End asan.

Section asan_ubsan.
Local Notation segs := OSSVerify.libdiginet.fuzz_codec.images.AsanUbsan.M.loaded_segments.
Local Notation ph := OSSVerify.libdiginet.fuzz_codec.images.AsanUbsan.M.phdrs.

Variable HS_TBL_U : nat -> option acs.
Variable TFIB_TBL_U : atable.

Definition HS_okU (h : nat) (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (uid hw : word)
    (fs : Fs.Fs) (c : config) : Prop :=
  exists ch E R FULL model,
    HS_TBL_U h = Some ch
    /\ c = cfg_of segs R (pc ch) FULL model
    /\ cs_ok segs TFIB_TBL_U YA02.LIMIT (YA02.TOP sp)
         (YA02.SINV0 ph sp rdraw brk0 argv envp uid hw) (YA02.argH0 ph sp rdraw argv envp uid hw) fs E ch R FULL model.

Hypothesis H_STARTUP_U :
  forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)) (fs : Fs.Fs) (stdin : InputStream)
    (uid gid hw : word) (groups : list word) (net : NetQueue) (nofile sigmask : word) (urnd : InputStream) (tmp : Fs.Fs),
  valid_sp sp -> valid_brk segs brk0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  valid_id uid -> valid_hwcap hw ->
  forall T : TSet, T [] ->
  (forall h c, HS_okU h sp rdraw brk0 argv envp uid hw (fs_seed_tmp fs tmp) c -> srealizes segs c T) ->
  srealizes segs (init_config segs OSSVerify.libdiginet.fuzz_codec.images.AsanUbsan.M.init_pc ph sp brk0 mbase rdraw YA02.LIMIT
    (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp)) T.

Variable B_U : asyms.

Hypothesis H_ALLOC_MALLOC_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @amalloc_realizes fx rc segs B_U.
Hypothesis H_ALLOC_FREE_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_realizes fx rc segs B_U.

Hypothesis H_RT_MEMCPY_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc segs B_U OCpy (pc_wrap_memcpy (as_code B_U)).

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

Hypothesis H_TRACES_B_U : as_universe B_U = YCej.Tfib_universe.

Local Notation DRV_TRACES_U := YCejTfib.Tfib_drv_traces.

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

Lemma codec_srealizesXU_rc : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
  valid_sp sp -> valid_brk segs brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  srealizes segs (init_config segs OSSVerify.libdiginet.fuzz_codec.images.AsanUbsan.M.init_pc ph sp brk mb rdraw YA02.LIMIT inp)
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

Theorem ASAN_UBSAN_T_of_parts : CodecAsanTop.ASAN_UBSAN_T.
Proof.
  intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp.
  change target_alloc_limit with YA02.LIMIT.
  exact (@codec_srealizesXU_rc (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowC sp Hsp) YA02.LIMIT) sp rnd brk mbase inp
    Hsp Hbrk Hmb Hfit Hinp (YM05.ceil_of_top_run _)).
Qed.

Theorem codec_asan_ubsan_agrees_of_parts : Statements.asan_ubsan_agrees.
Proof. exact (CodecAsanTop.asan_ubsan_agrees_of_asan_side ASAN_UBSAN_T_of_parts). Qed.
Theorem codec_asan_ubsan_halts_of_parts : Statements.asan_ubsan_halts.
Proof. exact (CodecAsanTop.asan_ubsan_halts_of_asan_side ASAN_UBSAN_T_of_parts). Qed.
End asan_ubsan.

