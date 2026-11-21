(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/YD1q.v (with the statements of
   YB1n.v:44-59 HS_ok / tfib_startup_T1, YB1n.v:73-81 HS_ok_open and YD1p.v:77-88 tfib_drv_main) for
   fuzz_scene's asan-ubsan image, module paths changed. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (changed g_HS_ok, g_startup_stmt, g_hs_open, g_drv_mainX_stmt, g_srealizes); internal commit ids in comments replaced by public commits or removed. *)
(* fuzz_scene's driver glue for the asan-ubsan image, in the form of cgif_file_fuzzer lib/YD1q.v (the asan-ubsan twin
   of A/AD1q.v); lib/A/G_Drv.v is the asan twin of this file. Nothing here walks a
   program function: the start-up, the hand-off and the driver walk are Section hypotheses, and so is every leaf
   the driver walk consumes.
   - Image constants: the segments and program headers are scene's Images (AsanUbsan.M.loaded_segments,
     AsanUbsan.M.phdrs, the donor's YB1h.v:16-17 TSEGS / TPH). The start-up table TF (YB12.v TFIB), the hand-off
     states HS (YB01.v:597 HS_tfib), the three driver format-string addresses
     (YD1q.v:56-58) and the entry constants of the program's contract A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK
     A_EMPTY (YCfn.v:18-23) are Section Variables. The asyms record B (YD2l.v:11 TfibB) is a Section Variable.
   - The program's contract: the donor's YCfn.v:57-67 tfib_lib_contract_x states cgif's sink record tfib_K
     (YE2k.v:9-52) and cgif's A_EMPTY in its pre, which no scene state meets (a Theorem Labs lane's ENTRY-REVIEW.md items 7a, 9).
     It is the Section Variable scene_tfib_lib_contract_x (rc, fx, the six entry constants, then B MT XM_LIB XN_LIB RLO
     RHI), whose instance is a Theorem Labs lane's scene contract; the driver walk takes it at fx0 (YD1p.v:48 LIBC) and the
     hand-over takes it at every fx (YD1q.v:46 LIBX, YCfn.v:69-70's _all form).
   - B's tables: the donor's YF0m.v:292 TfibSyms is measured unsatisfiable when relocated by rename (a Theorem Labs lane, 22:25Z);
     it is the Section Variable TS, whose instance is scene's TfibSyms from the collector (a Theorem Labs lane's YF0m).
   - The driver's site types (the stdout / stderr / exit sites, the read check, the read-only test) are Section
     Variables too. Their instances are the restaged core's Definitions at scene's addresses (see the Variables
     below); G_Top.v and G_Close.v bind them.
   - Trace set: the driver walk concludes CLOSEDX (Reusable/YO01.v:38) at scene_shape := AgreeScene.ag_sil_shape
     (lib/SceneAsanBase.v). CLOSEDX is stated for any lib_shape (YO01.v:14), and specx_closedx_eq (YO01.v:158) holds for
     any lib_shape, so, as YD1q.v:86-87 does, srz_conseq gives SPECX (Reusable/YO06.v:40) at scene_shape: the trace
     set of SceneAsanTop.ASAN_UBSAN_T (lib/AU/SceneAsanTop.v). *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_scene.images Require Import AsanUbsan.
(* Required first, so that the short names below resolve to the lib/Reusable kernel copies and the lib/AU
   relocated modules (scene's released tree also has lib/U/Reusable twins of some of them). Layout (a Theorem Labs lane, version A):
   lib/AU holds the asan-ubsan twins of the A files and the donor files whose closure reaches a module that differs
   between images (YCbq). Every other module comes from lib/Reusable, YCe5 and YK09 among them: the placement table
   of record marks both SHARED. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require SceneAsanBase.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require SceneAsanTop.
(* Gate 6h: no sink-head instance is in scope (lib/Reusable/SinkGuard.v removes the released src0 instances). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require SinkGuard.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK15 YK18 YI16 YO05 YO09 YO06 YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK0c YK0e YG0f YG00 YG01 YG0n YG0d YK04 YA0i YA0n YO01.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK09 YA0c YA0e YA01 YA02.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YCbq YC5d YCbp.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YB1v.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
(* The lib_shape is scene_shape (SceneAsanBase: AgreeScene.ag_sil_shape, built on ZTraceSpec.checksum_shape, as
   intended), passed by name at every site; no lib_shape instance is declared here. *)
#[local] Abbreviation TSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation TPH := AsanUbsan.M.phdrs.
Section b. Context {rc : YM05.RunCeil}.
Section d.
Variable TF : atable.
(* LPS 727298f3: the hand-off states are per CONFIG_RSEQ flag (AU/YB01r.v HS_tfib_r), so HS takes the flag. *)
Variable HS : Z -> nat -> option acs.
Variables FMT_OPEN FMT_RDERR FMT_USAGE : Z.
Variables A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY : Z.
Variable scene_tfib_lib_contract_x : YM05.RunCeil -> YK11.FPState -> Z -> Z -> Z -> Z -> Z -> Z ->
  asyms -> ameter_ops -> (Z -> Z) -> (Z -> Z) -> Z -> Z -> Prop.
Variable TS : asyms -> Prop.
(* The driver's site types are Section Variables. Their instances are the restaged core's Definitions at fx0, at
   scene's addresses (a Theorem Labs lane checked them against the .symtab): AU/YD1i.v:19 aread_check_stmt, AU/YD1w.v:119 /
   :144 / :151 xst_frame_tfa / printf_first_tfa / printf_next_tfa, AU/YD1x.v:37 / :38 / :57 / :83 / :69 est_img_tfa /
   est_frame_tfa / fwrite_site_tfa / refused_site_tfa / fprintf_s_site_tfa (bound in G_Close.v) and AU/YD1x.v:94
   exit_site_tfa (bound in G_Top.v). in_ro is bound in G_Close.v to the scene listing's in_roP over its relro
   window. *)
Variable in_ro : Z -> Prop.
Variable aread_check : asyms -> Prop.
Variable xst_frame : (nat -> (word -> bool) -> (word -> option byte) -> Prop) -> Prop.
Variables printf_first printf_next : asyms -> (nat -> (word -> bool) -> (word -> option byte) -> Prop) -> Prop.
Variables est_img est_frame : ((word -> bool) -> (word -> option byte) -> Prop) -> Prop.
Variables fwrite_site refused_site : asyms -> ((word -> bool) -> (word -> option byte) -> Prop) -> Prop.
Variable fprintf_s_site : asyms -> ((word -> bool) -> (word -> option byte) -> Prop) -> Z -> list byte -> list byte -> Prop.
Variable exit_site : asyms -> ((word -> bool) -> (word -> option byte) -> Prop) -> (nat -> (word -> bool) -> (word -> option byte) -> Prop) -> Prop.
(* YB1n.v HS_ok, over TF and HS: the launch input is YA02's, with the kernel record [kb], the exec file name
   and the SIGPIPE disposition [sdef] free, and the hand-off state the one of the run's own CONFIG_RSEQ flag. *)
Definition g_HS_ok (h : nat) (sp : word) (rdraw : EntryDraw) (brk0 mbase : word)
  (argv envp : list (list byte)) (fs0 : Fs.Fs) (stdin : InputStream) (uid gid hw : word)
  (groups : list word) (net : NetQueue) (nofile sigmask : word) (urnd : InputStream) (tmp : Fs.Fs)
  (kb : KernelBuild) (execfn : list byte) (sdef : bool) (fsq : Fs.Fs) (c : config) : Prop :=
  exists ch E R FULL model,
  HS (rseq_z (kb_rseq kb)) h = Some ch
  /\ c = cfg_of TSEGS R (pc ch) FULL model
  /\ cs_ok TSEGS TF YA02.LIMIT (YA02.TOP sp)
       (YA02.SINV0 TPH sp rdraw brk0 mbase argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef
          AsanUbsan.M.init_pc)
       (YA02.argH0 sp rdraw argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) fsq E ch R FULL model.
(* YB1n.v tfib_startup_T1's statement. *)
Definition g_startup_stmt : Prop :=
  forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)) (fs : Fs.Fs)
    (stdin : InputStream) (uid gid hw : word) (groups : list word) (net : NetQueue) (nofile sigmask : word)
    (urnd : InputStream) (tmp : Fs.Fs) (kb : KernelBuild) (execfn : list byte) (sdef : bool),
  valid_sp sp -> valid_brk TSEGS brk0 -> valid_mmap_base mbase -> valid_argv argv -> valid_envp envp ->
  entry_stack_fits sp argv envp -> valid_id uid -> valid_hwcap hw -> valid_nofile nofile ->
  valid_sigmask (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) ->
  valid_launch (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) ->
  entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw)
    (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) ->
  forall T : TSet, T [] ->
  (forall h c, g_HS_ok h sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef
     (fs_seed_tmp fs tmp) c -> srealizes TSEGS c T) ->
  srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk0 mbase rdraw YA02.LIMIT
    (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef)) T.
(* YB1n.v HS_ok_open, proved as the donor proves it (YA0e.v co_sinv), with NX0G (YA01.v). *)
Lemma g_hs_open :
  forall h sp rdraw brk0 mbase argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef fsq c,
  g_HS_ok h sp rdraw brk0 mbase argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef fsq c ->
  exists ch E R FULL model,
  HS (rseq_z (kb_rseq kb)) h = Some ch /\ c = cfg_of TSEGS R (pc ch) FULL model
  /\ cs_ok TSEGS TF YA02.LIMIT (YA02.TOP sp)
       (YA02.SINV0 TPH sp rdraw brk0 mbase argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef
          AsanUbsan.M.init_pc)
       (YA02.argH0 sp rdraw argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) fsq E ch R FULL model
  /\ (forall n, (n < NX0G)%nat ->
        ev E n = ev (YA02.E0 sp rdraw brk0 argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) n)
  /\ (forall a, YA02.argH0 sp rdraw argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef E a = true ->
        FULL a = wrap_mem (YA02.inp argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef) mbase TPH
          (Z_to_bv 64 (Z.of_N AsanUbsan.M.init_pc)) sp rdraw a)
  /\ eb E = eb (YA02.E0 sp rdraw brk0 argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef).
Proof.
  intros h sp rdraw brk0 mbase argv envp fs0 stdin uid gid hw groups net nofile sigmask urnd tmp kb execfn sdef fsq c
    (ch & E & R & FULL & model & Hh & Hc & HC).
  exists ch, E, R, FULL, model. split; [exact Hh|]. split; [exact Hc|]. split; [exact HC|].
  exact (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC).
Qed.
(* YD1q.v drv_mainX_stmt (YD1p.v), at scene_shape: the hand-off state of the run's own CONFIG_RSEQ flag, the
   stack invariant abstract (as YD1g.v, YD2i.v) and the launch's fifth [valid_entry] conjunct given. *)
Definition g_drv_mainX_stmt : Prop :=
  forall (sp : word) (rdraw : EntryDraw) (brk mbase : word) (inp : ProcInput) (h : nat) (ch : acs) (E : env)
    (R : bvmap 5 word) (FULL : word -> option byte) (model : Model) (SINV : env -> (word -> option byte) -> Prop),
  valid_sp sp -> valid_brk TSEGS brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  HS (rseq_z (kb_rseq (in_kernel inp))) h = Some ch ->
  (forall E' M, SINV E' M -> uE E' e_sp0 = YA02.TOP sp + 8388608) ->
  cs_ok TSEGS TF YA02.LIMIT (YA02.TOP sp) SINV
    (YA02.argH0 sp rdraw (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp)
       (in_hwcap inp) (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp)
       (in_kernel inp) (in_execfn inp) (in_sigpipe_default inp)) (in_fs inp) E ch R FULL model ->
  (forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 sp rdraw brk (in_argv inp) (in_envp inp) (in_image_fs inp)
     (in_stdin inp) (in_uid inp) (in_gid inp) (in_hwcap inp) (in_groups inp) (in_net inp) (in_nofile inp)
     (in_sigmask inp) (in_urandom inp) (in_tmp inp) (in_kernel inp) (in_execfn inp) (in_sigpipe_default inp)) n) ->
  (forall a, YA02.argH0 sp rdraw (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp) (in_uid inp)
     (in_gid inp) (in_hwcap inp) (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp)
     (in_tmp inp) (in_kernel inp) (in_execfn inp) (in_sigpipe_default inp) E a = true ->
   FULL a = wrap_mem inp mbase TPH (Z_to_bv 64 (Z.of_N AsanUbsan.M.init_pc)) sp rdraw a) ->
  srealizes TSEGS (cfg_of TSEGS R (pc ch) FULL model) (CLOSEDX (LS:=SceneAsanBase.scene_shape) inp).
(* The driver walk: YD1p.v tfib_drv_main's statement, every leaf it takes as a premise. *)
Definition g_drv_walk_stmt : Prop :=
  forall (B : asyms), TS B ->
  amalloc_realizes tfibsegs B -> afree_realizes tfibsegs B ->
  aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)) -> aread_check B ->
  forall (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z),
  (forall S m, mo_ok MT S m) -> (forall a, RLO <= a < RHI -> in_ro a) ->
  scene_tfib_lib_contract_x rc YK11.fx0 A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY B MT XM_LIB XN_LIB RLO RHI ->
  forall xst : nat -> (word -> bool) -> (word -> option byte) -> Prop,
  xst_frame xst -> printf_first B xst -> printf_next B xst ->
  forall est : (word -> bool) -> (word -> option byte) -> Prop,
  est_img est -> est_frame est -> fwrite_site B est -> refused_site B est ->
  fprintf_s_site B est FMT_OPEN (strB "cli: cannot open "%string) nlB ->
  fprintf_s_site B est FMT_RDERR (strB "cli: read error on "%string) nlB ->
  fprintf_s_site B est FMT_USAGE (strB "usage: "%string) (strB " INPUT"%string ++ nlB) ->
  exit_site B est xst ->
  g_drv_mainX_stmt.
(* The leaves (YD1q.v). *)
Variable B : asyms.
Hypothesis HB : TS B.
Hypothesis AMALLOC : amalloc_realizes tfibsegs B.
Hypothesis AFREE : afree_realizes tfibsegs B.
Hypothesis AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Hypothesis ARDCHK : aread_check B.
Variables (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z).
Hypothesis MT_FREE : forall S m, mo_ok MT S m.
Hypothesis RO_IN : forall a, RLO <= a < RHI -> in_ro a.
Hypothesis LIBX : forall fx : YK11.FPState,
  scene_tfib_lib_contract_x rc fx A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY B MT XM_LIB XN_LIB RLO RHI.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis XFR : xst_frame xst.
Hypothesis PF1 : printf_first B xst.
Hypothesis PFN : printf_next B xst.
Variable est : (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis ESTI : est_img est.
Hypothesis ESTF : est_frame est.
Hypothesis FWS : fwrite_site B est.
Hypothesis RFS : refused_site B est.
Hypothesis FPO : fprintf_s_site B est FMT_OPEN (strB "cli: cannot open "%string) nlB.
Hypothesis FPR : fprintf_s_site B est FMT_RDERR (strB "cli: read error on "%string) nlB.
Hypothesis FPU : fprintf_s_site B est FMT_USAGE (strB "usage: "%string) (strB " INPUT"%string ++ nlB).
Hypothesis EXS : exit_site B est xst.
(* Start-up and driver walk (the hand-off is g_hs_open above). *)
Hypothesis STARTUP : g_startup_stmt.
Hypothesis DRV : g_drv_walk_stmt.
Lemma g_drv_mainX : g_drv_mainX_stmt.
Proof.
  exact (DRV B HB AMALLOC AFREE AICPY ARDCHK MT XM_LIB XN_LIB RLO RHI MT_FREE RO_IN (LIBX YK11.fx0) xst XFR PF1 PFN
    est ESTI ESTF FWS RFS FPO FPR FPU EXS).
Qed.
(* YD1q.v tfib_srealizesX_of_main: the input is taken apart into its fields; [Run.valid_input] fixes the abort
   and terminal-SIGPIPE declarations, the address size and the channel reader, and says the kernel record is its
   own [recorded_kernel], so the input is [YA02.inp] at that record, the exec file name and the SIGPIPE
   disposition. *)
Theorem g_srealizes : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
  valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk mb rdraw) inp ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk mb rdraw YA02.LIMIT inp)
    (SPECX (LS:=SceneAsanBase.scene_shape) inp).
Proof.
  intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hlau Hceil.
  pose proof Hinp as (Hva & Hve & _ & _ & _ & [Huid _] & Hnof & Hsig & Hhw & Hab & Hmmu & _ & Hvl & Hcr & Hspt & Hkern).
  destruct inp as [argv envp fs stdin uid gid groups net nofile sigmask hw ab mmu urnd tmp kern execfn cr spd spt].
  cbn [in_argv in_envp in_uid in_hwcap in_nofile in_abort_terminal in_va_size in_channel_reader in_sigpipe_terminal
    in_kernel] in Hva, Hve, Hfit, Huid, Hhw, Hnof, Hab, Hmmu, Hcr, Hspt, Hkern.
  subst ab mmu cr spt.
  rewrite Hkern in Hinp, Hsig, Hvl, Hlau |- *.
  change (mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw false Sv48 urnd tmp
    (recorded_kernel kern) execfn true spd false)
    with (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd) in *.
  apply (srz_conseq TSEGS _
    (CLOSEDX (LS:=SceneAsanBase.scene_shape)
      (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd)));
    [| apply t_eq_sym; apply (specx_closedx_eq (LS:=SceneAsanBase.scene_shape))].
  apply (STARTUP sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd
    Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hnof Hsig Hvl Hlau
    (CLOSEDX (LS:=SceneAsanBase.scene_shape)
      (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd))
    (CLOSEDX_has_nil (LS:=SceneAsanBase.scene_shape) _)).
  intros h c Hok.
  destruct (g_hs_open h sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd
    (fs_seed_tmp fs tmp) c Hok) as (ch & E & R & FULL & model & Hch & -> & HC & HE & HM & _).
  assert (SP0 : forall E' M, YA02.SINV0 TPH sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask
    urnd tmp kern execfn spd AsanUbsan.M.init_pc E' M -> uE E' e_sp0 = YA02.TOP sp + 8388608).
  { intros E' M HSv. eapply YA02.SINV0_sp0; try eassumption. Unshelve. all: first [assumption | exact TSEGS | exact TF]. }
  exact (g_drv_mainX sp rdraw brk mb (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd)
    h ch E R FULL model _ Hsp Hbrk Hfit Hinp Hlau Hceil Hch SP0 HC HE HM).
Qed.
End d.
End b.
