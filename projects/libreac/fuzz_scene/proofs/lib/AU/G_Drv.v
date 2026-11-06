(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/YD1q.v (with the statements of
   YB1n.v:44-59 HS_ok / tfib_startup_T1, YB1n.v:73-81 HS_ok_open and YD1p.v:77-88 tfib_drv_main) for
   fuzz_scene's asan-ubsan image, module paths changed. *)
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
   - B's tables: the donor's YF0m.v:291 TfibSyms is measured unsatisfiable when relocated by rename (a Theorem Labs lane, 22:25Z);
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
   of record (port/6o/placement.tsv at 5977155c3d7) marks both SHARED. *)
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
Variable HS : nat -> option acs.
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
(* YB1n.v:44-50 HS_ok, over TF and HS. *)
Definition g_HS_ok (h : nat) (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (uid hw : word)
  (fs : Fs.Fs) (c : config) : Prop :=
  exists ch E R FULL model,
  HS h = Some ch
  /\ c = cfg_of TSEGS R (pc ch) FULL model
  /\ cs_ok TSEGS TF YA02.LIMIT (YA02.TOP sp)
       (YA02.SINV0 TPH sp rdraw brk0 argv envp uid hw) (YA02.argH0 TPH sp rdraw argv envp uid hw) fs E ch R FULL model.
(* YB1n.v:51-59 tfib_startup_T1's statement. *)
Definition g_startup_stmt : Prop :=
  forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)) (fs : Fs.Fs)
    (stdin : InputStream) (uid gid hw : word) (groups : list word) (net : NetQueue) (nofile sigmask : word)
    (urnd : InputStream) (tmp : Fs.Fs),
  valid_sp sp -> valid_brk TSEGS brk0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  valid_id uid -> valid_hwcap hw ->
  forall T : TSet, T [] ->
  (forall h c, g_HS_ok h sp rdraw brk0 argv envp uid hw (fs_seed_tmp fs tmp) c -> srealizes TSEGS c T) ->
  srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk0 mbase rdraw YA02.LIMIT
    (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp)) T.
(* YB1n.v:73-86 HS_ok_open, proved as the donor proves it (YA0e.v:232 co_sinv), with NX0G (YA01.v:711). *)
Lemma g_hs_open :
  forall (h : nat) (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (uid hw : word)
    (fs : Fs.Fs) (c : config),
  g_HS_ok h sp rdraw brk0 argv envp uid hw fs c ->
  exists ch E R FULL model,
  HS h = Some ch /\ c = cfg_of TSEGS R (pc ch) FULL model
  /\ cs_ok TSEGS TF YA02.LIMIT (YA02.TOP sp)
       (YA02.SINV0 TPH sp rdraw brk0 argv envp uid hw) (YA02.argH0 TPH sp rdraw argv envp uid hw) fs E ch R FULL model
  /\ (forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 TPH sp rdraw brk0 argv envp uid hw) n)
  /\ (forall a, YA02.argH0 TPH sp rdraw argv envp uid hw E a = true -> FULL a = wrap_mem TPH sp argv envp uid hw rdraw a)
  /\ eb E = eb (YA02.E0 TPH sp rdraw brk0 argv envp uid hw).
Proof.
  intros h sp rdraw brk0 argv envp uid hw fs c (ch & E & R & FULL & model & Hh & Hc & HC).
  exists ch, E, R, FULL, model. split; [exact Hh|]. split; [exact Hc|]. split; [exact HC|].
  exact (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC).
Qed.
(* YD1q.v:60-72 drv_mainX_stmt (YD1p.v:77-88), at scene_shape. *)
Definition g_drv_mainX_stmt : Prop :=
  forall (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput) (h : nat) (ch : acs) (E : env)
    (R : bvmap 5 word) (FULL : word -> option byte) (model : Model),
  valid_sp sp -> valid_brk TSEGS brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  HS h = Some ch ->
  cs_ok TSEGS TF YA02.LIMIT (YA02.TOP sp)
    (YA02.SINV0 TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model ->
  (forall n, (n < NX0G)%nat ->
     ev E n = ev (YA02.E0 TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) n) ->
  (forall a, YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) E a = true ->
     FULL a = wrap_mem TPH sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw a) ->
  srealizes TSEGS (cfg_of TSEGS R (pc ch) FULL model) (CLOSEDX (LS:=SceneAsanBase.scene_shape) inp).
(* The driver walk: YD1p.v:29-88 tfib_drv_main's statement, every leaf it takes (YD1p.v:31-61) as a premise. *)
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
(* The leaves (YD1q.v:37-59). *)
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
(* YD1q.v:75-94 tfib_srealizesX. *)
Theorem g_srealizes : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
  valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk mb rdraw YA02.LIMIT inp)
    (SPECX (LS:=SceneAsanBase.scene_shape) inp).
Proof.
  intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil.
  pose proof Hinp as (Hva & Hve & Hvfs & _ & [Huid Hgid] & Hnof & Hsig & Hhw & Hab & Hmmu & _).
  destruct inp as [argv envp fs stdin uid gid groups net nofile sigmask hw ab mmu urnd tmp]. cbn in *. subst ab mmu.
  change (mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw false Sv48 urnd tmp)
    with (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp) in *.
  apply (srz_conseq TSEGS _
    (CLOSEDX (LS:=SceneAsanBase.scene_shape) (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp)));
    [| apply t_eq_sym; apply (specx_closedx_eq (LS:=SceneAsanBase.scene_shape))].
  apply (STARTUP sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp
    Hsp Hbrk Hva Hve Hfit Huid Hhw
    (CLOSEDX (LS:=SceneAsanBase.scene_shape) (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp))
    (CLOSEDX_has_nil (LS:=SceneAsanBase.scene_shape) _)).
  intros h c Hok.
  destruct (g_hs_open h sp rdraw brk argv envp uid hw (fs_seed_tmp fs tmp) c Hok)
    as (ch & E & R & FULL & model & Hch & -> & HC & HE & HM & _).
  exact (g_drv_mainX sp rdraw brk (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp)
    h ch E R FULL model Hsp Hbrk Hfit Hinp Hceil Hch HC HE HM).
Qed.
End d.
End b.
