(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK15 YK18 YK0c YK0e YK09 YA0c YA0e YA01 YA02.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB12 AB1h AB01 AB1n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0f YG00 YG01 YG0n YG0d YK04 YA0i YA0n YCbq YI16 YC5d YCbp.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACfn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO05 YO09 YO06 YO01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI17 YI0a YO08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0f YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0m ACeg AD1v AD1w AD1x AD1i.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACfn AD1p.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.
Lemma ff_unl_has_nil : forall K fs, (forall l, K l []) -> ff_unl K fs [].
Proof.
intros K fs HK. unfold ff_unl, ff_leaf, unlink_shape.
destruct (fs_under fs sink_path); [apply HK|]. destruct (Fs.fs_lookup fs sink_path); [left; apply HK | apply HK].
Qed.
Lemma ff_libk_has_nil : forall pl fs K, (forall l, K l []) -> ff_libk pl fs K [].
Proof.
intros pl fs K HK. unfold ff_libk.
destruct (ff_cfg (zbytes pl)) as [[[g loops] rest]|]; [| apply HK].
destruct (g_opens g); [| apply ff_unl_has_nil; exact HK].
unfold openat_shape. destruct (fs_under fs sink_path); [apply ff_unl_has_nil; exact HK | left; apply ff_unl_has_nil; exact HK].
Qed.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance ff_lib_shape.
Section b. Context {rc : YM05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis AMALLOC : amalloc_realizes tfibsegs B.
Hypothesis AFREE : afree_realizes tfibsegs B.
Hypothesis AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Hypothesis ARDCHK : aread_check_stmt B.
Variables (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z).
Hypothesis MT_FREE : forall S m, mo_ok MT S m.
Hypothesis RO_IN : forall a, RLO <= a < RHI -> in_ro_tfa a.
Hypothesis LIBX : tfib_lib_contract_x_all B MT XM_LIB XN_LIB RLO RHI.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis XFR : xst_frame_tfa xst.
Hypothesis PF1 : printf_first_tfa B xst.
Hypothesis PFN : printf_next_tfa B xst.
Variable est : (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis ESTI : est_img_tfa est.
Hypothesis ESTF : est_frame_tfa est.
Hypothesis FWS : fwrite_site_tfa B est.
Hypothesis RFS : refused_site_tfa B est.
Hypothesis FPO : fprintf_s_site_tfa B est 0x1d727 (strB "cli: cannot open "%string) nlB.
Hypothesis FPR : fprintf_s_site_tfa B est 0x1d73c (strB "cli: read error on "%string) nlB.
Hypothesis FPU : fprintf_s_site_tfa B est 0x15859 (strB "usage: "%string) (strB " INPUT"%string ++ nlB).
Hypothesis EXS : exit_site_tfa B est xst.
Definition drv_mainX_stmt : Prop :=
forall (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput) (h : nat) (ch : acs) (E : env) (R : bvmap 5 word)
(FULL : word -> option byte) (model : Model),
valid_sp sp -> valid_brk TSEGS brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
HS_tfib h = Some ch ->
cs_ok TSEGS TFIB YA02.LIMIT (YA02.TOP sp)
(YA02.SINV0 TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model ->
(forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) n) ->
(forall a, YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) E a = true ->
FULL a = wrap_mem TPH sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw a) ->
srealizes TSEGS (cfg_of TSEGS R (pc ch) FULL model) (CLOSEDX inp).
Lemma DRV_MAINX : drv_mainX_stmt.
Proof. exact (tfib_drv_main B HB AMALLOC AFREE AICPY ARDCHK MT XM_LIB XN_LIB RLO RHI MT_FREE RO_IN (LIBX _) xst XFR PF1 PFN est ESTI ESTF FWS RFS FPO FPR FPU EXS). Qed.
Theorem tfib_srealizesX : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk mb rdraw YA02.LIMIT inp) (SPECX inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil.
pose proof Hinp as (Hva & Hve & Hvfs & _ & [Huid Hgid] & Hnof & Hsig & Hhw & Hab & Hmmu & _).
destruct inp as [argv envp fs stdin uid gid groups net nofile sigmask hw ab mmu urnd tmp]. cbn in *. subst ab mmu.
change (mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw false Sv48 urnd tmp)
with (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp) in *.
apply (srz_conseq TSEGS _ (CLOSEDX (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp)));
[| apply t_eq_sym; apply specx_closedx_eq].
apply (tfib_startup_T1 sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp Hsp Hbrk Hva Hve Hfit Huid Hhw
(CLOSEDX (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp)) (CLOSEDX_has_nil _)).
intros h c Hok.
destruct (HS_ok_open h sp rdraw brk argv envp uid hw (fs_seed_tmp fs tmp) c Hok) as (ch & E & R & FULL & model & Hch & -> & HC & HE & HM & _).
exact (DRV_MAINX sp rdraw brk (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp) h ch E R FULL model
Hsp Hbrk Hfit Hinp Hceil Hch HC HE HM).
Qed.
End d.
End b.
