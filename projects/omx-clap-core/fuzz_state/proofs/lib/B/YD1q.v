(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/B/YD1q.v, with its module paths changed and its addresses moved to omx-clap-core/fuzz_state's ASan build. *)
(* Modified by Theorem Labs, 2026-10-29: A/AD1q.v's delta -> (tfib_srealizesX over LI) applied by 3-way merge; B's literals unchanged. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the revision's launch (CONFIG_RSEQ-sized auxv, execfn, group id, launch premises); the input-owned, top-anchored launch stack; the start-up certificate per CONFIG_RSEQ flag with states computed in the build); with libreac/fuzz_boxreg's repair of its copy of this file (its proofs/lib/B/AD1q.v). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.omx_clap_core.fuzz_state.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK15 YK18 YK0c YK0e YK09 YA0c YA0e YA01 YA02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB12 YB1h YB01r YB1n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0f YG00 YG01 YG0n YG0d YK04 YA0i YA0n YCbq YI16 YC5d YCbp.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YCfn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YI17 YO08.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0f YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YF0m YCeg YD1v YD1w YD1x YD1i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YCfn YD1p.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
Section b. Context {rc : YM05.RunCeil} {LS : lib_shape}.
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
Variable LI : Z -> world tfibsegs -> (word -> option byte) -> Prop.
Hypothesis LIBX : tfib_lib_contract_xI_all B MT XM_LIB XN_LIB RLO RHI LI.
Hypothesis LIK : lib_inv_stable LI.
Hypothesis LI0 : lib_inv_init LI.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis XFR : xst_frame_tfa xst.
Hypothesis PF1 : printf_first_tfa B xst.
Hypothesis PFN : printf_next_tfa B xst.
Variable est : (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis ESTI : est_img_tfa est.
Hypothesis ESTF : est_frame_tfa est.
Hypothesis FWS : fwrite_site_tfa B est.
Hypothesis RFS : refused_site_tfa B est.
Hypothesis FPO : fprintf_s_site_tfa B est 0x1d7d8 (strB "cli: cannot open "%string) nlB.
Hypothesis FPR : fprintf_s_site_tfa B est 0x1d7ed (strB "cli: read error on "%string) nlB.
Hypothesis FPU : fprintf_s_site_tfa B est 0x15897 (strB "usage: "%string) (strB " INPUT"%string ++ nlB).
Hypothesis EXS : exit_site_tfa B est xst.
(* LPS 727298f3: the driver's main is stated over the hand-off state of the run's own CONFIG_RSEQ flag
   ([HS_tfib_r]), with the stack invariant abstract and the launch's fifth [valid_entry] conjunct
   [entry_launch_ok_va] given, which the start-up's invariant reads. *)
Definition drv_mainX_stmt : Prop :=
forall (sp : word) (rdraw : EntryDraw) (brk mbase : word) (inp : ProcInput) (h : nat) (ch : acs) (E : env) (R : bvmap 5 word)
(FULL : word -> option byte) (model : Model) (SINV : env -> (word -> option byte) -> Prop),
valid_sp sp -> valid_brk TSEGS brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
HS_tfib_r (rseq_z (kb_rseq (in_kernel inp))) h = Some ch ->
(forall E' M, SINV E' M -> uE E' e_sp0 = YA02.TOP sp + 8388608) ->
cs_ok TSEGS TFIB YA02.LIMIT (YA02.TOP sp) SINV
(YA02.argH0 sp rdraw (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp) (in_hwcap inp)
  (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp) (in_kernel inp)
  (in_execfn inp) (in_sigpipe_default inp)) (in_fs inp) E ch R FULL model ->
(forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 sp rdraw brk (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp)
  (in_uid inp) (in_gid inp) (in_hwcap inp) (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp)
  (in_tmp inp) (in_kernel inp) (in_execfn inp) (in_sigpipe_default inp)) n) ->
(forall a, YA02.argH0 sp rdraw (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp) (in_hwcap inp)
  (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp) (in_kernel inp)
  (in_execfn inp) (in_sigpipe_default inp) E a = true ->
FULL a = wrap_mem inp mbase TPH (Z_to_bv 64 (Z.of_N AsanUbsan.M.init_pc)) sp rdraw a) ->
srealizes TSEGS (cfg_of TSEGS R (pc ch) FULL model) (CLOSEDX inp).
Lemma DRV_MAINX : drv_mainX_stmt.
Proof. exact (tfib_drv_main B HB AMALLOC AFREE AICPY ARDCHK MT XM_LIB XN_LIB RLO RHI MT_FREE RO_IN LI (LIBX _) LIK LI0 xst XFR PF1 PFN est ESTI ESTF FWS RFS FPO FPR FPU EXS). Qed.
(* The input is taken apart into its fields; [Run.valid_input] fixes the abort and terminal-SIGPIPE
   declarations, the address size and the channel reader, and says the kernel record is its own
   [recorded_kernel], so the input is [YA02.inp] at that record, the exec file name and the SIGPIPE
   disposition. *)
Theorem tfib_srealizesX : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
entry_launch_ok_va Sv48 (mkEntry sp brk mb rdraw) inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk mb rdraw YA02.LIMIT inp) (SPECX inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hlau Hceil.
pose proof Hinp as (Hva & Hve & _ & _ & _ & [Huid _] & Hnof & Hsig & Hhw & Hab & Hmmu & _ & Hvl & Hcr & Hspt & Hkern).
destruct inp as [argv envp fs stdin uid gid groups net nofile sigmask hw ab mmu urnd tmp kern execfn cr spd spt].
cbn [in_argv in_envp in_uid in_hwcap in_nofile in_abort_terminal in_va_size in_channel_reader in_sigpipe_terminal in_kernel]
in Hva, Hve, Hfit, Huid, Hhw, Hnof, Hab, Hmmu, Hcr, Hspt, Hkern.
subst ab mmu cr spt.
rewrite Hkern in Hinp, Hsig, Hvl, Hlau |- *.
change (mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw false Sv48 urnd tmp (recorded_kernel kern) execfn true spd false)
with (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd) in *.
apply (srz_conseq TSEGS _ (CLOSEDX (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd)));
[| apply t_eq_sym; apply specx_closedx_eq].
apply (tfib_startup_T1 sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd
Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hnof Hsig Hvl Hlau
(CLOSEDX (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd)) (CLOSEDX_has_nil _)).
intros h c Hok.
destruct (HS_ok_open h sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd
(fs_seed_tmp fs tmp) c Hok) as (ch & E & R & FULL & model & Hch & -> & HC & HE & HM & _).
assert (SP0 : forall E' M, YA02.SINV0 TPH sp rdraw brk mb argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp
kern execfn spd AsanUbsan.M.init_pc E' M -> uE E' e_sp0 = YA02.TOP sp + 8388608).
{ intros E' M HSv. eapply YA02.SINV0_sp0; try eassumption. Unshelve. all: first [assumption | exact TSEGS | exact TFIB]. }
exact (DRV_MAINX sp rdraw brk mb (YA02.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd tmp kern execfn spd)
h ch E R FULL model _ Hsp Hbrk Hfit Hinp Hlau Hceil Hch SP0 HC HE HM).
Qed.
End d.
End b.
