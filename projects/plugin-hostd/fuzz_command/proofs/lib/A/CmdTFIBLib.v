(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AD2o.v (tfib_srealizesX_rc, tfib_srealizesX_top, TFIB_T_of_partsXF) and the XL0 of its A/ACfi.v for plugin-hostd/fuzz_command, in the form of libreac/fuzz_grant's lib/A/AGrantT.v and lib/A/GrantTop.v: TFIB_T of lib/A/CmdTFIB.v from one hypothesis on the program, the contract tfib_lib_contract_x_all of lib/A/ACfn.v (fuzz_command's call index and GI_cmdA) at every run ceiling and call index, instead of cgif's three library-function contracts; the allocator laws, the allocator and interceptor contracts and the driver's sites are discharged as AD2o.v discharges them, on fuzz_command's ASan image; the start-up certificate classes of lib/A/CmdStartCert.v and the module destructor's contract (class DtorExit of lib/A/AE37.v) are Section hypotheses (with the certificate checks' classes of AD1g.v, AD2i.v, AD1d.v, AD1f.v, AD2k.v and the a_vis alignment check class TfibAvis8 of CmdWorldH8.v); the driver's free, printf and exit sites are discharged at every float state; the plain build's sink instances are removed as GrantTop.v removes them. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.plugin_hostd.fuzz_command.images Require Import Asan.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK15 YK18 YA02.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1h.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0f YG00 YG01 YG0n YG0d YG05 YG0q YI16 YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import ACfn AB1v AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YF0p.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AD2l ACeg AD1v AD1w AD1x AD1i AD1k AD1l AD1o AD1j AD2m AF0w AF0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import CmdStartCert AE37 AD1q CmdShape CmdTFIB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AD1g AD2i AD1d AD1f AD2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI5b YI5c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance cmd_shape.
Open Scope Z_scope.
(* The guard: the plain build's sink hints (lib/Reusable/YI5b.v src0_sink_head and lib/Reusable/YI5c.v src0_sink,
   both global instances) are out of the way, so no sink argument of this file can be filled with the plain build's
   head: a bare `sink_head` is the ASan image's own head (lib/A/AE2k.v), as `sk_probe_is_asan` shows. The paths are
   written in full: lib/U/Reusable has modules of the same short names (YI16, YI5b, YI5c), loaded in this closure. *)
#[local] Remove Hints OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
#[local] Remove Hints OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable.YI5c.src0_sink : typeclass_instances.
Definition sk_probe : OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable.YI16.sink_head := _.
Lemma sk_probe_is_asan : sk_probe = AE2k.tfib_sink_head.
Proof. reflexivity. Qed.
(* The meter the program contract carries: it counts nothing (cgif_file's XL0). *)
Definition XL0 : Z -> Z := fun _ => 0.
Lemma valid_sp_windowX : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.
Section b.
(* The start-up certificate (lib/A/CmdStartCert.v, and the checks of lib/A/AD1g.v, AD2i.v, AD1d.v, AD1f.v, AD2k.v,
   CmdWorldH8.v) and the module destructor's contract (lib/A/AE37.v): named hypotheses until fuzz_command's own are
   compiled. *)
Context {SD : StartData} {ST : StartThm} {HCK : AD1g.TfibHolesChk} {HIF : AD1g.TfibHolesIf} {ECA : AD2i.EntryCheckAll} {HCB : AD1d.TfibHolesChkB} {HIS : AD1f.TfibHolesImgsh} {FCA : AD2k.FinvCheckAll}.
Context {HSA : TfibHolesStkAux} {HAV : CmdWorldH8.TfibAvis8}.
Context {DE : DtorExit}.
Let B : asyms := CmdB.
Let HB : CmdBSyms B := CmdB_syms.
Let HD : forall t, as_dhash B t = tfib_dhash t := fun t => eq_refl.
(* What the program side owes (C3): one call of LLVMFuzzerTestOneInput (lib/A/ACfn.v A_LLVMF) keeps the ASan state,
   returns 0, writes nothing, leaves the caller's input bytes as it found them and carries fuzz_command's global
   invariant GI_cmdA from call j to call j + 1 (lib/A/ACfn.v tfib_lib_contract_x_all), at every run ceiling and
   call index, over the read-only range CMD_RLO..CMD_RHI (lib/A/Prog/CmdGlob.v: .data.rel.ro and .got, lib/A/ACeg.v
   in_ro_tfa's second part). *)
Hypothesis LIBX : forall (rc : YM05.RunCeil) (j : nat),
@tfib_lib_contract_x_all rc cmd_shape CmdB ameter_triv XL0 XL0 CMD_RLO CMD_RHI GI_cmdA j.
Section RC. Context {rc : YM05.RunCeil}.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let AMALLOC : amalloc_realizes tfibsegs B := tfib_amalloc_realizes B HB HD.
(* The free, printf and exit sites are reached after a program call too, at the float state the call returned with:
   each is discharged at every float state by the same lemma (lib/A/AD1p.v takes them so). *)
Let AFREE : forall fy : YK11.FPState, afree_realizes (fx := fy) tfibsegs B := fun fy => afree_realizes_closed (fx := fy) B HB HD.
Let AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)) := tfib_AICPY B HB.
Let RO_IN : forall a, CMD_RLO <= a < CMD_RHI -> in_ro_tfa a := fun a H => or_intror H.
Let ARDCHK : aread_check_stmt B := tfib_ARDCHK B HB.
Let MT_FREE : forall S m, mo_ok ameter_triv S m := fun _ _ => I.
Let xst : nat -> (word -> bool) -> (word -> option byte) -> Prop := AD1k.xst.
Let XFR : xst_frame_tfa xst := tfib_xst_frame.
Let PF1 : forall fy : YK11.FPState, printf_first_tfa (fx := fy) B xst := fun fy => tfib_printf_first (fx := fy) B HB (AR_laws_ok tfibsegs B) HB.
Let PFN : forall fy : YK11.FPState, printf_next_tfa (fx := fy) B xst := fun fy => tfib_printf_next (fx := fy) B HB (AR_laws_ok tfibsegs B) HB.
Let est : (word -> bool) -> (word -> option byte) -> Prop := AD1k.est.
Let ESTI : est_img_tfa est := tfib_est_img.
Let ESTF : est_frame_tfa est := tfib_est_frame.
Let FWS : fwrite_site_tfa B est := tfib_fwrite_site B HB LAWS.
Let RFS : refused_site_tfa B est := tfib_refused_site B HB LAWS HB.
Let FPO : fprintf_s_site_tfa B est 0x1d922 (strB "cli: cannot open "%string) nlB := tfib_fprintf_open_site B HB LAWS HB.
Let FPR : fprintf_s_site_tfa B est 0x1d937 (strB "cli: read error on "%string) nlB := tfib_fprintf_rderr_site B HB LAWS HB.
Let FPU : fprintf_s_site_tfa B est 0x158ea (strB "usage: "%string) (strB " INPUT"%string ++ nlB) := tfib_fprintf_usage_site B HB LAWS HB.
Let EXS : forall fy : YK11.FPState, exit_site_tfa (fx := fy) B est xst := fun fy => tfib_exit_site (fx := fy) B HB (AR_laws_ok tfibsegs B).
Lemma cmd_srealizesX_rc : forall sp rdraw brk mb inp,
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk mb rdraw target_alloc_limit inp) (SPECX inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil.
change target_alloc_limit with YA02.LIMIT.
exact (tfib_srealizesX B HB AMALLOC AFREE AICPY ARDCHK ameter_triv XL0 XL0 CMD_RLO CMD_RHI MT_FREE RO_IN (LIBX rc) xst XFR PF1 PFN est ESTI ESTF FWS RFS FPO FPR FPU EXS
sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil).
Qed.
End RC.
Theorem cmd_srealizesX_top : forall sp rdraw brk mb inp,
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk mb rdraw target_alloc_limit inp) (SPECX inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp.
exact (@cmd_srealizesX_rc (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowX sp Hsp)) sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp (YM05.ceil_of_top_run _)).
Qed.
(* Shared contract C2: the driver and the start-up over the program contract. *)
Theorem cmd_TFIB_T_of_lib : TFIB_T.
Proof. intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp. exact (cmd_srealizesX_top sp rnd brk mbase inp Hsp Hbrk Hmb Hfit Hinp). Qed.
End b.
