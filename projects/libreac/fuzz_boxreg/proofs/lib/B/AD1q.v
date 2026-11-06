(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made for libreac/fuzz_boxreg's ASan+UBSan build from
   proofs/cgif/cgif_file_fuzzer/lib/YD1q.v (origin/ossv/recipes c8557374ad2), the ASan+UBSan twin of cgif's
   lib/A/AD1q.v: module paths changed to lib/B, TfibSyms -> lib.B.AF0m's BoxregSyms (fully qualified, so it cannot
   bind to lib/A/AF0m.v's record of the same name), the library shape lib/A/BoxShape.v box_shape
   in place of cgif's ff_lib_shape (so cgif's YI17 / YI0a and their lemmas ff_unl_has_nil / ff_libk_has_nil are
   dropped), the three fprintf format addresses moved to fuzz_boxreg.asan-ubsan, and drv_mainX_stmt / DRV_MAINX
   inlined into the proof of tfib_srealizesX (as this tree's lib/A/AD1q.v does). *)
(* Modified by Theorem Labs, 2026-10 (a Theorem Labs lane): the float state at return of LLVMFuzzerTestOneInput left open, in
   fuzz_grant's shape (a working branch bd0315ce146, proofs/libreac/fuzz_grant/lib/A/AD1q.v; a Theorem Labs lane's
   path-mapped diff core/fxslot.thin.patch, its AD1q hunks): drv_mainX_stmt and the start-up lemma
   tfib_srealizesX_of_main (the start-up proof this file had, unchanged); tfib_srealizesXP, the closed walk with the
   float-state invariant P (the core's tfib_drv_main at LIBC : forall fx, P fx -> tfib_lib_contract_xP (fx := fx) ..
   P); tfib_srealizesXF, it at P = a zero rounding mode with LIBX : ACfn.v tfib_lib_contract_xf_all; and
   tfib_srealizesX, the name the closing reads, now from LIBX : ACfn.v tfib_lib_contract_x_all through
   tfib_lib_contract_xf_all_of_x_all. NOT fuzz_grant's pinned tfib_srealizesX: boxreg's whole-run contract returns at
   some fx' (its clause, since a working branch ac56ab8e8ff), so the driver goes on at fx' and its
   after-call hypotheses AFREE / PF1 / PFN / EXS are asked at every float state with a zero rounding mode, as in
   tfib_srealizesXF; a form with them at YK11.fx0 only does not follow. The fprintf string addresses FPO / FPR /
   FPU stay this file's (0x1d605 / 0x1d61a / 0x157df). *)
(* boxreg content behind cgif's module name; source lib/B/Prog/BoxBLibX.v / lib/A/BoxShape.v.
   Its core modules are in this tree; among the Requires below, its proof rests on lib/B/AB1n.v,
   lib/B/ACfn.v and lib/B/AD1p.v (the start-up theorem, LIBX and the driver's main).
   Read from this module (before the fx-slot): tfib_srealizesX only (cgif YD1q.v:75, read by AD2o.v:71; for fuzz_boxreg,
   lib/B/Prog/BoxBClose.v's CORE_A, "AD1q tfib_srealizesX with AD2o's core premises discharged"). This file states
   exactly that name, in cgif's shape: the Section hypotheses are cgif's, LIBX is lib/B/ACfn.v's
   tfib_lib_contract_x_all (BoxBLibX.v's tbfib_lib_contract_x_all at the instance ACfn.v names) at box_shape, and the
   proof is cgif's: the start-up theorem tfib_startup_T1 (B/AB1n.v), the hand-off HS_ok_open, and the driver's main
   tfib_drv_main (B/AD1p.v), whose LIBC is LIBX at fx0.
   Constants (each measured ONCE on the ORIGINAL unstripped image
   the release's unstripped fuzz_boxreg.asan-ubsan, sha256
   1d548458eac37ae17f9e8dfb06a5dfef3c606ec9e03eca8ef291d5fec9dce495, with pyelftools 0.33 and capstone 5.0.7; each
   string occurs exactly once in the whole file, .rodata; main is 0x7fb0c, 708 bytes):
   - FPO 0x1d605: "cli: cannot open %s\n" (NUL-terminated, the only occurrence); main loads it into a1 with
     `auipc a1, 0xfff9e` at 0x7fda8 and `addi a1, a1, -0x7a3` at 0x7fdac (0x7fda8 - 0x62000 - 0x7a3 = 0x1d605),
     a0 = stderr, before the fprintf call at 0x7fd6c. cgif: 0x1d6e9. ASan build: the same 0x1d605, a1 at 0x7fd4c.
   - FPR 0x1d61a: "cli: read error on %s\n" (only occurrence); `auipc a1, 0xfff9e` at 0x7fd44 and
     `addi a1, a1, -0x72a` at 0x7fd48 (0x7fd44 - 0x62000 - 0x72a = 0x1d61a). cgif: 0x1d6fe. ASan build: a1 at 0x7fce8.
   - FPU 0x157df: "usage: %s INPUT\n" (only occurrence); `auipc a1, 0xfff96` at 0x7fcb4 and
     `addi a1, a1, -0x4d5` at 0x7fcb8 (0x7fcb4 - 0x6a000 - 0x4d5 = 0x157df), before the fprintf call at 0x7fcbc.
     cgif: 0x15859. ASan build: a1 at 0x7fc58. *)
(* Modified by Theorem Labs, 2026-10 (a Theorem Labs lane): tfib_srealizesXP takes P_FRM and passes it to the core's tfib_drv_main
   (AD1p.v P_FRM, freeze 4 + 5); tfib_srealizesXF gives it for P = a zero rounding mode, where it is the identity. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_boxreg.images Require Import AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK15 YK18 YK0c YK0e YK09 YA0c YA0e YA01 YA02.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B Require Import AB12 AB1h AB01 AB1n.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0f YG00 YG01 YG0n YG0d YK04 YA0i YA0n YCbq YI16 YC5d YCbp.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B Require Import ACfn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YI16 YO08.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require BoxShape.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0f YG0d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B Require Import AB1v AF0m ACeg AD1v AD1w AD1x AD1i.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B Require Import ACfn AD1p.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK0o.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.BoxShape.box_shape.
Section b. Context {rc : YM05.RunCeil}.
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
(* The start-up part of the closed walk, at YK11.fx0: from the start state to the driver's main (this file's start-up
   proof, unchanged). *)
Lemma tfib_srealizesX_of_main : drv_mainX_stmt -> forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk mb rdraw YA02.LIMIT inp) (SPECX inp).
Proof.
intros DRV_MAINX sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil.
pose proof Hinp as (Hva & Hve & Hvfs & _ & [Huid Hgid] & Hnof & Hsig & Hhw & Hab & Hmmu & _).
destruct inp as [argv envp fs stdin uid gid groups net nofile sigmask hw ab mmu urnd tmp].
cbn in Hsp, Hbrk, Hmb, Hfit, Hinp, Hceil, Hva, Hve, Hvfs, Huid, Hgid, Hnof, Hsig, Hhw, Hab, Hmmu |- *. subst ab mmu.
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
(* The closed walk with the float-state invariant P (fuzz_grant AD1q.v Section dP): the walk starts at YK11.fx0 (P0),
   each call of LLVMFuzzerTestOneInput returns at some float state with P (LIBX, ACfn.v tfib_lib_contract_xP), and the
   driver goes on there, so its after-call hypotheses (AFREE, PF1, PFN, EXS) are asked at every float state with P. *)
Section dP.
Variable P : YK11.FPState -> Prop.
Hypothesis P0 : P YK11.fx0.
Variable B : asyms.
Hypothesis HB : OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.AF0m.BoxregSyms B.
Hypothesis AMALLOC : amalloc_realizes tfibsegs B.
Hypothesis AFREE : forall fx : YK11.FPState, P fx -> afree_realizes (fx := fx) tfibsegs B.
Hypothesis AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Hypothesis ARDCHK : aread_check_stmt B.
Variables (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z).
Hypothesis MT_FREE : forall S m, mo_ok MT S m.
Hypothesis RO_IN : forall a, RLO <= a < RHI -> in_ro_tfa a.
Hypothesis LIBX : forall fx : YK11.FPState, P fx -> tfib_lib_contract_xP (fx := fx) B MT XM_LIB XN_LIB RLO RHI P.
Hypothesis P_FRM : forall fx : YK11.FPState, P fx -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis XFR : xst_frame_tfa xst.
Hypothesis PF1 : forall fx : YK11.FPState, P fx -> printf_first_tfa (fx := fx) B xst.
Hypothesis PFN : forall fx : YK11.FPState, P fx -> printf_next_tfa (fx := fx) B xst.
Variable est : (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis ESTI : est_img_tfa est.
Hypothesis ESTF : est_frame_tfa est.
Hypothesis FWS : fwrite_site_tfa B est.
Hypothesis RFS : refused_site_tfa B est.
Hypothesis FPO : fprintf_s_site_tfa B est 0x1d605 (strB "cli: cannot open "%string) nlB.
Hypothesis FPR : fprintf_s_site_tfa B est 0x1d61a (strB "cli: read error on "%string) nlB.
Hypothesis FPU : fprintf_s_site_tfa B est 0x157df (strB "usage: "%string) (strB " INPUT"%string ++ nlB).
Hypothesis EXS : forall fx : YK11.FPState, P fx -> exit_site_tfa (fx := fx) B est xst.
Theorem tfib_srealizesXP : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk mb rdraw YA02.LIMIT inp) (SPECX inp).
Proof.
exact (tfib_srealizesX_of_main (tfib_drv_main P P0 B HB AMALLOC AFREE AICPY ARDCHK MT XM_LIB XN_LIB RLO RHI MT_FREE RO_IN LIBX P_FRM
xst XFR PF1 PFN est ESTI ESTF FWS RFS FPO FPR FPU EXS)).
Qed.
End dP.
(* The closed walk at cgif's exists-fx' slot (ACfn.v tfib_lib_contract_xf_all): P is a zero rounding mode, which
   holds at YK11.fx0 (YK0o.v fp_frm_zero_fx0). *)
Section dF.
Variable B : asyms.
Hypothesis HB : OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.AF0m.BoxregSyms B.
Hypothesis AMALLOC : amalloc_realizes tfibsegs B.
Hypothesis AFREE : forall fx : YK11.FPState, frm_zero (@fp_csr fx) -> afree_realizes (fx := fx) tfibsegs B.
Hypothesis AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Hypothesis ARDCHK : aread_check_stmt B.
Variables (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z).
Hypothesis MT_FREE : forall S m, mo_ok MT S m.
Hypothesis RO_IN : forall a, RLO <= a < RHI -> in_ro_tfa a.
Hypothesis LIBX : tfib_lib_contract_xf_all B MT XM_LIB XN_LIB RLO RHI.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis XFR : xst_frame_tfa xst.
Hypothesis PF1 : forall fx : YK11.FPState, frm_zero (@fp_csr fx) -> printf_first_tfa (fx := fx) B xst.
Hypothesis PFN : forall fx : YK11.FPState, frm_zero (@fp_csr fx) -> printf_next_tfa (fx := fx) B xst.
Variable est : (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis ESTI : est_img_tfa est.
Hypothesis ESTF : est_frame_tfa est.
Hypothesis FWS : fwrite_site_tfa B est.
Hypothesis RFS : refused_site_tfa B est.
Hypothesis FPO : fprintf_s_site_tfa B est 0x1d605 (strB "cli: cannot open "%string) nlB.
Hypothesis FPR : fprintf_s_site_tfa B est 0x1d61a (strB "cli: read error on "%string) nlB.
Hypothesis FPU : fprintf_s_site_tfa B est 0x157df (strB "usage: "%string) (strB " INPUT"%string ++ nlB).
Hypothesis EXS : forall fx : YK11.FPState, frm_zero (@fp_csr fx) -> exit_site_tfa (fx := fx) B est xst.
Theorem tfib_srealizesXF : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk mb rdraw YA02.LIMIT inp) (SPECX inp).
Proof.
exact (tfib_srealizesXP (fun fx : YK11.FPState => frm_zero (@fp_csr fx)) fp_frm_zero_fx0 B HB AMALLOC AFREE AICPY ARDCHK
MT XM_LIB XN_LIB RLO RHI MT_FREE RO_IN (fun fx Hz => tfib_lib_contract_xP_of_xf (fx := fx) B MT XM_LIB XN_LIB RLO RHI Hz (LIBX fx)) (fun fx Hz => Hz)
xst XFR PF1 PFN est ESTI ESTF FWS RFS FPO FPR FPU EXS).
Qed.
End dF.
(* The name the closing reads: the closed walk from boxreg's whole-run contract (ACfn.v tfib_lib_contract_x_all, the
   exists-fx' contract of BoxLibX.v / BoxBLibX.v), through tfib_lib_contract_xf_all_of_x_all and tfib_srealizesXF. Its
   after-call hypotheses are XF's (at every float state with a zero rounding mode), not pinned at YK11.fx0. *)
Section d.
Variable B : asyms.
Hypothesis HB : OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.AF0m.BoxregSyms B.
Hypothesis AMALLOC : amalloc_realizes tfibsegs B.
Hypothesis AFREE : forall fx : YK11.FPState, frm_zero (@fp_csr fx) -> afree_realizes (fx := fx) tfibsegs B.
Hypothesis AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Hypothesis ARDCHK : aread_check_stmt B.
Variables (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z).
Hypothesis MT_FREE : forall S m, mo_ok MT S m.
Hypothesis RO_IN : forall a, RLO <= a < RHI -> in_ro_tfa a.
Hypothesis LIBX : tfib_lib_contract_x_all B MT XM_LIB XN_LIB RLO RHI.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis XFR : xst_frame_tfa xst.
Hypothesis PF1 : forall fx : YK11.FPState, frm_zero (@fp_csr fx) -> printf_first_tfa (fx := fx) B xst.
Hypothesis PFN : forall fx : YK11.FPState, frm_zero (@fp_csr fx) -> printf_next_tfa (fx := fx) B xst.
Variable est : (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis ESTI : est_img_tfa est.
Hypothesis ESTF : est_frame_tfa est.
Hypothesis FWS : fwrite_site_tfa B est.
Hypothesis RFS : refused_site_tfa B est.
Hypothesis FPO : fprintf_s_site_tfa B est 0x1d605 (strB "cli: cannot open "%string) nlB.
Hypothesis FPR : fprintf_s_site_tfa B est 0x1d61a (strB "cli: read error on "%string) nlB.
Hypothesis FPU : fprintf_s_site_tfa B est 0x157df (strB "usage: "%string) (strB " INPUT"%string ++ nlB).
Hypothesis EXS : forall fx : YK11.FPState, frm_zero (@fp_csr fx) -> exit_site_tfa (fx := fx) B est xst.
Theorem tfib_srealizesX : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk mb rdraw YA02.LIMIT inp) (SPECX inp).
Proof.
exact (tfib_srealizesXF B HB AMALLOC AFREE AICPY ARDCHK MT XM_LIB XN_LIB RLO RHI MT_FREE RO_IN
(tfib_lib_contract_xf_all_of_x_all B MT XM_LIB XN_LIB RLO RHI LIBX)
xst XFR PF1 PFN est ESTI ESTF FWS RFS FPO FPR FPU EXS).
Qed.
End d.
End b.
