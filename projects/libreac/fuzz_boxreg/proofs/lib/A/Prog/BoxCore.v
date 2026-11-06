(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AD2o.v (TFIB_T_of_partsXF,
   origin/ossv/recipes c8557374ad2) in the form of libreac/fuzz_grant's lib/A/AGrantT.v (a working branch), for
   libreac/fuzz_boxreg's ASan build (fuzz_boxreg.asan): module paths changed, TfibSyms -> BoxregSyms, the program's
   whole-run contract taken as one hypothesis, fuzz_boxreg.asan's read-only range and fprintf strings, and the
   after-call parts given at every float state with a zero rounding mode (the relocated core's lib/A/AD1q.v
   tfib_srealizesX, fx-slot form). *)
(* The relocated core's closed walk of fuzz_boxreg.asan at the image's asyms record (rule 24: no function proved;
   this file is assembly). box_TFIB_T_of_lib is lib/A/Prog/BoxClose.v's coreA_srz: from the whole-run contract of
   LLVMFuzzerTestOneInput (lib/A/ACfn.v tfib_lib_contract_x_all, the instance of lib/A/Prog/BoxLibX.v's statement with
   SINKN := YE00.asink_none box_segs tfib_K and METAI := YE01.ameta_inv box_segs tfib_K) to TFIB_T (lib/A/BoxTFIB.v).
   Each premise of AD1q.v:198 tfib_srealizesX other than that contract is a landed core lemma at TfibB
   (lib/A/AD2l.v:33 / :95):
   - AMALLOC lib/A/AF0w.v:45 tfib_amalloc_realizes; AFREE lib/A/AF0q.v:13 afree_realizes_closed;
   - AICPY / ARDCHK lib/A/AD2m.v:17 / :22 tfib_AICPY / tfib_ARDCHK;
   - MT := YCbp.v:17 ameter_triv (its mo_ok is True); RO_IN: [0x98958, 0x99bb0) is the second disjunct of
     lib/A/ACeg.v:60 in_ro_tfa (BoxClose.v's BOX_RLO / BOX_RHI; XM_LIB = XN_LIB = BoxClose.v's BXL0);
   - xst / est and their frame laws lib/A/AD1k.v:133 / :114 / :116; the fwrite / refused sites AD1k.v:275 / :316;
     the printf sites lib/A/AD1o.v:245 / :281; the three fprintf sites lib/A/AD1l.v:147 / :152 / :157 (strings
     0x1d605 / 0x1d61a / 0x157df, as AD1q.v:29-32 measures them); the exit site lib/A/AD1j.v:124.
   The run ceiling comes from the start's sp (lib/ZComplete.v:45 valid_sp_window_for_ceil, YM05.v:48 RunCeilOf). *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_boxreg.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK15 YK18 YA02 YK0o.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require Import AB1h.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG0f YG00 YG01 YG0n YG0d YG05 YG0q YI16 YC5d YCbp.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require Import ACfn AB1v AF0m.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YF0p.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require Import
AD2l ACeg AD1v AD1w AD1x AD1i AD1k AD1l AD1o AD1j AD2m AF0w AF0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require Import AD1q BoxShape BoxTFIB.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require ZComplete.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance box_shape.
Open Scope Z_scope.

Section b.
Let B : asyms := TfibB.
Let HB : BoxregSyms B := TfibB_syms.
Let HD : forall t, as_dhash B t = tfib_dhash t := fun t => eq_refl.
(* What the program side owes: LLVMFuzzerTestOneInput's whole-run contract at every run ceiling (BoxClose.v's
   coreA_srz premise, at its instance). *)
Hypothesis LIBX_ALL : forall rc : YM05.RunCeil,
  @tfib_lib_contract_x_all rc box_shape TfibB ameter_triv (fun _ => 0) (fun _ => 0) 0x98958 0x99bb0.
Section RC. Context {rc : YM05.RunCeil}.
Let AMALLOC : amalloc_realizes tfibsegs B := tfib_amalloc_realizes B HB HD.
Let AFREE : forall fx : YK11.FPState, frm_zero (@fp_csr fx) -> afree_realizes (fx := fx) tfibsegs B :=
  fun fx _ => afree_realizes_closed (fx := fx) B HB HD.
Let AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)) := tfib_AICPY B HB.
Let ARDCHK : aread_check_stmt B := tfib_ARDCHK B HB.
Let MT_FREE : forall S m, mo_ok ameter_triv S m := fun _ _ => I.
Let RO_IN : forall a, 0x98958 <= a < 0x99bb0 -> in_ro_tfa a := fun a H => or_intror H.
Let LIBX : tfib_lib_contract_x_all TfibB ameter_triv (fun _ => 0) (fun _ => 0) 0x98958 0x99bb0 := LIBX_ALL rc.
Let xst : nat -> (word -> bool) -> (word -> option byte) -> Prop := AD1k.xst.
Let XFR : xst_frame_tfa xst := tfib_xst_frame.
Let PF1 : forall fx : YK11.FPState, frm_zero (@fp_csr fx) -> printf_first_tfa (fx := fx) B xst :=
  fun fx _ => tfib_printf_first (fx := fx) B HB (AR_laws_ok tfibsegs B) HB.
Let PFN : forall fx : YK11.FPState, frm_zero (@fp_csr fx) -> printf_next_tfa (fx := fx) B xst :=
  fun fx _ => tfib_printf_next (fx := fx) B HB (AR_laws_ok tfibsegs B) HB.
Let est : (word -> bool) -> (word -> option byte) -> Prop := AD1k.est.
Let ESTI : est_img_tfa est := tfib_est_img.
Let ESTF : est_frame_tfa est := tfib_est_frame.
Let FWS : fwrite_site_tfa B est := tfib_fwrite_site B HB (AR_laws_ok tfibsegs B).
Let RFS : refused_site_tfa B est := tfib_refused_site B HB (AR_laws_ok tfibsegs B) HB.
Let FPO : fprintf_s_site_tfa B est 0x1d605 (strB "cli: cannot open "%string) nlB :=
  tfib_fprintf_open_site B HB (AR_laws_ok tfibsegs B) HB.
Let FPR : fprintf_s_site_tfa B est 0x1d61a (strB "cli: read error on "%string) nlB :=
  tfib_fprintf_rderr_site B HB (AR_laws_ok tfibsegs B) HB.
Let FPU : fprintf_s_site_tfa B est 0x157df (strB "usage: "%string) (strB " INPUT"%string ++ nlB) :=
  tfib_fprintf_usage_site B HB (AR_laws_ok tfibsegs B) HB.
Let EXS : forall fx : YK11.FPState, frm_zero (@fp_csr fx) -> exit_site_tfa (fx := fx) B est xst :=
  fun fx _ => tfib_exit_site (fx := fx) B HB (AR_laws_ok tfibsegs B).
Lemma box_srealizesX_rc : forall sp rdraw brk mb inp,
  valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk mb rdraw target_alloc_limit inp) (SPECX inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil.
change target_alloc_limit with YA02.LIMIT.
exact (tfib_srealizesX B HB AMALLOC AFREE AICPY ARDCHK ameter_triv (fun _ => 0) (fun _ => 0) 0x98958 0x99bb0 MT_FREE
  RO_IN LIBX xst XFR PF1 PFN est ESTI ESTF FWS RFS FPO FPR FPU EXS sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil).
Qed.
End RC.
Theorem box_TFIB_T_of_lib : TFIB_T.
Proof.
intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp.
exact (@box_srealizesX_rc (YM05.RunCeilOf (bv_unsigned sp) (ZComplete.valid_sp_window_for_ceil sp Hsp))
  sp rnd brk mbase inp Hsp Hbrk Hmb Hfit Hinp (YM05.ceil_of_top_run _)).
Qed.
End b.
