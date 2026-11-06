(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/libreac/fuzz_grant/lib/A/AGrantT.v (a working branch
   7d31e8f3534; itself from proofs/cgif/cgif_file_fuzzer/lib/A/AD2o.v) for libreac/fuzz_disco's ASan build: module paths
   changed, B := AD2l.TfibB, the library shape DiscoAsanTop.disco_shape (= Reusable/DiscoShape.v disco_lib_shape, the
   same term), the read-only range lib/A/Prog/DiscoImg.v disco_relro_lo / disco_relro_hi, the floating-point state
   quantified across the driver's calls where lib/A/AD1q.v quantifies it (AFREE, PF1, PFN, EXS), and the program
   contract taken with the read-only facts its walks use (H_RO) as its antecedent. *)
(* The lower closing file of fuzz_disco's ASan build (rule 24: no function proved; this file is assembly).
   Every input of lib/A/AD1q.v tfib_srealizesX except the program contract is a proved lemma of the landed core
   (a working branch f0d1f4eacff), plugged in below as a Let: the start-up (AB1n tfib_startup_T1 over AB01 HS_tfib
   and AB12 TFIB, used inside tfib_srealizesX), the symbol table (AD2l TfibB / TfibB_syms), both allocator realizes
   (AF0w, AF0q), the memcpy interceptor and the read check (AD2m), and the driver's stdio sites (AD1k, AD1o, AD1l,
   AD1j). The Section hypotheses are ONLY the program contract LIBX_ALL (lib/A/Prog/DiscoLibX.v disco_lib_x_all,
   a Theorem Labs lane) and the read-only facts H_RO it takes, until the part discharges them itself. lib/A/AD2p.v closes the
   two statements from TFIB_T_of_lib. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_disco.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK15 YK18 YK0c YK0e YK09 YA0c YA0e YA01 YA02.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import AB12 AB1h AB01 AB1n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0f YG00 YG01 YG0n YG0d YG0q YK04 YA0i YA0n YCbq YI16 YC5d YCbp YF0p.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YO05 YO09 YO06 YO01 DiscoShape YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import AB1v AF0m ACeg ACfn AD1v AD1w AD1x AD1i AD1p.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import AD2l AD2m AF0w AF0q AD1k AD1l AD1o AD1j AD1q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require DiscoImg DiscoRo DiscoRoList.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require DiscoAsanTop AZ03.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance disco_lib_shape.

Local Notation LS := DiscoAsanTop.disco_shape.
Local Notation segs := OSSVerify.libreac.fuzz_disco.images.Asan.M.loaded_segments.

(* donor lib/A/AD2o.v:27-28 (fuzz_grant AGrantT.v:32-33). *)
Lemma valid_sp_windowX : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.

(* The read-only facts the part's walks take (row A9 of proofs/libreac/fuzz_disco/lib/A/OBLIGATIONS.md at a working branch 37e11e67676d), a Theorem Labs lane's
   lib/A/Prog/DiscoEntBodyStmt.v:72 d_ro_hyps at TfibB and the asan image: the read-only ranges the walks READ hold
   no owned static and no errno byte (DiscoRo.disco_ro_unowned), the registered globals are marked in the shadow
   (globs_marked) and the image's shadow is mapped (img_shadow_vis). It replaces the ROSTAT form
   `forall a, in_rom segs a -> ~ owned /\ ~ errno`, which is FALSE for fuzz_disco (owned-static redzone entries lie in
   .rodata, e.g. 0x20f9e in (0x20f9e, 0x22), AF0m.v:1401; a Theorem Labs lane 2026-10-29T03:04Z). Closed at TfibB by a Theorem Labs lane's
   lib/A/Prog/DiscoRoClose.v (disco_ro_unowned_tfib, disco_globs_marked, disco_img_shadow_vis), by computation. *)
Definition H_RO_stmt (rc : YM05.RunCeil) : Prop :=
  DiscoRo.disco_ro_unowned TfibB
  /\ DiscoRo.globs_marked (rc := rc) segs TfibB DiscoRoList.disco_globs
  /\ DiscoRo.img_shadow_vis (rc := rc) segs TfibB.

Section b.
Let B : asyms := TfibB.
Let HB : TfibSyms B := TfibB_syms.
Let HD : forall t, as_dhash B t = tfib_dhash t := fun t => eq_refl.
(* The read-only facts of the part's walks, as above; the part takes them until it discharges them itself. *)
Hypothesis H_RO : forall rc : YM05.RunCeil, H_RO_stmt rc.
(* What the program side owes (donor lib/A/AD1q.v:39 LIBX, lib/A/ACfn.v tfib_lib_contract_x_all): one call of
   LLVMFuzzerTestOneInput keeps the ASan state, returns 0, writes nothing and leaves the caller's input bytes as it
   found them, at the donor's XL0 (fun _ => 0), ameter_triv and fuzz_disco's relro range. Owner: lib/A/Prog/DiscoLibX.v
   disco_lib_x_all (a Theorem Labs lane). *)
Hypothesis LIBX_ALL : forall rc : YM05.RunCeil, H_RO_stmt rc ->
  @tfib_lib_contract_x_all rc LS TfibB ameter_triv (fun _ => 0) (fun _ => 0)
    DiscoImg.disco_relro_lo DiscoImg.disco_relro_hi.
Section RC. Context {rc : YM05.RunCeil}.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let AMALLOC : amalloc_realizes tfibsegs B := tfib_amalloc_realizes B HB HD.
Let AFREE : forall fq : YK11.FPState, afree_realizes (fx := fq) tfibsegs B :=
  fun fq => afree_realizes_closed (fx := fq) B HB HD.
Let AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)) := tfib_AICPY B HB.
Let ARDCHK : aread_check_stmt B := tfib_ARDCHK B HB.
Let MT_FREE : forall S m, mo_ok ameter_triv S m := fun _ _ => I.
Let RO_IN : forall a, DiscoImg.disco_relro_lo <= a < DiscoImg.disco_relro_hi -> in_ro_tfa a := fun a H => or_intror H.
Let LIBX : tfib_lib_contract_x_all B ameter_triv (fun _ => 0) (fun _ => 0)
    DiscoImg.disco_relro_lo DiscoImg.disco_relro_hi := LIBX_ALL rc (H_RO rc).
Let xst : nat -> (word -> bool) -> (word -> option byte) -> Prop := AD1k.xst.
Let XFR : xst_frame_tfa xst := tfib_xst_frame.
Let PF1 : forall fq : YK11.FPState, printf_first_tfa (fx := fq) B xst :=
  fun fq => tfib_printf_first (fx := fq) B HB (AR_laws_ok tfibsegs B) HB.
Let PFN : forall fq : YK11.FPState, printf_next_tfa (fx := fq) B xst :=
  fun fq => tfib_printf_next (fx := fq) B HB (AR_laws_ok tfibsegs B) HB.
Let est : (word -> bool) -> (word -> option byte) -> Prop := AD1k.est.
Let ESTI : est_img_tfa est := tfib_est_img.
Let ESTF : est_frame_tfa est := tfib_est_frame.
Let FWS : fwrite_site_tfa B est := tfib_fwrite_site B HB LAWS.
Let RFS : refused_site_tfa B est := tfib_refused_site B HB LAWS HB.
Let FPO : fprintf_s_site_tfa B est 0x1d860 (strB "cli: cannot open "%string) nlB :=
  tfib_fprintf_open_site B HB LAWS HB.
Let FPR : fprintf_s_site_tfa B est 0x1d875 (strB "cli: read error on "%string) nlB :=
  tfib_fprintf_rderr_site B HB LAWS HB.
Let FPU : fprintf_s_site_tfa B est 0x1583b (strB "usage: "%string) (strB " INPUT"%string ++ nlB) :=
  tfib_fprintf_usage_site B HB LAWS HB.
Let EXS : forall fq : YK11.FPState, exit_site_tfa (fx := fq) B est xst :=
  fun fq => tfib_exit_site (fx := fq) B HB (AR_laws_ok tfibsegs B).
(* donor lib/A/AD2o.v:63-84 (fuzz_grant AGrantT.v:63-73): lib/A/AD1q.v:68 tfib_srealizesX over the Lets above. *)
Lemma disco_srealizesX_rc : forall sp rdraw brk mb inp,
  valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk mb rdraw target_alloc_limit inp) (SPECX (LS:=LS) inp).
Proof.
  intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil.
  change target_alloc_limit with YA02.LIMIT.
  exact (tfib_srealizesX B HB AMALLOC AFREE AICPY ARDCHK ameter_triv (fun _ => 0) (fun _ => 0)
    DiscoImg.disco_relro_lo DiscoImg.disco_relro_hi MT_FREE RO_IN LIBX xst XFR PF1 PFN est ESTI ESTF FWS RFS FPO FPR FPU EXS
    sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil).
Qed.
End RC.
(* donor lib/A/AD2o.v:75-84 tfib_srealizesX_top (fuzz_grant AGrantT.v:75-82): the run's ceiling taken at the stack pointer. *)
Theorem disco_srealizesX_top : forall sp rdraw brk mb inp,
  valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  srealizes TSEGS (init_config TSEGS Asan.M.init_pc TPH sp brk mb rdraw target_alloc_limit inp) (SPECX (LS:=LS) inp).
Proof.
  intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp.
  exact (@disco_srealizesX_rc (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowX sp Hsp)) sp rdraw brk mb inp
    Hsp Hbrk Hmb Hfit Hinp (YM05.ceil_of_top_run _)).
Qed.
(* donor lib/A/AD2o.v:75-84 TFIB_T_of_partsXF (fuzz_grant AGrantT.v:83-84); AZ03.TFIB_T is DiscoAsanTop.ASAN_T. *)
Theorem TFIB_T_of_lib : AZ03.TFIB_T.
Proof.
  intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp.
  exact (disco_srealizesX_top sp rnd brk mbase inp Hsp Hbrk Hmb Hfit Hinp).
Qed.
End b.
