(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AD2o.v (tfib_srealizesX_rc, tfib_srealizesX_top, TFIB_T_of_partsXF) and the XL0 of its A/ACfi.v for plugin-hostd/fuzz_command, in the form of libreac/fuzz_grant's lib/A/AGrantT.v and lib/A/GrantTop.v: TFIB_T of lib/A/CmdTFIB.v from one hypothesis on the program, the contract tfib_lib_contract_x_all of lib/A/ACfn.v (fuzz_command's call index and GI_cmdA) at every run ceiling and call index, instead of cgif's three library-function contracts; the allocator laws, the allocator and interceptor contracts and the driver's sites are discharged as AD2o.v discharges them, on fuzz_command's ASan image; the start-up certificate classes of lib/A/CmdStartCert.v and the module destructor's contract (class DtorExit of lib/A/AE37.v) are Section hypotheses (with the certificate checks' classes of AD1g.v, AD2i.v, AD1d.v, AD1f.v, AD2k.v and the a_vis alignment check class TfibAvis8 of CmdWorldH8.v); the driver's free, printf and exit sites are discharged at every float state; the plain build's sink instances are removed as GrantTop.v removes them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/CmdTFIBLib.v (origin/ossv/recipes 501c0d516c69) for reac-pw/fuzz_segconf's image B (fuzz_segconf.asan-ubsan) as lib/B/SegTFIBBLib.v, in the form of image A's lib/A/SegTFIBLib.v (commit 2fe2ad08d169): module paths (lib.A to lib.B); Cmd*/cmd_* -> Seg*/seg_*; TFIB_T -> lib/B/SegTFIBB.v TFIB_T_B; the start-up certificate classes are not taken, the core's de-classed lib/B/YD1q.v takes the generated start-up (lib/B/YB01.v, YB1n.v) in their place; the module destructor's contract is lib/B/Rt/RtDtorExit.v's instance cmd_dtor_exit; the driver's three fprintf literals at fuzz_segconf.asan-ubsan's addresses (0x1d8d2, 0x1d8e7, 0x15977, as lib/B/YD1l.v). *)
(* C2 of image B's top chain (fuzz_command's lib/B/CmdTFIBBLib.v role): TFIB_T_B (lib/B/SegTFIBB.v) from one
   hypothesis on the program, LIBX (C3, lib/B/Prog/SegLibX.v), through the driver theorem of the core's de-classed
   lib/B/YD1q.v tfib_srealizesX, with the allocator, interceptor and driver-site premises discharged by image B's core
   files. proves no function (kind: merge; the driver and the start-up over the program contract). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_pw.fuzz_segconf.images Require Import AsanUbsan.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK15 YK18 YA02.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1h.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG01 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YG0q YC5d YCbp.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YCfn YB1v YF0m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YF0p.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YD2l YCeg YD1v YD1w YD1x YD1i YD1k YD1l YD1o YD1j YD2m
  YF0w YF0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YE2k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YE37 YD1q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import SegShape.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import SegTFIBB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtDtorExit.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YI5b YI5c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance seg_shape.
Open Scope Z_scope.
(* The guard: the plain build's sink hints (lib/Reusable/YI5b.v src0_sink_head and lib/Reusable/YI5c.v src0_sink,
   both global instances) are out of the way, so no sink argument of this file can be filled with the plain build's
   head: a bare `sink_head` is image B's own head (lib/B/YE2k.v), as `sk_probe_is_asan_ubsan` shows. *)
#[local] Remove Hints OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
#[local] Remove Hints OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable.YI5c.src0_sink : typeclass_instances.
Definition sk_probe : OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable.YI16.sink_head := _.
Lemma sk_probe_is_asan_ubsan : sk_probe = YE2k.tfib_sink_head.
Proof. reflexivity. Qed.
(* the core YD1q's local shape is the close's seg_shape, the shape the plain side's lib/AgreeSeg.v
   plain_slot_ag is stated at *)
Lemma seg_ag_sil_shape_eq : YD1q.seg_ag_sil_shape = seg_shape.
Proof. reflexivity. Qed.
(* The meter the program contract carries: it counts nothing (cgif_file's XL0). *)
Definition XL0 : Z -> Z := fun _ => 0.
Lemma valid_sp_windowX : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.
Section b.
Let B : asyms := SegB.
Let HB : SegBSyms B := SegB_syms.
Let HD : forall t, as_dhash B t = tfib_dhash t := fun t => eq_refl.
(* What the program side owes (C3, lib/B/Prog/SegLibX.v): one call of LLVMFuzzerTestOneInput (lib/B/YCfn.v A_LLVMF)
   keeps the memory-checking state, returns 0, writes nothing, leaves the caller's input bytes as it found them and
   carries segconf's global invariant GI_segA from call j to call j + 1 (lib/B/YCfn.v tfib_lib_contract_x_all), at every
   run ceiling and call index, over the read-only range SEG_RLO..SEG_RHI (lib/B/Prog/SegGlob.v: .data.rel.ro and .got,
   lib/B/YCeg.v in_ro_tfa's second part). *)
Hypothesis LIBX : forall (rc : YM05.RunCeil) (j : nat),
@tfib_lib_contract_x_all rc seg_shape SegB ameter_triv XL0 XL0 SEG_RLO SEG_RHI GI_segA j.
Section RC. Context {rc : YM05.RunCeil}.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let AMALLOC : amalloc_realizes tfibsegs B := tfib_amalloc_realizes B HB HD.
(* The free, printf and exit sites are reached after a program call too, at the float state the call returned with:
   each is discharged at every float state by the same lemma. *)
Let AFREE : forall fy : YK11.FPState, afree_realizes (fx := fy) tfibsegs B := fun fy => afree_realizes_closed (fx := fy) B HB HD.
Let AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)) := tfib_AICPY B HB.
Let RO_IN : forall a, SEG_RLO <= a < SEG_RHI -> in_ro_tfa a := fun a H => or_intror H.
Let ARDCHK : aread_check_stmt B := tfib_ARDCHK B HB.
Let MT_FREE : forall S m, mo_ok ameter_triv S m := fun _ _ => I.
Let xst : nat -> (word -> bool) -> (word -> option byte) -> Prop := YD1k.xst.
Let XFR : xst_frame_tfa xst := tfib_xst_frame.
Let PF1 : forall fy : YK11.FPState, printf_first_tfa (fx := fy) B xst := fun fy => tfib_printf_first (fx := fy) B HB (AR_laws_ok tfibsegs B) HB.
Let PFN : forall fy : YK11.FPState, printf_next_tfa (fx := fy) B xst := fun fy => tfib_printf_next (fx := fy) B HB (AR_laws_ok tfibsegs B) HB.
Let est : (word -> bool) -> (word -> option byte) -> Prop := YD1k.est.
Let ESTI : est_img_tfa est := tfib_est_img.
Let ESTF : est_frame_tfa est := tfib_est_frame.
Let FWS : fwrite_site_tfa B est := tfib_fwrite_site B HB LAWS.
Let RFS : refused_site_tfa B est := tfib_refused_site B HB LAWS HB.
Let FPO : fprintf_s_site_tfa B est 0x1d8d2 (strB "cli: cannot open "%string) nlB := tfib_fprintf_open_site B HB LAWS HB.
Let FPR : fprintf_s_site_tfa B est 0x1d8e7 (strB "cli: read error on "%string) nlB := tfib_fprintf_rderr_site B HB LAWS HB.
Let FPU : fprintf_s_site_tfa B est 0x15977 (strB "usage: "%string) (strB " INPUT"%string ++ nlB) := tfib_fprintf_usage_site B HB LAWS HB.
Let EXS : forall fy : YK11.FPState, exit_site_tfa (fx := fy) B est xst :=
  fun fy => tfib_exit_site (fx := fy) (DE := RtDtorExit.cmd_dtor_exit) B HB (AR_laws_ok tfibsegs B).
Lemma seg_srealizesX_rc : forall sp rdraw brk mb inp,
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk mb rdraw target_alloc_limit inp) (SPECX inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil.
change target_alloc_limit with YA02.LIMIT.
exact (tfib_srealizesX B HB AMALLOC AFREE AICPY ARDCHK ameter_triv XL0 XL0 SEG_RLO SEG_RHI MT_FREE RO_IN (LIBX rc) xst XFR
PF1 PFN est ESTI ESTF FWS RFS FPO FPR FPU EXS sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil).
Qed.
End RC.
Theorem seg_srealizesX_top : forall sp rdraw brk mb inp,
valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk mb rdraw target_alloc_limit inp) (SPECX inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp.
exact (@seg_srealizesX_rc (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowX sp Hsp) YA02.LIMIT) sp rdraw brk mb inp Hsp
  Hbrk Hmb Hfit Hinp (YM05.ceil_of_top_run _)).
Qed.
(* Shared contract C2: the driver and the start-up over the program contract. *)
Theorem seg_TFIB_T_B_of_lib : TFIB_T_B.
Proof. intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp. exact (seg_srealizesX_top sp rnd brk mbase inp Hsp Hbrk Hmb Hfit Hinp). Qed.
End b.
Print Assumptions seg_TFIB_T_B_of_lib.
