(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: made for reac-repacer/fuzz_uci's ASan image from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/A/DecodeClose.v (the closing form: one named Section hypothesis per open part, the parts proved elsewhere applied as Lemmas of the hypotheses' names and statements, the program contract LIB_CONTRACT from the entry walk and its callees, the two statements from AsanTop; its About / Print Assumptions commands are left out, because on this image's core those commands for the three tops take about 13 minutes per build) and libreac/fuzz_grant proofs/libreac/fuzz_grant/lib/A/AGrantT.v (the driver step: the core arguments of tfib_srealizesX, the run ceiling and TFIB_T), with the sink guard of fuzz_grant's lib/A/GrantTop.v; names GrantB -> UciB, the library shape fuzz_uci's checksum_shape, fuzz_uci's own program statements and rows; module paths changed. *)
(* WireCloseParts: every part of the composition of fuzz_wire's two ASan statements that is not a program walk, each a
   Lemma of the relocated core, the relocated runtime contracts or the kit, at B := WireB (lib/A/AD2l.v:16) and
   segs := wiresegs0 (lib/A/WireTFIB.v): the runtime contracts the program calls, the facts about B and the meter the
   walks take, the leaf-kit facts, and the driver step (wire_TFIB_T_of_lib): the core's lib/A/AD1q.v:172
   tfib_srealizesX over the program contract of the entry function, which lib/A/WireClose.v gives from the walks.
   The form is fuzz_uci's lib/A/UciClose.v sections 2-6 at fuzz_wire's names. This file proves no program function
   and takes no hypothesis. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YK15 YK18 YA02.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB1h.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YK04 YA0i YA0n YG0f YG00 YG01 YG0n YG0d YG05 YG0q YI16 YE00 YE01 YCbq YC5d YCbp.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YG0t.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import ACfn AB1v AF0m.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YF0p.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import
AD2l ACeg AD1v AD1w AD1x AD1i AD1k AD1l AD1o AD1j AD2m AF0w AF0q.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AE2k AD1u.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import ACej.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AD1q WireTFIB.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require AE2q AE2r AE2s.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import WirePSyms WirePAddr.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require PaBase WireCg WirePImg LeafCgKit LeafCgClose.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Rt Require MemmoveDef Memmove StackMalloc0 AF0s.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require WireAFacts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance checksum_shape.
Open Scope Z_scope.

Module PB := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.PaBase.
Module PCs := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.WireCg.
Module WImg := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.WirePImg.
Module LK := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.LeafCgKit.
Module LCl := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.LeafCgClose.
Module MD := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Rt.MemmoveDef.
Module WAF := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.WireAFacts.

(* The guard: the plain build's sink hints are out of the way, so no `{SK}` can be filled with the plain build's
   head. *)
#[local] Remove Hints YI5b.src0_sink_head : typeclass_instances.
#[local] Remove Hints YI5c.src0_sink : typeclass_instances.

(* What a bare `sink_head` resolves to in this file: the ASan image's own head. *)
Definition sk_probe : YI16.sink_head := _.
Lemma sk_probe_is_asan : sk_probe = AE2k.tfib_sink_head.
Proof. reflexivity. Qed.

(* The stack-pointer window, from valid_sp. *)
Lemma valid_sp_windowW : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.

(* The image's data the parts are stated at. *)
Local Abbreviation segs := wiresegs0.
Local Abbreviation B := AD2l.WireB.
Local Abbreviation MT := ameter_triv.
Local Abbreviation XL := WAF.wire_XL0.
Local Abbreviation RLO := WAF.WIRE_RLO.
Local Abbreviation RHI := WAF.WIRE_RHI.
Local Abbreviation SK := AE2k.tfib_sink_head.
Local Abbreviation KS := AE2k.tfib_K.

(* ===================================================================================================== *)
(* The runtime contracts the program calls                                                               *)
(* ===================================================================================================== *)
(* malloc / free: lib/A/AF0w.v:46 tfib_amalloc_realizes, lib/A/AF0q.v:14 afree_realizes_closed. *)
Lemma H_RT_MALLOC : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @amalloc_realizes fx rc segs B.
Proof. intros rc fx. exact (@AF0w.tfib_amalloc_realizes fx rc B WireB_syms (fun t => eq_refl)). Qed.
Lemma H_RT_FREE : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_realizes fx rc segs B.
Proof. intros rc fx. exact (@AF0q.afree_realizes_closed fx rc B WireB_syms (fun t => eq_refl)). Qed.
(* The memcpy interceptor the driver calls, lib/A/AD2m.v:18 tfib_AICPY. *)
Lemma H_RT_MEMCPY_WRAP : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc segs B OCpy (pc_wrap_memcpy (as_code B)).
Proof. intros rc fx. exact (AD2m.tfib_AICPY B WireB_syms). Qed.
(* __asan_memcpy (0x50c34), lib/A/AE2q.v:145 asan_memcpy_realizes; LLVMFuzzerTestOneInput and check_copy call it. *)
Lemma H_RT_ASAN_MEMCPY : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc segs B OCpy (wire_sigma WS___asan_memcpy).
Proof.
  intros rc fx. change (wire_sigma WS___asan_memcpy) with 0x50c34.
  intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull Hsrc.
  exact (AE2q.asan_memcpy_realizes B (AR_laws_ok tfibsegs B) WireB_syms
    ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull Hsrc).
Qed.
(* __asan_memset (0x510d0), lib/A/AE2r.v:568 asan_memset_realizes; check_read calls it. *)
Lemma H_RT_ASAN_MEMSET : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc segs B OSet (wire_sigma WS___asan_memset).
Proof.
  intros rc fx. change (wire_sigma WS___asan_memset) with 0x510d0.
  intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull _.
  exact (AE2r.asan_memset_realizes B (AR_laws_ok tfibsegs B) WireB_syms
    ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Hra Hhull Ham).
Qed.
(* __asan_memmove (0x51310), lib/A/Rt/Memmove.v:148 asan_memmove_contract; rp_copy_untag calls it. *)
Lemma H_RT_ASAN_MEMMOVE : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @MD.amemmove_realizes fx rc segs B (wire_sigma WS___asan_memmove).
Proof. intros rc fx. exact (@Memmove.asan_memmove_contract fx rc B (AR_laws_ok tfibsegs B) WireB_syms). Qed.
(* The bcmp interceptor (0x4157c), lib/A/AE2s.v:712 bcmp_icpt_contract; check_copy calls it. *)
Lemma H_RT_BCMP : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @abcmp_realizes fx rc segs B (wire_sigma WS___interceptor_trampoline_bcmp).
Proof. intros rc fx. exact (@AE2s.bcmp_icpt_contract fx rc B (AR_laws_ok tfibsegs B) WireB_syms). Qed.
(* The fake stack of classes 0 (check_meter, a0 = 0x40 at +0x6c) and 1 (check_read, a0 = 0x80 at +0x74): the
   relocated runtime contracts lib/A/Rt/StackMalloc0.v stack_malloc0_contract and lib/A/Rt/AF0s.v
   stack_malloc1_contract at WireB. *)
Lemma H_RT_STACK_MALLOC0 : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @astack_malloc_realizes fx rc segs B 0.
Proof. intros rc fx. exact (@StackMalloc0.stack_malloc0_contract fx rc B (AR_laws_ok tfibsegs B) WireB_syms). Qed.
Lemma H_RT_STACK_MALLOC1 : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @astack_malloc_realizes fx rc segs B 1.
Proof. intros rc fx. exact (@AF0s.stack_malloc1_contract fx rc B (AR_laws_ok tfibsegs B) WireB_syms). Qed.

(* The record's code addresses are the listing's: 0x522f8 / 0x522f4 / 0x3c544 / 0x3c6b8 (lib/A/AF0l.v Tfib_code). *)
Lemma HB_PC_WRAP_MALLOC : pc_wrap_malloc (as_code B) = wire_sigma WS___interceptor_trampoline_malloc.
Proof. reflexivity. Qed.
Lemma HB_PC_WRAP_FREE : pc_wrap_free (as_code B) = wire_sigma WS___interceptor_trampoline_free.
Proof. reflexivity. Qed.
Lemma HB_PC_STACK_MALLOC0 : pc_stack_malloc (as_code B) 0 = wire_sigma WS___asan_stack_malloc_0.
Proof. reflexivity. Qed.
Lemma HB_PC_STACK_MALLOC1 : pc_stack_malloc (as_code B) 1 = wire_sigma WS___asan_stack_malloc_1.
Proof. reflexivity. Qed.

(* ===================================================================================================== *)
(* The facts about B, the meter and the fake stack                                                       *)
(* ===================================================================================================== *)
(* lib/A/AF0m.v ts_universe at WireB_syms; Reusable/YG05.v model_laws_ok. *)
Lemma HB_UNIVERSE_OK : universe_ok (as_universe B).
Proof. exact (ts_universe B WireB_syms). Qed.
Lemma HB_MODEL_LAWS : model_laws (as_universe B).
Proof. exact (model_laws_ok (as_universe B) HB_UNIVERSE_OK). Qed.
(* Reusable/YCbp.v ameter_triv_laws, ameter_triv_fs_laws. *)
Lemma HB_METER_LAWS : ameter_laws MT.
Proof. exact ameter_triv_laws. Qed.
Lemma HB_METER_FS_LAWS : ameter_fs_laws MT.
Proof. exact ameter_triv_fs_laws. Qed.
(* Reusable/YG05.v stack_malloc_progress, Reusable/YG0t.v astack_free_law_ok, and AR_laws' al_flag /
   al_client_img with the image cover lib/A/ACeg.v tfib_img_cover. *)
Lemma HB_SMP : stack_malloc_progressP B.
Proof. intros s cid W Hc Hn. exact (stack_malloc_progress (as_universe B) s cid W Hc Hn). Qed.
Lemma HB_ASF : forall (rc : YM05.RunCeil), astack_free_law segs B.
Proof. intros rc. exact (YG0t.astack_free_law_ok (rc := rc) segs B). Qed.
Lemma HB_FFL : forall (rc : YM05.RunCeil), frame_flag_lawP segs B.
Proof.
  intros rc ly S W mem md cid pos HAR Hin.
  pose proof (AR_laws_ok segs B) as LAWS.
  destruct (al_flag _ _ LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
  destruct (al_client_img _ _ LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
  { right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
  pose proof HAR as (M & L & _). pose proof (ACeg.tfib_img_cover ly S md L) as [C1 C2].
  unfold ACeg.TFIB_IMG_LO, ACeg.TFIB_IMG_END in C1, C2.
  destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
  split; [exact Hp|]. split; [exact Ho|]. split.
  - split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
  - split; [exact H4096|]. split; [|exact Hceil]. unfold zone2, off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
(* The core's sink record laws, lib/A/AD1u.v:44 tfib_AIL, and Reusable/YE01.v asink_none_kept / ameta_inv_kept
   specialised to one journal step. *)
Lemma HB_SINK_IMG_LAWS : @asink_img_laws SK segs B KS.
Proof. apply AD1u.tfib_AIL; first [exact WireB_syms | apply AR_laws_ok]. Qed.
Lemma HB_SINK_KEPT : forall (rc : YM05.RunCeil),
  forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k,
    @ajournal rc SK segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
    ~ YI16.sink_open_fp FP ->
    asink_none segs KS (mrestrict (w_H W0) mem0) md0 -> asink_none segs KS (mrestrict (w_H W') mem') md'.
Proof.
  intros rc STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ Hc HS.
  exact (asink_none_kept (rc := rc) (SK := SK) segs B KS HB_SINK_IMG_LAWS
    STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ Hc HS).
Qed.
Lemma HB_META_KEPT : forall (rc : YM05.RunCeil),
  forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k M,
    @ajournal rc SK segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
    ameta_inv segs KS ly (mrestrict (w_H W0) mem0) M -> ameta_inv segs KS ly' (mrestrict (w_H W') mem') M.
Proof.
  intros rc STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k M HJ HM.
  exact (ameta_inv_kept (rc := rc) (SK := SK) segs B KS HB_SINK_IMG_LAWS
    STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k M HJ HM).
Qed.
(* The call-rule form the walks consume, Reusable/YCbp.v amalloc04_rule_triv / afree04_rule_triv, at the image's
   segments (lib/A/Prog/WirePImg.v wire_segs_low), the record's api_env (lib/A/WireAFacts.v), AR_laws_ok and
   HB_MODEL_LAWS. *)
Lemma H_LINK_MALLOC04 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @amalloc04_rule fx rc SK segs B MT.
Proof.
  intros rc fx. apply (amalloc04_rule_triv (SK := SK) segs B).
  - exact WImg.wire_segs_low.
  - exact WAF.wire_api_env_WireB.
  - apply AR_laws_ok.
  - exact HB_MODEL_LAWS.
  - exact (H_RT_MALLOC rc fx).
Qed.
Lemma H_LINK_FREE04 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @afree04_rule fx rc SK segs B MT.
Proof.
  intros rc fx. apply (afree04_rule_triv (SK := SK) segs B).
  - exact WImg.wire_segs_low.
  - exact WAF.wire_api_env_WireB.
  - apply AR_laws_ok.
  - exact HB_MODEL_LAWS.
  - exact (H_RT_FREE rc fx).
Qed.

(* ===================================================================================================== *)
(* The leaf-kit facts (lib/A/Prog/LeafCgClose.v)                                                         *)
(* ===================================================================================================== *)
Lemma H_KIT_AVIEW_EXT : @LK.aview_ext_stmt (aview segs).
Proof. exact LCl.wire_a_kit_aview_ext. Qed.
Lemma H_KIT_AVIEW_SOME : @LK.aview_some_stmt (aview segs).
Proof. exact LCl.wire_a_kit_aview_some. Qed.
Lemma H_LEAF_GLUE : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @PCs.wire_leaf_wr_at rc B (@LK.leaf_cg_of_evtF_stmt) fx.
Proof. intros rc fx. exact (LCl.wire_a_leaf_glue B rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME). Qed.

(* ===================================================================================================== *)
(* The driver step: the core's tfib_srealizesX over the program contract of the entry function           *)
(* ===================================================================================================== *)
Section RC. Context {rc : YM05.RunCeil}.
Let HB : WireSyms B := WireB_syms.
Let HD : forall t, as_dhash B t = tfib_dhash t := fun t => eq_refl.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let AMALLOC : amalloc_realizes tfibsegs B := tfib_amalloc_realizes B HB HD.
Let AFREE : afree_realizes tfibsegs B := afree_realizes_closed B HB HD.
Let AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)) := tfib_AICPY B HB.
Let RO_IN : forall a, RLO <= a < RHI -> in_ro_tfa a := fun a H => or_intror H.
Let ARDCHK : aread_check_stmt B := tfib_ARDCHK B HB.
Let MT_FREE : forall S m, mo_ok MT S m := fun _ _ => I.
Let xst : nat -> (word -> bool) -> (word -> option byte) -> Prop := AD1k.xst.
Let XFR : xst_frame_tfa xst := tfib_xst_frame.
Let PF1 : printf_first_tfa B xst := tfib_printf_first B HB LAWS HB.
Let PFN : printf_next_tfa B xst := tfib_printf_next B HB LAWS HB.
Let est : (word -> bool) -> (word -> option byte) -> Prop := AD1k.est.
Let ESTI : est_img_tfa est := tfib_est_img.
Let ESTF : est_frame_tfa est := tfib_est_frame.
Let FWS : fwrite_site_tfa B est := tfib_fwrite_site B HB LAWS.
Let RFS : refused_site_tfa B est := tfib_refused_site B HB LAWS HB.
Let FPO : fprintf_s_site_tfa B est 0x1d5f9 (strB "cli: cannot open "%string) nlB := tfib_fprintf_open_site B HB LAWS HB.
Let FPR : fprintf_s_site_tfa B est 0x1d60e (strB "cli: read error on "%string) nlB := tfib_fprintf_rderr_site B HB LAWS HB.
Let FPU : fprintf_s_site_tfa B est 0x157da (strB "usage: "%string) (strB " INPUT"%string ++ nlB) := tfib_fprintf_usage_site B HB LAWS HB.
Let EXS : exit_site_tfa B est xst := tfib_exit_site B HB LAWS.

Lemma wire_srealizesX_rc : @tfib_lib_contract_x_all rc checksum_shape B MT XL XL RLO RHI ->
  forall sp rdraw brk mb inp,
  valid_sp sp -> valid_brk segs brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  srealizes segs (init_config segs WAs.M.init_pc WAs.M.phdrs sp brk mb rdraw target_alloc_limit inp)
    (SPECX (LS:=checksum_shape) inp).
Proof.
  intros LIBX sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil.
  change target_alloc_limit with YA02.LIMIT.
  exact (tfib_srealizesX B HB AMALLOC AFREE AICPY ARDCHK MT XL XL RLO RHI MT_FREE RO_IN LIBX xst XFR PF1 PFN est ESTI
    ESTF FWS RFS FPO FPR FPU EXS sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil).
Qed.
End RC.

(* The run ceiling of the start: TFIB_T from the program contract at every run ceiling. *)
Theorem wire_TFIB_T_of_lib :
  (forall rc : YM05.RunCeil, @tfib_lib_contract_x_all rc checksum_shape B MT XL XL RLO RHI) -> TFIB_T.
Proof.
  intros LIB sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp.
  exact (@wire_srealizesX_rc (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowW sp Hsp))
    (LIB (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowW sp Hsp))) sp rnd brk mbase inp
    Hsp Hbrk Hmb Hfit Hinp (YM05.ceil_of_top_run _)).
Qed.
