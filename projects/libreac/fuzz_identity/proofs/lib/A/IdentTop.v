(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/libreac/fuzz_grant/lib/A/GrantTop.v (a working branch 7d31e8f3534) and lib/A/AGrantT.v (a working branch 2d4a68692f3) for fuzz_identity's ASan build. *)
(* The closing file of fuzz_identity's ASan build (image A): IdentityTFIB.TFIB_T and the two statements
   Statements.asan_agrees and Statements.asan_halts, from named parts only.

   Base: the COMPOSED A tree. The integration tip (a working branch 9a386c7f2e0),
   a TEST-ONLY commit 775ce0daf90 (the applied release
   core, the start-up slots and lib/A/IdentRtGlue.v), lib/A/AD1q.v with the library shape as Section
   parameter LS (dad83fa3779), and the wrapper walks lib/A/Rt/WrapBinders.v with their 15 files
   (a working branch eb5680cf9c2; TEST-ONLY, by path). The core's definitions and lemmas are on this
   tree: no core name and no link premise is a Section variable or a Section hypothesis of this file.

   The chain, each link proved in its owner's file:
     IdentEntryLink.ident_entry_link_x / ident_entry_link (lib/A/Prog/IdentEntryLink.v:755, :765) -- the program
       contract of the entry function (LLVMFuzzerTestOneInput, 0x8070c) in the link's copy of the core's contract
       (IdentEntryLink.v:89-148);
     the link's copy IS the core's lib/A/ACfn.v:72 tfib_lib_contract_x_all at the core's sink names, by conversion
       (Let LIBX below): ident_segs and tfibsegs are both Asan.M.loaded_segments (IdentImg.v:21, AB1v.v:13), the
       core's head AE2k.tfib_sink_head is ident_asan_sink_head (tfib_sink_head_is_asan below), YE01.v:195
       arodata_okS is IdentEntryLink.v:96 arodata_okS, and ACfn.v:21-26 are IdentEntryLink.v:69-75;
     the core's driver and start-up lib/A/AD1q.v:71 tfib_srealizesX, at identity_shape (LS explicit), applied as
       fuzz_grant's AGrantT.v:63-84 applies it;
     AsanTop.identity_asan_agrees_of_tfib / identity_asan_halts_of_tfib (lib/A/AsanTop.v:51, :67).

   THE LINK'S OPEN NAMES (IdentEntryLink.v:178-698, each at every fx and rc), instantiated by:
     IdentB          lib/A/AD2l.v:15 IdentB
     asink_syms_T    Reusable/YE00.v:38 asink_syms
     KS              lib/A/AE2k.v:58 tfib_K
     asink_none      Reusable/YE00.v:131 asink_none
     ameta_inv       Reusable/YE01.v:146 ameta_inv
     LAWS            Reusable/YG0q.v:804 AR_laws_ok
     TL              lib/A/IdentRtGlue.v:49 ident_TL
     TLF             lib/A/Prog/IdentFrameImg.v:28 ident_palf; its five premises (IdentB's as_got_uar,
                     as_uar_cell and three pc_stack_malloc entries) by eq_refl
     PSIG            lib/A/Prog/IdentProgSigImg.v:9 ident_prog_sig
     ML              Reusable/YG05.v:139 model_laws_ok, at lib/A/AF0m.v:1633 ts_universe of AD2l.v:73 TfibB_syms
     ASM0 ASM3 ASM4  lib/A/Rt/StackMalloc0.v:515 stack_malloc0_contract, Rt/StackMalloc3.v:517
                     stack_malloc3_contract, Rt/StackMalloc4.v:515 stack_malloc4_contract
     SMP             Reusable/YG05.v:70 stack_malloc_progress
     ASF             Reusable/YG0t.v:474 astack_free_law_ok
     FFL             lib/A/IdentRtGlue.v:62 ident_FFL
     AMEMSET         ident_AMEMSET below: lib/A/AE2r.v:567 asan_memset_realizes (0x51cf4 = IS___asan_memset,
                     IdentAddr.v:18) with its premises in aintrin_realizes's order (amem_range before the two
                     shadow premises; the OSet premise is True), as AD1o.v:74 oset_of_icpt does for the wrap entry
     AMEMCPY         lib/A/AE2q.v:144 asan_memcpy_realizes (0x51858 = IS___asan_memcpy, Prog/IdentAddr.v:20)
     ABCMP           lib/A/AE2s.v:711 bcmp_icpt_contract (0x421a0 = IS___interceptor_trampoline_bcmp, IdentAddr.v:22)
     ASSF5           lib/A/Rt/SetShadow.v:191 ident_set_shadow_f5 (SetShadow.v:30 SSF5_ENTRY = 0x54820
                     = IS___asan_set_shadow_f5, IdentAddr.v:32)
     GM IV ZS_STEM ZS_NAME HUMM HUMF
                     lib/A/IdentStartupFacts.v:1049, :1058, :1069, :1076, :1088, :1096, from the record facts below
     HIMG_UNOWNED    lib/A/IdentHimgOwned.v:109 ident_HIMG_UNOWNED, from the record facts below
     AMALLOC4        Reusable/YCbp.v:30 amalloc04_rule_triv, from IdentImg.v:81 pa_segs_low (ident_segs_low),
                     IdentRtGlue.v:33 ident_api_env, AR_laws_ok, ML and the core's AF0w.v:45 tfib_amalloc_realizes
     AFREE4          Reusable/YCbp.v:39 afree04_rule_triv, from the same and the core's AF0q.v:13
                     afree_realizes_closed
     AJ_NIL_IO       ident_AJ_NIL_IO below: the A restatement of jl2_nil_io
                     (lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_lit2glue.v:185-192, the same proof text, at A's segments)
     AJ_FP_NIL       lib/A/ACfh.v:20 ajournal_fp_nil
     ASINK_NONE_KEPT Reusable/YE01.v:89 asink_none_kept, at lib/A/AD1u.v:46 tfib_AIL
     AMETA_INV_KEPT  Reusable/YE01.v:160 ameta_inv_kept, at lib/A/AD1u.v:46 tfib_AIL
     ASTRLEN         lib/A/Rt/WrapBinders.v:59 astrlen_binder_A (the strlen trampoline 0x4218c, Rt/StrlenDef.v:36)
     ASTRCMP         lib/A/Rt/WrapBinders.v:71 astrcmp_binder_A (the strcmp trampoline 0x42194, Rt/StrcmpDef.v:27)
     AMEMCHR         lib/A/Rt/WrapBinders.v:83 amemchr_binder_A (the memchr trampoline 0x421a4, Rt/MemchrDef.v:24)
   RECORD FACTS. HOWN, HERRNO (IdentHimgOwned.v:106-107) and HZS, HUNIV, HRA0M, HRA0F (IdentStartupFacts.v:1022-1026)
   close by eq_refl at the core's IdentB, and HCONST by
   fun ly => ex_intro _ (Tfib_const_sym ++ Tfib_const_abs) (app_assoc _ _ _) (IdentStartupFacts.v:27): the core's
   Tfib_owned_static (AF0m.v:1551), TFIB_ERRNO (AF0m.v:24), Tfib_zero_shadow (AF0m.v:1549), Tfib_const_shadow
   (AF0m.v:833), Tfib_universe (ACej.v:170) and Tfib_code's allocator return addresses (AF0l.v:10-11) are the
   start-up tables those files copy.

   THE CORE'S LEMMAS, instantiated in Section RC as fuzz_grant's AGrantT.v:41-74 instantiates them:
     TfibSyms AF0m.v:1612; IdentB_syms := AD2l.v:73 TfibB_syms; HD := eq_refl (AD2l.v:33 as_dhash := YF0p.v:14
     tfib_dhash); RO_IN := or_intror (ACeg.v:31 in_ro_tfa, its second part [0x9ada0, 0x9d0a8) = [RLO, RHI));
     tfib_amalloc_realizes AF0w.v:45; afree_realizes_closed AF0q.v:13; tfib_AICPY / tfib_ARDCHK AD2m.v:17 / :22;
     aread_check_stmt AD1i.v:19; xst / est AD1k.v:126 / :87; tfib_xst_frame AD1k.v:134; tfib_est_img /
     tfib_est_frame AD1k.v:115 / :117; tfib_fwrite_site / tfib_refused_site AD1k.v:317 / :358; tfib_printf_first /
     tfib_printf_next AD1o.v:246 / :282; tfib_fprintf_open_site / _rderr_site / _usage_site AD1l.v:147 / :152 / :157
     at AE3j.v:27 FMT_open = 0x1d88c, AE3k.v:27 FMT_rderr = 0x1d8a1, AE3n.v:27 FMT_usage = 0x15944; tfib_exit_site
     AD1j.v:125; the predicates xst_frame_tfa, printf_first_tfa, printf_next_tfa (AD1w.v:120, :145, :152) and
     est_img_tfa, est_frame_tfa, fwrite_site_tfa, fprintf_s_site_tfa, refused_site_tfa, exit_site_tfa (AD1x.v:42,
     :43, :62, :74, :88, :99). The library shape of every core lemma is identity_shape (the local instance below).

   THE SINK HEAD IS EXPLICIT. This file Requires lib/A/AE2k.v but does not Import it, so the core's #[export]
   instance tfib_sink_head (AE2k.v:41) is not in resolution. The plain build's sink hints (Reusable YI5b / YI5c) are
   removed below; a bare `sink_head` then does not elaborate (the `Fail` line). Every part this file names is passed
   `ident_asan_sink_head` (sk_ofl_head = 0x5f8648, IdentEntryLink.v:68) by name; sk_probe_is_asan shows what a bare
   head resolves to, and tfib_sink_head_is_asan that the core's head is the same head. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import String.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_identity Require Statements.
From OSSVerify.libreac.fuzz_identity.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO09 YO05 YO06 YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YA02 YI5b YI5c.
(* The core (compose-A). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YF0p YE00 YE01.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YG05 YG0t YCbp.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB1v AF0m AD2l ACeg.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AD1i AD1w AD1x AD1k AD1o AD1l AD1j AD2m AF0w AF0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AD1q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require AE2k ACfn ACfh AD1u AE2q AE2r AE2s AE3j AE3k AE3n.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Rt Require StackMalloc0 StackMalloc3 StackMalloc4 SetShadow.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Rt Require WrapBinders.
(* The program side. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaTable PaSym IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentImg IdentFrame IdentRo IdentProgSig.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Rt Require Import StrlenDef StrcmpDef MemchrDef SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require IdentProgSigImg IdentFrameImg.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentEntryLink.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require IdentHimgOwned IdentStartupFacts IdentRtGlue.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import IdentityTFIB.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require AsanTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Agree.
Import ListNotations.
Open Scope Z_scope.

(* The guard: the plain build's sink hints are out of the way, so no `{SK}` can be filled with the plain head. *)
#[local] Remove Hints YI5b.src0_sink_head YI5c.src0_sink YI5c.src0_sink_laws : typeclass_instances.
Fail Definition sk_bare : YI16.sink_head := _.
#[local] Existing Instance ident_asan_sink_head.
(* What a bare `sink_head` resolves to in this file: the ASan image's own head. *)
Definition sk_probe : YI16.sink_head := _.
Lemma sk_probe_is_asan : sk_probe = ident_asan_sink_head.
Proof. reflexivity. Qed.
(* The core's head (AE2k.v:41, sk_ofl_head := A_ofl_head = 0x5f8648, AE2k.v:32) is the same head: the core's
   ACfn.v contract, stated at it, is the link's contract, stated at ident_asan_sink_head. *)
Lemma tfib_sink_head_is_asan : AE2k.tfib_sink_head = ident_asan_sink_head.
Proof. reflexivity. Qed.

(* fuzz_grant's AGrantT.v:32-33. *)
Lemma valid_sp_windowX : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.

(* The link's Section L notations SEGS and SIGMA (IdentEntryLink.v:174, :176), at the run ceiling rc. *)
Local Notation SEGSr rc := (@pa_segs _ ident_listing (@PI_ident rc)).
Local Notation SIGMAr rc := (@pa_sigma _ ident_listing (@PI_ident rc)).

Section asan.

(* ---- the record facts, at the core's IdentB (AD2l.v:15) ---------------------------------------------------- *)
(* IdentHimgOwned.v:106-107: the core record's owned-static list and errno word. *)
Let HOWN : as_owned_static IdentB = IdentHimgOwned.TFIB_OWNED_STATIC_A := eq_refl.
Let HERRNO : as_errno IdentB = IdentHimgOwned.TFIB_ERRNO_A := eq_refl.
(* IdentStartupFacts.v:1022-1026: its zero-shadow table, the tail of its const cells, its universe and the two
   allocator return addresses of its code. *)
Let HZS : as_zero_shadow IdentB = IdentStartupFacts.TFIB_ZERO_SHADOW_A := eq_refl.
Let HCONST : forall ly, exists pre, as_const IdentB ly = pre ++ IdentStartupFacts.TFIB_CONST_SHADOW_A :=
  fun ly => ex_intro _ (Tfib_const_sym ++ Tfib_const_abs) (app_assoc _ _ _).
Let HUNIV : as_universe IdentB = IdentStartupFacts.TFIB_UNIVERSE_A := eq_refl.
Let HRA0M : pc_malloc_ra0 (as_code IdentB) = 0x52e48 := eq_refl.
Let HRA0F : pc_free_ra0 (as_code IdentB) = 0x52ce8 := eq_refl.

(* ---- the core side ----------------------------------------------------------------------------------------- *)
#[local] Existing Instance YK11.fx0.
(* The library shape of the core's lemmas: identity_shape (IdentityTFIB.v:14), ahead of any other lib_shape
   instance loaded with it. *)
#[local] Existing Instance OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg.Agree.checksum_shape_ag | 0.

(* fuzz_grant's AGrantT.v:35-37. *)
Let B : asyms := IdentB.
Let HB : TfibSyms B := TfibB_syms.
Let HD : forall t, as_dhash B t = tfib_dhash t := fun t => eq_refl.
(* IdentEntryLink.v:236 ML: Reusable/YG05.v:139, at the universe fact of TfibB_syms (AF0m.v:1633 ts_universe). *)
Let ML : model_laws (as_universe IdentB) := YG05.model_laws_ok (as_universe IdentB) (ts_universe IdentB TfibB_syms).

(* IdentEntryLink.v:243 AMEMSET: lib/A/AE2r.v:567 asan_memset_realizes at __asan_memset (0x51cf4 =
   IS___asan_memset, Prog/IdentAddr.v:18), its premises in aintrin_realizes's order: amem_range comes before the
   two shadow premises, and the OSet premise is True (the pattern of AD1o.v:74 oset_of_icpt at the wrap entry). *)
Lemma ident_AMEMSET : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
@aintrin_realizes fx rc (SEGSr rc) IdentB OSet (SIGMAr rc IS___asan_memset).
Proof.
intros fx rc ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM HRA HHULL _.
exact (AE2r.asan_memset_realizes IdentB (AR_laws_ok _ IdentB) TfibB_syms ly S W regs mem md d x n HPRE G10 G11 G12
  Hn Hd Hdn HDST HRA HHULL HAM).
Qed.

(* IdentEntryLink.v:254-256 AJ_NIL_IO: the A restatement of jl2_nil_io
   (lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_lit2glue.v:185-192, the same proof text), at A's segments SEGSr rc and
   the head ident_asan_sink_head: a journal whose footprint is empty keeps the fd table and the file system
   (Reusable/YCbq.v:80 aos_step_closed, footprint []). *)
Lemma ident_AJ_NIL_IO : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
forall STK sp0 ly S (W : world (SEGSr rc)) mem md own ly' S' W' mem' md' k,
@ajournal rc ident_asan_sink_head (SEGSr rc) IdentB STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof.
intros fx rc STK sp0 ly S W mem md own ly' S' W' mem' md' k HJ.
pose proof HJ as (_ & _ & _ & _ & Hio & _).
destruct (aos_step_closed [] md md' ltac:(intros (x & Hx & _); destruct Hx) Hio) as (E1 & E2 & _ & _).
unfold m_fds, m_fs. rewrite E1, E2. split; reflexivity.
Qed.

(* ---- the chain ------------------------------------------------------------------------------------------- *)

(* The closer's LIBX_ALL (fuzz_grant's AGrantT.v:40), in the link's copy of the contract, from the entry link
   (IdentEntryLink.v:755, :765): the link's open names at every fx and rc, in ident_entry_link_x's argument order,
   each instantiated as the header lists. *)
Lemma ident_lib_all : forall rc : YM05.RunCeil,
@IdentEntryLink.tfib_lib_contract_x_all ident_asan_sink_head YE00.asink_syms AE2k.tfib_K YE00.asink_none YE01.ameta_inv
  rc identity_shape IdentB ameter_triv XL0 XL0 RLO RHI.
Proof.
apply (ident_entry_link IdentB YE00.asink_syms AE2k.tfib_K YE00.asink_none YE01.ameta_inv).
intros fx rc.
exact (@ident_entry_link_x fx rc IdentB YE00.asink_syms AE2k.tfib_K YE00.asink_none YE01.ameta_inv
  (AR_laws_ok _ IdentB)
  (IdentRtGlue.ident_TL fx rc)
  (IdentFrameImg.ident_palf IdentB eq_refl eq_refl eq_refl eq_refl eq_refl)
  IdentProgSigImg.ident_prog_sig
  ML
  (StackMalloc0.stack_malloc0_contract IdentB (AR_laws_ok _ IdentB) TfibB_syms)
  (StackMalloc3.stack_malloc3_contract IdentB (AR_laws_ok _ IdentB) TfibB_syms)
  (StackMalloc4.stack_malloc4_contract IdentB (AR_laws_ok _ IdentB) TfibB_syms)
  (YG05.stack_malloc_progress (as_universe IdentB))
  (YG0t.astack_free_law_ok (SEGSr rc) IdentB)
  (IdentRtGlue.ident_FFL fx rc)
  (ident_AMEMSET fx rc)
  (AE2q.asan_memcpy_realizes IdentB (AR_laws_ok _ IdentB) TfibB_syms)
  (AE2s.bcmp_icpt_contract IdentB (AR_laws_ok _ IdentB) TfibB_syms)
  (WrapBinders.astrlen_binder_A fx rc) (WrapBinders.astrcmp_binder_A fx rc)
  (SetShadow.ident_set_shadow_f5 IdentB (AR_laws_ok _ IdentB) TfibB_syms)
  (IdentStartupFacts.ident_GM IdentB HZS HCONST) (IdentStartupFacts.ident_IV IdentB HZS HCONST)
  (ident_AJ_NIL_IO fx rc)
  (IdentHimgOwned.ident_HIMG_UNOWNED IdentB HOWN HERRNO)
  (IdentStartupFacts.ident_ZS_STEM IdentB HZS) (IdentStartupFacts.ident_ZS_NAME IdentB HZS)
  (IdentStartupFacts.ident_HUMM IdentB HUNIV HRA0M) (IdentStartupFacts.ident_HUMF IdentB HUNIV HRA0F)
  (YCbp.amalloc04_rule_triv (SK := ident_asan_sink_head) (SEGSr rc) IdentB
     (@pa_segs_low _ ident_listing (@PI_ident rc)) (IdentRtGlue.ident_api_env fx rc) (AR_laws_ok _ IdentB) ML
     (tfib_amalloc_realizes IdentB TfibB_syms HD))
  (YCbp.afree04_rule_triv (SK := ident_asan_sink_head) (SEGSr rc) IdentB
     (@pa_segs_low _ ident_listing (@PI_ident rc)) (IdentRtGlue.ident_api_env fx rc) (AR_laws_ok _ IdentB) ML
     (afree_realizes_closed IdentB TfibB_syms HD))
  (WrapBinders.amemchr_binder_A fx rc)
  (ACfh.ajournal_fp_nil (rc := rc) (SK := ident_asan_sink_head) (SEGSr rc) IdentB)
  (YE01.asink_none_kept (rc := rc) (SK := ident_asan_sink_head) (SEGSr rc) IdentB AE2k.tfib_K
     (AD1u.tfib_AIL IdentB TfibB_syms))
  (YE01.ameta_inv_kept (rc := rc) (SK := ident_asan_sink_head) (SEGSr rc) IdentB AE2k.tfib_K
     (AD1u.tfib_AIL IdentB TfibB_syms))).
Qed.

(* fuzz_grant's AGrantT.v:41-74, text for text at fuzz_identity's names. *)
Section RC. Context {rc : YM05.RunCeil}.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let AMALLOC : amalloc_realizes tfibsegs B := tfib_amalloc_realizes B HB HD.
Let AFREE : afree_realizes tfibsegs B := afree_realizes_closed B HB HD.
Let AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)) := tfib_AICPY B HB.
(* The core's contract (ACfn.v:72) is the link's copy at the core's sink names: the conversion the header names. *)
Let LIBX : @ACfn.tfib_lib_contract_x_all rc identity_shape B ameter_triv XL0 XL0 RLO RHI := ident_lib_all rc.
Let RO_IN : forall a, RLO <= a < RHI -> in_ro_tfa a := fun a H => or_intror H.
Let ARDCHK : aread_check_stmt B := tfib_ARDCHK B HB.
Let MT_FREE : forall S m, mo_ok ameter_triv S m := fun _ _ => I.
Let xst : nat -> (word -> bool) -> (word -> option byte) -> Prop := AD1k.xst.
Let XFR : xst_frame_tfa xst := tfib_xst_frame.
Let PF1 : printf_first_tfa B xst := tfib_printf_first B HB LAWS HB.
Let PFN : printf_next_tfa B xst := tfib_printf_next B HB LAWS HB.
Let est : (word -> bool) -> (word -> option byte) -> Prop := AD1k.est.
Let ESTI : est_img_tfa est := tfib_est_img.
Let ESTF : est_frame_tfa est := tfib_est_frame.
Let FWS : fwrite_site_tfa B est := tfib_fwrite_site B HB LAWS.
Let RFS : refused_site_tfa B est := tfib_refused_site B HB LAWS HB.
Let FPO : fprintf_s_site_tfa B est AE3j.FMT_open (YO05.strB "cli: cannot open "%string) YO05.nlB :=
  tfib_fprintf_open_site B HB LAWS HB.
Let FPR : fprintf_s_site_tfa B est AE3k.FMT_rderr (YO05.strB "cli: read error on "%string) YO05.nlB :=
  tfib_fprintf_rderr_site B HB LAWS HB.
Let FPU : fprintf_s_site_tfa B est AE3n.FMT_usage (YO05.strB "usage: "%string) (YO05.strB " INPUT"%string ++ YO05.nlB) :=
  tfib_fprintf_usage_site B HB LAWS HB.
Let EXS : exit_site_tfa B est xst := tfib_exit_site B HB LAWS.
Lemma ident_srealizesX_rc : forall sp rdraw brk mb inp,
valid_sp sp -> valid_brk identsegs0 brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
srealizes identsegs0 (init_config identsegs0 Asan.M.init_pc Asan.M.phdrs sp brk mb rdraw target_alloc_limit inp)
  (SPECX (LS:=identity_shape) inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil.
change target_alloc_limit with YA02.LIMIT.
exact (@tfib_srealizesX rc identity_shape B HB AMALLOC AFREE AICPY ARDCHK ameter_triv XL0 XL0 RLO RHI MT_FREE RO_IN LIBX
  xst XFR PF1 PFN est ESTI ESTF FWS RFS FPO FPR FPU EXS sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil).
Qed.
End RC.

(* fuzz_grant's AGrantT.v:75-82. *)
Theorem ident_srealizesX_top : forall sp rdraw brk mb inp,
valid_sp sp -> valid_brk identsegs0 brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
srealizes identsegs0 (init_config identsegs0 Asan.M.init_pc Asan.M.phdrs sp brk mb rdraw target_alloc_limit inp)
  (SPECX (LS:=identity_shape) inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp.
exact (@ident_srealizesX_rc (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowX sp Hsp)) sp rdraw brk mb inp
  Hsp Hbrk Hmb Hfit Hinp (YM05.ceil_of_top_run _)).
Qed.

(* IdentityTFIB.TFIB_T (lib/A/IdentityTFIB.v:19), as fuzz_grant's AGrantT.v:83-84 closes it. *)
Theorem ident_TFIB_T_of_parts : TFIB_T.
Proof.
intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp.
exact (ident_srealizesX_top sp rnd brk mbase inp Hsp Hbrk Hmb Hfit Hinp).
Qed.

(* The two statements of fuzz_identity's ASan build, given only the named parts above (lib/A/AsanTop.v:51, :67). *)
Theorem ident_asan_agrees_of_parts : Statements.asan_agrees.
Proof. exact (AsanTop.identity_asan_agrees_of_tfib ident_TFIB_T_of_parts). Qed.
Theorem ident_asan_halts_of_parts : Statements.asan_halts.
Proof. exact (AsanTop.identity_asan_halts_of_tfib ident_TFIB_T_of_parts). Qed.

(* Inside the Section, Print Assumptions lists what the two statements rest on: no Section hypothesis is left, so
   only the axioms toolchain/allowed-axioms.txt allows. *)
Print Assumptions ident_asan_agrees_of_parts.
Print Assumptions ident_asan_halts_of_parts.
End asan.
