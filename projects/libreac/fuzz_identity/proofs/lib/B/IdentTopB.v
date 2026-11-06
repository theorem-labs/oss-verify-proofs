(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/libreac/fuzz_identity/lib/A/IdentTop.v (a working branch b49fc549b95; itself from fuzz_grant's GrantTop.v and a Theorem Labs lane's AGrantT.v 2d4a68692f3) for fuzz_identity's ASan+UBSan build; on the composed B tree as the A closer of 2e13013179f is on the composed A tree. *)
(* The closing file of fuzz_identity's ASan+UBSan build (image B): IdentityTFIB.TFIB_TB (lib/B/IdentityTFIB.v:20) and
   the two statements Statements.asan_ubsan_agrees and Statements.asan_ubsan_halts, from named parts only. The image-B
   twin of lib/A/IdentTop.v.

   Base: the COMPOSED B tree, the B stage (run 18, composed by
   zcompose.py, pin 47d69dd554d7d8ea; B patch 16: one ameter_ops, Reusable/YC5d.v): the B core lib/ReusableB/Y*.v
   (cgif's A core relocated onto fuzz_identity.asan-ubsan) with ReusableB/YD1q.v taking the library shape as Section
   parameter LS (`Context {rc} {LS : lib_shape}`), the B wrapper binders lib/B/Rt/WrapBinders.v, and the B
   runtime glue lib/B/IdentRtGlueB.v of record (taken by
   path). The core's definitions and lemmas are on this tree: no core name and no link premise is a Section variable
   or a Section hypothesis of this file.

   The chain, each link proved in its owner's file:
     IdentEntryLink.identb_entry_link_x / identb_entry_link (lib/B/Prog/IdentEntryLink.v:726, :741) -- the program
       contract of the entry function (LLVMFuzzerTestOneInput, 0x80774) in the link's copy of the core's contract
       (IdentEntryLink.v:88-147);
     the link's copy IS the core's lib/ReusableB/YCfn.v:70 tfib_lib_contract_x_all at the core's sink names, by
       conversion (Let LIBX below): identb_segs and tfibsegs are both AsanUbsan.M.loaded_segments (IdentBImg.v:22,
       YB1v.v:14), the core's head YE2k.tfib_sink_head is ident_asan_ubsan_sink_head (tfib_sink_head_is_asan below),
       YE01.v:195 arodata_okS is IdentEntryLink.v:95 arodata_okS, and YCfn.v:19-24 are IdentEntryLink.v:69-74. The
       meter is the link's ameter_triv (IdentEntryLink.v:80), over Reusable/YC5d.v's ameter_ops, the one meter record
       of the tree (B patch 16), as on A;
     the core's driver and start-up lib/ReusableB/YD1q.v:66 tfib_srealizesX, at identity_shape (LS explicit),
       applied as fuzz_grant's AGrantT.v:63-84 applies it;
     AsanUbsanTop.identity_asan_ubsan_agrees_of_tfib / identity_asan_ubsan_halts_of_tfib (lib/B/AsanUbsanTop.v:30,
       :46).

   THE LINK'S OPEN NAMES (IdentEntryLink.v:183-723, each at every fx and rc), instantiated by:
     IdentB          lib/ReusableB/YD2l.v:12 IdentB (cgif YD2l.v's TfibB renamed)
     asink_syms_T    Reusable/YE00.v:38 asink_syms
     KS              lib/ReusableB/YE2k.v:59 tfib_K
     asink_none      Reusable/YE00.v:131 asink_none
     ameta_inv       lib/ReusableB/YE01.v:146 ameta_inv
     LAWS            Reusable/YG0q.v:804 AR_laws_ok
     TL              lib/B/IdentRtGlueB.v:72 identb_TL
     TLF             lib/B/Prog/IdentBFrameImg.v:30 identb_palf; its five premises (IdentB's as_got_uar 0x9c6e8,
                     as_uar_cell 0xa52c0 and the pc_stack_malloc entries 0x3cfe8, 0x3d15c, 0x3d308 of YF0l.v:12) by
                     eq_refl
     PSIG            lib/B/Prog/IdentBProgSigImg.v:9 identb_prog_sig
     ML              lib/B/IdentRtGlueB.v:85 identb_ML
     ASM0 ASM3 ASM4  lib/B/Rt/StackMalloc0.v:518 stack_malloc0_contract, Rt/StackMalloc3.v:520
                     stack_malloc3_contract, Rt/StackMalloc4.v:518 stack_malloc4_contract
     SMP             lib/B/IdentRtGlueB.v:88 identb_SMP
     ASF             Reusable/YG0t.v:474 astack_free_law_ok
     FFL             lib/B/IdentRtGlueB.v:92 identb_FFL
     AMALLOC4        lib/B/IdentRtGlueB.v:113 identb_AMALLOC4 (the glue of record,
                     at the link's meter IdentEntryLink.v:80 ameter_triv)
     AFREE4          lib/B/IdentRtGlueB.v:121 identb_AFREE4 (the same)
     HUMB            lib/B/IdentStartupFacts.v:1938 identb_HUMB, from the record facts below
     AMEMSET         identb_AMEMSET below: lib/ReusableB/YE2r.v:568 asan_memset_realizes (0x51d5c =
                     IB___asan_memset, Prog/IdentBAddr.v:19) with its premises in aintrin_realizes's order (amem_range
                     before the two shadow premises; the OSet premise is True); the restatement of lib/A/IdentTop.v's
                     ident_AMEMSET at B's segments
     AMEMCPY         lib/ReusableB/YE2q.v:145 asan_memcpy_realizes (0x518c0 = IB___asan_memcpy, IdentBAddr.v:21)
     ABCMP           lib/ReusableB/YE2s.v:711 bcmp_icpt_contract (0x42208 = IB___interceptor_trampoline_bcmp,
                     IdentBAddr.v:24)
     ASTRLEN         lib/B/Rt/WrapBinders.v:63 astrlen_binder_B (the strlen trampoline 0x421f4)
     ASTRCMP         lib/B/Rt/WrapBinders.v:75 astrcmp_binder_B (the strcmp trampoline 0x421fc)
     AMEMCHR         lib/B/Rt/WrapBinders.v:87 amemchr_binder_B (the memchr trampoline 0x4220c)
     ASSF5           lib/B/Rt/SetShadow.v:193 ident_set_shadow_f5 (SetShadow.v:32 SSF5_ENTRY = 0x54888
                     = IB___asan_set_shadow_f5, IdentBAddr.v:34)
     GM IV ZS_STEM ZS_NAME HUMM HUMF
                     lib/B/IdentStartupFacts.v:1902, :1910, :1918, :1922, :1926, :1932, from the record facts below
     HIMG_UNOWNED    lib/B/IdentHimgOwned.v:106 identb_HIMG_UNOWNED, its HOWN / HERRNO lib/B/IdentCloseImgB.v:120
                     identb_HOWN / :125 identb_HERRNO from the record facts below
     AJ_FP_NIL       lib/ReusableB/YCfh.v:20 ajournal_fp_nil
     AJ_NIL_IO       lib/B/IdentCloseImgB.v:130 identb_AJ_NIL_IO (jl2_nil_io at the B head and image instance)
     SRZ_ENTER       lib/ReusableB/YCfh.v:38 srz_enter
     ASINK_NONE_KEPT lib/ReusableB/YE01.v:89 asink_none_kept, at lib/ReusableB/YD1u.v:45 tfib_AIL
     AMETA_INV_KEPT  lib/ReusableB/YE01.v:160 ameta_inv_kept, at lib/ReusableB/YD1u.v:45 tfib_AIL
   RECORD FACTS. HZS, HCONST, HUNIV, HMRA, HFRA (IdentStartupFacts.v:1871-1875), TS_OWNED, TS_ERRNO
   (IdentCloseImgB.v:115-116) and IN_RO_TFA (the core's in_ro_tfa, IdentCloseImgB.v:145) close by eq_refl at the
   core's IdentB: the core's Tfib_zero_shadow (YF0m.v:1576), Tfib_const (YF0m.v:1575, over Tfib_const_sym,
   Tfib_const_abs, Tfib_const_shadow), Tfib_universe (YCej.v:223), Tfib_owned_static (YF0m.v:1578), TFIB_ERRNO
   (YF0m.v:25), Tfib_code's allocator return addresses (YF0l.v:10-11) and in_ro_tfa (YCeg.v:31) are the text those
   files copy (IdentStartupFacts.v:42-1617 Module StartupB, IdentCloseImgB.v:50-108 Module IdentCloseTables). HCONST
   is an equation on B, not an existential as on A: fun ly => eq_refl.

   THE CORE'S LEMMAS, instantiated in Section RC as fuzz_grant's AGrantT.v:41-74 instantiates them:
     TfibSyms YF0m.v:1640; IdentB_syms := YD2l.v:70 TfibB_syms; HD := IdentRtGlueB.v:107 identb_HD (eq_refl,
     YD2l.v:30 as_dhash := YF0p.v:14 tfib_dhash); RO_IN := IdentCloseImgB.v:148 identb_RO_IN over IN_RO_TFA (its
     right arm [0x9b080, 0x9d388) = [RLO, RHI), IdentEntryLink.v:76-77); tfib_amalloc_realizes YF0w.v:44;
     afree_realizes_closed YF0q.v:10; tfib_AICPY / tfib_ARDCHK YD2m.v:16 / :21; aread_check_stmt YD1i.v:18; xst / est
     YD1k.v:127 / :88; tfib_xst_frame YD1k.v:135; tfib_est_img / tfib_est_frame YD1k.v:116 / :118; tfib_fwrite_site /
     tfib_refused_site YD1k.v:319 / :360; tfib_printf_first / tfib_printf_next YD1o.v:246 / :282;
     tfib_fprintf_open_site / _rderr_site / _usage_site YD1l.v:146 / :151 / :156 at YE3j.v:28 FMT_open = 0x1d893,
     YE3k.v:28 FMT_rderr = 0x1d8a8, YE3n.v:28 FMT_usage = 0x1594b (the addresses YD1q.v:48-50 states);
     tfib_exit_site YD1j.v:122; the predicates xst_frame_tfa, printf_first_tfa, printf_next_tfa (YD1w.v:118, :143,
     :150) and est_img_tfa, est_frame_tfa, fwrite_site_tfa, fprintf_s_site_tfa, refused_site_tfa, exit_site_tfa
     (YD1x.v:36, :37, :56, :68, :82, :93); the meter IdentEntryLink.v:80 ameter_triv. The library shape of every core
     lemma is identity_shape (the local instance below).

   THE SINK HEAD IS EXPLICIT. This file Requires lib/ReusableB/YE2k.v but does not Import it, so the core's
   #[export] instance tfib_sink_head (YE2k.v:41) is not in resolution. The plain build's sink hints (Reusable YI5b /
   YI5c) are removed below (the link's IdentBSkGuard.v removes them too; the local line repeats it in this file); a
   bare `sink_head` then does not elaborate (the `Fail` line). Every part this file names is passed
   `ident_asan_ubsan_sink_head` (sk_ofl_head = 0x5f8948, IdentEntryLink.v:68) by name; sk_probe_is_asan shows what a
   bare head resolves to, and tfib_sink_head_is_asan that the core's head is the same head. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import String.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_identity Require Statements.
From OSSVerify.libreac.fuzz_identity.images Require AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO09 YO05 YO06 YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YI5b YI5c.
(* The core (the B stage). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YF0p YE00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YG0t.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.ReusableB Require Import YB1v YF0m YD2l YCeg YE01.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.ReusableB Require Import
YD1i YD1w YD1x YD1k YD1o YD1l YD1j YD2m YF0w YF0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.ReusableB Require Import YD1q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.ReusableB Require
YE2k YCfn YCfh YA02 YD1u YE2q YE2r YE2s YE3j YE3k YE3n.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require StackMalloc0 StackMalloc3 StackMalloc4 SetShadow.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require WrapBinders.
(* The program side. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym IdentBase IdentRo.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Agree.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import IdentBSkGuard.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBImg IdentBFrame IdentBProgSig IdentBProgSigImg.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import StrlenDef StrcmpDef MemchrDef SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require
LLVMFuzzerTestOneInput buf_of IdentBFrameImg.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import IdentEntryLink.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B Require IdentHimgOwned.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B Require IdentStartupFacts IdentCloseImgB IdentRtGlueB.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B Require Import IdentityTFIB.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B Require AsanUbsanTop.
Import ListNotations.
Open Scope Z_scope.

(* The guard: the plain build's sink hints are out of the way, so no `{SK}` can be filled with the plain head. *)
#[local] Remove Hints YI5b.src0_sink_head YI5c.src0_sink YI5c.src0_sink_laws : typeclass_instances.
Fail Definition sk_bare : YI16.sink_head := _.
#[local] Existing Instance ident_asan_ubsan_sink_head.
(* What a bare `sink_head` resolves to in this file: the ASan+UBSan image's own head. *)
Definition sk_probe : YI16.sink_head := _.
Lemma sk_probe_is_asan : sk_probe = ident_asan_ubsan_sink_head.
Proof. reflexivity. Qed.
(* The core's head (YE2k.v:41, sk_ofl_head := A_ofl_head = 0x5f8948, YE2k.v:32) is the same head: the core's
   YCfn.v contract, stated at it, is the link's contract, stated at ident_asan_ubsan_sink_head. *)
Lemma tfib_sink_head_is_asan : YE2k.tfib_sink_head = ident_asan_ubsan_sink_head.
Proof. reflexivity. Qed.

(* fuzz_grant's AGrantT.v:32-33. *)
Lemma valid_sp_windowX : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.

(* The link's Section L notations SEGS and SIGMA (IdentEntryLink.v:179, :181), at the run ceiling rc. *)
Local Notation SEGSr rc := (@pa_segs _ identb_listing (@PI_identb rc)).
Local Notation SIGMAr rc := (@pa_sigma _ identb_listing (@PI_identb rc)).

Section asan_ubsan.

(* ---- the record facts, at the core's IdentB (YD2l.v:12) --------------------------------------------------- *)
(* IdentStartupFacts.v:1871-1875: its zero-shadow table, its constant cells, its universe and the two allocator
   return addresses of its code, against the start-up tables IdentStartupFacts.v copies (Module StartupB). *)
Let HZS : as_zero_shadow IdentB = B.IdentStartupFacts.StartupB.Tfib_zero_shadow := eq_refl.
Let HCONST : forall ly, as_const IdentB ly = B.IdentStartupFacts.StartupB.Tfib_const ly := fun ly => eq_refl.
Let HUNIV : as_universe IdentB = B.IdentStartupFacts.StartupB.Tfib_universe := eq_refl.
Let HMRA : pc_malloc_ra0 (as_code IdentB) = 0x52eb0 := eq_refl.
Let HFRA : pc_free_ra0 (as_code IdentB) = 0x52d50 := eq_refl.
(* IdentCloseImgB.v:115-116: its owned-static list and errno word (TfibSyms's ts_owned / ts_errno), against
   IdentCloseImgB.v's copy of YF0m.v (Module IdentCloseTables). *)
Let TS_OWNED : as_owned_static IdentB = IdentCloseImgB.IdentCloseTables.Tfib_owned_static := eq_refl.
Let TS_ERRNO : as_errno IdentB = IdentCloseImgB.IdentCloseTables.TFIB_ERRNO := eq_refl.
(* IdentCloseImgB.v:145: the core's in_ro_tfa (YCeg.v:31, at tfibsegs = AsanUbsan.M.loaded_segments) is the
   read-only segments or the relro range. *)
Let IN_RO_TFA : forall a, in_ro_tfa a =
((exists s, In s AsanUbsan.M.loaded_segments /\ seg_writable s = false /\
   Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s))
 \/ (0x9b080 <= a < 0x9d388)) := fun a => eq_refl.

(* ---- the core side ----------------------------------------------------------------------------------------- *)
#[local] Existing Instance YK11.fx0.
(* The library shape of the core's lemmas: identity_shape (IdentityTFIB.v:15), ahead of any other lib_shape
   instance loaded with it. *)
#[local] Existing Instance OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg.Agree.checksum_shape_ag | 0.

(* IdentEntryLink.v:249 AMEMSET: lib/ReusableB/YE2r.v:568 asan_memset_realizes at __asan_memset (0x51d5c =
   IB___asan_memset, Prog/IdentBAddr.v:19), its premises in aintrin_realizes's order: amem_range comes before the
   two shadow premises, and the OSet premise is True. The proof text of lib/A/IdentTop.v's ident_AMEMSET
   at B's segments. *)
Lemma identb_AMEMSET : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
@aintrin_realizes fx rc (SEGSr rc) IdentB OSet (SIGMAr rc IB___asan_memset).
Proof.
intros fx rc ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM HRA HHULL _.
exact (YE2r.asan_memset_realizes IdentB (AR_laws_ok _ IdentB) TfibB_syms ly S W regs mem md d x n HPRE G10 G11 G12
  Hn Hd Hdn HDST HRA HHULL HAM).
Qed.

(* ---- the chain ------------------------------------------------------------------------------------------- *)

(* The closer's LIBX_ALL (fuzz_grant's AGrantT.v:40), in the link's copy of the contract, from the entry link
   (IdentEntryLink.v:726, :741): the link's open names at every fx and rc, in identb_entry_link_x's argument order,
   each instantiated as the header lists. *)
Lemma identb_lib_all : forall rc : YM05.RunCeil,
@tfib_lib_contract_x_all ident_asan_ubsan_sink_head YE00.asink_syms YE2k.tfib_K YE00.asink_none YE01.ameta_inv
  rc identity_shape IdentB ameter_triv XL0 XL0 RLO RHI.
Proof.
apply (identb_entry_link IdentB YE00.asink_syms YE2k.tfib_K YE00.asink_none YE01.ameta_inv).
intros fx rc.
exact (@identb_entry_link_x fx rc IdentB YE00.asink_syms YE2k.tfib_K YE00.asink_none YE01.ameta_inv
  (@AR_laws_ok rc (SEGSr rc) IdentB)
  (IdentRtGlueB.identb_TL fx rc)
  (IdentBFrameImg.identb_palf IdentB eq_refl eq_refl eq_refl eq_refl eq_refl)
  identb_prog_sig
  (IdentRtGlueB.identb_ML fx rc)
  (B.Rt.StackMalloc0.stack_malloc0_contract IdentB (AR_laws_ok _ IdentB) TfibB_syms)
  (B.Rt.StackMalloc3.stack_malloc3_contract IdentB (AR_laws_ok _ IdentB) TfibB_syms)
  (IdentRtGlueB.identb_SMP fx rc)
  (YG0t.astack_free_law_ok (SEGSr rc) IdentB)
  (IdentRtGlueB.identb_FFL fx rc)
  (IdentRtGlueB.identb_AMALLOC4 fx rc)
  (B.IdentStartupFacts.identb_HUMB IdentB HUNIV HMRA)
  (identb_AMEMSET fx rc)
  (YE2q.asan_memcpy_realizes IdentB (AR_laws_ok _ IdentB) TfibB_syms)
  (YE2s.bcmp_icpt_contract IdentB (AR_laws_ok _ IdentB) TfibB_syms)
  (WrapBinders.astrlen_binder_B fx rc) (WrapBinders.astrcmp_binder_B fx rc)
  (B.Rt.SetShadow.ident_set_shadow_f5 IdentB (AR_laws_ok _ IdentB) TfibB_syms)
  (B.IdentStartupFacts.identb_GM IdentB (@AR_laws_ok rc (SEGSr rc) IdentB) HZS HCONST)
  (B.IdentStartupFacts.identb_IV IdentB (@AR_laws_ok rc (SEGSr rc) IdentB) HZS HCONST)
  (IdentHimgOwned.identb_HIMG_UNOWNED IdentB
    (IdentCloseImgB.identb_HOWN IdentB TS_OWNED) (IdentCloseImgB.identb_HERRNO IdentB TS_ERRNO))
  (B.IdentStartupFacts.identb_ZS_STEM IdentB HZS) (B.IdentStartupFacts.identb_ZS_NAME IdentB HZS)
  (B.IdentStartupFacts.identb_HUMM IdentB HUNIV HMRA) (B.IdentStartupFacts.identb_HUMF IdentB HUNIV HFRA)
  (IdentRtGlueB.identb_AFREE4 fx rc)
  (B.Rt.StackMalloc4.stack_malloc4_contract IdentB (AR_laws_ok _ IdentB) TfibB_syms)
  (WrapBinders.amemchr_binder_B fx rc)
  (YCfh.ajournal_fp_nil (rc := rc) (SK := ident_asan_ubsan_sink_head) (SEGSr rc) IdentB)
  (IdentCloseImgB.identb_AJ_NIL_IO IdentB fx rc) (YCfh.srz_enter (SEGSr rc))
  (YE01.asink_none_kept (rc := rc) (SK := ident_asan_ubsan_sink_head) (SEGSr rc) IdentB YE2k.tfib_K
     (YD1u.tfib_AIL IdentB TfibB_syms))
  (YE01.ameta_inv_kept (rc := rc) (SK := ident_asan_ubsan_sink_head) (SEGSr rc) IdentB YE2k.tfib_K
     (YD1u.tfib_AIL IdentB TfibB_syms))).
Qed.

(* fuzz_grant's AGrantT.v:35-37. *)
Let B : asyms := IdentB.
Let HB : TfibSyms B := TfibB_syms.
Let HD : forall t, as_dhash B t = tfib_dhash t := IdentRtGlueB.identb_HD.

(* fuzz_grant's AGrantT.v:41-74, text for text at fuzz_identity B's names. *)
Section RC. Context {rc : YM05.RunCeil}.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let AMALLOC : amalloc_realizes tfibsegs B := tfib_amalloc_realizes B HB HD.
Let AFREE : afree_realizes tfibsegs B := afree_realizes_closed B HB HD.
Let AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)) := tfib_AICPY B HB.
(* The core's contract (YCfn.v:70) is the link's copy at the core's sink names: the conversion the header names. *)
Let LIBX : @YCfn.tfib_lib_contract_x_all rc identity_shape B ameter_triv XL0 XL0 RLO RHI := identb_lib_all rc.
(* fuzz_grant's AGrantT.v:47 Let RO_IN (or_intror at the core's in_ro_tfa): IdentCloseImgB.v:148 identb_RO_IN over
   IN_RO_TFA. RLO, RHI = 0x9b080, 0x9d388 (IdentEntryLink.v:76-77). *)
Let RO_IN : forall a, RLO <= a < RHI -> in_ro_tfa a :=
  IdentCloseImgB.identb_RO_IN in_ro_tfa
    (fun a => exists s, In s AsanUbsan.M.loaded_segments /\ seg_writable s = false /\
       Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s))
    IN_RO_TFA.
Let ARDCHK : aread_check_stmt B := tfib_ARDCHK B HB.
Let MT_FREE : forall S m, mo_ok ameter_triv S m := fun _ _ => I.
Let xst : nat -> (word -> bool) -> (word -> option byte) -> Prop := YD1k.xst.
Let XFR : xst_frame_tfa xst := tfib_xst_frame.
Let PF1 : printf_first_tfa B xst := tfib_printf_first B HB LAWS HB.
Let PFN : printf_next_tfa B xst := tfib_printf_next B HB LAWS HB.
Let est : (word -> bool) -> (word -> option byte) -> Prop := YD1k.est.
Let ESTI : est_img_tfa est := tfib_est_img.
Let ESTF : est_frame_tfa est := tfib_est_frame.
Let FWS : fwrite_site_tfa B est := tfib_fwrite_site B HB LAWS.
Let RFS : refused_site_tfa B est := tfib_refused_site B HB LAWS HB.
Let FPO : fprintf_s_site_tfa B est YE3j.FMT_open (YO05.strB "cli: cannot open "%string) YO05.nlB :=
  tfib_fprintf_open_site B HB LAWS HB.
Let FPR : fprintf_s_site_tfa B est YE3k.FMT_rderr (YO05.strB "cli: read error on "%string) YO05.nlB :=
  tfib_fprintf_rderr_site B HB LAWS HB.
Let FPU : fprintf_s_site_tfa B est YE3n.FMT_usage (YO05.strB "usage: "%string) (YO05.strB " INPUT"%string ++ YO05.nlB) :=
  tfib_fprintf_usage_site B HB LAWS HB.
Let EXS : exit_site_tfa B est xst := tfib_exit_site B HB LAWS.
Lemma identb_srealizesX_rc : forall sp rdraw brk mb inp,
valid_sp sp -> valid_brk identsegsB0 brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
srealizes identsegsB0
  (init_config identsegsB0 AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mb rdraw target_alloc_limit inp)
  (SPECX (LS:=identity_shape) inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil.
change target_alloc_limit with YA02.LIMIT.
exact (@tfib_srealizesX rc identity_shape B HB AMALLOC AFREE AICPY ARDCHK ameter_triv XL0 XL0 RLO RHI MT_FREE RO_IN LIBX
  xst XFR PF1 PFN est ESTI ESTF FWS RFS FPO FPR FPU EXS sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil).
Qed.
End RC.

(* fuzz_grant's AGrantT.v:75-82. *)
Theorem identb_srealizesX_top : forall sp rdraw brk mb inp,
valid_sp sp -> valid_brk identsegsB0 brk -> valid_mmap_base mb ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
srealizes identsegsB0
  (init_config identsegsB0 AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mb rdraw target_alloc_limit inp)
  (SPECX (LS:=identity_shape) inp).
Proof.
intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp.
exact (@identb_srealizesX_rc (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowX sp Hsp)) sp rdraw brk mb inp
  Hsp Hbrk Hmb Hfit Hinp (YM05.ceil_of_top_run _)).
Qed.

(* IdentityTFIB.TFIB_TB (lib/B/IdentityTFIB.v:20), as fuzz_grant's AGrantT.v:83-84 closes TFIB_T. *)
Theorem identb_TFIB_TB_of_parts : TFIB_TB.
Proof.
intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp.
exact (identb_srealizesX_top sp rnd brk mbase inp Hsp Hbrk Hmb Hfit Hinp).
Qed.

(* The two statements of fuzz_identity's ASan+UBSan build, given only the named parts above (lib/B/AsanUbsanTop.v:30,
   :46). *)
Theorem identb_asan_ubsan_agrees_of_parts : Statements.asan_ubsan_agrees.
Proof. exact (AsanUbsanTop.identity_asan_ubsan_agrees_of_tfib identb_TFIB_TB_of_parts). Qed.
Theorem identb_asan_ubsan_halts_of_parts : Statements.asan_ubsan_halts.
Proof. exact (AsanUbsanTop.identity_asan_ubsan_halts_of_tfib identb_TFIB_TB_of_parts). Qed.

(* Inside the Section, Print Assumptions lists what the two statements rest on: no Section hypothesis is left, so
   only the axioms toolchain/allowed-axioms.txt allows. *)
Print Assumptions identb_asan_ubsan_agrees_of_parts.
Print Assumptions identb_asan_ubsan_halts_of_parts.
End asan_ubsan.
