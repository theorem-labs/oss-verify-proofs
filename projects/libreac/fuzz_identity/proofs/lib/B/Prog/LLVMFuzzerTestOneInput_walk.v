(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the contract of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACfn.v:33-69
   (tfib_lib_pre_x, tfib_lib_post_x, tfib_lib_contract_x) restated for libreac/fuzz_identity's ASan+UBSan
   build: the module paths are this unit's lib.B, the image is the position-abstract one (pa_segs,
   BASE + AF_LLVMFuzzerTestOneInput of identb_listing), the library shape and every constant of the unit's
   relocated core are parameters of the Section, and the measured needs of this build's entry (events, live
   bytes, stack) are stated beside it. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput.v; 45 of its 172 lines of code are new or changed and 100 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput's ASan+UBSan walk (image B, fuzz_identity.asan-ubsan 0x80774 = BASE +
   AF_LLVMFuzzerTestOneInput): the contract tLLVMFuzzerTestOneInput_spec (LLVMFuzzerTestOneInput.v), proved under
   exactly the contract's Section hypotheses. The proof is one application of the composition
   LLVMFuzzerTestOneInput_top.pb_from_segs (the segment statements of LLVMFuzzerTestOneInput_inv.v chained from the
   entry to the return, srealizes, no cut) to HLIBK and the 21 segment lemmas seg_A .. seg_L and seg_early, each
   applied to the contract hypotheses it takes. Section c below is the contract's Section c with its Definitions
   left out; the four names the contract defines inside its Section are applied to their Section arguments here
   (LLVMF_MALLOC_CTX RA_LLVMF, LLVMF_FREE_CTX RA_LLVMF, CTX_BUF_OF RA_LLVMF, llvmf_img B G), as the segment files
   state them. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require
buf_of check_str put_dec reac_box_catalogue reac_box_catalogue_defect reac_box_family_of reac_box_family_stem
reac_box_name reac_identity_fw_str reac_identity_init reac_identity_ingest reac_identity_reac_ver_str.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import StrlenDef StrcmpDef MemchrDef SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require LLVMFuzzerTestOneInput_top.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require
LLVMFuzzerTestOneInput_seg_A LLVMFuzzerTestOneInput_seg_B LLVMFuzzerTestOneInput_seg_C LLVMFuzzerTestOneInput_seg_D1 LLVMFuzzerTestOneInput_seg_D2 LLVMFuzzerTestOneInput_seg_D3r LLVMFuzzerTestOneInput_seg_D3 LLVMFuzzerTestOneInput_seg_D4 LLVMFuzzerTestOneInput_seg_D5 LLVMFuzzerTestOneInput_seg_D6 LLVMFuzzerTestOneInput_seg_loop LLVMFuzzerTestOneInput_seg_rec_exit LLVMFuzzerTestOneInput_seg_E LLVMFuzzerTestOneInput_seg_F LLVMFuzzerTestOneInput_seg_G LLVMFuzzerTestOneInput_seg_H LLVMFuzzerTestOneInput_seg_I LLVMFuzzerTestOneInput_seg_J LLVMFuzzerTestOneInput_seg_K LLVMFuzzerTestOneInput_seg_L 
LLVMFuzzerTestOneInput_seg_early.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* A segment lemma, applied to the contract hypotheses it takes (found in the context of Section c). *)
Ltac walk_seg L := eapply L; eassumption.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable LS : lib_shape.
Hypothesis HLIBK : forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs []).
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Hypothesis HLIVE : LIVE_LLVMF <= LIVE_LIB.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis PSIG : identb_prog_sig_ok (PI := PI).
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis HMT0 : forall s s' : astate, mo_le MT s s' 0.
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Variable G : list (Z * Z).
Hypothesis GM : globs_marked SEGS B G.
Hypothesis IV : img_shadow_vis SEGS B.
Hypothesis G_HW : In (VAL (A_OBJ 6), 36) G.
Hypothesis G_SW : In (VAL (A_OBJ 7), 24) G.
Hypothesis G_CAT : In (VAL (A_OBJ 28), 3256) G.
Hypothesis G_X : In (VAL (A_OBJ 4), 2) G.
Hypothesis G_PAREN : In (VAL (A_OBJ 9), 3) G.
Hypothesis G_IN : In (VAL (A_OBJ 10), 7) G.
Hypothesis G_OUT : In (VAL (A_OBJ 11), 6) G.
Hypothesis G_REAC : In (VAL (A_OBJ 8), 5) G.
Hypothesis HXM : forall n, EV_LLVMF * (mo_malloc MT 256 + mo_free MT) <= XM_LIB n.
Hypothesis HXN : forall n, EV_LLVMF * (mo_malloc MT 256 + mo_free MT) <= XN_LIB n.
Hypothesis HUMM : forall c, In c (LLVMF_MALLOC_CTX RA_LLVMF) ->
In (firstn kUnwindMax (pc_malloc_ra0 (as_code B)
:: flat_map (fun r => if r =? pc_malloc_ra0 (as_code B) then [] else [r]) c)) (as_universe B).
Hypothesis HUMF : forall c, In c (LLVMF_FREE_CTX RA_LLVMF) ->
In (firstn kUnwindMax (pc_free_ra0 (as_code B)
:: flat_map (fun r => if r =? pc_free_ra0 (as_code B) then [] else [r]) c)) (as_universe B).
Hypothesis HIMG : forall (W : world SEGS) mem,
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> llvmf_img B G W mem.
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis ASM4 : astack_malloc_realizes SEGS B 4.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA IB___asan_memset).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA IB___asan_memcpy).
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA IB___interceptor_trampoline_bcmp).
Hypothesis AMEMCHR : amemchr_realizes SEGS B (SIGMA IB___interceptor_trampoline_memchr).
Hypothesis ASTRLEN : astrlen_realizes SEGS B (SIGMA IB___interceptor_trampoline_strlen).
Hypothesis ASTRCMP : astrcmp_realizes SEGS B (SIGMA IB___interceptor_trampoline_strcmp).
Hypothesis ASSF5 : aset_shadow_realizes SEGS B (SIGMA IB___asan_set_shadow_f5) 0xf5.
Hypothesis AJ_FP_NIL : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Hypothesis SRZ_ENTER : forall (W : world SEGS) (c : config) (T : TSet),
AI SEGS (w_H W) (w_A W) (cfg_model c) ->
SRr SEGS W c (fun W' c' => AI SEGS (w_H W') (w_A W') (cfg_model c') -> srealizes SEGS c' T) ->
srealizes SEGS c T.
Hypothesis ASINK_NONE_KEPT : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
~ YI16.sink_open_fp FP ->
asink_none SEGS KS (rd W mem) md -> asink_none SEGS KS (rd W' mem') md'.
Hypothesis AMETA_INV_KEPT : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k M,
ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
ameta_inv SEGS KS ly (rd W mem) M -> ameta_inv SEGS KS ly' (rd W' mem') M.
Hypothesis HCHK : check_str.tcheck_str_spec B.
Hypothesis HCAT : reac_box_catalogue.tcat_spec B.
Hypothesis HCATD : reac_box_catalogue_defect.treac_box_catalogue_defect_spec B G.
Hypothesis HSTEM : reac_box_family_stem.treac_box_family_stem_spec B.
Hypothesis HFWS : reac_identity_fw_str.treac_identity_fw_str_spec B.
Hypothesis HINIT : reac_identity_init.treac_identity_init_spec B (BASE + AF_reac_identity_init).
Hypothesis HING : reac_identity_ingest.treac_identity_ingest_spec B.
Hypothesis HFAM : reac_box_family_of.treac_box_family_of_spec B.
Hypothesis HVS : reac_identity_reac_ver_str.treac_identity_reac_ver_str_spec B.
Hypothesis HPD : put_dec.tput_dec_spec B.
Hypothesis HBN : reac_box_name.treac_box_name_spec B G.
Hypothesis HBUF : buf_of.tbuf_of_spec B MT (CTX_BUF_OF RA_LLVMF).

Theorem pb_LLVMFuzzerTestOneInput : @tLLVMFuzzerTestOneInput_spec fx rc SK PI B MT XM_LIB XN_LIB RLO RHI LS
RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS.
(* Every Section variable and hypothesis, so that the closed theorem takes exactly the contract's, in its order. *)
Proof using All.
pose proof (@LLVMFuzzerTestOneInput_top.pb_from_segs fx rc SK PI B MT XM_LIB XN_LIB RLO RHI LS RA_LLVMF A_EMPTY
LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS HLIBK) as P.
unfold pb_LLVMFuzzerTestOneInput_stmt in P.
apply P; clear P.
- walk_seg LLVMFuzzerTestOneInput_seg_A.seg_A.
- walk_seg LLVMFuzzerTestOneInput_seg_B.seg_B.
- walk_seg LLVMFuzzerTestOneInput_seg_C.seg_C.
- walk_seg LLVMFuzzerTestOneInput_seg_D1.seg_D1.
- walk_seg LLVMFuzzerTestOneInput_seg_D2.seg_D2.
- walk_seg LLVMFuzzerTestOneInput_seg_D3r.seg_D3r.
- walk_seg LLVMFuzzerTestOneInput_seg_D3.seg_D3.
- walk_seg LLVMFuzzerTestOneInput_seg_D4.seg_D4.
- walk_seg LLVMFuzzerTestOneInput_seg_D5.seg_D5.
- walk_seg LLVMFuzzerTestOneInput_seg_D6.seg_D6.
- walk_seg LLVMFuzzerTestOneInput_seg_loop.seg_loop.
- walk_seg LLVMFuzzerTestOneInput_seg_rec_exit.seg_rec_exit.
- walk_seg LLVMFuzzerTestOneInput_seg_E.seg_E.
- walk_seg LLVMFuzzerTestOneInput_seg_F.seg_F.
- walk_seg LLVMFuzzerTestOneInput_seg_G.seg_G.
- walk_seg LLVMFuzzerTestOneInput_seg_H.seg_H.
- walk_seg LLVMFuzzerTestOneInput_seg_I.seg_I.
- walk_seg LLVMFuzzerTestOneInput_seg_J.seg_J.
- walk_seg LLVMFuzzerTestOneInput_seg_K.seg_K.
- walk_seg LLVMFuzzerTestOneInput_seg_L.seg_L.
- walk_seg LLVMFuzzerTestOneInput_seg_early.seg_early.
Qed.

Print Assumptions pb_LLVMFuzzerTestOneInput.

End c.
End b.
End a.

Check @pb_LLVMFuzzerTestOneInput.
Print Assumptions pb_LLVMFuzzerTestOneInput.
Set Printing All.
Print pb_LLVMFuzzerTestOneInput.
