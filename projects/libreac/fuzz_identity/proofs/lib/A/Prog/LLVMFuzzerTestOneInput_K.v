(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:1527-1530,
   1556-1561, for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_D4.v, with its module names changed; 39 of its 89 lines of code are new or changed and 888 lines of the source are left out. *)
(* seg_K of lib/A/Prog/LLVMFuzzerTestOneInput_inv.v (fuzz_identity.asan 0x81e60 .. 0x82090, 140 slots), composed
   from the pieces proved for it:
     LLVMFuzzerTestOneInput_Klib.v  k_rne    the r <> 0 path, 0x81e60 -> 0x82090
                                    k_pairA  0x81e60 -> 0x81e88: the r = 0 branch, strlen (nm), check_str (nm)
                                    k_pairC  0x81ea0 -> 0x81eb8: strlen (dp), check_str (dp)
                                    seg_K_of_pieces  the composition
     LLVMFuzzerTestOneInput_KpB.v   k_pairB  0x81e88 -> 0x81ea0: strlen (tk), check_str (tk)
     LLVMFuzzerTestOneInput_Kcmp.v  k_cmp    0x81eb8 -> 0x81f00: the two strcmp and the loop set-up
     LLVMFuzzerTestOneInput_Ktok.v  k_token_loop  0x81f00 -> 0x81fa0: the token loop
     LLVMFuzzerTestOneInput_Kcat.v  k_cat_tail    0x81fa0 -> 0x82090: catalogue, defect, the mask compare
   The cut points and the statements of the five pieces are LLVMFuzzerTestOneInput_Kcut.v's. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String Ascii.
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig IdentBlkTail YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Rt Require Import StrlenDef WrapRo.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import AStrcmpDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YK1g.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_Kcut check_str
LLVMFuzzerTestOneInput_Klib LLVMFuzzerTestOneInput_KpB LLVMFuzzerTestOneInput_Kcmp LLVMFuzzerTestOneInput_Ktok
LLVMFuzzerTestOneInput_Kcat reac_box_catalogue reac_box_catalogue_defect.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
Section c.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
(* what the pieces take, each as the contract's Section states it (LLVMFuzzerTestOneInput.v) *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis TL : PALib B.
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Hypothesis PSIG : ident_prog_sig_ok (PI := PI).
Hypothesis ASTRLEN : astrlen_realizes SEGS B (SIGMA IS___interceptor_trampoline_strlen).
Hypothesis ASTRCMP : AStrcmpDef.astrcmp_realizes SEGS B (SIGMA IS___interceptor_trampoline_strcmp).
Hypothesis HCHK : check_str.tcheck_str_spec B.
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.


(* The window of kpre's first keep clause is check_str's, 16 + 2 * ESTACK = 8208 bytes below sp = mf
   (check_str.v:70, ESTACK = 4096 at YG0d.v:19). Every callee reached inside seg_K's range writes only inside
   its own window, and each of those windows fits in it:
     wrapper strlen                2 * ESTACK = 8192   lib/A/Rt/StrlenDef.v:39,43,53
     wrapper strcmp                2 * ESTACK = 8192   lib/Reusable/AStrcmpDef.v:47,52,62
     check_str                     16 + 2 * ESTACK     lib/A/Prog/check_str.v:70
     reac_box_catalogue            16 + ESTACK = 4112  lib/A/Prog/reac_box_catalogue.v:48
     reac_box_catalogue_defect     16 + 2 * ESTACK     lib/A/Prog/reac_box_catalogue_defect.v:86
   (seg_K calls no other function: the only calls in 0x81e60 .. 0x82090 are those five.) *)
Lemma k_callee_windows_fit :
2 * ESTACK <= check_str.CHECK_STR_STK /\
reac_box_catalogue.CAT_STK <= check_str.CHECK_STR_STK /\
reac_box_catalogue_defect.REAC_BOX_CATALOGUE_DEFECT_STK <= check_str.CHECK_STR_STK /\
check_str.CHECK_STR_STK = 8208.
Proof.
unfold check_str.CHECK_STR_STK, reac_box_catalogue.CAT_STK,
  reac_box_catalogue_defect.REAC_BOX_CATALOGUE_DEFECT_STK, ESTACK. repeat split; lia.
Qed.

(* What the catalogue tail needs in addition, each as the contract's Section states it. *)
Variable G : list (Z * Z).
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Hypothesis GM : globs_marked SEGS B G.
Hypothesis IV : img_shadow_vis SEGS B.
Hypothesis G_CAT : In (@pa_val _ ident_listing PI (A_OBJ 27), 3256) G.
Hypothesis HIMG : forall (W : world SEGS) mem,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> llvmf_img B G W mem.
Hypothesis HCAT : tcat_spec B (@pa_val _ ident_listing PI A_TEXT + AF_reac_box_catalogue) pa_relro_lo pa_relro_hi.
Hypothesis HCATD : treac_box_catalogue_defect_spec B G.

(* seg_K: the segment statement of lib/A/Prog/LLVMFuzzerTestOneInput_inv.v, from its six pieces. *)
Theorem seg_K_holds :
seg_K B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
  arodata_okS.
Proof.
apply seg_K_of_pieces; try assumption.
- apply k_pairB; assumption.
- apply k_cmp; assumption.
- apply k_token_loop; assumption.
- eapply k_cat_tail; eassumption.
Qed.
End c.
End b.
End a.
