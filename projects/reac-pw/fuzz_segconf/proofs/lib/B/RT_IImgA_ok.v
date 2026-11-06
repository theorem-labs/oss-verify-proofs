(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/RT_IImgA_ok.v; relocated to plugin-hostd/fuzz_command.asan by the GXA address relocator (target fuzz_command.asan): module paths changed; 0 address numerals moved (address checker 0767e70e074a, predict mode, fm.asan -> fuzz_command.asan, symbol + offset; the relocator's table for this file); GXA symbol keys kept (0x1029e, 0x103b3, 0x10884, 0x10964, 0x10984, 0x109cc, 0x10b9c, 0x15f04, 0x15f44, 0x17d50, 0x17f40, 0x18704, 0x19534, 0x19668, 0x1973c, 0x1ae04, 0x1ae48, 0x1af98, 0x21334, 0x21738, 0x21920, 0x22e18, 0x34288, 0x35000, 0x7f000200, 0x7f000300, 0x7f000400, 0x7f000700, 0x7f000800). *)
(* Modified by Theorem Labs, 2026-10: relocated from lib/A/<same path> to fuzz_command.asan-ubsan by the image-B address relocator (the A-to-B address map, keyed by the image maps' symbol names and by code; GXA symbol keys kept), whose check table lists every changed numeral *)
(* Modified by Theorem Labs, 2026-10: copied from plugin-hostd/fuzz_reply lib/A/RT_IImgA_ok.v;
   the module path prefix is this harness's, the instance is
   RT_IImgA.v's A_img on fuzz_manifest.asan, and the measured addresses in the comments are
   fuzz_manifest's. *)
(* The image facts that lib/CJ/RL/GXA/G_vfprintf_snf_closed.v takes as Context (its lines 29-78),
   proved at RT_IImgA.v's instance A_img on the pinned fuzz_manifest.asan.  Each fact is a
   vm_compute check of code bytes (CodeAtT), of read-only bytes (RoB) or of the symbol map's
   relative layout (RelCode / RelSym / RelNear / ZFact), discharged by IInst.v's `inst` tactic
   exactly as the plain instance's facts are.  A wrong pairing in RT_IImgA.v makes the matching
   lemma here fail, so this file is the instruction-for-instruction check of the pairing, not a
   restatement.  The statements are copied verbatim from those Context lines. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib Require Import SFModel Arr ITree Nodes PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Spec Require Import Prelim Monad FmtFp StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.G Require Import G_memset G_memcpy G_fwritex G_pad G_fmt_fp_lib G_pop_arg GRoTab.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.G Require ProgAt3.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.G.ProgAt3.ProgAt2.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require Import Printf_model Printf_zfacts G_pop_arg_x.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require G_printf_core_common.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require Import G_towrite G_vfprintf_snf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GXA Require Import AsanFacts SetCall StrnlenCall CopyCall VfprintfCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GXA Require G_printf_core_common.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GXA.G_printf_core_common.G_printf_iface.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GXA Require Import G_sn_write G_fwritex_w G_fwritex_room G_printf_core.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GXA Require Import G_vfprintf_snf G_printf_snfsink.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GXA Require G_vsnprintf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import RT_IImgA.
Import ListNotations.
Open Scope Z_scope.

#[local] Existing Instance A_img.
Local Notation GLRN a b := (RelNear (sym a) (sym b)) (only parsing).
Local Notation GLRS a := (RelSym (sym a)) (only parsing).

(* vfprintf and __towrite *)
Lemma fr_CODE_vfprintf : CodeAtT img_segs (sym 0x7f000400) (PROGAT_CODE_vfprintf A_img). Proof. inst. Qed.
Lemma fr_RB_vfprintf : RelCode (sym 0x7f000400) 432. Proof. inst. Qed.
Lemma fr_RN_printf_core : GLRN 0x7f000400 0x18704. Proof. inst. Qed.
Lemma fr_RN_lockfile : GLRN 0x7f000400 0x7f000700. Proof. inst. Qed.
Lemma fr_RN_towrite : GLRN 0x7f000400 0x17f40. Proof. inst. Qed.
Lemma fr_RN_unlockfile : GLRN 0x7f000400 0x7f000800. Proof. inst. Qed.
Lemma fr_RN_stack_chk_fail : GLRN 0x7f000400 0x15f04. Proof. inst. Qed.
Lemma fr_CODE_towrite : CodeAtT img_segs (sym 0x17f40) (PROGAT_CODE_towrite A_img). Proof. inst. Qed.
Lemma fr_RB_towrite : RelCode (sym 0x17f40) 84. Proof. inst. Qed.
(* the string-buffer write callback and __fwritex *)
Lemma fr_CODE_sn_write : CodeAtT img_segs (sym 0x7f000300) (PROGAT_CODE_sn_write A_img). Proof. inst. Qed.
Lemma fr_RS_snw : RelSym (sym K_SN_WRITE). Proof. inst. Qed.
Lemma fr_RB_snw : RelCode (sym K_SN_WRITE) 220. Proof. inst. Qed.
Lemma fr_RN_snw_memcpy : GLRN 0x7f000300 0x21334. Proof. inst. Qed.
Lemma fr_CODE_fwritex : CodeAtT img_segs (sym 0x17d50) (PROGAT_CODE_fwritex A_img). Proof. inst. Qed.
Lemma fr_RB_fwritex : RelCode (sym 0x17d50) 312. Proof. inst. Qed.
Lemma fr_RN_fwritex_memcpy : GLRN 0x17d50 0x21334. Proof. inst. Qed.
(* printf_core *)
Lemma fr_CODE_printf_core : CodeAtT img_segs (sym 0x18704) (printf_core_prog_at A_img). Proof. inst. Qed.
Lemma fr_RB_printf_core : RelCode (sym 0x18704) 3632. Proof. inst. Qed.
Lemma fr_RO_10884 : RoB img_segs (sym 0x10884) ROT_0x10884. Proof. inst. Qed.
Lemma fr_RN_B_fwritex : GLRN 0x18704 0x17d50. Proof. inst. Qed.
Lemma fr_RN_B_pop_arg : GLRN 0x18704 0x19534. Proof. inst. Qed.
Lemma fr_RN_B_fmt_fp : GLRN 0x18704 0x1973c. Proof. inst. Qed.
Lemma fr_RN_B_strnlen : GLRN 0x18704 0x21920. Proof. inst. Qed.
Lemma fr_RN_B_pad : GLRN 0x18704 0x19668. Proof. inst. Qed.
Lemma fr_RN_B_memset : GLRN 0x18704 0x21738. Proof. inst. Qed.
Lemma fr_RN_B_stack_chk_fail : GLRN 0x18704 0x15f04. Proof. inst. Qed.
Lemma fr_RS_K_109cc : GLRS 0x109cc. Proof. inst. Qed.
Lemma fr_RS_K_10884 : GLRS 0x10884. Proof. inst. Qed.
Lemma fr_RS_K_1029e : GLRS 0x1029e. Proof. inst. Qed.
Lemma fr_RS_K_10b9c : GLRS 0x10b9c. Proof. inst. Qed.
Lemma fr_RO_states0 : RoB img_segs (sym 0x109cc) (zb STATES0). Proof. inst. Qed.
Lemma fr_RO_pfx : RoB img_segs (sym 0x1029e) (zb [45; 43; 32; 32; 32; 48; 88; 48; 120]%Z). Proof. inst. Qed.
Lemma fr_RO_xdigits : RoB img_segs (sym 0x10b9c) (zb XDIGITS). Proof. inst. Qed.
Lemma fr_RO_states : RoB img_segs (sym 0x109cc) (zb STATES). Proof. inst. Qed.
(* not one of G_vfprintf_snf_closed.v's Context facts: this lemma checks RT_IImgA.v's FMT_emit row (A_exact key 0x102a8),
   which no other lemma reads *)
Lemma fr_RO_fmt_emit : RoB img_segs (sym 0x102a8) (zb FMT_emit). Proof. inst. Qed.
(* globals: the stack-guard GOT word and the guard *)
Lemma fr_RS_got_ssp : GLRS 0x22e18. Proof. inst. Qed.
Lemma fr_RS_34288 : GLRS 0x34288. Proof. inst. Qed.
Lemma fr_RS_35000 : GLRS 0x35000. Proof. inst. Qed.
Lemma fr_RL0_0 : ZFact (sym 0x22e18 + 8 <= sym 0x34288). Proof. inst. Qed.
Lemma fr_RL0_1 : ZFact (sym 0x34288 + 8 <= sym 0x35000). Proof. inst. Qed.
Lemma fr_RL1_0 : ZFact (sym 0x22e18 + 240 <= sym 0x34288). Proof. inst. Qed.
(* the remaining Context lines of G_vfprintf_snf_closed.v: printf_core's other near calls, its two
   other tables, and the prefix's placement *)
Lemma fr_RN_B_errno_location : GLRN 0x18704 0x15f44. Proof. inst. Qed.
Lemma fr_RN_B_strerror : GLRN 0x18704 0x1ae04. Proof. inst. Qed.
Lemma fr_RN_B_wctomb : GLRN 0x18704 0x1ae48. Proof. inst. Qed.
Lemma fr_RS_K_103b3 : GLRS 0x103b3. Proof. inst. Qed.
Lemma fr_RS_K_10964 : GLRS 0x10964. Proof. inst. Qed.
Lemma fr_RQ_pfx_lo : ZFact (0x10000 <= sym 0x1029e)%Z. Proof. inst. Qed.
Lemma fr_RQ_pfx_got : ZFact (sym 0x1029e + 9 <= sym 0x22e18)%Z. Proof. inst. Qed.

(* musl vsnprintf, at the SECOND instance (RT_IImgA.v A_img_vsn): its call to vfprintf lands on the
   link-time wrapper __wrap_vfprintf 0x41308, not on musl vfprintf's body 0x8ede0; every other row
   is A_img's (A_sym_vsn_agree).  The statements are G_vsnprintf.v's Context lines, with the
   instance written explicitly. *)
Lemma fr_CODE_vsnprintf : CodeAtT (@img_segs A_img_vsn) (@sym A_img_vsn 0x7f000200) (G_vsnprintf.PROGAT_CODE_vsnprintf A_img_vsn). Proof. inst. Qed.
Lemma fr_RB_vsnprintf : RelCode (@sym A_img_vsn 0x7f000200) 204. Proof. inst. Qed.
Lemma fr_RN_vsn_memset : RelNear (@sym A_img_vsn 0x7f000200) (@sym A_img_vsn 0x21738). Proof. inst. Qed.
Lemma fr_RN_vsn_vfprintf : RelNear (@sym A_img_vsn 0x7f000200) (@sym A_img_vsn 0x7f000400). Proof. inst. Qed.
Lemma fr_RN_vsn_stack_chk_fail : RelNear (@sym A_img_vsn 0x7f000200) (@sym A_img_vsn 0x15f04). Proof. inst. Qed.
Lemma fr_RQ_vsn_22e18 : ZFact (0x14000 <= @sym A_img_vsn 0x22e18). Proof. inst. Qed.
(* the rows G_vsnprintf.v also takes, at the second instance.  A_sym_vsn differs from A_sym only at
   0x7f000400 and none of these is that row, but each is checked against the image here again. *)
Lemma fr_RS_vsn_got_ssp : RelSym (@sym A_img_vsn 0x22e18). Proof. inst. Qed.
Lemma fr_RS_vsn_snw : RelSym (@sym A_img_vsn K_SN_WRITE). Proof. inst. Qed.
Lemma fr_RS_vsn_34288 : RelSym (@sym A_img_vsn 0x34288). Proof. inst. Qed.
Lemma fr_RS_vsn_35000 : RelSym (@sym A_img_vsn 0x35000). Proof. inst. Qed.
Lemma fr_RL0_0_vsn : ZFact (@sym A_img_vsn 0x22e18 + 8 <= @sym A_img_vsn 0x34288). Proof. inst. Qed.
Lemma fr_RL0_1_vsn : ZFact (@sym A_img_vsn 0x34288 + 8 <= @sym A_img_vsn 0x35000). Proof. inst. Qed.

(* musl pop_arg and the builtin __extenddftf2 it calls (both called directly in this build, not
   wrapped): G/G_pop_arg.v:441-446 and GX/G_pop_arg_x.v:33-37 take these image facts.  With them,
   the released proofs pop_arg_contract_ok (G_pop_arg.v:611), pop_arg_x_contract_ok
   (G_pop_arg_x.v:74) and extenddftf2_contract_ok (G_pop_arg.v:289) close at A_img: these are GXA's
   SPEC_pop_arg / SPEC_pop_arg_x call contracts, DISCHARGED. *)
Lemma fr_CODE_extenddftf2 : CodeAtT img_segs (sym 0x1af98) (G_extenddftf2.PROGAT_CODE_extenddftf2 A_img). Proof. inst. Qed.
Lemma fr_RB_extenddftf2 : RelCode (sym 0x1af98) 400. Proof. inst. Qed.
Lemma fr_CODE_pop_arg : CodeAtT img_segs (sym 0x19534) (PROGAT_CODE_pop_arg A_img). Proof. inst. Qed.
Lemma fr_RB_pop_arg : RelCode (sym 0x19534) 308. Proof. inst. Qed.
Lemma fr_RO_10984 : RoB img_segs (sym 0x10984) ROT_0x10984. Proof. inst. Qed.
Lemma fr_RN_B_extenddftf2 : RelNear (sym 0x19534) (sym 0x1af98). Proof. inst. Qed.
Lemma fr_RS_K_10984 : RelSym (sym 0x10984). Proof. inst. Qed.

Lemma fr_extenddftf2_contract : @G_extenddftf2.extenddftf2_contract A_img.
Proof.
unshelve eapply G_extenddftf2.extenddftf2_contract_ok.
all: first [exact fr_CODE_extenddftf2 | exact fr_RB_extenddftf2].
Qed.
Lemma fr_pop_arg_contract : @pop_arg_contract A_img.
Proof.
unshelve eapply pop_arg_contract_ok.
all: first [exact fr_CODE_pop_arg | exact fr_RB_pop_arg | exact fr_RO_10984 | exact fr_RN_B_extenddftf2
          | exact fr_RS_K_10984 | exact fr_extenddftf2_contract].
Qed.
Lemma fr_pop_arg_x_contract : @pop_arg_x_contract A_img.
Proof.
unshelve eapply pop_arg_x_contract_ok.
all: first [exact fr_CODE_pop_arg | exact fr_RB_pop_arg | exact fr_RO_10984 | exact fr_RN_B_extenddftf2
          | exact fr_RS_K_10984 | exact fr_extenddftf2_contract | exact fr_pop_arg_contract].
Qed.
