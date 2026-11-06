(* The closing file of reac-pw/fuzz_segconf image B's interceptor layer (fuzz_segconf.asan-ubsan): the image-B twin of
   lib/A/Rt/SegRtClosed.v (commit 895530bdd2a0; the role of plugin-hostd/fuzz_command's lib/B/Rt/RtClosed.v at
   501c0d516c69), the same theorems over image B's files: each row of the interceptor interface
   (provenance/evidence/interceptors/INTERFACE-A-interceptors.md, rule 4) restated with its `AR_laws tfibsegs B` premise
   discharged by the kit's own law proof (Reusable/YG0q.v:804, `YG0q.AR_laws_ok tfibsegs B`), so that only the per-binary
   record `SegBSyms B` (B/YF0m.v) remains. Each theorem stays generic in the floating-point state and the run
   ceiling. Image: fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3...; the entry addresses are the unstripped twin's
   .symtab values (sha256 80e82127e8ca...), as lib/B/Rt/RtAPI.v names them. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK15 YK0s YP09 YI04 YK04 YM05 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v YF0m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtStack RtString RtAPI.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require
RtSM5 RtSF5 RtSStrlen RtStrcmpC RtLStrncmpR RtLStrspn Memchr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtSeg SegRtPC.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require
RtLStrchr RtLStrncasecmp RtLStrstr RtLIsalnum RtLStrcasecmp RtLStrrchr RtLStrtol0 RtLStrncpy.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtFormat RtPFCmd RtPFSeg RtFSnprintfSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YCbp.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YF0p.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YE2k YD2l YE2s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtSegCalloc RtLCalloc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* Row 20's window: the two 8-byte words musl memchr (0x9aaa4) reads in its word loop. On the image-B pin,
   0x9aafc auipc a3,0xfff76 / 0x9ab00 ld a3,-1940(a3) loads the word at 0x10368 (0x0101010101010100) and
   0x9ab04 auipc a4,0xfff76 / 0x9ab08 ld a4,-1972(a4) loads the word at 0x10350 (0x8080808080808080); both lie in
   the first PT_LOAD (vaddr 0x10000, R only), at the same addresses as in image A. lib/B/Prog/SegInstB.v names the
   same numerals memchr_loA / memchr_hiA. *)
Definition memchr_lo : Z := 0x10350.
Definition memchr_hi : Z := 0x10370.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
(* the per-binary record of fuzz_segconf.asan (A/YF0m.v) *)
Hypothesis HB : SegBSyms B.

(* row 1: the strncmp interceptor (__interceptor_trampoline_strncmp 0x43aa4), lifted from the Bz-kit walk *)
Theorem seg_strncmp_closed : RtString.astrncmp_realizes tfibsegs B PC_strncmp.
Proof. exact (RtLStrncmpR.cmd_strncmp B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.

(* row 2: the strspn interceptor (0x43abc); musl strspn reads the stack-protector GOT word and guard *)
Theorem seg_strspn_closed : RtString.astrspn_realizes tfibsegs B PC_strspn A_SSP_GOT A_SSP_GUARD.
Proof. exact (RtLStrspn.cmd_strspn B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.

(* row 14: __asan_stack_malloc_5 (0x3eab8), a whole-frame class *)
Theorem seg_stack_malloc5_closed : YG0d.astack_malloc_realizes tfibsegs B 5.
Proof. exact (RtSM5.cmd_stack_malloc5_contract B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.

(* row 15: __asan_stack_free_5 (0x3ecc4, whole-frame shadow); its walk RtSF5 compiles on image B, whose start-up
   record carries the 0xf5 fill word's cell (0x10338) *)
Theorem seg_stack_free5_closed : RtStack.astack_free_cls_realizes tfibsegs B RtAPI.PC_stack_free_5 5.
Proof. exact (RtSF5.cmd_stack_free5_contract B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.

(* rows 16 and 17: the strlen (0x43a98) and strcmp (0x43aa0) interceptors *)
Theorem seg_strlen_closed : RtString.astrlen_realizes tfibsegs B PC_strlen.
Proof. exact (RtSStrlen.cmd_strlen B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
Theorem seg_strcmp_closed : RtString.astrcmp_realizes tfibsegs B PC_strcmp.
Proof. exact (RtStrcmpC.cmd_strcmp B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.

(* row 20: the memchr interceptor (0x43ac8) at all three sites: any byte c, n < 2^32, found or not found,
   over musl memchr's word-constant window [memchr_lo, memchr_hi) *)
Theorem seg_memchr_closed : MemchrDef.amemchr_realizesM tfibsegs B memchr_lo memchr_hi PC_memchr.
Proof. exact (Memchr.memchr_icpt_realizesM B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.

(* ---- the closings of the other rows, re-exported here as each lands ---- *)

(* rows 6-9 (commit 04abba419ff7): strchr (0x43ab4), strncasecmp (0x43aac), strstr
   (0x43ab0) and isalnum (musl's, 0x9094c, called directly); their posts in SegModel's terms are lib/A/Rt/RtLFmModel.v.
   isalnum reads no runtime cell, so its closing does not take the record. *)
Theorem seg_strchr_closed : RtSeg.astrchr_realizes tfibsegs B SegRtPC.PC_strchr.
Proof. exact (RtLStrchr.seg_strchr_closed B HB). Qed.
Theorem seg_strncasecmp_closed : RtSeg.astrncasecmp_realizes tfibsegs B SegRtPC.PC_strncasecmp.
Proof. exact (RtLStrncasecmp.seg_strncasecmp_closed B HB). Qed.
Theorem seg_strstr_closed :
RtSeg.astrstr_realizes tfibsegs B SegRtPC.PC_strstr RtAPI.A_SSP_GOT RtAPI.A_SSP_GUARD.
Proof. exact (RtLStrstr.seg_strstr_closed B HB). Qed.
Theorem seg_isalnum_closed : RtSeg.aisalnum_realizes tfibsegs B SegRtPC.PC_isalnum.
Proof. exact (RtLIsalnum.seg_isalnum_closed B). Qed.

(* row 10 (commit 26143c78b97f): strcasecmp (0x43aa8); its post in SegModel's terms is
   lib/A/Rt/RtLStrcasecmpM.v (casecmp_post_model) *)
Theorem seg_strcasecmp_closed : RtSeg.astrcasecmp_realizes tfibsegs B SegRtPC.PC_strcasecmp.
Proof. exact (RtLStrcasecmp.seg_strcasecmp_closed B HB). Qed.

(* row 11 (commit bd8a77380141): strrchr (0x43ab8); its post in SegModel's terms is RtLStrrchr.seg_strrchr_model *)
Theorem seg_strrchr_closed : RtSeg.astrrchr_realizes tfibsegs B SegRtPC.PC_strrchr.
Proof. exact (RtLStrrchr.seg_strrchr_closed B HB). Qed.

(* row 3 (commit 974c1799c680): strtol (0x43b44) with a NULL end pointer *)
Theorem seg_strtol0_closed : RtSeg.astrtol0_realizes tfibsegs B RtAPI.PC_strtol RtAPI.A_SSP_GOT RtAPI.A_SSP_GUARD.
Proof. exact (RtLStrtol0.seg_strtol0_closed B HB). Qed.

(* row 12 (commit 72c15d54ad72): strncpy (0x43b40) *)
Theorem seg_strncpy_closed : RtSeg.astrncpy_realizes tfibsegs B SegRtPC.PC_strncpy.
Proof. exact (RtLStrncpy.seg_strncpy_closed B HB). Qed.

(* rows 4 and 5 (commit 4ab8ed78f4eb): snprintf (0x43af0) and vsnprintf (0x43ae8, the caller's va_list) over
   segconf's piece grammar, and snprintf in RtFormat's text *)
Theorem seg_snprintf_closed : RtPFSeg.seg_asnprintf_realizes tfibsegs B RtPFCmd.CMD_IMG_LO RtPFCmd.CMD_IMG_HI
RtPFCmd.CMD_SNP_CR RtAPI.PC_snprintf RtAPI.A_SSP_GOT RtAPI.A_SSP_GUARD.
Proof. exact (RtFSnprintfSeg.seg_snprintf_closed B HB). Qed.
Theorem seg_vsnprintf_closed : RtPFSeg.seg_avsnprintf_realizes tfibsegs B RtPFCmd.CMD_IMG_LO RtPFCmd.CMD_IMG_HI
RtPFCmd.CMD_SNP_CR SegRtPC.PC_vsnprintf RtAPI.A_SSP_GOT RtAPI.A_SSP_GUARD.
Proof. exact (RtFSnprintfSeg.seg_vsnprintf_closed B HB). Qed.
Theorem seg_rtformat_closed : RtFormat.asnprintf_realizes tfibsegs B RtAPI.PC_snprintf RtAPI.A_SSP_GOT RtAPI.A_SSP_GUARD.
Proof. exact (RtFSnprintfSeg.seg_rtformat_closed B HB). Qed.

(* row 13 (commit e70080ec7000): calloc (0x56cc4). The record's depot hash agreeing with the image's is a premise of the
   statement: SegBSyms B does not give it for every trace. The instance at YD2l.SegB, with no premise, follows End closed. *)
Theorem seg_acalloc_closed : (forall t, as_dhash B t = YF0p.tfib_dhash t) -> forall fx0 : YK11.FPState,
@RtSegCalloc.aseg_calloc04_rule fx0 rc YE2k.tfib_sink_head tfibsegs B YCbp.ameter_triv SegRtPC.PC_calloc
RtLCalloc.SEG_CALLOC_CSTK.
Proof. intros HDH fx0. exact (@RtLCalloc.seg_acalloc_closed rc B HB HDH fx0). Qed.

(* row 19 (image-B frame file lib/B/YE2s.v, the twin of the image-A frame's AE2s.v): bcmp
   (__interceptor_trampoline_bcmp 0x43ac4), the kit's text closed by the frame *)
Theorem seg_bcmp_closed : YG0d.abcmp_realizes tfibsegs B 0x43ac4.
Proof. exact (YE2s.bcmp_icpt_contract B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.

End closed.

(* row 13 at the image's own record YD2l.SegB *)
Theorem seg_acalloc_closed_segB : forall (rc : YM05.RunCeil) (fx0 : YK11.FPState),
@RtSegCalloc.aseg_calloc04_rule fx0 rc YE2k.tfib_sink_head tfibsegs YD2l.SegB YCbp.ameter_triv SegRtPC.PC_calloc
RtLCalloc.SEG_CALLOC_CSTK.
Proof. exact RtLCalloc.seg_acalloc_closed_segB. Qed.

Print Assumptions seg_strncmp_closed.
Print Assumptions seg_strspn_closed.
Print Assumptions seg_stack_malloc5_closed.
Print Assumptions seg_strlen_closed.
Print Assumptions seg_strcmp_closed.
Print Assumptions seg_memchr_closed.
Print Assumptions seg_strchr_closed.
Print Assumptions seg_strncasecmp_closed.
Print Assumptions seg_strstr_closed.
Print Assumptions seg_isalnum_closed.
Print Assumptions seg_strcasecmp_closed.
Print Assumptions seg_strrchr_closed.
Print Assumptions seg_strtol0_closed.
Print Assumptions seg_strncpy_closed.
Print Assumptions seg_snprintf_closed.
Print Assumptions seg_vsnprintf_closed.
Print Assumptions seg_rtformat_closed.
Print Assumptions seg_acalloc_closed.
Print Assumptions seg_acalloc_closed_segB.
