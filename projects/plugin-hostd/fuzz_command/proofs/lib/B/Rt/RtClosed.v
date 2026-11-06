(* The closing file of the runtime contracts for image B (plugin-hostd/fuzz_command's ASan+UBSan build,
   fuzz_command.asan-ubsan), the twin of lib/A/Rt/RtClosed.v: each proved runtime contract of that image
   restated with its `AR_laws tfibsegs B` premise discharged by the core's own law proof
   (Reusable/YG0q.v:804, `YG0q.AR_laws_ok tfibsegs B`, which is generic in the segment list and the record,
   so it serves B's segments lib/B/YB1v.v:12 as it serves A's), so that only the per-binary record
   `CmdBSyms B` remains. None of these contracts names a further hypothesis, so `CmdBSyms B` (lib/B/YF0m.v:4875)
   is the whole residual. Each theorem stays generic in the floating-point state and the run ceiling. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK15 YK0s YP09 YI04 YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG0v YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB1v YF0m YF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtStack RtShadow RtString RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtNumber.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require
RtShadowProof RtSM0 RtSM1 RtSM3 RtSM4 RtSM5 RtSM7 RtSF5 RtSF7 RtSRegion RtSStrlen RtStrcmpC RtSMemchrNf.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require
RtLStrncmpR RtLStrspn RtLStrcpy RtLStrcat RtLAtoi RtLStrtol.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtFormat RtFSnprintf RtFSprintf.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YE32.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtSStrcspn RtSStrtok2.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YF0p.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YD2l YF0w.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtAlloc RtDDefs RtDStrdupX RtDStrndup.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
(* the per-binary record of fuzz_command.asan-ubsan (B/YF0m.v:4875) *)
Hypothesis HB : CmdBSyms B.

(* __asan_set_shadow_00 (0x5a53c), _f5 (0x5a644), _f8 (0x5a65c) *)
Theorem cmd_set_shadow_00_closed : aset_shadow_realizes tfibsegs B RtShadowProof.SS00_ENTRY 0.
Proof. exact (RtShadowProof.cmd_set_shadow_00 B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
Theorem cmd_set_shadow_f5_closed : aset_shadow_realizes tfibsegs B RtShadowProof.SSF5_ENTRY 0xf5.
Proof. exact (RtShadowProof.cmd_set_shadow_f5 B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
Theorem cmd_set_shadow_f8_closed : aset_shadow_realizes tfibsegs B RtShadowProof.SSF8_ENTRY 0xf8.
Proof. exact (RtShadowProof.cmd_set_shadow_f8 B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.

(* __asan_stack_malloc_0/1/3/4/5 (the whole-frame classes) and _7 (the size-driven class, 0x40290) *)
Theorem cmd_stack_malloc0_contract_closed : astack_malloc_realizes tfibsegs B 0.
Proof. exact (RtSM0.cmd_stack_malloc0_contract B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
Theorem cmd_stack_malloc1_contract_closed : astack_malloc_realizes tfibsegs B 1.
Proof. exact (RtSM1.cmd_stack_malloc1_contract B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
Theorem cmd_stack_malloc3_contract_closed : astack_malloc_realizes tfibsegs B 3.
Proof. exact (RtSM3.cmd_stack_malloc3_contract B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
Theorem cmd_stack_malloc4_contract_closed : astack_malloc_realizes tfibsegs B 4.
Proof. exact (RtSM4.cmd_stack_malloc4_contract B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
Theorem cmd_stack_malloc5_contract_closed : astack_malloc_realizes tfibsegs B 5.
Proof. exact (RtSM5.cmd_stack_malloc5_contract B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
Theorem cmd_stack_malloc7_contract_closed :
astack_malloc_sz_realizes tfibsegs B RtAPI.PC_stack_malloc_7 7.
Proof. exact (RtSM7.cmd_stack_malloc7_contract B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.

(* __asan_stack_free_5 (0x401dc, whole-frame shadow) and _7 (0x4040c, size-driven) *)
Theorem cmd_stack_free5_contract_closed : astack_free_cls_realizes tfibsegs B 0x401dc 5.
Proof. exact (RtSF5.cmd_stack_free5_contract B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
Theorem cmd_stack_free7_contract_closed : astack_free_realizes tfibsegs B 0x4040c 7.
Proof. exact (RtSF7.cmd_stack_free7_contract B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.

(* __asan_region_is_poisoned (0x5a1f8), the range check of every check over 64 bytes *)
Theorem cmd_region_ok_closed : aregion_poisoned_zero_realizes tfibsegs B PC_region_is_poisoned.
Proof. exact (RtSRegion.cmd_region_ok B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.

(* the strlen (0x4517c) and strcmp (0x45188) interceptors *)
Theorem cmd_strlen_closed : astrlen_realizes tfibsegs B PC_strlen.
Proof. exact (RtSStrlen.cmd_strlen B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
Theorem cmd_strcmp_closed : RtString.astrcmp_realizes tfibsegs B PC_strcmp.
Proof. exact (RtStrcmpC.cmd_strcmp B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.

(* the memchr interceptor (0x451a4), memchr(x, 0, n) with no zero byte in the n bytes *)
Theorem cmd_memchr_nf_closed : amemchr0_nf_realizes tfibsegs B PC_memchr.
Proof. exact (RtSMemchrNf.cmd_memchr0_nf B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.

(* the string and number interceptors lifted from the Bz-kit walks (RtL*.v): strncmp (0x4518c), strspn
   (0x45194), strcpy (0x45224), strcat (0x45220), atoi (0x45230) and strtol (0x4522c) *)
Theorem cmd_strncmp_closed : RtString.astrncmp_realizes tfibsegs B PC_strncmp.
Proof. exact (RtLStrncmpR.cmd_strncmp B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
Theorem cmd_strspn_closed : RtString.astrspn_realizes tfibsegs B PC_strspn A_SSP_GOT A_SSP_GUARD.
Proof. exact (RtLStrspn.cmd_strspn B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
Theorem cmd_strcpy_closed : RtString.astrcpy_realizes tfibsegs B PC_strcpy.
Proof. exact (RtLStrcpy.cmd_strcpy B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
Theorem cmd_strcat_closed : RtString.astrcat_realizes tfibsegs B PC_strcat.
Proof. exact (RtLStrcat.cmd_strcat B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
Theorem cmd_atoi_closed : RtNumber.aatoi_realizes tfibsegs B PC_atoi A_FLAG_REPLACE_STR A_SSP_GOT A_SSP_GUARD.
Proof. exact (RtLAtoi.cmd_atoi B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
Theorem cmd_strtol_closed : RtNumber.astrtol_realizes tfibsegs B PC_strtol A_SSP_GOT A_SSP_GUARD.
Proof. exact (RtLStrtol.cmd_strtol B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.

(* snprintf (0x451d0) and sprintf (0x451cc) on omx-clap-core/fuzz_manifest's GXA printf route (RtFSnprintf.v,
   RtFSprintf.v; the world field w_H8 the route uses comes from the core's world record through RtWH8.v's instance) *)
Theorem cmd_snprintf_closed : RtFormat.asnprintf_realizes tfibsegs B PC_snprintf A_SSP_GOT A_SSP_GUARD.
Proof. exact (RtFSnprintf.cmd_snprintf B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
Theorem cmd_sprintf_closed : RtFormat.asprintf_realizes tfibsegs B PC_sprintf A_SSP_GOT A_SSP_GUARD.
Proof. exact (RtFSprintf.cmd_sprintf B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.

(* the memset interceptor 0x57674 in the aintrin_realizes OSet form that RtSStrcspn.cmd_strcspn takes: a Theorem Labs lane's
   relocation of cgif's memset walk (lib/B/YE32.v memset_icpt_realizes), whose statement differs only in where
   amem_range stands among the premises (as lib/B/YD1o.v oset_of_icpt and lib/A/Rt/RtSStrcspn.v cspn_oset read it) *)
Lemma cspn_oset_b : aintrin_realizes tfibsegs B OSet 0x57674.
Proof.
intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull _.
exact (YE32.memset_icpt_realizes B (YG0q.AR_laws_ok tfibsegs B) HB ly S W regs mem md d x n
HPRE G10 G11 G12 Hn Hd Hdn Hdst Hra Hhull Ham).
Qed.

(* the strcspn interceptor (0x45198; its musl body calls the strlen and memset interceptors) and musl's strtok_r
   (which calls the strspn and strcspn interceptors) *)
Theorem cmd_strcspn_closed : RtString.astrcspn_realizes tfibsegs B PC_strcspn A_SSP_GOT A_SSP_GUARD.
Proof. exact (RtSStrcspn.cmd_strcspn B (YG0q.AR_laws_ok tfibsegs B) HB cspn_oset_b). Qed.
Theorem cmd_strtok_r_closed : RtString.astrtok_r_realizes tfibsegs B PC_strtok_r A_SSP_GOT A_SSP_GUARD.
Proof.
exact (RtSStrtok2.cmd_strtok_r B (YG0q.AR_laws_ok tfibsegs B) HB
(RtLStrspn.cmd_strspn B (YG0q.AR_laws_ok tfibsegs B) HB)
(RtSStrcspn.cmd_strcspn B (YG0q.AR_laws_ok tfibsegs B) HB cspn_oset_b)).
Qed.
End closed.

(* The allocator family: asan_malloc (0x34574), the malloc interceptor's body (0x58ba4), strdup (trampoline
   0x45228) and strndup (trampoline 0x45184), from the relocated malloc chain (lib/B/YF0w.v). That chain also takes
   the depot-hash equation [forall t, as_dhash B t = tfib_dhash t], which holds by computation at the pinned record,
   so these are stated at the record itself, CmdB (lib/B/YD2l.v:20), and keep no premise at all. *)
Section closed_record. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Let HD : forall t, as_dhash YD2l.CmdB t = YF0p.tfib_dhash t := fun t => eq_refl.
Theorem cmd_amalloc_inner_closed : RtDDefs.amalloc_inner_realizes tfibsegs YD2l.CmdB RtDDefs.PC_asan_malloc.
Proof. exact (YF0w.cmd_amalloc_inner YD2l.CmdB YD2l.CmdB_syms HD). Qed.
Theorem cmd_amalloc_body_row_closed :
RtDDefs.amalloc_body_realizes tfibsegs YD2l.CmdB RtDDefs.PC_malloc_body PC_STRNDUP_RA0.
Proof. exact (YF0w.cmd_amalloc_body_closed YD2l.CmdB YD2l.CmdB_syms HD). Qed.
Theorem cmd_strdup_closed : RtAlloc.astrdup_realizes tfibsegs YD2l.CmdB PC_strdup PC_STRDUP_RA0.
Proof.
exact (RtDStrdupX.cmd_strdup YD2l.CmdB (YG0q.AR_laws_ok tfibsegs YD2l.CmdB) YD2l.CmdB_syms
(YF0w.cmd_amalloc_inner YD2l.CmdB YD2l.CmdB_syms HD)).
Qed.
Theorem cmd_strndup_closed :
RtAlloc.astrndup_realizes tfibsegs YD2l.CmdB PC_strndup PC_STRNDUP_RA0 PC_STRNDUP_MID.
Proof.
exact (RtDStrndup.cmd_strndup YD2l.CmdB (YG0q.AR_laws_ok tfibsegs YD2l.CmdB) YD2l.CmdB_syms
(YF0w.cmd_amalloc_body_closed YD2l.CmdB YD2l.CmdB_syms HD)).
Qed.
End closed_record.

Print Assumptions cmd_set_shadow_00_closed.
Print Assumptions cmd_set_shadow_f5_closed.
Print Assumptions cmd_set_shadow_f8_closed.
Print Assumptions cmd_stack_malloc0_contract_closed.
Print Assumptions cmd_stack_malloc1_contract_closed.
Print Assumptions cmd_stack_malloc3_contract_closed.
Print Assumptions cmd_stack_malloc4_contract_closed.
Print Assumptions cmd_stack_malloc5_contract_closed.
Print Assumptions cmd_stack_malloc7_contract_closed.
Print Assumptions cmd_stack_free5_contract_closed.
Print Assumptions cmd_stack_free7_contract_closed.
Print Assumptions cmd_region_ok_closed.
Print Assumptions cmd_strlen_closed.
Print Assumptions cmd_strcmp_closed.
Print Assumptions cmd_memchr_nf_closed.
Print Assumptions cmd_strncmp_closed.
Print Assumptions cmd_strspn_closed.
Print Assumptions cmd_strcpy_closed.
Print Assumptions cmd_strcat_closed.
Print Assumptions cmd_atoi_closed.
Print Assumptions cmd_strtol_closed.
Print Assumptions cmd_snprintf_closed.
Print Assumptions cmd_sprintf_closed.
Print Assumptions cmd_strcspn_closed.
Print Assumptions cmd_strtok_r_closed.
Print Assumptions cmd_amalloc_inner_closed.
Print Assumptions cmd_amalloc_body_row_closed.
Print Assumptions cmd_strdup_closed.
Print Assumptions cmd_strndup_closed.
