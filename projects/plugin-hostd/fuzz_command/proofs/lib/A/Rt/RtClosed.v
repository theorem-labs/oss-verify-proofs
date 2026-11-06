(* The closing file of the runtime contracts (the walks' closing pattern, on the worked example
   A/Prog/SupRemoveAllRefitClosed.v): each proved runtime contract of plugin-hostd/fuzz_command's ASan build
   restated with its `AR_laws tfibsegs B` premise discharged by the core's own law proof
   (Reusable/YG0q.v:804, `YG0q.AR_laws_ok tfibsegs B`), so that only the per-binary record `CmdBSyms B`
   remains. None of these contracts names a further hypothesis, so `CmdBSyms B` is the whole residual.
   Each theorem stays generic in the floating-point state and the run ceiling. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v AF0m AF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtStack RtShadow RtString RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtNumber.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require
RtShadowProof RtSM0 RtSM1 RtSM3 RtSM4 RtSM5 RtSM7 RtSF5 RtSF7 RtSRegion RtSStrlen RtStrcmpC RtSMemchrNf.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require
RtLStrncmpR RtLStrspn RtLStrcpy RtLStrcat RtLAtoi RtLStrtol.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtSStrcspn RtSStrtok2.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtFormat RtFSnprintf RtFSprintf.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YF0p.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AD2l AF0w.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtAlloc RtDDefs RtDStrdupX RtDStrndup.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
(* the per-binary record of fuzz_command.asan (A/AF0m.v:4874) *)
Hypothesis HB : CmdBSyms B.

(* __asan_set_shadow_00 (0x5a4f0), _f5 (0x5a5f8), _f8 (0x5a610) *)
Theorem cmd_set_shadow_00_closed : aset_shadow_realizes tfibsegs B RtShadowProof.SS00_ENTRY 0.
Proof. exact (RtShadowProof.cmd_set_shadow_00 B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
Theorem cmd_set_shadow_f5_closed : aset_shadow_realizes tfibsegs B RtShadowProof.SSF5_ENTRY 0xf5.
Proof. exact (RtShadowProof.cmd_set_shadow_f5 B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
Theorem cmd_set_shadow_f8_closed : aset_shadow_realizes tfibsegs B RtShadowProof.SSF8_ENTRY 0xf8.
Proof. exact (RtShadowProof.cmd_set_shadow_f8 B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.

(* __asan_stack_malloc_0/1/3/4/5 (the whole-frame classes) and _7 (the size-driven class) *)
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

(* __asan_stack_free_5 (0x40190, whole-frame shadow) and _7 (0x403c0, size-driven) *)
Theorem cmd_stack_free5_contract_closed : astack_free_cls_realizes tfibsegs B 0x40190 5.
Proof. exact (RtSF5.cmd_stack_free5_contract B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
Theorem cmd_stack_free7_contract_closed : astack_free_realizes tfibsegs B 0x403c0 7.
Proof. exact (RtSF7.cmd_stack_free7_contract B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.

(* __asan_region_is_poisoned (0x5a1ac), the range check of every check over 64 bytes *)
Theorem cmd_region_ok_closed : aregion_poisoned_zero_realizes tfibsegs B PC_region_is_poisoned.
Proof. exact (RtSRegion.cmd_region_ok B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.

(* the strlen (0x45130) and strcmp (0x4513c) interceptors *)
Theorem cmd_strlen_closed : astrlen_realizes tfibsegs B PC_strlen.
Proof. exact (RtSStrlen.cmd_strlen B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
Theorem cmd_strcmp_closed : RtString.astrcmp_realizes tfibsegs B PC_strcmp.
Proof. exact (RtStrcmpC.cmd_strcmp B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.

(* the memchr interceptor (0x45158), memchr(x, 0, n) with no zero byte in the n bytes *)
Theorem cmd_memchr_nf_closed : amemchr0_nf_realizes tfibsegs B PC_memchr.
Proof. exact (RtSMemchrNf.cmd_memchr0_nf B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.

(* the string and number interceptors lifted from the Bz-kit walks (RtL*.v): strncmp (0x45140), strspn
   (0x45148), strcpy (0x451d8), strcat (0x451d4), atoi (0x451e4) and strtol (0x451e0) *)
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

(* the strcspn interceptor (0x4514c; its musl body calls the strlen and memset interceptors) and musl's strtok_r
   (0x9f804, which calls the strspn and strcspn interceptors) *)
Theorem cmd_strcspn_closed : RtString.astrcspn_realizes tfibsegs B PC_strcspn A_SSP_GOT A_SSP_GUARD.
Proof. exact (RtSStrcspn.cmd_strcspn B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
Theorem cmd_strtok_r_closed : RtString.astrtok_r_realizes tfibsegs B PC_strtok_r A_SSP_GOT A_SSP_GUARD.
Proof.
exact (RtSStrtok2.cmd_strtok_r B (YG0q.AR_laws_ok tfibsegs B) HB
(RtLStrspn.cmd_strspn B (YG0q.AR_laws_ok tfibsegs B) HB)
(RtSStrcspn.cmd_strcspn B (YG0q.AR_laws_ok tfibsegs B) HB)).
Qed.

(* snprintf (0x45184) and sprintf (0x45180) on omx-clap-core/fuzz_manifest's GXA printf route (RtFSnprintf.v,
   RtFSprintf.v; the world field w_H8 the route uses comes from the core's world record through RtWH8.v's instance) *)
Theorem cmd_snprintf_closed : RtFormat.asnprintf_realizes tfibsegs B PC_snprintf A_SSP_GOT A_SSP_GUARD.
Proof. exact (RtFSnprintf.cmd_snprintf B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
Theorem cmd_sprintf_closed : RtFormat.asprintf_realizes tfibsegs B PC_sprintf A_SSP_GOT A_SSP_GUARD.
Proof. exact (RtFSprintf.cmd_sprintf B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
End closed.

(* The allocator family: asan_malloc (0x34528), the malloc interceptor's body (0x58b58), strdup (trampoline
   0x451dc) and strndup (trampoline 0x45138), from the relocated malloc chain (A/AF0w.v). That chain also takes the depot-hash equation
   [forall t, as_dhash B t = tfib_dhash t], which holds by computation at the pinned record (as A/CmdTFIBLib.v:49
   uses it), so these are stated at the record itself, CmdB (A/AD2l.v:19), and keep no premise at all. *)
Section closed_record. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Let HD : forall t, as_dhash AD2l.CmdB t = YF0p.tfib_dhash t := fun t => eq_refl.
Theorem cmd_amalloc_inner_closed : RtDDefs.amalloc_inner_realizes tfibsegs AD2l.CmdB RtDDefs.PC_asan_malloc.
Proof. exact (AF0w.cmd_amalloc_inner AD2l.CmdB AD2l.CmdB_syms HD). Qed.
Theorem cmd_amalloc_body_row_closed :
RtDDefs.amalloc_body_realizes tfibsegs AD2l.CmdB RtDDefs.PC_malloc_body PC_STRNDUP_RA0.
Proof. exact (AF0w.cmd_amalloc_body_closed AD2l.CmdB AD2l.CmdB_syms HD). Qed.
Theorem cmd_strdup_closed : RtAlloc.astrdup_realizes tfibsegs AD2l.CmdB PC_strdup PC_STRDUP_RA0.
Proof.
exact (RtDStrdupX.cmd_strdup AD2l.CmdB (YG0q.AR_laws_ok tfibsegs AD2l.CmdB) AD2l.CmdB_syms
(AF0w.cmd_amalloc_inner AD2l.CmdB AD2l.CmdB_syms HD)).
Qed.
Theorem cmd_strndup_closed :
RtAlloc.astrndup_realizes tfibsegs AD2l.CmdB PC_strndup PC_STRNDUP_RA0 PC_STRNDUP_MID.
Proof.
exact (RtDStrndup.cmd_strndup AD2l.CmdB (YG0q.AR_laws_ok tfibsegs AD2l.CmdB) AD2l.CmdB_syms
(AF0w.cmd_amalloc_body_closed AD2l.CmdB AD2l.CmdB_syms HD)).
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
Print Assumptions cmd_strcspn_closed.
Print Assumptions cmd_strtok_r_closed.
Print Assumptions cmd_snprintf_closed.
Print Assumptions cmd_sprintf_closed.
Print Assumptions cmd_amalloc_inner_closed.
Print Assumptions cmd_amalloc_body_row_closed.
Print Assumptions cmd_strdup_closed.
Print Assumptions cmd_strndup_closed.
