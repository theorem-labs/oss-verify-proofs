(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import F_syscalls MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import MallocKit_B MallocModel_B MallocKit_B3 F_ntf_B F_ntf_C.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import F_am_A.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_F_am_D () := "C69OSSVerify5KrLib2CJ4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib2CJ4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc7am_takeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes6option02C69OSSVerify5KrLib2CJ4Spec6Malloc:m_set_nextC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc:m_set_prevC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib2CJ4Spec6MallocDset_avail_meta_countC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc>set_avail_metaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2CJ4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2CJ4Spec5STree5stree02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1A6F_am_A7am_tookC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01I69OSSVerify5KrLib2CJ4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00I69OSSVerify5KrLib2CJ4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2CJ4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc9META_SIZEC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I69OSSVerify5KrLib2CJ4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K69OSSVerify5KrLib2CJ4Spec6Malloc<undef_reason03C1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ctx_cells_cbn :=
  cbn [ctx set_head upd_ctx s_ctx set_free_meta_head set_avail_meta set_avail_meta_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
       c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Lemma am_take_eq {R} st (k : mstate -> optr -> M R) bail q :
  c_avail_meta (ctx st) = Some q ->
  am_take st k bail = k (am_took st q (c_avail_meta_count (ctx st) - 1)) (Some q).
Proof.
ltac2:(KReplay.run1 (kr_t_F_am_D ()) ["AC_1"] "p'0h01Hh11Rh24bailh31ch41kh51oh61qh71rh82sti001mi011xp;1p;2p;3p;5p;6p;4g0000R0p4p70g000hR1p4p710p8p200R2g001FR3p4p710p8P2g002;R4p4p710p8P3j10Tg0036j13Tg003mj16Tg004mj21Tg005Oj35Tg005ij1?Tg006Kj2<Tg007Ij2;Tg008Gj2:Tg009?j12Tg00:Ej18Tg00:cj24Tg00;@j29Tg00<Hj2ETg00=Jj2DTg00>Ej3CTg00?Aj1>Tg00@9j5=Tg00A3j37Tg00Akj2@TP1j6ATP4j4BTg00BER4f3R1#0\0\4f2R4#0g00CAR3%31#6f0R5,13R6550P0f1R7,13R8f6R9#0g00D9P3f7#0P5f5R:g00D[%?3R;1<;5';W7g00EUg00FO,:7,13%25g00GL#8R;'4/95'EW3/D95C5P6O2g00H1g00HiR6P9g00IG#>f4R9V6D=n10110100021010000P9%3:#2/4;97:41134O235X50%0:R0P1%39R3#2/4;9797P8O2R8'@%63P5EAP:P9P1P4CB=508eW0W6W2W4W8X12o"). Qed.

End AC_1.
