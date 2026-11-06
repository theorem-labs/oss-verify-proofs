(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import AcctCore ModelX.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Placement.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MmXfer () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List6filterI47Corelib4Init9Datatypes4list00I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes4bool01C47Corelib4Init9Datatypes4andbI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat5Nat2Z6inj_leK47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C56Stdlib6ZArith4Znat5Nat2Z8inj_succI46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums8positive03C46Stdlib5Lists4List7existsbI46Stdlib5Lists4List5NoDup00C46Stdlib5Lists4List<NoDup_filterC46Stdlib5Lists4List4inclC46Stdlib5Lists4List2InI47Corelib4Init5Logic3and00C46Stdlib5Lists4List9filter_InC47Corelib4Init5Logic7and_indC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result01c59OSSVerify5KrLib4LibA6MmXfer4relXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ModelX5stripC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedI47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4LibA6ModelX2MXC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C47Corelib4Init5Logic9False_indI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00K6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result02K6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result03C47Corelib4Init5Logic3iffC47Corelib4Init5Logic6eq_symK47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00c59OSSVerify5KrLib4LibA6MmXfer:strip_selfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXfer;filter_trueC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude>check_ret_onlyI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbc59OSSVerify5KrLib4LibA6MmXfer7relX_idC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap@mmap_noreserve_bC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_add_lazyC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapAwith_mmap_backingI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapCwith_mmap_destroyedC45stdpp9bitvector;definitions;bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem5StateBpage_outside_rangeC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_forget_rangec59OSSVerify5KrLib4LibA6MmXferDwith_mmap_backing_MXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ModelXBvm_forget_range_MXC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapEwith_mmap_replacementc59OSSVerify5KrLib4LibA6MmXferEmat_with_mmap_backingC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXferHvmmaps_with_mmap_backingC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectCmprotect_model_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm7MadviseEmadvise_dontneed_nextC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State?with_vm_backingC59OSSVerify5KrLib4LibA6ModelX6MX_matC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap@forget_vm_rangesc59OSSVerify5KrLib4LibA6MmXfer;ranges_keepC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXfer:filter_andC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>brk_model_nextc59OSSVerify5KrLib4LibA6MmXferCforget_vm_ranges_MXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ModelX>with_vmmaps_MXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ModelX;m_vmmaps_MXC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap=with_brk_nextC4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap:brk_unmapsc59OSSVerify5KrLib4LibA6MmXfer6robustC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3lebC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula09C46Stdlib4Bool4Bool>eq_true_iff_eqK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula05I47Corelib4Init5Logic2or00C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeC47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes?RelationClasses?iff_equivalenceK46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib4LibA8AcctCore=nonlazy_bytesC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_backing_usedC59OSSVerify5KrLib4LibA8AcctCoreEvm_backing_used_splitC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op201c59OSSVerify5KrLib4LibA6MmXfer@filter_length_leC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03C4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitc59OSSVerify5KrLib4LibA6MmXfer9mat_boundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXfer:robust_lebC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXferEvm_backing_used_canonC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ModelXBvm_backing_used_MXC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateGvm_backing_within_limitc59OSSVerify5KrLib4LibA6MmXfer:mat_bound0C1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapHmmap_noreserve_backed_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapBmmap_fixed_rw_nextc59OSSVerify5KrLib4LibA6MmXferImat_with_mmap_replacementC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXferLvmmaps_with_mmap_replacementC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXferFbacking_within_limit_XC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXferHwith_mmap_replacement_MXC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapGmmap_fixed_rw_budget_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapGmmap_fixed_rw_span_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapLmmap_fixed_rw_span_budget_okc59OSSVerify5KrLib4LibA6MmXferFmprotect_model_next_MXC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectBmprotect_budget_okC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall5w_is0C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap7min_brkC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes3orbC4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z3subC4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z:ltb_irreflC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap8brk_r_okC45stdpp9bitvector;definitions6bv_subC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem5State;region_freec59OSSVerify5KrLib4LibA6MmXferGstrip_with_mmap_backingC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC4ELinuxProcessSemantics?LinuxProcessSem5State7map_hasC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude:listNN_eqbC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>munmap_free_okC4ELinuxProcessSemantics?LinuxProcessSem5State:map_removec59OSSVerify5KrLib4LibA6MmXfer=relX_ret_onlyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXferIstrip_with_mmap_destroyedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXfer;relX_filterC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXferFwith_mmap_destroyed_MXC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4Mmap<check_munmapC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC4ELinuxProcessSemantics?LinuxProcessSem5State=maps_subtractC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_start_brkC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spK4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01C4ELinuxProcessSemantics?LinuxProcessSem5State6EINVALC4ELinuxProcessSemantics?LinuxProcessSem5State9TASK_SIZEC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm7MadviseBmadvise_dontneed_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm7MadviseCmadvise_dontneed_okc59OSSVerify5KrLib4LibA6MmXferHmadvise_dontneed_next_MXC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm7Madvise=check_madviseC4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectImprotect_grows_conflict_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectBmprotect_modeled_bC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<errno_ret_inc59OSSVerify5KrLib4LibA6MmXfer9relX_sameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXferDmprotect_budget_ok_XC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm8Mprotect>check_mprotectC4ELinuxProcessSemantics?LinuxProcessSem5State<map_containsC4ELinuxProcessSemantics?LinuxProcessSem5State6ENOMEMC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8Mprotect?mprotect_errnosC4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retc59OSSVerify5KrLib4LibA6MmXfer@with_brk_next_MXC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXferFforget_vm_ranges_stripC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXfer:brk_r_ok_XC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4Mmap9check_brkC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap9brk_zerosC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapBmmap_off_aligned_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_pglen_ok_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;mmap_anon_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapAmmap_plain_anon_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>mmap_modeled_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_noaccess_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapEmmap_fixed_noaccess_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_fixed_rw_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapImmap_noreplace_noaccess_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapCmmap_noreplace_rw_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapImmap_fixed_destroyed_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapMmmap_fixed_noaccess_span_nextc59OSSVerify5KrLib4LibA6MmXferKstrip_with_mmap_replacementC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXferIfixed_rw_span_budget_ok_XC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXferDfixed_rw_budget_ok_XC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA6MmXferEnoreserve_backed_ok_XC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4Mmap:check_mmapc59OSSVerify5KrLib4LibA6MmXferAstrip_with_vmmapsC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;mmap_errnosC4ELinuxProcessSemantics?LinuxProcessSem5State6EEXIST".
(* [comment removed for export] *)
Unset Lia Cache.
Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma filter_true : forall {A} (l : list A), List.filter (fun _ => true) l = l.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h01lh11Ah23IHlh31ah41fp;1p;3p;2p;6p;5p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p200R0g002UR1p4p710p8P0g0033R2p4p7210p8P0p1003Pp4p710p8P0g003nR3p4p710p8P0g004PR4p4p710p8g004kj11TP4j30Tg005Kj32Tg005ej16Tg006Ej25Tg006_j34j29TP2j63TP1j68TP3j57Tf0R3#1f1R1%11R2f2R4#1R5g007?R6V4=043;23W0%61R7,52P6V1=017=227ef3R7#1P6V7=073;23f4R7#1R2P6V7R8=071R99474R:P:A4741R:f5R;#1^02R<P2P3P6V;=0;4O1X4<1974R4P415<4E3P2P2P4P9P1P3E3E8A078:=22:eW2X05X31P3D7W0X10o"). Qed.

Lemma filter_and : forall {A} (f g : A -> bool) (l : list A),
  List.filter f (List.filter g l) = List.filter (fun a => g a && f a) l.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "p'0h01ah11lh21bi001bh31Ah42IHh51fh62f0h71gh81xp;1p;3p;2p;6p;5p200R0g002UR1p4p710p8P0g0033R2p4p7210p8P0p1003Pp4p710p8P0g003nR3p4p710p8P0g004PR4p4p710p8g004kj13TP4j30Tg007_j22Tg005Kj31Tg005ej1:Tg006Ej26Tg006_j34j29TP2j65TP1j68TP3j57Tf0R3g008=R1[f1R2P1[f2R4#3f3R5%35R6f4R7#3R8A07439075P5P3O1R9P7P3O1R:'2X07=07331W1%:5R;,66A052;9054P4P3O1/29X05=05;516ef5R6#3A06539067P6P3O1R;,2:X06=06331P7P4O1P1P1f8R:#3R9f7R<P1f9R=#3R>P3f6R?=0:5R@94:7P@n010000002000050:P1P>P<P7O1,23P<P3O1RAP:P3O1RB'2X0:=0:5RC94:7RDPCn010000002000031P3P?P5O1REP1P1P1f:#3RFP3A0=<790=:RG94=6PGn0100000020000P1PFP3P=P3O1,2BX0==0=7RB94=6PBn010000002000051>P3P9A0:<@R@94:7RBPBPDP>^19R>P9P3PGO1X6>19:7R:P:16>:E5P9P9P:P@PCP4E5E8A19BDeP4A19@Cen0110000020000b2%3<R@A0<64RC94<590<?P1P9g007?/2EP?P3O1RB/2AX0<=0<4RA94<5RDPAn010000002000031eP2A0<?CP1P9g008]/2EPDPAn010000002000051@en0110000020100b2%3?A4?42R490?790?612;BX0?=0?431eW4X18X85P3D7W1W7W5X30o"). Qed.

Lemma filter_length_le : forall {A} (f : A -> bool) (l : list A), (length (List.filter f l) <= length l)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "p'0h04__x1h14__x2h27__arithh34__ffh48__varmaph55__with61lh73IH0h84cstrh95cstr0h:1xh;1Ah<2IHh=1bi001bh>1fp;1p;3p;2p;4p;5p;<p;7p;8p200R0g003nR1p4p710p8P0g009=R2p4p710p8P0g004PR3p4p710p8g004kj16TP3j33TP2j20Tg009]R2j21Tg00:7R3j22Tg006Ej27Tg005ej1ATg00:Sj1OTg00;1j1LTg00;Oj1ITg00<:j2DTg00<]j2WTg00=?j2VTg005Kj3UTg00=kj3TTg00>Jj4RTg00?<j4;Tg006_j3<Tg00?gR4j1=Tg00@FR5j14Tg00@fj1PTg00ADj25Tg00Aaj4NTg00BHj1?Tg00Bmj2KTg00CKj4JTg00Cij2>Tg00DLj1HTg00E1j1MTg00ESj3CTP1j5GTg00F6l<ETg00F[j4FTg00GFj7STg00Gjl<YTg00HOj8XTg00I3R1g00IRR6P2P5P3g00J0R7g00JRR8g00K1R9f1R:P8P9f0R;M<Ep=QP6P:g00KOP;CFp=8P:g00L6R<g00LUR=P=g00M5R>P;g00MUFSp=9P1P1P6P6P4P5P5f3R4g00N5f2R?P:P;M<Yp=@P1P6P2P5P3P7f5R7f4R3P4P?P:P;M<Ep=:P4P<P=P=P>P?P:P;GXp=Bg008=R<\;%6:P?%6?A34?;,04104;'1W611881299R81769R5/Q5g00NYR5#AR2%65R5%O6R1%L6R@%I6RA1D69RB/8B'91WA>R>P;P?g007?RB,7<1V;?=U<BdAT69:CRRBb3b4b5P8P;b2C;%A?R893?:,0?10?8'1e%64A334;,03103;'1P3P?O1P<P<f7R8P<f8R<#6P;f6RC=384RD9<83PDn0100000020000'01084#='1P;A3C7?RE,0CRF#=RG10C?RH#=RI'1%4FRJg00OERK#PRL'5RM%4HRN/5LRO'2PGPM15;LX:6RMPFPJ176JRGC@PIPOPMPHPN176NRMC@RPE:11FH12JNRQPFPJPGPHPNPME:P:CNRMPQ108DRD#?R8%4D,29RD10<3R<#?RN%4<,29R9P2P5P61K6?P:P1CJR1P@PA1>6KR<%HK,>6RK'8,9ARH%M=R=1D6LRR9C6<AC6KRRR'8,9ACBP>PBb3b4b5X06X1612;:RK15:L15?LRL'2[^06^16P;f:RS/0C#4f9=3SC,0S#4P4O3RSb2b9b8b7C;A<C4E,0C/1Ie11FIRC12JOPFPJPGPIPOPPE:PMPQP8PDPNP9P2P5P1P@PAPHP=18<R,9ACBP>PBb3b4b5X06X1612:L\K^06^16PSb2b9b8b7C;PCen0110000020101b=A<7?:R:9373,07107:'1eW<W6X:?P;DGW6W>X;0o"). Qed.

Lemma NoDup_filter' : forall {A} (f : A -> bool) (l : list A), List.NoDup l -> List.NoDup (List.filter f l).
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h01Ah11fh21lp;1p;2p;4p200R0p100Ojp4p710p8P0g00PFR1p4p710p8g004kj12TP1j21Tg00Pbj40Tf0R1g008=[f1R2#2f2R3/11f3P3P2P1C0UW2W1X00o"). Qed.

Lemma incl_filter : forall {A} (f : A -> bool) (l : list A), List.incl (List.filter f l) l.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h01Ah11fh21lh31xh41Hh52Hxh62H0p;1p;3p;2p;4p;5p200R0g00Ojp4p710R1p8P0g00QCR2p4p710p8g004kj14Tg004Pj32Tg00Q\j30Tg00R3R3j23Tg00RNj48Tg00Rlj57TP2j35Tg005Kj36Tg008=R2f0R4g007?36p=1P2\4R2f1R5#4f2R6f3R7A2765704%46R8P3A27649075f4R3?065P7P6O1#1'3[R9A0754P6P5O1#1'3A23759036R:[f5R;?076P3P7O1#1'3\:P7P6P5P4C8P5n2001000000120000000W2X35X12X01P9^28^35^12^01P4P;P3P6P7P5O5A0;67P3P6O1#1'3f6R1?073R2P;P7O1#1P2P1P3O1#1P5W6X42P4D7b5b4W5W3A2654=564eW2W1X00o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition relX (mo : Model) (mat : list word) (rX r : check_result) : Prop :=
  match rX, r with
  | CheckOk mX eX, CheckOk m e =>
      eX = e /\ strip m = with_vmmaps (m_vmmaps m) (strip mo) /\
      exists f, mX = MX m (List.filter f mat) /\ m_vm_materialized m = List.filter f (m_vm_materialized mo)
  | CheckReject, CheckReject => True
  | CheckUnmodeled, CheckUnmodeled => True
  | _, _ => False
  end.

(* [comment removed for export] *)
Lemma relX_ok_l : forall mo mat mX eX r,
  relX mo mat (CheckOk mX eX) r ->
  exists m f, r = CheckOk m eX /\ strip m = with_vmmaps (m_vmmaps m) (strip mo) /\
              mX = MX m (List.filter f mat) /\ m_vm_materialized m = List.filter f (m_vm_materialized mo).
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "p'0h01fh11mi001mh21Hh32eXh41Ah51Bh61Sh71eh82mXh93math:2moh;1ri011ci023evsi031xp;1p;2p;4p;3p;6p100SIp4p70R0g005KR1p4p710R2p8P0p100T9p4p710R3p8P0g003PR0p4p710R4p8p100TUp4p70R5P2p8P5P3p8P5P4p8p100UCp4p70R5P2p8P5P3p8P5P4p8g00DLj1>Tg00V9j1OTg00VWj1NTg004kj1HTg00W:j21Tg00XDj4BTg00Y9j15Tg00Yoj1;Tg00Zfj2?Tg00[`j10Tg00\`R4j24TP1j33Tg00R3R1j26Tg004Pj38Tg00]:j2@Tg006Ej2KTg00]mj4CTg00^Hj4ITP0j6JTg00^bj2GTf3R0f2R5f1R3f0R238'@p=<f4R6A8532730p=2g00_AR7?360A3753/62'6p=7g00`7R8?353/62p=:1472p=9%52,?3p==f5R9A8053,@6537/62p=AA3753/62p=F1?329375p=E%029853p=M1@329375p=DA3832p=Lg00OE#>#>#>#>#>#>#O#NR:#HR;g00aA#HR<P8P9P61105P2CBg008=\:R=1139%53R>%;3R?f8R@#5RA'?f6RBP3P:P2f7RCC<P;%03RDP:P2%0@D2D75:0X0='4X17#9[P2P@PC11B91132CBP1A3<B3%55%;5f9RE'=P@P0P:P2PEP;%00P:P2f:RF#0RGD2EAX0=,4=3F1196113EP>f<RH#5RI,??PFP3P:P2f;RJC<P;PDP:P2%0HD2D73:X0=,4=X17#9P2A3<@0P<P6%5B%;Bf=RK#53ERLPHPCP:P2PKP;%0CRMP:P2f>RN#0ROD2EAX0=,4=RP'611E@RQ1130P>f@RR,=?PNP3P:P2f?RSC<P;PDP:P2%0RD2D7RT3:X0=,4=X17#9[X3<%59%;9/?IPJPBP:P2PHP;%0BP:P2%0KRID2EAX0=,4=3FP1PLPP113@=:QTX0=,4=X17#9P2%;@%5S5EAPSPFP:P2PRP;PGP:P2fARG#0RFD2EAX0=,4=P4P=PRPJP:P2PGP;%0JP:P2fBRJ#0R4D2EAX0=11KH113HP>fDRH,=?PJfCRS98:2RA,@3AM:2HR@93;DD73:X0=,4=X17#9P21@KAA3;I@5FJP1A8:3H9DSNP;POP:P3fERO#0D211GR113RP>fHRN,=?fFR1P3P:P2fGR@C<P;PDP:P2%0NRID2D73:X0=,4=X17#9P2A8:019DORP;PFP:P6PID2P711HS113SP>fKRH,=?fIRIP3P:P2fJRFC<P;PDP:P2%0HD2D73:X0=,4=X17PJP=11SJRH%5S%;S/=FPNPSP:P2PIC<P;%0SP:P2%0FD2D77:HX0=P911JGRG/LG%5J%;J%5I3ERHA8:9N9D@JR@P;P4P:P9%0ID2RI'6R4'61K8GPHP4PEP@PIP3P2CCCCCCCICIW5W4P3P2O2n2001000000121000000W2X0=P3P2O2n2001000000121103000W2W6P3P2O2n2001000000121000000W2PEP2EJW2P3P2O2n2001000000121000000W2X7<X17P3P2O2P6P01153R5g00b7R<CB1136RE938<P>1=?CP9P3P:P2PBC<P;PDP:P2PMD2D7RM'6X0=,4=X17#9/G2W2P6P0P5g00cAR5CBA385E/6MX0=,4=X17#9/G2W2n011010003211001020000X;8W3X87W9X:7o"). Qed.

Lemma relX_ok_r : forall mo mat rX m e,
  relX mo mat rX (CheckOk m e) ->
  strip m = with_vmmaps (m_vmmaps m) (strip mo) /\
  exists f, rX = CheckOk (MX m (List.filter f mat)) e /\ m_vm_materialized m = List.filter f (m_vm_materialized mo).
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "p'0h01fh11Hh21eh31mi001mh42eXh52mXh61Bh71Sh83math92moh:2rXi011ci023evsi031xp;1p;2p;4p;3p;6g00DLj1<Tg00V9j1NTg00VWj1LTg004kj1DTg00W:j27Tg00XDj4BTg00Y9j11Tg00Yoj1:Tg00Zfj2@Tg00[`j10Tg00\`R0j24Tg005Kj36Tg00R3R1j2;Tg004Pj3=Tg006Ej2JTg00]mj4FTg00^Hj4ITg003Pj6ETg00^bj2GTg00]:j2CTf4R2f3R3f2R4f1R53='Cf0R6'7p=5A=4569623p=2g00`7R7?645/;6p=8g00_AR8?645/;6p=3%16,@5p=MA=456,C3p=9%:5/@6p=?1@569684p=>1456,;4p=A1C569684p=HA6756p=Kg00OE#<#<#<#<#<#<#N#LR9#DR:P7g00aA#DR;f5R<P2P41756R=CB%14R>%:4R?f6R@#1RA'@g008=\9RBP3P9P6P@P4D5P:%03RCP9P6f7RD#0RED2582X0B'433[]2^38P6f8RFPD1734P=CBP1A6;35f9RG,M?P3P9P6PGC9P:PCP9P6f:RH#0RID253<X0B,4B53>%13%1H,?317@<P2P9P6PHP3D5P:%02P9P6f;RJ#0RKD238X0B,4B33P6A6;<3P;P2%:@f=RL#15>ARAPDP9P6PLC9P:PEP9P6f>RE#0RMD253GX0B,4BRN';%1D%:D%1E3>RO17H4PFP9P6PEPDD5RPP:%0FP9P6f?RQ#0D2RR38X0B7AB[X4;%1<RSf<RT#1,?<P@P9P6PTC9P:%0@RUP9P6%0LRVD253FX0B,4B33P1PAPN17HD?8PRX0B9AOBP6%1F%:F%1QRF3>PHP9P6f@RHC9P:PIP9P6fARI#0ROD253TX0B,4BP0PBPJP9P6PIC9P:PKP9P6fBRK#0R0D253LX0B%1J%1KRR,?J17EJPTP9P6PKPJD5P:%0TP9P6fCRT#0RJD238X0B,4B33P6PLP9P6PTC9P:PVP9P6fDRV#0RLD253QP1A=95V9HHEP:PMP9P5fE#0D2fFRM#1,?Q17KQPHP9P6PMPQD5P:%0HP9P6fGRQ#0D238X0B,4B53FP6A=93M9HKHP8PIP9P2PQC9P:P0P9P<fIR0#0D2RQ%1TfJRH#1,?T174TPVP9P6PHPTD5P:PLP9P6fK#0D238X0B,4B33[X58P:POP9P2fHRO#0D2%:K%105>RPTP9P@P0PKD5PTP9P6P0PKD5P:PJP9P6%0HD238X0BRH,4BPGPBPHP<PKP9P<POPID5RI/KIPQ1J7IP6CFCICFW6PTP6EEW1P5P6O2n2001000000121000000W1X0BP5P6O2n2001000000121103000W1W7P5P6O2n2001000000121000000W1P@P6EEW1P5P6O2n2001000000121000000W1X2;X38X4;X58P5P6O2P2P3g00b7R5P=CBA>>?SRSP3P9P6P<P4D5R49675P:PCP9P6PUD2RU';X0B7AB/G6W1X2;X38P2P3g00cAR3P=CBA6734/;UX0B9ASB/G6W1X2;X38n011010003211001020000X:7W8X98o"). Qed.

Lemma relX_unmodeled : forall mo mat rX r, relX mo mat rX r -> (rX = CheckUnmodeled <-> r = CheckUnmodeled).
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "p'0h01Hh12H0h21rh32H1h43Heqh53evsi003evsh61mi011mh71eh84evs0h92m0h:3math;2moh<2rXi021cp;1p;4p;2p;3p;6g00DLj15Tg00V9j1>Tg00VWj1<Tg004kj19Tg00XDj40Tg00dKj22Tg00W:j21Tg00ddj4:Tg005Kj36Tg00^bj23Tg00]mj47Tg00T9j6;Tg006Ej2=Tg00`7R0f0R1g00cAR236p=4P0P2f2R3g00e@R4f1R5P1E;p=8g00_AR6g00OE#5#5#5#5#5#5#>#<#9P0f4R7f3R8P5P1C0%43%45R9'2[^20P1g00aA#9R:P0f8R;f7R<1183R=P1C01178R>#4/29[P1f;f:R?f6R@f5RA'11151RBC011<@#4RC%4=RD[1135RE#4RF11;<RG#4[P0PGP2P1C:A602GP0p-0RGP1g00e\RHPHg00f9RIn011020003201011000000X70RJf9RK/1;;81PH11A7#4/31b3b4X1CP0P=P2P1C:A602=A8J>1PH11?K#4/31b3b4X1FC7W0X8:X96P5P1O2P<P@PEg00b7RKC0A60K2R?,2D/31W0P<P@PEP2C0A6022RE,2D/31W0n011020003201011000000X20W5X66P5P1O2P0P7P8PKP1C012?9[P1P<P@PKPBC012?F/31W0X5:X66P5P1O2P8P3PKPKC0P?\?RDPDP1P?P0PKP0PGP1PHPIPHn011020003201011000000X70P4P2P1E;PH13?1b3b4X1?RHPHC7W0P8P3PKP2C012?E/31W0n011020003201011000000X20P0P7P8P2P1C012E9[P1P<P@P2PBC012EF/31W0X5:X66P5P1O2P8P3P2PKC012E?/31W0P8P3P2P2C0PE\ER3P31=02X1EREPEC7W0n011020003201011000000X20n011020003201011000000X<0W:W;o"). Qed.

(* [comment removed for export] *)
Lemma strip_self : forall mo, strip mo = with_vmmaps (m_vmmaps mo) (strip mo).
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h02mop;1p;2g00Yoj13Tg00Y9j12Tg00Zfj20Tg006Ej21Tg00_AR0f0R1#3%21'0,10W0o"). Qed.

Lemma relX_id : forall mo mat e, relX mo mat (CheckOk (MX mo mat) e) (CheckOk mo e).
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h01lh11eh21fh33math42mop;1p;3p;2p;4p;6g00DLj11Tg00V9j1DTg00VWj1>Tg004kj19Tg005Kj30Tg00Y9j1BTg00Yoj1?Tg00Zfj2=Tg00]:j23Tg004Pj32Tg00[`j17Tg00R3j24Tg00\`j2<Tg006Ej26Tg00fUj1CTg00]mj45Tg00gPj2;Tg003Pj68Tg00^Hj4ATg00W:j2:Tg00XDj4@Tg00_AR0g00OE#1#1#1#1#1#1#D#>R1#9R2g00aA#9R3f0R4=034f2R5#BR6%?5/=6500R6g008=\1R7f3R8/35R9A2145,38500%78R:A214:502'4X27R;'<R<'41634P6P<%C5P7P;g007?V1R;P2f1R713849009A21;:902:'4X02P2%75R8A0099A02:4'4X021357R:=00:A0288160:1628C5A21;81;18E8A21;71;17E8CAC5C5P5P71::41:54C@eW1W3W4o"). Qed.

Lemma relX_filter : forall mo mat m f e,
  strip m = with_vmmaps (m_vmmaps m) (strip mo) ->
  m_vm_materialized m = List.filter f (m_vm_materialized mo) ->
  relX mo mat (CheckOk (MX m (List.filter f mat)) e) (CheckOk m e).
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h01fh11Hh21Sh31eh41mh53math62mop;1p;2p;3p;4g00DLj12Tg00V9j1ATg00VWj1>Tg004kj19Tg00Y9j14Tg00Yoj1;Tg00Zfj28Tg005Kj30Tg00[`j13Tg004Pj31Tg00]:j25Tg00R3j27Tg00\`j2=Tg006Ej2<Tg00]mj46Tg00^Hj4@Tg00W:j2:Tg00XDj4?Tg00_AR0g00OE#2#2#2#2#2#2#A#>R1#9R2g008=\1R3g00aA#9R4f2R5#4%;5f4R6#4R7'8500f3R8#3f5R9#3R:9115502A0455%;6f6R;#4'89007R7A116;,59f0R<=11;,59500f7#3911<902:'7X03R:,=3R='71<45P7P=f1P3P:P8A1189,56R:=00:%36%3;91185021<0:P<C6C@C6C6P;P91::51:65C?eW1W2W3W0X40W5W6o"). Qed.

Lemma relX_same : forall mo mat m e,
  strip m = with_vmmaps (m_vmmaps m) (strip mo) ->
  m_vm_materialized m = m_vm_materialized mo ->
  relX mo mat (CheckOk (MX m mat) e) (CheckOk m e).
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h01lh11Hh21Sh31eh41fh51mh63math72mop;1p;2p;3p;4p;6g00DLj11Tg00V9j1DTg00VWj1@Tg004kj19Tg00Y9j18Tg00Yoj1>Tg00Zfj2=Tg00[`j13Tg005Kj30Tg00]:j25Tg004Pj34Tg00R3j26Tg00\`j2CTg006Ej2?Tg00]mj47Tg00gPj2<Tg003Pj6:Tg00^Hj4BTg00W:j2;Tg00XDj4ATg00_AR0f1R1f0R230p=2g00OE#1#1#1#1#1#1#D#@R3#9R4g00aA#9R5%81%>1f3R6#8R7'='2f2R8#3f4R9#3R:504A0588%>6f5R;#8'=,27R7g008=\3R<159;R=A432;,59'2f6#3R>9432904:'6X4<R?'CR@'61?58P7P@P1P<P?g007?V3R?P4P91592,2=A43?>904:'6X04P4%3;R>12==A04:2'6X041569R:/2:%36=04>1?0:P2C7A43?>1<3>E:A43?91<39E:CBC7C7P;P91;:81;68CAeW1W2W3X50W6X70o"). Qed.

Lemma relX_reject : forall mo mat, relX mo mat CheckReject CheckReject.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h03math12mop;1g00DLj10Tg00V9j13Tg00VWj12Tg004kj11Tg00_Ag00OE#0#0#0#0#0#0#3#2#1g00e@W0W1o"). Qed.
Lemma relX_unm : forall mo mat, relX mo mat CheckUnmodeled CheckUnmodeled.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h03math12mop;1g00DLj10Tg00V9j13Tg00VWj12Tg004kj11Tg00_Ag00OE#0#0#0#0#0#0#3#2#1g00e@W0W1o"). Qed.

Lemma relX_ret_only : forall mo mat eff r e,
  relX mo mat (check_ret_only eff r (MX mo mat) e) (check_ret_only eff r mo e).
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "p'0h01pi001ph12cih22csh31eh41rh52ush62wsh72zsh81bi011bh93effh:1mi021mh;3math<2moh=3reti03:eff_copiesi04;eff_copyinsi057eff_reti06:eff_unmapsi07:eff_writesi089eff_zerosi091li0:1sp;1p;2p;4p;3p;6g00DLj12Tg00V9j19Tg00VWj18Tg004kR0j11Tg00]:j25Tg00hLj44Tg00XDj40Tg00iVj26Tg00j6j37Tg00W:j23Tg00jcj3;Tg00k[j6:Tg00_Ag00OE#2#2#2R1#2#2#2#9R2#8R3#1g00lYR4P4g00aA#1R4f5R5f4R6f2R7f1R81556f0R9C4P7P8P5P9C4C0]3^43P9%91#8#1,63R1#1R:1633R;#1R<g00mWR=#1R>g00I3,63R?#1R@P0P1fARAf@RBP0P1g00`7RCP9P0P;PCf6RDP0P;PCP5P0P=PCP6P0P?PCf3REg008=RFPCf8=727RG15AB/38g00b7RHn0100000020000RIPHn10110400020020100109RJPHn10110300020020102109RKPHn10110600020020100109RLPHn10110800020020100109PHn10110700020020100109P0P1PCP9P0P;PCPDP0P;PCP5P0P=PCP6P0P?PCPEPFPCPG13A8PHn0100000020000RGPHn10110400020020100109RMPHn10110300020020102109RNPHn10110600020020100109ROPHn10110800020020100109PHn10110700020020100109C0PDP0P;PAPBP0P;PCP9PLPHn10110800020020100109P0P;PCP9POPHn10110800020020100109C0P5P0P;PAPBP0P;PCP9PKPHn10110600020020100109P0P;PCP9PNPHn10110600020020100109C0P6P0P=PAPBP0P=PCP9PJPHn10110300020020102109P0P=PCP9PMPHn10110300020020102109C0PEP0P?PAPBP0P?PCP9PIPHn10110400020020100109P0P?PCP9PGPHn10110400020020100109C0P7f7RG=728PFPFfBR2PAPFPCP9152A/37PHn0100000020000PFPCP91327PHn0100000020000C0P9A;AB8g00e@RAn0110100020000b8PAX1@X0?P8P9O2n10110900020020100109PAX2>X:=P8P9O2n10110900020020102109PAX5<X0;P8P9O2n10110900020120100109PAX7<X0;P8P9O2n10110900020120100109PAX6:X01P8P9O2n10110901020120100109PBf?R1PGPDP5P6PEP7E:RDP815B1P9C4PDP8PBP9C4C0eX34X43W1W2X5<W7W6X=3P5P6PEP7P8P9O6n0110:000161105107108106103104W9W;W<o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma with_mmap_backing_MX : forall flags a n m mat,
  with_mmap_backing flags a n (MX m mat) = MX (with_mmap_backing flags a n m) mat.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "p'0h01ah11bi001bh25flagsh31mh43math51np;1p;2p;3p;4g00DLj11Tg00V9j19Tg00VWj17Tg004kj16Tg00nOj18Tg00]:j20Tg00oTj32Tg005Kj34Tg006Ej23Tg010Nj45Tg00OE#1#1#1#1#1#1#9#7R0g00_AR1%60f4R2#8g008=R3P3P3P1f0R4f5R5f3R6f2R7'0R8722P8n0100000020000P3P1P4A2526P6n0100000020000/07541P4A2267f1R5'0,311075,31n0110000020000b1P2P6P71054C5P2P6P7P5C5/04541eW4W3X50X00W2o"). Qed.

Lemma mat_with_mmap_backing : forall flags a n m,
  m_vm_materialized (with_mmap_backing flags a n m) = m_vm_materialized m.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "p'0h01ah11bi001bh25flagsh31mh41np;1p;3p;2p;4g00DLj10Tg00V9j19Tg00VWj14Tg00nOj13Tg004kj18Tg00oTj37Tg00[`j11Tg005Kj32Tg006Ej25Tg010Nj46Tg00OE#0#0#0#0#0#0#9#4R0g00_AR1f3R2#3g008=R3P3%80R4P3P1f0R1f4f2R3772P3n0100000020000#1%1332P1f1R5#1,54R6P6n0110000020000b1P2P3P5P1C6#1%11524eW3X40X00W2o"). Qed.

Lemma vmmaps_with_mmap_backing : forall flags a n m,
  m_vmmaps (with_mmap_backing flags a n m) = m_vmmaps m.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "p'0h01ah11bi001bh25flagsh31mh41np;1p;3p;2p;4g00DLj10Tg00V9j18Tg00VWj14Tg00nOj13Tg00oTj37Tg00Yoj11Tg005Kj32Tg006Ej25Tg010Nj46Tg00OE#0#0#0#0#0#0#8#4R0g00_AR1f3R2#3g008=R3P3g011TR4P3P1f0R1f4f2R3772P3n0100000020000#1%1332P1f1R5#1,54R6P6n0110000020000b1P2P3P5P1C6#1%11524eW3X40X00W2o"). Qed.

Lemma with_mmap_destroyed_MX : forall a n h m mat,
  with_mmap_destroyed a n h (MX m mat) =
  MX (with_mmap_destroyed a n h m) (List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) mat).
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h01ah11hh21mh33math41np;1p;4p;2p;3g00DLj10Tg00V9j1:Tg00VWj13Tg004kj12Tg012Kj49Tg013Sj21Tg00ADj28Tg014=j24Tg004Pj35Tg00]:j26Tg006Ej27Tg00OE#0#0#0#0#0#0#:R0#3R1g011Tg00_AR2%21f4R3f3R4f2f1C91103R31104,83'4f0551'6,72W3W2W1X41W0o"). Qed.

Lemma mat_with_mmap_destroyed : forall a n h m,
  m_vm_materialized (with_mmap_destroyed a n h m) =
  List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) (m_vm_materialized m).
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h01ah11hh21mh31np;1p;2p;3g00DLj10Tg00V9j19Tg00VWj13Tg004kj12Tg013Sj21Tg00ADj28Tg014=j27Tg00[`j14Tg004Pj35Tg006Ej26Tg00OE#0#0#0#0#0#0#9R0#3R1g011Tg00_A%21f3,10R2f2,10,82'7f0#4551'6W2W1X31W0o"). Qed.

Lemma with_mmap_replacement_MX : forall flags a n m mat,
  with_mmap_replacement flags a n (MX m mat) =
  MX (with_mmap_replacement flags a n m) (List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) mat).
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h01mh11ah25flagsh33math41np;1p;2p;3p;4p;5p;6g00DLj10Tg00V9j1?Tg00VWj1<Tg004kj1;Tg013Sj23Tg00ADj28Tg015>j32Tg014=j25Tg004Pj36Tg00]:j21Tg010Nj44Tg005Kj37Tg016<j5:Tg017Aj4>Tg003Pj6=Tg018Dj49Tg00OE#0#0#0#0#0#0#?R0#<R1g00_AR2%;1P2f3R3,30R4f2R5,30,84R6f1R732R81546f0R9561R:'1f5R;f4R<P3P9C4P;P<P3130<R01804R;;25C4150;=617'1572X02P<P3P5P8P:D:1179R89246P4P6P7P9C>E=P<P3P5P8C9P<P3P5P7C9/1:572eW3W0X41X11W2o"). Qed.

Lemma mat_with_mmap_replacement : forall flags a n m,
  m_vm_materialized (with_mmap_replacement flags a n m) =
  List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) (m_vm_materialized m).
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h01ah15flagsh21lh31mh41np;1p;2p;3p;4p;6g00DLj10Tg00V9j1?Tg00VWj18Tg004kj17Tg013Sj22Tg00ADj26Tg015>j3;Tg00[`j11Tg014=j24Tg004Pj33Tg005Kj35Tg006Ej29Tg010Nj4:Tg019Nj4>Tg003Pj6=Tg018Dj4<Tg00OE#0#0#0#0#0#0#?R0#8R1g00_A%71R2f2R3,20R4f1R5,20,64R6f0R73;R8#1f3R9,20R01604'4%155319527X221446%17531R6,92P9P3P5P8C:#1P9P3P5P8C>E=P9P3P5P7C<#1=526eW3X41X01W1o"). Qed.

Lemma vmmaps_with_mmap_replacement : forall flags a n m,
  m_vmmaps (with_mmap_replacement flags a n m) = m_vmmaps m.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h01ah15flagsh21mh31nh41vp;1p;2p;3p;4p;6g00DLj10Tg00V9j1<Tg00VWj15Tg013Sj23Tg00ADj2;Tg015>j3:Tg00Yoj11Tg005Kj32Tg006Ej26Tg010Nj47Tg01:Tj44Tg003Pj68Tg018Dj49Tg00OE#0#0#0#0#0#0#<R0#5R1g00_Ag011TR2f2R3,30R4f1R5,30,;4f0R43:R0#1%159224X42%14R6,62f3R7P3P5P0C7#1P7P3P5P0C4E8P7P3P5P4C9#1=226eW2X31X01W1o"). Qed.

Lemma mprotect_model_next_MX : forall m mat a n,
  mprotect_model_next (MX m mat) a n = MX (mprotect_model_next m a n) mat.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h01ah11mh23math31np;1p;3p;2g00DLj10Tg00V9j16Tg00VWj12Tg004kj11Tg01;]j35Tg00]:j24Tg006Ej23Tg00_AR0g00OE#0#0#0#0#0#0#6#2R1#1f3f1f035f2'4,30X31X01W2W1o"). Qed.

Lemma mat_mprotect_model_next : forall m a n, m_vm_materialized (mprotect_model_next m a n) = m_vm_materialized m.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h01ah11mh21np;1p;2g00DLj10Tg00V9j15Tg00VWj12Tg004kj11Tg00[`j14Tg006Ej23Tg00_Ag00OE#0#0#0#0#0#0#5#2R0%10f2#4'3X20W0W1o"). Qed.

(* [comment removed for export] *)
Lemma madvise_dontneed_next_MX : forall m mat a n,
  madvise_dontneed_next (MX m mat) a n =
  MX (madvise_dontneed_next m a n) (List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) mat).
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h01ah11mh23math31np;1p;3p;2g00DLj10Tg00V9j1:Tg00VWj13Tg004kj12Tg01<ij39Tg013Sj21Tg00ADj28Tg014=j24Tg004Pj35Tg00]:j26Tg006Ej27Tg00_AR0g00OE#0#0#0#0#0#0#:R1#3R2#2f3f1R3f0R4391113R31114,83'4f2552'6,70X32X02W2W1o"). Qed.

Lemma mat_madvise_dontneed_next : forall m a n,
  m_vm_materialized (madvise_dontneed_next m a n) =
  List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) (m_vm_materialized m).
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h01ah11mh21np;1p;2p;3g00DLj10Tg00V9j19Tg00VWj13Tg004kj12Tg013Sj21Tg00ADj28Tg014=j27Tg00[`j14Tg004Pj35Tg006Ej26Tg00_Ag00OE#0#0#0#0#0#0#9R0#3R1%21f1,10R2f0,10,82'7f2#4551'6X21W0W1o"). Qed.

Lemma vmmaps_madvise_dontneed_next : forall m a n, m_vmmaps (madvise_dontneed_next m a n) = m_vmmaps m.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h01ah11mh21np;1p;2g00DLj10Tg00V9j14Tg00VWj12Tg00Yoj11Tg006Ej23Tg00_Ag00OE#0#0#0#0#0#0#4#2R0g011Tf2#1'3X20W0W1o"). Qed.

Lemma madvise_dontneed_next_canon : forall m a n,
  m_vm_materialized m = [] -> madvise_dontneed_next m a n = m.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h01lh11Hh21ah31mh41np;1p;3p;2p;6g00DLj10Tg00V9j1@Tg00VWj1:Tg004kj19Tg00[`j18Tg005ej1;Tg005Kj31Tg01>6j16Tg013Sj22Tg00ADj27Tg014=j24Tg004Pj35Tg01>nj33Tg01?lj1?Tg00T9j6>Tg003Pj6=Tg01<ij3<Tg00_AR0g00OE#0#0#0#0#0#0#@R1#:R2%92R3f2R4#8%;2R531P3P5f4R6#6R7f3R8,21R91214R:,79'4f0R9552;36=106X03P3%88R;A3796=106X03%?8P5P9E>%68f1R3,21,7:,4:=525;38=108eP;P9E=A<843=108eW1X42W2W3o"). Qed.

(* [comment removed for export] *)
Fixpoint ranges_keep (ranges : list (word * word)) (p : word) : bool :=
  match ranges with
  | [] => true
  | (a, n) :: rest => page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) p && ranges_keep rest p
  end.

Lemma forget_vm_ranges_MX : forall l m mat,
  forget_vm_ranges l (MX m mat) = MX (forget_vm_ranges l m) (List.filter (ranges_keep l) mat)
  /\ m_vm_materialized (forget_vm_ranges l m) = List.filter (ranges_keep l) (m_vm_materialized m)
  /\ m_vmmaps (forget_vm_ranges l m) = m_vmmaps m.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "p'0h01lh11mh21pi001ph33math41ah52a0h62E1h72E2h82E3h91Hh:2IHh;1nh<1vi011bp;1p;2p;3p;4p;6p;5g00DLj1BTg00V9j1ZTg00VWj1VTg00iVR0j2TTg004kj1STg00]:j29Tg01@cj21Tg01Ahj16j2ETg00[`j1;Tg004Pj30Tg00Yoj13Tg005Kj32Tg00R3R1j28Tg006Ej2ATg00]mj4HTg00gPj2RTg003Pj6>Tg005ej1UTg006_j3PTg013Sj24Tg00ADj25Tg015>j37Tg014=j2@j3FTg007_j2DTg01Bdj4OTg017Aj4YTg01C_j4XTg003nj5WTf4R2f3R3#;f2R432g011TR5f1R6#3f0R732'8p=?g00_AR8f6R9f5R:'1A0346,9232/87p==A2567p=CA28:2A2346/87'8p=JA2867p=IA2346/87p=M%;79046p=:A0467,93p=<1146=287p=L%;6=247p=Q%36=257p=G1867,84p=KA2846/87p=Ng00OE#B#B#B#B#B#B#ZR;#VR</T<R=#SR>P=%S<R?P41967R@1146RAP<%64RBP7P?PA%;6RC90<BPA%36RAD?F=]3^18RBX0>P?P71946RD1947P?%;4REg007?RFX2<=0<E%34RG/CGRHEJX0?P?PCPDPDP?PEP7PHEJX0?1I@@A2?CCRH1CAARD'81A8@PHPD1A?C1A5ACHCHPFV<RF=0<C1R<CE>A0<F71R<7E>%U=RFP@11F6RDP<%6FRFP7P?PDA0<FCPDPAD?F=eX3?X18P0P<P<AP=23R0P@1106RDP<%60R0P7P?PDA0<0CPDPAD?F=^3?^18\B^0>P7P814;:RD14;2,5DR0;76RF1@D0=0<7RH'9RIP2P714;9RJ15JDRK;74RL,12RMP<f7RN,4;RO15OJRP;F71E:7'DX2<RQP6P?%;MRRA0<QE%3MRQ/CGCMF=X18P4PFPHO2P3PI113FRIP<%63RGPHP?PIA:<GFPI%3FD?F=P11@JK=0<6RK,9LPMP<%62RMPKC<5L2P?PRA:<ML%3L,CQCMP:A7OP3RQP<1@OPP4C<11:QRQP<f8RP,4;RL15LORO;F71E97'DX2<RMP4P?PQA:<M3PQ%33D?F=P7A7LO2RQ1@LO=0<3RO'9119QP<%69POC<5L9P?f9RO,4;RQ15QL;7:RL,1NRM%6N=:<LPM%3LD?P1f:R1,4;RL15LQ;79RQ,1PRM%6P=:<Q5Q?%3Q,GMPOf;RM,4;RQ15QLRL;7NR4P<1@QLP9C<11O4R4P<f<RL,4;RR15RQRQ;F71E17'DX2<RKP9P?P4A:<KNP4%3ND?F=P7A7RQPRQ,11%61=:<Q5Q?f=RQ,4;RP15PR;7ORR,1M%3R'GP8f>RR,4;RN15NPRP;71R4,1LRK%6LR91@NPRP=0<ORJ50<RF'9P7f?,4;RI15INRN;7MRG,1QRHP<f@,4;R;15;I;F71ER7'DRRX2<R;P1C<REP?%;HA:<;MR;%3MRM,GHRSEJX18P?A:<94PHP<%6QRT1@IN=0<1C</IERUA2?7;RV;KSX0?P5%34RSA:<TG=2?;R;1C7M5KUX<5P?AFIN71EQ7'DRQX4<RN=0<ORI19H71GGMRM,8;7NEX0?P?%;1R;90<NRNPHP<PRX4<P1C<18VM7NEX0?19KIPKP<PQX2<RQPOC<RI'IA0<Q;RQ92?NRN%31R1,CSRS'81A8IPNPS1A?Q1A51CHCHA0<P;90<9P<P9PPP;COE>PFP<P9PPPOCOE>%3KP7E>%;KP6E>194J,1LP:E>W8W7P6P7O2n2001000010121000000W9W6P6P7O2n2101000010121000000b5A7D0@PDP0P6P7CYE>P<P<P:P2CX=P=3R3P@1136R@P<%63R3P7P?P@A0<3CP@PAD?F=eX3?X18X:BX0>X;<X4<P6P7O2n2001100010121101101X5=P7DWW0o"). Qed.

Lemma forget_vm_ranges_strip : forall l m,
  strip (forget_vm_ranges l m) = with_vmmaps (m_vmmaps (forget_vm_ranges l m)) (strip m).
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "p'0h01mh11lh22IHh31ah42a0h51ni001bi011pp;1p;2p;3p;6p;4p;5g00DLj14Tg00V9j1CTg00VWj1=Tg00iVR0j2<Tg004kj1BTg01@cj22Tg00Y9j10Tg00Yoj13Tg00Zfj21Tg005Kj35Tg00fUj1;Tg005ej1:Tg006_j37Tg013Sj26Tg00ADj29Tg015>j38Tg006Ej2ATg003Pj6@Tg01C_j4?Tg003nj5>Tg00OE#4#4#4#4#4#4#CR1#=R2/<2R3#BR4P3g00_AR5f1R6f0R7'2R8#0%38%07R8'1555]0R9X14%;7%:3/27R:#0%3:/18555eX05P0P2P2f3R0f2R:573/27R;#0%3;/18555^05\9^14P7P5f4R;,61R<1610,9<;87R=,2:R>#3R?%0='1f5,61R1191<;86,20#3%06'19557X0511?8,A5%0>P6P=O1E@P2P2P;P0C?=73:/27R:#0%3:/18555eX05X29X14X52X32P6P7O2n2001101000121100100X43P7D>W1o"). Qed.

Lemma with_brk_next_MX : forall m mat req r,
  with_brk_next (MX m mat) req r = MX (with_brk_next m req r) (List.filter (ranges_keep (brk_unmaps r (vm_brk (m_vmmaps m)))) mat)
  /\ m_vm_materialized (with_brk_next m req r) =
       List.filter (ranges_keep (brk_unmaps r (vm_brk (m_vmmaps m)))) (m_vm_materialized m).
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h01mh12E1h22E2h31Hh42_Hh51ah61lh73math81rh93reqh:1vp;1p;2p;3p;4p;6g00DLj1<Tg00V9j1NTg00VWj1LTg004kj1FTg00Yoj10Tg00]:j22Tg01@cj21Tg01Ahj15Tg004Pj37Tg00[`j1;Tg01D?j3ETg00Zfj2@Tg01EBj3MTg005Kj38Tg006Ej2CTg00]mj4KTg003Pj6=Tg01FFj3ITg01GEj2HTg01HAj3BTg01ICj1GTg01J8j2JTg00R3R0j2DTf1R1f0R2#G'Jp=3f3R3f2R4;E1/@2p=4f4R5A7412783p=Ag00_AR6?841/D2p=:%;29741p=6%;1=842p=9A8412,D3p=?A8612p=>g00OE#<#<#<#<#<#<#N#LR7#FR8g011TR9%03R:1312P2P4P11253C4'1%05R;,31R<P;P4P1P5C4R;'1R=%5<R>=773'2R?P8%;=R@P7P>%;5DARA3:X:9P6AE:12RB/@3RC/24RD11<2?:?AX06132:R:?MC411:D11:CRD%5:R:=774RA'2A67:C998DP9%0D%0CC?3:P012;3,1</>?P8P@P7P>%;;DAP9%0=%0;C?f5R;#0R=,34R>P=P3P4P;C4R=/25'111>=R=%5>R>=775'2A67>;998=3:P2f6R=#0R>,33R@P>P5P3P=C4R>/2;'111@>%5@=77;'2'>f7R@#0R>,35R?P>P;P5P@C4R5'1R>%5?=675598P9%0>%05C?P0f8R0#0R5,3;R>P5P=P;P0C4R5'1R?%5>=675598%0?%05589f9R5#0R?,3=R>P?P@P=P5C4R=/20'111>=R=%5>R>=770'2A67>5998=3:P2f:R=#0R>,3@R?P>P0P@P=C4R@'1%5?=67@598f;R@#0R?,30P?P5P0P@C4R0'1#0%00589P6f<R9#0R0,35R?P0P=P5P9C4R5'1R0%5?R>=77@'2R<f=RC#0RD,3=REPDP@P=PCC4'1R=%5ERE=779'2RDA67ECRE998=5:2X06P8A67>5R=A882E9:DDX681><<A67>9R>988=1C6<1C8>CK%;0P1E=125@,1?P;E=W4W2P1P2O2n2001000000121000000W3W1P1P2O2n2001000000121000000b51234R;,@BAIB34E=%0;1H34E=AB;12AB312R2/2AA67:399823:eX87X97W7X06o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Slack.
Variable NMAX : nat.

Definition robust (x lim : Z) : Prop := x + Z.of_nat NMAX * page_size <= lim \/ lim < x.

Lemma robust_leb : forall x lim d, robust x lim -> 0 <= d <= Z.of_nat NMAX * page_size ->
  (x + d <=? lim) = (x <=? lim).
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) ["Slack"] "h04__x1h14__x2h24__x3h31Hh42Hdh57__arithh64__ffh74__p1h88__varmaph95__with:4__x4h;4__x5h<4cstrh=5lemmah>2H0h?1dh@3limhA1xp;2p;1p;3p;9p;7p;4p;6p;8g01K7j2dTg00@Fj1cTg01Knj2@Tg00ADj21Tg00:7j20Tg01LKj2BTg00R3j29Tg01Lgj24Tg005Kj3ETg00dKR0j2>Tg01MDj2MTg01N0l9KTg01Njj2JTg01OJj3`Tg01P<j7YTg00BHj1XTg00?gj1<Tg01Q7j27Tg01Q`j2ATg005ej1UTg006_j3?Tg004kj1RTg00Bmj2;Tg00:Sj1QTg00CKj4=Tg00;1j1PTg00;Oj1OTg00<:j2NTg00DLj1CTg00Cij28Tg01RLj1DTg01S1j3LTg00E1j1STg00ESj3FTg01STj7TTg00<]j2bTg006Ej2aTg00=?j2_Tg00=kj3\Tg00>Jj4[Tg01T8j3GTg01TZj6ZTg00F[j4ITg01U>j3WTg00GFj7]Tg01Ugj7^Tg00HOj8VTg008=R1f0R2g007?R33Ep=5g00IRR4f1R5;W2p=2P4P5g00KOP2CIp=6P5g00L6R6g00LUR7P7g00M5R8P2g00MUF]p=3f2R9P6P7P7P8P5P2F^p=Hf3R:P6P7P7P8P9P5P2GVp=:1d95g01VKp,4NMAXR;#cR<g01VeR='@R>,1:/091B9:g00K1R?/09109>'9f5R@/1:f4RA'414@A5E1[P211A>/0:10?:10:>'9RBf6RC/1ARD/4@RE14C@RF%5E10D@'>p-0RGP0g01W]f7RH/1@RI/4C#510ICRIP214HC#5RJPJ1MGJM9KW=RK1JD@RD%5F10C@'>PGP0g01XN9`G0PIPJ10HCP2FYW=RJ1JC@RI%X;R;10?<R0g00NYRLg00JRRM#<RN#<RO#<RP,74RQ174O174MRM'2'2g01Y@RO'A%<P,74174NRN/2M'2/AO%ULRP5?L3?%RLRRP4P41;4AP9%Q4RSC=P5P41;4@P:PSC=C=%P4RS%O4RT1N4?g00OERU#CRV,84RW'6,3TRX%CV,84%DV,845L4RV,6W,3T5HT%S7RYPT184URZ=F4V%DU,84RU'6,3TPYPTP6P7P7P8AF4ZW/6U,3T16ZU,3TFTRWC:C:1bT8RVP2P91a131_29#5dA\4?5C[R3b6b8b9X04X14X24X:4X;410?5R?1@:A,05'91@A@,15/0:119:/0A109A'>R1[[^04^14^24^:4^;4P2P=P<PHPCf8R<P9P:O7b5b<O2O23GW4W3P2O11B:APKPDPJPIP;P012MN,2Q/AO=?LPPRP41;49P51;4:C=PSPTPTP6P7P7P8P@EZ9HTXPYPTP4PUg01YlPZCI,3TPYPWC:C:PVP3b6b8b9X04X14X24X7G19?:1B:5P1[[^04^14^24^7GP210C>PHPCP<P9P:O6b5b<O2O29GEFX4BW3P2O1n200100000021100011000W>X?4X@4XA4o"). Qed.

Lemma vm_backing_used_canon : forall m, m_vm_materialized m = [] -> vm_backing_used m = nonlazy_bytes m.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) ["Slack"] "h01mh11xh24__x1h34__x2h41nh51Hh67__arithh74__ffh88__varmaph95__with:1lh;1yh<1zp;1p;3p;2p;<p;4p;7p;6p;Bg00DLj14Tg00V9j1ZTg00VWj1JTg004kj1;Tg00[`j1?Tg005ej1<Tg005Kj37j1YTg01ZSj1:Tg009=j26Tg00@FR0j15Tg01KnR1j20Tg00ADR2j21Tg01[Sj1VTg006Ej22Tg00F6l<QTg00Bmj2NTg00:Sj1ITg00CKj4HTg00;1j1FTg00;Oj1ETg00Cij29Tg00<:j2GTg01S1j3DTg00ESj3KTg00F[j4LTg00GFj7CTg00<]j2BTg00=?j2MTg00=kj3ATg00>Jj4OTg00?<j4PTg003Pj68Tg01\1j1@Tg01\oj1STg01^7j4XTg00Gjl<WTg01^ZlB>Tg00IRR3f1R4f0R537p=3P3P3g01_@P5CXp==g00I3R6P3P3P3P0P0f3R0f2R7P4g00JRR8g00K1R9P5M<Wp=UP3P3P3P3P3P3P1f6R:f5R;f4R<P1P0P7P9P4g01VeR1P1P5MB>p=TP3P3P3P3P3P3P2P5P4P7P2P0P<P;P:f7f8f9MB>p=Rg00_Ag00OER:#4R;#4#4#4#4#4#Z#JR<#;R0%?5%<<R237P3%:4R=%?4R>,6<#5/01'1%:7R?,35X<3P0P216<5#5/01,1?/3?X:0%58R8/01R0,1=R@/3=1091RA,1=RB/3=P3P3%Y3RCP5X13RDPC1345#VX;3X13P@PBPDPDPD1145#=,23X03X43P=P=123=RBP0PAPDPDPD1045#=,23X03X43P8PDPD%55,23X161239CU1231FTM:RP=P=PBM<Qg00NYRB#<%;BP31N37P4%I3CH%F3%E3RBg00L6g00LUR6P6g00M5R6P3193:R:1G39193;5D35K3g01_dP:CLg00MUFC1BB6P5P7g008=R6g007?RB'21M57=76BdAA394COb7b8b9X23X331094,15/35^23^33P5P1P?O2b6CP16<2#5/01,1=/3=eP>P5E8%@4%S4E8W5W0o"). Qed.

Lemma mat_bound : forall (mat : list word) f, (length mat <= NMAX)%nat ->
  0 <= Z.of_nat (length (List.filter f mat)) * page_size <= Z.of_nat NMAX * page_size.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) ["Slack"] "h02H1h14__x1h24__x2h34__x3h41Hh52H0h67__arithh74__ffh88__varmaph95__with:4cstrh;5cstr0h<5cstr1h=1fh>3matp;1p;2p;3p;4p;7p;<p;8g00DLj1=Tg00V9j1XTg00VWj1QTg004kj1JTg009=j20Tg009]R0j29Tg01`Kj3WTg004Pj3:Tg00@FR1j11Tg00:7R2j22Tg006Ej27Tg00Aaj4KTg00BHj1ATg01Q7j2;Tg00?gj1<Tg01U>j3?Tg01Q`j2GTg01aLj2FTg005ej1YTg006_j3ETg00Bmj2DTg00CKj4VTg00;1j1UTg00;Oj1TTg00<:j2HTg00Cij2>Tg00E1j1PTg01RLj1OTg00@fj1NTg01S1j3BTg01Ugj7MTg00<]j2LTg00=?j2RTg005Kj3STg00=kj3_Tg00>Jj4^Tg01Knj28Tg00R3j2ITg00F6l<]Tg00F[j4\Tg00GFj7ZTg00HOj8[Tf0R3#=#=p=5g00I3g00IRR4P0P1P2g00J0f5R2f4R1f3R0f2R5f1R6P3M<]p=Cg00K1R7/23p=3P4P6g00KOP3C\p=4P6g00L6R8g00LUR9P9g00M5R:P3g00MUFZp=6P0P8P9P9P:P5P6P3G[p=@g00OER;#=R<#=#5#5R=#X#QR>#Jg008=R?\>10>6p,4NMAXR@'9AW>65A:>65,0>10>5'9A:>50,0>RA10>0RB'9%1ARC%1BRD'2REPAPC174CPBPD174DECP3CKPE10>1RE/9@%1ERD%1@RB'2RAPEPD174DP@PB174BECP5CKPA%A@%3Bf6R@,0>RA#A%1A#3f79:>@,0>R@#A%1@#3g00NYR@g00JRRA,;4RD%<A#<RA#<RE,;41;4A5?49?4Dg01Y@RA'G'F%<E,;49?4D/GA,FD%Y@5E@3E%J@P41D45P61D40CV%U4%T4R@1H47RD1>4;RA'4,6@%P9REP@%O;,>4R;1>4<R<'4,6@PEP@14A;,6@PEP@P8P9P9P:%5=#5#5#NR=,H4R99B4ARA,4D,6@AB4<9,4A,6@FMC@C@C@1L@:P3P5g007?R@,7?1R35=S?@dA_476C^b7b8b9X14X24X34%3312051251180=R0#3181=,20'I[[[^14^24^34P3f9R3,0>#1PBf8=:>3,0>#1P6P1P2O6b6b<b;b:b0b0g01VeR2,8CRC#318B2,2C'Ieb5W4W=W>o"). Qed.

Lemma mat_bound0 : forall (mat : list word), (length mat <= NMAX)%nat ->
  0 <= Z.of_nat (length mat) * page_size <= Z.of_nat NMAX * page_size.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) ["Slack"] "h04__x1h14__x2h21Hh32H0h47__arithh54__ffh68__varmaph75__with84cstrh95cstr0h:3matp;1p;2p;4p;3p;7p;<p;8g00DLj13Tg00V9j1UTg00VWj1JTg004kj1ETg009=j26Tg009]R0j2ATg00@FR1j14Tg00:7R2j20Tg006Ej28Tg00Aaj4HTg00BHj1?Tg01Q7j29Tg00?gj1:Tg01U>j3DTg01Q`j2CTg01aLj2BTg005ej1XTg006_j3@Tg00Bmj2WTg00:Sj1VTg00CKj4TTg00;1j1STg00;Oj1QTg00<:j2=Tg00Cij2<Tg00E1j1LTg00@fj1KTg01S1j3>Tg01Ugj7MTg00<]j2NTg00=?j2OTg005Kj3PTg00=kj3GTg00>Jj4RTg01Knj27Tg00R3j2FTg00F6l<\Tg00F[j4[Tg00GFj7ZTg00HOj8YTf0R3#3#3p=1g00I3g00IRR4P0P1P2g00J0f5R2f4f3R1f2R0f1R5P3M<\p=IP4P5g00KOP3C[p=2P5g00L6R6g00LUR7P7g00M5R8P3g00MUFZp=5P1P6P7P7P8P0P5P3GYp=;g00OER9#3R:#3#1#1R;#U#JR<#E16<3p,4NMAXR='A16<5R>/A=%4>R?%4=R@'0RAP>P?184?P=P@184@EIP3CHPA%?=g00K1R=/0@16<1RA#?%4A,0=g00NYRAg00JRR>,94RB%:>#:R>#:,949D4Bg01Y@RC'C'B194>9D4B/CC,BB%XA5@A3@%EAP41W40P5%V4CT%S4%Q4RA1=4=RB1<49R9'2,5A%L7RCPA1<4:R:,29,5APCPAP6P7P7P8%1;#1#1#KR;,=4R79>49R9,2B,5AA>4:7,29,5AFMC;C;1NA8P3P0g008=RAg007?R8'81O30=PA8dAG4=5CRb5b6b7X04X1410=31050170;R0,0=171;,00'F[[^04^14P3P@16<2#4P5P1O4b4b9b8b3g01VeR1,7?R?,0=17@1,0?'FeW2W:o"). Qed.

(* [comment removed for export] *)
Lemma backing_within_limit_X : forall m' mat f,
  m_vm_materialized m' = [] -> (length mat <= NMAX)%nat ->
  robust (nonlazy_bytes m') (vm_limit (m_vmmaps m')) ->
  vm_backing_within_limit (MX m' (List.filter f mat)) = vm_backing_within_limit m'.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) ["Slack"] "h01zh13CANh23LENh31Rh41fh52m'h63math71vp;1p;3p;2p;5p;6g00DLj10Tg00V9j1JTg00VWj1CTg004kj1@Tg00[`j1ITg005ej1HTg005Kj33Tg009=j25Tg009]j2ATg01ZSj16Tg00Yoj11Tg01b8j14Tg01K7j2?Tg004Pj3>Tg00@Fj1=Tg01Knj2<Tg00ADj2;Tg00]:j29Tg01Lgj22Tg01\1j17Tg01boj3GTg01cij5FTg01ddj2BTg003Pj68Tg01GEj2DTg01ejj2ETg01fmj1:Tg00_Ag00OE#0#0#0#0#0#0#J#CR0#@R1g008=R2\0f2R3#I%H05311503p,4NMAX'Af4R1#6%11#4'?g00IRR4f5R5#6R6f3R7=>01R8,50#=g01VeR9'<R:';f0R;f6R<A>015R='9#1#4'2%7<%1<#4R>'2R?532X04g011TR@%15RA%6<150=#=/<9';R9%4;'2=32?X7@P4P6129>12;>532X04P6%4AP:P;f19G17DF%751B53E81958R3#11D58E8%731E58E8%:3%:5532eW3W2W1W4W6W5o"). Qed.

Lemma noreserve_backed_ok_X : forall flags mo mat nZ,
  m_vm_materialized mo = [] -> (length mat <= NMAX)%nat ->
  (mmap_noreserve_b flags = true \/ robust (nonlazy_bytes mo + nZ) (vm_limit (m_vmmaps mo))) ->
  mmap_noreserve_backed_ok flags (MX mo mat) nZ = mmap_noreserve_backed_ok flags mo nZ.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) ["Slack"] "p'0h01Rh11Eh21zh31Hh44__x1h54__x2h64__x3h74__x4h83CANh93Heqh:3LENh;4LEN0h<7__arithh=4__ffh>8__varmaph?5__with@1bi001bhA4cstrhB5cstr0hC1ehD5flagshE3mathF2mohG2nZhH1vp;1p;3p;2p;6p;4p;7p;5p;<g00DLj17Tg00V9j1eTg00VWj1WTg004kj1HTg00[`j1dTg005ej1MTg005Kj34Tg009=j2;Tg009]R0j2KTg00nOj19Tg01ZSj15Tg00ADj20Tg01K7j2>Tg01VKR1j2?Tg006Ej2ATg00]:j2:Tg01\1j16Tg01Lgj21Tg00T9j6LTg00^bj2VTg00@FR2j18Tg01Knj2DTg00Yoj1CTg01b8j1JTg00:7R3j2BTg00Aaj4TTg00BHj1ITg00Bmj2GTg00:Sj1RTg00CKj4FTg00;1j1QTg00;Oj1PTg00Cij2<Tg00ESj3=Tg01RLj1OTg01S1j3STg00F[j4cTg00GFj7bTg00<]j2aTg00=?j2`Tg00=kj3_Tg00>Jj4^Tg01h3j2]Tg01cij5\Tg01ddj2[Tg003Pj6ETg01GEj2ZTg01ejj2YTg01hnj3NTg00F6l<XTg008=R4f0R5g007?R634p=@%C5#Jp=3f1R7=445p=2g00I3g00IRR8P0P2P3g00J0f5R3f4R2f3R0f2R9P7P5M<Xp=Ug00OER:#7R;#7R<#7#7#7#7#e#WR=g00_A%H=R>%d9%M=54>1;=9p,4NMAXR>'K%93#@%52/09%32'>'?f6R?#9P41A45f7R@#9/25P4f9RA#9/25%@7%5A/0@%3A'>RB'?P4P4P9P6f:RC/:ARD#6f8RE'0%3D'1RDn0100000020000P4P4P9P6%6C/0E%3CRF'1RGn0100000020000'2]0]1P7%9ERH#@A4466%5E/0?%3E'>RI'?1A46RJW0W1g008]RK944HA44K6RH/?IP1PHPB12DGP5P5PHP4PKP4p-0P5g00e\RKg00f9n0110000020000XC4g00e@P6P5ELPKf=RKf<R6':R4#6f;RG'0%34'1%6K/0G%3KR4'1'2/V5b3b9X0HP5O1%5C/0E/>FP8%5GRF1;=CRH#8RDg01VeRB'DR1'0RI105CRL1:6G#3'1%66/0C%36RM'1RN'2X28g011TRO%CG%56RP1;=G#8/DBRQ'0/0CRR%J5'1/2NXHOP8PF11RM11LM'2X281KH>%8>RL,BDROPHPD1A8DP>PL1A8LEUP@CTPO%I>g00K1R>/BL1;=6R6#I%86,B>g00NYR6#M%H6P8P81G82P9%R8CFP71G80CF%Q8%P8R6g00L6g00LURLPLg00M5RLP81<8:RO1<8;R;5=8%O:,<81<8<5S8R<5=8g01_dA=8O<==8;Ccg00MUFb1a6LP5P9PJ1`59#@dA_8>7C^b=b>b?X48X58X68X7810571D90R>'0105>/07548^48^58^68^78P5PBf>,;=#8PKf?#5O4b<bBbAb;10FA/0110IA548P810PCRP/0Q1154%5K/0G/14'2X28PPPMPQP71]GED\PRP5ELb3%6G1[GEEE1:GCRE#C1ZGCEE%6E1YGCEEW0P5O1n200100000021000011000W0W1n0110000020001P5P9O2b1b@1:32=N?0AN?30'2eW0W:W8XG8WEWFWDo"). Qed.

Lemma fixed_rw_budget_ok_X : forall flags mo mat addr n,
  m_vm_materialized mo = [] -> (length mat <= NMAX)%nat ->
  robust (nonlazy_bytes (with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_next (m_vmmaps mo) addr n) mo)))
         (vm_limit (m_vmmaps mo)) ->
  mmap_fixed_rw_budget_ok flags (MX mo mat) addr n = mmap_fixed_rw_budget_ok flags mo addr n.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) ["Slack"] "h01lh11mh21vh33CANh43LENh51Rh64addrh75flagsh83math92moh:1np;1p;3p;2p;4p;6p;5g00DLj13Tg00V9j1NTg00VWj1LTg004kj1BTg00[`j19Tg005ej1MTg005Kj30Tg009=j2KTg009]j2DTg00Yoj12Tg01j;j36Tg00Zfj25Tg018Dj44Tg01ZSj1ATg01b8j1@Tg01K7j2>Tg00]:j27Tg01fmj18Tg013Sj2;Tg00ADj2=Tg014=j2<Tg004Pj3:Tg006Ej2JTg003Pj61Tg01kBj4HTg01lLj4ETg01mYj6FTg01n`j5GTg01FFj3CTg01GEj2ITg01oij4?Tg00OE#3#3#3#3#3#3#NR0#LR1g00_AR2%B1R3f3R4#9%M1R55031K14p,4NMAX'Df6R6P4f2R7f5R8#2R9?647/58C4#A%@9'>g011TR9%26R:g008=R;f8R<P8f4R=f0R>?68=f7R?/76'5C4#8P<P8P=%2??68=/5?C4R@#8RA30X29P2A6:=4R:/56RB/78RCP<P8P=P>C4#8=0;AX12P2P?P=P4PBC4R<1;0=RD1;04,=D'<RE=:18'7%8>=0;AX12P<P8PEP3%9B9:1EA03>5X03P3P51;08R01=0D'<=:1>=035X031J35%96P7E1%9<P?P=P4PBCHE1f1P9%2B%A@%@>'>X29P>%2<P?P=P4PBCEE1EFP?P=P4PCC4P?P=P4PBP8DGE11768RB,5:AC:68E1%2B1I68E1P?PBP=P4C?P?P6P=P4C?50;eW5W4W3X:1X61W8W9W7o"). Qed.

(* [comment removed for export] *)
Lemma fixed_rw_span_budget_ok_X : forall flags mo mat addr n,
  m_vm_materialized mo = [] -> (length mat <= NMAX)%nat ->
  robust (nonlazy_bytes (with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_span_next (m_vmmaps mo) addr n) mo)))
         (vm_limit (m_vmmaps mo)) ->
  mmap_fixed_rw_span_budget_ok flags (MX mo mat) addr n = mmap_fixed_rw_span_budget_ok flags mo addr n.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) ["Slack"] "h01lh11mh21vh33CANh43LENh51Rh64addrh75flagsh83math92moh:1np;1p;3p;2p;4p;6p;5g00DLj13Tg00V9j1NTg00VWj1LTg004kj1BTg00[`j19Tg005ej1MTg005Kj30Tg009=j2KTg009]j2DTg00Yoj12Tg0215j36Tg00Zfj25Tg018Dj44Tg01ZSj1ATg01b8j1@Tg01K7j2>Tg00]:j27Tg01fmj18Tg013Sj2;Tg00ADj2=Tg014=j2<Tg004Pj3:Tg006Ej2JTg003Pj61Tg01kBj4HTg01lLj4ETg01mYj6FTg01n`j5GTg01FFj3CTg01GEj2ITg022Aj4?Tg00OE#3#3#3#3#3#3#NR0#LR1g00_AR2%B1R3f3R4#9%M1R55031K14p,4NMAX'Df6R6P4f2R7f5R8#2R9?647/58C4#A%@9'>g011TR9%26R:g008=R;f8R<P8f4R=f0R>?68=f7R?/76'5C4#8P<P8P=%2??68=/5?C4R@#8RA30X29P2A6:=4R:/56RB/78RCP<P8P=P>C4#8=0;AX12P2P?P=P4PBC4R<1;0=RD1;04,=D'<RE=:18'7%8>=0;AX12P<P8PEP3%9B9:1EA03>5X03P3P51;08R01=0D'<=:1>=035X031J35%96P7E1%9<P?P=P4PBCHE1f1P9%2B%A@%@>'>X29P>%2<P?P=P4PBCEE1EFP?P=P4PCC4P?P=P4PBP8DGE11768RB,5:AC:68E1%2B1I68E1P?PBP=P4C?P?P6P=P4C?50;eW5W4W3X:1X61W8W9W7o"). Qed.

Lemma mprotect_budget_ok_X : forall mo mat addr n,
  m_vm_materialized mo = [] -> (length mat <= NMAX)%nat ->
  robust (nonlazy_bytes (mprotect_model_next mo addr n)) (vm_limit (m_vmmaps mo)) ->
  mprotect_budget_ok (MX mo mat) addr n = mprotect_budget_ok mo addr n.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) ["Slack"] "h03math13CANh23LENh31Rh44addrh51mh62moh71np;1p;3p;2p;6p;4g00DLj10Tg00V9j1FTg00VWj1<Tg004kj16Tg00[`j1ETg005ej1CTg005Kj32Tg009=j2;Tg009]j2:Tg01;]j31Tg01ZSj17Tg00Yoj18Tg01b8j19Tg01K7j2DTg00]:j24Tg01fmj13Tg004Pj3BTg01mYj6?Tg00gPj2>Tg00T9j6=Tg023Rj4@Tg003Pj6ATg024Yj35Tg00_AR0g00OE#0#0#0#0#0#0#F#<R1#6R2f3R3#E%C15221;13p,4NMAX':f5R4f2R5713#7%84#9'DP0f6R6f4R7;13R8/44g008=R9f0R:#3f7?147R;#3R<32X50P2g007?V1R0=B1414;:#3=29<X02P8P4P0P5f1P:E?P41>14E=1464R:?173P6P4P7P3C@EAA5:73A5673529eW3W2W1X71X41W0W6o"). Qed.

Lemma brk_r_ok_X : forall mo mat req r,
  m_vm_materialized mo = [] -> (length mat <= NMAX)%nat ->
  robust (nonlazy_bytes mo + bv_unsigned (bv_sub req (vm_brk (m_vmmaps mo)))) (vm_limit (m_vmmaps mo)) ->
  brk_r_ok (MX mo mat) req r = brk_r_ok mo req r.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) ["Slack"] "p'0h01bi001bh12Erh22Ebh31Hh41rh51zh64__x1h74__x2h84__x3h94__x4h:1ah;3CANh<3LENh=4LEN0h>1Rh?7__arithh@4__ffhA8__varmaphB5__withC4cstrhD5cstr0hE3mathF2mohG3reqhH1vp&0p;1p;3p;2p;4p;7p;5p;6p;8p;<g00DLj1KTg00V9k10;Tg00VWj1tTg004kj1\Tg00[`k10:Tg005ej1aTg005Kj3>Tg009=j2?Tg009]R0j2]Tg01ZSj1<Tg00Yoj19Tg01ICj1:Tg00ADj28Tg01b8j1;Tg01K7k208Tg025dj1fTg013Sj21Tg026^j1WTg027Zj22Tg0287j2CTg00j6j36Tg028Tj14Tg029Rj1BTg00iVj2nTg02:Jj2=Tg02;0j2MTg00]:j2[Tg01\1j1PTg007_j20j1eTg006Ej2@Tg02;Mk309Tg00@FR1j1NTg01Lgj2GTg00:7R2j2VTg00Aak403Tg00BHj1`Tg00Bmj2dTg00:Sk102Tg00CKj4_Tg00;1k100Tg00;Oj1~Tg00Cij2TTg00ESj3STg01RLj1{Tg01S1j3zTg00F[j4yTg00GFj7xTg00<]j2sTg00=?j2rTg00=kj3qTg00>Jj4pTg01Knj2UTg01h3j2oTg01cij5vTg00T9j6wTg02<Bj8^Tg003Pj6Lj7|Tg02<_j1mTg01ddj2}Tg01ejj2lTg01GEk201Tg02=Cj3cTg02>@j3kTg02>ej1jTg02?_k105Tg02@Uj3iTg02A2j3gTg00F6m<06Tf3R3f2R4f1R5f0R63k'1p=7g00K1R7/241256'0p=E%j5&0565i4p=Ag01VeR8,86p=bf5R9f4R:'G1=569g34'0p=Q1845/G6,03p=5g008=R;?>56p=31?56#Np=Z1U68,85p=Y%N6/U8p=I1845/86p=F1G56,04p=Hf6R</G91858/M6,=49g:3'0p=Dg007?R=9>;6p=O1276p=h1256,04p=X1U68p>0710=6p=Jg00I3g00IRR>P0P1P2g00J0P9P:P3P4P5P6N<06p>041845/G6p=ug008]R29>;6p=Rg00_Ag00OER1#KR0#KR?#K#K#K#K$0;R@#tRA#\RB&0:3%aA5>B1?A3p,4NMAXRB']%<9P@P@P3%99RC#:C7'8%;C+08g011TRC%9<RDP;P;%f9RE11@9RF%W6,1@'2'C%:6RG96@:RHP;P;11@GRI,2FA6@:9RJ/CHRHP;P;11@:RK9EIIP;P;%4IRI%4KRL'2PL%B61nAARM?A661=@IP@%bLRN/MIEQP=n0100000020000f7RI/[<#PP@P@P:PGC7%;6C5P=n0100000020000,0Hn0100000020001n0100000020001P;P;%9IRH#W,1@,2F,CERE%:HRG96@:ROP;P;11@GRP,2FRQ1CJORJP;P;AEPPKRRP;P;%4PRP/2LPL%BHAAMHH1=@PP@1MNPEQP=n0100000020000RP%PIP@P@P:PGC7RG%;HRHC5P=n0100000020000,0Jn0100000020001n0100000020001RN'3XHCP>%<<RC1ZA9'YP;P;PEPOP;P;PQPJP;P;PRPPP6PGPHC5P=n0100000020000,0Jn0100000020001n0100000020001RL/3NX5>P>PCP;P;PEPOP;P;PQPJP;P;PR%<I1?A<#I;FG=HPHP=n0100000020100,0Jn0100000020001n0100000020001/3LX5>%f:%WD,1@,2K'CP;P;P;P;P6f8RK#9RD#:RL96@9RJP;P;11@<RH11@LRP'2RGA6@9<RR/CJREP;P;AEPPFRCP;P;%4PRP%4FRF'2PF%BDAAMDD1=@PP@PFPPFDP=n0100000020000RP%<KRF1?AI#IP@P@P9PLC7RL3F%;DRD3HP=n0100000020100,0En0100000020001n0100000020001P;P;P6PJP;P;PGPEP;P;PCPPPFPLPDC5P=n0100000020000,0En0100000020001n0100000020001'3P61@;OPQP;P;P;P;P6A6@<IRQf9RO#9RD#:RL96@<'CRFP;P;11@LRP?EPHRCP;P;%4PRP%4HRH'2PH%BDAAMDD1=@PP@PHPPFDP=n0100000020000RP%<ORH1?AK#IP@P@P<PLC7RL3F%;DRD3HP=n0100000020100,0Fn0100000020001P;P;P6PFP;P;PCPPPHPLPDC5P=n0100000020000,0Fn0100000020001'3P61@;EPRP;1@;6RR13Q6P;A6@KO/36f<RQ#9RE#:RF96@ORD,C5RLP;P;11@FRH11@ORP7EHRCP;P;%4HRH%4PRP'2PP%BEAAMEE1=@HP@PPPHFDP=n0100000020000RH%<QRPf;RG,?A#IP@P@POPFC7RF3F%;ERE3HP=n0100000020100'0P;P;PCPHPPPFPEC5P=n0100000020000,0L'3]1P5A6@IKRI#Og00R3A6@56#OA>A45[RLA>A56A6@45#ORE[A>A34\EB09@56P5n2001000000120000000X0AX:AREPL^0A^:ARLP6POf:RFP5O3A>AOFPAPGP;P;f>RP#9RH#:RC,1@RJ#hRN11@6RS7XJRTP;P;%4JRU%4SRS'2PS%BHRVAAMHHRW1=@URXP@PSPUFDP=n0100000020000RS%<PRYf=RZ,?AR[#NR\$07R]'8R^P@P@P6PCC7R_%;HRHC5P=n0100000020100#JP;P;PTPSPYP_PHC5P=n0100000020000#J'3X4A%9Z#:R_,1@RS11@GRT7ESP;P;P;P;P6P;P;f?RS#9R`#:Ra,1@Rb#4Rc11@Z#4Rd'2Pd%B`ReAAM``Rf1=@cRgP@PdPcFDP=n0100000020000Rd%<SRh1?AP#IRi'8RjP@P@PZPaC7Rk'8Rl%;`R`3HP=n0100000020100#JP;P;P618hkRk=Hd`P=n0100000020000#J'3P6P;P;%e=RdPdP;P;11@QRm#4Rn,2UPnPVPWPXP@%bnRo/MUEQP=n0100000020000RpP@P@PQPCC7Rq,8^Rr/GHRs'018YqRq/GHRt,0pP;\;Ru/@dP;P;%epRpPpPsPt1@up1][B%NBRp,V\RuP[P\1@>\PBPp1@>pJ04POH03Pu%`B1V7p1?ASRp#`%Np,V7g00NYRp#a%\pP>P>1d>:P4&02>C_P51d>3C_&00>%~>Rpg00L6g00LURBPBg00M5RBP>1T>1Ru1T>0R05S>%{1,T>1T>?5z>R?5S>g01_dAS>u?=S>0Cyg00MUFx1spBP6P41@;=RB1r64#OdAq>75Cpb@bAbBX6>X7>X8>X9>1U43R79F65AF6755>>^6>^7>^8>^9>P6P8fAR8,ZAR7P@P@f@RpfBR0#9R?#:RuC7%<0R1O4b?bDbCb=18q]=>>rP>18ki%9pRr#;Rq,G6%<pP@P@PP%:rRrC7;uq'3X5>PkP`PiPO1oPFDvPlP6Ewb3G^G^10==,@;n0110001020100b0PFP6ELb1b3%9GRl#:RO96@KRi,C=RkP;P;11@OR>11@KRq7E>RpP;P;%4>R>%4qRq'2Pq%BlAAMll1=@>P@PqP>FDP=n0100000020000R>%<GRq1?AF#IP@P@PKPOC7RO3F%;lRl3HP=n0100000020100RK'0P;P;PpP>PqPOPlC5P=n0100000020000Rl,0k'3eW1%RIPiP;PR13D6P;A6@GC/36P;P;AEbbmRmP;P;12cnPnPePfPgP@1MocEQP=n0100000020000RoPjP@P@PQPaC7RjP`C5P=n0100000020100,05P;P;PmPoPhPjP`C5P=n0100000020000,05'3]2P5A6@F_R_#OPEPLP6PQPaP5O3A>AQaPAPrA6@6S#RP;P;11@uRS11@5Ra7ESRQP;P;%4SRL%4aRa'2Pa%B?REAAM??RF1=@LR`P@PaPLFDP=n0100000020000Ra1Y17R7P@P@P5PuC7R5%;?R?C5P=n0100000020100P;P;PQPaP1P5P?C5P=n0100000020000'3]1X4AA6@rP#R%98#:,1@#hP;P;P;P;fCR8#9Rr#:RP,1@R5=X65RaP;P;%45R5/25P5%BrAAMrr1=@5P@P5P5FDP=n0100000020000R5%<8R81?A0#IP@P@PPPPC7RP3F%;rRr3HR0P=n0100000020100P;P;PaP5P8PPPrC5RrP=n0100000020100'3P6P;P2P;P;P6P0P=n0100000020100P;P;P6PrP=n0100000020100'3X0;PB12SSRr%mSELP;P;%JrRSP;P;12LLPLPEPFP`P@PLPLFDP=n0100000020000RLP7P@P@PuPuC7RuP?C5R7P=n0100000020100P;P;PSPLP1PuP?C5R?P=n0100000020100'3ePBP;P;102rRrP7P=n0100000020100P;P;PrP?P=n0100000020100'3en0110001020101b0W1PZP6P9F|b2b3P;P;AXNJTRNP;P;%4TRT,2UPTPVPWPXP@PTPUFDP=n0100000020000RUP^P@P@PGPCC7RCPHC5P=n0100000020100RG#JP;P;PNPUPYPCPHC5P=n0100000020000R=#J'3eW2%R_1@;2102G102='3eW2n0110001020101P6O1b2b01C2iRi/0K10il'3eW1n0110001020101P6O1b1b0n0110001020001b0n0110001020001b0%P<1}<4EL1[<9R4#P1l<9EL%94201<9ELAc4:3Ac<:3'3eW>W<W;X4AXGAWEWFo"). Qed.

End Slack.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma strip_with_vmmaps : forall h m, strip (with_vmmaps h m) = with_vmmaps h (strip m).
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h01hh11mp;1p;2g00Y9j12Tg00Zfj21Tg006Ej20Tg011Tg00_AR0f1f0#2'1,00W1W0o"). Qed.
Lemma vmmaps_strip : forall m, m_vmmaps (strip m) = m_vmmaps m.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h01mp;1p;2g00Yoj11Tg006Ej20Tg00_Ag011Tf0#1'0W0o"). Qed.
Lemma strip_vm_add_lazy : forall a n m, strip (vm_add_lazy a n m) = strip m.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h01ah11mh21np;1p;2g00DLj10Tg00V9j14Tg00VWj12Tg00Y9j11Tg006Ej23Tg00OE#0#0#0#0#0#0#4#2R0g00_AR1f0#1,31W1X20W0o"). Qed.
Lemma strip_vm_forget_range : forall lo hi m, strip (vm_forget_range lo hi m) = strip m.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h02hih12loh21mp;1p;2g00Y9j11Tg006Ej20Tg00IRR0g00_AR1f0#1,01W2X00W1o"). Qed.
Lemma strip_with_mmap_backing : forall f a n m, strip (with_mmap_backing f a n m) = strip m.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "p'0h01ah11bi001bh21fh31mh41np;1p;3p;2p;4g00DLj10Tg00V9j18Tg00VWj14Tg00nOj13Tg00oTj37Tg00Y9j11Tg005Kj32Tg006Ej25Tg010Nj46Tg00OE#0#0#0#0#0#0#8#4R0g00_AR1f3R2#3g008=R3P3P3P1f0R3f4f2R4772P4n0100000020000#1%14521P3f1R5#1,51R6P6n0110000020000b1P2P4P5P3C6#1%13521eW3X40X00W2o"). Qed.
Lemma strip_with_mmap_destroyed : forall a n h m, strip (with_mmap_destroyed a n h m) = with_vmmaps h (strip m).
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h01ah11hh21mh31np;1p;2g00DLj10Tg00V9j15Tg00VWj12Tg00Y9j11Tg00Zfj24Tg006Ej23Tg00OE#0#0#0#0#0#0#5#2R0g011Tg00_AR1f1f0#1'4,31W2W1X30W0o"). Qed.
Lemma strip_with_mmap_replacement : forall f a n m, strip (with_mmap_replacement f a n m) = strip m.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h01mh11ah21fh31np;1p;2p;3p;4p;6g00DLj10Tg00V9j1<Tg00VWj15Tg013Sj23Tg00ADj2;Tg015>j3:Tg00Y9j11Tg005Kj32Tg006Ej26Tg010Nj47Tg02Alj44Tg003Pj68Tg018Dj49Tg00OE#0#0#0#0#0#0#<R0#5R1g00_AR2P2f2R3,30R4f1R5,30,;4f0R43:R0#1%159224X02%14R6,62f3R7P3P5P0C7#1P7P3P5P0C4E8P7P3P5P4C9#1=226eW0X31X11W2o"). Qed.
Lemma strip_mprotect_model_next : forall m a n, strip (mprotect_model_next m a n) = with_vmmaps (m_vmmaps (mprotect_model_next m a n)) (strip m).
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h01ah11mh21np;1p;3p;2g00DLj10Tg00V9j17Tg00VWj12Tg01;]j31Tg00Yoj16Tg00Y9j15Tg00Zfj23Tg006Ej24Tg00_AR0g00OE#0#0#0#0#0#0#7#2R1f2R2f1f031#6%52'3,40X21W0W1o"). Qed.
Lemma strip_madvise_dontneed_next : forall m a n, strip (madvise_dontneed_next m a n) = strip m.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h01ah11mh21np;1p;2g00DLj10Tg00V9j14Tg00VWj12Tg00Y9j11Tg006Ej23Tg00_AR0g00OE#0#0#0#0#0#0#4#2R1f2#1,30X21W0W1o"). Qed.
Lemma with_vmmaps_idem : forall h h' m, with_vmmaps h (with_vmmaps h' m) = with_vmmaps h m.
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h01hh12h'h21mp;2g00Zfj21Tg006Ej20Tg011TR0g00_AR1f2f0'1,01W2X10W0o"). Qed.
Lemma with_vmmaps_strip_vmmaps : forall m h, with_vmmaps (m_vmmaps (with_vmmaps h (strip m))) (strip m) = with_vmmaps h (strip m).
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) [] "h01hh11mp;1p;2g00Y9j12Tg00Zfj21Tg006Ej20Tg00_AR0g011Tf0f1#2'1,00W0W1o"). Qed.

(* [comment removed for export] *)
Ltac strip_tac :=
  rewrite ?strip_with_mmap_replacement, ?strip_with_mmap_backing, ?strip_with_mmap_destroyed, ?strip_with_vmmaps,
          ?vmmaps_with_mmap_replacement, ?vmmaps_with_mmap_backing;
  first [ reflexivity | apply strip_self ].

(* [comment removed for export] *)
Ltac xfer_leaf :=
  first [ exact I
        | apply relX_id
        | apply relX_same; [ strip_tac | rewrite ?mat_with_mmap_backing; reflexivity ]
        | apply relX_filter; [ strip_tac | rewrite ?mat_with_mmap_replacement, ?mat_with_mmap_backing; reflexivity ]
        | apply relX_ret_only ].

(* [comment removed for export] *)
Ltac xfer_push :=
  progress (rewrite ?m_vmmaps_MX, ?with_vmmaps_MX, ?with_mmap_backing_MX, ?with_mmap_destroyed_MX,
                    ?with_mmap_replacement_MX, ?mprotect_model_next_MX).

Ltac xfer :=
  cbv zeta;
  repeat first
    [ xfer_leaf
    | lazymatch goal with
      | |- relX _ _ (match ?x with _ => _ end) (match ?x with _ => _ end) => destruct x
      end
    | xfer_push ].

Section Transfer.
Variable NMAX : nat.

Lemma check_munmap_X : forall addr len eff mo mat,
  relX mo mat (check_munmap addr len eff (MX mo mat)) (check_munmap addr len eff mo).
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) ["Transfer"] "p'0h01bi001bh11mi011mh21pi021ph3:eff_copiesi03:eff_copiesh4;eff_copyinsi04;eff_copyinsh5:eff_writesi05:eff_writesh69eff_zerosi069eff_zerosh74addrh83effi073effh97eff_reti087eff_reth::eff_unmapsi09:eff_unmapsh;3lenh<3math=2moh>1vi0:1li0;2m0i0<1ri0=1si0>2usp;1p;2p;4p;3p;5p;6p;7p;8g00DLj1GTg00V9j1XTg00VWj1UTg004kR0j1BTg00Yoj12Tg013Sj21Tg02C4j2VTg02CTj2TTg02D1j1STg025dj1ITg0287j2RTg02DOj1[Tg00]:j24Tg005ej1ZTg00hLj40Tg028Tj1DTg00ADj2JTg027Zj2OTg02?_j1ETg02:Jj2FTg02EGj3HTg00iVj2MTg01C_j4@Tg006_j3?Tg02F=j2>Tg007_j2ATg012Kj46Tg00W:j23Tg02GCj3CTg00XDj45Tg02HFj2QTg014=j2=Tg004Pj3<Tg02I?j5KTg00Y9j1NTg00Zfj2PTg005Kj3jTg006Ej2YTg02J=j4iTg003Pj6LTg00[`j1hTg02KGj7gTg02LCj5fTg01GEj2eTg02MJj4WTg02NRj1`Tg02OLj3_Tg02>ej1^Tg02PHj1aTg01ICj1bTg01b8j1]Tg02QCj1cTg02R>j1dTg02S7j8\Tf1R1f0R2#D'Fp=9%E1/Q2p=;f2R31112'Jp=:%`3?_12p=7f7R4#^f6R5f5R6f4R7#af3R8#b%]3%c1%d2G\p=8g00OE#G#G#GR9#G#G#G#XR:#UR;g00lYR<g00_AR=%B;R>g011TR?%21R@P3P1g008=RAg00`7RB11:6RCg01VeRD'Vg00K1RE'T#S%I7'RRFP8g02Sn#[RG1431RHg00aA#ZRIC0RJPAPBg02TcRK11:7RL#DRM,JC'ORNPJPAPB%E21F:MRO7H6P<PBP8P0%X9#U#B,M;R9PBP7P01M;;RPPBP8P0g00mWRQPBP1P0g00I3,M;RRPBP2PAPB%I6RSP;P;f;RTf:RU,1:RV,9:RWC@%ZPRX5?P,>3'ARYPTPWP51;5T11:TRZA:Z:WR[575P5P5P5P5P5G8f8R\/44C6/3Ig00b7R]n0100000020000P]n1011040002012010210:P]n1011030002012010;10:P]n1011060002012010210:P]n1011050002012010210:n0110700016110<10510610>103104PAPBAC26MP81F:ER^PHPIC0RHg00cAR_n0100000020000n0100000020100n0100000020001n0100000020001PAPBPFP8PGP3PIC0R`PAPBPNP`PAPB%23R`#E?H6OROP<PBP8P0P9PBP7P0PPPBP8P0PQPBP1P0PRPBP2PAPBPYPTPW%2\RW1;WTA7WZ[PWPWPWPWPWG8P\C6/3IP]n0100000020000P]n1011040002012010210:P]n1011030002012010;10:P]n1011060002012010210:P]n1011050002012010210:n0110700016110<10510610>103104PAPBAC`6MR`P8P^P3PIC0P_n0100000020000n0100000020100n0100000020001n0100000020001RMC5X>?P=P711:8#DR?,F:RWP@%E@R[/Q7A:L:WRa97@LP@P@P@P@P@G8RbP1C61=La=<;2'4P3P1PAPBPFPJPAPBPNPJPAPBPOP<PBP8P0P9PBP7P0PPPBP8P0PQPBP1P0PRPBP2PAPBPY135IP]n0100000020000P]n1011040002002010210:P]n1011030002002010;10:P]n1011060002002010210:P]n1011050002002010210:n0110700016010<10510610>103104PAPBP`PHP_n0100000020000n0100000020000n0100000020001n0100000020001PMC5X1=1VLD/TE#S%I8'RREPAPAP8P3PAPBP2P7PG1483RDPIC0RMPAPB11:5RH%DCRC'J,OKR`PMPAPB%28RM#E1F:C7H5RYP<PBP7P0P9PBP7P0PPPBP8P0PQPBP1P0PRPBP2PAPBP;P;f<RO19:ZRZC@=?PX,>3,ASRJPOPZf9RF#2Ra1;aO11:OROA:O:ZRZ57aPaPaPaPaPaG8PFC6Ra1=OZ=<;\'4/3IP]n0100000020100P]n1011040002012010210:P]n1011030002012010;10:P]n1011060002012010210:P]n1011050002012010210:n0110700016110<10510610>103104PAPBACM5CRMP7P^PDPIC0P_n0100000020000n0100000020100n0100000020001n0100000020001PAPBP2P7PGP8PIC0RDPAPBP`PDPAPBPYP<PBP7P0P9PBP7P0PPPBP8P0PQPBP1P0PRPBP2PAPBPJ13aIP]n0100000020000P]n1011040002012010210:P]n1011030002012010;10:P]n1011060002012010210:P]n1011050002012010210:n0110700016110<10510610>103104PAPBPMP7P^P8PIC0P_n0100000020000n0100000020100n0100000020001n0100000020001C5P2P3P1P8PGPIDKPNPAPAP7P8PAPBP2P6PG1478RNPIC0PAPB%27RM#E%DHRH,F:7H4RaP<PBP6P0P9PBP7P0PPPBP8P0PQPBP1P0PRPBP2PAPBP;P;f=RJ19:OROC@=?PX,>3,ASRDPJPO%2UR`1;`J11:JRJA:J:ORO57`P`P`P`P`P`G8PUC6R`1=JO=<;F'4/3IP]n0100000020100P]n1011040002012010210:P]n1011030002012010;10:P]n1011060002012010210:P]n1011050002012010210:n0110700016110<10510610>103104PAPBACM4HRHP6P^PNPIC0P_n0100000020000n0100000020100n0100000020001PAPBP2P6PGP7PIC0PAPBPaP<PBP6P0P9PBP7P0PPPBP8P0PQPBP1P0PRPBP2PAPBPD13`IP]n0100000020000P]n1011040002012010210:P]n1011030002012010;10:P]n1011060002012010210:P]n1011050002012010210:n0110700016110<10510610>103104PAPBPHP6P^P7PIC0P_n0100000020000n0100000020100n0100000020001C5P2P8P3P7PGPIDKPYPAPAP6P7PAPBP2P<PBP5P0P9PBP7P0PPPBP8P0PQPBP1P0PRPBP2PAPBP;P;f>RY19:JRJC@=?PX,>3,ASR`PYPJ%2TRD1;DY11:YRYA:Y:JRJ57DPDPDPDPDPDG8PTC6RT1=YJ=<;U'4/3IP]n0100000020100P]n1011040002012010210:P]n1011030002012010;10:P]n1011060002012010210:P]n1011050002012010210:RJn0110700016110<10510610>103104PAPB%2611:4#D7C\R\P5P^1467PIC0P_n0100000020000n0100000020100PAPBP2P<PBP5P0P9PBP7P0PPPBP8P0PQPBP1P0PRPBP2PAPBP`13TIP]n0100000020000P]n1011040002012010210:P]n1011030002012010;10:P]n1011060002012010210:P]n1011050002012010210:RTn0110700016110<10510610>103104PAPBP\P5P^P6PIC0P_n0100000020000n0100000020100C5P2P<P6P7P<PBP2PJn0110700016110<10510610>103104P<PBP2PTn0110700016110<10510610>103104C5P6%B9RT%BPRJ%BQR\%BRR`P0P9fARYf@RDP0P9PBP2P0PPPBP7P0PQPBP3P0PRPBP1PAPB%I5P;P;fDRafCRN,1:,9:RMC@=?PX,>8'AROPaPM%2YRC1;Ca11:aRZA:Z:MRc57CPCPCPCPCPCG8RCPYC6Rd1=ZcRc=<;D'4/3IP]n0100000020100ReP]n1011040002012010210:RfP]n1011030002012010;10:RgP]n1011060002012010210:P]n1011050002012010210:P0P9PBP2P0PPPBP7P0PQPBP3P0PRPBP1PAPBPO13dIP]n0100000020000ROP]n1011040002012010210:RhP]n1011030002012010;10:RiP]n1011060002012010210:P]n1011050002012010210:C5P7P0PPPYPDP0PPPBP2PgP]n1011060002012010210:P0PPPBP2PiP]n1011060002012010210:C5P8P0PQPYPDP0PQPBP2PfP]n1011030002012010;10:P0PQPBP2PhP]n1011030002012010;10:C5P1P0PRPYPDP0PRPBP2PeP]n1011040002012010210:P0PRPBP2POP]n1011040002012010210:C5P2P;P;PNfBRN,1:,9:C@=?PX,>3,ASPAPAPNPYPAPBP2fERO19:ZRZ%2NRe1;eO11:OROA:O:ZRZ57ePePePePePeG8PNC6Re1=OZ=<;Y'4/3IP]n0100000020100PAPBP213eIP]n0100000020000C5P2PYPDPdPcPIP=%NYRD,PC%2e%NN'P9j=2X1=%2d/PD,Y=%NdPaPMPCPYCiEL%hY9<;c,Y>Fgg00e@R>n0110001020100b0P>X4`X2RP1P2O2n10110:0102012010210:P>X3\X1QP1P2O2n10110:0102012010110:P>X6JX2PP1P2O2n10110:0102012010210:P>X5TX29P1P2O2n10110:0102012010210:W4W3X:JW6W5X9;P6P7P8P3P1P2O6n0110=010161108105106109103104PHPAPAP5P6PAPBP2P4P^1456PIC0P_n0100000020000PAPBP2P4P^P5PIC0P_n0100000020000C5P2P6P7P5P^PIDKP>n0110000020000b0n0110001020100b0n0110001020001b0n0110001020001b0P1P2PAPBPEP3PG1412R>PIC0R6PAPB1JL?,OKRKP6PAPBAH[7WR[P<PBP3P0P9PBP7P0PPPBP8P0PQPBP1P0PRPBP2PAPBP;P;PU11:F,9:RFC@=?PX,>3,ASRSPUPF%24RX1;XUA:V:FRF97XVPXPXPXPXPXG8P4C6R41=VF=<;5'4/3IP]n0100000020100P]n1011040002012010210:P]n1011030002012010;10:P]n1011060002012010210:P]n1011050002012010210:n0110700016110<10510610>103104PAPBAC@7?R?P3P^P>PIC0P_n0100000020000n0100000020100n0100000020001n0100000020001PAPBPEP3PGP1PIC0RGPAPBPKPGPAPBP[P<PBP3P0P9PBP7P0PPPBP8P0PQPBP1P0PRPBP2PAPBPS134IP]n0100000020000P]n1011040002012010210:P]n1011030002012010;10:P]n1011060002012010210:P]n1011050002012010210:n0110700016110<10510610>103104PAPBP?P3P^P1PIC0P_n0100000020000n0100000020100n0100000020001n0100000020001C5eP7PWPbP>C6P7PWPbP1P2DfEL%2>1e12ELP1P2P7P8P3P>CWP7P8P3P1CWC5eW<W=W8X;;W7o"). Qed.

(* [comment removed for export] *)
Lemma check_madvise_X : forall addr len advice eff mo mat,
  relX mo mat (check_madvise addr len advice eff (MX mo mat)) (check_madvise addr len advice eff mo).
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) ["Transfer"] "p'0h01bi001bh11pi011ph2:eff_copiesi02:eff_copiesh3;eff_copyinsi03;eff_copyinsh4:eff_unmapsi04:eff_unmapsh5:eff_writesi05:eff_writesh61mi061mh74addrh86adviceh93effi073effh:7eff_reti087eff_reth;9eff_zerosi099eff_zerosh<3lenh=3math>2moh?1vi0:1li0;2m0i0<1ri0=1si0>2zsp;1p;2p;4p;3p;5p;7p;6g00DLj1?Tg00V9j1RTg00VWj1LTg004kR0j1ATg00Yoj19Tg013Sj21Tg02C4j2NTg02CTj2MTg02D1j1BTg02DOj1XTg00]:j27Tg005ej1JTg00hLj40Tg02U[j1HTg025dj1ETg02:Jj2>Tg028Tj1@Tg00ADj2=Tg01Lgj2CTg02Vej3<Tg00iVj2GTg01<ij33Tg00W:j24Tg00XDj42Tg02I?j5FTg004Pj3DTg00Y9j1WTg00Zfj2VTg006Ej2OTg00[`j1UTg02KGj7TTg02X0j4STg003Pj6ITg01GEj2^Tg02Y9j5QTg01C_j4]Tg006_j3\Tg02F=j2[Tg007_j2ZTg014=j2PTf1R1f0R2#@'>p=5f7R3f6R4f5R5f4R6f3R7f2R8P1C];\2'['Zp=61=12,P8p=KAD812,77p=Y1112,=8p=:1P81=D72p=;1781/42p=8g00OE#?#?#?R9#?#?#?#RR:#LR;g00lYR<g00_AR=%A;R>g011TR?%91R@P8P1g008=RAg00`7RB11:4RCg01VeRD'Ng00K1RE'M#BRFP7g02Sn#XRG1781RHg00aA#JRIC0RJPAPB%H6#BRKg00cARLPAPB%E5RMP71>:ERNPHPIC0RHPAPBg02ZERO11:5RP#@RQ,=C'CRRPJPAPB1>:QRQ9<24P<PBP7P0%R9#L#A,G;R9PBP6P01G;;RSPBP8P0g00mWRTPBP1P0g00I3,G;RUPBP2PAPBPMP7PSP;P;f<RVf;RW,1:RX,5:RY%JSRZG6R[f8R\/73?3VY/4Ig00b7R]n0100000020000P]n1011030002002010110:P]n1011020002002010;10:P]n1011040002002010110:P]n1011050002002010110:n0110700016110<10510>104102103PLn0100000020100n0100000020001n0100000020001n0100000020001n0100000020001PAPBPFP7PGP8PIC0R^PAPBPKPLPAPBPMP7PNP8PIC0PAPBPRP^PAPB%98?<4QRQP<PBP7P0P9PBP6P0PSPBP8P0PTPBP1P0PUPBP2PAPBP[A3\VY/4IP]n0100000020000P]n1011030002002010110:P]n1011020002002010;10:P]n1011040002002010110:P]n1011050002002010110:n0110700016110<10510>104102103PLn0100000020100n0100000020001n0100000020001n0100000020001n0100000020001RYC2X??P=11:6#@R?,>:R^9315P;11:^9KPPP2CYP8P1PAPBPFPJPAPBPKPLPAPBPMPHPAPBPRPJPAPBPQP<PBP7P0P9PBP6P0PSPBP8P0PTPBP1P0PUPBP2PAPBP[144IP]n0100000020000P]n1011030002002010110:P]n1011020002002010;10:P]n1011040002002010110:P]n1011050002002010110:n0110700016010<10510>104102103PLn0100000020000n0100000020001n0100000020001n0100000020001n0100000020001PYC2X6=1NPD/ME#BREPAPAP7P8PAPBP2P6PG1778RDPIC0RYPAPB%H5#BR[PLPAPB%E4RQP6PNPDPIC0PAPB11:3RD%@CRC'=,CORJPYPAPB%971>:C7<3RCP<PBP6P0P9PBP6P0PSPBP8P0PTPBP1P0PUPBP2PAPBPMP7PSP;P;f=RY11:V,5:RRPZG6RHf9RF?3YRR_P;11:YR`A:`:RP\C;;8IP]n0100000020000P]n1011030002012010110:P]n1011020002012010;10:P]n1011040002012010110:P]n1011050002012010110:n0110700016110<10510>104102103PLn0100000020100n0100000020001n0100000020001n0100000020001n0100000020001PAPBP2P6PGP7PIC0RRPAPBP[PLPAPBPQP6PNP7PIC0PAPBPJPRPAPBPCP<PBP6P0P9PBP6P0PSPBP8P0PTPBP1P0PUPBP2PAPBPH14_IP]n0100000020000P]n1011030002002010110:P]n1011020002002010;10:P]n1011040002002010110:P]n1011050002002010110:n0110700016110<10510>104102103PLn0100000020100n0100000020001n0100000020001n0100000020001n0100000020001C2P2P8P1P7PGPIDFPKPAPAP6P7PAPBP2PLPAPB%E3RKP5PN1767R_PIC0PAPB11:\RH%@DRD'=,CORCP5PGP_PIC0PAPB%961>:D7<\RDP<PBP5P0P9PBP6P0PSPBP8P0PTPBP1P0PUPBP2PAPBPMP7PSP;P;f>R_15:`R`PZG6RRf:RJ?3_`R[P;11:_R_A:_:`PFC;;8IP]n0100000020000P]n1011030002012010110:P]n1011020002012010;10:P]n1011040002012010110:P]n1011050002012010110:n0110700016110<10510>104102103PLn0100000020100n0100000020001n0100000020001n0100000020001PAPBP2PLPAPBPKP5PNP6PIC0PAPBPCP5PGP6PIC0PAPBPDP<PBP5P0P9PBP6P0PSPBP8P0PTPBP1P0PUPBP2PAPBPR14[IP]n0100000020000P]n1011030002002010110:P]n1011020002002010;10:P]n1011040002002010110:P]n1011050002002010110:n0110700016110<10510>104102103PLn0100000020100n0100000020001n0100000020001n0100000020001C2P2g00e@R[PQPAPAP5P6PAPBP2P4PN1756RRPIC0PAPB11:FRD%@HRH'=,CORKP4PGPRPIC0PAPB%951>:H7<FRFP<PBP4P0P9PBP6P0PSPBP8P0PTPBP1P0PUPBP2PAPBPMP7PSP;P;f?RH15:_R_PZG6RRA3WH_R`P;11:HRHA:H:_PJC;;8IP]n0100000020000P]n1011030002012010110:P]n1011020002012010;10:P]n1011040002012010110:P]n1011050002012010110:n0110700016110<10510>104102103PLn0100000020100n0100000020001n0100000020001PAPBP2P4PNP5PIC0PAPBPKP4PGP5PIC0PAPBPFP<PBP4P0P9PBP6P0PSPBP8P0PTPBP1P0PUPBP2PAPBPR14`IP]n0100000020000P]n1011030002002010110:P]n1011020002002010;10:P]n1011040002002010110:P]n1011050002002010110:n0110700016110<10510>104102103PLn0100000020100n0100000020001n0100000020001C2P2P6P7P5PNPIDFPCPAPAP4P5PAPBP2P3PG1745PIC0PAPB%9415:D7<JRDP<PBP3P0P9PBP6P0PSPBP8P0PTPBP1P0PUPBP2PAPBPMP7PSP;P;f@RC15:HRHPZG6R`A3VCHRRP;11:CRCA:C:HPWC;;8IP]n0100000020000P]n1011030002012010110:P]n1011020002012010;10:P]n1011040002012010110:P]n1011050002012010110:n0110700016110<10510>104102103PLn0100000020100n0100000020001PAPBP2P3PGP4PIC0PAPBPDP<PBP3P0P9PBP6P0PSPBP8P0PTPBP1P0PUPBP2PAPBP`14RIP]n0100000020000P]n1011030002002010110:P]n1011020002002010;10:P]n1011040002002010110:P]n1011050002002010110:n0110700016110<10510>104102103PLn0100000020100n0100000020001C2P2P5P6P4PGPIDFPFPAPAP3P4PAPBP2P<PBP\P0P9PBP6P0PSPBP8P0PTPBP1P0PUPBP2PAPBPMP7PSP;P;fARF15:CRCPZG6RRA3YFCRYP;11:FRFA:F:CPVC;;8IP]n0100000020000P]n1011030002012010110:P]n1011020002012010;10:P]n1011040002012010110:P]n1011050002012010110:RVn0110700016110<10510>104102103PLn0100000020100PAPBP2P<PBP\P0P9PBP6P0PSPBP8P0PTPBP1P0PUPBP2PAPBPR14YIP]n0100000020000P]n1011030002002010110:P]n1011020002002010;10:P]n1011040002002010110:P]n1011050002002010110:RYn0110700016110<10510>104102103PLn0100000020100C2P2P<P3P4P<PBP2PVn0110700016110<10510>104102103P<PBP2PYn0110700016110<10510>104102103C2P3%A9RY%ASRV%ATRR%AUR\P0P9fCRFfBRCP0P9PBP2P0PSPBP7P0PTPBP8P0PUPBP1PAPBPQP6PSP;P;fGRQfFR`,1:,5:RDPZG6RHA3FQDRK11:QRQ11:D7KQRD=D;C;8IP]n0100000020000R_P]n1011030002012010110:RaP]n1011020002012010;10:RbP]n1011040002012010110:P]n1011050002012010110:P0P9PBP2P0PSPBP7P0PTPBP8P0PUPBP1PAPBPH14KIP]n0100000020000RHP]n1011030002002010110:RcP]n1011020002002010;10:RdP]n1011040002002010110:P]n1011050002002010110:C2P6P0PSPFPCP0PSPBP2PbP]n1011040002012010110:P0PSPBP2PdP]n1011040002002010110:C2P8P0PTPFPCP0PTPBP2PaP]n1011020002012010;10:P0PTPBP2PcP]n1011020002002010;10:C2P1P0PUPFPCP0PUPBP2P_P]n1011030002012010110:P0PUPBP2PHP]n1011030002002010110:C2P2PMP7PSP;P;P`fE,1:,5:PZG6PAPAfDR`PFPAPBP2fHRH15:QRQ53`R`P;11:HRHA:H:QPFC;;8IP]n0100000020000PAPBP214`IP]n0100000020000C2P2PFPCPKPDPI%9K%WF'V,O=%UF9D;D,O>FTP[n0110000020100b0P[X3\X1UP1P2O2n10110:0102012010110:P[X2RX6TP1P2O2n10110:0102012010610:P[X4VX1SP1P2O2n10110:0102012010110:P[X5YX19P1P2O2n10110:0102012010110:W3W2X4VW;W5X:;P5P6P7P8P1P2O6n0110=010161108105109104102103P[n0110001020100b0n0110001020001b0n0110001020001b0n0110001020001b0n0110001020001b0P1P2PAPBPEP8PG1712R[PIC0RVPAPB%H7#BRYPLPAPB%E6RRP8PNP[PIC0PAPB1=P?,COROPVPAPBA<@5^R@P<PBP8P0P9PBP6P0PSPBP8P0PTPBP1P0PUPBP2PAPBPMP7PSP;P;PW11:J,5:RJPZG6RZA33WJRWP;PXA:X:JP4C;;8IP]n0100000020000P]n1011030002012010110:P]n1011020002012010;10:P]n1011040002012010110:P]n1011050002012010110:n0110700016110<10510>104102103PLn0100000020100n0100000020001n0100000020001n0100000020001n0100000020001PAPBPEP8PGP1PIC0RGPAPBPYPLPAPBPRP8PNP1PIC0PAPBPOPGPAPBP@P<PBP8P0P9PBP6P0PSPBP8P0PTPBP1P0PUPBP2PAPBPZ14WIP]n0100000020000P]n1011030002002010110:P]n1011020002002010;10:P]n1011040002002010110:P]n1011050002002010110:n0110700016110<10510>104102103PLn0100000020100n0100000020001n0100000020001n0100000020001n0100000020001C2eA3[5^P1P2P5P^CSEI%9[1^12EIP1P2P5P6P7P8P[DQP5P6P7P8P1DQC2eW=W>W9X8;X<;W7o"). Qed.

Lemma check_mprotect_X : forall addr len prot eff mo mat,
  m_vm_materialized mo = [] -> (length mat <= NMAX)%nat ->
  robust NMAX (nonlazy_bytes (mprotect_model_next mo addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))))
              (vm_limit (m_vmmaps mo)) ->
  relX mo mat (check_mprotect addr len prot eff (MX mo mat)) (check_mprotect addr len prot eff mo).
Proof.
  intros addr len prot eff mo mat CAN LEN R. unfold check_mprotect.
  unfold mprotect_refusable. rewrite !(mprotect_budget_ok_X NMAX) by assumption.
  rewrite !m_vmmaps_MX, !mprotect_model_next_MX.
  xfer.
Qed.

Lemma check_brk_X : forall req eff mo mat,
  m_vm_materialized mo = [] -> (length mat <= NMAX)%nat ->
  robust NMAX (nonlazy_bytes mo + bv_unsigned (bv_sub req (vm_brk (m_vmmaps mo)))) (vm_limit (m_vmmaps mo)) ->
  relX mo mat (check_brk req eff (MX mo mat)) (check_brk req eff mo).
Proof.
ltac2:(KReplay.run1 (kr_t_MmXfer ()) ["Transfer"] "p'0h02E1h12E2h21mi001mh31bi011bh42cih52csh61pi021ph72wsh83CANh93LENh:1Rh;1ah<3effi033effh=3math>2moh?1ri041rh@3reqhA2usi052ushB1vhC2zsi062zsi07:eff_copiesi08;eff_copyinsi097eff_reti0::eff_unmapsi0;:eff_writesi0<9eff_zerosi0=1li0>2m0i0?1sp;1p;3p;2p;4p;6p;7p;8g00DLj1CTg00V9j1QTg00VWj1MTg004kR0j1ATg00[`j13Tg005ej1OTg005Kj3?Tg009=j2VTg009]j2TTg01ZSj1STg00Yoj16Tg01ICj1@Tg02>@j3RTg013Sj2bTg00ADj2_Tg01b8j1\Tg01K7j3YTg02dhj1=Tg02e^j4WTg00]:j21Tg01HAj30Tg004Pj32Tg00R3R1j2UTg00iVj2HTg02=Cj3:Tg01J8j25Tg02F=j27Tg00XDj44Tg00k[j6JTg00W:j2FTg01Ahj1KTg01D?j3ITg00Zfj2BTg01@cj2LTg00Y9j1ETg006Ej2`Tg02f_j2^Tg003Pj6GTg02KGj7]Tg01GEj2[Tg02gfj8ZTg02haj3NTg02ifj3XTg007_j2PTf1R2f0R3#6#@'5#Kp=<g00_AR4??23p=>%63#@p=Df3R5f2R6?X23'7p=91P62/P3p=8A0562/F3p=;%@3,52p=ag00OE#C#C#CR7#C#C#C#QR8#MR9g00lYR:%A9R;%32%O95?;1V92p,4NMAXR<'T%S5f5R=%65R>#@5R8,b8'_%\>5Y<f4R>P5f6R8%==R?CW11>5R@?08?A0>8?RA1<?>R?=295'1'>%3A%3>929?5?;'UP111=>f7R1%=8R?30A0=1?RA1<?=R?=29>'1'>%3A%3=929?5?;P8P=P:g00`7R?P1P0%Q7#M#A,H9R7P?P>P0g00mWRAP?P2P0g00I3,H9RBP?P3g008=RCP?f<RDf;RE'1RFf>RG;:=P5PGP=%DFRHC915=H,7638PFPGP=g00aA#ORFC;g00b7RHn0100000020000PHn1011080002002010210=PHn1011070002002010>10=PHn10110;0002002010210=n0110300016010410;106105107108P:P?P1P0P7P?P>P0PAP?P2P0PBP?P3PCP?A:DG=P5PGP=%DDRIC915=I,7638PDPGP=PFC;PHn0100000020000PHn1011080002002010210=PHn1011070002002010>10=PHn10110;0002002010210=n0110300016010410;106105107108C4P31118f9RGf8RI#=RJ30A01GJ1<J1=298'1'>f:RJ%=GRK50I#31<KI%3I5295?;P:11JG%=3RK70DA0JDK1<KJ=29G'1'>f=%=2RK50E#31<KE%3E5295?;PDPEP:P?P6P0P7P?P>P0PAP?P2P0PBP?P3PCP?fBREfA'1RDfDRK;:=P5PKP=%DDRLC915=L,7638PDPKP=PFC;PHn0100000020000PHn1011080002002010210=PHn1011070002002010>10=PHn10110;0002002010210=n0110300016010410;106105107108P:P?P6P0P7P?P>P0PAP?P2P0PBP?P3PCP?A:EK=P5PKP=%DER:C915=:,7638PEPKP=PFC;PHn0100000020000PHn1011080002002010210=PHn1011070002002010>10=PHn10110;0002002010210=n0110300016010410;106105107108C4]1]0PJ%A7RJ1H99#ARE%AAR:%ABRDfERL/1KfGRMP=P>P5P6P2P3EJ#=RN30A0LMN1<NL=29K'1'>fFRNfHROP8P=P>P5P6P2EJ#=RP30#31<PN%3N5295?;P0P7POPMP0P7P?P3P0PAP?P>P0PBP?P5PCP?11OMR;fJRP;:IP8PPPI%D;RQC9RR15IQ,7=RQ38A0;PIR;/FFRSPHn0100000020000RTPHn1011080002002010210=RUPHn1011070002002010>10=PHn10110;0002002010210=P0P7P?P3P0PAP?P>P0PBP?P5PCP?A:OPIRVP8PPPI%6ORW#@RXC915IXRX,7=38A0OPIRY/FFPHn0100000020000RZPHn1011080002002010210=R[PHn1011070002002010>10=PHn10110;0002002010210=C4P8P0PAPOPMP0PAP?P3PUPHn1011070002002010>10=P0PAP?P3P[PHn1011070002002010>10=C4P5P0PBPOPMP0PBP?P3PTPHn1011080002002010210=P0PBP?P3PZPHn1011080002002010210=C4P6PCfIR0=:M1RTPOPMPCP?A83RQPSPHn0100000020000PZC4X3Cg011TRQ%6MRRPOPMPCP?P8PPPI%@3R[C915I[,7=58VPSPHn0100000020000PZC4XBQP=P0P1%@RRRC9151R,7>58TRTPCPCP0POPCP?P3110OfKRRPGPFC;PHn0100000020000PCP?P3P0PRPGPFC;RQPHn0100000020000C4P3P4%KXRZ=29M,1YP0PO1F3FPQC4X24POPMPYPZPFP4AIWPI/BORW,LXRP#6RI%EW'B%60RZ,aGAIZRG/B0'L#6%E0'B,>3X24%EORO,BI,`4%EP1^XWEG%EY%6Y/BO'>eP2F]P;P6EGg00e@R;n0110100020000b3PMPNPCP?PT11MNROP0P1PFC;PHn0100000020000PCP?PTPMP0P1PFC;PHn0100000020000C4e%6O1[MNEGA:O01P<PMPNP0P1PLPKfCGZEGP;X4DX6BP2P3O2n10110=0002012010210=P;X5:X2AP2P3O2n10110=0002012010010=P;X7JX67P2P3O2n10110=0002012010210=W1W0W4W5XAEWCW7X?9P=P>P5P6P2P3O6n0110?01016110910;10<10:107108P2P3O2W1W0P2P3O2n2001000000121000000b;P>P5AN8=@AN8=>C4eW:W9W8W=X>4W<W@o"). Qed.

Lemma check_mmap_X : forall addr len prot flags fd off eff mo mat,
  m_vm_materialized mo = [] -> (length mat <= NMAX)%nat ->
  let nZ := page_round_up_Z (bv_unsigned len) in
  (mmap_noreserve_b flags = true \/ robust NMAX (nonlazy_bytes mo + nZ) (vm_limit (m_vmmaps mo))) ->
  robust NMAX (nonlazy_bytes (with_mmap_replacement flags addr (Z_to_bv 64 nZ)
                                 (with_vmmaps (mmap_fixed_rw_next (m_vmmaps mo) addr (Z_to_bv 64 nZ)) mo)))
              (vm_limit (m_vmmaps mo)) ->
  (* [comment removed for export] *)
  robust NMAX (nonlazy_bytes (with_mmap_replacement flags addr (Z_to_bv 64 nZ)
                                 (with_vmmaps (mmap_fixed_rw_span_next (m_vmmaps mo) addr (Z_to_bv 64 nZ)) mo)))
              (vm_limit (m_vmmaps mo)) ->
  relX mo mat (check_mmap addr len prot flags fd off eff (MX mo mat)) (check_mmap addr len prot flags fd off eff mo).
Proof.
  intros addr len prot flags fd off eff mo mat CAN LEN nZ R1 R2 R3. unfold check_mmap.
  unfold mmap_grant_refusable, mmap_reserve_refusable, mmap_fixed_fresh_refusable, mmap_fixed_commit_refusable,
         mmap_fixed_span_refusable.
  rewrite !(noreserve_backed_ok_X NMAX) by assumption.
  rewrite !(fixed_rw_budget_ok_X NMAX) by assumption.
  rewrite !(fixed_rw_span_budget_ok_X NMAX) by assumption.
  rewrite !m_vmmaps_MX, !with_vmmaps_MX, !with_mmap_backing_MX, !with_mmap_destroyed_MX, !with_mmap_replacement_MX.
  xfer.
Qed.

End Transfer.
