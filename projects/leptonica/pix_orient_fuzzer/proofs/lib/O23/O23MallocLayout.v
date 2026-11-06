(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec Hoare AgentLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import MallocLayout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_O23MallocLayout () := "C47Corelib7Classes?RelationClasses9ReflexiveI47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init5Logic2eq01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00c69OSSVerify5KrLib3O23?O23MallocLayout6ImgS16aSrc_leptonica_pix_orient_fuzzer_repro_segment_000C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3O23?O23MallocLayout6ImgS16aSrc_leptonica_pix_orient_fuzzer_repro_segment_001C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3O23?O23MallocLayout6ImgS16aSrc_leptonica_pix_orient_fuzzer_repro_segment_002C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3O23?O23MallocLayout6ImgS16aSrc_leptonica_pix_orient_fuzzer_repro_segment_003C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_sizeC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive01I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01I47Corelib4Init5Logic2eq00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentK47Corelib4Init9Datatypes6option02C69OSSVerify5KrLib6Common8Mallocng<MallocLayout:seg_missesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat3N2Z9is_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C69OSSVerify5KrLib6Common8Mallocng<MallocLayoutAfind_segment_noneC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout7ml_segsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205c59OSSVerify5KrLib3O23?O23MallocLayout9s16_basesC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib3O23?O23MallocLayout4LS16C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23MallocLayout8s16_segsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K46Stdlib9micromega6VarMap1t01C69OSSVerify5KrLib6Common8Mallocng<MallocLayout@find_segment_hitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23MallocLayout<chk_seg_byteC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout9chk_rangeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02C69OSSVerify5KrLib6Common8Mallocng<MallocLayout6A_LOCKC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib6Common8Mallocng<MallocLayout8chk_listC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23MallocLayout<chk_rom_zeroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout>A_SIZE_CLASSESC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3divC46Stdlib5Lists4List8flat_mapC69OSSVerify5KrLib6Common8Mallocng<MallocLayout=chk_rom_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout:A_DEBRUIJNC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout?A_SMALL_CNT_TABC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout=A_MED_CNT_TABC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout9A_GOT_SSPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout5A_SSPC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3powC47Corelib5Lists7ListDef3mapC69OSSVerify5KrLib6Common8Mallocng<MallocLayout@size_classes_tabC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout>debruijn32_tabC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout=small_cnt_tabC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout;med_cnt_tabC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC47Corelib4Init9Datatypes8list_indC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC46Stdlib5Lists4List7forallbC46Stdlib5Lists4List2InC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC46Stdlib5Lists4List=Forall_forallC47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6ltb_ltI46Stdlib5Lists4List6Exists00C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr07C69OSSVerify5KrLib6Common8Mallocng<MallocLayout6IMG_LOC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout5RW_LOC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout6IMG_HIC1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00c59OSSVerify5KrLib3O23?O23MallocLayout=s16_find_noneC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayoutDseg_rom_none_of_findC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayoutBwview_of_find_noneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;lt_ge_casesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewc59OSSVerify5KrLib3O23?O23MallocLayout=s16_find_seg0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout@wview_of_find_roC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23MallocLayout=s16_find_seg1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23MallocLayout=s16_find_seg2C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib6Common8Mallocng<MallocLayout?chk_range_soundC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic5proj1C69OSSVerify5KrLib6Common8Mallocng<MallocLayout@wview_of_find_rwC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23MallocLayout=s16_find_seg3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayoutDseg_rom_some_of_findC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes4prod01C47Corelib4Init5Logic7f_equalC59OSSVerify5KrLib6Common8AgentLib7u64_litC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2or01C47Corelib4Init5Logic7and_indK47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or02C4ELinuxProcessSemantics?LinuxProcessSem5State<reserved_topC69OSSVerify5KrLib6Common8Mallocng<MallocLayout5A_CTXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout6A_LIBCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout4A_TPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout7A_ERRNOC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayoutAA_MALLOC_REPLACEDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23MallocLayoutAForall_map_mod256C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C69OSSVerify5KrLib6Common8Mallocng<MallocLayoutCchk_rom_bytes_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout>chk_list_soundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC56Stdlib6ZArith6BinInt1Z6eqb_eqC35stdpp7tactics<f_equal_helpc59OSSVerify5KrLib3O23?O23MallocLayoutCForall_lt256_of_chkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout9PC_MALLOCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout7PC_FREEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout9PC_CALLOCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout<PC_LIBC_FREEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout>PC_MALLOC_IMPLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout;PC_GET_METAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout9PC_NTFREEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout=PC_ALLOC_METAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout=PC_ALLOC_SLOTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout:PC_ENFRAMEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout;PC_ALLZEROPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout7PC_MMAPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout;PC_MPROTECTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout9PC_MUNMAPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout:PC_VM_WAITC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout>PC_SYSCALL_RETC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout<PC_ERRNO_LOCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout7PC_LOCKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout9PC_UNLOCKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout9PC_MEMCPYC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout9PC_MEMSETC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common8Mallocng<MallocLayout>MallocLayoutOk01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z4to_NC46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes4bool02K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00c59OSSVerify5KrLib3O23?O23MallocLayout>s16_seg2_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23MallocLayout>s16_seg3_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23MallocLayout>s16_seg0_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23MallocLayout>s16_seg1_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout8CTX_SIZEC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23MallocLayout:s16_tablesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23MallocLayout<s16_ctx_zeroC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03".
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Module ImgS16 := Plain.

(* [comment removed for export] *)
Instance LS16 : MallocLayout := {|
  ml_segs := ImgS16.M.loaded_segments;
  IMG_LO := 0x10000; RW_LO := 0x10f000; IMG_HI := 0x145000;

  A_LOCK           := Z_to_bv 64 0x144020;
  A_CTX            := Z_to_bv 64 0x144028;
  A_INIT_DONE      := Z_to_bv 64 0x144030;
  A_MMAP_CTR       := Z_to_bv 64 0x144034;
  A_FREE_META_HEAD := Z_to_bv 64 0x144038;
  A_AVAIL_META     := Z_to_bv 64 0x144040;
  A_AVAIL_META_CNT := Z_to_bv 64 0x144048;
  A_AVAIL_AREA_CNT := Z_to_bv 64 0x144050;
  A_META_SHIFT     := Z_to_bv 64 0x144058;
  A_AREA_HEAD      := Z_to_bv 64 0x144060;
  A_AREA_TAIL      := Z_to_bv 64 0x144068;
  A_AVAIL_AREAS    := Z_to_bv 64 0x144070;
  Z_UNMAP_SEQ      := 0x144378;
  Z_BOUNCES        := 0x144398;
  A_SEQ            := Z_to_bv 64 0x1443b8;
  A_BRK            := Z_to_bv 64 0x1443c0;
  A_MALLOC_REPLACED := Z_to_bv 64 0x1443c8;

  A_LIBC       := Z_to_bv 64 0x143fb0;
  A_NEED_LOCKS := Z_to_bv 64 0x143fb3;
  A_PAGE_SIZE  := Z_to_bv 64 0x143fe0;
  A_TP         := Z_to_bv 64 0x123d20;
  A_ERRNO      := Z_to_bv 64 0x123c7c;
  A_GOT_SSP    := Z_to_bv 64 0x112758;
  A_SSP        := Z_to_bv 64 0x143f90;

  A_SIZE_CLASSES  := Z_to_bv 64 0x4ddb0;
  A_SMALL_CNT_TAB := Z_to_bv 64 0x4de10;
  A_MED_CNT_TAB   := Z_to_bv 64 0x1f15c;
  A_DEBRUIJN      := Z_to_bv 64 0x1f5c8;

  PC_MALLOC      := (0xfa4b4%bv : word);
  PC_FREE        := (0xfa374%bv : word);
  PC_CALLOC      := (0xfa23c%bv : word);
  PC_LIBC_FREE   := (0xfa4b8%bv : word);
  PC_MALLOC_IMPL := (0xfae44%bv : word);
  PC_GET_META    := (0xfa684%bv : word);
  PC_NTFREE      := (0xfa794%bv : word);
  PC_ALLOC_META  := (0xfab6c%bv : word);
  PC_ALLOC_SLOT  := (0xfb1b4%bv : word);
  PC_ENFRAME     := (0xfba58%bv : word);
  PC_ALLZEROP    := (0xfbba8%bv : word);
  PC_MMAP        := (0xfd6a0%bv : word);
  PC_MPROTECT    := (0xfd78c%bv : word);
  PC_MUNMAP      := (0xfd8a8%bv : word);
  PC_VM_WAIT     := (0xfd69c%bv : word);
  PC_SYSCALL_RET := (0xfa1fc%bv : word);
  PC_ERRNO_LOC   := (0xf9d30%bv : word);
  PC_LOCK        := (0x10a834%bv : word);
  PC_UNLOCK      := (0x10aabc%bv : word);
  PC_MEMCPY      := (0x109cb0%bv : word);
  PC_MEMSET      := (0x10a230%bv : word)
|}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Abbreviation SEG0 := ImgS16.Plain_segment_000.
Local Abbreviation SEG1 := ImgS16.Plain_segment_001.
Local Abbreviation SEG2 := ImgS16.Plain_segment_002.
Local Abbreviation SEG3 := ImgS16.Plain_segment_003.
(* [comment removed for export] *)
Local Abbreviation B0 := 0x10000.  Local Abbreviation B1 := 0x62000.  Local Abbreviation B2 := 0x10f000.
Local Abbreviation B3 := 0x113000.  Local Abbreviation B4 := 0x145000.
Local Abbreviation P0 := 82%nat.  Local Abbreviation P1 := 173%nat.  Local Abbreviation P2 := 4%nat.  Local Abbreviation P3 := 50%nat.

Lemma s16_segs : ml_segs = [SEG0; SEG1; SEG2; SEG3].
Proof.
ltac2:(KReplay.run1 (kr_t_O23MallocLayout ()) [] "p;1p;3p;2p-1p10000p4p710p9g000\j13Tg001<j12Tg001\j30Tg002<j21Tg002VR0#3g003Ug005Fg0077g008h%20500500500500'1o"). Qed.

Lemma s16_bases :
  Z.of_N (seg_base SEG0) = B0 /\ Z.of_N (seg_base SEG0) + Z.of_N (seg_size SEG0) = B1 /\
  Z.of_N (seg_base SEG1) = B1 /\ Z.of_N (seg_base SEG1) + Z.of_N (seg_size SEG1) = B2 /\
  Z.of_N (seg_base SEG2) = B2 /\ Z.of_N (seg_base SEG2) + Z.of_N (seg_size SEG2) = B3 /\
  Z.of_N (seg_base SEG3) = B3 /\ Z.of_N (seg_base SEG3) + Z.of_N (seg_size SEG3) = B4.
Proof.
ltac2:(KReplay.run1 (kr_t_O23MallocLayout ()) [] "p;1p;2p;4p;3g00:Yj1>Tg00;Wj13Tg00<5j10Tg00<Zj16Tg00=8j1=Tg00>6j2<Tg00>Sj11Tg00?8j25Tg002<j29Tg00?Sj44Tg00?nj3?Tf0R0#0#0p=;%00#0#0#0p=8%00#0#0#0#0#0#0#0p=7g00@HR1f1;?0p=2%10#0p=:g003UR0#>#3R2g00@fR3#0#;R4#0R5#8#7#6R6'2%=0#3,<2%:3#;#:#8#7#6R2'2R0g005FR7#>#3R8/22R9%=7#3,<8%15#1#1#1#8#7#6R5'2R8g0077R7#>#3R:/25R;%=7#3,<:%14#;#1#1#8#7#6R4'2R:g008hR7#>#3R</24R=%=7#3,<<%03#:#;#:#1#8#7#6R3'2R<'5R7'5R>'5R?'5R@'5RA'51916P0PA1912R2P9P@P2P8P?1915R5P;P>P5P:P71914R4P=P<P41913C4C4C4C4C4C4C4o"). Qed.

(* [comment removed for export] *)
Lemma s16_find_none : forall a, (a < B0 \/ B4 <= a) -> find_segment ml_segs a 1 = None.
Proof.
ltac2:(KReplay.run1 (kr_t_O23MallocLayout ()) [] "h04__p1h14__x1h24__x2h34__x3h44__p2h54__p3h67__arithh74__ffh84__p4h94__p5h:8__varmaph;5__with<4cstrh=5cstr0h>5cstr1h?5cstr2h@5cstr3hA5cstr4hB5cstr5hC5cstr6hD4__p6hE1BhF2HahG1ahH1lp;1p;2p;3p;4p;6p;7p;8g00<5j10Tg00<Zj1>Tg00AKj2ETg00>Sj11Tg00Agj2PTg00BCj2OTg000\j1WTg001<j1VTg001\j3<Tg00B]j1\Tg00C?j3rTg00DCj1ZTg00?nj3DTg00:Yj1GTg00;Wj18Tg00=8j1LTg00>6j2:Tg00Dej2cj3JTg00F1j15Tg00FTj1bTg00G2j2aTg00GSj1HTg00H2j2BTg00H[j3`Tg00IDj3FTg00Imj2UTg00JYj2TTg00K7j4_Tg00KUj1^Tg00L3j1]Tg00L^j2MTg00MAj3[Tg00Mdj4NTg00NOj2qTg002<j2pTg00O1j2oTg00O]j3nTg00P<j4lTg00Pnj2iTg00QOj6ITg00R0j4hTg00SCj1gTg00TLj6fTg00?8j2QTg00Tjj2eTg00UMj7XTg00V1j6jTg00VUj7RTg00W9j7dTg00W]j8mTf0R0#0#0p=C%00#0#0#0p=?%00#0#0#0#0#0#0#0p=Ag00@HR1f1R2;D0p=4f2R3=D12/Q0p=91Q20,Q3p=3g00XAR4/P0p=61e10p=;P3g00X_R5g00Y>R6P6g00Y^R7P1P2g00Z>P0CNg00ZeR8FXp=7P2P5P6P6P7P0Ejp==f4R9P5P6P6P7f3R:P3P5P6P6P7P2P0FRFRp=2P1P2g00[EP0CNp=SP2P5P6P6P7P0P8FXp=KP3P5P6P6P7P2P0Fdp=YP:P5P6P6P7P3P2P0Gmp=@P3P5P6P6P7P2P0FRp=kg00@fR5#0R8#CR;#0R<#?#A#>R=,E0%05#1#0#C#1#0#1#?#A#>R>/P0'Og002VR?#WR@g003URAg005FRBg0077RCg008hRD%V?RE5<?RF5<?RG5<?RH5<?RI%\?%>5RJ9r03%Z?3DXH@PIP2PJg00[l%GARI#8R@/4=RK%LARL#8RM,:@%15RN#0#C#1#0#?#A#>RO'4RP%GBRQ#8RR/4ORS%LBRT#8RU,:R%1<#1#1#1#?#A#>R<'4RV%GCRW#8RX/4<RY%LCRZ#8R[,:X%1;#C#1#1#?#A#>R;'4R\%GDR]#8R^%LDR_#8R`,:^/4>79;Ra33Rb33Rc33P?1c3JRdPAPH%5TRT%6URH%5ZRZ%6[Re%5_R_%6`Rf%5IRI%6@Rg%5QRQ%6RRh%5WRW%6XRi%5]R]%6^Rj%5LRL%6MRkp-0Rlg00\nRm%b5,a1g00]ZRn#HRo#HRp#HRq#H,B15`11B1pRp1B1o5F15F1g00^9Ro'U1B1q1B1n9F1p5F1/Uo%Vm5<m3<Ro%WmRmP11T13P21T1:C_Rp%^1Rn%]1RqPq1M18R8%;=Rr57qPq1M1N9[18RN%;ORs57qf5Rt,=qRuD2%Z6R6Pq1M15R5/Sr,KqP1%;>Rrg00^eP5CN,Kq5YqP61S58,Kq%;J9[15,SN,Kq5YqC@R5C@1qq7R7P0P3g00_LRvg00_lRw'p1o03=DvwdAn142ClR4b7b:b;X11X21X31W01:23Rw?9O:992=1E2=1P>2'O1E3:1::91:3J'E'O[R=[^11^21^31^0lP0PcPMP@f;R@f9RMf:RcO6b6bCbBbAb@b?b>b=b<AJ3JAeP?PdPBPGPTPHPZPeP_PfPIPgPQPhPWPiP]PjPLPkPoPmPpPnPqPqPuPqf6RG,=qRAPqA7q8sPq%;<Rs97qNf7Rv,=qRxD2D2P6P5C@P7P4b7b:b;X11X21X31X0lX4lX5lA9w<t992O93:9P=[^11^21^31^0l^4l^5lP0PbPPPKPUPRP@PMPcO8b6bCbBbAb@b?b>b=b<AJ3JBeP?PdPCPFPTPHPZPeP_PfPIPgPQPhPWPiP]PjPLPkPoPmPpPnPqPqPuPqPAPqPxPqf8RF,=qRBPqA7q8sPq%;;Rs97qN1=qMRRD2D2D2P6P5C@P7P4b7b:b;X11X21X31X0lX4lX5lX8lX9lA9w;v992<93tG93:9P=[^11^21^31^0l^4l^5l^8l^9lP0PaPVPSPPPKP[PXP@PMPcO:b6bCbBbAb@b?b>b=b<AJ3JCeP?PdPDPEPTPHPZPeP_PfPIPgPQPhPWPiP]PjPLPkPoPmPpPnPqPqPuPqPAPqPxPqPBPqPRPq1=qcA7q8sA7qNr5kqD2D2D2P6P5C@P7P4b7b:b;X11X21X31X0lX4lX5lX8lX9lXDl14w>992;93vF93tG93:9P=[^11^21^31^0l^4l^5l^8l^9l^DlP0P\PYPVPSPPPKP`P^P@PMPcO;b6bCbBbAb@b?b>b=b<AJ3JDe1i?dEIEIEIEIbEChg00`L#gg00aIEfWFXG1o"). Qed.

Lemma s16_find_seg0 : forall a, B0 <= a -> a + 1 <= B1 -> find_segment ml_segs a 1 = Some SEG0.
Proof.
ltac2:(KReplay.run1 (kr_t_O23MallocLayout ()) [] "h04__p1h14__x1h24__x2h37__arithh44__ffh54__p2h68__varmaph75__with84__x3h94cstrh:5cstr0h;5cstr1h<5cstr2h=5cstr3h>5cstr4h?5cstr5h@5cstr6hA1BhB2H1hC2H2hD1ahE1lp;1p;2p;3p;4p;8p;6p;7g00<5j10Tg00<Zj19Tg00Agj28Tg00>6j26Tg00>Sj11Tg000\j1PTg001<j1LTg001\j3:Tg00B]j1TTg00C?j3STg00bJj2jTg00?nj3ATg00:Yj1?Tg00;Wj14Tg00=8j1>Tg00?8j2HTg00Dej2YTg00Pnj2XTg00F1j15Tg00GSj1OTg00H2j2GTg00IDj3FTg00Imj2NTg00JYj2MTg00blj1WTg00K7j4KTg00KUj1VTg00L3j1UTg00L^j2CTg00Tjj2JTg00Mdj4ETg00DCj1iTg00NOj2hTg002<j2gTg00O1j2fTg00O]j3cTg00P<j4bTg00FTj1_Tg00G2j2^Tg00H[j3]Tg00MAj3QTg00cJj8\Tg00SCj1`Tg00TLj6aTg00UMj7[Tg00V1j6dTg00VUj7eTg00W]j8ZTf0R0#0#0p=B%00#0#0#0p=<%00#0#0#0#0#0#0#0p=;g00@HR1f1R2;A0p=Rf2R3=A12/H0p=2g00XAR4/80p=3P2g00X_R5g00Y>R6P6g00Y^R7P0g00ZeF[p=7P2P5P6P6P7P0Edp=IP3P5P6P6P7P2P0Fep=DP1P2g00^eP0CEp==f3R8P5P6P6P7P3P2P0GZp=@g00@fR5#0R9#BR:#0R;#<#;#9R</80%95R=,62%15R>#0#B#1#0#<#;#9R?'8R@g002VRA#PRBg003URCg005FRDg0077REg008hRF%LARG5:A5:A5:ARH5:A%TAAS08=1jAC3AXEBg00[l%?CRB#4RI/R<RJ%>CRK#4RL,6I%?DRM#4RN%>DRD#4RO,6N%1;#1#1#1#<#;#9R;%?ERP#4RQ%>ERE#4RR,6Q%1:#B#1#1#<#;#9R:%?FRS#4RT%>FRF#4RU,6T%05#1#0#B#1#0#1#<#;#9'R72:3272;3272?R;72?R:'HPGPCPHP8P=1Y8=,XA%5DRD%3ORO%5ERE%3RRR%5FRF%3URU%5BRB%3IRA%5MRM%3NRN%5PRP%3QRQ%5SRS%3TRT%5KRK%3LRHp-0RCg00\nRGg00]ZRV#ORW#O,G1RX1G1W1G1V5F1RV5F1g00^9RW'N%LGRY3:%PGRZP11M13R[P2%W1CK%V1R\%U1R]P11C15R^g00Z>R_1J1<R`CE,7]f4Ra,I]5D]%i6R6P]1C19R9,=`,7]P61=^9,7]C@C@1h]7R7P0P3g00_LR`g00_lRb'g1f03=A`bdAc142CbR4b4b6b7X11X21W0A20<318<31838[[^11^21^0CP0P:f<R:PIf9R<f;O5b3b@b?b>b=b<b;b:b9PDPOPEPRPFPUPBPAPMPNPPPQPSPTPKPH%_5,^1=]1X=F1V/NW=:GYPZP1P[P21M18CKP\P]f5,I]P11C1>9Q19R9P_1J1?R_CE,7]f6,I]5D]5D]P6P]1J1=9Q1^R^/=_,7]P61=^9,7]C@C@P7P4b4b6b7X11X21X81X0CX5C1623?2?a,H8163=168a'8\@[^11^21^81^0C^5CP0P;PJPLPIP:P<f:O7b3b@b?b>b=b<b;b:b9G\bAg00`L#`g00aIEaWCWBXD1o"). Qed.
Lemma s16_find_seg1 : forall a, B1 <= a -> a + 1 <= B2 -> find_segment ml_segs a 1 = Some SEG1.
Proof.
ltac2:(KReplay.run1 (kr_t_O23MallocLayout ()) [] "h04__p1h14__p2h24__p3h34__x1h44__x2h54__x3h67__arithh74__ffh88__varmaph95__with:4cstrh;5cstr0h<5cstr1h=5cstr2h>5cstr3h?5cstr4h@5cstr5hA5cstr6hB4__p4hC1BhD2H1hE2H2hF1ahG1lp;1p;2p;3p;4p;7p;6p;8g00>Sj11Tg00<5j10Tg00<Zj1;Tg00Agj2:Tg00>6j28Tg000\j1RTg001<j1NTg001\j39Tg00B]j1WTg00C?j3VTg00bJj2pTg00?nj3KTg00:Yj1ETg00;Wj16Tg00=8j1DTg00?8j2>Tg00Dej2Zj3`Tg00F1j17Tg00GSj1STg00H2j2JTg00IDj3ITg00Imj2QTg00JYj2PTg00K7j4OTg00KUj1YTg00L3j1XTg00L^j2GTg00MAj3MTg00Tjj2FTg00DCj1UTg00Mdj4LTg00W9j7oTg00NOj2nTg002<j2mTg00O1j2iTg00O]j3hTg00P<j4fTg00AKj2TTg00BCj2aTg00Pnj2_Tg00QOj6bTg00blj1cTg00FTj1^Tg00G2j2dTg00H[j3eTg00cJj8]Tg00SCj1\Tg00TLj6gTg00V1j6[Tg00UMj7jTg00VUj7kTg00W]j8lTf0R0#0#0p=C%00#0#0#0p=?%00#0#0#0#0#0#0#0p=@g00@HR1f1R2;K0p=2f2R31>20'>p=<g00XAR4/:0p=5P2g00X_R5g00Y>R6P6g00Y^R7P0E[p=AP1P2g00Z>P0CLp=HP2P5P6P6P7P0g00ZeFjp=3P3P5P6P6P7P2P0Fkp=4P1P2g00^eP0CLp=Bf3R8P5P6P6P7P3P2P0Glp==g00@fR9#1R:#0#C#1#0#?#@#;R;/:0%;9R<,82%09R=#CR>#0R?#1#1#1#1#?#@#;R@':RAg002VRB#RRCg003URDg005FREg0077RFg008hRG%NBRH59B59BRI59B59B%WBAV08<1pBE3KXGCg00[l%EDRC#6RJ%??#@#;'2R?%DDRK#6RL,8J/2;RM%EERN#6RO/2;RP%DERQ#6RR,8O/2@%EFRS#6RT/2@%DFRF#6RU,8T%1>#C#1#1#?#@#;R>'2%EGRV#6RW/2>%DGRG#6R>,8W%09#1#0#C#1#0#1#?#@#;'2'>3<RX'>RY'>RZ3<A9BDHPEPIP8P<PB1Z8<RIPDPH%7QRQ%5RRH%7FRF%5URU%7GRG%5>R>%7CRC%5JRE%7NRN%5OR[%7SRS%5TRT%7VRV%5WRW%7KRK%5LR\p-0R]g00\nR^g00]ZR_#SR`#S,J1Ra1J1`1J1_5I1R_5I1g00^9R`'Q%N^Rb39Rc%R^RdP11P13ReP21P18CORf%Y1Rg%X1Rhf5Ri,AhRj1G1=R=1G1:5M1R:1F1;Rk'H,3hf6Rl,AhRm54h54h%U6RnPh1G19Ro,Bk,3hPnPhP5P6P6P7f7R6,AhR5P1P:g00[E1F1<9M1oRpCL,3hFoC=C=1nh7R7P0P3g00_LRqg00_lRr'm1i03=KqrdAh142CfR4b7b8b9X31X41X51X0]X1]W21823Rr/2;f4Rq5<81:;2188qRs183<Rt'T,a6[[^31^41^51^0]^1]^2]P0f<R6/TJPZP?PLPJP6f9RJf;RLO8b6bAb@b?b>b=b<b;b:A`8<De1_BIEbPQPHPFPUPGP>PCPEPNP[PSPTPVPWPKP\PcPdP1PeP2%c1COPgPh1Ahq1Hok,3h=4hm94hj54hPnPh1Bk=,3hPn1Bo=,3hC=C=P7P4b7b8b9X31X41X0]X1]X2]120;/>q9<381:;31:38[[^31^41^0]^1]^2]P0PYPMP?P6POPJPLO7b6bAb@b?b>b=b<b;b:PQPHPFPUPGP>PCPEPNP[PSPTPVPWPKP\%^9,d1=e1a=I1_/Q`=9^bPdPfPgPh1F1@Rg,H:,3hf8,Ah54h94h594hm94hjPnPh1Bpg,3hPn1Bp:,3hC=C=P7P4b7b8b9X31X41X51X0]X1]X2]XB]12r@=<il9<8q1:ts\A[^31^41^51^0]^1]^2]^B]P0PXPPPMP?PRPOP6PJf:O9b6bAb@b?b>b=b<b;b:G]bCg00`L#\g00aIEgWEWDXF1o"). Qed.
Lemma s16_find_seg2 : forall a, B2 <= a -> a + 1 <= B3 -> find_segment ml_segs a 1 = Some SEG2.
Proof.
ltac2:(KReplay.run1 (kr_t_O23MallocLayout ()) [] "h04__p1h14__p2h24__p3h34__x1h44__x2h54__p4h64__p5h74__x3h87__arithh94__ffh:8__varmaph;5__with<4cstrh=5cstr0h>5cstr1h?5cstr2h@5cstr3hA5cstr4hB5cstr5hC5cstr6hD4__p6hE1BhF2H1hG2H2hH1ahI1lp%0p;1p;2p;3p;4p;6p;8p;7g00<5j10Tg00>Sj11Tg00<Zj1>Tg00Agj2=Tg00>6j25Tg000\j1TTg001<j1PTg001\j3;Tg00B]j1\Tg00C?j3[Tg00bJj2rTg00?nj3MTg00:Yj1DTg00;Wj19Tg00=8j1FTg00?8j2?Tg00Dej2_j3WTg00F1j16Tg00GSj1UTg00H2j2JTg00IDj3ITg00Imj2STg00JYj2RTg00K7j4QTg00KUj1^Tg00L3j1]Tg00L^j2HTg00MAj3OTg00Tjj2GTg00DCj1ZTg00Mdj4NTg00NOj2qTg002<j2pTg00O1j2oTg00O]j3nTg00P<j4kTg00AKj2KTg00BCj2XTg00Pnj2gTg00QOj6VTg00blj1fTg00FTj1dTg00G2j2eTg00H[j3bTg00cJj8aTg00SCj1hTg00TLj6`Tg00V1j6iTg00UMj7jTg00VUj7LTg00W9j7lTg00W]j8mTf0R0#0#0p=C%00#0#0#0p=@%00#0#0#0#0#0#0#0p=Ag00@HR1f1R2;M0p=2f2R31?20'?p=3g00XAR4/=0p=:P2g00X_R5g00Y>R6P6g00Y^R7P0Eip=<P1P2g00Z>P0CNp=EP2P5P6P6P7P0g00ZeFjp=4f4R8P5P6P6P7f3R9P3P5P6P6P7P2P0FLFLp=7P1P2g00^eP0CNp=BP3P5P6P6P7P2P0Flp=YP9P5P6P6P7P3P2P0Gmp=8P3P5P6P6P7P2P0FLp=cg00@fR5#0R:#CR;#0R<#1#1#1#1#@#A#>R=/=0%>5R>,52%1;#C#1#1#@#A#>R;'=R?g002VR@#TRAg003URBg005FRCg0077RDg008hRE%P@RF5;@RG5;@5;@5;@%\@A[09>1r@D3MXIAg00[l%DBRA#9RH%@<#A#>'2R<%FBRI#9RJ,5H%15RK#0#C#1#0#@#A#>RL'2RM%DCRN#9RO/2LRP%FCRQ#9RR,5O/2=RS%DDRT#9RU/2=S00%FDRV#9RW,5U/2;%DERX#9RY/2;%FERE#9RZ,5Y%05#1#0#C#1#0#1#@#A#>'2'?S01'?R['?R\33R]33A;@CFR^9;@BPDPGP9P>P@1_9>RGPBP^%6QRQ%:RR^%6VRV%:WRD%6ERE%:ZRZ%6ARA%:HR_%6NRN%:OR`%6TRT%:URa%6XRX%:YRY%6IRI%:JRbp-0Rcg00\nRdg00]ZRe#URf#U,J1Rg1J1f1J1e5I1Re5I1g00^9Rf'S%PdRh3;Ri%TdRjP11R13RkP21R19CQRl%^1Rm%]1RnPnf5Ro,<nRpPn1H1:R:1H1K5O1RK1G1L'E,4nf6Rq,<nRrD7%Z6R6Pn1G1=Rs1H15Rt'B,4nRuP6f7Rv,<nRwP1PKg00[E1G1>9O1tRxCN,4nRy5YnC8C81qn7R7P0P3g00_LRzg00_lR{'p1o03=Mz{dAn142CkR4b9b:b;X31X41X71X0cX1cW21523R{/2L=3981==2RL1598Rz153>R|'KR},Xv[[^31^41^71^0c^1c^2cP0f<R~/KHP]P<PJPHP~f9RHf;RJO8b8bCbBbAb@b?b>b=b<AW9>BeP@PGPCPFPQP^PVPDPEPZPAP_PNP`PTPaPXPYPIPbPiPjPlPmPnPnPpPnPrPnPwPn1EKs,4nf8RF,<nRBD7D7P6PnPuP61<nHRu=YnyC8C8P7P4b9b:b;X31X41X71X0cX1cX2cX5cX6c12{==3oq93981XH}\L[^31^41^71^0c^1c^2c^5c^6cP01K~OP\PPPMP<PRPOP~PHPJO:b8bCbBbAb@b?b>b=b<AW9>Ce1g@GEVEVPQP^PVPDPEPZPAP_PNP`PTPaPXPYPIPbPiPjP1PkP2%f1CQPmPnPn1<n8PnPpPnPrPnPw1Ets,4n=cnBD7D7P6Pn1Bs:,4nP61Bt:,4nC8C8P7P4b9b:b;X31X41X0cX1cX2cX5cX6c120=/?q938o93391==31=39[[^31^41^0c^1c^2c^5c^6cP0P[PSPPPMP<P~PUPHPJO9b8bCbBbAb@b?b>b=b<PQP^PVPDPEPZPAP_PNP`PTPaPXPYPIPb%d5,e1=b1g=I1e/Sf=;dhPjPlPmPnPnPpPnPrPnPwPnPBPnPuPn1G1;Ru,EK,4nf:RB,<nD7D7D7P6Pn1Bxu,4nP61BxK,4nC8C8P7P4b9b:b;X31X41X71X0cX1cX2cX5cX6cXDc12{;=3vF93oq93981=|z\?[^31^41^71^0c^1c^2c^5c^6c^DcP0Q01Q00PSPPPMP<PWPUP~PHPBO;b8bCbBbAb@b?b>b=b<GabEg00`L#hg00aIE`WGWFXH1o"). Qed.
Lemma s16_find_seg3 : forall a, B3 <= a -> a + 1 <= B4 -> find_segment ml_segs a 1 = Some SEG3.
Proof.
ltac2:(KReplay.run1 (kr_t_O23MallocLayout ()) [] "h04__p1h14__p2h24__p3h34__x1h44__x2h54__p4h64__p5h74__x3h84__p6h94__p7h:7__arithh;4__ffh<8__varmaph=5__with>4cstrh?5cstr0h@5cstr1hA5cstr2hB5cstr3hC5cstr4hD5cstr5hE5cstr6hF1BhG2H1hH2H2hI1ahJ1lp%0p;1p;2p;3p;4p;6p;8p;7g00<5j10Tg00>Sj14Tg00<Zj1>Tg00Agj2=Tg00>6j2<Tg000\j1XTg001<j1TTg001\j37Tg00B]j1]Tg00C?j3\Tg00bJj2rTg00?nj3PTg00:Yj1ETg00;Wj1:Tg00=8j1GTg00?8j2ATg00Dej2`j3LTg00F1j19Tg00GSj1YTg00H2j2KTg00IDj3JTg00Imj2WTg00JYj2VTg00K7j4UTg00KUj1_Tg00L3j1^Tg00L^j2ITg00MAj3STg00Tjj2?Tg00DCj1[Tg00Mdj4RTg00NOj2qTg002<j2pTg00O1j2oTg00O]j3nTg00P<j4kTg00AKj2HTg00BCj2NTg00Pnj2gTg00QOj6MTg00blj1fTg00FTj1dTg00G2j2eTg00H[j3cTg00cJj8bTg00SCj1hTg00TLj6aTg00V1j6iTg00UMj7jTg00VUj7OTg00W9j7lTg00W]j8mTf0R0#0#0p=F%00#0#0#0p=@%00#0#0#0#0#0#0#0p=Bg00@HR1f1R2;P0p=2f2R31A20'Ap=1g00XAR4/=0p=8P2g00X_R5g00Y>R6P6g00Y^R7P0Eip=;P1P2g00Z>P0CRp=CP2P5P6P6P7P0g00ZeFjp=5f4R8P5P6P6P7f3R9P3P5P6P6P7P2P0FOFOp=3P1P2g00^eP0CRp=DP3P5P6P6P7P2P0Flp=QP9P5P6P6P7P3P2P0Gmp=6P3P5P6P6P7P2P0FOp=Zg00@fR5#0R:#FR;#4#F#4#4#@#B#>R</=0%>5R=,<2%05#4#0#F#4#0#4#@#B#>R>'=S00g002VR?#XR@g003URAg005FRBg0077RCg008hRD%T?RE57?57?57?57?%]?A\09=1r?D3PXJ@g00[l%EAR@#:RF%0;R;#@#B#>'2RG%GARH#:RI,<F%45RJ#0#F#4#0#@#B#>RK'2RL%EBRM#:RN/2KRO%GBRP#:RQ,<N%4;#4#4#4#@#B#>R;'2RR%ECRS#:RT/2;RU%GCRV#:RW,<T/2<S01%EDRX#:RY/2<S02%GDRZ#:R[,<Y/2>S03'AS0431S0531R\31A7?CER]97?BR^97?APDPEP9P=P?1`9=RDPAP^%9PRP%8QR^%9VRV%8WR_%9ZRZ%8[R`%9@R@%8FRa%9MRM%8NRb%9SRS%8TRc%9XRX%8YRd%9HRH%8IRep-0Rfg00\nRgg00]ZRh#YRi#Y,K1S061K1i1K1h5J1S075J1g00^9Rh'W%TgRi37Rj%XgRkP11V13S08P21V19CURl%_1Rm%^1RnPnf5Ro,;nRpPn1I1:R:1I1J5S1RJ1?1K'C,5nf6Rq,;nRrD3%[6R6Pn1?1<Rs1I15Rt'D,5nRuP6f7Rv,;nRwP1PJg00[E1?1=9S1tRxCR,5nRy5QnC6C61qn7R7P0P3g00_LRzg00_lR{'p1o03=Pz{dAn142CkR4b;b<b=X31X41X71X0fX1fW21<23R{/2K=1981=<2RK1<98Rz1<3=R|'HR},Nv[[^31^41^71^0f^1f^2fP0f<R~/HFP\PGPIPFP~f9RFf;RIO8b:bEbDbCbBbAb@b?b>AL9=AeP?PDPBP]PPP^PVP_PZP`P@PaPMPbPSPcPXPdPHPePjPkPlPmPnPnPpPnPrPnPwPn1?1;,CJ,5nf8R],;nRAD3D3P6PnPuP61;nFR\=QnyC6C6P7P4b;b<b=X31X41X71X0fX1fX2fX5fX6f12{;=1oq91981NF}\K[^31^41^71^0f^1f^2f^5f^6fP01H~NQ05POPLPGPQPNP~PFPIO:b:bEbDbCbBbAb@b?b>AL9=BeP?PDPCPEPPP^PVP_PZP`P@PaPMPbPSPcPXPdPHPePjPkPlPmPnPnPpPnPrPnPwPnPAPnP\Pn1CJs,5nf:RE,;nRBD3D3D3P6PnPuP61;nIRu=QnyC6C6P7P4b;b<b=X31X41X71X0fX1fX2fX5fX6fX8fX9f12{<=1v]91oq91981NI}\K[^31^41^71^0f^1f^2f^5f^6f^8f^9fP01H~TQ04PUPRPOPLPGPWPTP~PFPIO<b:bEbDbCbBbAb@b?b>AL9=Ce1g?DEMEMEMPPP^PVP_PZP`P@PaPMPbPSPcPXPdPHPePjPkP1Q08P2%f1CUPmPnPn1;n8PnPpPnPrPnPwPnPAPnP\1Cts,5n=ZnBD3D3D3P6Pn1Ds:,5nP61Dt:,5nC6C6P7P4b;b<b=X31X41X0fX1fX2fX5fX6fX8fX9f120</A]91qv918o91391=<31=39[[^31^41^0f^1f^2f^5f^6f^8f^9fP0Q03Q01PUPRPOPLPGP~PYPFPIO;b:bEbDbCbBbAb@b?b>PPP^PVP_PZP`P@PaPMPbPSPcPXPdPHPe%d5,e1Q065c1Q075J1/Wh=7giPkPlPmPnPnPpPnPrPnPwPnPAPnP\PnPB1?1>RB,CJ,5n9ZnuD3D3D3P6Pn1DxB,5nP61DxJ,5nC6C6P7P4b;b<b=X31X41X71X0fX1fX2fX5fX6fX8fX9f12{>,AF91v]91oq9198Q001=|z[[^31^41^71^0f^1f^2f^5f^6f^8f^9fP0Q02Q01PUPRPOPLPGP[PYP~PFPEO<b:bEbDbCbBbAb@b?b>GbbFg00`L#hg00aIEaWHWGXI1o"). Qed.

(* [comment removed for export] *)
Definition chk_seg_byte (seg : Segment) (off : Z) : bool :=
  match segment_byte_at (seg_bytes seg) (Z.to_N off) with Some _ => true | None => false end.

Lemma s16_seg0_bytes : chk_range (chk_seg_byte SEG0) 0 P0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O23MallocLayout ()) [] "p;2p;1p;3g002<j26Tg00d\j15Tg00eaj34Tg00?nj33Tg00GSj10Tf0R0#0#0p=2%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00_LR0g00_lR1'6g003U#5g00XAg00]Z#2#1#1#1#1#134=301do"). Qed.
Lemma s16_seg1_bytes : chk_range (chk_seg_byte SEG1) 0 P1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O23MallocLayout ()) [] "p;2p;1p;3g002<j27Tg00d\j16Tg00GSj10Tg00eaj34Tg00?nj33Tf0R0#0#0#0#0p=2%00#0#0#0#0#0#0#0p=5%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00_LR0g00_lR1'7g005F#6g00XAg00]Z#0#2#5#1#1#1#1#134=301do"). Qed.
Lemma s16_seg2_bytes : chk_range (chk_seg_byte SEG2) 0 P2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O23MallocLayout ()) [] "p;2p;1p;3g002<j24Tg00d\j13Tg00GSj10Tg00eaj31Tg00?nj32Tg00_LR0g00_lR1'4g0077#3g00XAg00]Z#0#0#0#031=201do"). Qed.
Lemma s16_seg3_bytes : chk_range (chk_seg_byte SEG3) 0 P3 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O23MallocLayout ()) [] "p;2p;1p;3g002<j26Tg00d\j15Tg00eaj34Tg00?nj33Tg00GSj10Tf0R0#0#0p=2%00#0#0#0p=1g00_LR0g00_lR1'6g008h#5g00XAg00]Z#2#1#1#1#134=301do"). Qed.

(* [comment removed for export] *)
Definition chk_rom_zero (a : Z) : bool :=
  match seg_rom ml_segs (Z_to_bv 64 a) with Some v => bv_unsigned v =? 0 | None => false end.
Lemma s16_ctx_zero : chk_list chk_rom_zero (bv_unsigned A_LOCK) 940 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O23MallocLayout ()) [] "p;2p;1p;3g002<j2:Tg00<5j12Tg00flj14Tg00gJj13Tg00hRj29Tg00i<j35Tg00?nj36Tg00GSj10Tf0R0#0#0#0#0p=8%00#0#0#0#0#0#0#0p=7%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g00_LR0g00_lR1':g00jFg00@f#2#2#2#2#2#2#4g00`L#3'9g00]Z#8#7#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#135=601do"). Qed.

Lemma s16_tables :
  chk_rom_bytes (seg_rom ml_segs) (bv_unsigned A_SIZE_CLASSES) (flat_map (fun c => [c mod 256; c / 256]) size_classes_tab) = true
  /\ chk_rom_bytes (seg_rom ml_segs) (bv_unsigned A_DEBRUIJN) debruijn32_tab = true
  /\ chk_rom_bytes (seg_rom ml_segs) (bv_unsigned A_SMALL_CNT_TAB) small_cnt_tab = true
  /\ chk_rom_bytes (seg_rom ml_segs) (bv_unsigned A_MED_CNT_TAB) med_cnt_tab = true
  /\ chk_rom_bytes (seg_rom ml_segs) (bv_unsigned A_GOT_SSP) (map (fun i => (bv_unsigned A_SSP / 2^(8*i)) mod 256) [0;1;2;3;4;5;6;7]) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O23MallocLayout ()) [] "h01ch11ip;3p;2p;4p;1g00?nj3<Tg00?8j23Tg002<j2?Tg00?Sj47Tg00SCj1KTg00kKj1GTg00<5j10Tg00flj1>Tg00lGj1=Tg00hRj24Tg00<Zj11Tg00mWj29Tg00n7j2:Tg001<j1JTg00nTj4ITg00o1j35Tg010@j1FTg011Lj1@Tg012]j1ATg013lj1BTg0157j1CTg016>j2DTg016[j2ETg00>Sj18Tg001\j3;Tg0178j4HTg00@HR0f1f0R13;p=2g00_LR2g00_lR37<1p=6A<233R41344R5,34R6,341?23R3P4P6P3P4P5P3P4P4P3P3C7C7C7C7g00`LR3#K#GR4g00@fR5#0R6#0R2#0R7#0#0#0R8#>R9%=3'4P0P0%08#0#1R8,911:18%J0R:'2'2X00g017TCI35#6%F3,49g018f554#6%@3,49g01:6554#6%A3,49g01;E554#6%B3,49P0P0%C3,49%16R9%17/D1'E':/98X10g00XA%15%85R5#1%12%86#1%05#1%85#1/2:'2'2'2'2,29'25;0CH554#6'3'3'3'3do"). Qed.

Lemma Forall_map_mod256 : forall (l : list Z) (f : Z -> Z),
  Forall (fun b => 0 <= b < 256) (map (fun x => f x mod 256) l).
Proof.
ltac2:(KReplay.run1 (kr_t_O23MallocLayout ()) [] "h01xh11lh23IHlh37__arithh44__ffh58__varmaph65__with71ah81bh91fp;1p;2p;3p;4p;7p;6p;5g000\j14Tg00Agj2KTg00<5j10Tg00<Zj18Tg00AKj27Tg00?8j2FTg00mWj21Tg01<Rj33Tg00Pnj2;Tg001<j15Tg00blj19Tg00KUj1:Tg00L3j1JTg00Tjj26Tg00Mdj4ITg00UMj7ETg00NOj2CTg002<j2BTg00O1j2?Tg00?nj3@Tg00O]j3ATg00P<j4>Tg01=3j3=Tg00QOj6DTg001\j3<Tg01=Zj5GTg0178j4HTg00@HR0P0f1R1f0R2CHp=2%40R3P0\0P0g00XAR4/K2g00@f#0#0#0#0#0#0#0#0#8R5,72'FX80R6f2R7P2O1/15X00/22530X131;06P1P2O1/15X00%50'29306ef3R8P2O1/15X00/229306P0P6P8P7O1R8/15f4P2O1/15X00R9/21g00\nR:#5%4:%90%:0%J0R:g00X_g00Y>R;P;g00Y^R;P01604g00[E1605CIg00ZeFE1C:;P2P7g00_LR;g00_lR:'B1?27=@;:dAA041C>b4b5b61745P2b39=85P2EDA<071,299306eW2X13X70P1DGW9W1o"). Qed.

Lemma Forall_lt256_of_chk : forall l, forallb (fun b => (0 <=? b) && (b <? 256)) l = true -> Forall (fun b => 0 <= b < 256) l.
Proof.
ltac2:(KReplay.run1 (kr_t_O23MallocLayout ()) [] "h01Hh11xh21mh31nh41lh51Ah62H1h72H2h81Ph94__x1h:1bh;2H0h<2Hxh=7__arithh>4__ffh?8__varmaph@5__withA5lemmap;1p;2p;3p;4p;7p;8g000\j19Tg01><j25Tg00<5j12Tg00<Zj1CTg01>Yj23Tg01?6j2?Tg01?Tj38Tg01@0j36Tg01@Gj2DTg01@`j3BTg01AQj3ATg01<Rj3:Tg01B4j3VTg00Agj21Tg00AKj24Tg00?8R0j27Tg01BVj3UTg01C9j2TTg01CYj2RTg001<j1QTg00JYj2JTg00KUj1GTg00L3j1FTg00L^j2ETg00Tjj2=Tg00Mdj4;Tg00DCj1HTg00VUj7ITg00NOj2KTg002<j2LTg00O1j2MTg00O]j3NTg00P<j4OTg00?nj3PTg00UMj7@Tg00W]j8STg00_LR1f0R2g00_lR33Pp=0f1R4g00X_R5g00Y>R6P6g00Y^R7P2g00ZeF@p=<f3R8P5P6P6P7f2R9P4P2GSp=>g00@HR:#9g00XAR;/52g00@fR<#2#2#2#2#2#2#2#2#CR=,32'?X::R>=8:2#0A8:>4#0A6:29P>P4O1#0R?[^1:R@'DA8:>9#0A6:28P?[^1:;B2WAAA:>4P2O2P@g01D9p4p710R@p-0\2R>%94R?P0A:942f4RA?629PAP4O1[^18RB[A6824P8P4O1[^19A:894[RCA:A89\BAV942P2n2001000000120000000W4W8W5PC^4?^8>^5@P2P:11;2142=R@'7X::P8A6:2AP8P4P2O215;4134='?#015;9R>139=R?;U2%0>%0?'7P015;8#0138=#011;A14A='7P2f5,5;#0f6/3=#0P01542#01194[RA11421594#0R?[1189\?1T42P4n2001000000120000000X2:X3:PA^2:^3:P2P;f8RAP9O311;AP01342#01494[R014421394#0RA[1489\A1R42P4n2001000000120000000X2:X3:P0^2:^3:P2f:R0P=P8O3140=g00\nR0#Q%901J:4%G:%F:R0P:1E:<R<g00[E1=:=C;,<0RA%H6R?P0P:1=:;g00^eP<C;,<0R<P?P0P5P6P6P7P<PAFIC>C>1K07P2P91L131M29#0dAN:;4COb>b?b@X9:11;411;9149='7[\@^9:P2f<P4P8O3b=b7b0b6b0W7W6P4P2O2n2001000000121000000b0b0W<X1:O4b;b0W0W4o"). Qed.

Instance LS17ok : MallocLayoutOk LS16.
Proof.
  pose proof s16_bases as B.
  split.
  -  cbn. lia.
  -  intros a Ha. apply seg_rom_none_of_find. apply s16_find_none. exact Ha.
  -  intros m a Ha. apply wview_of_find_none. apply s16_find_none. exact Ha.
  -  intros m a Ha. cbn in Ha.
    destruct (Z.lt_ge_cases (bv_unsigned a) B1).
    + apply (wview_of_find_ro _ m a SEG0); [apply s16_find_seg0; lia | reflexivity].
    + apply (wview_of_find_ro _ m a SEG1); [apply s16_find_seg1; lia | reflexivity].
  -  intros m a Ha. cbn in Ha.
    destruct (Z.lt_ge_cases (bv_unsigned a) B3).
    + apply (wview_of_find_rw _ m a SEG2); [apply s16_find_seg2; lia | reflexivity |].
      pose proof (chk_range_sound _ _ _ s16_seg2_bytes (bv_unsigned a - B2) ltac:(lia)) as Hc.
      unfold chk_seg_byte in Hc. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 B))))).
      destruct (segment_byte_at (seg_bytes SEG2) (Z.to_N (bv_unsigned a - B2))); [discriminate | discriminate].
    + apply (wview_of_find_rw _ m a SEG3); [apply s16_find_seg3; lia | reflexivity |].
      pose proof (chk_range_sound _ _ _ s16_seg3_bytes (bv_unsigned a - B3) ltac:(lia)) as Hc.
      unfold chk_seg_byte in Hc. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 B))))))).
      destruct (segment_byte_at (seg_bytes SEG3) (Z.to_N (bv_unsigned a - B3))); [discriminate | discriminate].
  -  intros a Ha. cbn in Ha.
    destruct (Z.lt_ge_cases (bv_unsigned a) B1); [| destruct (Z.lt_ge_cases (bv_unsigned a) B2); [| destruct (Z.lt_ge_cases (bv_unsigned a) B3)]].
    + apply (seg_rom_some_of_find _ a SEG0); [apply s16_find_seg0; lia | reflexivity |].
      pose proof (chk_range_sound _ _ _ s16_seg0_bytes (bv_unsigned a - B0) ltac:(lia)) as Hc.
      unfold chk_seg_byte in Hc. rewrite (proj1 B).
      destruct (segment_byte_at (seg_bytes SEG0) (Z.to_N (bv_unsigned a - B0))); [discriminate | discriminate].
    + apply (seg_rom_some_of_find _ a SEG1); [apply s16_find_seg1; lia | reflexivity |].
      pose proof (chk_range_sound _ _ _ s16_seg1_bytes (bv_unsigned a - B1) ltac:(lia)) as Hc.
      unfold chk_seg_byte in Hc. rewrite (proj1 (proj2 (proj2 B))).
      destruct (segment_byte_at (seg_bytes SEG1) (Z.to_N (bv_unsigned a - B1))); [discriminate | discriminate].
    + apply (seg_rom_some_of_find _ a SEG2); [apply s16_find_seg2; lia | reflexivity |].
      pose proof (chk_range_sound _ _ _ s16_seg2_bytes (bv_unsigned a - B2) ltac:(lia)) as Hc.
      unfold chk_seg_byte in Hc. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 B))))).
      destruct (segment_byte_at (seg_bytes SEG2) (Z.to_N (bv_unsigned a - B2))); [discriminate | discriminate].
    + apply (seg_rom_some_of_find _ a SEG3); [apply s16_find_seg3; lia | reflexivity |].
      pose proof (chk_range_sound _ _ _ s16_seg3_bytes (bv_unsigned a - B3) ltac:(lia)) as Hc.
      unfold chk_seg_byte in Hc. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 B))))))).
      destruct (segment_byte_at (seg_bytes SEG3) (Z.to_N (bv_unsigned a - B3))); [discriminate | discriminate].
  -  intros b sz Hin. cbv -[Z_to_bv] in Hin.
    destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; rewrite !u64_lit by lia; cbn; lia.
  -  intros a Ha. cbn in Ha.
    destruct (Z.lt_ge_cases a B1); [| destruct (Z.lt_ge_cases a B2); [| destruct (Z.lt_ge_cases a B3)]].
    + exists (Z_to_bv 64 B0), (Z_to_bv 64 (B1 - B0)). split; [cbv -[Z_to_bv]; tauto | rewrite !u64_lit by lia; lia].
    + exists (Z_to_bv 64 B1), (Z_to_bv 64 (B2 - B1)). split; [cbv -[Z_to_bv]; tauto | rewrite !u64_lit by lia; lia].
    + exists (Z_to_bv 64 B2), (Z_to_bv 64 (B3 - B2)). split; [cbv -[Z_to_bv]; tauto | rewrite !u64_lit by lia; lia].
    + exists (Z_to_bv 64 B3), (Z_to_bv 64 (B4 - B3)). split; [cbv -[Z_to_bv]; tauto | rewrite !u64_lit by lia; lia].
  -  vm_compute. reflexivity.
  -  reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  -  reflexivity.
  -  reflexivity.
  - reflexivity.
  - reflexivity.
  -  reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  -  cbn; rewrite !u64_lit by lia; lia.
  - cbn; rewrite !u64_lit by lia; lia.
  - cbn; rewrite !u64_lit by lia; lia.
  - cbn; rewrite !u64_lit by lia; lia.
  - cbn; rewrite !u64_lit by lia; lia.
  - unfold CTX_SIZE; cbn; rewrite !u64_lit by lia; lia.
  - cbn; rewrite !u64_lit by lia; lia.
  -  apply chk_rom_bytes_sound; [apply Forall_map_mod256 | exact (proj2 (proj2 (proj2 (proj2 s16_tables))))].
  -  intros a Ha. cbn in Ha. rewrite !u64_lit in Ha by lia.
    pose proof (chk_list_sound _ _ _ s16_ctx_zero (bv_unsigned a) ltac:(cbn; rewrite !u64_lit by lia; lia)) as Hc.
    unfold chk_rom_zero in Hc. rewrite Z_to_bv_bv_unsigned in Hc.
    destruct (seg_rom ml_segs a) as [v|]; [|discriminate]. apply Z.eqb_eq in Hc.
    f_equal. rewrite <- (Z_to_bv_bv_unsigned 8 v). rewrite Hc. reflexivity.
  -  cbn; rewrite !u64_lit by lia; lia.
  - reflexivity.
  - apply chk_rom_bytes_sound; [apply Forall_lt256_of_chk; vm_compute; reflexivity | exact (proj1 s16_tables)].
  - apply chk_rom_bytes_sound; [apply Forall_lt256_of_chk; vm_compute; reflexivity | exact (proj1 (proj2 s16_tables))].
  - apply chk_rom_bytes_sound; [apply Forall_lt256_of_chk; vm_compute; reflexivity | exact (proj1 (proj2 (proj2 s16_tables)))].
  - apply chk_rom_bytes_sound; [apply Forall_lt256_of_chk; vm_compute; reflexivity | exact (proj1 (proj2 (proj2 (proj2 s16_tables))))].
  -  repeat (apply Forall_cons || apply Forall_nil); cbv; repeat split; congruence.
Qed.
