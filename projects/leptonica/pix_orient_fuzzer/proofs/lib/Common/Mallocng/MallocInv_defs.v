(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg VmLedger.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import MallocLayout MallocTree MallocOps.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_MallocInv_defs () := "c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defsCalloc_ceiling_rangeC1?~~~~~~~~~~~~~~~C47Corelib7Program6Basics4flipC46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes3appC69OSSVerify5KrLib6Common8Mallocng<MallocLayout8mlo_hullC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout6IMG_LOC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout5RW_LOC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC69OSSVerify5KrLib6Common8Mallocng<MallocLayout6IMG_HIC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic3and00C69OSSVerify5KrLib6Common8Mallocng<MallocLayout7mlo_ctxC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02C69OSSVerify5KrLib6Common8Mallocng<MallocLayout5A_CTXC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib6Common8Mallocng<MallocLayout6A_LOCKC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib6Common8Mallocng<MallocLayout=mlo_order_gotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout9A_GOT_SSPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout7A_ERRNOC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout?mlo_order_errnoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout4A_TPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout<mlo_order_tpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout5A_SSPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout=mlo_order_sspC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout6A_LIBCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout>mlo_order_libcC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib6Common8Mallocng<MallocLayout=mlo_order_ctxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayoutAA_MALLOC_REPLACEDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayoutBmlo_order_replacedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout=mlo_ctx_alignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout9mlo_errnoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib6Common8Mallocng<MallocLayout<mlo_tp_alignC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs=alloc_ceilingC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4ZdivAZ_div_mod_eq_fullC56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3mulC46Stdlib6ZArith4Zdiv:Z_mod_multC56Stdlib6ZArith6BinInt1Z8mul_commC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init5Logic6eq_indK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init5Logic3and01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib6Common8Mallocng<MallocLayout8CTX_SIZEC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5LOCKAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5ERRNOC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs3CTXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs7CTX_ENDC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs;layout_numsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout=mlo_tables_roC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout:A_DEBRUIJNC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout>A_SIZE_CLASSESC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout?A_SMALL_CNT_TABC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout=A_MED_CNT_TABC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayoutFmlo_size_classes_alignC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs>T_SIZE_CLASSESC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs;T_SMALL_CNTC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs9T_MED_CNTC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs:T_DEBRUIJNC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs8meta_rec01C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs7mr_prevC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs7mr_nextC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs6mr_memC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs8mr_availC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs8mr_freedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs6mr_w32C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs2MTC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs4mt_fC1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs6mfield00C1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5mrole00C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs6mfield01C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs6mfield02C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs6mfield03C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs6mfield04C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs6mfield05C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs6mfield06C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs7mt_roleC1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs8meta_rec00C1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC47Corelib4Init5Logic6eq_symc69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs8word_eqZC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5caddrC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5cslot01C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs8C_SECRETC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout;A_INIT_DONEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout=mlo_init_doneC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5cslot02C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs6C_INITC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout:A_MMAP_CTRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout<mlo_mmap_ctrC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5cslot03C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5C_CTRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout@A_FREE_META_HEADC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayoutBmlo_free_meta_headC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5cslot04C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5C_FMHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout<A_AVAIL_METAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout>mlo_avail_metaC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5cslot05C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs4C_AMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout@A_AVAIL_META_CNTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayoutBmlo_avail_meta_cntC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5cslot06C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5C_AMCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout@A_AVAIL_AREA_CNTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayoutBmlo_avail_area_cntC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5cslot07C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5C_AACC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout<A_META_SHIFTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout>mlo_meta_shiftC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5cslot08C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs7C_SHIFTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout;A_AREA_HEADC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout=mlo_area_headC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5cslot09C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs7C_AHEADC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout;A_AREA_TAILC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout=mlo_area_tailC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5cslot0:C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs7C_ATAILC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout=A_AVAIL_AREASC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout?mlo_avail_areasC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5cslot0;C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs8C_AAREASC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout5A_SEQC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout7mlo_seqC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5cslot0<C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5C_SEQC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout5A_BRKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout7mlo_brkC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5cslot0=C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5C_BRKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout;Z_UNMAP_SEQC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout=mlo_unmap_seqC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5cslot0@C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs6C_USEQC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout9Z_BOUNCESC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout;mlo_bouncesC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5cslot0AC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs8C_BOUNCEC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions:bv_modulusC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lC45stdpp9bitvector;definitions@Z_to_bv_unsignedC59OSSVerify5KrLib6Common5Hoare3at_C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismc69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5at_Z0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs9A_LOCK_eqC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpc69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs8A_CTX_eqC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Class HeapTop := {
  alloc_ceiling : Z;
  alloc_ceiling_range : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000
}.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition LOCKA : Z := bv_unsigned A_LOCK.
Definition CTX : Z := LOCKA + 8.
Definition CTX_END : Z := LOCKA + 936.   (* [comment removed for export] *)
Definition C_SECRET : Z := LOCKA + 8.
Definition C_INIT : Z := LOCKA + 16.     (* [comment removed for export] *)
Definition C_CTR : Z := LOCKA + 20.      (* [comment removed for export] *)
Definition C_FMH : Z := LOCKA + 24.
Definition C_AM : Z := LOCKA + 32.
Definition C_AMC : Z := LOCKA + 40.
Definition C_AAC : Z := LOCKA + 48.
Definition C_SHIFT : Z := LOCKA + 56.
Definition C_AHEAD : Z := LOCKA + 64.
Definition C_ATAIL : Z := LOCKA + 72.
Definition C_AAREAS : Z := LOCKA + 80.
Definition C_ACTIVE : Z := LOCKA + 88.   (* [comment removed for export] *)
Definition C_USAGE : Z := LOCKA + 472.   (* [comment removed for export] *)
Definition C_USEQ : Z := LOCKA + 856.    (* [comment removed for export] *)
Definition C_BOUNCE : Z := LOCKA + 888.  (* [comment removed for export] *)
Definition C_SEQ : Z := LOCKA + 920.     (* [comment removed for export] *)
Definition C_BRK : Z := LOCKA + 928.
Definition ERRNO : Z := bv_unsigned A_ERRNO.

Definition T_SIZE_CLASSES : Z := bv_unsigned A_SIZE_CLASSES.
Definition T_SMALL_CNT : Z := bv_unsigned A_SMALL_CNT_TAB.
Definition T_MED_CNT : Z := bv_unsigned A_MED_CNT_TAB.
Definition T_DEBRUIJN : Z := bv_unsigned A_DEBRUIJN.

(* [comment removed for export] *)
Definition size_classes : list Z := size_classes_tab.

(* [comment removed for export] *)
Lemma alloc_ceiling_val : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "p;1g0000j10Tp,2HT#0o"). Qed.

Lemma layout_nums :
  (LOCKA = bv_unsigned A_LOCK /\ CTX = LOCKA + 8 /\ CTX_END = LOCKA + 936 /\ ERRNO = bv_unsigned A_ERRNO /\
   bv_unsigned A_CTX = LOCKA + 8) /\
  4096 <= IMG_LO /\ IMG_LO <= RW_LO /\ RW_LO + 64 <= LOCKA /\ LOCKA + 940 <= IMG_HI /\ IMG_HI <= 2^32 /\
  0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000 /\
  RW_LO <= ERRNO /\ ERRNO + 4 <= LOCKA.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "p'0h04__x1h14__p1h22H9h34__x2h44__p2h54__x3h63H10h73H11h83H12h93H13h:3H14h;3H15h<3H16h=3H17h>3H18h?3H19h@3H20hA3H21hB3H22hC3H23hD3H24hE7__arithhF4__ffhG4__p3hH8__varmaphI5__withJ5__x10hK5__x11hL5__x12hM5__x13hN4__x4hO4__x5hP4__x6hQ4__x7hR4__x8hS4__x9hT1qhU2q0hV2q1hW1rhX2r0hY2r1hZ3H25h[3H26h\3H27h]3H28h^3H29h_3H30h`3H31ha3H32hb3H33hc3H34hd9__sat4097he9__sat4098hf9__sat4099hg9__sat4100hh9__sat4101hi9__sat4102hj9__sat4103hk9__sat4104hl2q2hm2q3hn2r2ho2r3hp3H35hq3H36hr3H37hs3H38ht5__x14hu5__x15hv2q4hw2r4hx4__p4hy5__x16hz5__x17h{5__x18h|5__x19h}2Hah~1Hi002H0i012H1i022H2i032H3i042H4i055H4096i062H5i072H6i082H7i092H8i0:3HE4i0;2Hei0<2Hhi0=4Hlo0i0>2Hmi0?2Hti0@2_Hi0A3_H0i0B3_H1i0C3_H2i0D7__sat10i0E7__sat11i0F7__sat12i0G7__sat13i0H1zp%0p%1p%2p&0p;2p;1p;4p;3p;6p;7p;8p-1R0p1001GR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001ep4p710p8P0p1002<p4p710p8g002Yk20qTg003ck10pTg004kk10KTg0062j20Tg006Nk10`Tg007Vj12Tg008;j1]Tg008Yk20WTg0096j2aTg009VR0j21Tg00:1k20hTg00;:k10<Tg00;Xk10_Tg00<_j2\Tg00=Ik10^Tg00>Qj2<Tg00>nk20]Tg00@=k10\Tg00AHk10[Tg00BQk20STg00Cbk10RTg00Dhk20PTg00F6k10OTg00G=k20NTg00HLk10JTg00ITk20HTg00Jdj18Tg00KIk20CTg00LXk10BTg00Mkk20ATg00O?k20@Tg00PNk20?Tg00QYj2ZTg00R6k20oTg0000k10mTg00SDk10cTg00TUk20;Tg00U<j2nTg00UYj2mTg00VJk209Tg00W;j2lTg00W\k100Tg00X5j2kTg00X\j2CTg00Y8j2jTg00Y_j2gTg00ZEj2iTg00Zkk108Tg00[Ik207Tg00[jj1:Tg00\Ik206Tg00]2j2eTg00]^k10ZTg00^>k10YTg00^^k10XTg00_<k10VTg00_Zk10UTg00`Ek204Tg00`hk10QTg00aJk203Tg00amj4PTg00bXk20MTg00c:j2rTg00cTk20ITg00d@j3NTg00dZk30GTg00e9k40FTg00ekk20ETg00fSk30DTg00g7j3{Tg00gZj2QTg00h7k20>Tg00hWk20TTg00i9k605Tg00iWk60nTg00j3j2yTg00j\k30iTg00k?k401Tg00kZk30:Tg00lCj3^Tg00llk20gTg00mXk30fTg00n8k20eTg00nVj4sTg00o4j7pTg00oXk60dTg010<k30bTg010_j3~Tg011Bj8STg011fk60aTg012Jj7zTg012nk30lTg013WR1f0R2'Cp=K%22#2#2#2p=|%22#]p=Vg0145R3?N21p=4f1R4=N32p=3f2R5/<4/02p=A1054/12p=L%82#8p>0k%82#8#8#8p=o%22#2p=x%22#2#2#2#2#2#2#2p=wf3R61Q54/<25N3p=E1012p=;1021p=h20632p==B0:354=^32p=RA^3429^35p=[A^342p=fg014S-0g2p=_g015?R7@0f42p=Y20e32p=BP3P3f4R8P6P5CsP4P2Csp=>20432p=GP5g015kR9g016JR:P:g016jR;P3P4g017JR<P2CPg0181R=Fpp=9P4P9P:P:P;P2J0dp=}20332p=6B0b342p=JA~342p=@P5P9P:P:P;P3P4g018QR>P2CPP=Fpp=7P8P9P:P:P;P6P9P:P:P;P5P=FpP4P2GSp=Hf5R?P9P:P:P;P8P9P:P:P;P3P6P<P5CPP=FpP4P2GSp=Xf6R@P9P:P:P;P?P9P:P:P;P8P6P5GSP4P2GSp=UB0:342p=OP3P8P6P3P5P4P2CsCsp=uP3P5P4P2Csp=MP3P5P<A~342CPp>02P8P9P:P:P;P6P5P4P9P:P:P;P2P=FpGSp=WP3A~354P>P2CPp=`P3P4P>P2CPp=vP4P9P:P:P;P2P=Fpp>0LP4P9P:P:P;P2J0ap=FP8P9P:P:P;P6P5P9P:P:P;P4P2FzFzp=TP3P4P<P2CPp=qP?P9P:P:P;P8P9P:P:P;P6P5FzP4P2GSp=IP@P9P:P:P;P?P8P6P9P:P:P;P5P4P2GSGSp=51<429N35p=b1142,15p=?P5P9P:P:P;P4P2Fzp=tP@P?P8P6P5P4P2H01H01p=dP6P9P:P:P;P5P4P2GSp>0=B0l342p=DA^3429^359^369^38p=c1Q54/<2p>0jp,2MLR9p,4MLokR<+0q&0p9R=#KS00&0K9R>,0=S01&0`9RA,0>S02g0198RB#2RC#]RD%2CS03#2RE#2S04#2S05#]S06+0WS07,0ARFQ05#2S08#2#|#VRG,a=RH#4RI1a>GRJ#41aAGRK#4'1RL'1RM'1RN'1RO'1RP'120h9<Q08$0<RQ&0_9'\RR&0^9,\QRS%]ERT'<S09'3S0:20]9<&0\9,\QS0;Q0;&0[9,\QRU7AT5L>20S9<Q03#]RV,<US0<&0R9,\QRW'020P9<&0O9,\QS0=,0W20N9<Q0=&0J9,\QS0>7AT20H9<Q0>%8BS0?#8RX#2S0@#2#VS0A;AS20C9<g019]&0B9,\QS0B5AR20A9<Q0B?AVA20@9<1aRTRQ#420?9<%8CRY#2S0C#2S0D#8S0E#2#VRZ,ZWS0F,3U20o9<1aWTR<#4p,2HTR9$0m%8XS0G#8$0k#o#oR[#2#o#o#x#|#w#w#VS0H&0c9S0I'0S0JQ0I%8[#o#o#x#|#w#w#VS0K'0S0L'1S0MP0Q00PP10G=S0Nf<R[Q00P0Q01POQ0NP2Q01P0Q02PNQ0NP2Q02P0PFPMQ0NP2P0PIPLQ0NP220;=GP=PG1n=GR0PHCER91mRTS0O%;R%;TR\%;QR][[S0P209=G%;=R^%;GR_%;0[[1mWTS0Q%;WR`%;<Ra\\[S0R1m=GS0S%;HRb\_\^S0T1l=GS0U%4GR^$00RcP9[S0V1k=GS0W%KGR91CHG,1b[S0X1j=GS0Y1CG1Rb1CGH%hH'1[S0Z1g=GS0[%40\^S0\1i=GS0]13H=\^S0^P0P3PHP31lWTS0_%4TRd$00RePWPT1nWTRfP<CES0`[S0a1kWTS0b%KTRg1C<T,1a[S0c1jWTS0d1CT1Ra1CT<%h<'1[S0e1gWTS0f%4f\dS0g1iWTRh13<W\dRiPfP3P<P31lRTRjPRPT1nRTRkPQCE\eRe1kRTRl1CQT,1]\gRg1jRTR]1CTQ%hQ'1\aRa1gRTRm%4k\dRn1iRTRo13QR\dRpPkP3PQP3&08B-073Rqg01:gRr#:Rs#:Rt#:Ru#=S0h%=tS0i2063rRr5Rq3R%:uRu#=S0jQ0hQ0i3[%=sS0k/frS0l#_'e'e&0Z7Rs'Y&0Y7R7%B6P6&0X3RtP6PtD>P5PtP4PtD>&0V3Rv&0U3RwPw%GGRx20431Ry59w,}wS0m&0Q:R:2033BRBQ04#6S0n,Jx%6CRC'@59wP:PwPwPCPyP:PwPwP3Pyg01;FS0oPBCPP:A7wxBS0pDHEXFU20Mw;R;P2P5g01;mRzg01<MR{'r20I25=Nz{dB0G314H0FR{bFbHbIX03X33X53g01<mS0q\^RzP4PGP6P5CE[%45%K510G6[[[^03^33^53P2f@R|f?R}P=fER~fLS0rf\O6bEbYbVbDbCbBbAb@bXbUb?b>b=b<b;bWbTb:b9b8b7b6c0Dc0Ec0Fc0Gb2Z0CLZ0>IP4P2O2n2001000000121000000X2MZ0BFP4P2O2n2001000000121000000X2NY0AP4P2O2n2001000000121000000X2OY0@P4P2O2n2001000000121000000X2PY0=P4P2O2n2001000000121000000Q0NP3Q0F1a2V#4Z0H3S0s20;WTQ0`1mAGS0`%;A%;KRP\_[S0tQ06-0EDS0u%KDQ06#;Q07#K[[S0v%;DROg01=JRNQ06>0DD4UW}S0wQ07#;\N^}OS0xQ0OQ0PQ0QQ0R209WT%;f\\\`Q0SQ0T1m>GS0y%;>%;JR`\_[S0zQ0_Q0aQ0bQ0cQ0dQ0eQ0fQ0gPhPiPfP3P<P31l>GS0{P>PG1n>GR_PJCE\cS0|1k>GS0}1CJG,1`\9S0~1j>GS101CGJ%hJ'1\bS111g>GS12%4_\^S131i>GS1413J>\^S15P_P3PJP3Q0UQ0VQ0WQ0XQ0YQ0ZQ0[Q0\Q0]Q0^P0P3PHP3PjPePlPgP]PaPmPnPoPpPkP3PQP31lAGS16PAPG1nAGR`PKCE\cS171kAGS181CKG,1P\9S191jAGS1:1CGK%hK'1\bS1;1gAGS1<%4`\^S1=1iAGS1>13KA\^S1?P`P3PKP3p-0R^%:uS1@#:S1A#:S1B#:S1C#:S1D#:S1E#:S1F#:S1G#:S1H#:S1I#:Ru#:S1J#:S1K#=S1L%=uS1M;[r#_Q1LQ1M,OqS1N/fr5Rq#_/Ys'YP7%B}S1Of7RuPtP8f;Rb#BS1PD>P5f9R9#BS1QfCRP%BPS1Rf=RcPtDuP4%B|S1Sf8R\;MtP?fBS1T#BS1U?M[tP6fARO#BS1Vf:RNPtP@f>RM#BS1WD>D>D>PvPwPwQ0mP:%6YS1X%8YS1Y#2#6,Jx%6ERY'@59wP:PwPw%GTRI=9wy,}wS1ZP:Q03#8S1[#6RLQ0C#8#6,JIQ0n'@59wP:PwPwQ0mP:PwQ03#6S1\Q1[#8#6,JxS1]%6XS1^402DWS1_P:PwPwQ1ZP:Pw1JIB%8E#6RE602CDWP:PwQ0?#6S1`97wxS1aP:PwA9wEyP:PwPwQ0?#2S0?#2S1b#6S1c%GZS1d9{3CS1eP:PwPwQ0nPyP:PwPwQ0G#6S0G%GVS0nQ1X3`P:PwPwQ0@#8#2S1f#2#x#VS1g#GS1hQ0G5`LP:PwPwQ0@#6S0@Q0A#GS1iQ0C#6RE3`P:PwPwQ0?#8#6S0CQ0@7`IP:PwPwQ0C,vCP:PwPwQ1\Q1Y#6S1j57wQ1j/@IQ1c57wP:PwPwPL1@EIS1kP:PwPwP3PyQ0oQ1`CP-0LwS0oPwQ1`Q1\57wS1lPw1Fw~S1mPwfFRX,FwS1nPwfGS1o,FwS1pPwQ1^=9wyS1qA9wYyDTDTDTS1rP:PwQ0n%GDS1s/JBQ0E#]S0E#G5{3'JQ1e'qDWEXEIDHDHDHDHDHEXEXF5F5FUFUP;P{bFbHbIX03X33X53XN3XO3XP3XQ3XR3XS3XJ3XK3XL3XM3Xt3Xu3Xy3Xz3X{3X|3X1^X4^WG1QGPS1e=b?u\zS1tQ0q\dS1u1QTPS1v=b9|[Q1e/<\S1w,3@\zQ1uP?PTP8PPCE[10G@S1xfDS1y#4S1z1ZuZ,3|%4~S1{AA~V[Q1g=A|XQ0AQ1T5AX1<XTS1|Q1o'0RdQ1o,0cAL|XdQ1|,3~%KOS1|Q1T,0OS1}fRS1~fSS20fTS21Q1zQ1{3?3?3?S1{1QD|Q0E'Z,QV1ZOZ'3[[[[[[[[[[[[[[[[^03^33^53^N3^O3^P3^Q3^R3^S3^J3^K3^L3^M3^t3^u3^y3^z3^{3^|3^1^^4^^G^P2%4}S22PFQ02P5P9Q1ofMS1oP\Q0BQ0>Q0=PUQ0;PSPRP4PXPAP>P=PWfNS23PuPMQ0rQ20f]f_f`fafbfcS24fdS25feS26fffhS27fiS28fjS29OVbEbobmbcbbbab`b_bnblb^b]b\b[bZbYbVbDbCbBbAb@bXbUb?b>b=b<b;bWbTb:b9b8b7b6bdbebfbgbhbibjbk1QDfQ0E'ZRD,QVRdQ0F'3P3PdQ0sP31QDVQ0s20>DVPd20TVDJ05Q0FP2J0nb6b2PUP6J051aUVRD#413SSS0FQ09Q09'3S0sQ1f#8S1f#x#VS0E,<SRd/3dS2:13UUS2;Q0:'1S2<'1S2='1S2>'1S2?Q0NQ01Q08#]S08,<>S2@/0SS2AQ1f#8#2#VS1f=ASAS2BQ0M10>US2CQ0</0SS0<'1S2D'1S2E,1FS2F'1S2G'1S2H'1S2I'1S2JQ0FQ2>1r3SQ0sQ2=Q09,r3Q2:Q2<1r3dQ2;Q0:1r3UQ0`Q0tQ0uQ0vQ0wQ0xQ0OQ0PQ0QQ0RQ0SQ0T1mUVS0:%;U%;V%;DS2;[[S2<Q0yQ0zQ0{Q0|Q0}Q0~Q10Q11Q12Q13Q14Q15P_P3PJP31lUVS2:%4VS09$00PUPV1nUVRdPDCE[S2=1kUVS0s%KVQ2;1CDV'1[S2;1jUVS2>1CV11CVD%hD'1[S0F1gUVS2KQ09%4d[S2L1iUVS2MQ0913DU[R1PdP3PDP3Q0UQ0VQ0WQ0XQ0YQ0ZQ0[Q0\Q0]Q0^P0P3PHP3Q0_Q0aQ0bQ0cQ0dQ0eQ0fQ0gPhPiPfP3P<P3PjPePlPgP]PaPmPnPoPpPkP3PQP3Q16Q17Q18Q19Q1:Q1;Q1<Q1=Q1>Q1?P`P3PKP3Q1@#=S1@,OqS2N/fr#_/YsP7PtPuQ1RP8Q1V?MbtD>S1VP5Q1O?M9tS1R%BcS2O7MPP4%B\S2PP?%B[S2QP6Q1SPNPtP@Q1U?MMtD>S1UD>D>PvPwPwQ0mP:Q1XQ1b#2#6,JxS1b/@Y59wP:PwPwQ1ZP:Q1Y#8#6,JIQ0G'@S1Y99wBP:PwPwQ0n=9wy,}wS1SP:PwQ0nQ0D#6'JQ1[#2#6Rx'@S1[,qEDWS0DP:PwQ1_P:PwA9wxyS1_P:PwQ1aP:PwQ1jQ1d5{3S1d99wES2RP:PwQ0G=9wyS0GP:PwPwQ0@Q0n'@S2SQ1X'vP:PwPwQ1hQ0@5`BP:PwQ0CQ1i'@S1i=7wCS1XP:PwQ1c/@IQ0C57wS0CP:PwQ1jQ1c57wS1jP:PwQ1\=7wL1@LIS1c=7wES2T5twS2UP:Pw1@CIS2V99wBRxP:PwQ1rP:PxF5F5F5DHDHF5F5F5FUFUP;P{bFbHbIX03X33X53XN3XO3XP3XQ3XR3XS3XJ3XK3XL3XM3Xt3Xu3Xy3Xz3X{3X|3X1^X4^XG^Q1tQ1uQ1v/<}S1v,35[Q09Q0q[S09PbPVPPPOCE[S0qQ1e=bu9\zQ1T#4S1r10GuS2W1Z}Z,3MS2XQ1zQ1y/<VS2Y/0[Q1g=A9~Q0A,<~S2Z/0bAA~TXS2[10~XS2\Q1yQ1y?AT~5L|S2]1<}TS2^,3MQ1{Ab|OT[[[[[[[[[[[[[[[[^03^33^53^N3^O3^P3^Q3^R3^S3^J3^K3^L3^M3^t3^u3^y3^z3^{3^|3^1^^4^^G^P2%4XS1tPFQ02P5P9Q23fUS1{Q1oP\Q0BQ0>Q0=PWPUQ0;P4Q21PAP>P=PSPRPuPMQ20fZS2_Q24Q25fgS2`Q27Q28Q29fkS2aflS2bfmS2cfoS2dfpS2efqS2fOVbEbwbvbsbrbqbpbcbobmbbbab`b_b^bnblb]b\b[bZbDbYbVbCbBbAb@b?bXbUb>b=b<b;b:bWbTb9b8b7b6b2bdbebfbgbhbibjbkFdFdQ0NQ2IQ0`Q0tQ0uQ0vQ0wQ0xQ0OQ0PQ0QQ0RQ0SQ0TQ0:Q2<Q0yQ0zQ0{Q0|Q0}Q0~Q10Q11Q12Q13Q14Q15P_P3PJP3Q2:Q2=Q0sQ2;Q2>Q0FQ2KQ2LQ2MP1PdP3PDP3Q0UQ0VQ0WQ0XQ0YQ0ZQ0[Q0\Q0]Q0^P0P3PHP3Q0_Q0aQ0bQ0cQ0dQ0eQ0fQ0gPhPiPfP3P<P3PjPePlPgP]PaPmPnPoPpPkP3PQP3Q16Q17Q18Q19Q1:Q1;Q1<Q1=Q1>Q1?P`P3PKP3PsP7%B4S2IPvPwQ0pP:Q0pH0=P;P{bFbHbIX0310G210G4[^03P2P=Q25O2bEbwbvbsbrbqbpbcbobmbbbab`b_b^bnblb]b\b[bZbDbYbVbCbBbAb@b?bXbUb>b=b<b;b:bWbTb9b8b7b6b2bdbebfbgbhbibjbkQ01Q2HQ0`Q0tQ0uQ0vQ0wQ0xQ0OQ0PQ0QQ0RQ0SQ0TQ0:Q2<Q0yQ0zQ0{Q0|Q0}Q0~Q10Q11Q12Q13Q14Q15P_P3PJP3Q2:Q2=Q0sQ2;Q2>Q0FQ2KQ2LQ2MP1PdP3PDP3Q0UQ0VQ0WQ0XQ0YQ0ZQ0[Q0\Q0]Q0^P0P3PHP3Q0_Q0aQ0bQ0cQ0dQ0eQ0fQ0gPhPiPfP3P<P3PjPePlPgP]PaPmPnPoPpPkP3PQP3Q16Q17Q18Q19Q1:Q1;Q1<Q1=Q1>Q1?P`P3PKP3PsP7%B5?M4tPvPwPw1Fw8S2HA7wBCS0p1Fw?S2g5twP:Q0pEIP;P{bFbHbIX03X33X1^X4^1024=?561045[^03^33^1^^4^P2Q02Q1tQ21#4%44S2h3?S2i7?FS2jQ00P>P=Q2fO5bEbwbvbsbrbqbpbcbobmbbbab`b_b^bnblb]b\b[bZbDbYbVbCbBbAb@b?bXbUb>b=b<b;b:bWbTb9b8b7b6b2bdbebfbgbhbibjbkQ2AQ2GQ0`Q0tQ0uQ0vQ0wQ0xQ0OQ0PQ0QQ0RQ0SQ0TQ0:Q2<Q0yQ0zQ0{Q0|Q0}Q0~Q10Q11Q12Q13Q14Q15P_P3PJP3Q2:Q2=Q0sQ2;Q2>Q0FQ2KQ2LQ2MP1PdP3PDP3Q0UQ0VQ0WQ0XQ0YQ0ZQ0[Q0\Q0]Q0^P0P3PHP3Q0_Q0aQ0bQ0cQ0dQ0eQ0fQ0gPhPiPfP3P<P3PjPePlPgP]PaPmPnPoPpPkP3PQP3Q16Q17Q18Q19Q1:Q1;Q1<Q1=Q1>Q1?P`P3PKP3Q1J#=S1JQ1I#=S1IQ1E#=S1E,OqQ0jQ0l'f3[5RqQ06,y3/Dr1y3VRXQ1L'DQ03$08-073RxQ1M'OS03Q1G#=S1G,DXQ1F#=,DXS1FQ1E,DXS1EQ1D#=S1D,DXS1LQ1C#=,DXS1CQ1B#=,DXS1BQ1A#=,DXS1AQ1@Q0i,OxS065Rx3[DcDc#_'e/YsP7%B?S1@P}Q1WP9PtDuP5Q2QPuPtP8PtD>P4%B@P}%BNP6Q2OP\PtP}Q1O?MbtD>D>D>S1OPvPwPwQ1ZP:PwQ1Y,qYDWS1WP:PwQ0DP:PwPwQ0mP:PwQ1]Q0?#6S0?'@S1],qBDWS2GP:PwQ1_P:PwQ1aP:PwQ2RP:PwQ0GP:PwQ1XP:PwQ0CP:PwQ1jP:PwPwA7wBLQ2TP:PwPwPYQ2VP:PwPwQ0oPwQ1`=7wBPw1FwOPwQ1T,FwPw1FwPPwQ0?=9wyS0?Q1y,FwDTDTDTS1TP:PwQ08#G=`BCDWEXEIF5F5F5F5F5P;P{bFbHbIX03X33X53XN3XO3XP3XQ3XR3XS3XJ3XK3XL3XM3Xt3Xu3X1^X4^XG^Xx^Q1uP?PTP}PbCE[S1`Q09B0jV}cS2T,3\[P6PGP}P@CE\zS2A%4MS2kQ1x1Z[ZS2l,3b%4|S2mQ0A,<|S2n/0\1<|TS2o/0OS2p10|OS2qQ2^/0|9LN}Ab}[T%KM10M[fKQ0rQ1oQ22Q233?3?3?S0rQ08=AcM[[[[[[[[[[[[[^03^33^53^N3^O3^P3^Q3^R3^S3^J3^K3^L3^M3^t3^u3^1^^4^^G^^x^P2Q2hQ1tPFQ02P9Q23Q1{Q1oP\Q0>Q0=PWPUQ0;PRQ21P=PSP>PMQ20Q2_Q24Q25Q2`Q27Q2aQ2bQ2cQ2dQ2eQ2fOPbEbwbvbsbrbqbpbcbobmbbbab`b_b^bnblb]b\b[bZbDbYbVbCbBbAb@b?bXbUb>b=b<b;b:bWbTb9b8b7b6b2bdbebfbgbhbibjbkQ2BQ2FQ0`Q0tQ0uQ0vQ0wQ0xQ0OQ0PQ0QQ0RQ0SQ0TQ0:Q2<Q0yQ0zQ0{Q0|Q0}Q0~Q10Q11Q12Q13Q14Q15P_P3PJP3Q2:Q2=Q0sQ2;Q2>Q0FQ2KQ2LQ2MP1PdP3PDP3Q0UQ0VQ0WQ0XQ0YQ0ZQ0[Q0\Q0]Q0^P0P3PHP3Q0_Q0aQ0bQ0cQ0dQ0eQ0fQ0gPhPiPfP3P<P3PjPePlPgP]PaPmPnPoPpPkP3PQP3Q16Q17Q18Q19Q1:Q1;Q1<Q1=Q1>Q1?P`P3PKP3Q1K#:#:Ry#:S1K#=,OqS2F%=yQ1H#=RyQ2NQ0k=RqrDc1y3T/DrQ1K#:#=Q2FQ1I,OqS2FQ1GQ0i5[yDc#_'e/YsP7Q1VP5Q1RQ2O7M?P4Q2PPPQ2QP6Q1UD>D>PvPwPwQ0mP:Q1bQ1^'@99wCP:PwQ1WP:PwQ0DP:PwPwQ0mP:Q1\Q1]59wP:PwQ1_P:PwQ1aP:PwQ2RP:PwQ0GP:PwPwQ2S/vCP:PwPwQ1hQ0@5`YP:PwPwQ1i/vBP:PwQ0CP:PwQ1jP:PwQ2UP:Pw1@BI99wYP:PwPwQ0oPwQ1lPwQ1mPwQ1nPwQ1pQ0?Q1q5twDTDTP:Q1f#G,@B=7wCEIF5F5DHDHDHF5F5FUF5FUP;P{bFbHbIX03X33X53XN3XO3XP3XQ3XR3XS3XJ3XK3XL3XM3Xt3Xu3Xy3Xz3X{3X|3X1^X4^XG^Q1e=b5@\zQ1uQ1v,3\[Q0qQ1w,3u\zQ1rQ2WQ2XQ1zQ2Y/09Q1g=A}~Q2Z/0NQ2[Q2\Q2]Q1y1<MTR~'3Q1|Q1}Q1~Q20Q21%4PQ1z3?3?3?Q1f=A|O[[[[[[[[[[[[[[[[^03^33^53^N3^O3^P3^Q3^R3^S3^J3^K3^L3^M3^t3^u3^y3^z3^{3^|3^1^^4^^G^P2Q1tPFQ02P5P9Q23Q1{Q1oP\Q0BQ0>Q0=PWPUQ0;PRP4Q21P>P=PAPSPuPMQ20Q2_Q24Q25Q2`Q27Q28Q29Q2aQ2bQ2cQ2dQ2eQ2fOVbEbwbvbsbrbqbpbcbobmbbbab`b_b^bnblb]b\b[bZbDbYbVbCbBbAb@b?bXbUb>b=b<b;b:bWbTb9b8b7b6b2bdbebfbgbhbibjbkPFQ2EQ0`Q0tQ0uQ0vQ0wQ0xQ0OQ0PQ0QQ0RQ0SQ0TQ0:Q2<Q0yQ0zQ0{Q0|Q0}Q0~Q10Q11Q12Q13Q14Q15P_P3PJP3Q2:Q2=Q0sQ2;Q2>Q0FQ2KQ2LQ2MP1PdP3PDP3Q0UQ0VQ0WQ0XQ0YQ0ZQ0[Q0\Q0]Q0^P0P3PHP3Q0_Q0aQ0bQ0cQ0dQ0eQ0fQ0gPhPiPfP3P<P3PjPePlPgP]PaPmPnPoPpPkP3PQP3Q16Q17Q18Q19Q1:Q1;Q1<Q1=Q1>Q1?P`P3PKP3PsP7Q2IPvPwPw1Fw6ROPwQ2HPwQ2gQ1sQ05$0<60i397wBRP1Fw@5twDTP:PPEIP;P{bFbHbIX03X1^X4^XG^Xx^Q07,02=?689?45Q07,04[^03^1^^4^^G^^x^P2Q2iQ02Q01Q00PAQ2fO6bEbwbvbsbrbqbpbcbobmbbbab`b_b^bnblb]b\b[bZbDbYbVbCbBbAb@b?bXbUb>b=b<b;b:bWbTb9b8b7b6b2bdbebfbgbhbibjbkQ0MQ2DQ0JQ0LQ0`Q0tQ0uQ0vQ0wQ0xQ0OQ0PQ0QQ0RQ0SQ0TQ0:Q2<Q0yQ0zQ0{Q0|Q0}Q0~Q10Q11Q12Q13Q14Q15P_P3PJP3Q2:Q2=Q0sQ2;Q2>Q0FQ2KQ2LQ2MP1PdP3PDP3Q0UQ0VQ0WQ0XQ0YQ0ZQ0[Q0\Q0]Q0^P0P3PHP3Q0_Q0aQ0bQ0cQ0dQ0eQ0fQ0gPhPiPfP3P<P3PjPePlPgP]PaPmPnPoPpPkP3PQP3Q16Q17Q18Q19Q1:Q1;Q1<Q1=Q1>Q1?P`P3PKP3PsP7Q2IPvPwPwQ0H#G=7wBRPPOP:PPEIP;P{bFbHbIX03X1^Q0H?L24Q0H/04[^03^1^P2Q0LQ0IQ26O3bEbwbvbsbrbqbpbcbobmbbbab`b_b^bnblb]b\b[bZbDbYbVbCbBbAb@b?bXbUb>b=b<b;b:bWbTb9b8b7b6b2bdbebfbgbhbibjbkQ0`Q0tQ0uQ0vQ0wQ0xQ0OQ0PQ0QQ0RQ0SQ0TQ0:Q2<Q0yQ0zQ0{Q0|Q0}Q0~Q10Q11Q12Q13Q14Q15P_P3PJP3Q2:Q2=Q0sQ2;Q2>Q0FQ2KQ2LQ2MP1PdP3PDP3Q0UQ0VQ0WQ0XQ0YQ0ZQ0[Q0\Q0]Q0^P0P3PHP3Q0_Q0aQ0bQ0cQ0dQ0eQ0fQ0gPhPiPfP3P<P3PjPePlPgP]PaPmPnPoPpPkP3PQP3Q16Q17Q18Q19Q1:Q1;Q1<Q1=Q1>Q1?P`P3PKP3PsP7Q2IPvPwPwPOQ0K#G97wBROP:POEIP;P{bFbHbIX03X1^Q0K,02,14Q0K,04[^03^1^P2Q0JQ0IQ26O3bEbwbvbsbrbqbpbcbobmbbbab`b_b^bnblb]b\b[bZbDbYbVbCbBbAb@b?bXbUb>b=b<b;b:bWbTb9b8b7b6b2bdbebfbgbhbibjbkH01Q2CQ0<Q0`Q0tQ0uQ0vQ0wQ0xQ0OQ0PQ0QQ0RQ0SQ0TQ0:Q2<Q0yQ0zQ0{Q0|Q0}Q0~Q10Q11Q12Q13Q14Q15P_P3PJP3Q2:Q2=Q0sQ2;Q2>Q0FQ2KQ2LQ2MP1PdP3PDP3Q0UQ0VQ0WQ0XQ0YQ0ZQ0[Q0\Q0]Q0^P0P3PHP3Q0_Q0aQ0bQ0cQ0dQ0eQ0fQ0gPhPiPfP3P<P3PjPePlPgP]PaPmPnPoPpPkP3PQP3Q16Q17Q18Q19Q1:Q1;Q1<Q1=Q1>Q1?P`P3PKP3Q1NQ1IQ0l9Rqy3[Q04#],y3/DrROQ1J,DXQ03Q1I,DXQ1BQ1AQ063[Dc#_'e/YsP7Q1OPvPwQ1WP:PwPwQ1SP:PwQ1[,qCDWP:PwQ2GP:PwQ1_P:PwQ1aP:PwQ1d99wCP:PwQ0GP:PwQ1i=7wLP:PwQ0CP:PwQ1jP:PwPwA7wBEQ1k=7wCP:PwPwPYQ1cP:PwQ1TP:Q0pH0=EXEIF5F5F5F5F5P;P{bFbHbIX03X33X53XN3XO3XP3XQ3XR3XS3XJ3XK3XL3XM3Xt3Xu3X1^X4^XG^Xx^Q1`Q09Q2T,36[Q2AQ2kQ1xQ2l,3@Q2mQ2n/0[Q2pQ2qQ2o/0b9LN|Q2o,3}Q0r10cMR|[[[[[[[[[[[[[^03^33^53^N3^O3^P3^Q3^R3^S3^J3^K3^L3^M3^t3^u3^1^^4^^G^^x^P2Q2hQ1tPFQ02P9Q23Q1{Q1oP\Q0>Q0=PWQ0;PSPRQ21P=PUP>PMQ20Q2_Q24Q25Q2`Q27Q2aQ2bQ2cQ2dQ2eQ2fOPbEbwbvbsbrbqbpbcbobmbbbab`b_b^bnblb]b\b[bZbDbYbVbCbBbAb@b?bXbUb>b=b<b;b:bWbTb9b8b7b6b2bdbebfbgbhbibjbkQ0`Q0tQ0uQ0vQ0wQ0xQ0OQ0PQ0QQ0RQ0SQ0TQ0:Q2<Q0yQ0zQ0{Q0|Q0}Q0~Q10Q11Q12Q13Q14Q15P_P3PJP3Q2:Q2=Q0sQ2;Q2>Q0FQ2KQ2LQ2MP1PdP3PDP3Q0UQ0VQ0WQ0XQ0YQ0ZQ0[Q0\Q0]Q0^P0P3PHP3Q0_Q0aQ0bQ0cQ0dQ0eQ0fQ0gPhPiPfP3P<P3PjPePlPgP]PaPmPnPoPpPkP3PQP3Q16Q17Q18Q19Q1:Q1;Q1<Q1=Q1>Q1?P`P3PKP3Q2FPyQ1GQ1D,OqQ0h/frDcQ1M,DXQ1IQ1FQ1EQ1LQ1CQ1BQ0j,Ox'fDc9Rxy5Rx5[O#_'e/YsP7PtP8Q2QP\PtDuP5Q1PP@PtPcPtD>P4Q1@PcQ1QP6%BuPcQ2OPNPtDuD>D>PvPwPwQ1ZP:Q1Y99wLP:PwPwQ1SP:Q1[99wBP:PwQ1_P:PwQ1aP:PwPwPBQ1dP:PwQ0GP:PwQ1XP:PwQ0CP:PwQ1jP:PwPwQ1\=7wEQ1k=7wBP:PwPwPLQ2VP:PwPwQ0oQ1l1Fw}5twP:Q0n,@B=7wCEIEXEIF5F5EXF5FUFUP;P{bFbHbIX03X33X53XN3XO3XP3XQ3XR3XS3XJ3XK3XL3XM3X1^Q1uP?PTPcPNCE[Q09P5PVPcP[CE[%4[10G?1ZNZ,38Q2kQ0A=AMu10~}10M}10~99L[MAbMbT%KcfH7?|AA[Vc[[[[[[[[[[[[^03^33^53^N3^O3^P3^Q3^R3^S3^J3^K3^L3^M3^1^P2Q2jP9Q23Q1oP\Q0>Q0=PWQ0;PRP>P=PSPUPMQ20Q24Q25Q2`Q27Q2aQ2bQ2cQ2dQ2eQ2fOJbEbwbvbsbrbqbpbcbobmbbbab`b_b^bnblb]b\b[bZbDbYbVbCbBbAb@b?bXbUb>b=b<b;b:bWbTb9b8b7b6b2bdbebfbgbhbibjbkFdFdFdFdc0:c05Q2?Q2J'1ec09c0?c0;c08c07c06c04c03c02c01c00b~c0<g01=fRM=N3SRS1<MTRT/3TQ0E,<MR=/3=g01>oRW=N3U13RT'1RR'13?Q0NQ01Q2@Q1f,<MQ0MAAWVM9L>W5?F7LA7LM3?RM'1eg01@8=N3Tg01A?=N3=/1R5?S/1Meo"). Qed.

(* [comment removed for export] *)
Lemma layout_small : 4096 <= IMG_LO /\ IMG_LO <= RW_LO /\ RW_LO <= LOCKA /\ LOCKA + 940 <= IMG_HI /\ IMG_HI <= 2^32 /\
  2^33 <= alloc_ceiling <= 2^47.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "h04__p1h14__p2h24__x1h34__p3h44__p4h54__p5h67__arithh74__ffh86__sat0h96__sat1h:8__varmaph;5__with<2Hah=4__p6h>4__x2h?4__p7h@4__p8hA6__sat2hB6__sat3hC1Hp;1p;2p;3p;4p;6p;7p;8g007Vj11Tg00;:j1ETg00=Ij1XTg00<_j2FTg00d@j3=Tg008;j14Tg00>Qj29Tg00Jdj15Tg00AHj1TTg00;Xj1QTg003cj1eTg0062j20Tg004kj1]Tg006Nj1[Tg008Yj2KTg00SDj1YTg009Vj22Tg00ekj2HTg00X\j2CTg00fSj3GTg00]^j1VTg00^>j1UTg00n8j2NTg00_<j1STg00_Zj1RTg00aJj2MTg00`hj1PTg00bXj2hTg00c:j2gTg00cTj2fTg00dZj3dTg00e9j4cTg00^^j1bTg00nVj4^Tg010_j3OTg00j\j3JTg00k?j4?Tg011fj6\Tg00`Ej2_Tg00amj4`Tg00o4j7aTg012Jj7ITg011Bj8ZTf0R0#5#5p=W%10#1p=Bf4R1f3R2f2R3f1R4/20'2'2'2p=A%10#1#1#1p=L%50#5#5#5p=8%10#1#1#1#1#1#1#1p=D1240,23p=>g013WR5/00p=;P4g015kR6g016JR7P7g016jR8P0E\p=7g0145R9/_0p=<P3P6P7P7P8P9P4g018QP0C`g0181Fap=6P1P6P7P7P8P2P3P6P7P7P8P4P0FIFIp=3P2P6P7P7P8P3P4P0GZp=:P3P6P7P7P8P4P0FIp=@g01BJg01=fR6g0198R:#1R;#1R<#1R=#1R>#1R?#1R@#ERAp,2MLRB#X'F5=9g01@8%4=,96R=5=9g01A?%W:RC#1#5#1#5RD#1#B#4,965=9g01>oRE%TB,FA5=9%QB,FA==9=DAR=%B@#L#4RA%eBRF'0RG%]BRH,0FRI%4@R@,9H/06RJ%5D#B#4RD,96%[BRB'0RK%4;RL%4?RM'KRN,0BRO%8C#8#8RC#1#8#8#1#B#L#D#D#4RPp,2HT#YRQ'0RR%5C#8#8#1#B#L#D#D#4RC,0QRS'210HE%4<,9E/06'2RE'2R<'2RT'2RU'2RV'2RW3>PG10H6RX%5>R>#4RY,KLRZ/0QR[%8;R\#4R],KLR^,0QR_'2R`,2ORa,2KRb'2Rc,2I1HLMRd1C5LRe%;M1C5N[[Rf%;LRgg01=JRhAGLM4UW<RM%;N\h^<gRip-0Rjg015?Rk#VRl%UkRk1N94Rm%S9Rn%R9RoPo17o2RpPo%<A1M9:R:56oRq17o1RrD3%P7R7PqC:1ho8R8P0P3g01;mRqg01<MRs'g1f03==qsdAd954CcRsb7b:b;X29X0jW110A0=>4310A4[^29^0j^1jP0PWP=PFP2O4b6b8b9PIPcPdPfPMPiPlPkP91N93P4%b9C^RcPnPoPoPrPof5RW,7oRA1M9;R;96o:Rqf6Rt,7oRu5@oD3P7PqC:P8Psb7b:b;X29X>9X0jX1jX3j1004/219>321043Rv[^29^>9^0j^1j^3jP0PVPGP=PHPFP2O6b6b8b9PXPbPdPfPMPiPlPkPcPnPoPoPrPoPAPoPuPo%<@9O9:=6o;f7Rb,7oRXD3D3P7PqC:P8Psb7b:b;X29X>9X0jX1jX3jX4jP3P2P1190@/04PWDAPv[^29^>9^0j^1j^3j^4jP0PUPIPGP=P6PHP2O7b6b8b9PKPaPdPfPMPiPlPkPcPnPoPoPrPoPAPoPuPoPX%<D9O9:=6o;R;f8Rc,7oRa5@oD3D3P7P;C:P8Psb7b:b;X29X>9X0jX1jX3jX4jX5jP3P2P1PW190D/04/2tDA194D/03[^29^>9^0j^1j^3j^4j^5jP0PTPJPIPGP=PBP6P2O8b6b8b9POP`PdPfPMPiPlPkPmPnPoPoPpPoPrPoPAPoPuPoPXPo%<LR`%E?5J996o:R?PaD3D3D3P7P?C:P8Psb7b:b;X29X0jX1jX3jX4jX5jX=jP4P3P2P1100N=>WtDA104N[^29^0j^1j^3j^4j^5j^=jP0P<PKPJPIPGP=PBP2O8b6b8b9P[P_1HLY%;Y1C5Z[\eAGLY4VhX<g%;Z\h^<gPdPfPMPiPlPkPmPnPoPoPpPoPrPoPAPoPuPoPXPoPa%<P=6o:f9,7oRY5@of:,7oR_5@oD3D3D3P7%E>9J9`=6o:C:P8Psb7b:b;X29X0jX1jX3jX4jX5jX=jX?jX@jP4P3P2P110P0/2b/2c9>WtDA10Z4[^29^0j^1j^3j^4j^5j^=j^?j^@jP0PEPSPOPKPJPIPGP=PQPWO:b6b8b9bAbB1HL]%;]1C5^[\eAGL]4VhX<g%;^\h^<gPdPfPMPiPlPkPmPnPoPoPpPoPrPoPAPoPuPoPXPoPa%<C96o:9@oY=@o_D3D3D3P7%E\9J9`96o:C:P8Psb7b:b;X29X0jX1jX3jX4jX5jX=jX?jX@jP4P3P2P1100C,2b/2c9>WtDA104^[^29^0j^1j^3j^4j^5j^=j^?j^@jP0PEPRPOPKPJPIPGP=PQPWO:b6b8b9bAbBC?C?C?C?C?C?bCo"). Qed.

(* [comment removed for export] *)
Lemma layout_aligns :
  IMG_LO mod 4096 = 0 /\ RW_LO mod 4096 = 0 /\ IMG_HI mod 4096 = 0 /\ CTX mod 8 = 0 /\ LOCKA mod 8 = 0 /\ ERRNO mod 4 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "p'0h04__p1h14__x1h24__x2h32H0h44__p2h51Hh62H1h73H10h83H11h93H12h:3H13h;3H14h<3H15h=3H16h>3H17h?3H18h@3H19hA2H2hB3H20hC3H21hD3H22hE3H23hF3H24hG2H3hH2H4hI2H5hJ2H6hK2H7hL2H8hM2H9hN7__arithhO1qhP2q0hQ2q1hR2q2hS2q3hT1rhU2r0hV2r1hW2r2hX2r3hY3H25hZ3H26h[3H27h\3H28h]3H29h^3H30h_3H31h`3H32ha3H33hb3H34hc4__ffhd7__sat10he7__sat11hf7__sat12hg7__sat13hh7__sat14hi7__sat15hj7__sat16hk7__sat17hl7__sat18hm6__sat9hn8__varmapho5__withp2q4hq2q5hr2r4hs2r5ht3H35hu3H36hv3H37hw3H38hx4__p3hy4__p4hz2q6h{2r6h|4__p5h}4__p6h~4__x3i004__x4i014__x5i024__x6i034__x7i042Hai055__x10i065__x11i075__x12i084__x8i094__x9i0:1zi0;3HC8i0<3HE4i0=3HL8i0>2Hci0?2Hei0@2Hhi0A2Hti0B6__sat0i0C6__sat1i0D6__sat2i0E6__sat3i0F6__sat4i0G6__sat5i0H6__sat6i0I6__sat7p%0p%1p&0p;2p;1p;3p;4p;6p;7p;8g002Yk20OTg003ck10NTg004kj1}Tg0062j2VTg006Nk10HTg007Vj13Tg008;j1HTg008Yk207Tg0096j27Tg00:1k20MTg00;:k10LTg00;Xk10KTg00<_j2eTg00=Ik10ETg00>Qj2aTg00O?k20<Tg00PNk20;Tg00AHk109Tg00Cbk108Tg00Jdj1@Tg00QYj2WTg00R6k206Tg00TUj2tTg00U<j2BTg00UYj2MTg00ekj2|Tg00fSj3{Tg00VJj2pTg00W;j2LTg00W\j1gTg00X5j2JTg00Y8j2NTg00X\j2=Tg00Y_j2FTg00ZEj2CTg00[jj1ETg00\Ij2xTg00llj2fTg00Zkk10GTg00[Ik20FTg00]^k10DTg00mXj3bTg00^>k10CTg00^^k10?Tg00_<k10>Tg00_Zk10=Tg00`Ej2wTg00`hk10:Tg00aJj2uTg00g7j3jTg00bXk205Tg00c:k204Tg00cTk203Tg00d@j3YTg00dZk302Tg00e9k401Tg00gZj2<Tg00h7j2sTg00hWj2rTg00i9j6kTg00iWj6nTg00j3k200Tg012nj3~Tg00]2j2qTg009Vj22Tg00k?j4]Tg00lCj3lTg00kZk30@Tg00n8k20ATg00nVk40BTg00amj4cTg00o4j7mTg00oXj6zTg010<j3yTg010_k30ITg011fk60JTg012Jj7oTg011Bj8XTg013WR0f0R1'=p=>g0145R2?Y10p=0f2R3f1R4/21'2p=df4R5f3R61241,23'2'2p=?AY241p=51<34/a19Y26p=91V01p=11=41,23p=I1=341V10'2p=O1x21p=UAl2419l23p=DB0@241p=T20A21p=;P2P3P4P1H0Bp=41w21p=RP3g015kR7g016JR8P8g016jR9P2P4g017JR:P1Ccg0181R;Fmp=8P4P7P8P8P9P1Ezp=v1u21p=6Ay241p=GB0I241p=QP2P4P:P1Ccp=[P2P4g01;FP1Ccp=ZP4P7P8P8P9P1P;Fmp=KP2P4g018QP1Ccp=\P4P7P8P8P9P1J0Jp=SP5P7P8P8P9P6P3P7P8P8P9P4P1FoFop=:P6P7P8P8P9P3P4P1GXp=iP5P7P8P8P9P6P7P8P8P9P3P;FmP4P1GXp=Pf6R;P7P8P8P9f5R:P7P8P8P9P5P6P3GXP4P1GXp=A1a419Y23p=^Al241p=_P3P7P8P8P9P4P1Fop=`P;P7P8P8P9P:P5P6P7P8P8P9P3P4P1GXGXp=hp,2MLR7p,4MLokR<+0O&0N7R=#>%}7R>,V=S00&0H7R?,V>S01g0198R@#3RA#HRB%3AS02#3RC#3#3RD#HRE+07RF,V?S03%3DRD#3#3#3#3#3#3#HRG,7=RH#0S0417>GRI#0S0517?GRJ#0S063dD?20M7<&0LDRD&0K7'eRK&0E7,eDRL%HCRM'aRN'520<7<17KMRO#020;7<&097,eDRP&087,eDRD%@ARQ#3S07#3S08#@S09#3#3#HS0:'WS0;'52067<17DMR<#0P2Q0;Q02#HR7,71#0Z0:2S0<1tDMPDPM1BDMRRP<C9RS1M?GS0=%1?%1GS0>%1JRT[[S0?1|BES0@%>B%1E%>F[[S0A%1BRUg01=JRVA{BE4UY04S0B%1F\V`04US0C1MKMS0D%1K%1MRU%1ORV[[S0E1M=GS0F%1=Q0>%1HRF[[S0G1MDMS0H%1DRE%1<RW\U[S0I1pDM%1R\U\E1M>GS0J%1>Q0>%1IRE[[S0K1LDMS0L%0MRX#gS0MPS[S0N1JDMS0O%>MRSAIW<M[S0P1NDMS0Q1=M0S0RAOM<<[S0S1FDMS0T%0R\XS0U1CDMS0V15<D\XS0WPRP2P<P21L>GS0X%0GRW#gRYP>PG1B>GRZPIC9[S0Y1J>GS0Z%>GS0[AIEIG[S0\1N>GS0]1=G0REAOGII[S0^1F>GS0_%0Z\WS0`1C>GS0a15I>\WS0bPZP2PIP21L=GS0cP=PG1B=GR[PHC9\YS0d1J=GS0eQ0[AIFHG[S0f1N=GS0gAOGHH\ERF1F=GR\%0[\WR]1C=GR^15H=\WR_P[P2PHP21LKMR`Q0MPKPM1BKMRaPOC9[Rb1JKMRcAIVOM\SRV1NKMRdQ0RAOMOO[Re1FKMRf%0a\XRg1CKMRh15OK\XRiPaP2POP21L?GRjP?PG1B?GRkPJC9\YRY1J?GRlQ0[AITJG[RT1N?GRmAOGJJ\ERE1F?GRn%0k\WRo1C?GRp15J?\WRqPkP2PJP2p-0Rrg015?Rsg01:gRt#E#ES0h#ES0i#ES0j#ES0k#ES0l#ERu#E#URv%UuS0m1x2tRt3Dg014SS0n'f&0G@-0F2Ru/TvQ0m,TuS0o;DtQ0n'f&0DsRv5bs3b&0CsS0pf8Rw#;&0?2Rx745f:S0q#;94x;743f<Ry#;?4yxf9Rz#;74:f7R{f;S0r#;54x746744&0>2S0s&0=2R|P|%RGR}1w20R~58|,v|S0t&0:8R8%6QS0u%@C#6,G}%6CS0v'Q58|P8P|P|Q0tP8%@@RC#6S0w%@CRQ#@#6S0x,G}%3CS0y#6S0z'Q58|P8P|P|Q0tP8Q02#6S0t%3Q#6,G}%6QS0{'Q58|P8P|P|%RMRQ=8|~,v|S0|P8%6ARA1u2@RC,GQS0}Q0y#@#6S0y'Q58|P8P|P|Q0y/[~P8P|P|Q0w,Z~,K|S0yP|Q0wQ0t'\,K|P|Q0tQ0u'\,K|P|f>S0t,S|P|Q0z=8|~P|Q0{=8|~Q0v=8|~D:D:D:P8%R7S0v%RB/GCQ09#HS09#R5j2'GQ0:#R9j2A58|CiDPFAFAFAFA205|9S0{P1P3g01;mS0zg01<MR9+04Q0z20313;Y9dB02204H01S0zbcbnboX12X22X~2Z002Z012Z022Z032Z082Z092Z052Z062Z072W0g01<mS0u\WRW1<GyR9=^:w[A^59{\WA^;9z\WQ0u\XS0uP:PMP5PyC9[%0yRW%>{S0w1V{w1VwzfAQ0q#0Q0r#0;dWD?1<B;Q09'W,<7Q0:,W{'5[[[[[[^12^22^~2`002`012`022`032`082`092`052`062`072^0rP1Q03P3f@fGfMP4fFS0:f?S0rP?P>P=PDfNP{fEfLfSf]faOCbNbXbSbFbEbDbCbBbWbRb@b?b>b=b<bVbQb;b:b9b8b7bUbPbMbLbKbJbIbTbObHbGbAb6b3c0Bc0Cc0Dc0Ec0Fc0Gc0Hc0I1<BRQ09'WRB,<7RDQ0;'5P2PDQ0<P21<B7Q0<1sB7PD1r7BEkQ0;P1Enb3b5PPP4Ek17P7RB#0S0;P2PK171M#0Z0:2S0<P6PNP5En17NMRD#0S091tNMPNPM1BNMR>PDC9S0qQ0=Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0HQ0IQ0FQ0G1MNMS0~%1NR?%1DRW\U[S101MP7S11%1P%17%1BR9[[S121pNM%1>\U\?Q0JQ0K1LNMS13Q0MQ0q[S0q1JNMS14AIWDM\SS151NNMS16Q0RAOMDD[S171FNMS18%0>\XS191CNMS1:15DN\XS1;P>P2PDP2Q0XQ0YQ0ZQ0\Q0]Q0^Q0_Q0`Q0aQ0bPZP2PIP21LP7S1<%07S1=#gPPP71BP7RNPBC9[S1>1JP7S1?%>7S1@AI9B7[S1A1NP7S1B1=70AO7BB[R01FP7R9Q1=%0N[RW1CP7R?Q1=15BP[RPPNP2PBP2Q0cQ0dQ0eQ0fQ0gPFP\P]P^P_P[P2PHP2Q0LQ0NQ0OQ0PQ0QQ0SQ0TQ0UQ0VQ0WPRP2P<P2P`PbPcPVPdPePfPgPhPiPaP2POP2PjPYPlPTPmPEPnPoPpPqPkP2PJP2Q0l#US0lQ0i#US0iQ0h#US0h,Tu/_t3D2002M=~2tS1=Q0oQ0lQ0k#US0kQ0j#US0j,TuQ0i'_3D3DQ0n'f'qQ0l,TuS0lQ0i,TuS0iQ0h/_t3DQ1=Q0mQ0lQ0k,TuQ0jQ0i'_3D3DQ0n'f'q=bsv5bsQ0p%;{?4{x94x{%;:?4{x743%;5?4{x%;;94x{746744Q0sP|P|Q0|P8Q02#@#6RsQ08#6,GQQ07#6Ru'Q58|P8P|P|1QAQRtQ0}Q0x'Q'[P8P|P|Q0x/[~P8P|P|1[u~P8P|P|1[stP8P|Q0y1S|zS0x5`|P8%H@R@#R9j2C,GQ=8|ACiDPDPDPDPFAQ0{Q0zbcbnboX12X22X~2Z002Z012Z022Z032X0rQ0uP5PMP{P:C9[1a3MPMP4P;C9%0{RtA^{:MQ0w/2y1W;@,<M/5{[[\t[[[^12^22^~2`002`012`022`032^0rP1Q00Q01Q03Q0:#0S0:fT#0%04Rt'2D?Pzf[S0wPwPKP=PLf\Q0tflfmS0tfqfrfsS0uO>bNbsbqbbbab`b_b^brbpb]b\b[bZbYbXbSbFbEbDbCbBbWbRb@b?b>b=b<bVbQb;b:b9b8b7bUbPbMbLbKbJbIbTbObHbGbAb6b3bmbdbebfbgbhbibjbkbl1W>@R@,<MRK/5LP2PKQ0<P21<@MQ0<1s@MPK1rM@EkPLP1Enb3b517LMR@#0S0<Q04Q05Q06Q09Q0<Q0;'2S0y'2S0}'2S07'2Q0=Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0HQ0IQ0FQ0GQ0~Q10Q11Q121MLMS08%1L%1@RK\U[S02Q0JQ0KQ0cQ0dQ0eQ0fQ0gPFP\P]P^P_P[P2PHP2Q0XQ0YQ0ZQ0\Q0]Q0^Q0_Q0`Q0aQ0bPZP2PIP21LLMS0|Q0MPLPM1BLMRUP@C9[S0M1JLMS0nAIK@M\SS1=1NLMRKQ0RAOM@@[Rz1FLMRy%0U\XRs1CLMRu15@L\XRXPUP2P@P2Q1<Q1>Q1?Q1AQ1BP0P9PWP?PPPNP2PBP2Q13Q0qQ14Q15Q16Q17Q18Q19Q1:Q1;P>P2PDP2Q0LQ0NQ0OQ0PQ0QQ0SQ0TQ0UQ0VQ0WPRP2P<P2P`PbPcPVPdPePfPgPhPiPaP2POP2PjPYPlPTPmPEPnPoPpPqPkP2PJP2PvQ0p%;3?44xRxQ0sP|P|1\~A,K|P8P|P|1\~}P81\~C,K|S0RDPP8P|P|1Z~A,K|RAP|1S|5S0mP|1S|:RLP|1S|;S0lA8|C~RC1S|{S0i5`|D:D:P8PCCiFAQ0{Q0zbcbnboX12X22X0rX4rXxrXyr%14S0jQ0>%13[[%>3S0>P6P5P:12t;D?%03S0k[[^12^22^0r^4r^xr^yrP1Q0w#0S0w/2tS0hQ03Q01Q00P=fbR3Q0tfzR4O8bNb{bzbwbvbubtbbbsbqbab`b_b^b]brbpb\b[bZbYbFbXbSbEbDbCbBb@bWbRb?b>b=b<b;bVbQb:b9b8b7bMbUbPbLbKbJbIbHbTbObGbAb6b3b5bmbdbebfbgbhbibjbkblQ05Q07Q0=Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0HQ0IQ0FQ0GQ0~Q10Q11Q12Q08Q02Q0JQ0KQ0XQ0YQ0ZQ0\Q0]Q0^Q0_Q0`Q0aQ0bPZP2PIP2Q0|Q0MQ0nQ1=PKPzPyPsPuPXPUP2P@P2Q1<Q1>Q1?Q1AQ1BP0P9PWP?PPPNP2PBP2Q13Q0qQ14Q15Q16Q17Q18Q19Q1:Q1;P>P2PDP2Q0cQ0dQ0eQ0fQ0gPFP\P]P^P_P[P2PHP2Q0LQ0NQ0OQ0PQ0QQ0SQ0TQ0UQ0VQ0WPRP2P<P2P`PbPcPVPdPePfPgPhPiPaP2POP2PjPYPlPTPmPEPnPoPpPqPkP2PJP2PvQ0pPxQ0sP|P|P|1Z~}P8Q0RQ0m5`|S0mDPS0RP8P|P|PAP|PLP|Q0lP|Q0iP|1S|wS07P|PCQ0xD:D:D:P8PCFhQ0{Q0zbcbnboX12X22X0rX4rXxrXyrX|rX}rQ0[Q0j/26S0j[R}Q0>P5P:P;Ad{twD?Q0k[[^12^22^0r^4r^xr^yr^|r^}rP1PtQ0:Q03Q01Q001=3GS0[P=P3fgRGP4O:bNb{bzbwbvbubtbbbsbqbab`b_b^b]brbpb\b[bZbYbFbXbSbEbDbCbBb@bWbRb?b>b=b<b;bVbQb:b9b8b7bMbUbPbLbKbJbIbHbTbObGbAb6b3b5bmbdbebfbgbhbibjbkblQ06Q0}Q0=Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0HQ0IQ0FQ0GQ0~Q10Q11Q12Q08Q02Q0JQ0KPjPYPlPTPmPEPnPoPpPqPkP2PJP2Q0XQ0YQ0ZQ0\Q0]Q0^Q0_Q0`Q0aQ0bPZP2PIP2Q0|Q0MQ0nQ1=PKPzPyPsPuPXPUP2P@P2Q1<Q1>Q1?Q1AQ1BP0P9PWP?PPPNP2PBP2Q13Q0qQ14Q15Q16Q17Q18Q19Q1:Q1;P>P2PDP2Q0cQ0dQ0eQ0fQ0gPFP\P]P^P_P[P2PHP2Q0LQ0NQ0OQ0PQ0QQ0SQ0TQ0UQ0VQ0WPRP2P<P2P`PbPcPVPdPePfPgPhPiPaP2POP2PvQ0pPxQ0sP|Q0RP8P|P|PAP|PLP|Q0lP|Q0iP|Q07P|Q0xPCD:D:D:P8PCFhQ0{Q0zbcbnboX12X22X0rX4rXxrXyrX|rX}rQ0>P5P:P;Ad{wtD?Q0k[\}^12^22^0r^4r^xr^yr^|r^}rP1Q0wQ0r#0Q03Q01Q00Q0[P=P3PGP4O:bNb{bzbwbvbubtbbbsbqbab`b_b^b]brbpb\b[bZbYbFbXbSbEbDbCbBb@bWbRb?b>b=b<b;bVbQb:b9b8b7bMbUbPbLbKbJbIbHbTbObGbAb6b3b5bmbdbebfbgbhbibjbkblQ09Q0yQ0=Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0HQ0IQ0FQ0GQ0~Q10Q11Q12Q08Q02Q0JQ0KQ13Q0qQ14Q15Q16Q17Q18Q19Q1:Q1;P>P2PDP2Q0XQ0YQ0ZQ0\Q0]Q0^Q0_Q0`Q0aQ0bPZP2PIP2Q0|Q0MQ0nQ1=PKPzPyPsPuPXPUP2P@P2Q1<Q1>Q1?Q1AQ1BP0P9PWP?PPPNP2PBP2Q0cQ0dQ0eQ0fQ0gPFP\P]P^P_P[P2PHP2Q0LQ0NQ0OQ0PQ0QQ0SQ0TQ0UQ0VQ0WPRP2P<P2P`PbPcPVPdPePfPgPhPiPaP2POP2PjPYPlPTPmPEPnPoPpPqPkP2PJP2PvQ0pPxQ0sP|P|1Z~Q,K|P8Q0mP8P|PCP8P|A`|ALP8PCFhRCFAQ0{Q0zbcbnboX12X22X0rX4rRLQ0j\S%>6/2:%06[\tRt[^12^22^0r^4rR6P1Q00Q01Q03Q0:Q0hD?R:1=3MRSP=P3PGftP4O7bNb{bzbwbvbubtbbbsbqbab`b_b^b]brbpb\b[bZbYbFbXbSbEbDbCbBb@bWbRb?b>b=b<b;bVbQb:b9b8b7bMbUbPbLbKbJbIbHbTbObGbAb6b3b5bmbdbebfbgbhbibjbkblQ0<Q0;Q0=Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0HQ0IQ0FQ0GQ0~Q10Q11Q12Q08Q02Q0JQ0KQ0|Q0MQ0nQ1=PKPzPyPsPuPXPUP2P@P2Q0XQ0YQ0ZQ0\Q0]Q0^Q0_Q0`Q0aQ0bPZP2PIP2Q1<Q1>Q1?Q1AQ1BP0P9PWP?PPPNP2PBP2Q13Q0qQ14Q15Q16Q17Q18Q19Q1:Q1;P>P2PDP2Q0cQ0dQ0eQ0fQ0gPFP\P]P^P_P[P2PHP2Q0LQ0NQ0OQ0PQ0QQ0SQ0TQ0UQ0VQ0WPRP2P<P2P`PbPcPVPdPePfPgPhPiPaP2POP2PjPYPlPTPmPEPnPoPpPqPkP2PJP2PLP6P1P:PSP=P3PGQ0uP4O7bNb{bzbwbvbubtbbbsbqbab`b_b^b]brbpb\b[bZbYbFbXbSbEbDbCbBb@bWbRb?b>b=b<b;bVbQb:b9b8b7bMbUbPbLbKbJbIbHbTbObGbAb6b3b5bmbdbebfbgbhbibjbkblQ0=Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0HQ0IQ0FQ0GQ0~Q10Q11Q12Q08Q02Q0JQ0KQ1<Q1>Q1?Q1AQ1BP0P9PWP?PPPNP2PBP2Q0XQ0YQ0ZQ0\Q0]Q0^Q0_Q0`Q0aQ0bPZP2PIP2Q0|Q0MQ0nQ1=PKPzPyPsPuPXPUP2P@P2Q13Q0qQ14Q15Q16Q17Q18Q19Q1:Q1;P>P2PDP2Q0cQ0dQ0eQ0fQ0gPFP\P]P^P_P[P2PHP2Q0LQ0NQ0OQ0PQ0QQ0SQ0TQ0UQ0VQ0WPRP2P<P2P`PbPcPVPdPePfPgPhPiPaP2POP2PjPYPlPTPmPEPnPoPpPqPkP2PJP2PvQ0pPxQ0sP|P|Q0v,Z~,K|P8Q0mP8PCFAQ0{Q0zbcbnboX12X22X0rX4rQ1@Q0j[Pt[^12^22^0r^4rP1P:1=37P=P3PGfuP4O7bNb{bzbwbvbubtbbbsbqbab`b_b^b]brbpb\b[bZbYbFbXbSbEbDbCbBb@bWbRb?b>b=b<b;bVbQb:b9b8b7bMbUbPbLbKbJbIbHbTbObGbAb6b3b5bmbdbebfbgbhbibjbkblC]C]C]C]C]c0=c0;c0<c0Ac0?c04c0>c0@Q04Q05Q06g01@8/7M#0g01=f/7M#0g01>o/77#0'2D?eo"). Qed.

(* [comment removed for export] *)
Lemma layout_tabs :
  T_SIZE_CLASSES = bv_unsigned A_SIZE_CLASSES /\ T_SMALL_CNT = bv_unsigned A_SMALL_CNT_TAB /\
  T_MED_CNT = bv_unsigned A_MED_CNT_TAB /\ T_DEBRUIJN = bv_unsigned A_DEBRUIJN /\
  4096 <= IMG_LO /\ (IMG_LO <= T_DEBRUIJN /\ T_DEBRUIJN + 32 <= RW_LO) /\ (IMG_LO <= T_SIZE_CLASSES /\ T_SIZE_CLASSES + 96 <= RW_LO) /\
  (IMG_LO <= T_SMALL_CNT /\ T_SMALL_CNT + 27 <= RW_LO) /\ (IMG_LO <= T_MED_CNT /\ T_MED_CNT + 4 <= RW_LO) /\ RW_LO <= IMG_HI /\ IMG_HI <= 2^32.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "h04__p1h14__p2h24__x1h34__x2h44__p3h54__p4h62H2h72H3h82H4h92H5h:2H6h;7__arithh<4__ffh=6__sat2h>6__sat3h?6__sat4h@8__varmaphA5__withB1qhC1rhD4__p5hE4__p6hF2HahG4__x3hH4__x4hI4__x5hJ4__x6hK4__x7hL1HhM2H0hN2H1p%0p&0p;1p;2p;3p;4p;6p;7p;8g007Vj11Tg00;:j1_Tg00=Ij1oTg00<_j2ATg008;j19Tg00>Qj2BTg00Jdj15Tg00AHj1lTg00;Xj1iTg003ck10<Tg0062j20Tg004kk105Tg006Nj1yTg008Yj2wTg00SDj1rTg009Vj22Tg01CYj2kTg01Dhj1jTg01F4j1hTg01GDj1gTg01HUj1fTg01Idj2eTg0096j2dTg00c:j2HTg00UYj2cTg00ekj2bTg00X\j2ITg00fSj3aTg00W;j2`Tg00W\k10;Tg00U<k20:Tg00gZj2^Tg00X5k209Tg00Y8k208Tg00Y_k204Tg00ZEk203Tg00]^k102Tg00^>j1{Tg00_<j1zTg00_Zj1xTg00aJj2YTg00`hj1vTg00bXj2uTg00cTj2tTg00d@j3NTg00dZj3sTg00e9j4qTg00^^j1pTg00k?j4FTg00[jj1WTg00\Ij2RTg00lCj3XTg00llj2nTg00mXj3mTg00`Ej2VTg00oXj6|Tg010<j3}Tg00j\j3~Tg00n8k200Tg011fk601Tg00amj4[Tg00o4j7ZTg012Jj7QTg011Bj8]Tg00nVk406Tg010_k307Tf0R0#1#1p=Jg0145R1f1R2;N0p==f3R3f2R4;N2/20p=?%10#1#1#1p=L1B42/00p=3%50#5#5#5p=C%10#1#1#1#1#1#1#1p=P1042/20p=O1242/20p=>1220,24p=4g013WR59N10p=M1020,24p=\20010p=GP2g015kR6g016JR7P7g016jR8P0J01p=71V10p=@P4P6P7P7P8P1P2g018QP0C[g0181R9FZp=:P4P6P7P7P8P2P0FQp=6f5R:P6P7P7P8f4R;P6P7P7P8P3P4FQP2P0G]p=8P1P4P2P0H06p=;1Y10p=EB07120p=DP;P6P7P7P8P3P4P6P7P7P8P2P0FQFQp=<P1P2g017JP0C[p=SP2P6P7P7P8P0P9FZp=UP3P6P7P7P8P4P2P0G]p=Tf6R9P:P;P3P4P2P0CFCFp=Kg01BJP1g01=fR<g0198R=#1R>#1R?#1R@#1S00#1RA#1RB#_RCp,2MLRD#o'AP1g01@8%9@,B<REP1g01A?%5=RF#5RG#1#5#1#5RH#1#J#9,B<P1g01>oRI%lD,AC%iD,AC/=EC?C?C?C?S01%JB#L#9RE&0<DRJ'0RK&05DRL,0JS02%9BRB=3L<S03%5H#J#9RH%yDRM53<S04%9>RN%9ARO'wRP,0MS05%CG#C#CRG#1#C#C#1#J#L#P#P#9p,2HT#rRQ'0%5G#C#C#1#J#L#P#P#9,0Q%9?R?=3I<9OLI3>S06'2S07'234RI34p,4MLokRQ,kD%jD,ACRG,0JRRA3GOLRS'2RT%hD,ACRU,0JRV%1FRW#L#9RX=3ULS08'2RY%gD,ACRZ,0JS09%5WS0:#5#9RW=3ZLS0;'2R[%fD,ACRC,0JS0<A3C?LS0='2R\'2S0>'2R]'21eDQ1dUNRQ#M1=UU1=ZZRD1=CCR^1=GGR_10LMS0?Q05'2S0@,2\S0A,2[S0B,2YR`,2TRa,2KRb'2Rc'2Rd'21H1UPDPd1H1ZP^Pc1H1CP_Pb1H1GPKPa1cUNRa105U105NRb105QR_[[Rc1bNOR^1I5NRd105O1I5P[[RDg01=JReAaNO2UXFbRf105P\e^FbRb1`UNRe%MNRg$0;20:UNRh,^N/BQ,=U[Ri209UNRj1IQN,2_\dRd208UNR_1IN51INQ?\Q5[Rk204UNRl%Mh\gRm203UNRn1=QU\gRoPhP1PQP1p-0Rpg015?Rq$02Rr%{qRs%G2S0C%z1Rt%x1RuPu17u3S0D%@ES0E1Y1=R=5:uRv17u;Rw56u%v7RxPvE81uu8RvP0P4g01;mRyg01<MRz'H1t04=NyzdAs152CqRzb<b@bAX21X0pW110E0=42410E2[^21^0p^1pP0PIQ01PJf=RIO4b;bCbBb:b9b8b7b6b=b>b?PTP`PRPSPaPcP^PDPfPbPePiPjPdP_PkPlPmPnPoPhP1PQP1PrPs%G4%p1R`7;2RyPtPuPu%E>R{9:u=R|=6uw17u:R}PxP|E8PvPzb<b@bAX21X31X0pX1p1002R~?>431024S0F[^21^31^0p^1pP0P]PSPGPJf<RSO5b;bCbBb:b9b8b7b6b=b>b?PaPcP^PDPfPbPePiPjPdP_PkPlPmPnPoPhP1PQP1PrPsPyPtPuPu%@O,D==:u{S0G96uwP}PxQ0GE8PvPzb<b@bAX21X31X0pX1pA30O2=>43A32O4[^21^31^0p^1pP0P]PRPLPGPSO5b;bCbBb:b9b8b7b6b=b>b?CFPYQ0BPVQ08PaPcP^PDPfPbPePiPjPdP_PkPlPmPnPoPhP1PQP1PrPsPyPtPuPuPwA6u|}17u9RR56uPxP|E8PvPzb<b@bAX21X31X0pX1pX4p12~3=44;Q0F[^21^31^0p^1p^4pP0Q0>Q08PTPUPJPSO6b;bCbBb:b9b8b7b6b=b>b?PaPcP^PDPfPbPePiPjPdP_PkPlPmPnPoPhP1PQP1PrPsPyPtPuPuPw%@X,D==:u{R]96u}=6uRPxP]E8PvPzb<b@bAX21X31X0pX1pX4p1B0X=\32=44;A32X4[^21^31^0p^1p^4pP0Q0>PVPTPLPUPSO6b;bCbBb:b9b8b7b6b=b>b?CFP[Q0AQ09Q0;PaPcP^PDPfPbPePiPjPdP_PkPlPmPnPoPhP1PQP1PrPsPyPtPuPuPwPuP}PuA6u|Rf7RV,7uR]D<PxP|E8PvPzb<b@bAX21X31X0pX1pX4pX5pA>~;:9443Q0F[^21^31^0p^1p^4p^5pP0P\Q0;PYPTPZPJPSO7b;bCbBb:b9b8b7b6b=b>b?PaPcP^PDPfPbPePiPjPdP_PkPlPmPnPoPhP1PQP1PrPsPyPtPuPuPwPuP}Pu%@W,D==:u{S0;96uRP]D<PxQ0;E8PvPzb<b@bAX21X31X0pX1pX4pX5pA30W2=>;:9443A32W4[^21^31^0p^1p^4p^5pP0P\Q09PYPTPLPZPSO7b;bCbBb:b9b8b7b6b=b>b?CFP\Q0@Q0<Q0=PaPcP^PDPfPbPePiPjPdP_PkPlPmPnPoPhP1PQP1PrPsPyPtPuPuPwPuP}PuPRA6u|]D<PxP|E8PvPzb<b@bAX21X31X0pX1pX4pX5pA4;~:9443Q0F[^21^31^0p^1p^4p^5pP0Q0=P[PYPTPCPJPSO7b;bCbBb:b9b8b7b6b=b>b?PaPcP^PDPfPbPePiPjPdP_PkPlPmPnPoPhP1PQP1PrPsPyPtPuPuPwPuP}PuPR%@?,D==:u{Ry96u]D<PxPyE8PvPzb<b@bAX21X31X0pX1pX4pX5pA30?294;:9443A32?4[^21^31^0p^1p^4p^5pP0Q0<P[PYPTPLPCPSO7b;bCbBb:b9b8b7b6b=b>b?CFQ0?Q05PaPcP^PDPfPbPePiPjPdP_PkPlPmPnPoPhP1PQP1g01:gRY#WR[#W,R11R1[1R1Y5X15X1g014S'n=mqrPs%G9?;V`?;V`%G;?;V`7;4%GV?;V`%G:7;V?;3`7;2PtPuPuPuP6P7P7P8%@NR81V15R5'S,UuE|PxQ0:#ER7%5@#E9}18Q00#ER@'D'S,UuCTPxPu1S@5,UuPxPuPuf9R@,7u%5>#1#ER>=:u7f:R7,7u56uf;R5,7u56uPxPuPu17uSPuQ0E=:u>Pu17uIPu%@B,D=%EFRF5:uPu%@H,DF=:u{f>R{,7uD<D<PxP|E8E8CTCTPvPzb<b@bAX21X31XG1XH1XI1XJ1XK1X0pX1pX4pX5pXDpXEpg01<m\g1^NV/B9,=:[%M9AO:97=4@510E9A33B:1B:Hf?7O;54{54I10;:[[[[^21^31^G1^H1^I1^J1^K1^0p^1p^4p^5p^Dp^EpP0Q07Q02Q01Q0>Q08PTP4P2PUPJP<PMPLPVP5PSPIOAb;bCbBb:b9b8b7b6b=b>b?PaPcP^PDPfPbPePiPjPdP_PkPlPmPnPoPhP1PQP1PrPsQ0CPtPuPuQ0DPuPwPuP}PuPRPuP]%_A9~189:u=R=f8,7u56uD<D<PxP=E8PvPzb<b@bAX21X0pX1pX4pX5pXDpXEp100P=4:9943;9424102P[^21^0p^1p^4p^5p^Dp^EpP0Q06Q04Q03Q02PKQ01PMPIO8b;bCbBb:b9b8b7b6b=b>b?FKFKFKFKFKbNbMP1g01K<RIPUP1g01LNRUPZP1g01M]RZPCP1g01NjR1PGA31OL9OJ110JIA3IXL10JUA3UWL10JZA3Z?LQ0@3>3>3>54KC?C?C?C?ebLo"). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition byte_of (v : Z) (k : Z) : Z := (v / 2 ^ (8 * k)) mod 256.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive slot_st := SIdle | STaken | SLive (off n : Z) | SNested (child : Z).

Inductive mrole :=
| RFree                        (* [comment removed for export] *)
| RAvail                       (* [comment removed for export] *)
| RDead                        (* [comment removed for export] *)
| RGroup (aib : Z) (slots : list slot_st).   (* [comment removed for export] *)

(* [comment removed for export] *)
Inductive mfield := FPrev | FNext | FMem | FAvail | FFreed | FW32.

Definition mfield_eq_dec : forall a b : mfield, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition moff (fl : mfield) : Z :=
  match fl with FPrev => 0 | FNext => 8 | FMem => 16 | FAvail => 24 | FFreed => 28 | FW32 => 32 end.
Definition mlen (fl : mfield) : Z :=
  match fl with FAvail | FFreed => 4 | _ => 8 end.

(* [comment removed for export] *)
Record meta_rec := MTR { mr_prev : Z; mr_next : Z; mr_mem : Z; mr_avail : Z; mr_freed : Z; mr_w32 : Z;
                         mt_role : mrole }.
Definition mt_f (mt : meta_rec) (fl : mfield) : Z :=
  match fl with
  | FPrev => mr_prev mt | FNext => mr_next mt | FMem => mr_mem mt
  | FAvail => mr_avail mt | FFreed => mr_freed mt | FW32 => mr_w32 mt
  end.
Definition MT (f : mfield -> Z) (r : mrole) : meta_rec :=
  MTR (f FPrev) (f FNext) (f FMem) (f FAvail) (f FFreed) (f FW32) r.
(* [comment removed for export] *)
Global Arguments mt_f : simpl never.

Lemma mt_f_MT : forall f r fl, mt_f (MT f r) fl = f fl.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "p'0h01fh12fli002flh21ri011mp;7p;1p;3p;2g01P8j7;Tg01QFj1:Tg01RQj13Tg01S\j12Tg01Tfj19Tg01V2j15Tg01W>j14Tg00d@j31Tg01XHj26Tg01YNj27Tg00c:j28Tg0145R0f0R1'8p=0g01ZVR2P0[g01[bP2P2P0P1f3R3g01\mR4O1P3g01^9R5O1P3g01_ER6O1P3g01`QR7O1P3g01a]R8O1P3g01biR9O1f2R:F;R;#:%3;%2;%9;%5;%4;n011000006000000000000P3P1O1510P1P:P4O1#0P:P5O1#0P:P6O1#0P:P7O1#0P:P8O1#0P:P9O1#0n011010006000000000000f1,6:/71P:P1O1510eX12W2W0o"). Qed.
Lemma mt_role_MT : forall f r, mt_role (MT f r) = r.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "h01fh11rp;2g00c:j20Tg01ZVg0145[g01[bR0f0,00W1W0o"). Qed.
Lemma meta_ext : forall mt mt', mt_role mt = mt_role mt' -> (forall fl, mt_f mt fl = mt_f mt' fl) -> mt = mt'.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "p'0h02flh12Hfh21ah32frh41mi001mh53mt'h61nh71ph82r'h91wh:2E1h;2E2h<2E3h=2E4h>2E5h?2E6h@2HrhA2a'hB3fr'hC2m'hD2mthE2n'hF2p'hG1rhH2w'i018mr_availi028mr_freedi036mr_memi047mr_nexti057mr_previ066mr_w32i077mt_rolep;1p;3p;2p;7g01d5j17Tg00d@j36Tg01YNj22Tg01P8j70Tg00c:j2:Tg00iWj78Tg00i9j79Tg0145R0f2R1f1R2'2f0R336p=1g01e@R4?623p=3f7R5f6R6f5R7f4R8f3R9P1P2F0/23p=5A6023p=;P0P7P8P9P1P2P3F9p=4P4g01[bR:%72%73R;36g01ZVR<1213R=9193]01391[[^54P3P4f8R>P5P6P7P8P9P1F0R?#7=6:;f:R;f9R@P>P5P6P7P8F0RA?13=^0<13A1[[P3fERAfDR=fCRBfBRCfARDf@REf?RFF0#7P6P7P8P9P1P2P3F0#756:fGRGfFRHPAP=PBPCPDF012?3713^0<P:PDfIR?fHRIPGPHPAP=PBF0RJP;P@P>P5P6P7P2F0RK/23713^0<13JK]1X8:PIPGPHPAP=PBPCF0RKP@P>P5P6P7P8PCF0RL/23713^0<P3g01\mRMO112LM91KMP2g01^9RMO1P;P@P>P5P6P7PBPMG591JMP1g01_ERMO1fJRJP?PIPGPHPAP=F0f;RKP;P@P>P5P6P=PMG571MP9g01`QRMO1fKRLPJP?PIPGPHPAF0f<RNPKP;P@P>P5PAPMG571MP8g01a]RMO1fLR5PLPJP?PIPGPHF0f=ROPNPKP;P@P>PHPMG571MP7g01biRMO1fMR>P5PLPJP?PIPGF0f>RIPOPNPKP;P@PGPMG571MPFP2fORMfNRGP>P5PLPJF0R@PDPEPFPIPOPNPJF0R;/23RP713^0<13@;]1X70PEPGP>P5PLPJP?F0PEPFPIPOPNPKP?P3G5713^0<PFPCP2PMPGP>P5PLF0R?PCPDPEPFPIPOPLF0RO/23RK713^0<13?O]1X60PDPEPGP>P5PLPJF0?13P^0<PFPBPCP2PMPGP>P5F0RPPBPCPDPEPFPIP5F0RI/23RJ713^0<13PI]1X40PCPDPEPGP>P5PLF0?13K^0<PFP=PBPCP2PMPGP>F0RKP=PBPCPDPEPFP>F0RL/23RI713^0<13KL]1X20PBPCPDPEPGP>P5F0?13J^0<PFPAP=PBPCP2PMPGF0RJPAP=PBPCPDPEPGF0R5/23RL713^0<13J5]1X30P=PBPCPDPEPGP>F0?13I^0<PFPHPAP=PBPCP2PMF0RFPHPAP=PBPCPDPMF0RM/23713^0<13FM]1X901;LL^0<1:45W1PGP7P3E4W1PGP7P3E4W1PGP7P3E4W1PGP7P3E4W1PGP7P3E4W1PGP7P6E4b?b>b=b<b;b:W1P1P2P3F8W1W@X8:XH0XB0XA0XC0XE0XF0P6P7P8P9P1P2P3O7n01100000171105104103101102106107X54XG:X90X30X20X40X60X70P6P7P8P9P1P2P3O7n01100000171105104103101102106107XD4o"). Qed.
Lemma MT_eta : forall mt, MT (mt_f mt) (mt_role mt) = mt.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "p'0h01ah12frh21mi001mh32mth41nh51ph61rh71wi018mr_availi028mr_freedi036mr_memi047mr_nexti057mr_previ066mr_w32i077mt_rolep;1p;2p;3p;7g01YNj15Tg01d5j14Tg01XHj20Tg00d@j31Tg01P8j73Tg00c:j22Tg01e@R0P0f0R1#5%41'0=101P1g0145R2g01[bf6R3f5R4f4R5f3R6f2R7f1R8P1F3,20W6X72X12X02X22X42W5P3P4P5P6P7P8P1O7n01100000170105104103101102106107W3o"). Qed.

Definition mt_prev (mt : meta_rec) : Z := mt_f mt FPrev.
Definition mt_next (mt : meta_rec) : Z := mt_f mt FNext.
Definition mt_mem (mt : meta_rec) : Z := mt_f mt FMem.
Definition mt_avail (mt : meta_rec) : Z := mt_f mt FAvail.
Definition mt_freed (mt : meta_rec) : Z := mt_f mt FFreed.
Definition mt_w32 (mt : meta_rec) : Z := mt_f mt FW32.

Definition mupd (mt : meta_rec) (fl : mfield) (v : Z) : meta_rec :=
  MT (fun fl' => if mfield_eq_dec fl' fl then v else mt_f mt fl') (mt_role mt).
Definition mrole_set (mt : meta_rec) (r : mrole) : meta_rec := MT (mt_f mt) r.

(* [comment removed for export] *)
Definition mmap_t := Z -> option meta_rec.
Definition aupd (g : mmap_t) (ma : Z) (mt : meta_rec) : mmap_t :=
  fun x => if Z.eq_dec x ma then Some mt else g x.

(* [comment removed for export] *)
Inductive cslot :=
| KSecret | KInit | KCtr | KFmh | KAm | KAmc | KAac | KShift | KAhead | KAtail | KAareas | KSeq | KBrk
| KActive (i : Z) | KUsage (i : Z) | KUseq (i : Z) | KBounce (i : Z).

Definition cslot_eq_dec : forall k k' : cslot, {k = k'} + {k <> k'}.
Proof. decide equality; apply Z.eq_dec. Defined.

Definition caddr (k : cslot) : Z :=
  match k with
  | KSecret => C_SECRET | KInit => C_INIT | KCtr => C_CTR | KFmh => C_FMH | KAm => C_AM
  | KAmc => C_AMC | KAac => C_AAC | KShift => C_SHIFT | KAhead => C_AHEAD | KAtail => C_ATAIL
  | KAareas => C_AAREAS | KSeq => C_SEQ | KBrk => C_BRK
  | KActive i => C_ACTIVE + 8 * i | KUsage i => C_USAGE + 8 * i
  | KUseq i => C_USEQ + i | KBounce i => C_BOUNCE + i
  end.

(* [comment removed for export] *)
Lemma word_eqZ : forall (w : word) z, bv_unsigned w = z -> w = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "h01zh11Hh21wp;1p;2p;3p;4p;6g007Vj10Tg00;:j18Tg01fNj14Tg00<_j21Tg00d@j33Tg01g1j22Tg01gWj27Tg01hIj45Tg00iWj66Tg0198#0#0#0#0#0#0#8R0#4R1g0145R2f1R3,10f0R4532P2f2R5,10R6f31204531X02P11206P51705C5P3P4E6W1W0W2o"). Qed.

Lemma A_LOCK_eq : A_LOCK = Z_to_bv 64 LOCKA.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "p;1p;2p;3g00=Ij12Tg00c:j21Tg01hej30Tp,2ML#2g01=fR0g0145/1030o"). Qed.
Lemma A_CTX_eq : A_CTX = Z_to_bv 64 (caddr KSecret).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "p;1p;2p;3g00;Xj17Tg01j1j16Tg00:1j22Tg007Vj10Tg00;:j15Tg00<_j23Tg00d@j31Tg01hej34Tp,2MLR0#7R1g01k:#6R2p,4MLok,20g0145R0g0198#0#0#0#0#0#0#5/31R1g01lE31eA1012e34o"). Qed.
Lemma A_INIT_DONE_eq : A_INIT_DONE = Z_to_bv 64 (caddr KInit).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "h04__x1h11zh27__arithh34__ffh48__varmaph55__witp;1p;2p;3p;4p;7p;6g01mQj1LTg01j1j1KTg007Vj10Tg00;:j1;Tg00;Xj1JTg00<_j23Tg008;j15Tg00>Qj21Tg00=Ij1=Tg00d@j32Tg00]^j1:Tg00^>j18Tg00n8j29Tg00_<j1ITg00_Zj1HTg00aJj2FTg00`Ej26Tg010_j34Tg00amj4CTg00o4j7@Tg00bXj2ATg00c:j2BTg00cTj2?Tg00dZj3>Tg00e9j4DTg00:1j2ETg00i9j67Tg01n^j2GTg01hej3<Tp,2MLR0#LR1g01om#KR2g0145R3g0198R4#0#0#0R5#0R6#0#0#;R7%J0'3R8%55R5'1f0R9%=0,37R:%56R6'1R;523X13P311:51195R<=23;X13g015?R;#:%8;f1R;,93%I3%H3R=g015kg016JR>P>g016jR>P31F34R41635R?543=43?g017J16369434CCg0181F@1A=>P9f2R>g01;mR=g01<MR4'B1?9>=2=4dg013W=>3;CDb3b4b5X0311<51196523^03P9P:O1b2P8p,4MLokR8,E0E71371R71G08E7g02189237eA2372e3<o"). Qed.
Lemma A_MMAP_CTR_eq : A_MMAP_CTR = Z_to_bv 64 (caddr KCtr).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "h04__x1h11zh27__arithh34__ffh48__varmaph55__witp;1p;2p;3p;4p;7p;6g022Bj1MTg01j1j1LTg007Vj10Tg00;:j1;Tg00;Xj1KTg00<_j23Tg00Jdj17Tg008;j16Tg00>Qj21Tg00=Ij1<Tg00d@j32Tg00]^j1:Tg00^>j19Tg00n8j2JTg00_<j1GTg00_Zj1ETg00aJj2CTg00`Ej24Tg010_j35Tg00amj4@Tg00o4j7ATg00bXj2BTg00c:j2?Tg00cTj2>Tg00dZj3DTg00e9j4=Tg00:1j2FTg00i9j68Tg023Nj2HTg01hej3ITp,2MLR0#MR1g024\#LR2g0145R3g0198R4#0R5#0#0R6#0#0#0#;R7%K0'3R8%74#0#0#6R9'1f0R:%<0,37R;%75#0#0#6R5'1R<523X13P3%66R6,1;11:9=23<X13g015?R<#:%9<f1R<,J3%G3%E3R=g015kg016JR>P>g016jR>P31C34R414365531439553g017J14359534C@g0181FA1B=>P:f2R>g01;mR=g01<MR4'?1>:>=2=4dg013W=D3<C=b3b4b5X0311:6/1911:5523^03P:P;O1b2P8p,4MLokR8,F0E81371R71H08E8g025g9237eA2372e3Io"). Qed.
Lemma A_FREE_META_HEAD_eq : A_FREE_META_HEAD = Z_to_bv 64 (caddr KFmh).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "h04__x1h11zh27__arithh34__ffh48__varmaph55__witp;1p;2p;3p;4p;7p;6g0270j1MTg01j1j1LTg007Vj10Tg00;:j18Tg00;Xj1KTg00<_j25Tg008;j16Tg00>Qj21Tg00=Ij1<Tg00Jdj1;Tg00d@j32Tg00]^j19Tg00^>j1:Tg00n8j2JTg00_<j1GTg00_Zj1CTg00aJj2@Tg00`Ej24Tg010_j33Tg00amj4?Tg00o4j7ATg00bXj2BTg00c:j2>Tg00cTj2=Tg00dZj3DTg00e9j4ETg00:1j2FTg00i9j67Tg028Bj2HTg01hej3ITp,2MLR0#MR1g029V#LR2g0145R3g0198R4#0#0#0R5#0R6#0#0#8R7%K0'5R8%66R6'1f0R9%<0,57R:%;4#0#0#0#6R;'1R<523X13P3%65R5,1:1196=23<X13g015?R<#9%:<f1R<,J3%G3%C3R=g015kg016JR>P>g016jR>P31@34R414355331436533g017J143;9334C?g0181FA1B=>P9f2R>g01;mR=g01<MR4'>1=9>=2=4dg013W=D3<CEb3b4b5X031195/16119;523^03P9P:O1b2P8p,4MLokR8,F0E71571R71H08E7g02:a9237eA2372e3Io"). Qed.
Lemma A_AVAIL_META_eq : A_AVAIL_META = Z_to_bv 64 (caddr KAm).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "h04__x1h11zh27__arithh34__ffh48__varmaph55__witp;1p;2p;3p;4p;7p;6g02;jj1MTg01j1j1LTg007Vj10Tg00;:j18Tg00;Xj1KTg00<_j25Tg00Jdj1?Tg008;j16Tg00>Qj21Tg00=Ij1;Tg00d@j32Tg00]^j19Tg00^>j1:Tg00n8j2JTg00_<j1GTg00_Zj1ETg00aJj2CTg00`Ej24Tg010_j33Tg00amj4@Tg00o4j7ATg00bXj2BTg00c:j2>Tg00cTj2=Tg00dZj3DTg00e9j4<Tg00:1j2FTg00i9j67Tg02=8j2HTg01hej3ITp,2MLR0#MR1g02>H#LR2g0145R3g0198R4#0#0#0R5#0#0R6#0#8R7%K0'5R8%?4#0#0#0#6R9'1f0R:%;0,57R;%66R6'1R<523X13P3%65R5,1;11:9=23<X13g015?R<#9%:<f1R<,J3%G3%E3R=g015kg016JR>P>g016jR>P31C34R414355331439533g017J14369334C@g0181FA1B=>P:f2R>g01;mR=g01<MR4'>1=:>=2=4dg013W=D3<C<b3b4b5X0311:5/1911:6523^03P:P;O1b2P8p,4MLokR8,F0E71571R71H08E7g02?S9237eA2372e3Io"). Qed.
Lemma A_AVAIL_META_CNT_eq : A_AVAIL_META_CNT = Z_to_bv 64 (caddr KAmc).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "h04__x1h11zh27__arithh34__ffh48__varmaph55__witp;1p;2p;3p;4p;7p;6g02@[j1MTg01j1j1LTg007Vj10Tg00;:j18Tg00;Xj1KTg00<_j25Tg008;j16Tg00>Qj21Tg00=Ij1<Tg00Jdj1;Tg00d@j32Tg00]^j19Tg00^>j1:Tg00n8j2JTg00_<j1GTg00_Zj1CTg00aJj2@Tg00`Ej24Tg010_j33Tg00amj4?Tg00o4j7ATg00bXj2BTg00c:j2>Tg00cTj2=Tg00dZj3DTg00e9j4ETg00:1j2FTg00i9j67Tg02Amj2HTg01hej3ITp,2MLR0#MR1g02CA#LR2g0145R3g0198R4#0R5#0#0R6#0#0R7#0#8R8%K0'5R9%67R7'1f0R:%<0,58R;%;5#0#0#0#6R5'1R<523X13P3%66R6,1;11:7=23<X13g015?R<#9%:<f1R<,J3%G3%C3R=g015kg016JR>P>g016jR>P31@34R414365331437533g017J14359334C?g0181FA1B=>P:f2R>g01;mR=g01<MR4'>1=:>=2=4dg013W=D3<CEb3b4b5X0311:6/1711:5523^03P:P;O1b2P9p,4MLokR9,F0E71581R81H09E7g02DL9238eA2382e3Io"). Qed.
Lemma A_AVAIL_AREA_CNT_eq : A_AVAIL_AREA_CNT = Z_to_bv 64 (caddr KAac).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "h04__x1h11zh27__arithh34__ffh48__varmaph55__witp;1p;2p;3p;4p;7p;6g02EUj1NTg01j1j1MTg007Vj13Tg00;:j1LTg00;Xj1DTg00<_j25Tg00Jdj18Tg008;j17Tg00>Qj20Tg00=Ij1;Tg00d@j31Tg00]^j1:Tg00^>j1KTg00n8j2ITg00_<j1HTg00_Zj1CTg00aJj2BTg00`Ej26Tg010_j34Tg00amj4@Tg00o4j7ATg00bXj2?Tg00c:j2>Tg00cTj2ETg00dZj3=Tg00e9j4FTg00:1j2GTg00i9j69Tg02Fgj2<Tg01hej3JTf0R0#3#3p=2p,2MLR1#NR2g02H;#MR3g0145R4g0198R5#3R6#2R7#3#2#LR8%D1'5R9%86#3#2#7R6'0%;1,58R:%85#2#2#7R;'0R<9140X14P4%77R7,0:1006=14<X14g015?R<#:%K<f1R<,I4%H4%C4R=g015kg016JR>P>g016jR>P41B45R516475441646544g017J164;9445C@g0181FA1?=>P0f2R>g01;mR=g01<MR5'>1E0>=1=5dg013W==4<CFb3b4b5X041007/06100;514^04P0P:O1b2P9p,4MLokR9,G1E91582R81<19E9g02IF9148eA1483e3Jo"). Qed.
Lemma A_META_SHIFT_eq : A_META_SHIFT = Z_to_bv 64 (caddr KShift).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "h04__x1h11zh27__arithh34__ffh48__varmaph55__witp;1p;2p;3p;4p;7p;6g02JOj1NTg01j1j1MTg007Vj13Tg00;:j1LTg00;Xj1DTg00<_j25Tg00Jdj18Tg008;j17Tg00>Qj20Tg00=Ij1;Tg00d@j31Tg00]^j1:Tg00^>j1KTg00n8j2ITg00_<j1HTg00_Zj1CTg00aJj2BTg00`Ej26Tg010_j34Tg00amj4@Tg00o4j7ATg00bXj2?Tg00c:j2>Tg00cTj2ETg00dZj3=Tg00e9j4FTg00:1j2GTg00i9j69Tg02K]j2<Tg01hej3JTf0R0#3#3p=2p,2MLR1#NR2g02Lm#MR3g0145R4g0198R5#3#2R6#3#2#LR7%D1'5R8%85R9#2#2#7R:'0%;1,57R;%89#3#2#7R9'0R<9140X14P4%76R6,0;100:=14<X14g015?R<#:%K<f1R<,I4%H4%C4R=g015kg016JR>P>g016jR>P41B45R51646544164:544g017J16499445C@g0181FA1?=>P0f2R>g01;mR=g01<MR5'>1E0>=1=5dg013W==4<CFb3b4b5X041006/0:1009514^04P0P;O1b2P8p,4MLokR8,G1E91572R71<18E9g02N89147eA1473e3Jo"). Qed.
Lemma A_AREA_HEAD_eq : A_AREA_HEAD = Z_to_bv 64 (caddr KAhead).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "h04__x1h11zh27__arithh34__ffh48__varmaph55__witp;1p;2p;3p;4p;7p;6g02OCj1MTg01j1j1LTg007Vj10Tg00;:j1;Tg00;Xj1KTg00<_j23Tg00Jdj17Tg008;j16Tg00>Qj21Tg00=Ij1<Tg00d@j32Tg00]^j1:Tg00^>j19Tg00n8j2JTg00_<j1GTg00_Zj1ETg00aJj2CTg00`Ej24Tg010_j35Tg00amj4@Tg00o4j7ATg00bXj2BTg00c:j2?Tg00cTj2>Tg00dZj3DTg00e9j4=Tg00:1j2FTg00i9j68Tg02PPj2HTg01hej3ITp,2MLR0#MR1g02Q_#LR2g0145R3g0198R4#0#0#0R5#0#0#0R6#;R7%K0'3R8%74#7#0#0#0#6R9'1f0R:%<0,37R;%66R6'1R<523X13P3%65R5,1;11:9=23<X13g015?R<#:%9<f1R<,J3%G3%E3R=g015kg016JR>P>g016jR>P31C34R414355531439553g017J14369534C@g0181FA1B=>P:f2R>g01;mR=g01<MR4'?1>:>=2=4dg013W=D3<C=b3b4b5X0311:5/1911:6523^03P:P;O1b2P8p,4MLokR8,F0E81371R71H08E8g02Rj9237eA2372e3Io"). Qed.
Lemma A_AREA_TAIL_eq : A_AREA_TAIL = Z_to_bv 64 (caddr KAtail).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "h04__x1h11zh27__arithh34__ffh48__varmaph55__witp;1p;2p;3p;4p;7p;6g02T5j1MTg01j1j1LTg007Vj10Tg00;:j18Tg00;Xj1KTg00<_j25Tg008;j16Tg00>Qj21Tg00=Ij1<Tg00Jdj1;Tg00d@j32Tg00]^j19Tg00^>j1:Tg00n8j2JTg00_<j1GTg00_Zj1CTg00aJj2@Tg00`Ej24Tg010_j33Tg00amj4?Tg00o4j7ATg00bXj2BTg00c:j2>Tg00cTj2=Tg00dZj3DTg00e9j4ETg00:1j2FTg00i9j67Tg02UBj2HTg01hej3ITp,2MLR0#MR1g02VQ#LR2g0145R3g0198R4#0#0R5#0R6#0#0#0R7#8R8%K0'5R9%67R7'1f0R:%<0,58R;%;5#0#0#0#6R5'1R<523X13P3%66R6,1;11:7=23<X13g015?R<#9%:<f1R<,J3%G3%C3R=g015kg016JR>P>g016jR>P31@34R414365331437533g017J14359334C?g0181FA1B=>P:f2R>g01;mR=g01<MR4'>1=:>=2=4dg013W=D3<CEb3b4b5X0311:6/1711:5523^03P:P;O1b2P9p,4MLokR9,F0E71581R81H09E7g02W\9238eA2382e3Io"). Qed.
Lemma A_AVAIL_AREAS_eq : A_AVAIL_AREAS = Z_to_bv 64 (caddr KAareas).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "h04__x1h11zh27__arithh34__ffh48__varmaph55__witp;1p;2p;3p;4p;7p;6g02Xgj1MTg01j1j1LTg007Vj10Tg00;:j1;Tg00;Xj1KTg00<_j23Tg00Jdj17Tg008;j16Tg00>Qj21Tg00=Ij1<Tg00d@j32Tg00]^j1:Tg00^>j19Tg00n8j2JTg00_<j1GTg00_Zj1ETg00aJj2CTg00`Ej24Tg010_j35Tg00amj4@Tg00o4j7ATg00bXj2BTg00c:j2?Tg00cTj2>Tg00dZj3DTg00e9j4=Tg00:1j2FTg00i9j68Tg02Z6j2HTg01hej3ITp,2MLR0#MR1g02[G#LR2g0145R3g0198R4#0R5#0R6#0R7#0#0#0#;R8%K0'3R9%76#0#0#0#6R6'1f0R:%<0,38R;%75#0#0#0#0#6R5'1R<523X13P3%67R7,1;11:6=23<X13g015?R<#:%9<f1R<,J3%G3%E3R=g015kg016JR>P>g016jR>P31C34R414375531436553g017J14359534C@g0181FA1B=>P:f2R>g01;mR=g01<MR4'?1>:>=2=4dg013W=D3<C=b3b4b5X0311:7/1611:5523^03P:P;O1b2P9p,4MLokR9,F0E81381R81H09E8g02\R9238eA2382e3Io"). Qed.
Lemma A_SEQ_eq : A_SEQ = Z_to_bv 64 (caddr KSeq).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "h04__x1h11zh27__arithh34__ffh48__varmaph55__witp;1p;2p;3p;4p;7p;6g02]^j1NTg01j1j1MTg007Vj13Tg00;:j1LTg00;Xj1DTg00<_j27Tg00Jdj14Tg008;j18Tg00>Qj20Tg00=Ij1;Tg00d@j32Tg00]^j1:Tg00^>j1KTg00n8j2ITg00_<j1HTg00_Zj1CTg00aJj2BTg00`Ej26Tg010_j35Tg00amj4@Tg00o4j7ATg00bXj2?Tg00c:j2>Tg00cTj2ETg00dZj3=Tg00e9j4FTg00:1j2GTg00i9j69Tg02^ej2<Tg01hej3JTf0R0#3#3p=1p,2MLR1#NR2g02_n#MR3g0145R4g0198R5#3#1R6#3#1#LR7%D1'7R8%45#4#1#4R9#1#1#8R:'0%;1,77R;%49#3#1#8R9'0R<9240X14P4%86R6,0;100:=24<X14g015?R<#:%K<f1R<,I4%H4%C4R=g015kg016JR>P>g016jR>P41B45R51646554164:554g017J16499545C@g0181FA1?=>P0f2R>g01;mR=g01<MR5'>1E0>=2=5dg013W==4<CFb3b4b5X041006/0:1009524^04P0P;O1b2P8p,4MLokR8,G1E91772R71<18E9g02a99247eA2473e3Jo"). Qed.
Lemma A_BRK_eq : A_BRK = Z_to_bv 64 (caddr KBrk).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "h04__x1h11zh27__arithh34__ffh48__varmaph55__witp;1p;2p;3p;4p;7p;6g02bBj1NTg01j1j1MTg007Vj10Tg00;:j1LTg00;Xj1DTg00<_j27Tg00Jdj14Tg008;j18Tg00>Qj21Tg00=Ij1;Tg00d@j32Tg00]^j1:Tg00^>j1KTg00n8j2ITg00_<j1HTg00_Zj1CTg00aJj2BTg00`Ej26Tg010_j35Tg00amj4@Tg00o4j7ATg00bXj2?Tg00c:j2>Tg00cTj2ETg00dZj3=Tg00e9j4FTg00:1j2GTg00i9j69Tg02cIj2<Tg01hej3JTf0R0#0#0p=3p,2MLR1#NR2g02dR#MR3g0145R4g0198R5#0#3R6#0#3#LR7%D1'7R8%45#4#0R9#0#4#4#0#3#8R:'1%;1,77R;%49#0#3#3#8R9'1R<9240X14P4%86R6,1;110:=24<X14g015?R<#:%K<f1R<,I4%H4%C4R=g015kg016JR>P>g016jR>P41B45R51646554164:554g017J16499545C@g0181FA1?=>P0f2R>g01;mR=g01<MR5'>1E0>=2=5dg013W==4<CFb3b4b5X041106/1:1109524^04P0P;O1b2P8p,4MLokR8,G1E91772R71<18E9g02e]9247eA2473e3Jo"). Qed.
Lemma Z_UNMAP_SEQ_eq : Z_UNMAP_SEQ = caddr (KUseq 0).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "h04__x1h11zh27__arithh34__ffh48__varmaph55__witp;1p;2p;3p;4p;7p;6g007Vj11Tg00;:j1ATg00;Xj1=Tg00<_j29Tg00Jdj14Tg008;j17Tg00>Qj20Tg00=Ij1?Tg00d@j32Tg00]^j1<Tg00^>j1;Tg00n8j2:Tg00_<j1NTg00_Zj1MTg00aJj2LTg00`Ej26Tg010_j35Tg00amj4ITg00o4j7GTg00bXj2FTg00c:j2BTg00cTj2@Tg00dZj3CTg00e9j4DTg00:1j2ETg00i9j68Tg02ffj1HTg02h3j2>Tg02iBj1JTg01j1j1KTf0R0#1#1p=3g0145R1g0198R2#1#3R3#1#3#AR4p,2MLR5#='9R6%42#1#4#1#4R7#3#3#7R8'0%?5,94R4%47#1#3#7R7'0g013WR9'0R:9210X11P1%73R3,041008=21:X11g015?R:#<%;:f1R:,:1%N1%M1R;g015kg016JR<P<g016jR<P11L12R216135511618551g017J161795121619551CIg0181FG1F;<P0f2R<g01;mR;g01<MR2'B1@0<=2;2dAC19:CDb3b4b5X011003/081007/09521^01P0P4O1b2P6p,4MLokR6,E5E8%H5R41>56E8g02jM/099214e%J9#K9214eo"). Qed.
Lemma Z_BOUNCES_eq : Z_BOUNCES = caddr (KBounce 0).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "h04__x1h11zh27__arithh34__ffh48__varmaph55__witp;1p;2p;3p;4p;7p;6g007Vj12Tg00;:j1ATg00;Xj1=Tg00<_j29Tg00Jdj13Tg008;j17Tg00>Qj20Tg00=Ij1?Tg00d@j31Tg00]^j1<Tg00^>j1;Tg00n8j2:Tg00_<j1NTg00_Zj1MTg00aJj2LTg00`Ej26Tg010_j35Tg00amj4ITg00o4j7GTg00bXj2FTg00c:j2BTg00cTj2@Tg00dZj3CTg00e9j4DTg00:1j2ETg00i9j68Tg02kWj1HTg02lbj2>Tg02moj1JTg01j1j1KTf0R0#2#2p=4g0145R1g0198R2#2#4R3#2#4#AR4p,2MLR5#='9R6%32#2#3#3#3R7#4#4#7R8'0%?5,94R4%37#2#4#7R7'0g013WR9'0R:9110X11P1%73R3,041008=11:X11g015?R:#<%;:f1R:,:1%N1%M1R;g015kg016JR<P<g016jR<P11L12R216135511618551g017J161795121619551CIg0181FG1F;<P0f2R<g01;mR;g01<MR2'B1@0<=1;2dAC19:CDb3b4b5X011003/081007/09511^01P0P4O1b2P6p,4MLokR6,E5E8%H5R41>56E8g02o:/099114e%J9#K9114eo"). Qed.
Lemma A_ERRNO_eq : A_ERRNO = Z_to_bv 64 ERRNO.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "p;1p;2p;3g00AHj12Tg00c:j21Tg01hej30Tp,2ML#2g01>oR0g0145/1030o"). Qed.
Lemma A_SIZE_CLASSES_eq : A_SIZE_CLASSES = Z_to_bv 64 T_SIZE_CLASSES.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "p;1p;2p;3g01F4j12Tg00c:j21Tg01hej30Tp,2ML#2g01K<R0g0145/1030o"). Qed.
Lemma A_SMALL_CNT_TAB_eq : A_SMALL_CNT_TAB = Z_to_bv 64 T_SMALL_CNT.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "p;1p;2p;3g01GDj12Tg00c:j21Tg01hej30Tp,2ML#2g01LNR0g0145/1030o"). Qed.
Lemma A_MED_CNT_TAB_eq : A_MED_CNT_TAB = Z_to_bv 64 T_MED_CNT.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "p;1p;2p;3g01HUj12Tg00c:j21Tg01hej30Tp,2ML#2g01M]R0g0145/1030o"). Qed.
Lemma A_DEBRUIJN_eq : A_DEBRUIJN = Z_to_bv 64 T_DEBRUIJN.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "p;1p;2p;3g01Dhj12Tg00c:j21Tg01hej30Tp,2ML#2g01NjR0g0145/1030o"). Qed.

(* [comment removed for export] *)
Lemma at_Z0 : forall a d, at_ (Z_to_bv 64 a) d = Z_to_bv 64 (a + d).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "h01zh12b1h22b2h31nh41Hh51ah61dp;1p;3p;2p;6g01fNj15Tg00d@j37Tg00<_j21Tg030Fj3@Tg007Vj16Tg00;:j1=Tg01g1j24Tg00>Qj20Tg030jj22Tg031Pj1<Tg0096j28Tg00c:j2;Tg0329j3?Tg00i9j69Tg032`j2:Tg033Oj2>Tg0145R0f1R1f0R237p=3g034DR3%52R4%51R5g009Vf2R6#5?712f3R7/161171'3R8[11611162'3%57?761[R9f4#5?776\8A@612P2n2001000000120000000W2W1W3P9^25^14^33P2g0198#6#6#6#6#6#6#=R31436,13R4/01R5,43R91061R8,43R:P012351076R;,43,13R<,32X00P01236R=1026,23/3<X00P01238R<1237/06,23/32X00P0%<3R7,88R>18;7,32X001;0>1867/01/87A?617E910=1,23/3<e113:1:38E9P41:36E911391:35E9O4b4%531431/>21012,4337eX60X50o"). Qed.
Lemma at_lock : forall d, at_ A_LOCK d = Z_to_bv 64 (LOCKA + d).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "h01dh14baseh25lemmap;1p;2p;3p;4p;:p;9g007Vj10Tg00;:j1ATg01fNj1;Tg00=Ij17Tg01g1j25Tg00d@j3<j13Tg034bj1:Tg033OR0j21Tg035Rj44Tg0369j18Tg036hj42Tg037_j39Tg038Uj26Tg039Al:@Tg00>Qj2?Tg039nl9=Tg03:hj2>Tg0145R1g0198#0#0#0#0#0#0#AR2#;R3p,2ML#7R4g01=fR5,52R63<P3%33R7%:3f1R8,141168P3^01R9^13R:P3P9P7P1P3%31P7C4R;C4R<P3P9P;P1P3P7%83C2C299:<P0P4P6f0R6P8P81618M:@1?58,52R2P21632M9=W2g03<11>56O2W0o"). Qed.
Lemma at_ctx : forall d, at_ A_CTX d = Z_to_bv 64 (LOCKA + (8 + d)).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_defs ()) ["WithLayout"] "h04__x1h14__x2h21bh37__arithh44__ffh58__varmaph65__with71dp;1p;2p;3p;4p;7p;8p;6g007Vj12Tg00;:j1NTg01fNj1?Tg01j1j1;Tg01g1j24j1<Tg033Oj27Tg008;j1ATg00>Qj20Tg00d@j31Tg00c:j25Tg00]^j1:Tg00^>j19Tg00n8j2MTg00^^j1LTg00nVj4KTg00_<j1FTg00_Zj1ETg00aJj26Tg00`Ej2@Tg010_j33Tg00amj4BTg00o4j7>Tg00bXj2CTg00cTj2DTg00dZj3=Tg00e9j4GTg03=>j8HTg03:hj2ITg00i9j68Tg00;Xj1JTg0145R0g0198R1#2R2#2#2R3#2#2#2#NR4#?R5g01k:#;R6,44R7f0R8f1R9'7g01=fR:%A3R3/09R;'0,44R<515X25P51068R=,44A158<X25P0P5%<4R4P4P=1038,0:R<P5\0/54g015?R4#:%94P0f2R4,M0P9%L0CK%F0%E0R5g015kg016JR>P>g016jR>P01601R11@03R?5301602R2530g017JA30?29301CBg0181F>1C5>P8P4g01;mR>g01<MR5'51D84=1>5dg013W==09CGb4b5b6X00X101083/09108;510^00^10P8P9P:O2b3g01lE/08=10<eA10=<eGH17781I68E8p,2ML#Jg03=[E8W7o"). Qed.

Definition clen (k : cslot) : Z :=
  match k with
  | KInit | KCtr => 4
  | KSeq | KUseq _ | KBounce _ => 1
  | _ => 8
  end.

Definition cvalid (k : cslot) : Prop :=
  match k with
  | KActive i | KUsage i => 0 <= i < 48
  | KUseq i | KBounce i => 0 <= i < 32
  | _ => True
  end.

Definition ctx_rec := cslot -> Z.

Definition cupd (c : ctx_rec) (k : cslot) (v : Z) : ctx_rec :=
  fun k' => if cslot_eq_dec k' k then v else c k'.

Record astate := AST {
  a_ctx : ctx_rec;
  a_areas : list Z;                 (* [comment removed for export] *)
  a_meta : mmap_t;                 (* [comment removed for export] *)
  a_freelist : list Z;              (* [comment removed for export] *)
  a_active : Z -> list Z;           (* [comment removed for export] *)
  a_pages : list Z;                 (* [comment removed for export] *)
  a_brk_lo : Z;                     (* [comment removed for export] *)
  a_live : Z -> option Z;           (* [comment removed for export] *)
  (* [comment removed for export] *)
  a_mblocks : list (Z * Z);         (* [comment removed for export] *)
  a_xmaps : list (Z * Z)            (* [comment removed for export] *)
}.

Definition lupd (f : Z -> option Z) (p : Z) (v : option Z) : Z -> option Z :=
  fun x => if Z.eq_dec x p then v else f x.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition w_last (w : Z) : Z := w mod 32.
Definition w_freeable (w : Z) : Z := (w / 32) mod 2.
Definition w_sc (w : Z) : Z := (w / 64) mod 64.
Definition w_maplen (w : Z) : Z := w / 4096.

Definition mt_last (mt : meta_rec) : Z := w_last (mt_w32 mt).
Definition mt_sc (mt : meta_rec) : Z := w_sc (mt_w32 mt).
Definition mt_maplen (mt : meta_rec) : Z := w_maplen (mt_w32 mt).
Definition mt_cnt (mt : meta_rec) : Z := mt_last mt + 1.

(* [comment removed for export] *)
Definition mt_stride (mt : meta_rec) : Z :=
  if (mt_maplen mt =? 0) || negb (mt_last mt =? 0)
  then 16 * size_class (mt_sc mt)
  else mt_maplen mt * 4096 - 16.

(* [comment removed for export] *)
Definition slot_start_g (mem sd i : Z) : Z := mem + 16 + i * sd.          (* [comment removed for export] *)
Definition slot_end_g (mem sd i : Z) : Z := mem + 16 + i * sd + sd - 4.   (* [comment removed for export] *)
Definition slot_start (mt : meta_rec) (i : Z) : Z := slot_start_g (mt_mem mt) (mt_stride mt) i.
Definition slot_end (mt : meta_rec) (i : Z) : Z := slot_end_g (mt_mem mt) (mt_stride mt) i.

(* [comment removed for export] *)
Definition grp_map_len (mt : meta_rec) : Z := mt_maplen mt * 4096.

(* [comment removed for export] *)
Definition gext_lo (mt : meta_rec) : Z := mt_mem mt.
Definition gext_hi (mt : meta_rec) : Z := mt_mem mt + 12 + mt_cnt mt * mt_stride mt.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record fct := FCT { f_a : Z; f_n : Z; f_v : Z }.

(* [comment removed for export] *)
Definition grp_hdr_fields (ma : Z) (mt : meta_rec) (aib : Z) : list fct :=
  [FCT (mt_mem mt) 8 ma; FCT (mt_mem mt + 8) 1 aib].

(* [comment removed for export] *)
Definition slot_fields_g (mem sd : Z) (i : Z) (st : slot_st) : list fct :=
  let p0 := slot_start_g mem sd i in
  let e := slot_end_g mem sd i in
  [FCT (p0 - 4) 1 0; FCT e 1 0] ++
  match st with
  | SIdle | STaken => []
  | SLive off n =>
      let p := p0 + 16 * off in
      let rsv := e - p - n in
      (if off =? 0 then [] else [FCT (p0 - 3) 1 224; FCT (p0 - 2) 2 off; FCT (p - 4) 1 0])
      ++ [FCT (p - 3) 1 (i + 32 * Z.min rsv 5); FCT (p - 2) 2 ((p - mem - 16) / 16)]
      ++ (if rsv <? 5 then [] else [FCT (e - 4) 4 rsv; FCT (e - 5) 1 0])
      ++ (if rsv =? 0 then [] else [FCT (e - rsv) 1 0])
  | SNested child =>
      [FCT (p0 - 3) 1 (i + 32 * 6); FCT (p0 - 2) 2 ((p0 - mem - 16) / 16)]
  end.
Definition slot_fields (mt : meta_rec) (i : Z) (st : slot_st) : list fct :=
  slot_fields_g (mt_mem mt) (mt_stride mt) i st.

Section Facts.
  Variable A : astate.

  Definition has_ctx (f : fct) : Prop := exists k, cvalid k /\ f = FCT (caddr k) (clen k) (a_ctx A k).
  Definition has_area (f : fct) : Prop := exists pg, In pg (a_areas A) /\ f = FCT pg 8 (a_ctx A KSecret).
  Definition has_meta (f : fct) : Prop :=
    exists ma mt fl, a_meta A ma = Some mt /\ f = FCT (ma + moff fl) (mlen fl) (mt_f mt fl).
  Definition has_grp (f : fct) : Prop :=
    exists ma mt aib slots, a_meta A ma = Some mt /\ mt_role mt = RGroup aib slots /\
      (In f (grp_hdr_fields ma mt aib) \/
       exists i st, nth_error slots i = Some st /\ In f (slot_fields mt (Z.of_nat i) st)).

  Definition has (f : fct) : Prop := has_ctx f \/ has_area f \/ has_meta f \/ has_grp f.

  (* [comment removed for export] *)
  Definition fbyte (f : fct) (x b : Z) : Prop :=
    f_a f <= x < f_a f + f_n f /\ b = byte_of (f_v f) (x - f_a f).

  Definition facts (x b : Z) : Prop := exists f, has f /\ fbyte f x b.

  (* [comment removed for export] *)
  Definition dom (x : Z) : Prop :=
    (exists pg, In pg (a_areas A) /\ pg <= x < pg + 4096) \/
    (exists ma mt aib slots, a_meta A ma = Some mt /\ mt_role mt = RGroup aib slots /\
       0 < mt_maplen mt /\ mt_mem mt <= x < mt_mem mt + grp_map_len mt) \/
    (exists pg, In pg (a_pages A) /\ pg <= x < pg + 4096).
End Facts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mbyte (m : word -> option byte) (x : Z) : option Z :=
  match rdn ml_segs m (Z_to_bv 64 x) 1 with Some [b] => Some (bv_unsigned b) | _ => None end.

Record Rep (A : astate) (m : word -> option byte) : Prop := {
  rep_facts : forall x b, facts A x b -> mbyte m x = Some b;
  rep_dom   : forall x, dom A x -> m (Z_to_bv 64 x) <> None;
  (* [comment removed for export] *)
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition page_aligned (x : Z) : Prop := x mod 4096 = 0.

(* [comment removed for export] *)
Definition heap_range (lo hi : Z) : Prop :=
  0x1000 <= lo /\ lo <= hi /\ hi <= alloc_ceiling /\ (hi <= IMG_LO \/ IMG_HI <= lo).

(* [comment removed for export] *)
Definition dll (A : astate) (l : list Z) : Prop :=
  forall k x, nth_error l k = Some x ->
    exists mt, a_meta A x = Some mt /\
      mt_next mt = nth (S k mod length l) l 0 /\
      mt_prev mt = nth ((k + length l - 1) mod length l)%nat l 0.

(* [comment removed for export] *)
Definition meta_addr (pg : Z) (k : Z) : Z := pg + 24 + 40 * k.

(* [comment removed for export] *)
Definition is_live (A : astate) (p n : Z) : Prop :=
  exists ma mt aib slots i off, a_meta A ma = Some mt /\ mt_role mt = RGroup aib slots /\ 0 <= i /\
    nth_error slots (Z.to_nat i) = Some (SLive off n) /\ p = slot_start mt i + 16 * off.

Record WF (A : astate) : Prop := {
  (* [comment removed for export] *)
  wf_areas_nodup : NoDup (a_areas A);
  wf_areas_al : forall pg, In pg (a_areas A) -> page_aligned pg /\ heap_range pg (pg + 4096);
  wf_meta_dom : forall ma, a_meta A ma <> None <->
                  exists pg k, In pg (a_areas A) /\ 0 <= k < 101 /\ ma = meta_addr pg k;
  (* [comment removed for export] *)
  wf_init : a_ctx A KInit = 0 \/ a_ctx A KInit = 1;
  wf_uninit : a_ctx A KInit = 0 -> a_areas A = [] /\ a_ctx A KFmh = 0 /\ a_ctx A KAmc = 0 /\
              a_ctx A KAac = 0 /\ a_ctx A KBrk = 0 /\ a_ctx A KAtail = 0 /\
              a_ctx A KShift = 0 /\ a_pages A = [] /\ (forall sc, a_ctx A (KActive sc) = 0);
  wf_amc : 0 <= a_ctx A KAmc <= 100;
  wf_am : a_ctx A KAmc > 0 ->
          exists pg, a_areas A <> [] /\ pg = last (a_areas A) 0 /\
          a_ctx A KAm = meta_addr pg (101 - a_ctx A KAmc) /\
          forall k, 101 - a_ctx A KAmc <= k < 101 ->
            exists mt, a_meta A (meta_addr pg k) = Some mt /\ mt_role mt = RAvail;
  wf_atail : a_ctx A KAtail = last (a_areas A) 0;
  wf_ahead : a_ctx A KAhead = hd 0 (a_areas A);
  (* [comment removed for export] *)
  wf_avail_zero : forall ma mt, a_meta A ma = Some mt -> mt_role mt = RAvail ->
     mt_prev mt = 0 /\ mt_next mt = 0 /\ mt_mem mt = 0 /\ mt_avail mt = 0 /\ mt_freed mt = 0 /\ mt_w32 mt = 0;
  wf_free_zero : forall ma mt, a_meta A ma = Some mt -> mt_role mt = RFree ->
     mt_mem mt = 0 /\ mt_avail mt = 0 /\ mt_freed mt = 0 /\ mt_w32 mt = 0;
  (* [comment removed for export] *)
  wf_fl_nodup : NoDup (a_freelist A);
  wf_fl_head : a_ctx A KFmh = hd 0 (a_freelist A);
  wf_fl_mem : forall ma, In ma (a_freelist A) <-> exists mt, a_meta A ma = Some mt /\ mt_role mt = RFree;
  wf_fl_dll : dll A (a_freelist A);
  (* [comment removed for export] *)
  wf_grp : forall ma mt aib slots, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     (* [comment removed for export] *)
     0 <= mt_w32 mt < 2^64 /\ w_freeable (mt_w32 mt) = 1 /\
     (mt_sc mt < 48 \/ (mt_sc mt = 63 /\ mt_last mt = 0 /\ 0 < mt_maplen mt)) /\
     Z.of_nat (length slots) = mt_cnt mt /\
     0 <= mt_avail mt < 2 ^ (mt_cnt mt) /\ 0 <= mt_freed mt < 2 ^ (mt_cnt mt) /\
     Z.land (mt_avail mt) (mt_freed mt) = 0 /\
     0 <= aib < 256 /\ mt_avail mt < 2 ^ (aib mod 32 + 1) /\ aib mod 32 <= mt_last mt /\
     (forall i st, nth_error slots (Z.to_nat i) = Some st -> 0 <= i ->
        (Z.testbit (Z.lor (mt_avail mt) (mt_freed mt)) i = true <-> st = SIdle)) /\
     (* [comment removed for export] *)
     mt_mem mt mod 16 = 0 /\ 0x1000 <= mt_mem mt /\
     16 + mt_cnt mt * mt_stride mt <= (if mt_maplen mt =? 0 then 2^64 else grp_map_len mt) /\
     mt_mem mt + 16 + mt_cnt mt * mt_stride mt <= alloc_ceiling /\
     (0 < mt_maplen mt -> page_aligned (mt_mem mt) /\ heap_range (mt_mem mt) (mt_mem mt + grp_map_len mt));
  wf_live : forall ma mt aib slots i off n, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     nth_error slots (Z.to_nat i) = Some (SLive off n) -> 0 <= i ->
     0 <= off /\ 0 <= n /\ 16 * off + n <= mt_stride mt - 4 /\ off < 2^16 /\ off <= 255 /\ mt_stride mt - n < 2^20;
  wf_nested : forall ma mt aib slots i ch, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     nth_error slots (Z.to_nat i) = Some (SNested ch) -> 0 <= i ->
     exists mc aibc slc, a_meta A ch = Some mc /\ mt_role mc = RGroup aibc slc /\
       mt_maplen mc = 0 /\ mt_mem mc = slot_start mt i /\
       16 + mt_cnt mc * mt_stride mc <= mt_stride mt;   (* [comment removed for export] *)
  wf_nested_parent : forall ch mc aibc slc, a_meta A ch = Some mc -> mt_role mc = RGroup aibc slc ->
     mt_maplen mc = 0 ->
     exists ma mt aib slots i, a_meta A ma = Some mt /\ mt_role mt = RGroup aib slots /\
       0 <= i /\ nth_error slots (Z.to_nat i) = Some (SNested ch);
  (* [comment removed for export] *)
  wf_grp_root : forall ma mt aib slots, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     exists mr mtr aibr slr, a_meta A mr = Some mtr /\ mt_role mtr = RGroup aibr slr /\ 0 < mt_maplen mtr /\
       mt_mem mtr <= gext_lo mt /\ gext_hi mt + 4 <= mt_mem mtr + grp_map_len mtr /\
       (0 < mt_maplen mt -> mr = ma);
  (* [comment removed for export] *)
  wf_laminar : forall ma mt aib slots ma' mt' aib' slots',
     a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     a_meta A ma' = Some mt' -> mt_role mt' = RGroup aib' slots' -> ma <> ma' ->
     gext_hi mt + 4 <= gext_lo mt' \/ gext_hi mt' + 4 <= gext_lo mt \/
     (exists j ch, 0 <= j /\ nth_error slots (Z.to_nat j) = Some (SNested ch) /\
        slot_start mt j <= gext_lo mt' /\ gext_hi mt' <= slot_end mt j) \/
     (exists j ch, 0 <= j /\ nth_error slots' (Z.to_nat j) = Some (SNested ch) /\
        slot_start mt' j <= gext_lo mt /\ gext_hi mt <= slot_end mt' j);
  (* [comment removed for export] *)
  wf_act_head : forall sc, 0 <= sc < 48 -> a_ctx A (KActive sc) = hd 0 (a_active A sc);
  wf_act_nodup : forall sc, NoDup (a_active A sc);
  wf_act_dll : forall sc, 0 <= sc < 48 -> dll A (a_active A sc);
  wf_act_mem : forall sc ma, In ma (a_active A sc) ->
     exists mt aib slots, a_meta A ma = Some mt /\ mt_role mt = RGroup aib slots /\ mt_sc mt = sc;
  wf_unlinked : forall ma mt aib slots, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     ~ In ma (a_active A (mt_sc mt)) -> mt_prev mt = 0 /\ mt_next mt = 0;
  (* [comment removed for export] *)
  wf_act_nonhead : forall sc ma mt, In ma (a_active A sc) -> ma <> hd 0 (a_active A sc) ->
     a_meta A ma = Some mt -> mt_avail mt = 0 /\ mt_freed mt <> 0;
  wf_act63 : forall ma mt aib slots, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     mt_sc mt = 63 -> mt_prev mt = 0 /\ mt_next mt = 0;
  (* [comment removed for export] *)
  wf_disj_area_grp : forall pg ma mt aib slots, In pg (a_areas A) ->
     a_meta A ma = Some mt -> mt_role mt = RGroup aib slots -> 0 < mt_maplen mt ->
     pg + 4096 <= mt_mem mt \/ mt_mem mt + grp_map_len mt <= pg;
  wf_disj_grp_grp : forall ma mt aib slots ma' mt' aib' slots',
     a_meta A ma = Some mt -> mt_role mt = RGroup aib slots -> 0 < mt_maplen mt ->
     a_meta A ma' = Some mt' -> mt_role mt' = RGroup aib' slots' -> 0 < mt_maplen mt' ->
     ma <> ma' -> mt_mem mt + grp_map_len mt <= mt_mem mt' \/ mt_mem mt' + grp_map_len mt' <= mt_mem mt;
  wf_grp_mem_inj : forall ma mt aib slots ma' mt' aib' slots',
     a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     a_meta A ma' = Some mt' -> mt_role mt' = RGroup aib' slots' ->
     mt_mem mt = mt_mem mt' -> ma = ma';
  (* [comment removed for export] *)
  wf_live_map : forall p n, a_live A p = Some n <-> is_live A p n;
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  wf_span : forall ma mt aib slots, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     0 < mt_last mt -> mt_cnt mt * mt_stride mt < 2^20;
  (* [comment removed for export] *)
  wf_single : forall ma mt aib slots, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     mt_last mt = 0 -> 0 < mt_maplen mt -> mt_sc mt < 48 ->
     256 <= size_class (mt_sc mt) \/ mt_stride mt <= 16 * size_class (mt_sc mt);
  (* [comment removed for export] *)
  wf_inactive : forall ma mt aib slots j, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     aib mod 32 < j <= mt_last mt -> Z.testbit (mt_freed mt) j = true;
  (* [comment removed for export] *)
  wf_partial : forall sc ma mt aib slots ma' mt' aib' slots',
     In ma (a_active A sc) -> In ma' (a_active A sc) ->
     a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     a_meta A ma' = Some mt' -> mt_role mt' = RGroup aib' slots' ->
     aib mod 32 < mt_last mt -> aib' mod 32 < mt_last mt' -> ma = ma';
  (* [comment removed for export] *)
  wf_ctx_nonneg : forall k, 0 <= a_ctx A k;
  (* [comment removed for export] *)
  wf_nested_small : forall ma mt aib slots, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     mt_maplen mt = 0 -> 1 <= mt_last mt /\ 16 + mt_cnt mt * mt_stride mt <= 2048;
  (* [comment removed for export] *)
  wf_reusable : forall ma mt aib slots, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     mt_sc mt < 48 -> Z.lor (mt_avail mt) (mt_freed mt) <> 0 -> 16 * size_class (mt_sc mt) <= mt_stride mt;
  (* [comment removed for export] *)
  wf_cover : forall pa pm paib psl j ch x mtx aibx slx,
     a_meta A pa = Some pm -> mt_role pm = RGroup paib psl -> 0 <= j -> nth_error psl (Z.to_nat j) = Some (SNested ch) ->
     a_meta A x = Some mtx -> mt_role mtx = RGroup aibx slx ->
     slot_start pm j <= gext_lo mtx -> gext_hi mtx <= slot_end pm j ->
     exists mtc aibc slc, a_meta A ch = Some mtc /\ mt_role mtc = RGroup aibc slc /\
       gext_lo mtc <= gext_lo mtx /\ gext_hi mtx <= gext_hi mtc;
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  wf_shift : a_ctx A KShift < 48;
  (* [comment removed for export] *)
  wf_noarea_shift : a_areas A = [] -> a_ctx A KAac = 0 -> a_ctx A KShift = 0;
  (* [comment removed for export] *)
  wf_brk0 : a_ctx A KBrk = 0 -> a_areas A = [] /\ a_pages A = [] /\ a_ctx A KAac = 0;
  (* [comment removed for export] *)
  wf_stride20 : forall ma mt aib slots, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     mt_sc mt < 48 -> mt_stride mt < 2^20;
  (* [comment removed for export] *)
  wf_pages_al : forall pg, In pg (a_pages A) -> page_aligned pg /\ heap_range pg (pg + 4096);
  wf_disj_page_area : forall pg pg', In pg (a_pages A) -> In pg' (a_areas A) -> pg + 4096 <= pg' \/ pg' + 4096 <= pg;
  wf_disj_page_grp : forall pg ma mt aib slots, In pg (a_pages A) ->
     a_meta A ma = Some mt -> mt_role mt = RGroup aib slots -> 0 < mt_maplen mt ->
     pg + 4096 <= mt_mem mt \/ mt_mem mt + grp_map_len mt <= pg;
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  wf_partial_sc : forall ma mt aib slots, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     aib mod 32 < mt_last mt -> 7 <= mt_sc mt;
  (* [comment removed for export] *)
  wf_mblocks_len : Z.of_nat (length (a_mblocks A)) <=
     Z.of_nat (length (a_areas A)) + (if a_ctx A KAac =? 0 then 0 else 1);
  wf_mblocks_sz : forall c l, In (c, l) (a_mblocks A) ->
     0x1000 <= c /\ 0 < l <= 2 ^ (12 + Z.of_nat (length (a_mblocks A))) /\ c + l <= alloc_ceiling;
  (* [comment removed for export] *)
  wf_shift_mblocks : a_ctx A KShift <= Z.of_nat (length (a_mblocks A));
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  wf_shift_acct : 2 ^ (a_ctx A KShift + 1) <= Z.of_nat (length (a_areas A)) + a_ctx A KAac + a_ctx A KShift + 2 /\
                  2 ^ (a_ctx A KShift) <= Z.of_nat (length (a_areas A)) + a_ctx A KShift + 2 /\
                  Z.of_nat (length (a_mblocks A)) <= a_ctx A KShift
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint maps_pw (l : list (word * word)) : Prop :=
  match l with
  | [] => True
  | (a, n) :: r => region_free r a n = true /\ maps_pw r
  end.

(* [comment removed for export] *)
Definition mcov (l : list (word * word)) (x n : Z) : Prop :=
  exists b sz, In (b, sz) l /\ bv_unsigned b <= x /\ x + n <= bv_unsigned b + bv_unsigned sz.

Record VMok (A : astate) (h : VmMaps) : Prop := {
  (* [comment removed for export] *)
  vm_grp : forall ma mt aib slots, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     0 < mt_maplen mt ->
     In (Z_to_bv 64 (mt_mem mt), Z_to_bv 64 (grp_map_len mt)) (vm_maps h) /\
     region_free (vm_noaccess h) (Z_to_bv 64 (mt_mem mt)) (Z_to_bv 64 (grp_map_len mt)) = true;
  (* [comment removed for export] *)
  vm_brk_ok : a_ctx A KBrk = 0 \/ a_ctx A KBrk = 2^64 - 1 \/
              (a_ctx A KBrk = bv_unsigned (vm_brk h) /\ 0 < bv_unsigned (vm_brk h) /\
               bv_unsigned (vm_start_brk h) <= bv_unsigned (vm_brk h) /\ page_aligned (bv_unsigned (vm_brk h)));
  (* [comment removed for export] *)
  vm_areas_res : a_ctx A KAac > 0 ->
     page_aligned (a_ctx A KAareas) /\
     a_ctx A KAareas + 4096 * a_ctx A KAac <= alloc_ceiling /\
     map_contains (vm_maps h) (Z_to_bv 64 (a_ctx A KAareas)) (Z_to_bv 64 (4096 * a_ctx A KAac)) = true /\
     map_contains (vm_noaccess h) (Z_to_bv 64 (a_ctx A KAareas)) (Z_to_bv 64 (4096 * a_ctx A KAac)) = true;
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  vm_res : vm_reserved h = segments_reserved ml_segs;
  (* [comment removed for export] *)
  vm_brk_valid : 0 < bv_unsigned (vm_brk h) /\ bv_unsigned (vm_start_brk h) <= bv_unsigned (vm_brk h) /\
                 page_aligned (bv_unsigned (vm_brk h)) /\ bv_unsigned (vm_brk h) <= alloc_ceiling;
  (* [comment removed for export] *)
  vm_pw : maps_pw (vm_maps h);
  (* [comment removed for export] *)
  vm_maps_wf : forall b sz, In (b, sz) (vm_maps h) -> 0 < bv_unsigned sz /\ bv_unsigned b + bv_unsigned sz <= alloc_ceiling /\
     0x1000 <= bv_unsigned b /\ (bv_unsigned b + bv_unsigned sz <= IMG_LO \/ IMG_HI <= bv_unsigned b);
  (* [comment removed for export] *)
  vm_na_in : forall b sz, In (b, sz) (vm_noaccess h) -> 0 < bv_unsigned sz /\ mcov (vm_maps h) (bv_unsigned b) (bv_unsigned sz);
  (* [comment removed for export] *)
  vm_areas_cov : forall pg, In pg (a_areas A) ->
     mcov (vm_maps h) pg 4096 /\ region_free (vm_noaccess h) (Z_to_bv 64 pg) (Z_to_bv 64 4096) = true;
  vm_pages_cov : forall pg, In pg (a_pages A) ->
     mcov (vm_maps h) pg 4096 /\ region_free (vm_noaccess h) (Z_to_bv 64 pg) (Z_to_bv 64 4096) = true;
  (* [comment removed for export] *)
  vm_all : forall b sz, In (b, sz) (vm_maps h) ->
      (exists ma mt aib slots, a_meta A ma = Some mt /\ mt_role mt = RGroup aib slots /\ 0 < mt_maplen mt /\
          bv_unsigned b = mt_mem mt /\ bv_unsigned sz = grp_map_len mt)
      \/ (bv_unsigned (vm_start_brk h) <= bv_unsigned b /\ bv_unsigned b + bv_unsigned sz <= bv_unsigned (vm_brk h))
      \/ (exists c l, In (c, l) (a_mblocks A ++ a_xmaps A) /\ c <= bv_unsigned b /\ bv_unsigned b + bv_unsigned sz <= c + l);
  (* [comment removed for export] *)
  vm_brk_span : (a_ctx A KBrk = 0 -> vm_brk h = vm_start_brk h) /\
      bv_unsigned (vm_brk h) - bv_unsigned (vm_start_brk h) <= 4096 * (Z.of_nat (length (a_areas A)) + 1);
  (* [comment removed for export] *)
  vm_top : alloc_top h = alloc_ceiling
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition owned_of (A : astate) (x : Z) : Prop := (LOCKA <= x < CTX_END) \/ dom A x.

(* [comment removed for export] *)
Definition ctx0 : ctx_rec := fun _ => 0.
Definition A0 : astate := AST ctx0 [] (fun _ => None) [] (fun _ => []) [] 0 (fun _ => None) [] [].

(* [comment removed for export] *)
Definition set_xmaps (A : astate) (l : list (Z * Z)) : astate :=
  AST (a_ctx A) (a_areas A) (a_meta A) (a_freelist A) (a_active A) (a_pages A) (a_brk_lo A) (a_live A) (a_mblocks A) l.
Definition set_mblocks (A : astate) (l : list (Z * Z)) : astate :=
  AST (a_ctx A) (a_areas A) (a_meta A) (a_freelist A) (a_active A) (a_pages A) (a_brk_lo A) (a_live A) l (a_xmaps A).

End WithLayout.

(* [comment removed for export] *)
Ltac llia := first [lia | pose proof layout_small; lia | pose proof layout_nums; lia].
Ltac lnia := first [nia | pose proof layout_small; nia | pose proof layout_nums; nia].

(* [comment removed for export] *)
Ltac ceil := let H := fresh "HCEIL" in pose proof alloc_ceiling_val as H.
