(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import PropExec.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import AxSymExec3 AxSymExec3B.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require AsanHeapSortDef.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_AsanPlanCore () := "C47Corelib7Program6Basics4flipC47Corelib4Init9Datatypes3fstc79OSSVerify5KrLib2K52AS<AsanPlanCore3APC4vkeyC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C56Stdlib6PArith6BinPos3Pos;of_succ_natC47Corelib4Init5Logic7f_equalC56Stdlib6PArith6BinPos3Pos6to_natK47Corelib4Init9Datatypes3nat02C56Stdlib6PArith4Pnat;SuccNat2Pos7id_succC47Corelib4Init5Logic6eq_indI47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums8positive00C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List9fold_leftC46Stdlib5Lists4List:fold_rightC46Stdlib5Lists4List7existsbC79OSSVerify5KrLib2K52AS:AxSymExec33AX25sfactC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9MorphismsCeq_rewrite_relationC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C79OSSVerify5KrLib2K52AS:AxSymExec33AX26pt_gssC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC79OSSVerify5KrLib2K52AS:AxSymExec33AX26pt_gsoC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX2;pt_get_leafC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00I79OSSVerify5KrLib2K52AS:AxSymExec33AX25ptree00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC:live_agreeC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib5Arith8PeanoNat3Nat3eqbC79OSSVerify5KrLib2K52AS:AxSymExec33AX26pt_getC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01K47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes3orbC56Stdlib5Arith8PeanoNat3Nat8eqb_reflC56Stdlib5Arith8PeanoNat3Nat8eqb_specI47Corelib4Init9Datatypes7reflect00C47Corelib4Init5Logic9False_indc79OSSVerify5KrLib2K52AS<AsanPlanCore3APC9in_live_tC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC8vkey_injC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C79OSSVerify5KrLib2K52AS:AxSymExec33AX26pt_setC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02K79OSSVerify5KrLib2K52AS:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC>live_agree_varC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2K52AS:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC9expr_varsC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC;expr_vars_tC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2K52AS:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2K52AS:AxSymExec33AX24expr04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2K52AS:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2K52AS:AxSymExec33AX24expr06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2K52AS:AxSymExec33AX24expr07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2K52AS:AxSymExec33AX24expr08C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX28expr_indC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2K52AS:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics5Riscv5Instr5aluop00I4ELinuxProcessSemantics5Riscv5Instr5mulop00C47Corelib4Init9Datatypes8list_indc79OSSVerify5KrLib2K52AS<AsanPlanCore3APC5a_brkC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC4a_fdC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3sndc79OSSVerify5KrLib2K52AS<AsanPlanCore3APC7am_baseC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC6am_lenC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX26a_baseC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC4a_ssC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX26s_regsC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC2knC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC6a_mapsC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC5a_visC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC7a_ghostC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2K52AS:AxSymExec33AX25ptree01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC?live_agree_exprC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2K52AS:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC?live_agree_foldC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC9live_varsC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC;live_vars_tC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2K52AS:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~i79OSSVerify5KrLib2K52AS<AsanPlanCore3APC4amap00C1?~~~~~~~~~~~~~~~i79OSSVerify5KrLib2K52AS<AsanPlanCore3APC3acs00C1?~~~~~~~~~~~~~~~i79OSSVerify5KrLib2K52AS<AsanPlanCore3APC3afd00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2K52AS:AxSymExec33AX25saddr00C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC46Stdlib5Lists4List2InI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsC56Stdlib5Arith8PeanoNat3Nat6eqb_eqC46Stdlib5Lists4List>forallb_forallC47Corelib4Init5Logic5proj1C46Stdlib4Bool4Bool;andb_true_rC46Stdlib4Bool4Bool:andb_assocC46Stdlib5Lists4List7forallbI47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C56Stdlib5Arith8PeanoNat3Nat3ltbC56Stdlib5Arith8PeanoNat3Nat3lebc79OSSVerify5KrLib2K52AS<AsanPlanCore3APC?expr_all_live_tC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APCAforallb_expr_varsC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC8all_liveC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC3regC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX29split_litC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC=kn_gc_entry_tC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6filterc79OSSVerify5KrLib2K52AS<AsanPlanCore3APC6set_knC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC;kn_gc_entryC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC?live_vars_agreeC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2K52AS:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX28expr_eqbC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4negbK79OSSVerify5KrLib2K52AS:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2K52AS:AxSymExec33AX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2K52AS:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APCBexpr_all_live_t_eqC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2K52AS:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2K52AS:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2K52AS:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2K52AS:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2K52AS:AxSymExec33AX26kentry09C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2K52AS:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:filter_extC35stdpp7tactics<f_equal_helpc79OSSVerify5KrLib2K52AS<AsanPlanCore3APC5cs_gcC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC9cs_gc_refC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC8fresh_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX26s_knowC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX28facts_ofC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B4mkbcC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B6mk_kixC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX24s_pcC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX26s_nextC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2K52AS:AxSymExec33AX29sym_state01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B<sym_execTXBIC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX25s_logC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B6carryKC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC5mk_ssC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC7with_ssC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX2:sym_execTXC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX25carryC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B?sym_execTX_knowC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B9carryK_eqC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B?sym_execTXBI_eqC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC9run_blockC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC=run_block_refC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2K52AS:AxSymExec33AX28sidecond00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2K52AS:AxSymExec33AX26sentry00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2K52AS:AxSymExec33AX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B4bctx00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC?kentry_apart_bBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC>kentry_apart_bC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX2>ranges_apart_xC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3ltbC79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B?ranges_apart_xBC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2BCranges_apart_xB_eqfC1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityK47Corelib7Numbers7BinNums1Z01C79OSSVerify5KrLib2K52AS:AxSymExec33AX25two64C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC@kentry_apart_bpBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC?kentry_apart_bpC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX2>ranges_apart_pC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B?ranges_apart_pBC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2BCranges_apart_pB_eqfC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2K52AS:AxSymExec33AX25sprep00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC:kn_unfillBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC9kn_unfillC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC6kimg_bC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B9mk_sprepBC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B5bc_fkC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX28mk_sprepC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B:bc_fk_mkbcC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B=mk_sprepB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APCDkentry_apart_bpB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC>kn_unfillB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC:kn_unfillMC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC7havoc1BC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC6havoc1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC5kwr_bC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B:kzero_cutBC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B:kfill_cutBC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B9kunk_cutBC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX29kzero_cutC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX29kfill_cutC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX28kunk_cutC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B>kzero_cutB_eqfC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B>kfill_cutB_eqfC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B=kunk_cutB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APCCkentry_apart_bB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC8havoc1pBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC7havoc1pC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC9kn_havocBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC8kn_havocC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC<havoc1pB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC=kn_havocB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC9kn_havocMC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC8kwr_cutBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC7kwr_cutC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX24kcutC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B5kcutBC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B9kcutB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC8cutout1BC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC7cutout1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC<kwr_cutB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC9cutout1pBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC8cutout1pC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC:kn_cutoutBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC9kn_cutoutC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC=cutout1pB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC>kn_cutoutB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC:kn_cutoutMC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC7kreadZBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC6kreadZC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX2;know_lookupC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B<know_lookupBC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B@know_lookupB_eqfC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2K52AS:AxSymExec33AX24lres00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC8kread8eBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC7kread8eC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC:kwritableBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC9kwritableC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B4xloBC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B8xinsideBC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX23xloC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX27xinsideC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B8xloB_eqfC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B<xinsideB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC<kwritable_xBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC;kwritable_xC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B4xhiBC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX23xhiC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B8xhiB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC8kzero_xBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC7kzero_xC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC8kfill_xBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC7kfill_xC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3eqbK47Corelib7Numbers7BinNums8positive03c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC<off_image_xBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC;off_image_xC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC6img_loC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC6img_hiC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC7flat_xBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC6flat_xC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B;base_rangeBC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX2:base_rangeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B?base_rangeB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC8len_eqbBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC7len_eqbC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX27lin_ge0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B8lin_ge0BC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B<lin_ge0B_eqfC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C79OSSVerify5KrLib2K52AS:AxSymExec33AX26xtermsC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC=page_alignedBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC<page_alignedC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX26ealignC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B7ealignBC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B;ealignB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC5xlo1BC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC4xlo1C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX2:lin_brangeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX26zlit64C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B7erangeBC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B;lin_srangeBC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX26erangeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX2:lin_srangeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B;erangeB_eqfC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B?lin_srangeB_eqfC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B;lin_brangeBC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B?lin_brangeB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC5xhi1BC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC4xhi1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3minc79OSSVerify5KrLib2K52AS<AsanPlanCore3APC4xb2BC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC3xb2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC5deandC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC9xlo1B_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC9xhi1B_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC5xlo2BC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC4xlo2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC8xb2B_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC5xhi2BC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC4xhi2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC<kread_bytesBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC;kread_bytesC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC;kreadZB_eqfC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indc79OSSVerify5KrLib2K52AS<AsanPlanCore3APCAkread_bytesB_eqf'C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC@find_containingBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC?find_containingC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC6is_fogC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC7am_kindC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC9mkind_eqbC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4findi79OSSVerify5KrLib2K52AS<AsanPlanCore3APC5mkind00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC;xinside_shBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC:xinside_shC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APCCfind_containing_shBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APCBfind_containing_shC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC?xinside_shB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC:shadow_ofBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC9shadow_ofC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX25mkSrlC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC:shadow_offC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC4eaddC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B6mkSrlBC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B:mkSrlB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC=shadow_factsBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC<shadow_factsC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APCGfind_containing_shB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC>shadow_ofB_eqfC1?~~~~~~~~~~~~~~~k79OSSVerify5KrLib2K52AS<AsanPlanCore3APC5mkind02C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC;shd_end_okBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC:shd_end_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powc79OSSVerify5KrLib2K52AS<AsanPlanCore3APC3nxtC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC<expr_vars_ltC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC7flat_xeC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC8slice_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APCAshadow_apart_eachC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC7a_eagerC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC8a_abytesC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC8vis_costC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC2pcC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appc79OSSVerify5KrLib2K52AS<AsanPlanCore3APC7a_totszC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC5a_yloC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC8a_tidsetC1?~~~~~~~~~~~~~~~k79OSSVerify5KrLib2K52AS<AsanPlanCore3APC3acs01C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC?shd_end_okB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APCAshadow_factsB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC;flat_xB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC7vis_addC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC;vis_add_refC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC9sw_off_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC6add_knC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC;node_shdisjC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC?node_shdisj_refC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC7reg_litC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC7page_upC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC8mmap_lenC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC<mmap_len_refC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC<inside_mapsBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC;inside_mapsC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC;safe_rangeBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC:safe_rangeC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC:sw_trackedC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC@inside_mapsB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC6e_bandC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC7BANDLENC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC5SW_LOC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC3KHIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC=grant_keep_bBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC<grant_keep_bC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC?safe_rangeB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC@kn_grant_filterBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC?kn_grant_filterC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC9kimg_clipC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APCAgrant_keep_bB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC@kn_grant_filterMC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APCDkn_grant_filterB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC:null2_cs1MC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC9null2_cs1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC6escaleC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX26sr_updC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC<null2_kfactsC1?~~~~~~~~~~~~~~~k79OSSVerify5KrLib2K52AS<AsanPlanCore3APC4amap01C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC9add_entryC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APCCkn_grant_filterM_eqC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC:kn_rezeroBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC9kn_rezeroC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC>kn_rezeroB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC:kn_rezeroMC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC=fixed_args_inC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APCDfind_containingB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC=fixed_in_argsC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APCAfixed_in_args_refC1?~~~~~~~~~~~~~~~i79OSSVerify5KrLib2K52AS<AsanPlanCore3APC<fixed_in_arm00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC7ATOPMAXC1?~~~~~~~~~~~~~~~k79OSSVerify5KrLib2K52AS<AsanPlanCore3APC5mkind01C1?~~~~~~~~~~~~~~~k79OSSVerify5KrLib2K52AS<AsanPlanCore3APC5mkind03C1?~~~~~~~~~~~~~~~k79OSSVerify5KrLib2K52AS<AsanPlanCore3APC5mkind04C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC9budget_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC6rekindC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC=mmap_fixed_inC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APCAmmap_fixed_in_refC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC:dest_lfactC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC:dest_rfactC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC4esubC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC=replace_entryC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APCCmmap_destroyed_withC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APCGmmap_destroyed_with_refC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC:ENOMEM_RETC1?~~~~~~~~~~~~~~~k79OSSVerify5KrLib2K52AS<AsanPlanCore3APC5mkind06C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC=node_mprotectC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APCAnode_mprotect_refC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC;amap_matchBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC:amap_matchC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC<len_eqbB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APCApage_alignedB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC<kzero_xB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC?amap_matchB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC;node_munmapC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC?node_munmap_refC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC=kn_unfillM_eqC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC8vis_hereC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC:node_unvisC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC>node_unvis_refC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC7ret_litC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC:after_callC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC8kimg_cutC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC@off_image_xB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC@kwritable_xB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC<summary_fillC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC@summary_fill_refC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC<kn_havocM_eqC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC;copy_factsBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC:copy_factsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX2>zbytes_le_to_ZC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC<kread8eB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC@kread_bytesB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC@copy_factsB_eqf'C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3mulC47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z3divC47Corelib5Lists7ListDef3seqc79OSSVerify5KrLib2K52AS<AsanPlanCore3APC<kblob_prefixC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC?copy_factsB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC<summary_copyC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC@summary_copy_refC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC;after_call2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC3NCSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC;x_memiszeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC5eaddzC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC>kwritableB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC;summary_mizC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC?summary_miz_refC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC8img_covBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC7img_covC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC:x_istrncpyC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC8x_sealedC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC@summary_istrncpyC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APCDsummary_istrncpy_refC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC8SEALED_WC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC7x_sniffC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC9sniff_tabC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC:sniff_cellC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B<kn_readableBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC=kn_readable_xC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B5extKBC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX2;kn_readableC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS:AxSymExec33AX24extKC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B@kn_readableB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC<img_covB_eqfC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS;AxSymExec3B4AX2B9extKB_eqfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC=summary_sniffC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APCAsummary_sniff_refC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2K52AS<AsanPlanCore3APC6nt_setC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthc79OSSVerify5KrLib2K52AS<AsanPlanCore3APC6nt_getC1?~~~~~~~~~~~~~~~".   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Set Keyed Unification.
Import ListNotations.
Open Scope Z_scope.

Module APC.
Import AX2. Import AX2B.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition CEIL : Z := 0x7fff7f800000.
(* [comment removed for export] *)
Definition KHI : Z := 0x10007fff8000.
(* [comment removed for export] *)
Definition FLOOR : Z := 0x2aaaaaaab000.
(* [comment removed for export] *)
Definition MBASE_MIN : Z := 0x154555557000.
(* [comment removed for export] *)
Definition PID_MAX : Z := 4194304.
(* [comment removed for export] *)
Definition ATOPMAX : Z := 0x7fffff800000.
(* [comment removed for export] *)
Definition SW_LO : Z := 0x7fff7000.
(* [comment removed for export] *)
Definition e_band : expr := mkAlu ALU_ADD (mkAlu ALU_ADD (mkMd M_MUL (ELit 32768) (EVar 0)) (mkMd M_MUL (ELit 16) (EVar 6))) (ELit (-8388608)).
Definition BANDLEN : Z := 0x80800000.

Record atable : Type := AT {
  img_lo : Z; img_hi : Z;          (* [comment removed for export] *)
  n_res : nat;                     (* [comment removed for export] *)
  shadow_off : Z;                  (* [comment removed for export] *)
  a_entry : Z;                     (* [comment removed for export] *)
  rw_lo : Z; rw_len : Z;           (* [comment removed for export] *)
  ph_addr_z : Z; ph_ent_z : Z; ph_num_z : Z;   (* [comment removed for export] *)
  (* [comment removed for export] *)
  x_imemset : Z; x_imemcpy : Z; x_memset : Z; x_memcpy : Z; x_memiszero : Z;
  (* [comment removed for export] *)
  x_istrncpy : Z; x_sealed : Z; x_popfree : Z;
  (* [comment removed for export] *)
  x_sniff : Z; sniff_tab : Z; sniff_cell : Z;
  (* [comment removed for export] *)
  x_envscan : Z; x_envscan_k : Z; x_pnscan : Z; x_pnscan_k : Z;
  stops_more : list Z;             (* [comment removed for export] *)
  (* [comment removed for export] *)
  x_hsort : Z
}.

Section WithSegs.
Variable segs : list Segment.
Variable IT : itab.
Variable A : atable.
Variable nx0 : nat.     (* [comment removed for export] *)
Variable LIMIT : Z.     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive spiece : Type := SPLit (bs : list Z) | SPBlob (k : nat).

Inductive shape : Type :=
| SNil
| SExit (code : Z)
| SEmitP (fd : Z) (ps : list spiece) (s : shape)   (* [comment removed for export] *)
| SAlt2 (a b : shape)
| SCase (e : expr) (mid : Z) (s1 s2 : shape)
| SHole (h : nat)                            (* [comment removed for export] *)
| SNext.                                     (* [comment removed for export] *)


Fixpoint listZ_eqb (x y : list Z) : bool :=
  match x, y with [], [] => true | a :: x', b :: y' => Z.eqb a b && listZ_eqb x' y' | _, _ => false end.
Definition spiece_eqb (x y : spiece) : bool :=
  match x, y with SPLit a, SPLit b => listZ_eqb a b | SPBlob k, SPBlob k' => Nat.eqb k k' | _, _ => false end.
Fixpoint spieces_eqb (x y : list spiece) : bool :=
  match x, y with [], [] => true | a :: x', b :: y' => spiece_eqb a b && spieces_eqb x' y' | _, _ => false end.
Fixpoint shape_eqb (x y : shape) : bool :=
  match x, y with
  | SNil, SNil => true
  | SExit c, SExit c' => Z.eqb c c'
  | SEmitP fd ps s, SEmitP fd' ps' s' => Z.eqb fd fd' && spieces_eqb ps ps' && shape_eqb s s'
  | SAlt2 a b, SAlt2 a' b' => shape_eqb a a' && shape_eqb b b'
  | SCase e m a b, SCase e' m' a' b' => expr_eqb e e' && Z.eqb m m' && shape_eqb a a' && shape_eqb b b'
  | SHole h, SHole h' => Nat.eqb h h'
  | SNext, SNext => true
  | _, _ => false
  end.

(* [comment removed for export] *)
Definition salt2 (a b : shape) : shape :=
  match a, b with SNil, _ => b | _, SNil => a | _, _ => if shape_eqb a b then a else SAlt2 a b end.

(* [comment removed for export] *)
Definition hole_of (h : nat) : nat := Nat.modulo h 1000.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive mkind : Type := KRW | KRWLAZY | KNONE | KNONELAZY | KFOG | KHOLE.   (* [comment removed for export] *)

Definition mkind_eqb (a b : mkind) : bool :=
  match a, b with
  | KRW, KRW | KRWLAZY, KRWLAZY | KNONE, KNONE | KNONELAZY, KNONELAZY | KFOG, KFOG | KHOLE, KHOLE => true
  | _, _ => false
  end.

(* [comment removed for export] *)
Record amap : Type := AM {
  am_base : expr;       (* [comment removed for export] *)
  am_len  : expr;       (* [comment removed for export] *)
  am_kind : mkind
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition is_tok_kind (k : mkind) : bool := match k with KFOG | KHOLE => true | _ => false end.
(* [comment removed for export] *)
Definition mkind_lazy (k : mkind) : bool := match k with KRWLAZY | KNONELAZY => true | _ => false end.
Definition is_hole (m : amap) : bool := mkind_eqb (am_kind m) KHOLE.
Definition is_fog (m : amap) : bool := is_tok_kind (am_kind m).
Definition no_fog (ms : list amap) : bool := forallb (fun m => negb (is_fog m)) ms.
Definition no_holes (ms : list amap) : bool := forallb (fun m => negb (is_hole m)) ms.


(* [comment removed for export] *)
Inductive afd : Type :=
| FdStd                                   (* [comment removed for export] *)
| FdFile (k : nat) (len off : expr)       (* [comment removed for export] *)
| FdDir.                                  (* [comment removed for export] *)

Record acs : Type := ACS {
  a_ss    : sym_state;          (* [comment removed for export] *)
  a_maps  : list amap;          (* [comment removed for export] *)
  a_totsz : Z;                  (* [comment removed for export] *)
  a_ylo   : Z;                  (* [comment removed for export] *)
  a_eager : Z;                  (* [comment removed for export] *)
  a_vis   : list (expr * expr); (* [comment removed for export] *)
  a_ghost : list (expr * expr); (* [comment removed for export] *)
  a_abytes : Z;                 (* [comment removed for export] *)
  a_brk   : expr;               (* [comment removed for export] *)
  a_fd    : afd;
  a_tidset : bool               (* [comment removed for export] *)
}.

Definition reg (cs : acs) (n : nat) : expr := nth n (s_regs (a_ss cs)) (ELit 0).
Definition kn (cs : acs) : list kentry := s_know (a_ss cs).
Definition pc (cs : acs) : Z := s_pc (a_ss cs).
Definition nxt (cs : acs) : nat := s_next (a_ss cs).

Definition with_ss (cs : acs) (ss : sym_state) : acs :=
  ACS ss (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).
Definition mk_ss (p : Z) (sr : list expr) (k : list kentry) (nx : nat) : sym_state := SS p sr [] k nx.
Definition set_reg (cs : acs) (n : nat) (e : expr) : acs :=
  let ss := a_ss cs in with_ss cs (mk_ss (s_pc ss) (sr_upd (s_regs ss) n e) (s_know ss) (s_next ss)).
Definition set_pc (cs : acs) (p : Z) : acs :=
  let ss := a_ss cs in with_ss cs (mk_ss p (s_regs ss) (s_know ss) (s_next ss)).
Definition set_kn (cs : acs) (k : list kentry) : acs :=
  let ss := a_ss cs in with_ss cs (mk_ss (s_pc ss) (s_regs ss) k (s_next ss)).
Definition add_kn (cs : acs) (k : list kentry) : acs := set_kn cs (k ++ kn cs).
Definition bump (cs : acs) (d : nat) : acs :=
  let ss := a_ss cs in with_ss cs (mk_ss (s_pc ss) (s_regs ss) (s_know ss) (s_next ss + d)).
Definition set_regs (cs : acs) (sr : list expr) : acs :=
  let ss := a_ss cs in with_ss cs (mk_ss (s_pc ss) sr (s_know ss) (s_next ss)).

Definition lit_of (e : expr) : option Z := match e with ELit z => Some (z mod two64) | _ => None end.
Definition reg_lit (cs : acs) (n : nat) : option Z := lit_of (reg cs n).

(* [comment removed for export] *)
Definition eadd (a b : expr) : expr := mkAlu ALU_ADD a b.
Definition esub (a b : expr) : expr := mkAlu ALU_SUB a b.
Definition escale (c : Z) (e : expr) : expr := mkMd M_MUL (ELit c) e.
Definition eaddz (a : expr) (z : Z) : expr := mkAlu ALU_ADD a (ELit z).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint expr_vars (e : expr) (acc : list nat) : list nat :=
  match e with
  | ELit _ => acc
  | EVar n => if existsb (Nat.eqb n) acc then acc else n :: acc
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars x (expr_vars y acc)
  | EExt _ _ _ x => expr_vars x acc
  | EBlob _ _ _ _ => acc
  end.

Definition live_vars (cs : acs) : list nat :=
  let acc := fold_right expr_vars [] (s_regs (a_ss cs)) in
  let acc := fold_right (fun K acc => match K with
                                      | KWord a _ v => expr_vars (a_base a) (expr_vars v acc)
                                      | KZero a n => expr_vars (a_base a) (expr_vars n acc)
                                      | KBlob a n _ => expr_vars (a_base a) (expr_vars n acc)
                                      | KWr a n => expr_vars (a_base a) (expr_vars n acc)
                                      | KFill a n _ => expr_vars (a_base a) (expr_vars n acc)
                                      | KUnk a n => expr_vars (a_base a) (expr_vars n acc)
                                      | _ => acc end) acc (kn cs) in
  let acc := fold_right (fun m acc => expr_vars (am_base m) (expr_vars (am_len m) acc)) acc (a_maps cs) in
  let acc := fold_right (fun p acc => expr_vars (fst p) (expr_vars (snd p) acc)) acc (a_vis cs) in
  let acc := fold_right (fun p acc => expr_vars (fst p) (expr_vars (snd p) acc)) acc (a_ghost cs) in
  let acc := match a_fd cs with FdFile _ l o => expr_vars l (expr_vars o acc) | _ => acc end in
  expr_vars (a_brk cs) acc.

Definition all_live (live : list nat) (e : expr) : bool :=
  forallb (fun v => Nat.ltb v nx0 || existsb (Nat.eqb v) live) (expr_vars e []).

Definition kn_gc_entry (spb : expr) (spk : Z) (live : list nat) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => negb (expr_eqb b spb && Z.leb (k + Z.of_nat w) spk)
  | KZero (SA b k) (ELit n) => negb (expr_eqb b spb && Z.leb (k + n) spk)
  | KBlob (SA b k) (ELit n) _ => negb (expr_eqb b spb && Z.leb (k + n) spk)
  | KFill (SA b k) (ELit n) _ => negb (expr_eqb b spb && Z.leb (k + n) spk)
  | KUnk (SA b k) (ELit n) => negb (expr_eqb b spb && Z.leb (k + n) spk)
  | KRange e _ _ => all_live live e
  | KAlign e _ => all_live live e
  | KDisj a1 n1 a2 n2 => all_live live (a_base a1) && all_live live n1 && all_live live (a_base a2) && all_live live n2
  | _ => true
  end%bool.

Definition cs_gc_ref (cs : acs) : acs :=
  let '(spb, spk) := split_lit (reg cs 2) in
  let live := live_vars cs in
  set_kn cs (List.filter (kn_gc_entry spb spk live) (kn cs)).

(* [comment removed for export] *)
Definition vkey (n : nat) : positive := Pos.of_succ_nat n.
Fixpoint expr_vars_t (e : expr) (acc : ptree unit) : ptree unit :=
  match e with
  | ELit _ => acc
  | EVar n => pt_set (vkey n) tt acc
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars_t x (expr_vars_t y acc)
  | EExt _ _ _ x => expr_vars_t x acc
  | EBlob _ _ _ _ => acc
  end.
Definition live_vars_t (cs : acs) : ptree unit :=
  let acc := fold_right expr_vars_t PTLeaf (s_regs (a_ss cs)) in
  let acc := fold_right (fun K acc => match K with
                                      | KWord a _ v => expr_vars_t (a_base a) (expr_vars_t v acc)
                                      | KZero a n => expr_vars_t (a_base a) (expr_vars_t n acc)
                                      | KBlob a n _ => expr_vars_t (a_base a) (expr_vars_t n acc)
                                      | KWr a n => expr_vars_t (a_base a) (expr_vars_t n acc)
                                      | KFill a n _ => expr_vars_t (a_base a) (expr_vars_t n acc)
                                      | KUnk a n => expr_vars_t (a_base a) (expr_vars_t n acc)
                                      | _ => acc end) acc (kn cs) in
  let acc := fold_right (fun m acc => expr_vars_t (am_base m) (expr_vars_t (am_len m) acc)) acc (a_maps cs) in
  let acc := fold_right (fun p acc => expr_vars_t (fst p) (expr_vars_t (snd p) acc)) acc (a_vis cs) in
  let acc := fold_right (fun p acc => expr_vars_t (fst p) (expr_vars_t (snd p) acc)) acc (a_ghost cs) in
  let acc := match a_fd cs with FdFile _ l o => expr_vars_t l (expr_vars_t o acc) | _ => acc end in
  expr_vars_t (a_brk cs) acc.
Definition in_live_t (t : ptree unit) (v : nat) : bool :=
  match pt_get t (vkey v) with Some _ => true | None => false end.
Fixpoint expr_all_live_t (t : ptree unit) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => if Nat.ltb n nx0 then true else in_live_t t n
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => if expr_all_live_t t x then expr_all_live_t t y else false
  | EExt _ _ _ x => expr_all_live_t t x
  | EBlob _ _ _ _ => true
  end.
Definition kn_gc_entry_t (spb : expr) (spk : Z) (t : ptree unit) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => negb (expr_eqb b spb && Z.leb (k + Z.of_nat w) spk)
  | KZero (SA b k) (ELit n) => negb (expr_eqb b spb && Z.leb (k + n) spk)
  | KBlob (SA b k) (ELit n) _ => negb (expr_eqb b spb && Z.leb (k + n) spk)
  | KFill (SA b k) (ELit n) _ => negb (expr_eqb b spb && Z.leb (k + n) spk)
  | KUnk (SA b k) (ELit n) => negb (expr_eqb b spb && Z.leb (k + n) spk)
  | KRange e _ _ => expr_all_live_t t e
  | KAlign e _ => expr_all_live_t t e
  | KDisj a1 n1 a2 n2 => expr_all_live_t t (a_base a1) && expr_all_live_t t n1 && expr_all_live_t t (a_base a2) && expr_all_live_t t n2
  | _ => true
  end%bool.
Definition cs_gc (cs : acs) : acs :=
  let '(spb, spk) := split_lit (reg cs 2) in
  let live := live_vars_t cs in
  set_kn cs (List.filter (kn_gc_entry_t spb spk live) (kn cs)).

(* [comment removed for export] *)
Definition live_agree (acc : list nat) (t : ptree unit) : Prop :=
  forall v, existsb (Nat.eqb v) acc = in_live_t t v.
Lemma vkey_inj : forall a b, vkey a = vkey b -> a = b.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01Hh11ni001nh21ah31bh41tp;1p;3p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000NR1p4p710p8P0P1p4p7210p8g000kj16Tg001kj30Tg002Ej12Tg002lj64Tg003IR1j13Tg003kj11Tg004Jj17Tg0053j65Tg005OR0g005nR2f1R3#6f0R4#630P2P0P1f2#2R1%23R3P4E4%31R1%33500P0f3R3#2#3R2A0042X10P4%13R5%73R3E5A0051P0P2f5#1R2=004X10P4P5P3E5f4#1R3=005P0P0P0P0P4f6P4n0110000020010000X40P2P3P4E4b0b0b0W0X30W2o"). Qed.
Lemma live_agree_var : forall acc t n,
  live_agree acc t -> live_agree (if existsb (Nat.eqb n) acc then acc else n :: acc) (pt_set (vkey n) tt t).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bi001bh11Eh21ei011eh31oh41vh51Hh62HKh72NEh83acch91ni021nh:2n0h;1ri031rh<1si041sh=1ti051ui061xp;1p;2p;3p;6p;4p-1R0p1006SR1p4p710p8P0P1p4p7210p8P0p1006oR1p4p710p8P0P1p4p7210p8P0p1007Lp4p7210p8P0p1007jp4p7210p8P0g008IR0p4p710p8p1008ep4p70R1p1009dp4p710p8P1p100:Gp4p710p8P1p100;3R2p4p7210p8P1P2p4p710p8P1p100;gp4p710p8P1p100<Wp4p710p8g00=OR1p4p710g00>OR2p4p710R3p8g00>mR4p4p710P3p8p100?mp4p710P3p8g00A2j1RTg00ARj1QTg00BSj2ATg00CYj2ETg00D<j19Tg00DUR3j2MTg00E5j11j2>Tg000kj14Tg00EUj37Tg00FUR5j1PTg00G7j2OTg00GYj2=Tg001kj35Tg00H3j2?Tg00HPj1KTP2j6<TP1j4JTg00I5j2ITg00IZR1j2HTg00J=j2GTg00J\j2@Tg0053j6FTg00Kaj3LTP4j6DTP0j3BTg00Lej3NTg00MEj4CTg005OR0f1R4f0R235p=6AB042p=0AN042p=2g00NER6P4g00NeR7P2CCp=:g00OER8f2R9=B04;52p=3A5842p=8g00OeR:9582p=;%R0R;%Q61A941E291629R<%9<'MP3f3R3,64R<%9<%19R<P8P;f4R=#1R>f6R?'0P?12=?n0100000020000P5P6P8%4=f5R@':%49RA576P:g00PERBn1011060002101050033P2169=RCP0P@%12RDP8P;%1?REf8RF'0RGPF12?FRHn0100000020000RIP5P6P8%4?f7RJ':%42576P:PBn1011060002101050033X40%P6RK1O67P5P6P8P2P:PBn10110600021010500RL93EIX3K%1@RE/0JRMP81=8218G2P8%1FRGf:RN;32f9RO#1RPP8P;P4f;RQ12OQn0100000020000'0#;]1P4%1J/0ORR#;P2W1A58RBP8P:10PQ,?2#;X081=8:1>FF%KFE<12FN,0G#;eW1n0110000020000P2O1b1b0%4@RN/:?RQ=76NP6PNP7P?CJE<P3P2E<W2P2O1%9CPK%43RC976?RP10>IRI/8LX3KP8%13RK/0J18I2X08PMP8P8P8P;P2PO12JOn010000002000010EO53EP210>FRE,=81I=?16=?1>=?'H1>@JP8P116?Ff<,0GRG,?4/8GP416JORO1?:G/8GP@P2O1'GW2P2O1%9O1=8GW:P2O1n10210010300021010110102b0b;A3>HEen0110000020000b01@?3P=P3O1EFP8P;PMPJ12@Jn0100000020000P5P6P8PPP:PBn1011060002101050053KeA76QCP6PCPNP7P?g005n?5CNRCP4AL=?2O1W6%9CeEDE<W7P2O1n200110400021010111102b<P8P;10<=P=129=n01000000200001:A3/@253DeX40P8P;%14/03P31243n0100000020000%44/:9'AeW5X90W=W8o"). Qed.
Lemma live_agree_expr : forall e acc t, live_agree acc t -> live_agree (expr_vars e acc) (expr_vars_t e t).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h03acch11th21Hh34IHe1h44IHe2h52e1h62e2h72oph81eh91nh:2sxh;3IHeh<1ih=1kh>2loh?1zp;1p;2p;4p;3p;:g00A2j1?Tg00ARj1>Tg00BSj23Tg00Pej1=Tg00Qej47Tg00Roj16Tg00Soj21Tg00U4j22Tg00V;j35Tg00W;j34Tg00X;j38Tg00Y;j39Tg00Z;j4<Tg00[;j4:Tg00\;l:;Tf3R0f2R1'1f1R2f0R3'2'3p=0g00]=R4g005OR5#?R6g00NE#>R71323R8P0P1P0P2C0[]1]0R9X84g00^=R:P3%=0R;P1P;P2C0eX28X17X06W?P1P2P0P3C7%60R;P1P;P2C0eX28X17X06X95g00^[R;f5R<f4R=/1112=2P0P1P2P3O3R>O3R?f7R@f6RA;5=RBP1PBP2C0eX28X17X06X49X64X39X54W7P?A4@A=RBP1PBP2C0eX28X17X06X49X64X39X54X7;g00_GR;P?A8@A=RBP1PBP2C0eX28X17X06X49X64X39X54W7P?A9@A=R?P1P?P2C0eX28X17X06X49X64X39X54X7;g00OER;P>P@PAP<P=C<R@P1P@P2C0eX28X17X06X;9X84X95X>5W:P3PAP<P=P0C:R0P1P0P2C0eX28X17X06X95X<:X=5X:;P3M:;W8o"). Qed.
Lemma live_agree_fold : forall (X : Type) (f : X -> list nat -> list nat) (g : X -> ptree unit -> ptree unit) (l : list X) acc t,
  (forall a acc t, live_agree acc t -> live_agree (f a acc) (g a t)) ->
  live_agree acc t -> live_agree (fold_right f acc l) (fold_right g t l).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01ah13acch21lh31th41Hh53Hfgh62IHh71Xh81fh91gh:1rp;1p;2p;5p;3p200R0g00`3R1p4p710p8P0g007jR2p4p7210p8g00A2j12Tg00ARj15Tg00BSj21TP2j50Tg00Lej34TP1j53Tf0R1g005O#2R2P2[[f1R3g00NE#5R4P4[[f2R5#2f5R61131f8R7f3R8P5O2f7R9P8P3O2'1[^34^12]01153P9%29P2P7P9f4R:P1D0P4P7f6R;P8P1D0'1W2P1%27P2f9R8P7P6P1D0P4P8P9P:P1D0'1P:P5P2f:R<P8P;P3D0P4P<P7P6P3D0P1O4P2P<P8P;A4<53R5D0P4P<P7P6P5D0'1eW6W:X09P:D3W4W5X34X12W2W9W8X70o"). Qed.
Lemma live_vars_agree : forall cs, live_agree (live_vars cs) (live_vars_t cs).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h03acch11ai001ah21ni011nh31th47a_base0h56a_off0h61ki021kh71mi031mh81vi041vh91Hh:1Ki051Kh;1ci061ch<1ei071eh=2hii082hih>2loi092loh?1ph@1wi0:1whA2A0hB2A5hC2a1i0;2a1hD2a2i0<2a2hE2cshF3leni0=3lenhG2n1i0>2n1hH2n2i0?2n2hI1oi0@1ohJ3offi0A3offi0B6a_basei0C5a_offi0D1li0E1si0F1ui0G1xp;1p;2p;3p;5p;6p;4p;8g00`Uj1[Tg00A2j1ZTg00aVj1GTg00bVj2RTg000Nj3KTg00c6j3ITg00cSj1FTg00dVj1ETg00eXj1:Tg00fXj1QTg00g8j1<Tg00h8j1;Tg00i8j1ATg00j6j1@Tg00k8j1?Tg007jj50Tg00l9j1>Tg00ARj1WTg00m<j1VTg00FUR0j1UTg00n=j1TTg00E5j1HTg008Ij3DTg001kj3CTg00GYj2STg000kj1PTg00EUj3NTg00?mj2MTg00>Oj6LTg00J\j2OTg00BSj25Tg00SoR1j22Tg00U4R2j21Tg00n_j43Tg00ojj2JTg010kj89Tg0126j1YTg013;j1XTf2R3f1R4f0R5'2'2p=4P3g00]=R6P1P4P5D0p=Bf3R7g014BR8P3P4P5D0p=8P7g015DR9P3P4P5D0p=71145,13p=6P3P6P2P4P5D0p==g016F%[5g017GR:g005OR;#ZR<%G5R=P<1R66R>AK664R?AI664R@;45X0<X?>RAP<P>PAP<%F4RB%E4RC;45X0<X79RDP<P8P<P4%:3RE?457%:4RF?453RGA4E47RHP3P3P7PGf4RIPHPGn01105000:3010010:1042010010130100101102201091082010710330107109108201001014010;10>10<10?3010010110620100101X0<X:8RG%Q;RH%<5#;RJ5B<%A5RKC8%@5RLC7%?5RMD0%>5RND0ROP<P>PAP<P>PAP<PDP<PG%<7#;RP9B<H%A7RQC8%@7RRC7%?7RSD0%>7RTD09445POn0110G0003003010210D10@00P:g00NERO#WRUP=PUP>A6?@5X0UX?>R@PUP>P@PUA6BC5X0UX79RCPUP8PUP4A6E57A6F53RBA6E47R?P3P3P7PBPIP?PBn01105000:3010010:1042010010130100101102201091082010710330107109108201001014010;10>10<10?3010010110620100101X0UX:8RB%VOR?==UJPKC8PLC7PMD0PND0RNPUP>P@PUP>P@PUPCPUPBA=U?PPQC8PRC7PSD0PTD09645PNn0110G0003003010210D10@00%UORN%TOg00OERT%H4=D;HP0POPTP5g00Oeg00PER0n10110G00021010F003CXIN1ST0%P5R09NO?1MO0EL%H5=D;H1O?55CTeX8;15H?RTePT1545RT%GIR0P:P:P:P<P5PIf7RO,25RN,24PIn0110G0003003010210D10@00P:PUP5P7f6RS,15RR,14P7n0110G0003003010210D10@00'5P5P4P4f9RQ,25RPf8RM,15RLP5PQPMPOC3C3XJ6XF6X6;P3P4P5O3P4n011000003003010210=10A00b1W9X3UX0<P:P<P0P3f5RK,25RJ,24P3n0110G0003003010210D10@00P:PUP0P4115IR0,14P4n0110G0003003010210D10@00'5\T^3U^0<P5P<P>PAP<P>PAP<PDP<PG%<3#;R:9B<HR=%A3RVC8RW%@3RXC7RY%?3RZD0R[%>3R\D0PUP>P@PUP>P@PUPCPUPBA=U?:R]PVC8R^PXC7R_PZD0R`P\D0P>PAP@P\P[P`AK667AI667R`/2311`4P`P3P4P5C3C3VTX3UX0<X1>R`P>PAP@PZPYP_P`P9PDPCPXPWP^%F7%E7R^/2311^4P^P3P4P5C3C3VTX3UX0<X19P8PGPBPVP=P]P8P8P<P5A4E5S12FJRJA4E4SR]PKPKPSPJPOP]PJn01105000:3010010:1042010010130100101102201091082010710330107109108201001014010;10>10<10?3010010110620100101P8PUP5A6E5K11F0R0A6E4KRJPIPIPKP0PSPJP0n01105000:3010010:1042010010130100101102201091082010710330107109108201001014010;10>10<10?3010010110620100101'5P7g018HR0P012EP11EL'5^86^@;P5g00^=RL1J73#:RPf<RJ,25f;RK,15P5PJPKf:R]C3C3X86X@;W5X46P4P5O2n0110E00012010B10CW1P3P4P5O3P012FN11FR'5^26P51J34#:125]115QP5P]PQPMC3C3X26X5LX46P4P5O2n0110E00012010B10CX10P4P5O2RRP0A4E4QA6E4M'5RE^6;^26P5PP124J114KP4PJPKP]C3C3R]X6;X26X5LX46P4P5O2n0110E00012010B10CX10P3P4P5O3PIX=LX>LP4P5O2PIX7LX<6P4P5O2PSX=LX>LX<6P3P4P5O3PRPMXH6XD0XG6XC0P7P3P4P5O4P0PE^;L^26P5P]X;LX26X5LX46P4P5O2n0110E00012010B10CX10P3P4P5O3PRn01102000:3010010:1042010010130100101102201091082010710330107109108201001014010;10>10<10?3010010110620100101X9TX3UX0<X18P6P1P2P:PHP?P7P3P4P5C3VTX3UX0<X16P4G9G9G9G9G9O3bBbAC3%Y5%X5'5eWEo"). Qed.
Lemma forallb_expr_vars : forall P e acc,
  forallb P (expr_vars e acc) = (forallb P (expr_vars e []) && forallb P acc)%bool.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h03acch11bi001bh21xi011xh31Eh41nh51Fh61Hh74IHe1h84IHe2h92Pnh:1eh;2e1h<2e2h=2oph>2Hxh?1Ah@1ChA2ExhB1fhC1lhD1mhE2sxhF3IHehG1PhH1ihI1khJ2lohK1zp;1p;2p;3p;6p;7p;4p;:g00A2j1LTg00Soj27Tg00fXj1XTg00Pej1WTg00E5j1>j29Tg00Lej3@Tg019Ij21Tg001kj33Tg008IR0j3FTg019gj3BTg01:>R1j2=Tg01:YR2j2ATg01;3j3VTg01;Vj2UTg01<9j3TTg01<\j6QTg0053j6Jj7PTg00J=j2ITg00GYj2HTg01=7j1OTg00Roj1NTg01=Vj3RTg00V;j3STg00W;j3_Tg00X;j3^Tg00Y;j3]Tg00Z;j4\Tg00[;j4[Tg00\;l:ZTg01>4j36Tg00>Oj6YTg005OR3f1R4f0R536p=2g00OER6f4R7f3R8563f2R9=634/1533p=EA6394/15p=G1H65p=<f6R:f5R;/7756317949638/15536p=8AF345p=:A3645p=4g00OeR<9365p=011459369p=Dg00PER=9365p=CA6394=365p=KAB345p=5P6P7P8P9P4P5EYp=;17459639p=?17949638/15p=MP6\3g00]=R>%L3R?P81745R@P8%X3RA,74RB1285RCDE]0X:>g00^=RDAG8AC#<P8%W4REP5P8PEPAPCF8eX0?WK%>4/:5P6%<5RE%>9/:4/45P6%>7RF/:8/45f7RGP6P?P4P7A@3;7n0100000020000PGP6P?%>;/:APAA@3;An010000002000012G7RHDE]3P4%>8/:9RI#0P:P7O1RJ115HRK,4HX16PJP6PEPGP;O1RL/45P6f9RMPGO1/45f:RN/2GRO?D4O]9P4f8RPP:O1RQ#012M:RR,1<#<W9%CQPRP6PE14O5P6f<RO?KM5%C4]5P4f;RM/2PRE#0A36<=P0p4p710R0P6\5RQ%L4RSP1AF945#0AB759P8P5O1#0'=X28,A8[RTAB854P9P5O1#0'=X29,A9AF894#0RU[AB;58P7P5O1#0'=X27,A7\UAV945P4n2001000000120000000WCWBW?PT^CS^BQ^?0P5P3%>MPNPGO4155M19O5#0'=X23,A3P2P3155Of=RO/95#0'=X23g01>PR2P5f>,55f?RM/95#0'=P1154Mf@/94#0P2P5fARM,58fC/97#0P11945#0A3394[R1A33451994#0RN[A3389\N1U45P4n2001000000120000000XD3X43P1^D3^43P5fER1P:P4O3A331:P3fFRN155NP2]>X2315N1fIR1/2N#0fHR0,55fLP4O1#0[^23[fGRQ,55fKP4O1#0[^23fJRS/2Q#0[AT31NPOPQP5EQP1PQO1#0P6PSP0O1%05X16P5P=PMEJA36=<P6P=P6p-0P5P2g01>mn0110000020000X:6g01?IP<P5EJP21I25b6b@b@W>PGP5P8FPbAb6WAW>P4P5O2n2001000000120000000W6X23P4P5O2n2001000000120101000b3b6'IW5%CE1H6=W5n0110000020100P5O1b5b1ADR=ReW9n0110000020001P5O1b9b111J<R<%OJRRD;12:8R=P6P?1:FAPAA@37An0100000020000=G:=RF'4eW3%CIPJ11LH/4KX1611J=#<P<PRD;A@378=K:FeW3n0110000020100P5O1b3b1P8%N4RFP5P8PFPAPCF8eX0?X43g00^[RCP7P@P7PB1275DE^0?RFP:P@P:PB12:5RBDE^0?R@A?G7ARR1795R<,2GR='1PPP;178ARJ12P4RKCMRL,45X16179ARH,2GRI12G5RE'1R2A?P;ARM/15/4LX1611RIRL12PJRJ/1K,1M?D5KX1611LERL11MJ=D5KX16%<L11R2ARRIED;A?G7HP8PHO1D;P=P4P5O1R=D;A?G7<P8P<O1D;R<PGAS;79RHP5PGPHPAPEF8eX0?W8X<>W7X;>W=P<PGA_;79RHP5PGPHPAPEF8eX0?X8@X<>X7FX;>X=Cg00_GRCP<PGA^;79RHP5PGPHPAPEF8eX0?X8@X<>X7FX;>W=P<PGA];79R<P5PGP<PAPEF8eX0?X8@X<>X7FX;>X=CP=PGP;P7P8P9C\R;P5PGP;PAPEF8eX0?XF@X:>X43XJ3XE6AG:AB#<P:P7P8P9P4C[R4P5P:P4PAPBF8eX0?X43XHDXI3XE6P5M:ZW:WGo"). Qed.
Lemma expr_all_live_t_eq : forall acc t e, live_agree acc t -> expr_all_live_t t e = all_live acc e.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h04IHe1h11bi001bh21vh34IHe2h42e1h52e2h62oph71eh81nh92sxh:1Hh;3IHeh<3acch=1ih>1kh?2loh@1thA1zi011mi022m'p;1p;2p;6p;3p;4p;:g00A2j1STg00ARj1RTg00BSj2JTg01?ej2@Tg00E5j1>Tg00H3j20Tg00fXj1ITg00Soj26Tg00GYj2;Tg00Pej1ATg019Ij23Tg01@Ej2=Tg01=7j1QTg00>Oj6:Tg00J\j2PTg0053j6OTg00Roj1NTg01@ej27Tg001kj39Tg01B0j3FTg00V;j3GTg00W;j3HTg00X;j3ETg00Y;j3KTg00Z;j4LTg00[;j4DTg00\;l:CTg01C=j2MTg008Ij3BTg01>4j3<Tg005OR0f1R1f0R23Bp=1A<012p=2g00OER3f2R4/71;92p=8f4R5f3R6'716129<04593p=5A9312p=416129<04p=?%S0g00NE#Rg00]=R71J41p,3nx0R8,@2R9%>2R:f5R;'1'0X20R<%I0R=,62R>'29862X77g00^=R?g00OeR@,;3RAP6%A2RBP<PBP=D5eWAP311:5RBP3P31@18RCP@P2n0100000020000%>1/1;RD,0C/3@'4X13P3P0P3P8g00PERC1=12n0110100020010102/0BREP3P3P0P3P8PC1=42n0110100020010102RFP@PDn0100000020000/42X13P9P3P3P3P3P0P3P8PC1=62n0110100020010102R8P@%>4f6RG'1RHn0100000020000108H'4P210FD,;3RFPFn0110000020000b113E@%QEE:P3P3P9P@PBn0100000020000109B/3@'4e1P62P1P2O1EOP6%N2RBP<PBP=D5eX80g00^[RB11:G,09X20/2>9852R<f8RE,1:,09X20RF/2>98G2R>P3f9RD,1:,09X20RH166=R8'2RI161=RJ,2HRK'3P3P317E5RL17E4REPCn0100000020000/42X13P3PIP3P3P2PEPCn0100000020000f:,1:,09X20RE165=RM'2RNA?E4='3RE'4X13P3PKP3P3PNP2PCn0100000020000/4EX13PIP3P3A8D;2P3P3P1f<,1:,09X20/2MRMPCn0100000020000131M'4]0P2A93L@f;,1:,09X20/28R8,3@,;3W0A93LC13C8,;3W0n0110000020000P6O1b1f7R8/71P2E:1786P4E:A?H6JAFH6JE:RJP8AG561RCPHPCP=D5eW3X57W0X47W6PJP8AH561RCPHPCP=D5eX3>X57X0<X47X6Bg00_GRBPJP8AE561RCPHPCP=D5eX3>X57X0<X47W6PJP8AK561RJPHPJP=D5eX3>X57X0<X47X6BP2P8P5P6P4P1CLR5PHP5P=D5eX;>X77X80X?0X93PAPGP6P4P1P2CDR2PFP2P=D5eX80X=?X>0X93P1M:C1M619841eW:W7W@W<o"). Qed.
Lemma cs_gc_eq : forall cs, cs_gc cs = cs_gc_ref cs.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bh11ai001ah22kkh31ni011nh41lh51ci021ch61ei031eh72hii042hih82loi052loh91vi061vh:1wi071wh;1Hh<1Kh=2a1i082a1h>2a2i092a2h?2bkh@2cshA1ki0:1khB1mi0;1mhC2n1i0<2n1hD2n2i0=2n2hE1pi0>1phF3spbi0?3spbhG3spki0@3spki0A2a0i0B6a_basei0C5a_offi0D2b0i0E1ii0F2k0i0G2k1i0H2n0i0I2opi0J1si0K2sxi0L1xi0M1zp;1p;2p;3p;4p;5p;8p;6g003kj1MTg01DAj2`Tg01E@j1STg00bVR0j2PTg013;j13Tg01FCj3Jj4YTg00i8j1FTg01GLj3:Tg01Ggj2Ej1_Tg0126j14Tg01Hij3Bj4ZTg001kj3<Tg00A2j1NTg00GYj2ATg01J0j1WTg00BSj2VTg01K;j3HTg01L=j2@Tg01M?j1UTg01M_j2>Tg01N<j2?Tg019Ij20Tg01NYj1=Tg00ojj2DTg01O7j2GTg01P9j3CTg01Q;j2RTg01C=j22Tg01@ej25Tg01R=j48Tg01SKj2OTg01TMj3QTg01UOj2KTg00eXj1;Tg01VQj4TTg01WSj3LTg01XUj2ITg01YWj5^Tg01Z6j8]Tg01ZSj1\Tg01[Tj1XTg00>Oj6[Tg00OER1f7R2f6R3f5R4f4R5CYf3R6f2R7f1R8f0R9CZ3<p=11A19p=6A<189p=7P1P5P6P7P8P9E[p=9g016FR:g01\Y#M#M,`9#Sg00]=R;g00^=R<'PP0P;P<P0P;P<P:P9g014BR=%359J89%F5R>3:,E5n200110L00012010?10@P0P;P<P:P9%459B89=:=>,E5n200110L00012010?10@5<:P9%N=R>P:%_4R0P0%349J89R?%F4R@5:=%449B89R4=:=@P:\>/A0P=P?P4%W3%43%33'VP=P5P6f8R4#3P9P5P6%44P9G1P8g018HR?P?g005OR0f:R>f9RAf>RB#3RCAH789RDP>PA%4BREPDG1^9;]:P9f=RD,@6%U8,>7f<RF'?'0#=#6PDPFfARG#3RH1D67RI?H89RJPDPF%4GRGPJG1eX9;X:0X2<X0;P8P9O2n0110J00012010B10CW1P7P8P9O3P?P4P2%3FRJ1G89RKP4P2%4FRLPKG1^3;P9P;P1P91@6F1>79f;RK'?'0#=g00OeRMPMPMPMPMPMPMn0110H000810101101013010I10A10D3010I10A10D3010I10A10D3010I10A10D4010K1051011034010K10F10E101#6RNPKP>f?RO#3RP1D78RQ/G9RRPKP>%4OROPRG1eX4;X2<X0;P8P9O2n0110J00012010B10CX1?P8P9O2P?P>PAPCAC789RRP>PAPEPRG1^A0^3;P9P;P1P81@5B1>69/?D'0#=RBPMPMPMPMPMPMPMn0110H000810101101013010I10A10D3010I10A10D3010I10A10D3010I10A10D4010K1051011034010K10G10E101#6PDPFPHACI89RRPDPFPGPRG1eX?0X4;X2<X0;P8P9O2n0110J00012010B10CX1?P7P8P9O31A1MR0P2P3%3KRR1R89RSP2P3%4KRTPSG1eX7<X8<P8P9O212T8RS12L7,79X01%6S15R8PTPRP8P5C8D9P2P3PR1O89RRP2P3PTPRG1eXB<X6;P8P9O2%4DRR/27RT12E6,79X01%6T%3DRT/57PRPTP7P3C8D9PAP4PTAQ789RTPAP4PRPTG1eX7<X8<X6;P7P8P9O3P?P4P2PJ1K89RTP4P2PLPTG1^3;P9P0PKP>PP1KQ9R0PKP>POP0G1eX3;X2<X0;P8P9O2n0110J00012010B10CX1?P8P9O2%;6R0,2ORTf@RR#3R3/56,09%;7RS,53RU'01538R3'0%4RRR%;5'2R512R6'0RV12RS'0RS12R8'0RR'7X0112O7RW1059/0U/03/7RX01%;8RU,2OR510V9/03/7RX0112O9R310S9/7RX0110TW/05/03#615P9POPPP9P4C8D915PUPOPPPUP4C8D915P7POPPP7P4C8D915P0POPPP0P4C8D9PKP>PPP6P7P8P9CTR0PKP>POP0G1eXD;X>?XC;X=?P6P7P8P9O4P?P>PAPCAL789RCP>PAPEPCG1^5<^3;P9P;P1P8PBPMPMPMPMPMPMPMn0110H000810101101013010I10A10D3010I10A10D3010I10A10D3010I10A10D4010K1051011034010K10F10E101#6PDPFPHALI89RIPDPFPGPIG1eX5<X4;X2<X0;P8P9O2n0110J00012010B10CX1?P7P8P9O3P?P4P2PJ1I89RJP4P2PLPJG1^3;P9PNPKP>PP1IQ9RQPKP>POPQG1eX4;X2<X0;P8P9O2n0110J00012010B10CX1?P8P9O2n0110:000:30100107106201001013010010110:201051042010310;30103105104201001014110810<10910=3010010110220100101b;X<=P@D^G]XG<XF;P8P9O2n200110>00012110310MbE%\9%X95<:eW@o"). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint expr_vars_lt (b : nat) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => Nat.ltb n b
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars_lt b x && expr_vars_lt b y
  | EExt _ _ _ x => expr_vars_lt b x
  | EBlob _ _ _ _ => true
  end.
Definition saddr_vars_lt (b : nat) (a : saddr) : bool := expr_vars_lt b (a_base a).

(* [comment removed for export] *)
Fixpoint shape_vars_lt (b : nat) (s : shape) : bool :=
  match s with
  | SNil | SExit _ | SHole _ | SNext => true
  | SEmitP _ _ s' => shape_vars_lt b s'
  | SAlt2 x y => shape_vars_lt b x && shape_vars_lt b y
  | SCase e _ x y => expr_vars_lt b e && shape_vars_lt b x && shape_vars_lt b y
  end.
Definition kentry_vars_lt (b : nat) (K : kentry) : bool :=
  match K with
  | KWord a _ v => saddr_vars_lt b a && expr_vars_lt b v
  | KZero a n => saddr_vars_lt b a && expr_vars_lt b n
  | KBlob a n _ => saddr_vars_lt b a && expr_vars_lt b n
  | KImg _ _ => true
  | KAlign e _ => expr_vars_lt b e
  | KRange e _ _ => expr_vars_lt b e
  | KWr a n => saddr_vars_lt b a && expr_vars_lt b n
  | KDisj a1 n1 a2 n2 => saddr_vars_lt b a1 && expr_vars_lt b n1 && saddr_vars_lt b a2 && expr_vars_lt b n2
  | KFill a n _ => saddr_vars_lt b a && expr_vars_lt b n
  | KUnk a n => saddr_vars_lt b a && expr_vars_lt b n
  end.
Fixpoint sr_vars_lt (b : nat) (sr : list expr) : bool :=
  match sr with [] => true | e :: r => expr_vars_lt b e && sr_vars_lt b r end.
Fixpoint kn_vars_lt (b : nat) (k : list kentry) : bool :=
  match k with [] => true | K :: r => kentry_vars_lt b K && kn_vars_lt b r end.
Definition pairs_vars_lt (b : nat) (l : list (expr * expr)) : bool :=
  forallb (fun p => expr_vars_lt b (fst p) && expr_vars_lt b (snd p)) l.
Definition maps_vars_lt (b : nat) (ms : list amap) : bool :=
  forallb (fun m => expr_vars_lt b (am_base m) && expr_vars_lt b (am_len m)) ms.
Definition fd_vars_lt (b : nat) (f : afd) : bool :=
  match f with FdStd => true | FdFile _ l o => expr_vars_lt b l && expr_vars_lt b o | FdDir => true end.
(* [comment removed for export] *)
Definition fresh_ok (cs : acs) : bool :=
  let v := nxt cs in
  sr_vars_lt v (s_regs (a_ss cs)) && kn_vars_lt v (kn cs)
  && maps_vars_lt v (a_maps cs) && pairs_vars_lt v (a_vis cs) && pairs_vars_lt v (a_ghost cs)
  && expr_vars_lt v (a_brk cs) && fd_vars_lt v (a_fd cs) && Nat.leb nx0 v.

(* [comment removed for export] *)
Definition run_block_ref (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  if fresh_ok cs then
    let ss := a_ss cs in
    let ss' := sym_execTX segs IT K fuel true stops (SS (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss)) in
    match carry (s_log ss') (s_know ss') [] with
    | (kn', [], _) => Some (with_ss cs (mk_ss (s_pc ss') (s_regs ss') kn' (s_next ss')))
    | _ => None
    end
  else None.
(* [comment removed for export] *)
Definition run_block (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  if fresh_ok cs then
    let ss := a_ss cs in
    let bc := mkbc (facts_of (s_know ss)) in
    let kx := mk_kix (s_know ss) in                 (* [comment removed for export] *)
    let ss' := sym_execTXBI segs bc kx IT K fuel true stops (SS (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss)) in
    match carryK bc (s_log ss') (s_know ss') [] with
    | (kn', [], _) => Some (with_ss cs (mk_ss (s_pc ss') (s_regs ss') kn' (s_next ss')))
    | _ => None
    end
  else None.
Lemma run_block_eq : forall K fuel stops cs, run_block K fuel stops cs = run_block_ref K fuel stops cs.
Proof.
Local Unset Keyed Unification.
Local Set Keyed Unification.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h02knh11Kh21bi001bh32bch42csh52fkh64fuelh75hintsh85lemmah93logh:1pi011ph;1si021sh<5stopsi033kn'i041li052l0i062l1i071xp;1p;2p;6p;9p;4p;7p;3p;@g00A2R0j1BTg01]8j1\Tg00FUj1WTg00bVR1j2KTg00g8j1>Tg01^<j10Tg01_<R2j17Tg01`>R3j18Tg01a>j1DTg01b@j13Tg00h8j12Tg00fXj1ITg01c>j11Tg00n=j1MTg01d>j6ATg01eCl9ETg01fKj1@Tg01gJR4j4<Tg01hLj4;Tg01iMj2=Tg01jPj7?Tg01kTj3LTg001kj35j16Tg01lSj1VTg01mCj4:Tg01mjj1HTg01nYj44Tg01oPj3FTg020Fj1UTg0215j6STg021`j7Jl@RTg022Mj2CTg002lj6QTg0239l9PTg0243j7OTg00GYj2GTg025>j3TTg00>Oj6NTg026Cl9[Tg027Nj4ZTg028Sj4YTg00G7j2XTg016FR5f0R6'Xp=9g005OR7g00^=#B%\6g00OER8P8%W5R9P8P9P6P1g014B#BR:g029\R;#BR<'KR=%B8R>P9f2R?#>R@#0RA#7RB#8RCp,4segsRDPC%DAp,2ITREf5RFf4RGg00OeRHf3RI%3@%2@g02:`RJ#IRKPA%1@g018H#MR@EARLM9ERM#@%0M%I8RMC<P1P:P<P9f1RNP0P;P9P6f6ROPD%>ORP#0RQ#7#8%DQPEf9RRf8RSPHf7RT%3P%2PPKPQ%1PP@EARPM9ERQ#3%2QPN%1QC;'=#9%M5RQn10110500020020102106n2001101000120103105n2001107000120101104PQn0100000020100P8P9P6P1P=P>P9PDPEPFPGPHPIPLF?RL#@R8%0LRL;LMP1P:P<P9PNP0P;P9P6PDPEPRPSPHPTPPF?RP#3%2PPN%1PC;,=O#9PQn10110500020020102106n2001101000120103105RPn2001107000120101104RUPQn010000002000035P6g02;bRVPDPEPGPIPHP?%>NRW#3%2WPK%0WRX%1WP@EARWF?RYP1P=P>P9PC%@6%06PMC<P1P:P<P9PNP0P;P9P6%3G%2GPN%1GC;,=O#9PQn10110500020020102106n2001101000120103105n2001107000120101104=59UX;V%0YRV%0W55:P9%69%V9P1P=P>P9PCP8PLPMC<RZPPn2001107000120101104P1P=P>P9%7LR[#8R\P8PLPMC<R]PPn20011070001201011041K=>R^P9P1P=P>P9P6P1P:P<P9PNP0P;P9P6PDPEf:PRPHPS%>TRR#3%2RPK%0R%1RP@EAF?RR#3%2RPN%1RC;,=T#9PQn10110500020020102106n2001101000120103105n2001107000120101104V^PZP]g02<gR]%BJRJP^^7>RZ^0:RR]9R_]3R`P]P_%6]RaPJPR%6JP:PZ%6:RbP>P^%6>%6^RcC:RdC:ReC:RfC:RgP]P_PfPJPRPeP:PZPdP>P^Pc%H^C4C4C4C49F`gP4PCP\P]^5:R\P:P]PbPaC:RCP:P]Pa%H]C49F\CP3PBP[P:^0:R[P:P:PbPbC:RBP:P:Pb%H:C49F[BP2PAPLP:Pb%U:PLPAP6ESFJFJP8P81CJ8PLPL1C:LPMPM1C>MM@REQPUPU1C9UM9PW8PDPEPGPIPHP?PWFOP^%@YRY?LVMRLP1P=P>P9P6PPn2001107000120101104=59UX:^P1P=P>P9PLP1P:P<P9PNP0P;P9P6PDPEPSPTPHPO%>FRL#3%2LPK%0LRK%1LP@EAR@F?RL#3%2LPN%1LC;,=F#9PQn10110500020020102106n2001101000120103105n2001107000120101104RL,G9%7V#8PYPVPMC<ATYVMENO2PD%7X#8RY%DXPEPGPIPHP?PWM9ERVPDPXPEPGPIPHP?PW1G:XM9[ENP1P=P>P9PY%@V%0VPMC<P1P:P<P9PNP0P;P9P6PD%7K#8%DKPEPSPTPHPOP@M9ER@#3%2@PN%1@C;,=F#9PQn10110500020020102106n2001101000120103105n2001107000120101104=59Le1G9Qn0110001020100b2PIP?PNP6CZPIP?PNP6CY559eX45W<X67W1o"). Qed.

Definition run_block_gc (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  match run_block K fuel stops cs with Some cs' => Some (cs_gc cs') | None => None end.

Definition kentry_eqb (x y : kentry) : bool :=
  match x, y with
  | KWord a w v, KWord a' w' v' => saddr_eqb a a' && Nat.eqb w w' && expr_eqb v v'
  | KZero a n, KZero a' n' => saddr_eqb a a' && expr_eqb n n'
  | KBlob a n k, KBlob a' n' k' => saddr_eqb a a' && expr_eqb n n' && Nat.eqb k k'
  | KImg lo hi, KImg lo' hi' => Z.eqb lo lo' && Z.eqb hi hi'
  | KAlign e m, KAlign e' m' => expr_eqb e e' && Z.eqb m m'
  | KRange e lo hi, KRange e' lo' hi' => expr_eqb e e' && Z.eqb lo lo' && Z.eqb hi hi'
  | KWr a n, KWr a' n' => saddr_eqb a a' && expr_eqb n n'
  | KDisj a1 n1 a2 n2, KDisj a1' n1' a2' n2' => saddr_eqb a1 a1' && expr_eqb n1 n1' && saddr_eqb a2 a2' && expr_eqb n2 n2'
  | KFill a n c, KFill a' n' c' => saddr_eqb a a' && expr_eqb n n' && Z.eqb c c'
  | KUnk a n, KUnk a' n' => saddr_eqb a a' && expr_eqb n n'
  | _, _ => false
  end.

Definition amap_eqb (x y : amap) : bool :=
  expr_eqb (am_base x) (am_base y) && expr_eqb (am_len x) (am_len y) && mkind_eqb (am_kind x) (am_kind y).

Fixpoint list_eqb {T : Type} (eqb : T -> T -> bool) (x y : list T) : bool :=
  match x, y with
  | [], [] => true
  | a :: x', b :: y' => eqb a b && list_eqb eqb x' y'
  | _, _ => false
  end.

Definition pair_eqb (x y : expr * expr) : bool := expr_eqb (fst x) (fst y) && expr_eqb (snd x) (snd y).

Definition afd_eqb (x y : afd) : bool :=
  match x, y with
  | FdStd, FdStd => true
  | FdDir, FdDir => true
  | FdFile k l o, FdFile k' l' o' => Nat.eqb k k' && expr_eqb l l' && expr_eqb o o'
  | _, _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kentry_apart_b (allkn : list kentry) (ub : expr) (uk : Z) (un : expr) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => Nat.leb w 8 && ranges_apart_x allkn ub uk un b k (ELit (Z.of_nat w))
  | KZero (SA b k) l => ranges_apart_x allkn ub uk un b k l
  | KBlob (SA b k) l _ => ranges_apart_x allkn ub uk un b k l
  | KImg lo hi => Z.leb 0 lo && Z.leb lo hi && Z.ltb (hi - lo) two64 && ranges_apart_x allkn ub uk un (ELit 0) lo (ELit (hi - lo))
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA b k) n => ranges_apart_x allkn ub uk un b k n
  | KFill (SA b k) l _ => ranges_apart_x allkn ub uk un b k l
  | KUnk (SA b k) l => ranges_apart_x allkn ub uk un b k l
  end.

Definition kentry_apart_bB (bc : bctx) (ub : expr) (uk : Z) (un : expr) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => Nat.leb w 8 && ranges_apart_xB bc ub uk un b k (ELit (Z.of_nat w))
  | KZero (SA b k) l => ranges_apart_xB bc ub uk un b k l
  | KBlob (SA b k) l _ => ranges_apart_xB bc ub uk un b k l
  | KImg lo hi => Z.leb 0 lo && Z.leb lo hi && Z.ltb (hi - lo) two64 && ranges_apart_xB bc ub uk un (ELit 0) lo (ELit (hi - lo))
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA b k) n => ranges_apart_xB bc ub uk un b k n
  | KFill (SA b k) l _ => ranges_apart_xB bc ub uk un b k l
  | KUnk (SA b k) l => ranges_apart_xB bc ub uk un b k l
  end.

Lemma kentry_apart_bB_eqf : forall fk, kentry_apart_bB (mkbc fk) = kentry_apart_b fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01Ki001Kh11bi011bh22b1h32b2h42fkh52k1h62k2h72n1i022n1h82n2i032n2h92ukh:2unh;1xh<2x0h=2x1h>2x2i041ai052a1i062a2i071ci081ei092hii0:1ki0;2k0i0<1li0=2loi0>1mi0?1ni0@1vi0A1wp;1p;2p;3p;4p;7p;6p;5g00A2j1KTg01`>j13Tg02=ij1>j2Jj3?j4<j5ETg02?4j19j2Hj3=j4;j5FTg02@>j18j70Tg003kj11Tg01@Ej2:Tg01M?j1ITg00Pej15Tg019Ij22Tg01N<j27Tg02AFj2GTg02Acj2@Tg001kj36Tg00GYj2ATg02B@j1BTg02CKj1CTg00>Oj6DTg02DZj54Tg014BR0#Kg00]=R1g00^=R2g00OER3^00R4^:1R5]9f0R6#3#>%96P2P5f1R5#3/J61H56P1P4f2R4#3??56A=456P0P3f3R7#3P4P5P6C<P7P4P5P6C;P3^81^62^31^71^52^21R8f4R9#8P0P3P5g018HR:P3P4g01\Y#1#1#1#1#1#1#1#1,:7R;f5R<f9R=f8R>f7R?P5P6%I7#5R@O6'2n0110400012010110:P:P3P5P9P>P?f6RAP5P6P4O6n0110400012010110:RBP:P3P4P<P=P>P?P5P6P7O6n0110400012010110:RCg02E\RD/751756'21G65REg02F:'@'2RFP4PAP<P9%5DRDP5%5EREO6'2g00OeRGPGPBPGPCPBn01100000:3010410A10@2010410<3010410<10;2010=1092010810>3010810=1092010410?401051021061033010410<1072010410<P0P3P5P:P3P4f:RBP=P>P?P5P6P@F0,2;n0110400012010110:P:P3P5P=P>P?PAP5P6P4F0n0110400012010110:RCP:P3P4PBP=P>P?P5P6P7F0n0110400012010110:RBP?PAP<P9PDP5PEF0,2FPGPGPCPGPBPCn01100000:3010410A10@2010410<3010410<10;2010=1092010810>3010810=1092010410?401051021061033010410<1072010410<563X18P0P3P6P:P3P4P=P>P?PAP5P6P@F0,2;n0110400012010110:P:P3P5P>P?PAP<P5P6P4F0n0110400012010110:R;P:P3P4P=P>P?PAP5P6P7F0n0110400012010110:R?PAP<P9P7PDP5PEF0,2FPGPGP;PGP?P;n01100000:3010410A10@2010410<3010410<10;2010=1092010810>3010810=1092010410?401051021061033010410<1072010410<,A3%39R;#B%C9EDP;P7P4P5P6DEP9P7P4P5P6DF563eX>0D4X=1D4X<2D4X;1D4W4o"). Qed.
#[local] Hint Rewrite kentry_apart_bB_eqf : bceq.


(* [comment removed for export] *)
Definition kentry_apart_bp (allkn : list kentry) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => Nat.leb w 8 && ranges_apart_p allkn sp ub uk un b k (ELit (Z.of_nat w))
  | KZero (SA b k) l => ranges_apart_p allkn sp ub uk un b k l
  | KBlob (SA b k) l _ => ranges_apart_p allkn sp ub uk un b k l
  | KImg lo hi => Z.leb 0 lo && Z.leb lo hi && Z.ltb (hi - lo) two64 && ranges_apart_p allkn sp ub uk un (ELit 0) lo (ELit (hi - lo))
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA b k) n => ranges_apart_p allkn sp ub uk un b k n
  | KFill (SA b k) l _ => ranges_apart_p allkn sp ub uk un b k l
  | KUnk (SA b k) l => ranges_apart_p allkn sp ub uk un b k l
  end.

Definition kentry_apart_bpB (bc : bctx) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => Nat.leb w 8 && ranges_apart_pB bc sp ub uk un b k (ELit (Z.of_nat w))
  | KZero (SA b k) l => ranges_apart_pB bc sp ub uk un b k l
  | KBlob (SA b k) l _ => ranges_apart_pB bc sp ub uk un b k l
  | KImg lo hi => Z.leb 0 lo && Z.leb lo hi && Z.ltb (hi - lo) two64 && ranges_apart_pB bc sp ub uk un (ELit 0) lo (ELit (hi - lo))
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA b k) n => ranges_apart_pB bc sp ub uk un b k n
  | KFill (SA b k) l _ => ranges_apart_pB bc sp ub uk un b k l
  | KUnk (SA b k) l => ranges_apart_pB bc sp ub uk un b k l
  end.

Lemma kentry_apart_bpB_eqf : forall fk, kentry_apart_bpB (mkbc fk) = kentry_apart_bp fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01Ki001Kh11bi011bh22b1h32b2h42fkh52k1h62k2h72n1i022n1h82n2i032n2h92sph:2ubh;2ukh<2unh=1xh>2x0h?2x1h@2x2hA2x3i041ai052a1i062a2i071ci081ei092hii0:1ki0;2k0i0<1li0=2loi0>1mi0?1ni0@1vi0A1wp;1p;2p;3p;4p;5p;8p;6g00A2j1MTg01`>j13Tg02G9j1?j2Lj3Bj4=j5:j6HTg02HEj1;j2Cj3>j4<j58j6ITg02IPj19j80Tg003kj12Tg01@Ej2KTg01M?j1JTg00Pej15Tg019Ij21Tg01N<j26Tg02AFj2ATg02Acj2@Tg001kj37Tg00GYj2DTg02JXj1ETg02Kcj1FTg00>Oj6GTg02DZj54Tg014BR0#Mg02M2R1g00]=R2g00^=R3g00OER4^00R5^<2R6];R7]:f0R8#3#?%;8P2P7f1R7#3/L81C78P3P6f2R6#3?B78A>678P2P5f3R5#3P6P7P8C=P5P6P7P8C<P0P4f4R9#3P5P6P7P8D:P9P5P6P7P8D8P4^82^63^32^72^53^22^91R:f5R;#9P0P4P7g018HR<P4P6g01\Y#2#2#2#2#2#2#2#2,K5R=P;f:R>f9R?f8R@f7RAP7P8%J5#5RBO7'1n0110400012010110:P<P4P7P9P?P@PAf6RCP7P8P6O7n0110400012010110:RDP<P4P6P;P>P?P@PAP7P8P5O7n0110400012010110:REg02E\RF/671678'11A87RGg02F:'@'1RHP6PAPCP;P9%5FRFP7%5GRGO7'1g00OeRIPIPDPIPEPDn01100000:3010410A10@2010410<3010410<10;2010=1092010810>3010810=1092010410?401051021061033010410<1072010410<P0P4P7P<P4P6f;RDP>P?P@PAP7P8PBG0,1=n0110400012010110:P<P4P7P>P?P@PAPCP7P8P6G0n0110400012010110:REP<P4P6PDP>P?P@PAP7P8P5G0n0110400012010110:RDP@PAPCP;P9PFP7PGG0,1HPIPIPEPIPDPEn01100000:3010410A10@2010410<3010410<10;2010=1092010810>3010810=1092010410?401051021061033010410<1072010410<574X1:P0P4P8P<P4P6P>P?P@PAPCP7P8PBG0,1=n0110400012010110:P<P4P7P?P@PAPCP;P7P8P6G0n0110400012010110:R=P<P4P6P>P?P@PAPCP7P8P5G0n0110400012010110:R@PAPCP;P9P5PFP7PGG0,1HPIPIP=PIP@P=n01100000:3010410A10@2010410<3010410<10;2010=1092010810>3010810=1092010410?401051021061033010410<1072010410<,D4%3;R=#E%F;EGP=P9P5P6P7P8EHP;P9P5P6P7P8EI574eXA0D4X@2D4X?3D4X>2D4X=1D4W4o"). Qed.
#[local] Hint Rewrite kentry_apart_bpB_eqf : bceq.



Definition kimg_b (K : kentry) : bool := match K with KImg _ _ => true | _ => false end.

(* [comment removed for export] *)
Definition kn_unfill (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.filter (fun K => kimg_b K || kentry_apart_bp k sp ub uk un K) k.

Definition kn_unfillB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  List.filter (fun K => kimg_b K || kentry_apart_bpB bc sp ub uk un K) (bc_fk bc).

Lemma kn_unfillB_eqf : forall fk, kn_unfillB (mkbc fk) = kn_unfill fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01Kh12ukh22unh31bh42b1h52fkh62k1h71lh82n1h91sh:2sph;2ubh<1xh=2x0h>2x1p;1p;2p;3p;4p;6p;5g00A2j1KTg01`>j10Tg02N3j1>j2Jj3?j4ETg02O9j1:j2Ij3=j4FTg02HEj1<j66Tg02P>j1;Tg02Q@j49j1ATg00H3j22Tg02REj17Tg01GLj31Tg02SFj48j1HTg001kj33Tg00GYj2GTg02THj1@Tg00>Oj64Tg02UNj1BTg02G9j1CTg02VWj1DTg02DZj55Tg014BR0#KR1g00]=R2g00^=R3P1^22R4]1f0R5#0#>%:5P3P4f1R4#0/J51I45P2P1f2R6#0??45A=645g02M2R7g00OE^00^22^13^;2]:R8f3R9#<%;5R:P4f5R;#0f4R<P9P6C9P<P9P6P5O5'2X00%0<#7R=510P;P;P<P9P6C8P<P9P6P5E6,2:X00R>=10<R?531X38P7^82^63^42R7%H9P;P4P<P9P6O3P<P9P6P5E6,2:X00=10==31?X97P1P9A10>5=31?X71P<P<P9P6P4C8P9P6P4P5E6,2:X00=109,G1%09R0#7%@9E4%A0%B9E4%C0%D9E4P0P6P4P5CEP9P6P4P5CF531eX>2D5X=3D5X<2D5W5o"). Qed.
#[local] Hint Rewrite kn_unfillB_eqf : bceq.

Definition kn_unfillM (k : list kentry) := kn_unfillB (mkbc k).
Lemma kn_unfillM_eq : kn_unfillM = kn_unfill.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01kh12ubh22ukh32unp;1p;3p;5g00A2j15Tg02Wgj14Tg02Y1R0j10Tg02O9R1j11Tg001kj33Tg02DZj52Tg014B#5R2g00]=R3g00^=P2^33]2]1R3P0P1f0R1#4%01%11533eX02D2o"). Qed.



(* [comment removed for export] *)
Definition kwr_b (K : kentry) : bool := match K with KWr _ _ => true | _ => false end.
Definition havoc1 (k : list kentry) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if (kwr_b K || kentry_apart_b k ub uk un K)%bool then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cut k ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cut c k ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cut k ub uk un kb kk len
       | _ => []
       end.

Definition havoc1B (bc : bctx) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if (kwr_b K || kentry_apart_bB bc ub uk un K)%bool then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cutB bc ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cutB bc c ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cutB bc ub uk un kb kk len
       | _ => []
       end.

Lemma havoc1B_eqf : forall fk, havoc1B (mkbc fk) = havoc1 fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01lh11Ki001Kh21ci011ch32ukh42unh51bh62fkh72kbi022kbh82kki032kkh93leni043lenh:2ubh;2wbh<2wkh=2wnh>1xh?2x0h@2x1hA2x2i051ai062a1i072a2i081ei092hii0:1ki0;2k0i0<2loi0=1mi0>1ni0?2n1i0@2n2i0A1vi0B1wp;1p;2p;3p;4p;7p;8p;5p;6g00A2j1VTg01`>j10Tg02Z7j1Bj2Uj3Cj4@j5PTg02[:j1>j2Rj3Aj4?j5;Tg02?4j1=j56Tg02\<j18Tg00H3j24Tg00fXj1TTg00Lej3:Tg02]=j7Sj1HTg02^Cj8Qj1JTg02_Ij7Nj1LTg02`Nj77j1FTg02aQj89j2ETg02bTj75j1DTg001kj31Tg00GYj2GTg02cVj1ITg00>Oj62Tg02d`j1KTg02ejj1MTg02=ij1<Tg02g3j1OTg02DZj53Tg014BR0#VR1g00]=R2g00^=R3P1^10R4^42R5]3f0R6#0#B%>6P3P5f1R5#0/U61R56P2P4f2R4#0?C56AA456P0P1f3R7#0P4P5P6C@P7P4P5P6C?g00OER8^10^42^33^:2R9f4R:#=P8P1%85R;P6P:P7P4P5O4'4%T0R<9:05R=P0P1P5P<g018HR>P1P5f9R?#0R@f8RAf7RBf6RCP5P6P4FSn01105000120102103RDP<P<P<P<P<P<P>P1P4f:RE#0P4P?PAPBP5P6P7GQn01105000120102103RFP>P1P5P@PAPBPCP5P6P4FNn01105000120102103n01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<1092010510>4010610?10710@3010510410120105104n0100000020000P8P1f5R@P:P7P4P5D6,4;R;P=P0P1P5P<P>P1P5P?PAPBPCP5P6P4F7n01105000120102103P<P<P<P<P<P<P>P1P4P4PEP?PAPBP5P6P7G9n01105000120102103REP>P1P5P?PAPBPCP5P6P4F5n01105000120102103RGn01100000:3010510B10A201051043010510>10;2010<1092010810=3010810<1092010510>4010610?10710@3010510410120105104n0100000020000RH511X59P1^92^83^72^=2^<3^;2R9%D:P8P1P;P=P0P1P5P<PDP<P<P<P<P<P<PFP>P1P5P:PAPBPCP5P6P4O6n01105000120102103RFn01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<1092010510>4010610?10710@3010510410120105104n0100000020000=11HX09P9^23RI1E6@X23P8P1P;P=P0P1P5P<PDP<P<P<P<P<P<P>P1P4P@P4P?PAPBP5P6P7O7n01105000120102103PGn01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<1092010510>4010610?10710@3010510410120105104n0100000020000=11HX0IP9%F:P8P1P;P=P0P1P5P<PFP<P<P<P<P<P<PEPGn01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<1092010510>4010610?10710@3010510410120105104n0100000020000=11HX09P8P1%86P:P7P4P5P6D6'4A:06<P0P1P6P<P>P1P5PAPBPCP@P5P6P4F7n01105000120102103P<P<P<P<P<P<P>P1P4P4P?PAPBPCP5P6P7G9n01105000120102103P>P1P5PAPBPCP@P5P6P4F5n01105000120102103n01100000:3010510B10A201051043010510>10;2010<1092010810=3010810<1092010510>4010610?10710@3010510410120105104n0100000020000,G1%0:R@#H%I:E2%J@%K:E2%L@%M:E2%<@%O:E2P@P7P4P5P6DPP:P7P4P5P6D;511eXA0D3X@2D3X?3D3X>2D3W6o"). Qed.
#[local] Hint Rewrite havoc1B_eqf : bceq.


Definition havoc1p (k : list kentry) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if (kwr_b K || kentry_apart_bp k sp ub uk un K)%bool then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cut k ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cut c k ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cut k ub uk un kb kk len
       | _ => []
       end.

Definition havoc1pB (bc : bctx) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if (kwr_b K || kentry_apart_bpB bc sp ub uk un K)%bool then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cutB bc ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cutB bc c ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cutB bc ub uk un kb kk len
       | _ => []
       end.

Lemma havoc1pB_eqf : forall fk, havoc1pB (mkbc fk) = havoc1p fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01lh11Ki001Kh21ci011ch32ubh42ukh52unh61bh72fkh82kbi022kbh92kki032kkh:3leni043lenh;2sph<2wbh=2wkh>2wnh?1xh@2x0hA2x1hB2x2hC2x3i051ai062a1i072a2i081ei092hii0:1ki0;2k0i0<2loi0=1mi0>1ni0?2n1i0@2n2i0A1vi0B1wp;1p;2p;3p;4p;5p;7p;8p;6g00A2j1XTg01`>j10Tg02hBj1Bj2Wj3Dj4@j5=j6RTg02iFj1>j2Uj3Aj4?j5<j6STg02HEj1;j69Tg02\<j1:Tg00H3j24Tg00fXj1VTg00Lej38Tg02]=j7Tj1ITg02^Cj8Kj1LTg02_Ij7Cj1NTg02`Nj76j1GTg02aQj87j2FTg02bTj75j1ETg001kj31Tg00GYj2HTg02cVj1JTg00>Oj63Tg02d`j1MTg02ejj1OTg02G9j1PTg02VWj1QTg02DZj52Tg014BR0#XR1g02M2R2g00]=R3g00^=R4P1^10R5^53R6]4R7]3f0R8#0#B%>8P3P7f1R7#0/W81U78P4P6f2R6#0?D78AA678P3P5f3R5#0P6P7P8C@P5P6P7P8C?P0P1f4R9#0P5P6P7P8D=P9P5P6P7P8D<g00OER:^10^53^44^33^;2R;f5R<#;P:P1%:7R=P8P<P9P5P6P7O5'4%V0R>9807R?P0P1P7P>g018HR@P1P7f:RA#0RBf8RCf7RDf6REP7P8P6FTn01105000120102103RFP>P>P>P>P>P>P@P1P6f;RG#0P6f9RHPCPDP7P8P5GKn01105000120102103RIP@P1P7PBPCPDPEP7P8P6FCn01105000120102103n01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<1092010510>4010610?10710@3010510410120105104n0100000020000P:P1PEP<P9P5P6P7E9,4=R=P?P0P1P7P>P@P1P7PAPCPDPEP7P8P6F6n01105000120102103P>P>P>P>P>P>P@P1P6P6PGPHPCPDP7P8P5G7n01105000120102103RGP@P1P7PAPCPDPEP7P8P6F5n01105000120102103RBn01100000:3010510B10A201051043010510>10;2010<1092010810=3010810<1092010510>4010610?10710@3010510410120105104n0100000020000RJ511X6;P1^:3^94^83^>3^=4^<3R;%E<P:P1P=P?P0P1P7P>PFP>P>P>P>P>P>PIP@P1P7P9PCPDPEP7P8P6O6n01105000120102103RIn01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<1092010510>4010610?10710@3010510410120105104n0100000020000=11JX0;P;^24RK1F8EX24P:P1P=P?P0P1P7P>PFP>P>P>P>P>P>P@P1P6P<P6PHPCPDP7P8P5O7n01105000120102103PBn01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<1092010510>4010610?10710@3010510410120105104n0100000020000=11JX0KP;%G<P:P1P=P?P0P1P7P>PIP>P>P>P>P>P>PGPBn01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<1092010510>4010610?10710@3010510410120105104n0100000020000=11JX0;P:P1%:8P<P9P5P6P7P8E9'4A808>P0P1P8P>P@P1P7PHPDPEP<P7P8P6F6n01105000120102103P>P>P>P>P>P>P@P1P6P6PAPCPDPEP7P8P5G7n01105000120102103P@P1P7PHPDPEP<P7P8P6F5n01105000120102103n01100000:3010510B10A201051043010510>10;2010<1092010810=3010810<1092010510>4010610?10710@3010510410120105104n0100000020000,H1%0<RE#I%J<E3%LE%M<E3%NE%O<E3%PE%Q<E3PEP9P5P6P7P8ERP<P9P5P6P7P8ES511eXC0D2XB3D2XA4D2X@3D2X?2D2W7o"). Qed.
#[local] Hint Rewrite havoc1pB_eqf : bceq.


Definition kn_havoc (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.flat_map (havoc1p k sp ub uk un) k.

Definition kn_havocB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  List.flat_map (havoc1pB bc sp ub uk un) (bc_fk bc).

Lemma kn_havocB_eqf : forall fk, kn_havocB (mkbc fk) = kn_havoc fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01lh12ukh22unh31Kh42b1h52fkh62k1h72n1h81sh92sph:2ubh;1xh<2x0h=2x1p;1p;2p;3p;4p;5p;6g00A2j1JTg01`>j11Tg02jIj1<j2Ij3=j4CTg02kNj18j2Fj3;j4DTg02iFj1:j55Tg02Q@j49j1?Tg02REj16Tg02SFj47j1HTg001kj32Tg00GYj2ETg02THj1>Tg00>Oj63Tg02UNj1@Tg02hBj1ATg02lRj1BTg02DZj54Tg006oj4GTg014BR0P0f1R1f0R2CGp=0%J0R3g00]=R4g00^=R5P3^24R6]1%12#<%82P5P6%11/I21F12P4P3f2R6#1?=12A;612g02M2R7P3^30^24^15^:4]9R0f3R8#:P2f4R9#1R:P8P6P1C9P8P6P1O4%6:R:'0P9P9P8P6P1C7P8P6P1D5R;/09R<523X00P7^74^65^44R7%H8P9P2P8P6P1O3P8P6P1D5/0:=23<X87P3P810;2=23<X03P8P8P6P1P2C7P6P1P2D5/08,E3%18R<#6%>8E3%?<%@8E3%A<%B8E3P<P6P1P2CCP8P6P1P2CD523eX=4D4X<5D4X;4D4W5o"). Qed.
#[local] Hint Rewrite kn_havocB_eqf : bceq.

Definition kn_havocM (k : list kentry) := kn_havocB (mkbc k).
Lemma kn_havocM_eq : kn_havocM = kn_havoc.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01kh12ubh22ukh32unp;1p;3p;5g00A2j15Tg02mZj14Tg02ncR0j10Tg02kNR1j11Tg001kj33Tg02DZj52Tg014B#5R2g00]=R3g00^=P2^33]2]1R3P0P1f0R1#4%01%11533eX02D2o"). Qed.



(* [comment removed for export] *)
Definition kwr_cut (k : list kentry) (ub : expr) (uk : Z) (un : expr) (kb : expr) (kk : Z) (len : expr) : list kentry :=
  kcut KWr k ub uk un kb kk len.

Definition kwr_cutB (bc : bctx) (ub : expr) (uk : Z) (un : expr) (kb : expr) (kk : Z) (len : expr) : list kentry :=
  kcutB bc KWr ub uk un kb kk len.

Lemma kwr_cutB_eqf : forall fk, kwr_cutB (mkbc fk) = kwr_cut fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h02mkh12fkh22kbh32kkh41lh53lenh62ukh72unh82wbh92wkh:2wnh;1xh<2x0h=2x1h>2x2h?2x3h@2x4p;1p;2p;3p;4p;5p;6p;8p;7g00A2j1GTg01`>j10Tg02ohj1;j2Fj3<j45j57j69j7BTg030lj14j2=j3:j46j58j6Ej7CTg031oj2Dj83Tg001kj32Tg00GYj2>Tg032mj1?Tg033nj1@Tg00>Oj6ATg02DZj51Tg014BR0#GR1g00]=R2g00^=R3P1^52R4^33R5^22R6^72R7]6f0R8#0#;%48P3P7f1R7#0/F81=78P2P6f2R9#0?<78A:978P2P5f3R5#0P9P7P8C5P5P9P7P8C6P3P4f4R4#0P5P9P7P8D7P4P5P9P7P8D8P2P1f5R:#0P4P5P9P7P8E9P:P4P5P9P7P8EEg018HP0\2[R0P6^:2^93^82]0R6f7R;,D8X00P8g01UOR0f6R<P:P4P5P9P7O7P0P;P<P:P4P5P9P7G3521X46P0P<P:P4P5P9P7P8G3,>1%0<R0#?%@<EAP0P:P4P5P9P7P8FBP<P:P4P5P9P7P8FC521eX@2D1X?3D1X>2D1X=2D1X<3D1X;2D1W1o"). Qed.
#[local] Hint Rewrite kwr_cutB_eqf : bceq.


Definition cutout1 (k : list kentry) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if kentry_apart_b k ub uk un K then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cut k ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cut c k ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cut k ub uk un kb kk len
       | KWr (SA kb kk) len => kwr_cut k ub uk un kb kk len
       | _ => []
       end.

Definition cutout1B (bc : bctx) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if kentry_apart_bB bc ub uk un K then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cutB bc ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cutB bc c ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cutB bc ub uk un kb kk len
       | KWr (SA kb kk) len => kwr_cutB bc ub uk un kb kk len
       | _ => []
       end.

Lemma cutout1B_eqf : forall fk, cutout1B (mkbc fk) = cutout1 fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01lh12ukh22unh31Ki001Kh41ci011ch52ubh61bh72fkh82kbi022kbh92kki032kkh:3leni043lenh;2wbh<2wkh=2wnh>1xh?2x0h@2x1hA2x2i051ai062a1i072a2i081ei092hii0:1ki0;2k0i0<2loi0=1mi0>1ni0?2n1i0@2n2i0A1vi0B1wp;1p;2p;3p;4p;5p;7p;8p;6g00A2j1YTg01`>j10Tg0353j1Aj2Xj3Bj4?j5TTg0367j1=j2Kj3@j4>j5WTg030lj1<j76Tg02=ij5;j1PTg00fXj1:Tg00Lej39Tg02]=j7Vj1HTg02^Cj8Uj1LTg02_Ij7Jj1NTg02?4j57j1CTg02`Nj74j1FTg02aQj88j2ETg02bTj75j1DTg001kj31Tg00GYj2GTg02cVj1ITg00>Oj62Tg02d`j1MTg02ejj1OTg02g3j1QTg02ohj1RTg037:j1STg02DZj53Tg014BR0#YR1g00]=R2g00^=R3P1^30R4^22R5]1f0R6#0#A%=6P3P5f1R5#0/X61K56P2P4f2R4#0?B56A@456P0P1f3R7#0P4P5P6C?P7P4P5P6C>P1^:2^93^82R8^22^13^52R9f4R:#<g00OER;P1f5R<#0P:P7P4P5D;%:0R=9905R>P0P1P5P=g018HR?P1P5f9R@#0RAf8RBf7RCf6RDP5P6P4FVn01105000120102103REP=P=P=P=P?P1P5P:PBPCPDP5P6P4O6n01105000120102103RFP=P?P1P4f:RG#0P4P@PBPCP5P6P7GUn01105000120102103RHP?P1P5PAPBPCPDP5P6P4FJn01105000120102103RAn01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<109201051044010610?10710@3010510410120105104n0100000020000P;P1P<P:P7P4P5D7RIP>P0P1P5P=P?P1P5P@PBPCPDP5P6P4F4n01105000120102103P=P=P=P=P?P1P5P@PBPCPDP5P6P4F6n01105000120102103RJP=P?P1P4P4PGP@PBPCP5P6P7G8n01105000120102103RGP?P1P5P@PBPCPDP5P6P4F5n01105000120102103RKn01100000:3010510B10A201051043010510>10;2010<1092010810=3010810<109201051044010610?10710@3010510410120105104n0100000020000RL511X09P;^30^22^13^52R9%C:P;P1P6P:P7P4P5O4P>P0P1P5P=PEP=P=P=P=PJP=PHPAn01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<109201051044010610?10710@3010510410120105104n0100000020000=11LX69P8^=2^<3^;2R8%D:P;P1PIP>P0P1P5P=PEP=P=P=P=PJP=PHPFn01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<109201051044010610?10710@3010510410120105104n0100000020000=11LX08P8^43RH1E6<X43P;P1PIP>P0P1P5P=PEP=P=P=P=PJP=P?P1P4P<P4P@PBPCP5P6P7O7n01105000120102103PKn01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<109201051044010610?10710@3010510410120105104n0100000020000=11LX0HP8%F:P;P1PIP>P0P1P5P=PFP=P=P=P=PJP=PGPKn01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<109201051044010610?10710@3010510410120105104n0100000020000=11LX08P;P1P:P7P4P5P6D7A906=P0P1P6P=P?P1P5PBPCPDP<P5P6P4F4n01105000120102103P=P=P=P=P?P1P5PBPCPDP<P5P6P4F6n01105000120102103P=P?P1P4P4P@PBPCPDP5P6P7G8n01105000120102103P?P1P5PBPCPDP<P5P6P4F5n01105000120102103n01100000:3010510B10A201051043010510>10;2010<1092010810=3010810<109201051044010610?10710@3010510410120105104n0100000020000,G1%0:R<#H%I:E2%L<%M:E2%N<%O:E2%P<%Q:E2%R<%S:E2P<P7P4P5P6DTP:P7P4P5P6DW511eXA0D3X@2D3X?3D3X>2D3W7o"). Qed.
#[local] Hint Rewrite cutout1B_eqf : bceq.


Definition cutout1p (k : list kentry) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if kentry_apart_bp k sp ub uk un K then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cut k ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cut c k ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cut k ub uk un kb kk len
       | KWr (SA kb kk) len => kwr_cut k ub uk un kb kk len
       | _ => []
       end.

Definition cutout1pB (bc : bctx) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if kentry_apart_bpB bc sp ub uk un K then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cutB bc ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cutB bc c ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cutB bc ub uk un kb kk len
       | KWr (SA kb kk) len => kwr_cutB bc ub uk un kb kk len
       | _ => []
       end.

Lemma cutout1pB_eqf : forall fk, cutout1pB (mkbc fk) = cutout1p fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01lh12ubh22ukh32unh41Ki001Kh51ci011ch61bh72fkh82kbi022kbh92kki032kkh:3leni043lenh;2sph<2wbh=2wkh>2wnh?1xh@2x0hA2x1hB2x2hC2x3i051ai062a1i072a2i081ei092hii0:1ki0;2k0i0<2loi0=1mi0>1ni0?2n1i0@2n2i0A1vi0B1wp;1p;2p;3p;4p;5p;6p;7p;8g00A2j1[Tg01`>j10Tg038Bj1Aj2Zj3Bj4?j5<j6WTg039Gj1=j2Mj3@j4>j5;j6VTg030lj1:j75Tg02G9j6Yj1RTg00fXj1UTg00Lej39Tg02]=j7Lj1JTg02^Cj8Dj1NTg02_Ij7Cj1PTg02HEj66j1ETg02`Nj78j1HTg02aQj84j2GTg02bTj77j1FTg001kj31Tg00GYj2ITg02cVj1KTg00>Oj63Tg02d`j1OTg02ejj1QTg02VWj1STg02ohj1TTg037:j1XTg02DZj52Tg014BR0#[R1g02M2R2g00]=R3g00^=R4P1^40R5^33R6]2R7]1f0R8#0#A%=8P3P7f1R7#0/Z81M78P4P6f2R6#0?B78A@678P3P5f3R5#0P6P7P8C?P5P6P7P8C>P0P1f4R9#0P5P6P7P8D<P9P5P6P7P8D;P1^:3^94^83R:^33^24^13R;f5R<#:g00OER=P1f6R>#0P<P9P5P6P7EY%U0R?9907R@P0P1P7P?g018HRAP1P7f:RB#0RCf8RDf7REP>P7P8P6FLn01105000120102103RFP?P?P?P?PAP1P7P9PDPEP>P7P8P6O6n01105000120102103RGP?PAP1P6f;RH#0P6f9RIPDPEP7P8P5GDn01105000120102103RJPAP1P7PCPDPEP>P7P8P6FCn01105000120102103RCn01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<109201051044010610?10710@3010510410120105104n0100000020000P=P1P>P<P9P5P6P7E6RKP@P0P1P7P?PAP1P7PBPDPEP>P7P8P6F8n01105000120102103P?P?P?P?PAP1P7PBPDPEP>P7P8P6F5n01105000120102103RLP?PAP1P6P6PHPIPDPEP7P8P5G4n01105000120102103RHPAP1P7PBPDPEP>P7P8P6F7n01105000120102103RMn01100000:3010510B10A201051043010510>10;2010<1092010810=3010810<109201051044010610?10710@3010510410120105104n0100000020000RN511X0;P=^40^33^24^13^;2R;%E<P=P1P8P<P9P5P6P7O5P@P0P1P7P?PFP?P?P?P?PLP?PJPCn01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<109201051044010610?10710@3010510410120105104n0100000020000=11NX6;P:^>3^=4^<3R:%F<P=P1PKP@P0P1P7P?PFP?P?P?P?PLP?PJPGn01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<109201051044010610?10710@3010510410120105104n0100000020000=11NX0:P:^54RJ1G8>X54P=P1PKP@P0P1P7P?PFP?P?P?P?PLP?PAP1P6P<P6PIPDPEP7P8P5O7n01105000120102103PMn01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<109201051044010610?10710@3010510410120105104n0100000020000=11NX0JP:%H<P=P1PKP@P0P1P7P?PGP?P?P?P?PLP?PHPMn01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<109201051044010610?10710@3010510410120105104n0100000020000=11NX0:P=P1P<P9P5P6P7P8E6A908?P0P1P8P?PAP1P7PIPEP>P<P7P8P6F8n01105000120102103P?P?P?P?PAP1P7PIPEP>P<P7P8P6F5n01105000120102103P?PAP1P6P6PBPDPEP>P7P8P5G4n01105000120102103PAP1P7PIPEP>P<P7P8P6F7n01105000120102103n01100000:3010510B10A201051043010510>10;2010<1092010810=3010810<109201051044010610?10710@3010510410120105104n0100000020000,I1%0<R>#J%K<E3%N>%O<E3%P>%Q<E3%R>%S<E3%T>%X<E3P>P9P5P6P7P8EWP<P9P5P6P7P8EV511eXC0D2XB3D2XA4D2X@3D2X?2D2W7o"). Qed.
#[local] Hint Rewrite cutout1pB_eqf : bceq.


Definition kn_cutout (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.flat_map (cutout1p k sp ub uk un) k.

Definition kn_cutoutB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  List.flat_map (cutout1pB bc sp ub uk un) (bc_fk bc).

Lemma kn_cutoutB_eqf : forall fk, kn_cutoutB (mkbc fk) = kn_cutout fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01lh12ukh22unh31Kh42b1h52fkh62k1h72n1h81sh92sph:2ubh;1xh<2x0h=2x1p;1p;2p;3p;4p;5p;6g00A2j1JTg01`>j11Tg03:Kj1<j2Ij3=j4CTg03;Qj18j2Fj3;j4DTg039Gj1:j55Tg02Q@j49j1?Tg02REj16Tg02SFj47j1HTg001kj32Tg00GYj2ETg02THj1>Tg00>Oj63Tg02UNj1@Tg038Bj1ATg03<Vj1BTg02DZj54Tg006oj4GTg014BR0P0f1R1f0R2CGp=0%J0R3g00]=R4g00^=R5P3^24R6]1%12#<%82P5P6%11/I21F12P4P3f2R6#1?=12A;612g02M2R7P3^30^24^15^:4]9R0f3R8#:P2f4R9#1R:P8P6P1C9P8P6P1O4%6:R:'0P9P9P8P6P1C7P8P6P1D5R;/09R<523X00P7^74^65^44R7%H8P9P2P8P6P1O3P8P6P1D5/0:=23<X87P3P810;2=23<X03P8P8P6P1P2C7P6P1P2D5/08,E3%18R<#6%>8E3%?<%@8E3%A<%B8E3P<P6P1P2CCP8P6P1P2CD523eX=4D4X<5D4X;4D4W5o"). Qed.
#[local] Hint Rewrite kn_cutoutB_eqf : bceq.

Definition kn_cutoutM (k : list kentry) := kn_cutoutB (mkbc k).
Lemma kn_cutoutM_eq : kn_cutoutM = kn_cutout.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01kh12ubh22ukh32unp;1p;3p;5g00A2j15Tg03=_j14Tg03>iR0j10Tg03;QR1j11Tg001kj33Tg02DZj52Tg014B#5R2g00]=R3g00^=P2^33]2]1R3P0P1f0R1#4%01%11533eX02D2o"). Qed.



(* [comment removed for export] *)
Definition kn_keep (k : list kentry) (ws : list (expr * expr)) : list kentry :=
  let wss := map (fun w => (split_lit (fst w), xlo k (snd w))) ws in
  let test (b : expr) (o : Z) (n : option Z) : bool :=
    let mine := List.filter (fun w => expr_eqb (fst (fst w)) b) wss in
    match mine with
    | [] => true
    | _ => existsb (fun w => let wk := snd (fst w) in
                             match snd w with
                             | Some wl => Z.ltb 0 wl && Z.ltb wk (match n with Some n => o + n | None => wk + 1 end) && Z.ltb o (wk + wl)
                             | None => true
                             end) mine
    end in
  List.filter (fun K => match K with
                        | KWord (SA b o) w _ => test b o (Some (Z.of_nat w))
                        | KZero (SA b o) n => test b o (xhi k n)
                        | KBlob (SA b o) n _ => test b o (xhi k n)
                        | KFill (SA b o) n _ => test b o (xhi k n)
                        | KUnk (SA b o) n => test b o (xhi k n)
                        | _ => true
                        end) k.

(* [comment removed for export] *)
Definition kimg_cut1 (a n : Z) (K : kentry) : list kentry :=
  match K with
  | KImg lo hi =>
      if (Z.leb hi a || Z.leb (a + n) lo)%bool then [K]
      else (if Z.ltb lo a then [KImg lo a] else []) ++ (if Z.ltb (a + n) hi then [KImg (a + n) hi] else [])
  | _ => [K]
  end.
Definition kimg_cut (k : list kentry) (a n : Z) : list kentry := List.flat_map (kimg_cut1 a n) k.

(* [comment removed for export] *)
Definition kimg_clip (k : list kentry) : list kentry :=
  List.filter (fun K => match K with KImg lo hi => Z.leb (img_lo A) lo && Z.leb lo hi && Z.leb hi (img_hi A) | _ => true end) k.

(* [comment removed for export] *)
Definition kreadZ (k : list kentry) (b : expr) (off : Z) (n : nat) : option Z :=
  match know_lookup segs k b off n false [] [] with
  | LHit (ELit z) [] _ => Some (z mod two64)
  | _ => None
  end.

Definition kreadZB (bc : bctx) (b : expr) (off : Z) (n : nat) : option Z :=
  match know_lookupB segs bc b off n false [] [] with
  | LHit (ELit z) [] _ => Some (z mod two64)
  | _ => None
  end.

Lemma kreadZB_eqf : forall fk, kreadZB (mkbc fk) = kreadZ fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01nh13acch22fkh35hintsi005hintsh41li011lh53offh62rbh72rkh82sxi022sxh91xi031xh:2x0h;2x1i041ai052b0i061ei071ii081ki092k0i0:2loi0;2n0i0<2opi0=1si0>3scsi0?1vi0@1zp;1p;2p;3p;8p;6p;4p;5g00A2R0j12Tg00FUj1FTg01`>j10Tg03?oj16j2Cj3;j4@Tg03A2j1Ej2<j3:j4ATg03B4j27j85Tg00fXj13Tg03C9j28Tg00G7j29Tg00n=j1DTg001kj34Tg00GYj2BTg03CYj2=Tg03Daj2>Tg00>Oj6?Tg02DZj51Tg014B#2g00]=R1g00^=R2g005OR3%F2R4]0R5]5f0R6#0#6%E6P2P5f1R5#0/C61<56P3P4f2R7#0?;56A:756g00OER8%28g029\R9#2g03EmR:]1]3]8^03^72^61R;p,4segsR<f3R='7P:P4P6P=P7P5g00PER>%38R8%39R?O6P1P4P7P0P9P4P7g02F:,86,92%D2R9n10110>0002002010=101R0P9P9P9P9P9P9P9n0110?00081010@1010;3010<1041053010<1041053010<1041053010<1041054010210:10;1064010210810710;P9P9n0110300033010?10>1002010>10000P:P4P<f4P=P7P5P>P8P?G5P1P4P7P0P9P9P9P9P9P9P9n0110?00081010@1010;3010<1041053010<1041053010<1041053010<1041054010210:10;1064010210910710;R0P9P9n0110300033010?10>1002010>10000544X4;P:P4P<P=P7P5P6P>P8P?G5P0P9P9n0110300033010?10>1002010>10000,B4%0=R9,=<1>=<E?P9P7P5P6C@P=P7P5P6CA544eX;3D1X:2D1X91D1W2o"). Qed.
#[local] Hint Rewrite kreadZB_eqf : bceq.


(* [comment removed for export] *)
Definition kread8e (k : list kentry) (b : expr) (off : Z) : option expr :=
  match know_lookup segs k b off 8 false [] [] with
  | LHit v [] _ => Some v
  | _ => None
  end.

Definition kread8eB (bc : bctx) (b : expr) (off : Z) : option expr :=
  match know_lookupB segs bc b off 8 false [] [] with
  | LHit v [] _ => Some v
  | _ => None
  end.

Lemma kread8eB_eqf : forall fk, kread8eB (mkbc fk) = kread8e fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h03acch12fkh25hintsi005hintsh31li011lh41nh53offh62rbh72rkh82sxh91xi021xh:2x0i031si043scsi051vp;1p;2p;8p;3p;6p;5g00A2R0j11Tg00FUj1DTg01`>j12Tg03Fmj17j2<j3?Tg03H1j1Cj2;j3@Tg03B4j2:j85Tg003kj10Tg00fXj13Tg00G7j28Tg00n=j19Tg001kj36Tg00GYj2BTg03CYj2ATg03Daj2=Tg00>Oj6>Tg02DZj54Tg014B#1g00]=R1g00^=R2%D1R3]5f0R4#2#7%C4P2P3f1R5#2/<41;54g005Og00OER6%16g029\R7#1g03EmR8]0]2]8]4^72^61R9p,4segsR:f2R;':P8P3P4P;P5g01\Y#0#0#0#0#0#0#0#0R<g00PER=%36R6%37R>O6P0P7P3P5181;%91R7n10110400020020103101R0P7P7n011020003301051041002010410000P8P3P:f3P;P5P<P=P6P>G5P0P7P7n011020003301051041002010410000563X39P8P3P:P;P5P4P<P=P6P>G5P0P7P7n011020003301051041002010410000,B3%2;R7,A:1=;:E>A?754A@;54563eX:2D4X91D4W1o"). Qed.
#[local] Hint Rewrite kread8eB_eqf : bceq.



(* [comment removed for export] *)
Fixpoint kwritable (allkn k : list kentry) (b : expr) (off n : Z) : bool :=
  match k with
  | [] => false
  | KWr (SA wb wk) wn :: rest =>
      if (if (expr_eqb b wb && Z.leb wk off)%bool
          then match xlo allkn wn with Some wl => Z.leb (off + n) (wk + wl) | None => false end
          else false)
      then true
      else if (Z.leb 0 n && Z.ltb n two64 && xinside allkn b off (ELit n) wb wk wn)%bool then true
      else kwritable allkn rest b off n
  | _ :: rest => kwritable allkn rest b off n
  end.

Fixpoint kwritableB (bc : bctx) (k : list kentry) (b : expr) (off n : Z) : bool :=
  match k with
  | [] => false
  | KWr (SA wb wk) wn :: rest =>
      if (if (expr_eqb b wb && Z.leb wk off)%bool
          then match xloB bc wn with Some wl => Z.leb (off + n) (wk + wl) | None => false end
          else false)
      then true
      else if (Z.leb 0 n && Z.ltb n two64 && xinsideB bc b off (ELit n) wb wk wn)%bool then true
      else kwritableB bc rest b off n
  | _ :: rest => kwritableB bc rest b off n
  end.

Lemma kwritableB_eqf : forall fk, kwritableB (mkbc fk) = kwritable fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bh11nh23offh31kh42IHh51Kh62b1h72b2h81ei001eh92fkh:2k1i012k1h;2k2h<2n1i022n1h=2n2i032n2h>1oh?4resti041ai052a1i062a2i071ci082hii092k0i0:2loi0;1mi0<2n0i0=1vi0>1wi0?2wbi0@2wki0A2wli0B2wni0C1xp;1p;2p;3p;4p;5p;7p;6p;8g00A2j1TTg01`>j12Tg03I4j1Fj2Sj3Lj4Cj55Tg03J:j1Aj2Pj3Ej4Bj50Tg00fXj1RTg00GYj2>Tg01L=j2=Tg01N<j24Tg019Ij21Tg03K?j2Oj1JTg01M_j28Tg02Acj2;Tg00Pej19Tg03L?j7Dj1@Tg03MCj2:j1ITg03N@j7<j1GTg00FUR0j1HTg03OAj1KTg00>Oj67Tg03PEj1MTg00Lej3NTg00`3j8?Tg02DZj56Tg001kj3QTg00OER1f1R2f0R33Qp=3g014BR4#TR5P5g00]=R6g00^=R7P1^17R8]2R9]0%23#F%A3P6P9%22/S31P23P7P8f2R8#2?L23AE823P7P1f3R9#2P8P2P3CCP9P8P2P3CBP4f8R:#2P9P8P2P3D5P:P9P8P2P3D0'3^17^27^06X35f7R;%R4P8P2P3D0,>1X17X27X06f9R<#2P9P8P2P3D5P<P9P8P2P3D0'3^17^27^06P1f:R=f4R>P8P2P3D0P4P1f6R?P9P8P9P8P8P9g018HR@P1P2P1P1P1P11=;2143?'1RAP0P7P1f?RB#2RC/O818;?1823RD'4REg00PERFn10110C00021010A00PFn0100000020000RGg00OeRHP1P1g02E\RIf5RJ'4g02F:RK,;J'1RLPCP;P?%9JRCP2P3P8FD'1PHP>n0100000020000n0100000020000n0110400012010?10@P>P9P8n01109000:3010410>10=2010410<3010410<1012010:1082010010;3010010:1082010410B401051021061033010410<1072010410<P4P1P?f>RMP:P?PJP>D0R:f=P;PJP>P9D0RNP:PNPNP:P@P1P2P1P1P1P1PAP0P7P11:B8PEPFn10110C00021010A00PFn0100000020000PHP1P1PBP;P?PCP2P3P8F<,1LPHPBP<P;P?PJD0R<n0100000020000RBn0100000020000n0110400012010?10@P<P:PNn01109000:3010410>10=2010410<3010410<1012010:1082010010;3010010:1082010410B401051021061033010410<1072010410<RO'3X01P1^=6^;7^76^<6^:7^66RP%G=P4P1P?P:PNP:PNPNP:P@P1P2P1P1PGPHP1P1P>P;P?PCP2P3P8O6,1LPHP<n0100000020000n0100000020000n0110400012010?10@P<P:PNn01109000:3010410>10=2010410<3010410<1012010:1082010010;3010010:1082010410B401051021061033010410<1072010410</3OX0P%H7^86RP%I=P4P1P?P:PNP:PNPNP:P@P1P2P1P1P1P1PAP0P7P1P>P8O1PEPFn10110C00021010A00PFn0100000020000PHPBn0100000020000n0110400012010?10@P<P:PNn01109000:3010410>10=2010410<3010410<1012010:1082010010;3010010:1082010410B401051021061033010410<1072010410</3OX>PP4P1PJPNf<P?P>P9P8D0RPPNPPPPPNP@P1P2P1P1P1P11=?2143J'1P0P7P11:M818?J/4DPFn10110C00021010A00PFn0100000020000PHP1P114I>1;>K'1PMP?PJ%9>P2P3P8F<'1PHP:n0100000020000n0100000020000n0110400012010?10@P:PNPPn01109000:3010410>10=2010410<3010410<1012010:1082010010;3010010:1082010410B401051021061033010410<1072010410<,>1%2=R1#J%K=E7%@1%M=E7P1P>P8P2P3D5P9P8P2P3O3E7P1AN4J>RJP8P2P3D5P=PJP8P2P3D0'3eX17X27X06W4X?5X54P9P8P2P3G?X17D6X27D6X06D6X35D6W9o"). Qed.
#[local] Hint Rewrite kwritableB_eqf : bceq.


Fixpoint kwritable_x (allkn k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match k with
  | [] => false
  | KWr (SA wb wk) wn :: rest =>
      if (if (expr_eqb b wb && Z.leb wk off)%bool
          then match xhi allkn n, xlo allkn wn with
               | Some nh, Some wl => Z.leb (off + nh) (wk + wl)
               | _, _ => false
               end
          else false)
      then true
      else if xinside allkn b off n wb wk wn then true
      else kwritable_x allkn rest b off n
  | _ :: rest => kwritable_x allkn rest b off n
  end.

Fixpoint kwritable_xB (bc : bctx) (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match k with
  | [] => false
  | KWr (SA wb wk) wn :: rest =>
      if (if (expr_eqb b wb && Z.leb wk off)%bool
          then match xhiB bc n, xloB bc wn with
               | Some nh, Some wl => Z.leb (off + nh) (wk + wl)
               | _, _ => false
               end
          else false)
      then true
      else if xinsideB bc b off n wb wk wn then true
      else kwritable_xB bc rest b off n
  | _ :: rest => kwritable_xB bc rest b off n
  end.

Lemma kwritable_xB_eqf : forall fk, kwritable_xB (mkbc fk) = kwritable_x fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bh11nh23offh31kh41oh52IHh61Kh72b1h82b2h91ei001eh:2fkh;2k1i012k1h<2k2h=2n1i022n1h>2n2i032n2h?4resti041ai052a1i062a2i071ci082hii092k0i0:2loi0;1mi0<2n0i0=2nhi0>1vi0?1wi0@2wbi0A2wki0B2wli0C2wni0D1xp;1p;2p;3p;4p;5p;7p;6p;8g00A2j1WTg01`>j10Tg03QMj1Ej2Vj3Oj4Cj53Tg03RUj1Aj2Sj3Dj4Bj51Tg00fXj1UTg00GYj2=Tg01L=j2<Tg01N<j25Tg019Ij2;Tg03S\j2Rj1@Tg03K?j2Nj1JTg01M_j27Tg03L?j7Lj1?Tg03T\j29j1HTg03MCj28j1ITg03N@j7:j1FTg00FUR0j1GTg03OAj1KTg00>Oj64Tg03UYj1MTg03PEj1PTg00Lej3QTg00`3j8>Tg02DZj56Tg001kj3TTg00OER1f1R2f0R33Tp=2g014BR4#WR5P5g00]=R6g00^=R7P1^16R8]2R9]0%03#E%A3P6P9%02/V31S23P7P8f2R8#0?O23AD823P6P1f3R9#0P8P2P3CCP9P8P2P3CBP4f8R:#0P9P8P2P3D3P:P9P8P2P3D1'2^16^27^06X35f7R;%U4P8P2P3D1,=1X16X27X06f9R<#0P9P8P2P3D3P<P9P8P2P3D1'2^16^27^06P1f:R=f4R>P8P2P3D1P4P1f6R?P9P8P9P8P8P9g018HR@P1P2P1P1P1P11<;2153?';RAP0P7P1f?RB#0RCf5RD'RP0P7P1f@RE#0/N917:21783RF'5RGg00PERHn10110D00021010B00RIPHn10110D00021010=00PHn0100000020000RJg00OeRKP1P1PCP;P?PDP2P3P8FLPKP>n0100000020000n0100000020000n0110400012010@10AP>P9P8n01109000:3010410?10>2010410<3010410<1012010:1082010010;3010010:1082010410C401051021061033010410<1072010410<P4P1P?f>RCP:P?PDP>D1R:f=P;PDP>P9D1RLP:PLPLP:P@P1P2P1P1P1P1PAP0P7P119BDRMP0P7P118E9PGPHn10110D00021010B00PHn10110D00021010=00PHn0100000020000PKP1P1PBP;P?PDP2P3P8F:PKPBP<P;P?PDD1R<n0100000020000REn0100000020000n0110400012010@10AP<P:PLn01109000:3010410?10>2010410<3010410<1012010:1082010010;3010010:1082010410C401051021061033010410<1072010410<RN'2X01P1^>6^<7^86^=6^;7^76RO%F=P4P1P?P:PLP:PLPLP:P@P1P2P1P1PJPKP1P1P>P;P?PDP2P3P8O6PKP<n0100000020000n0100000020000n0110400012010@10AP<P:PLn01109000:3010410?10>2010410<3010410<1012010:1082010010;3010010:1082010410C401051021061033010410<1072010410</2NX0O%G7^96RO%H=P4P1P?P:PLP:PLPLP:P@P1P2P1P1P1P1PAP0P7P1P>PDO1PIPHn10110D00021010=00PHn0100000020000PKPEn0100000020000n0110400012010@10AP<P:PLn01109000:3010410?10>2010410<3010410<1012010:1082010010;3010010:1082010410C401051021061033010410<1072010410</2NX4OPO%I=P4P1P?P:PLP:PLPLP:P@P1P2P1P1P1P1PAP0P7P1PMP0P7P1PDP9O1PGPHn10110D00021010B00PHn10110D00021010=00PHn0100000020000PKPEn0100000020000n0110400012010@10AP<P:PLn01109000:3010410?10>2010410<3010410<1012010:1082010010;3010010:1082010410C401051021061033010410<1072010410</2NX4OP4P1PDPLf<P?P>P9P8D1ROPLPOPOPLP@P1P2P1P1P1P11<?2153D';P0P7P119C>P0P7P118B917;2/5FPHn10110D00021010B00PHn10110D00021010=00PHn0100000020000PKP1P1PCP?PDP>P2P3P8F:PKP:n0100000020000n0100000020000n0110400012010@10AP:PLPOn01109000:3010410?10>2010410<3010410<1012010:1082010010;3010010:1082010410C401051021061033010410<1072010410<,=1%0=R1#J%K=E4%@1%M=E4%?1%P=E4P1P>P8P2P3D3P9P8P2P3O3E4P1AQ4D>RDP8P2P3D3P=PDP8P2P3D1'2eX16X27X06W5X?5X64P9P8P2P3G>X16D6X27D6X06D6X35D6W:o"). Qed.
#[local] Hint Rewrite kwritable_xB_eqf : bceq.



(* [comment removed for export] *)
Fixpoint kzero_x (allkn k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match k with
  | [] => false
  | KZero (SA zb zk) zn :: rest =>
      if (if (expr_eqb b zb && Z.leb zk off)%bool
          then match xhi allkn n, xlo allkn zn with
               | Some nh, Some zl => Z.leb (off + nh) (zk + zl)
               | _, _ => false
               end
          else false)
      then true
      else if xinside allkn b off n zb zk zn then true
      else kzero_x allkn rest b off n
  | _ :: rest => kzero_x allkn rest b off n
  end.

Fixpoint kzero_xB (bc : bctx) (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match k with
  | [] => false
  | KZero (SA zb zk) zn :: rest =>
      if (if (expr_eqb b zb && Z.leb zk off)%bool
          then match xhiB bc n, xloB bc zn with
               | Some nh, Some zl => Z.leb (off + nh) (zk + zl)
               | _, _ => false
               end
          else false)
      then true
      else if xinsideB bc b off n zb zk zn then true
      else kzero_xB bc rest b off n
  | _ :: rest => kzero_xB bc rest b off n
  end.

Lemma kzero_xB_eqf : forall fk, kzero_xB (mkbc fk) = kzero_x fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bh11nh23offh31kh41oh52IHh61Kh72b1h82b2h91ei001eh:2fkh;2k1i012k1h<2k2h=2n1i022n1h>2n2i032n2h?4resti041ai052a1i062a2i071ci082hii092k0i0:2loi0;1mi0<2n0i0=2nhi0>1vi0?1wi0@1xi0A2zbi0B2zki0C2zli0D2znp;1p;2p;3p;4p;5p;7p;6p;8g00A2j1WTg01`>j10Tg03V]j1Ej2Vj3Oj4Cj53Tg03Waj1Aj2Sj3Dj4Bj51Tg00fXj1UTg00GYj2=Tg01L=j2<Tg01N<j25Tg019Ij2;Tg03S\j2Rj1@Tg03K?j2Nj1JTg01M_j27Tg03L?j7Lj1?Tg03T\j29j1HTg03MCj28j1ITg03N@j7:j1FTg00FUR0j1GTg03OAj1KTg00>Oj64Tg03UYj1MTg03PEj1PTg00Lej3QTg00`3j8>Tg02DZj56Tg001kj3TTg00OER1f1R2f0R33Tp=2g014BR4#WR5P5g00]=R6g00^=R7P1^16R8]2R9]0%03#E%A3P6P9%02/V31S23P7P8f2R8#0?O23AD823P6P1f3R9#0P8P2P3CCP9P8P2P3CBP4f8R:#0P9P8P2P3D3P:P9P8P2P3D1'2^16^27^06X35f7R;%U4P8P2P3D1,=1X16X27X06f9R<#0P9P8P2P3D3P<P9P8P2P3D1'2^16^27^06P1f:R=f4R>P8P2P3D1P4P1f6R?P9g018HR@P1P2P1P1P1P11<;2153?';RAP0P7P1f?RB#0RCf5RD'RP0P7P1f@RE#0/N917:21783RF'5RGg00PERHn10110@00021010C00RIPHn10110@00021010=00PHn0100000020000RJg00OeRKP1P1PCP;P?PDP2P3P8FLPKP>n0100000020000n0100000020000n0110400012010A10BP9P8P8P9P8P>P9P8n01109000:3010410?10>2010410D3010410<1012010:1082010010;3010010:1082010410<401051021061033010410<1072010410<P4P1P?f>RCP:P?PDP>D1R:P@P1P2P1P1P1P1PAP0P7P119BDRLP0P7P118E9PGPHn10110@00021010C00PHn10110@00021010=00PHn0100000020000PKP1P1PBP;P?PDP2P3P8F:PKPBP<P;P?PDD1R<n0100000020000REn0100000020000n0110400012010A10BP:f=P;PDP>P9D1RMPMP:PMP<P:PMn01109000:3010410?10>2010410D3010410<1012010:1082010010;3010010:1082010410<401051021061033010410<1072010410<RN'2X01P1^>6^<7^86^=6^;7^76RO%F=P4P1P?P:P@P1P2P1P1PJPKP1P1P>P;P?PDP2P3P8O6PKP<n0100000020000n0100000020000n0110400012010A10BP:PMPMP:PMP<P:PMn01109000:3010410?10>2010410D3010410<1012010:1082010010;3010010:1082010410<401051021061033010410<1072010410</2NX0O%G7^96RO%H=P4P1P?P:P@P1P2P1P1P1P1PAP0P7P1P>PDO1PIPHn10110@00021010=00PHn0100000020000PKPEn0100000020000n0110400012010A10BP:PMPMP:PMP<P:PMn01109000:3010410?10>2010410D3010410<1012010:1082010010;3010010:1082010410<401051021061033010410<1072010410</2NX4OPO%I=P4P1P?P:P@P1P2P1P1P1P1PAP0P7P1PLP0P7P1PDP9O1PGPHn10110@00021010C00PHn10110@00021010=00PHn0100000020000PKPEn0100000020000n0110400012010A10BP:PMPMP:PMP<P:PMn01109000:3010410?10>2010410D3010410<1012010:1082010010;3010010:1082010410<401051021061033010410<1072010410</2NX4OP4P1PDPMP@P1P2P1P1P1P11<?2153D';P0P7P119C>P0P7P118B917;2/5FPHn10110@00021010C00PHn10110@00021010=00PHn0100000020000PKP1P1PCP?PDP>P2P3P8F:PKP:n0100000020000n0100000020000n0110400012010A10BPMf<P?P>P9P8D1R?P?PMP?P:PMP?n01109000:3010410?10>2010410D3010410<1012010:1082010010;3010010:1082010410<401051021061033010410<1072010410<,=1%0=R1#J%K=E4%@1%M=E4%?1%P=E4P1P>P8P2P3D3P9P8P2P3O3E4P1AQ4D>RDP8P2P3D3P=PDP8P2P3D1'2eX16X27X06W5X?5X64P9P8P2P3G>X16D6X27D6X06D6X35D6W:o"). Qed.
#[local] Hint Rewrite kzero_xB_eqf : bceq.



(* [comment removed for export] *)
Fixpoint kfill_x (allkn k : list kentry) (b : expr) (off : Z) (n : expr) (c : Z) : bool :=
  match k with
  | [] => false
  | KFill (SA zb zk) zn c' :: rest =>
      if (if (Z.eqb (c' mod 256) (c mod 256) && expr_eqb b zb && Z.leb zk off)%bool
          then match xhi allkn n, xlo allkn zn with
               | Some nh, Some zl => Z.leb (off + nh) (zk + zl)
               | _, _ => false
               end
          else false)
      then true
      else if (Z.eqb (c' mod 256) (c mod 256) && xinside allkn b off n zb zk zn)%bool then true
      else kfill_x allkn rest b off n c
  | _ :: rest => kfill_x allkn rest b off n c
  end.

Fixpoint kfill_xB (bc : bctx) (k : list kentry) (b : expr) (off : Z) (n : expr) (c : Z) : bool :=
  match k with
  | [] => false
  | KFill (SA zb zk) zn c' :: rest =>
      if (if (Z.eqb (c' mod 256) (c mod 256) && expr_eqb b zb && Z.leb zk off)%bool
          then match xhiB bc n, xloB bc zn with
               | Some nh, Some zl => Z.leb (off + nh) (zk + zl)
               | _, _ => false
               end
          else false)
      then true
      else if (Z.eqb (c' mod 256) (c mod 256) && xinsideB bc b off n zb zk zn)%bool then true
      else kfill_xB bc rest b off n c
  | _ :: rest => kfill_xB bc rest b off n c
  end.

Lemma kfill_xB_eqf : forall fk, kfill_xB (mkbc fk) = kfill_x fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bh11ch21nh33offh41kh51oh62IHh71Kh82b1h92b2h:1ei001eh;2fkh<2k1i012k1h=2k2h>2n1i022n1h?2n2i032n2h@4resti041ai052a1i062a2i072c'i082hii092k0i0:2loi0;1mi0<2n0i0=2nhi0>1vi0?1wi0@1xi0A2zbi0B2zki0C2zli0D2znp;1p;2p;3p;4p;5p;6p;7p;9g00A2j1]Tg01`>j10Tg03Xdj1Kj2\j3Rj4Gj5Cj66Tg03Yhj1Dj2Uj3Jj4Ej5Bj61Tg00fXj1VTg00GYj2@Tg03Zkj13Tg03[Pj1TTg03C9j29Tg03[nj2>Tg01L=j2<Tg019Ij22Tg01N<j27Tg03S\j2Ij1ATg03K?j2Fj1PTg01M_j2:Tg03L?j7Hj1[Tg03T\j2=j1NTg03MCj2?j1OTg03N@j7;j1LTg00FUR0j1MTg03OAj1QTg00>Oj68Tg03UYj1STg03PEj1ZTg00Lej3YTg00`3l9WTg02DZj55Tg001kj3XTg00OER1f1R2f0R33Xp=4g014BR4#]R5P5g00]=R6g00^=R7P1^17R8^26R9]3R:]0%03#K%D3P6P:%02/\31U23P7P9f2R9#0?R23AJ923P6P8f3R8#0P9P2P3CGP8P9P2P3CEP7P1f4R:#0P8P9P2P3DCP:P8P9P2P3DBP4f:R;#0P:P8P9P2P3E6P;P:P8P9P2P3E1'4^17^26^37^06X45f9R<%V4P8P9P2P3E1,@1X17X26X37X06f;R=#0P:P8P9P2P3E6P=P:P8P9P2P3E1'4^17^26^37^06P1f<R>f5R?P8P9P2P3E1P4P1f7R@P8P9P8P9P9P8P9P:g018HRAP1P9P1P1P1P1g03\K#3#3#3#3#3#3#3#3#TRB,99RCf6RD/9B'>RE1<<2'2f8RF,73'2RGP0P7P1fBRH#0RI/I@P0P7P1fCRJ#0/F:1:;21:93RK'7RLg00PERMn10110@00021010C00RNPMn10110@00021010=00PMn0100000020000ROg00OeRPP1P1PIP<PFP@P2P3P8FH,2EPPP?n0100000020000n0100000020000n0110400012010A10BP9n01109000:3010410?10>2010410<3010410<1012010:1082010010;3010010:1082010410<401051021061033010410D1072010410<P4P1P@f@P<P@PDP?P:E1RIf?PFPDP?P:P8E1RQPIPQPQPIPQfARRP;PFP@PDP?E1R;PAP1P9P1P1P1P1PGP0P7P11=H@RSP0P7P11?J:PLPMn10110@00021010C00PMn10110@00021010=00PMn0100000020000PPP1P1PHP<PFP@P2P3P8F;,2EPPPHP=P<PFP@PDE1R=n0100000020000RJn0100000020000n0110400012010A10BPQn01109000:3010410?10>2010410<3010410<1012010:1082010010;3010010:1082010410<401051021061033010410D1072010410<RT'4X01P1^?6^=7^96^>6^<7^86RU%L>P4P1P@PIPQPIPQPQPIPQP;PAP1P9P1P1POPPP1P1P?P<PFP@P2P3P8O6,2EPPP=n0100000020000n0100000020000n0110400012010A10BPQn01109000:3010410?10>2010410<3010410<1012010:1082010010;3010010:1082010410<401051021061033010410D1072010410</4TX0U%M7^:6RU%N>P4P1P@PIPQPIPQPQPIPQP;PAP1P9P1P1P1P1PGP0P7P1P?P@O1PNPMn10110@00021010=00PMn0100000020000PPPJn0100000020000n0110400012010A10BPQn01109000:3010410?10>2010410<3010410<1012010:1082010010;3010010:1082010410<401051021061033010410D1072010410</4TX5UPU%O>P4P1P@PIPQPIPQPQPIPQP;PAP1P9P1P1P1P1PGP0P7P1PSP0P7P1PDP:O1PLPMn10110@00021010C00PMn10110@00021010=00PMn0100000020000PPPJn0100000020000n0110400012010A10BPQn01109000:3010410?10>2010410<3010410<1012010:1082010010;3010010:1082010410<401051021061033010410D1072010410</4TX5UP4P1PDPQf>P@P?P:P8P9E1RUPQPUPUPQPUPIPAP1P9P1P1P1P119?B,>CRC1<F2'2173@'2P0P7P11=RDP0P7P11?H:1:<2/7KPMn10110@00021010C00PMn10110@00021010=00PMn0100000020000PPP1P1PRPFP@PDP2P3P8F;,2CPPP;n0100000020000n0100000020000n0110400012010A10BPUn01109000:3010410?10>2010410<3010410<1012010:1082010010;3010010:1082010410<401051021061033010410D1072010410<,@1%0>R1#P%Q>E8%A1%S>E8%[1%Z>E8P1P?P8P9P2P3E6P:P8P9P2P3O4E8P1AY4D?RDP8P9P2P3E6P>PDP8P9P2P3E1'4eX17X26X37X06W6X@5X74P:P8P9P2P3M9WX17D5X26D5X37D5X06D5X45D5W;o"). Qed.
#[local] Hint Rewrite kfill_xB_eqf : bceq.



(* [comment removed for export] *)
Definition off_image_x (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  ranges_apart_x k b off n (ELit 0) (img_lo A) (ELit (img_hi A - img_lo A)).

Definition off_image_xB (bc : bctx) (b : expr) (off : Z) (n : expr) : bool :=
  ranges_apart_xB bc b off n (ELit 0) (img_lo A) (ELit (img_hi A - img_lo A)).

Lemma off_image_xB_eqf : forall fk, off_image_xB (mkbc fk) = off_image_x fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01bh12b1h22b2h32fkh42k1h52k2h61nh72n1h82n2h93offh:1xh;2x0h<2x1p;1p;2p;3p;7p;6p;4p;5g00A2j1ETg01`>j10Tg03]0j1;j2Dj3<j4?Tg03^8j15j2Bj3:j4@Tg02@>j16j74Tg00Pej13Tg03_?j17Tg03`Aj18Tg02AFj29Tg001kj32Tg00GYj2CTg02B@j1ATg02CKj1=Tg00>Oj6>Tg02DZj51Tg014B#Eg00]=R0g00^=R1g00OER2^60R3]9f0R4#0#;%54P1P3f1R3#0/D41B34P0P2f2R5#0?<34A:534P2^80^51^20^70^41^10R6f3R7#6P4P7P5P3g02E\#3R8p,1AR9#7R:%89/9:#3R9O6f4P7P5P3P8P:P9F4522X06P7P5P3P4P8P:P9F4,C2%07R9#A%=7E>P9P5P3P4C?P7P5P3P4C@522eX<0D1X;1D1X:0D1W3o"). Qed.
#[local] Hint Rewrite off_image_xB_eqf : bceq.



(* [comment removed for export] *)

(* [comment removed for export] *)
Definition flat_x (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match base_range k b, xlo k n, xhi k n with
  | Some (lo, hi), Some nl, Some nh => (Z.leb 0 (lo + off) && Z.leb (hi + off + nh) two64 && Z.ltb 0 nl)%bool
  | _, _, _ => false
  end.

Definition flat_xB (bc : bctx) (b : expr) (off : Z) (n : expr) : bool :=
  match base_rangeB bc b, xloB bc n, xhiB bc n with
  | Some (lo, hi), Some nl, Some nh => (Z.leb 0 (lo + off) && Z.leb (hi + off + nh) two64 && Z.ltb 0 nl)%bool
  | _, _, _ => false
  end.

Lemma flat_xB_eqf : forall fk, flat_xB (mkbc fk) = flat_x fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01oh11eh22fkh31nh43offh51xi001xh62x0h72x1i012hii022loi032nhi042nli051pp;1p;2p;3p;6p;4p;5g00A2j1QTg01`>j11Tg03aCj1Bj2Pj3Gj4LTg03bFj1>j2Oj3Aj4MTg00FUR0j17Tg03T\j1?j28Tg00bVR1j2=Tg03cHj2<j1ETg03K?j2;j1HTg01M_j20Tg01N<j24Tg019Ij22Tg02Acj2NTg03dOj2:j1CTg03MCj29j1FTg001kj33Tg00GYj2DTg03eSj1@Tg00>Oj66Tg03OAj1ITg03S\j1JTg03UYj1KTg02DZj55Tg014B#Qg00]=R2g00^=R3g00OER4^32R5]4f0R6#1#B%>6P3P5f1R5#1/P61O56P2P4f2R7#1?G56AA756%73^12R8f3R9#?P01=33R:P4f4R;#1/<9R<P1P3P3P4P6P0P3P4f7R=#1/;;P0P3P4P;f5R>O1g02E\R?109='4107=/06g02F:R@'4'21N?5RA'2RBg00PERCn10110000021010300PCn10110000021010400n2001105000120102101PCn10110000021010500P0P:P41:;9P1P3P3P4P6P0P3P419=;P0P3P4f8/8>PBPCn10110000021010300RBPCn10110000021010400n2001105000120102101R>PCn10110000021010500RD534X08P8%F9P0P:P4P<P1P3P3P4P6P0P3P4P9P;O1PBPCn10110000021010400n2001105000120102101PCn10110000021010500=34DX08%7:^12R8%C9P0P:P4P6P9O1P>PCn10110000021010500=34DX08P0P:P41:97P1P3P3P4P6P0P3P4f6R1/99P0P3P418=;1091,4?1071/06/4@'2/2APCn10110000021010300PCn10110000021010400n2001105000120102101PCn10110000021010500,D4%19RC#E%@9E6%HC%I9E6%JC%K9E6PCP7P5P6CLP9P7P5P6CM534eX72D5X63D5X52D5W2o"). Qed.
#[local] Hint Rewrite flat_xB_eqf : bceq.



(* [comment removed for export] *)
Definition ehi (k : list kentry) (e : expr) : option Z := xhi k e.
Definition elo (k : list kentry) (e : expr) : option Z := xlo k e.

(* [comment removed for export] *)
Definition len_eqb (k : list kentry) (n m : expr) : bool :=
  expr_eqb n m || (lin_ge0 k [(n, 0%Z)] [(m, 0%Z)] && lin_ge0 k [(m, 0%Z)] [(n, 0%Z)]).

Definition len_eqbB (bc : bctx) (n m : expr) : bool :=
  expr_eqb n m || (lin_ge0B bc [(n, 0%Z)] [(m, 0%Z)] && lin_ge0B bc [(m, 0%Z)] [(n, 0%Z)]).

Lemma len_eqbB_eqf : forall fk, len_eqbB (mkbc fk) = len_eqb fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01bh12fkh21mh33negh43posh51xh62x0p;1p;2p;3p;6p;5p;4g00A2j1GTg01`>j12Tg03f^j1=j2Fj3@Tg03gbj1:j2Ej3ATg03hej1>j30Tg01L=j27Tg00bVj2;Tg00fXj19Tg00Lej31Tg019Ij23Tg00H3j25Tg001kj38Tg00GYj2DTg03ifj1CTg03jjj1BTg00>Oj6?Tg02DZj56Tg03l2j4<Tg00]=R0g00^=R1f0R2g02E\C<p=4g014B#GP0g00OER3^20%22#=%:2P0P3f1R4#2/F21E42g03lRR5P3^35]4R5f2R6#>1764R7P21;01R1%46%91R831R9%44=118R:O2P2P:P9O2'3'5f3R;?09:A0;:9'3,57583X051742%42=118R8906:A068:'3'5,D3%26R8#C%B6E?A@842AA642583eX60D6X50D6W1o"). Qed.
#[local] Hint Rewrite len_eqbB_eqf : bceq.



(* [comment removed for export] *)
Definition lit_diff (e f : expr) : option Z :=
  match esub e f with ELit z => Some (z mod two64) | _ => None end.

(* [comment removed for export] *)
Definition page_aligned (k : list kentry) (e : expr) : bool :=
  match e with
  | ELit z => Z.eqb (z mod 4096) 0
  | _ => Z.leb 12 (ealign k e)
  end.

Definition page_alignedB (bc : bctx) (e : expr) : bool :=
  match e with
  | ELit z => Z.eqb (z mod 4096) 0
  | _ => Z.leb 12 (ealignB bc e)
  end.

Lemma page_alignedB_eqf : forall fk, page_alignedB (mkbc fk) = page_aligned fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01ei001eh12fkh21xh31zi011zi021ai031bi042e0i051ii061ki072k0i082loi091ni0:2opi0;2sxp;1p;2p;3p;6p;5g00A2j1DTg01`>j16Tg03mRj1;j2>Tg03n[j17j2?Tg03ocj1Cj22Tg03[Pj15Tg03C9j2:Tg03[nj29Tg040cj18Tg01N<j20Tg001kj33Tg00GYj2BTg041Hj1ATg042Kj1@Tg00>Oj6=Tg02DZj5<Tg03Zkj14Tf0R0#4#4p=1g014B#Dg00]=R1g00OER2%60#;%70g00^=^01R3f1R4#CP1P2P4g03\KR5#1#1#1#1#1#1#5,:0g02E\'9R6%85#1#5R5P4f2R7O1'0f3R8f4R9O1,05R:P:P:P:P9f5R:O1,05R;P;n01100000810101101093010:1021033010:1021033010:1021033010:1021034010;1081091044010;106105109P1P2P4P61287,0512:9,05R;P;P;P;f6/2:,05R:P:n01100000810101101093010:1021033010:1021033010:1021033010:1021034010;1081091044010;107105109532X33P1P2P0P61274,051298,05R5P5P5P5P;P;n01100000810101101093010:1021033010:1021033010:1021033010:1021034010;1081091044010;107105109,B2%64R;#A%@4E=1>;01?40532eX21D<W1o"). Qed.
#[local] Hint Rewrite page_alignedB_eqf : bceq.



(* [comment removed for export] *)
Definition kn_contra (k : list kentry) : bool :=
  existsb (fun K => match K with
                    | KRange e lo hi =>
                        if Z.ltb hi lo then true else
                        match e with
                        | EVar _ => false
                        | _ => let l := lin_of e in
                               match snd l with
                               | _ :: _ :: _ =>
                                   match lin_range (erange k) (fst l) (snd l) with
                                   | Some (a, b) => (Z.leb 0 a && Z.ltb b two64 && (Z.ltb b lo || Z.ltb hi a))%bool
                                   | None => false
                                   end
                               | _ => false
                               end
                        end
                    | _ => false
                    end) k.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition caller_saved : list nat := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.

Fixpoint sr_fresh (sr : list expr) (ixs : list nat) (nx : nat) : list expr :=
  match ixs with
  | [] => sr
  | i :: t => sr_fresh (sr_upd sr i (EVar nx)) t (S nx)
  end.

Definition NCS : nat := 16.

Definition ret_lit (cs : acs) : option Z :=
  match reg cs 1 with
  | ELit r => if (Z.eqb (r mod 2) 0 && Z.ltb r two64 && Z.leb 0 r)%bool then Some r else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition after_call (cs : acs) (ret : Z) (rv : option expr) (k' : list kentry) : option acs :=
  let ss := a_ss cs in
  let nx := s_next ss in
  let sr1 := sr_fresh (s_regs ss) caller_saved nx in
  let sr2 := match rv with Some e => sr_upd sr1 10 e | None => sr1 end in
  if (fresh_ok cs && kn_vars_lt nx k' && match rv with Some e => expr_vars_lt nx e | None => true end)%bool
  then Some (with_ss cs (mk_ss ret sr2 k' (nx + NCS)))
  else None.
(* [comment removed for export] *)
Definition after_call2 (cs : acs) (ret : Z) (rv : option expr) (k' : list kentry) (extra : nat) : option acs :=
  let ss := a_ss cs in
  let nx := s_next ss in
  let sr1 := sr_fresh (s_regs ss) caller_saved nx in
  let sr2 := match rv with Some e => sr_upd sr1 10 e | None => sr1 end in
  if (fresh_ok cs && kn_vars_lt (nx + NCS + extra) k' && match rv with Some e => expr_vars_lt nx e | None => true end)%bool
  then Some (with_ss cs (mk_ss ret sr2 k' (nx + NCS + extra)))
  else None.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition page_up (len : Z) : Z := ((len + 4095) / 4096) * 4096.

Definition is_ecall_at (cs : acs) : bool :=
  (Z.leb 0 (pc cs) && Z.ltb (pc cs + 4) two64 &&
  match fetch_word segs (Z_to_bv 64 (pc cs)) with
  | Some w => is_ecall w
  | None => false
  end)%bool.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition xlo1 (k : list kentry) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erange k e, lin_brange k e with
         | Some (lo, _), Some (lo', _) => Some (Z.max lo lo')
         | Some (lo, _), None => Some lo
         | None, Some (lo', _) => Some lo'
         | None, None => match lin_srange k e with Some (lo, _) => Some lo | None => None end   (* [comment removed for export] *)
         end
  end.

Definition xlo1B (bc : bctx) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erangeB bc e, lin_brangeB bc e with
         | Some (lo, _), Some (lo', _) => Some (Z.max lo lo')
         | Some (lo, _), None => Some lo
         | None, Some (lo', _) => Some lo'
         | None, None => match lin_srangeB bc e with Some (lo, _) => Some lo | None => None end   (* [comment removed for export] *)
         end
  end.

Lemma xlo1B_eqf : forall fk, xlo1B (mkbc fk) = xlo1 fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01oh11ei001eh22fkh31xi011xi021ai031bi042e0i051ii061ki072k0i082loi093lo'i0:1ni0;2opi0<1pi0=2p0i0>2sxi0?1zi0@2z0p;1p;2p;3p;6p;5g00A2j1MTg00FUR0j19Tg01`>j12Tg043Rj1<j2GTg044Sj1Lj2=Tg00bVR1j2KTg045Sj1Dj20Tg046Wj1@Tg00G7j28Tg047Wj27j1BTg048Zj2;Tg0497j25j1?Tg00n=j1:Tg04:>j23j1HTg04;>j21j1JTg001kj34Tg00GYj2CTg04<Bj1ATg00>Oj66Tg04=Ij1ETg04>Tj1>Tg04?[j1FTg02DZj5ITg014B#Mg00]=R2g00^=R3#9R4f0R5#2#<%L51K33R6#9^12R7f1R8#DP2P4P8%@5,83R9P0P6P4f3R:#2R;f2R<'7R=P1P3P3P4P5P0P6P4f4R>f5R?O1R@P1P3P3P4P51;>8,83n200110=00012010910@RA1838RBn10110100021010=00n200110<00012010810?P0P6P4P8P<O1RCP1P3P3P4P5PBn200110<00012010910?RDP0P6P415;<P1P3P3P4P5PBn200110<00012010810?R;%:3REn10110100021010<00n10110100021010<00n10110100021010<00P0P6P4%2?RF/7>RGP1P3P3P4P5P0P6P4f6RHf7RIO1PAPBn10110100021010=00n200110<00012010810?P0P6P4P:P>O1RJPDP0P6P415F>P;PEn10110100021010<00n10110100021010<00n10110100021010<00RFPFPFPFP0P6P4%2HRF/7?RKP1P3P3P4P5P0P6P4PIf8RLO1PAPBn10110100021010=00n200110<00012010810?P0P6P4P@PDP0P6P415F?P;PEn10110100021010<00n10110100021010<00n10110100021010<00RFPFn0110000081010?1010:3010;1021033010;1021033010;1021033010;1021034010>10810:1044010>10610510:P2P4P8P9P0P6P413:<P1P3P3P4P5P0P6P410H?RFPAPBn10110100021010=00n200110<00012010810?RMP0P6P410:<RNPDP0P6P411:<P;PEn10110100021010<00n10110100021010<00ROn10110100021010<00P0P6P413?>P1P3P3P4P5P0P6P410LIPAPBn10110100021010=00n200110<00012010810?RPP0P6P410?>RQPDP0P6P411?>P;PEn10110100021010<00n10110100021010<00RRn10110100021010<00RSPSPSPSP0P6P413H?P1P3P3P4P5P0P6P4f9/0LPAPBn10110100021010=00n200110<00012010810?RLP0P6P4PFPDP0P6P411H?P;PEn10110100021010<00n10110100021010<00R?n10110100021010<00RTPTn0110000081010?1010:3010;1021033010;1021033010;1021033010;1021034010>10810:1044010>10710510:RT544X07P7%J8P2P4P8P9P0P6P4P=PMP0P6P4PNPDP0P6P4PCP;PEn10110100021010<00n10110100021010<00n10110100021010<00P0P6P4PGPPP0P6P4PQPDP0P6P4PJP;PEn10110100021010<00n10110100021010<00n10110100021010<00RGPGPGPGP0P6P4PKPLP0P6P4PFPDP0P6P4P@P;PEn10110100021010<00n10110100021010<00n10110100021010<00RFPFn0110000081010?1010:3010;1021033010;1021033010;1021033010;1021034010>10810:1044010>10610510:=44TX07P7%H8P2P4P8P9P0P6P4PCPMPOn10110100021010<00P0P6P4PJPPPRn10110100021010<00RRPRPRPRP0P6P4P@PLP?n10110100021010<00R?P?n0110000081010?1010:3010;1021033010;1021033010;1021033010;1021034010>10810:1044010>10610510:=44TX07P2P4P5P9P0P6P413<8P1P3P3P4P5P0P6P4PQPAPBn10110100021010=00n200110<00012010810?P0P6P410<8PDP0P6P411<8P;PEn10110100021010<00n10110100021010<00n10110100021010<00P0P6P413>:P1P3P3P4P5P0P6P410IHPAPBn10110100021010=00n200110<00012010810?P0P6P410>:PDP0P6P411>:P;PEn10110100021010<00n10110100021010<00n10110100021010<00REPEPEPEPSPSn0110000081010?1010:3010;1021033010;1021033010;1021033010;1021034010>10810:1044010>10710510:,C4%28RS#B%A8E6%?S%E8E6%>S%F8E61GS51=85544eX32DIW2o"). Qed.
#[local] Hint Rewrite xlo1B_eqf : bceq.


Definition xhi1 (k : list kentry) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erange k e, lin_brange k e with
         | Some (_, hi), Some (_, hi') => Some (Z.min hi hi')
         | Some (_, hi), None => Some hi
         | None, Some (_, hi') => Some hi'
         | None, None => match lin_srange k e with Some (_, hi) => Some hi | None => None end   (* [comment removed for export] *)
         end
  end.

Definition xhi1B (bc : bctx) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erangeB bc e, lin_brangeB bc e with
         | Some (_, hi), Some (_, hi') => Some (Z.min hi hi')
         | Some (_, hi), None => Some hi
         | None, Some (_, hi') => Some hi'
         | None, None => match lin_srangeB bc e with Some (_, hi) => Some hi | None => None end   (* [comment removed for export] *)
         end
  end.

Lemma xhi1B_eqf : forall fk, xhi1B (mkbc fk) = xhi1 fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01oh11ei001eh22fkh31xi011xi021ai031bi042e0i052hii063hi'i071ii081ki092k0i0:2loi0;1ni0<2opi0=1pi0>2p0i0?2sxi0@1zi0A2z0p;1p;2p;3p;6p;5g00A2j1MTg00FUR0j19Tg01`>j12Tg04@fj1<j2GTg04Agj1Lj2=Tg00bVR1j2KTg045Sj1Dj20Tg046Wj1@Tg00G7j28Tg047Wj27j1BTg04Bgj2;Tg0497j25j1?Tg00n=j1:Tg04:>j23j1HTg04;>j21j1JTg001kj34Tg00GYj2CTg04<Bj1ATg00>Oj66Tg04=Ij1ETg04>Tj1>Tg04?[j1FTg02DZj5ITg014B#Mg00]=R2g00^=R3#9R4f0R5#2#<%L51K33R6#9^12R7f1R8#DP2P4P8%@5,83R9P0P6P4f3R:#2R;f2R<'7R=P1P3P3P4P5P0P6P4f4R>f5R?O1R@P1P3P3P4P51;:5,83n200110>00012010A106RA1835RBn10110100021010>00n200110=00012010@105P0P6P4P8P<O1RCP1P3P3P4P5PBn200110=00012010@106RDP0P6P415;<P1P3P3P4P5PBn200110=00012010@105R;%:3REn10110100021010=00n10110100021010=00n10110100021010=00P0P6P4%2?RF/7>RGP1P3P3P4P5P0P6P4f6RHf7RIO1PAPBn10110100021010>00n200110=00012010@105P0P6P4P:P>O1RJPDP0P6P415F>P;PEn10110100021010=00n10110100021010=00n10110100021010=00RFPFPFPFP0P6P4%2HRF/7?RKP1P3P3P4P5P0P6P4PIf8RLO1PAPBn10110100021010>00n200110=00012010@105P0P6P4P@PDP0P6P415F?P;PEn10110100021010=00n10110100021010=00n10110100021010=00RFPFn0110000081010@1010;3010<1021033010<1021033010<1021033010<1021034010?10:10;1044010?10810710;P2P4P8P9P0P6P413:<P1P3P3P4P5P0P6P410H?RFPAPBn10110100021010>00n200110=00012010@105RMP0P6P410:<RNPDP0P6P411:<P;PEn10110100021010=00n10110100021010=00ROn10110100021010=00P0P6P413?>P1P3P3P4P5P0P6P410LIPAPBn10110100021010>00n200110=00012010@105RPP0P6P410?>RQPDP0P6P411?>P;PEn10110100021010=00n10110100021010=00RRn10110100021010=00RSPSPSPSP0P6P413H?P1P3P3P4P5P0P6P4f9/0LPAPBn10110100021010>00n200110=00012010@105RLP0P6P4PFPDP0P6P411H?P;PEn10110100021010=00n10110100021010=00R?n10110100021010=00RTPTn0110000081010@1010;3010<1021033010<1021033010<1021033010<1021034010?10:10;1044010?10910710;RT544X07P7%J8P2P4P8P9P0P6P4P=PMP0P6P4PNPDP0P6P4PCP;PEn10110100021010=00n10110100021010=00n10110100021010=00P0P6P4PGPPP0P6P4PQPDP0P6P4PJP;PEn10110100021010=00n10110100021010=00n10110100021010=00RGPGPGPGP0P6P4PKPLP0P6P4PFPDP0P6P4P@P;PEn10110100021010=00n10110100021010=00n10110100021010=00RFPFn0110000081010@1010;3010<1021033010<1021033010<1021033010<1021034010?10:10;1044010?10810710;=44TX07P7%H8P2P4P8P9P0P6P4PCPMPOn10110100021010=00P0P6P4PJPPPRn10110100021010=00RRPRPRPRP0P6P4P@PLP?n10110100021010=00R?P?n0110000081010@1010;3010<1021033010<1021033010<1021033010<1021034010?10:10;1044010?10810710;=44TX07P2P4P5P9P0P6P413<8P1P3P3P4P5P0P6P4PQPAPBn10110100021010>00n200110=00012010@105P0P6P410<8PDP0P6P411<8P;PEn10110100021010=00n10110100021010=00n10110100021010=00P0P6P413>:P1P3P3P4P5P0P6P410IHPAPBn10110100021010>00n200110=00012010@105P0P6P410>:PDP0P6P411>:P;PEn10110100021010=00n10110100021010=00n10110100021010=00REPEPEPEPSPSn0110000081010@1010;3010<1021033010<1021033010<1021033010<1021034010?10:10;1044010?10910710;,C4%28RS#B%A8E6%?S%E8E6%>S%F8E61GS51=85544eX32DIW2o"). Qed.
#[local] Hint Rewrite xhi1B_eqf : bceq.



(* [comment removed for export] *)
Fixpoint deand (e : expr) : expr * Z :=
  match e with
  | EAlu ALU_AND x (ELit m) =>
      let m' := m mod two64 in
      let j := Z.log2 (two64 - m') in
      if (Z.eqb (two64 - m') (2 ^ j) && Z.leb j 48)%bool
      then let '(x', s) := deand x in (x', s + (2 ^ j - 1))
      else (e, 0)
  | EAlu ALU_ADD a b => let '(a', s1) := deand a in let '(b', s2) := deand b in (EAlu ALU_ADD a' b', s1 + s2)
  | _ => (e, 0)
  end.

Definition xb2 (k : list kentry) (e : expr) : option (Z * Z) :=
  let plain := match xlo1 k e, xhi1 k e with Some lo, Some hi => Some (lo, hi) | _, _ => None end in
  let '(e', s) := deand e in
  if Z.eqb s 0 then plain else
  match xlo1 k e', xhi1 k e' with
  | Some lo', Some hi' =>
      if Z.leb s lo' then
        match plain with
        | Some (lo, hi) => Some (Z.max lo (lo' - s), Z.min hi hi')
        | None => Some (lo' - s, hi')
        end
      else plain
  | _, _ => plain
  end.

Definition xb2B (bc : bctx) (e : expr) : option (Z * Z) :=
  let plain := match xlo1B bc e, xhi1B bc e with Some lo, Some hi => Some (lo, hi) | _, _ => None end in
  let '(e', s) := deand e in
  if Z.eqb s 0 then plain else
  match xlo1B bc e', xhi1B bc e' with
  | Some lo', Some hi' =>
      if Z.leb s lo' then
        match plain with
        | Some (lo, hi) => Some (Z.max lo (lo' - s), Z.min hi hi')
        | None => Some (lo' - s, hi')
        end
      else plain
  | _, _ => plain
  end.

Lemma xb2B_eqf : forall fk, xb2B (mkbc fk) = xb2 fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01oh11eh22fkh31xi001xi012e'i022hii033hi'i042loi053lo'i061pi075plaini081sp;1p;2p;3p;6p;5p;4g00A2j1NTg00bVR0j2MTg00FUR1j19Tg01`>j12Tg04CDj1Lj2GTg04DDj1Dj2<Tg04Agj1@j20Tg04ECj18Tg03[nj2=Tg043Rj23j1?Tg00G7j26Tg00n=j1;Tg01N<j2KTg02AFj2:Tg048Zj2HTg04Bgj2CTg044Sj21j1ATg001kj35Tg00GYj2BTg04FDj1>Tg00>Oj67Tg04@fj1ETg04GIj1FTg02DZj5ITg03l2j4JTg00^=R2P2f1R3f0R4CJp=4g014B#Ng00]=R51M22R6#9R7%24#L%D4%92^15R8%@3P0P5P2P7%83R9g00OER:P7g02E\,=4R;P1P2P7f4R<#2R=f3R>'3P1P2P7P>P<O1R?1434,66R@%;6RAn10110000021010200PAn10110000021010400RBP1P2P713=3P1P2P7P>f2R=O1P:P71K=3RCP1P6P7P1P2P7f6RD#2f5RE'3P1P2P7PEPDO1P@PAn10110000021010200PAn10110000021010400RFP0P2P2P7P41:<E,H31C4>'4,66n2001106000120104102RG1:3=/44,66RHn10110700021010600PFn0100000020000P1P2P7%2E/3<P1P2P7P<PEO1RFP@PAn10110000021010200PAn10110000021010400n10110000021010300PBn10110000021010500n0100000020000n2001100000121101108P0P5P2P7P9P:P7P;P1P2P711<>P1P2P710E<P@PAn10110000021010200RBPAn10110000021010400RIP1P2P711<3P1P2P710E=RJP:P7PCP1P6P7P1P2P711DEP1P2P7f7/0DP@PAn10110000021010200RKPAn10110000021010400RLPGPHn10110700021010600PLn0100000020000P1P2P711E<P1P2P710DEP@PAn10110000021010200REPAn10110000021010400RDn10110000021010300PIn10110000021010500n0100000020000n2001100000121101108RL557X08P8%A3P0P5P2P7P9P:P7P;P1P2P7P=P>O1PBPAn10110000021010400RBP1P2P7P=P3O1P1P2P7PJP:P7PCP1P6P7P1P2P7PFPKPAn10110000021010400RKPGPHn10110700021010600PKn0100000020000P1P2P7P?PEPAn10110000021010400n10110000021010300PBn10110000021010500n0100000020000n2001100000121101108=57LX08P0P5P2P7%84P:P7P;P1P2P711>=P1P2P710<>P@PAn10110000021010200PAn10110000021010400RAP1P2P711>3P1P2P710<=P:P7PCP1P6P7PDPGPHn10110700021010600PDn0100000020000PIn10110000021010300PAn10110000021010500n0100000020000n2001100000121101108,B7%23RA#?%>3E7%EA%F3E71GA41<34557eX35DIW2o"). Qed.
#[local] Hint Rewrite xb2B_eqf : bceq.


Definition xlo2 (k : list kentry) (e : expr) : option Z := match xb2 k e with Some (lo, _) => Some lo | None => None end.

Definition xlo2B (bc : bctx) (e : expr) : option Z := match xb2B bc e with Some (lo, _) => Some lo | None => None end.

Lemma xlo2B_eqf : forall fk, xlo2B (mkbc fk) = xlo2 fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01eh12fkh21oh31xi001xi012loi021pi031zp;1p;2p;3p;6p;5g00A2j1ATg00FUR0j13Tg01`>j12Tg04HNj14j2;Tg04IOj1@j2<Tg00bVR1j2:Tg04DDj17j20Tg00G7j25Tg00n=j16Tg001kj31Tg00GYj28Tg04CDj19Tg04JOj1?Tg00>Oj6>Tg02DZj5=Tg014B#Ag00]=R2g00^=R3#3R4f0R5#2#4%@51:33R6#3^02R7f1R8#7P0P6P4P5P8O1P1P3P3P4P51538n2001102000120101103R1%63R3n10110000021010200P0P6P4f2/08P1P3n10110000021010200514X27P0P6P41085P1P3n10110000021010200,84%28R3#9%?8E>1;351<85514eX32D=W1o"). Qed.
#[local] Hint Rewrite xlo2B_eqf : bceq.


Definition xhi2 (k : list kentry) (e : expr) : option Z := match xb2 k e with Some (_, hi) => Some hi | None => None end.

Definition xhi2B (bc : bctx) (e : expr) : option Z := match xb2B bc e with Some (_, hi) => Some hi | None => None end.

Lemma xhi2B_eqf : forall fk, xhi2B (mkbc fk) = xhi2 fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01eh12fkh21oh31xi001xi012hii021pi031zp;1p;2p;3p;6p;5g00A2j1ATg00FUR0j13Tg01`>j12Tg04KSj14j2;Tg04LTj1@j2<Tg00bVR1j2:Tg04DDj17j20Tg00G7j25Tg00n=j16Tg001kj31Tg00GYj28Tg04CDj19Tg04JOj1?Tg00>Oj6>Tg02DZj5=Tg014B#Ag00]=R2g00^=R3#3R4f0R5#2#4%@51:33R6#3^02R7f1R8#7P0P6P4P5P8O1P1P3P3P4P51535n2001102000120103101R1%63R3n10110000021010200P0P6P4f2/08P1P3n10110000021010200514X27P0P6P41085P1P3n10110000021010200,84%28R3#9%?8E>1;351<85514eX32D=W1o"). Qed.
#[local] Hint Rewrite xhi2B_eqf : bceq.

(* [comment removed for export] *)
Definition crange (k : list kentry) (e : expr) : option (Z * Z) :=
  match erange k e with Some r => Some r | None => xb2 k e end.



(* [comment removed for export] *)
Definition fact_ok (k : list kentry) (K : kentry) : bool :=
  match K with
  | KRange e lo hi =>
      match xlo2 k e, xhi2 k e with
      | Some l, Some h => Z.leb lo l && Z.leb h hi
      | _, _ => false
      end
  | KAlign e m => Z.ltb 0 m && Z.eqb m (2 ^ (Z.log2 m)) && Z.leb (Z.log2 m) (ealign k e)
  | KDisj (SA b1 k1) n1 (SA b2 k2) n2 => ranges_apart_x k b1 k1 n1 b2 k2 n2
  | _ => false
  end.

(* [comment removed for export] *)
Fixpoint kread_bytes (fuel : nat) (k : list kentry) (b : expr) (off : Z) : option (list Z) :=
  match fuel with
  | O => Some []
  | S f => match kreadZ k b off 1, kread_bytes f k b (off + 1) with
           | Some z, Some rest => Some (z :: rest)
           | _, _ => None
           end
  end.

Fixpoint kread_bytesB (bc : bctx) (fuel : nat) (b : expr) (off : Z) : option (list Z) :=
  match fuel with
  | O => Some []
  | S f => match kreadZB bc b off 1, kread_bytesB bc f b (off + 1) with
           | Some z, Some rest => Some (z :: rest)
           | _, _ => None
           end
  end.

Lemma kread_bytesB_eqf' : forall fk fuel, kread_bytesB (mkbc fk) fuel = kread_bytes fuel fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bh14fuelh21oh33offh41xi001xh52x0h62IHh71fh82fkh91ni014resti021zp;1p;2p;3p;4p;5p;6g00A2j1>Tg00FUR0j1;Tg01`>j10Tg04MTj24j39j4ATg04N\j26j38j42Tg001kj35Tg00GYj27Tg02DZj51Tg003kj13Tg03?oj4?j1CTg03[Pj1HTg01M_j2=Tg00Lej3GTg00G7j2FTg00n=j1ETg03A2j4:j1DTg04Ocj1BTg00>Oj6<Tg04Pjj4@Tg014B#>g005OR1g00]=R2g00^=R3%>3R4#;R5]3R6]0R7f2R8#0R9f0R:'416:835R;X11P2P6f1R<#0g01\YR='416=<P3P5A99=:A8=8:P=f3R9P<P:C2,75X53D1X42D1P2P6%09%3<R6'41669P3P5f4R6#0%38R>;9:A8>6:P7f5R>,69P0P3P5f6R?#0P8P<%3=R=C?P0P4P5P<P9g03\K#HR@,=8RAO2AG3<:,F4RB%E4RCn10110000021010100PCn10110000021010200P0P3P5P?P8P<P=C:P0P4P5P>f7P9PAC2PBPCn10110000021010100RAPCn10110000021010200RD555X27%;3^91^33^02R7%D>P0P3P5P:P8P<P=O3PAPCn10110000021010200=55DX27P0P3P5P>P<P:P=C:P0P4P5P6P?P81=<@C2PBPCn10110000021010100PCn10110000021010200,75%0>RC#C%B>E<14C9P8E<PC%39R9P<P:CAP9P>P<P:C2555eX53D1X42D1X6;X71P:C@W1W8o"). Qed.
Lemma kread_bytesB_eqf : forall fk, kread_bytesB (mkbc fk) = (fun fuel => kread_bytes fuel fk).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h04fuelh11bh22fkh33offp;1p;2p;5g00A2j10Tg00FUj16Tg01`>j12Tg04MTj11Tg04N\j25Tg04QKj24Tg02DZj53Tg014B#0g005OR0g00]=g00^=R1%01#6]3]1f0R1#2#1f1R2,51X001421X00D3W2o"). Qed.
#[local] Hint Rewrite kread_bytesB_eqf' kread_bytesB_eqf : bceq.


Definition node_join (cs : acs) (b : expr) (off : Z) (n : nat) : option acs :=
  if (Nat.leb 1 n && Nat.leb n 8 && flat_x (kn cs) b off (ELit (Z.of_nat n)))%bool then
    match kread_bytes n (kn cs) b off with
    | Some bs => Some (add_kn cs [KWord (SA b off) n (ELit (zbytes_le_to_Z bs))])
    | None => None
    end
  else None.

Fixpoint drop_ixs (ixs : list nat) (i : nat) (k : list kentry) : list kentry :=
  match k with
  | [] => []
  | K :: r => if existsb (Nat.eqb i) ixs then drop_ixs ixs (S i) r else K :: drop_ixs ixs (S i) r
  end.

(* [comment removed for export] *)
Definition residue_fact (k : list kentry) (e ne : expr) : list kentry :=
  let '(e', s) := deand e in
  if Z.ltb 0 s then
    match xlo1 k e', xhi1 k e' with
    | Some lo', Some _ => if Z.leb s lo' then [KRange (esub e' ne) 0 s] else []
    | _, _ => []
    end
  else [].

Definition node_fresh (cs : acs) (r : nat) (logc : Z) (base : option expr) : option acs :=
  let k := kn cs in let c := 2 ^ logc in
  let b := match base with Some b => b | None => ELit 0 end in
  let e := esub (reg cs r) b in
  if (Nat.ltb 0 r && Nat.ltb r 32 && Z.leb 0 logc && Z.leb logc 40 && Z.leb logc (ealign k e)
      && expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) e && fresh_ok cs)%bool then
    match xlo2 k e, xhi2 k e with
    | Some lo, Some hi =>
        let v := nxt cs in
        let ne := escale c (EVar v) in
        let kres := residue_fact k e ne in
        let kf := KRange (EVar v) ((lo + c - 1) / c) (hi / c) :: KRange (esub e ne) 0 0 :: kres in
        Some (bump (set_reg (add_kn cs kf) r (eadd b ne)) 1)
    | _, _ => None
    end
  else None.

(* [comment removed for export] *)
Definition node_droprange (cs : acs) (b n : expr) : acs :=
  let '(bb, bk) := split_lit b in set_kn cs (kn_havocM (kn cs) bb bk n).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition node_bump (cs : acs) (m : nat) : option acs :=
  if Nat.leb (nxt cs) m then Some (bump cs (m - nxt cs)) else None.

(* [comment removed for export] *)
Definition node_havoc (cs : acs) (rs : list nat) : option acs :=
  if (fresh_ok cs && forallb (fun r => Nat.ltb 0 r && Nat.ltb r 32) rs)%bool then
    let ss := a_ss cs in
    Some (with_ss cs (mk_ss (s_pc ss) (sr_fresh (s_regs ss) rs (s_next ss)) (s_know ss) (s_next ss + length rs)))
  else None.

(* [comment removed for export] *)
Fixpoint esize (e : expr) : nat :=
  match e with
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => S (esize a + esize b)
  | EExt _ _ _ a => S (esize a)
  | _ => 1%nat
  end.
Definition bigb (K : nat) (e : expr) : bool := Nat.ltb K (esize e).
Fixpoint kn_bigsubst (K : nat) (k : list kentry) (nx : nat) : list kentry * nat :=
  match k with
  | [] => ([], 0%nat)
  | KWord a w v :: r =>
      if bigb K v then let '(r', c) := kn_bigsubst K r (S nx) in (KWord a w (EVar nx) :: r', S c)
      else let '(r', c) := kn_bigsubst K r nx in (KWord a w v :: r', c)
  | x :: r => let '(r', c) := kn_bigsubst K r nx in (x :: r', c)
  end.
Definition node_havocbig (cs : acs) (K : nat) : option acs :=
  let rs := List.filter (fun r => bigb K (reg cs r)) (seq 1 31) in
  match node_havoc cs rs with
  | Some cs1 =>
      if fresh_ok cs1 then
        let nx1 := nxt cs1 in
        let '(k', c) := kn_bigsubst K (kn cs1) nx1 in
        Some (with_ss cs1 (mk_ss (pc cs1) (s_regs (a_ss cs1)) k' (nx1 + c)))
      else None
  | None => None
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition find_containing (k : list kentry) (ms : list amap) (kinds : list mkind) (b : expr) (off : Z) (n : expr) : option amap :=
  List.find (fun m => negb (is_fog m) && existsb (mkind_eqb (am_kind m)) kinds && xinside k b off n (am_base m) 0 (am_len m)) ms.

Definition find_containingB (bc : bctx) (ms : list amap) (kinds : list mkind) (b : expr) (off : Z) (n : expr) : option amap :=
  List.find (fun m => negb (is_fog m) && existsb (mkind_eqb (am_kind m)) kinds && xinsideB bc b off n (am_base m) 0 (am_len m)) ms.

Lemma find_containingB_eqf : forall fk, find_containingB (mkbc fk) = find_containing fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01mh11bh22b1h32b2h42fkh52k1h62k2h75kindsh81nh92n1h:2n2h;3offh<1xh=2x0h>2x1h?2x2h@2x3p;1p;2p;3p;4p;5p;7p;6g00A2j14Tg00FUj1OTg01`>j10Tg04RXj1;j2Dj3>j4<j58j6ITg04Sdj1Nj2?j3=j4:j59j6JTg03N@j1Mj75Tg04Toj1LTg01NYj1KTg04V1j1CTg04W4j1BTg008Ij36Tg019Ij22Tg00cSj1@Tg00dVj1ATg04X9j33Tg001kj37Tg00GYj2ETg03L?j1FTg03PEj1GTg00>Oj6HTg02DZj51Tg014B#4g015DR0#4R1g04XRR2#4R3g00]=R4g00^=R5%O0R6^84R7];R8]1R9]7f0R:#0#;%N:P3P9f1R9#0/D:1?9:P4P8f2R8#0?>9:A=89:P5P7f3R7#0P8P9P:C<P7P8P9P:C:P4P6f4R;#0P7P8P9P:D8P;P7P8P9P:D9g00OE^:4^65^34^94^55^24R<f5R=#M%L:#KR>%C:#BR?=62='2R@P9P;P7P8%@:RAg02E\RB%A:RCO6'2X00=30=f7P;P7P8PAPBPCF5,2@X00=30=576X1<A62?;,2>f6P7P8P9PAPBPCF5'2X00=30;,E6%0=R0#F%G=EHP0P;P7P8P9P:EIP=P;P7P8P9P:EJ576eX@4D1X?5D1X>4D1X=3D1X<1D1W4o"). Qed.
#[local] Hint Rewrite find_containingB_eqf : bceq.



(* [comment removed for export] *)
Definition xinside_sh (k : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if xinside k b1 k1 n1 b2 k2 n2 then true else xinside0 k b1 k1 n1 b2 k2 n2.
Definition xinside_shB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if xinsideB bc b1 k1 n1 b2 k2 n2 then true
  else if lin_ge0B bc [(b1, k1)] [(b2, k2)] then lin_ge0B bc [(b2, k2); (n2, 0%Z)] [(b1, k1); (n1, 0%Z)] else false.
Lemma xinside_shB_eqf : forall fk, xinside_shB (mkbc fk) = xinside_sh fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01bh12b1h22b2h32fkh42k1h52k2h62n1h72n2h83negh93posh:1xh;2x0h<2x1h=2x2h>2x3h?2x4p;1p;2p;3p;4p;5p;6p;7g00A2j1RTg01`>j11Tg04YUj1Bj2Qj3Cj4@j5=j6;j7LTg04Z\j1>j2Ij3Aj4?j5<j6Pj7MTg03N@j1Oj77Tg00bVj2NTg00fXj1HTg00Lej30Tg03ifj38j1FTg03hej35j1DTg001kj36Tg00GYj2ETg03jjj1GTg00>Oj69Tg03L?j1JTg03PEj1KTg02DZj52Tg03l2j4:Tg00]=R0g00^=R1f1R2f0R3C:p=4P0P1P3g02E\C:p=3g014B#RP0g00OER4^70R5^51R6^20R7^60R8^41R9%13#B%>3P1P8%12/Q31I23P0P7f2R7#1?C23AA723P0P6f3R6#1P7P2P3C@P6P7P2P3C?P1P5f4R5#1P6P7P2P3D=P5P6P7P2P3D<P0P4f5R8#1P5P6P7P2P3E;P8P5P6P7P2P3EPP9^10R9f6R:#OP4P4P3P:P8P5P6P7P2O6g00OeR;P4P4f7R<#1R=1N01R>14:8R?%H>R@30RA1467RB=0>@RC38%32=0>@90>BRB%35=0>@90>?R?58=g00PER=n0100000020000n0100000020000P4P4P<P:P8P5P6P7P2F7RDP;P4P4A5<ACA5<B?P=n0100000020000n0100000020000R<564X09g03lRR9P4^89]9R9%D:P4P4PDP;P4P4P3PAPCO2P3PBP?O2P=n0100000020000n0100000020000=64<X09P4P4P:P8P5P6P7P2P3F7P;P4P41485R;=0>@1472R9=0>@55:%33=0>@90>9%36=0>@90>;55:P=n0100000020000n0100000020000,E4%1:R=#F%G:E9%J=%K:E9P=P8P5P6P7P2P3FLP:P8P5P6P7P2P3FM564eX?0D2X>1D2X=0D2X<0D2X;1D2X:0D2W3o"). Qed.
#[local] Hint Rewrite xinside_shB_eqf : bceq.
Definition find_containing_sh (k : list kentry) (ms : list amap) (kinds : list mkind) (b : expr) (off : Z) (n : expr) : option amap :=
  List.find (fun m => negb (is_fog m) && existsb (mkind_eqb (am_kind m)) kinds && xinside_sh k b off n (am_base m) 0 (am_len m)) ms.
Definition find_containing_shB (bc : bctx) (ms : list amap) (kinds : list mkind) (b : expr) (off : Z) (n : expr) : option amap :=
  List.find (fun m => negb (is_fog m) && existsb (mkind_eqb (am_kind m)) kinds && xinside_shB bc b off n (am_base m) 0 (am_len m)) ms.
Lemma find_containing_shB_eqf : forall fk, find_containing_shB (mkbc fk) = find_containing_sh fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01mh11bh22b1h32b2h42fkh52k1h62k2h75kindsh81nh92n1h:2n2h;3offh<1xh=2x0h>2x1h?2x2h@2x3p;1p;2p;3p;4p;5p;7p;6g00A2j14Tg00FUj1OTg01`>j10Tg04[bj1;j2Dj3>j4<j58j6ITg04]1j1Nj2?j3=j4:j59j6JTg04Z\j1Mj75Tg04Toj1LTg01NYj1KTg04V1j1CTg04W4j1BTg008Ij36Tg019Ij22Tg00cSj1@Tg00dVj1ATg04X9j33Tg001kj37Tg00GYj2ETg04YUj1FTg04^?j1GTg00>Oj6HTg02DZj51Tg014B#4g015DR0#4R1g04XRR2#4R3g00]=R4g00^=R5%O0R6^84R7];R8]1R9]7f0R:#0#;%N:P3P9f1R9#0/D:1?9:P4P8f2R8#0?>9:A=89:P5P7f3R7#0P8P9P:C<P7P8P9P:C:P4P6f4R;#0P7P8P9P:D8P;P7P8P9P:D9g00OE^:4^65^34^94^55^24R<f5R=#M%L:#KR>%C:#BR?=62='2R@P9P;P7P8%@:RAg02E\RB%A:RCO6'2X00=30=f7P;P7P8PAPBPCF5,2@X00=30=576X1<A62?;,2>f6P7P8P9PAPBPCF5'2X00=30;,E6%0=R0#F%G=EHP0P;P7P8P9P:EIP=P;P7P8P9P:EJ576eX@4D1X?5D1X>4D1X=3D1X<1D1W4o"). Qed.
#[local] Hint Rewrite find_containing_shB_eqf : bceq.

(* [comment removed for export] *)
Definition shadow_of (k : list kentry) (b n : expr) : expr * Z * expr :=
  let '(sb, sk) := split_lit (eadd (mkSrl k b 3) (ELit (shadow_off A))) in (sb, sk, mkSrl k n 3).

Definition shadow_ofB (bc : bctx) (b n : expr) : expr * Z * expr :=
  let '(sb, sk) := split_lit (eadd (mkSrlB bc b 3) (ELit (shadow_off A))) in (sb, sk, mkSrlB bc n 3).

Lemma shadow_ofB_eqf : forall fk, shadow_ofB (mkbc fk) = shadow_of fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01ah11eh22fkh31nh41sh51xi001xh62x0i012sbi022skp;1p;2p;4p;3p;6p;5g00A2j1GTg00bVR0j27Tg01`>j13Tg04_Jj1:j2Ej3BTg04`Pj1Fj2?j3=Tg04aUj1>j31Tg040cj1<Tg03[Pj1;Tg04bTj19Tg00Pej18Tg04cZj22Tg01E@j14Tg03l2j40Tg001kj36Tg00GYj2DTg04dZj1CTg04e\j1@Tg00>Oj6ATg02DZj55Tg014B#Gg00]=R1g00^=R2,71R3/71R4^31f0R5#3#:%F5P1P4f1R6#3/E51?65P1^42^01R7f2R8#>P0P1P2P4P5P8g03\K#<#;R9O2p,1A#9#8R:'2#4P3P1P1P2P6P5C0R;P8f3R<P9O2C0n2001100000120101102P0P1P2P4A1<89/2:#4P3P1P;f5?1<9C0n2001100000120101102564X17P0P1P2P4A1869/2:#4P3P1P;f4?189C0n2001100000120101102,D4%38R9#C%@8EAAB965A=865564eX61D5X51D5W2o"). Qed.
#[local] Hint Rewrite shadow_ofB_eqf : bceq.



(* [comment removed for export] *)
Definition shadow_facts (k : list kentry) (ms : list amap) (b n : expr) : list kentry :=
  let '(sb, sk, sn) := shadow_of k b n in
  match find_containing_sh k ms [KRWLAZY] sb sk sn with
  | Some _ => [KWr (SA sb sk) sn; KZero (SA sb sk) sn]
  | None => []
  end.

Definition shadow_factsB (bc : bctx) (ms : list amap) (b n : expr) : list kentry :=
  let '(sb, sk, sn) := shadow_ofB bc b n in
  match find_containing_shB bc ms [KRWLAZY] sb sk sn with
  | Some _ => [KWr (SA sb sk) sn; KZero (SA sb sk) sn]
  | None => []
  end.

Lemma shadow_factsB_eqf : forall fk, shadow_factsB (mkbc fk) = shadow_facts fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bh11nh22fkh35kindsh42msh51oh63offh71pi001ph81xi011xh92x0h:2x1i021ai032sbi042ski052snp;1p;2p;3p;6p;4p;5g00A2j12Tg01`>j10Tg04fbj1?j2Mj3Ej4HTg04gkj1;j2Fj3>j4ITg00bVR0j29Tg04`Pj1<j37Tg00fXj15Tg00Lej34Tg04[bj6:j1BTg00ojj2LTg01UOj2KTg01O7j2JTg04]1j68j1@Tg001kj31Tg00FUR1j1DTg00GYj2ATg04i3j1CTg00>Oj66Tg04_Jj1=Tg04jFj1GTg02DZj53Tg014BR2#2R3g015DR4#2R5g00]=R6P3^16R7]0f0R8#0#?%;8P6P7f1R7#0/M81F78P6P3f2R9#0?E78A>978g00^=R:,96R;/96^16^06R<f3R=#<P0P;P6P3P8P9P7O2P0P6P:P3P7P1P4P3f8R>#0f7R?g04XRR@g04kP%5@34RAP7P8P9E:1L97RB/K=1JB=%52RB542542R2PBn10110100021010200n2001100000120103104n2001101000120100105P0P;P6P3f4RC?797RDP0P6P:P3P7P1P4P3P>P?PAP7P8P9E8P2PBn10110100021010200n2001100000120103104n2001101000120100105R>513X7<%2@%D4^16^6:^06]3^45R@%@=P0P;P6P3PDP0P6P:P3P7P1P4P3PCP?PAP7P8P9O5P2PBn10110100021010200n2001100000120103104n2001101000120100105=13>X5@P0P;P6P3A7=78P0P6P:P3P7P1P4P3P?f6PAP7P8P9E8P2PBn10110100021010200n2001100000120103104n2001101000120100105,A3%0=RB#B%C=E6%=B%G=E6PBP9P7P8CHP=P9P7P8CI513eX:6D3X96D3X85D3W2o"). Qed.
#[local] Hint Rewrite shadow_factsB_eqf : bceq.



(* [comment removed for export] *)
Definition vis_cost (nhi : Z) : Z := nhi + nhi / 8 + 16384.

(* [comment removed for export] *)
Definition lin_brange_raw (kn : list kentry) (fs : list sfact) (c : Z) (ts : list (Z * expr)) : option (Z * Z) :=
  match sum_subst fs ts 0 0 false with
  | (ts', (lo0, hi0), true) =>
      match lin_range (erange kn) c ts' with Some (lo, hi) => Some ((lo + lo0)%Z, (hi + hi0)%Z) | None => None end
  | _ => None
  end.
Definition ivl_meet (a b : option (Z * Z)) : option (Z * Z) :=
  match a, b with
  | Some (l1, h1), Some (l2, h2) => Some (Z.max l1 l2, Z.min h1 h2)
  | Some i, None => Some i
  | None, x => x
  end.
Fixpoint meet_each (kn : list kentry) (c : Z) (ts : list (Z * expr)) (fs : list sfact) (acc : option (Z * Z)) : option (Z * Z) :=
  match fs with
  | [] => acc
  | f :: r => meet_each kn c ts r (ivl_meet acc (lin_brange_raw kn [f] c ts))
  end.
Definition lin_brange_each (kn : list kentry) (e : expr) : option (Z * Z) :=
  let l := lin_of e in
  let fs := sum_facts kn kn in
  match meet_each kn (fst l) (snd l) fs (lin_brange_raw kn fs (fst l) (snd l)) with
  | Some (lo, hi) => if (Z.leb 0 lo && Z.ltb hi two64)%bool then Some (lo, hi) else None
  | None => None
  end.
Definition xhi_each (k : list kentry) (e : expr) : option Z :=
  match xhi k e, lin_brange_each k e with
  | Some h1, Some (_, h2) => Some (Z.min h1 h2)
  | Some h1, None => Some h1
  | None, Some (_, h2) => Some h2
  | None, None => None
  end.
Definition xlo_each (k : list kentry) (e : expr) : option Z :=
  match xlo k e, lin_brange_each k e with
  | Some l1, Some (l2, _) => Some (Z.max l1 l2)
  | Some l1, None => Some l1
  | None, Some (l2, _) => Some l2
  | None, None => None
  end.
(* [comment removed for export] *)
Definition flat_xe (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match base_range k b, xlo_each k n, xhi_each k n with
  | Some (lo, hi), Some nl, Some nh =>
      (Z.leb 0 (lo + off) && Z.ltb (hi + off) two64 && Z.leb (hi + off + nh) two64 && Z.leb 0 nl)%bool
  | _, _, _ => false
  end.

(* [comment removed for export] *)
Definition slice_ok (k : list kentry) (bb : expr) (bk : Z) (b n : expr) (p : expr * expr) : bool :=
  (expr_eqb (eadd (fst p) (snd p)) e_band && Z.leb 12 (ealign k (fst p))
   && match xhi_each k (snd p) with Some h => Z.ltb h 4096 | None => false end
   && Z.leb 12 (ealign k b) && Z.leb 12 (ealign k n)
   && ranges_apart_x k bb bk n e_band 0 (ELit BANDLEN))%bool.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition shadow_apart_each (k : list kentry) (sb : expr) (sk : Z) (sn : expr) (pb : expr) (pk : Z) (pn : expr) : bool :=
  match xhi_each k pn with Some h => (Z.ltb h two64 && ranges_apart_x k sb sk sn pb pk (ELit h))%bool | None => false end.

(* [comment removed for export] *)
Definition sw_off_ok : bool := ((SW_LO <=? shadow_off A) && (shadow_off A + 2 ^ 44 <=? KHI))%bool.
(* [comment removed for export] *)
Definition shd_end_ok (k : list kentry) (b n : expr) : bool :=
  if match xhi k b, xhi k n with Some h, Some m => Z.leb (h + m) (2 ^ 47) | _, _ => false end then true
  else lin_ge0 k [(ELit (2 ^ 47), 0%Z)] [(b, 0%Z); (n, 0%Z)].
Definition shd_end_okB (bc : bctx) (b n : expr) : bool :=
  if match xhiB bc b, xhiB bc n with Some h, Some m => Z.leb (h + m) (2 ^ 47) | _, _ => false end then true
  else lin_ge0B bc [(ELit (2 ^ 47), 0%Z)] [(b, 0%Z); (n, 0%Z)].
Lemma shd_end_okB_eqf : forall fk, shd_end_okB (mkbc fk) = shd_end_ok fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bh11eh22fkh31nh43negh51oh63posh71xi001xh82x0i011hi021mp;1p;2p;3p;6p;5p;4g00A2j1RTg01`>j10Tg04lSj1Bj2Qj3=Tg04mZj1>j2Lj3MTg03hej1Cj37Tg03S\j25j1FTg01M_j2@Tg03Zkj1?Tg03[Pj19Tg040cj16Tg04n`j2;Tg01N<j2PTg00bVj2OTg00Pej1NTg00fXj1KTg00Lej31Tg03T\j23j1DTg001kj32Tg00FUR0j1ATg00GYj2ETg03UYj1GTg00>Oj68Tg03ifj1Hj3JTg03jjj1ITg02DZj5:Tg03l2j4<Tg00]=R1g00^=R2f0R3g02E\C<p=4g014B#RP1g00OER4^31%03#B%>3P1P4f1R5#0/Q31L53g03lRR6P4^46]6R6f2R7#CP4P4P0P2P4f3R8#0R9/57P0P2P4f4R:#0/571@53g03\K#?R;#9%6;#6#6#6#9';R;'PR<g00PER=n10110000021010200P=n10110000021010100g00OeR>P31O12R?%N;#4%K?R;31R@%47%45RA=1?;51?RBO2n0100000020000P4P4P0P2P41387P0P2P413:7P<P=n10110000021010200P=n10110000021010100P>A78@BRBn0100000020000R:524X06%A2^11R6%D7P4P4P0P2P4P3P7O1P0P2P4P5P7O1P<P=n10110000021010200P=n10110000021010100P>PBn0100000020000=24:X56P4P4P0P2P41375P0P2P41385P<P=n10110000021010200P=n10110000021010100P>%43=1?;91?ARA977@n0100000020000R?,E4%07R;#F%G7E8%H;%I7E8P4P4P0P2P415;5P0P2P41595P<P=n10110000021010200P=n10110000021010100P>AJ;@An0100000020000=24?eA=;53AM753524eX81D:X71D:W2o"). Qed.
#[local] Hint Rewrite shd_end_okB_eqf : bceq.

(* [comment removed for export] *)
Definition vis_add_ref (cs : acs) (b n : expr) (k : list kentry) : option (acs) :=
  let k0 := kn cs in
  let '(bb, bk) := split_lit b in
  let '(sb, sk, sn) := shadow_of k0 b n in
  match xhi k0 n with
  | Some nhi =>
  if (Z.leb 3 (ealign k0 b) && Z.leb 3 (ealign k0 n) && flat_x k0 bb bk n
      && expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n
      && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                           (flat_x k0 pb pk (snd p) || flat_xe k0 pb pk (snd p))   (* [comment removed for export] *)
                           && (ranges_apart_x k0 bb bk n pb pk (snd p) || slice_ok k0 bb bk b n p)   (* [comment removed for export] *)
                           && (ranges_apart_x k0 sb sk sn pb pk (snd p) || shadow_apart_each k0 sb sk sn pb pk (snd p))) (a_vis cs)   (* [comment removed for export] *)
      (* [comment removed for export] *)
      && shd_end_ok k0 b n && sw_off_ok
      && Z.leb (a_eager cs + a_abytes cs + vis_cost nhi) LIMIT)%bool
  then Some (ACS (mk_ss (pc cs) (s_regs (a_ss cs)) (shadow_facts k0 (a_maps cs) b n ++ k) (nxt cs))
                (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                ((b, n) :: a_vis cs) (a_ghost cs) (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs))
  else None
  | None => None
  end.
(* [comment removed for export] *)
Definition vis_add (cs : acs) (b n : expr) (k : list kentry) : option (acs) :=
  let k0 := kn cs in let bc := mkbc k0 in   (* [comment removed for export] *)
  let '(bb, bk) := split_lit b in
  let '(sb, sk, sn) := shadow_ofB bc b n in
  match xhiB bc n with
  | Some nhi =>
  if (Z.leb 3 (ealignB bc b) && Z.leb 3 (ealignB bc n) && flat_xB bc bb bk n
      && expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n
      && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                           (flat_xB bc pb pk (snd p) || flat_xe k0 pb pk (snd p))   (* [comment removed for export] *)
                           && (ranges_apart_xB bc bb bk n pb pk (snd p) || slice_ok k0 bb bk b n p)   (* [comment removed for export] *)
                           && (ranges_apart_xB bc sb sk sn pb pk (snd p) || shadow_apart_each k0 sb sk sn pb pk (snd p))) (a_vis cs)   (* [comment removed for export] *)
      && shd_end_okB bc b n && sw_off_ok   (* [comment removed for export] *)
      && Z.leb (a_eager cs + a_abytes cs + vis_cost nhi) LIMIT)%bool
  then Some (ACS (mk_ss (pc cs) (s_regs (a_ss cs)) (shadow_factsB bc (a_maps cs) b n ++ k) (nxt cs))
                (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                ((b, n) :: a_vis cs) (a_ghost cs) (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs))
  else None
  | None => None
  end.

Lemma vis_add_eq : forall cs b n k, vis_add cs b n k = vis_add_ref cs b n k.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bh11pi001ph21nh31eh42b1h52b2h62csh71kh82k1h92k2h:1lh;2msh<2n1h=2n2h>1oh?3offh@1zi012bbi022bki033nhii042pbi052pki062sbi072ski082sni091xp&0p;1p;2p;3p;4p;7p;6p;;g00A2j1YTg00i8j17Tg03ocj1pj2CTg00FUR0j1JTg01E@j1ETg00bVR1j2FTg01`>j15Tg04_Jj3aj1mTg03S\j2Uj1oTg040cj1gTg03[Pj1eTg01N<j23Tg03aCj4Aj1kTg04o=j1`Tg050<j2BTg000Nk302Tg00c6k301Tg051Dj4XTg00H3j21Tg02B@j7?j1vTg052Gj6TTg053Kj7QTg00k8j1RTg01>4j3:Tg04lSj3Nj1tTg054Xj1VTg055[j1]Tg01M_j29Tg056_j1fTg057cj1ITg00g8j1LTg00h8j1MTg00j6j1HTg04fbj4Oj1sTg058aj3>Tg01hLj4=Tg059>j1GTg05:Aj1STg03l2j4dTg00Lej3cTg00l9j1bTg00`Uj1_Tg00aVj1^Tg05;Bj1\Tg05<Fl;<Tg00G7j2;Tg00n=k103Tg04`Pj3[j1{Tg03T\j2Zj1zTg019Ij22Tg03bFj4Dk100Tg02@>j7@j1~Tg04mZj3Pj1xTg04gkj4Kj1}Tg001kj34Tg00GYj2uTg05=Gj1qTg00>Oj68Tg03UYj1nTg04jFj1rTg05>Rj1lTg02CKj1wTg05?_j1jTg041Hj1yj2WTg042Kj1iTg05@fj4|Tg05Aij4hTf2R2f1R3'2f0R4'2p=0g05C0,23/24p=6g016FR5g00]=R6g014BR7#YR8g00^=R9^36R:f3R;#7R<#p%J5R=P1P6P9P=%E;R>P11F69R?P6P=f6R@#7RA#5f5RBf4RC3aRDP1P6P9P=P3P0P9P=f:RE#7RF#5RGf8RH'URIg00OERJP=g03\K#g#eRKf7RLPEO1'3PLf9RMO1,3Kf;RN#7RO#5RPP@PBPMCA30%`NRQ/BERR1BQMRS301F66RTP1P6P9PJB02664#ERUf>#7RV#5RWP3P4B01662RXCAPVP3P4PXCXRY'1PWPMPHf<RZP3P4PXF?PVPMPHf=R[PZP2ETR\'1R]PWPBPCP@P3P4PXF?PVPBPCP@P3P4PXFQRW'1R^30n2001109000120104105X1T%RNR_3:ANPEMR`30%VNRa%]NRb'9%f4Rc'9p,5LIMITRd'3Re'6%INRf%LN#MRgPP%HNRPPEPMCO=>7HPQC=PP%GNRh%SNRiPaP6P6PEPMCd=cT_Rj%bNRk19bcRb%_NRl%^NRm%\NRnM;<,;5Ro&035Rpn0100000020000Ppn10110900021010300n2001100000121106107n2001109000121100108n2001109000121101102P1P6P9P=P>P1P?P6P=A[ABCRAP1P6P9P=P3P0P9P=1ZFHRqPJP=1COE,3K1COM,3K'2RrPOP@PBPMCD'2?0RSRsP1P6P9PJPUPVP3P4PXCD/1YRtPVPMPHPZP3P4PXF@/1\PVPBPCP@P3P4PXF@/1W30n2001109000120104105X1T=:T_'2RVAPOEM'2/6ePfPgPOPPPEPMCK=>7HPQC=PPPhPiPaPjPkPbPlPmPnM;<,;5ROPpn0100000020000Ppn10110900021010300n2001100000120106107n2001109000121100108n2001109000121101102Ru34X@:PJ^26R:^?9^06Rv&00<P1P6P9P=P>P1P?P6P=PDP1P6P9P=P3P0P9P=PIPJP=PLP@PBPMO3,2r?0RSP1P6P9PJPUPEP3P4PXO3/1Y?0]^n2001109000120104105X1T=:T_;0`/6ePoPpn0100000020000Ppn10110900021010300n2001100000121106107n2001109000121100108n2001109000121101102=4=uX0vPJ^=6^99^56^<6^89^46Rv%~<P1P6P9P=P>P1P?P6P=PDP1P6P9P=P3P0P9P=PIPJP=P1P6P9PJPUPEPMPHPZP3P4PXO6/1\PEPBPCP@P3P4PXO6/1W50tn2001109000120104105X1T=:T_=0s`/6ePoPpn0100000020000Ppn10110900021010300n2001100000120106107n2001109000121100108n2001109000121101102=4=uX0vg015D#YP8^26^06];R8%}<P1P6P9P=P>P1P?P6P=PDP1P6P9P=P3P0P9P=PIPJP=12V`/6eR`PfPgPLPPPEPMO3=>7HPQC=PPPhPiPaPjPkPbPlPmPnM;<,;5Ppn0100000020000Ppn10110900021010300n2001100000121106107n2001109000121100108n2001109000121101102=4=uX:81F?6^26^06R8%{<P1P6P9P=P>P1P?P6P=P2PBPCO2P1P6P9P=P3P0P9P=PIPJP=P`POPpn0100000020000R`Ppn10110900021010300n2001100000121106107n2001109000121100108n2001109000121101102=4=uX18%J9^36R8%z<P1P6P9P=P>P1P?P6P=PAP1P6P9P=P3P0P9P=P@PHO1P`Ppn10110900021010300n2001100000120106107n2001109000121100108n2001109000121101102=4=uX>8P:^06R:%x<P1P6P9P=P>P1P?P6P=PAP1P6P9P=P3P0P9P=PqPJP=PLPEPMO2,2V/6ePOPpn0100000020000Ppn10110900021010300n2001100000120106107n2001109000121100108n2001109000121101102=4=uX0:P1P6P9P=%E2R:P1P?P6P=%7BRu?[C;P1P6P9P=P3P0P9P=%7MRO/ZLPJP=1CFM,3K1CFH,3KPFP@PBPHCD30%`ERe/BMRV1BeHRq30P1P6P9PJPU%7[R[P3P4PXCDP[P3P4PXCXRA'1P[PMPHPNP3P4PXF@P[PMPHPZPNP2ETRZ'1P[PBPCP@P3P4PXF@P[PBPCP@P3P4PXFQR>'130n2001109000120104105X1T%RER85:TAPFMH30%VER`%]ERI'9/9c/3dRd'6%IERn%LE#MRmPF%HERFPMPHCK=>7LPeC=PF%GERl%SERbP`P6P6PMPHCd=cT8Rk%bERj19IcRI%_ERc%^ERa%\EREM;<,;5Ppn0100000020000Ppn10110900021010300n2001100000120106107n2001109000121100108n2001109000121101102Ri,u=%5<Rh#t%q<E8%oh%n<E8%mh%r<E8%sh%l<E8%vh%w<E8%kh%j<E8%yh%i<E8P1P6P9P=P:P1P?P6P=%5u?aC;P1P6P9P=P3P0P9P=%5O/ULPJP=1WGM,3K1WGH,3KPGP@PBPHCA30?0VqP1P6P9PJPU%5[R[P3P4PXCA/1AP[PMPHPNP3P4PXF?/1ZP[PBPCP@P3P4PXF?/1>30n2001109000120104105X1T=:T8ANGMH30/6dPnPmPGPFPMPHCO=>7LPeC=PFPlPbP`PkPjPIPcPaPEM;<,;5Ppn0100000020000Ppn10110900021110300n2001100000121106107n2001109000121100108n2001109000121101102=4=ieP;P2P3P4C|P;P2P3P4Ch54=eW7X26W0W6o"). Qed.


(* [comment removed for export] *)
Definition is_map_entry (ms : list amap) (p : expr * expr) : bool :=
  existsb (fun m => negb (is_fog m) && expr_eqb (am_base m) (fst p) && expr_eqb (am_len m) (snd p)) ms.
(* [comment removed for export] *)
Definition inside_tracked (k : list kentry) (ms : list amap) (p : expr * expr) : bool :=
  let '(pb, pk) := split_lit (fst p) in
  existsb (fun m => negb (is_fog m) && xinside k pb pk (snd p) (am_base m) 0 (am_len m)) ms.
(* [comment removed for export] *)
Fixpoint find_kwr_at (k : list kentry) (e : expr) : option (expr * Z * expr) :=
  match k with
  | [] => None
  | KWr (SA b2 o2) n2 :: rest => if expr_eqb e (eaddz b2 o2) then Some (b2, o2, n2) else find_kwr_at rest e
  | _ :: rest => find_kwr_at rest e
  end.
(* [comment removed for export] *)
Definition kwr_join_first (k0 sf : list kentry) : list kentry :=
  match sf with
  | KWr (SA b1 o1) n1 :: _ =>
      match find_kwr_at k0 (eaddz (eadd b1 n1) o1) with
      | Some (b2, o2, n2) => if flat_x k0 b1 o1 (eadd n1 n2) then [KWr (SA b1 o1) (eadd n1 n2)] else []
      | None => []
      end
  | _ => []
  end.

(* [comment removed for export] *)
Fixpoint find_kzero_at (k : list kentry) (e : expr) : option (expr * Z * expr) :=
  match k with
  | [] => None
  | KZero (SA b2 o2) n2 :: rest => if expr_eqb e (eaddz b2 o2) then Some (b2, o2, n2) else find_kzero_at rest e
  | _ :: rest => find_kzero_at rest e
  end.
Definition kzero_join_second (k0 sf : list kentry) : list kentry :=
  match sf with
  | _ :: KZero (SA b1 o1) n1 :: _ =>
      match find_kzero_at k0 (eaddz (eadd b1 n1) o1) with
      | Some (b2, o2, n2) => if flat_x k0 b1 o1 (eadd n1 n2) then [KZero (SA b1 o1) (eadd n1 n2)] else []
      | None => []
      end
  | _ => []
  end.

(* [comment removed for export] *)
Definition slice_srl3 (k : list kentry) (n : expr) : expr :=
  let l := lin_of n in
  if (coeffs_div 8 (snd l) && match lin_brange_each k n with Some _ => true | None => false end)%bool
  then unlin ((fst l / 8)%Z, ldiv_terms 8 (snd l))
  else mkSrl k n 3.
(* [comment removed for export] *)
Definition shadow_facts_at (k : list kentry) (ms : list amap) (sb : expr) (sk : Z) (sn : expr) : list kentry :=
  match find_containing_sh k ms [KRWLAZY] sb sk sn with
  | Some _ => [KWr (SA sb sk) sn; KZero (SA sb sk) sn]
  | None => []
  end.

(* [comment removed for export] *)
Definition vis_slice (cs : acs) (b n : expr) : option acs :=
  let k0 := kn cs in
  let '(bb, bk) := split_lit b in
  let '(sb, sk, _) := shadow_of k0 b n in
  let sn := slice_srl3 k0 n in
  match xhi_each k0 n with   (* [comment removed for export] *)
  | Some nhi =>
  let snl := ELit ((nhi + 7) / 8) in
  if (Z.leb 12 (ealign k0 b) && Z.leb 3 (ealign k0 n) && Z.ltb nhi 4096 && expr_eqb (eadd b n) e_band
      && flat_x k0 bb bk (eaddz n 8)   (* [comment removed for export] *)
      && expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n
      && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                           flat_x k0 pb pk (snd p) && ranges_apart_x k0 sb sk snl pb pk (snd p)
                           && (ranges_apart_x k0 bb bk n pb pk (snd p) || is_map_entry (a_maps cs) p
                               || inside_tracked k0 (a_maps cs) p)) (a_vis cs)   (* [comment removed for export] *)
      && sw_off_ok && Z.leb (a_eager cs + a_abytes cs + vis_cost nhi) LIMIT)%bool   (* [comment removed for export] *)
  then let sf := shadow_facts_at (kn cs) (a_maps cs) sb sk sn in
       Some (ACS (mk_ss (pc cs) (s_regs (a_ss cs)) (kwr_join_first k0 sf ++ kzero_join_second k0 sf ++ sf ++ kimg_clip k0) (nxt cs))
                (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                ((b, n) :: a_vis cs) (a_ghost cs) (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs))
  else None
  | None => None
  end.

(* [comment removed for export] *)
Definition kwr_in (k : list kentry) (b : expr) (o : Z) (n : expr) : bool :=
  existsb (fun K => match K with KWr (SA b' o') n' => expr_eqb b' b && Z.eqb o' o && expr_eqb n' n | _ => false end) k.
Definition node_kwrjoin (cs : acs) (b1 : expr) (o1 : Z) (n1 : expr) (b2 : expr) (o2 : Z) (n2 : expr) : option acs :=
  let k := kn cs in
  if (kwr_in k b1 o1 n1 && kwr_in k b2 o2 n2 && expr_eqb (eaddz (eadd b1 n1) o1) (eaddz b2 o2)
      && flat_x k b1 o1 (eadd n1 n2))%bool
  then Some (add_kn cs [KWr (SA b1 o1) (eadd n1 n2)])
  else None.

(* [comment removed for export] *)
Fixpoint find_disj (k : list kentry) (b1 b2 : expr) : option (expr * Z * expr * expr * Z * expr) :=
  match k with
  | [] => None
  | KDisj (SA c1 o1) n1 (SA c2 o2) n2 :: r =>
      if (expr_eqb c1 b1 && expr_eqb c2 b2)%bool then Some (c1, o1, n1, c2, o2, n2)
      else if (expr_eqb c1 b2 && expr_eqb c2 b1)%bool then Some (c2, o2, n2, c1, o1, n1)
      else find_disj r b1 b2
  | _ :: r => find_disj r b1 b2
  end.
(* [comment removed for export] *)
Definition disj_side_fact (k : list kentry) (cA : expr) (oA : Z) (nA : expr) (cB : expr) (oB : Z) : option kentry :=
  match xlo2 k nA, base_range k cB with
  | Some n, Some (_, bhi) => if (Z.leb 0 n && Z.leb n (bhi + oB))%bool then Some (KRange (esub (eaddz cB oB) (eaddz cA oA)) n (bhi + oB)) else None
  | _, _ => None
  end.
(* [comment removed for export] *)
Definition elit_of (e : expr) : option Z := match e with ELit a => Some a | _ => None end.
Definition mul_var (e : expr) : option (Z * nat) := match e with EMd M_MUL (ELit c) (EVar v) => Some (c, v) | _ => None end.
Definition direct_fact (k : list kentry) (cA : expr) (oA : Z) (nA : expr) (cB : expr) (oB : Z) : list kentry :=
  match xlo2 k nA with
  | Some nlo =>
      match elit_of cA, mul_var cB, elit_of cB, mul_var cA with
      | Some a, Some (c, v), _, _ =>
          match xhi k (EVar v) with
          | Some h => if (Z.ltb 0 c && Z.leb 0 a && Z.ltb a two64 && Z.ltb (c * h) two64)%bool
                      then [KRange (EVar v) ((a + oA + nlo - oB + c - 1) / c) h] else []
          | None => []
          end
      | _, _, Some b, Some (c, v) =>
          match xlo k (EVar v), xhi k (EVar v) with
          | Some l, Some h => if (Z.ltb 0 c && Z.leb 0 b && Z.ltb b two64 && Z.ltb (c * h) two64)%bool
                              then [KRange (EVar v) l ((b + oB - oA - nlo) / c)] else []
          | _, _ => []
          end
      | _, _, _, _ => []
      end
  | None => []
  end.
(* [comment removed for export] *)
Definition casedisj_facts (d : list kentry) (K : kentry) : list kentry :=
  match d with [] => [K] | _ => d end.
Definition node_casedisj (cs : acs) (b1 b2 : expr) : option (acs * acs) :=
  let k := kn cs in
  match find_disj k b1 b2 with
  | Some (c1, o1, n1, c2, o2, n2) =>
      match flat_x k c1 o1 n1, flat_x k c2 o2 n2, disj_side_fact k c1 o1 n1 c2 o2, disj_side_fact k c2 o2 n2 c1 o1 with
      | true, true, Some K1, Some K2 => Some (add_kn cs (casedisj_facts (direct_fact k c1 o1 n1 c2 o2) K1),
                                              add_kn cs (casedisj_facts (direct_fact k c2 o2 n2 c1 o1) K2))
      | _, _, _, _ => None
      end
  | None => None
  end.

(* [comment removed for export] *)
Definition node_shdisj_ref (cs : acs) (b1 n1 b2 n2 : expr) : option acs :=
  let k := kn cs in
  let '(c1, o1) := split_lit b1 in let '(c2, o2) := split_lit b2 in
  let '(sb1, sk1, sn1) := shadow_of k b1 n1 in let '(sb2, sk2, sn2) := shadow_of k b2 n2 in
  if (Z.leb 3 (ealign k b1) && Z.leb 3 (ealign k n1) && Z.leb 3 (ealign k b2) && Z.leb 3 (ealign k n2)
      && flat_x k c1 o1 n1 && flat_x k c2 o2 n2 && flat_x k sb1 sk1 sn1 && flat_x k sb2 sk2 sn2
      && shd_end_ok k b1 n1 && shd_end_ok k b2 n2
      && ranges_apart_x k c1 o1 n1 c2 o2 n2)%bool
  then Some (add_kn cs [KDisj (SA sb1 sk1) sn1 (SA sb2 sk2) sn2])
  else None.
(* [comment removed for export] *)
Definition node_shdisj (cs : acs) (b1 n1 b2 n2 : expr) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  let '(c1, o1) := split_lit b1 in let '(c2, o2) := split_lit b2 in
  let '(sb1, sk1, sn1) := shadow_ofB bc b1 n1 in let '(sb2, sk2, sn2) := shadow_ofB bc b2 n2 in
  if (Z.leb 3 (ealignB bc b1) && Z.leb 3 (ealignB bc n1) && Z.leb 3 (ealignB bc b2) && Z.leb 3 (ealignB bc n2)
      && flat_xB bc c1 o1 n1 && flat_xB bc c2 o2 n2 && flat_xB bc sb1 sk1 sn1 && flat_xB bc sb2 sk2 sn2
      && shd_end_okB bc b1 n1 && shd_end_okB bc b2 n2
      && ranges_apart_xB bc c1 o1 n1 c2 o2 n2)%bool
  then Some (add_kn cs [KDisj (SA sb1 sk1) sn1 (SA sb2 sk2) sn2])
  else None.

Lemma node_shdisj_eq : forall cs b1 n1 b2 n2, node_shdisj cs b1 n1 b2 n2 = node_shdisj_ref cs b1 n1 b2 n2.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bh12b1h22b2h31nh42n1h52n2h62csh71eh82k1h92k2h:3offh;1pi001ph<1zi012c1i022c2i032o1i042o2i053sb1i063sb2i073sk1i083sk2i093sn1i0:3sn2i0;1xp;1p;2p;3p;4p;7p;6p;5g00i8j18Tg03ocj1aj2BTg00FUj1PTg01E@j1ATg00bVR0j2GTg01`>j17Tg04_Jj3>j1TTg040cj1OTg03[Pj1MTg01N<j21Tg03aCj45j1]Tg04lSj3=j1RTg02B@j7Ej1_Tg00ojj2FTg01VQj4XTg00fXj1VTg00Lej3UTg05D5j2DTg00G7j2CTg00n=j1STg04`Pj3<j1NTg03bFj44j1KTg04mZj3;j1ITg019Ij20Tg02@>j7@j1JTg001kj36Tg00GYj2QTg05=Gj1HTg00>Oj6:Tg04jFj1`Tg02CKj1^Tg05?_j1\Tg041Hj1Zj2?Tg042Kj1YTg05E7j5[Tg05F>j5WTf2R1f1R2'0f0R3'0p=2f4R4f3R5'0/01/02/03p=31B23,11p=91123,01p=Lg016FR6g00]=R7g00^=R8^77R9%84R:#a%P6R;P0P7P8P;%A4R<P0P7P8P;P<P01G78R=P7P;f9R>#8R?#7f8R@f7RA3>RBP0P7P8P;P2P0P=P7P;f=RC#8RD#7f:RE;>>RFP0P7P8P;P2g00OERGP;g03\K#O#MRHf<RIf@RJO1'1PIf?RKO1,1HPIf>RLO1,1H32PIPCO1,1HfARM#8RN#7ROf;RPPEPKC5POP>P@PCC5POf5RQP4f6RRC5D3POP2P3P1C5A=OJKRSA=OLCRTPOPPPEPKP>P@PCFEROD3g014BRU1FQ4PR1F23P1CX%VU3URU,DM,C6RM%S6RVn0100000020000n2001100000120106108n200110;00012010010:n2001100000120105107n200110;000120100109n200110;000120102104n200110;000120101103P0P7P8P;P<P0P7P8P;P<P0P=P7P;A<?@AR?P0P7P8P;P2P0P=P7P;A<DE>RDP0P7P8P;P2PGP;A9HNJ1BNK7LHA9HNLA9HNC32RWPNPPPEPKC4PNP>P@PCC4PNPQP4PRC4PNP2P3P1C4D3RXA;NJK'0A;NLCPNPPPEPKP>P@PCF@RN32PMPVn0100000020000n2001100000120106108n200110;00012010010:n2001100000120105107n200110;000120100109n200110;000120102104n200110;000120101103RY36X<9PG^37R9^:8^07RZ%K:P0P7P8P;P<P0P7P8P;P<P0P=P7P;PBP0P7P8P;P2P0P=P7P;PFP0P7P8P;P2PGP;PIPPPEPKO3,0WPIP>P@PCO3PIPQP4PRO332PIP2P3P1O3PSPTPOD3PMPVn0100000020000n2001100000120106108n200110;00012010010:n2001100000120105107n200110;000120100109n200110;000120102104n200110;000120101103=6;YX0ZPG^57^98^27^47^88^17RZ%J:P0P7P8P;P<P0P7P8P;P<P0P=P7P;PBP0P7P8P;P2P0P=P7P;PFP0P7P8P;P2PGP;A2XSTRTPIPPPEPKP>P@PCO6'0PMPVn0100000020000n2001100000120106108n200110;00012010010:n2001100000120105107n200110;000120100109n200110;000120102104n200110;000120101103=6;YX0Z1G=7^37^07RZ%N:P0P7P8P;P<P0P7P8P;P<P0P=P7P;P4P@PAO2P0P7P8P;P2P0P=P7P;P@PEP>O2P0P7P8P;P2PGP;10TNPMPVn0100000020000n2001100000120106108n200110;00012010010:n2001100000120105107n200110;000120100109n200110;000120102104n200110;000120101103=6;YX;ZP9^07R9%I:P0P7P8P;P<P0P7P8P;P<P0P=P7P;P?P0P7P8P;P2P0P=P7P;PDP0P7P8P;P2PGP;PIPJPKO2,0XPIPLPCO2;2NPMPVn0100000020000n2001100000120106108n200110;00012010010:n2001100000120105107n200110;000120100109n200110;000120102104n200110;000120101103=6;YX09P0P7P8P;%A5R9P0P7P8P;P9P0P=P7P;%8@RY?<ARP0P7P8P;P2P0P=P7P;%8IRM?<>@P0P7P8P;P2PGP;%8JRN=9HKA9HNLA9HNC32A9HNIPNPPPEPLC4PNP>P@PIC4PNPQP4PRC4D3PNP2P3P1C4A;NKLA;NCIPNPPPEPLP>P@PIF@D31DJU,C6R6PVn0100000020000n2001100000120106108n200110;00012010010:n2001100000120105107n200110;000120100109n200110;000120102104n200110;000120101103RU,Q;%7:RJ#R%H:E:%TJ%`:E:%_J%^:E:%]J%\:E:%ZJ%Y:E:P0P7P8P;P9P0P7P8P;P9P0P=P7P;%7Y?>ARP0P7P8P;P2P0P=P7P;%7M?>>@P0P7P8P;P2PGP;%7NRN/?K,1H1?NL,1H1?NC,1H321?NI,1HPNPPPEPLC5PNP>P@PIC5PNPQP4PRC5D3PNP2P3P1C5A=NKLA=NCIPNPPPEPLP>P@PIFED3P6PVn0100000020000n2001100000120106108n200110;00012010010:n2001100000120105107n200110;000120100109n200110;000120102104n200110;000120101103=6;UeP4P5P1P2P3D[P4P5P1P2P3DW56;eX57X27X47W1W6o"). Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mmap_len_ref (cs : acs) : option (expr * Z * Z) :=
  match reg_lit cs 11 with
  | Some len => if Z.ltb 0 len then Some (ELit (page_up len), page_up len, page_up len) else None
  | None =>
      let le := reg cs 11 in let k := kn cs in
      match xlo k le, xhi k le with
      | Some lo, Some hi =>
          if (Z.ltb 0 lo && Z.leb 12 (ealign k le) && Z.leb hi (2 ^ 46))%bool then Some (le, lo, hi) else None
      | _, _ => None
      end
  end.
(* [comment removed for export] *)
Definition mmap_len (cs : acs) : option (expr * Z * Z) :=
  match reg_lit cs 11 with
  | Some len => if Z.ltb 0 len then Some (ELit (page_up len), page_up len, page_up len) else None
  | None =>
      let le := reg cs 11 in let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
      match xloB bc le, xhiB bc le with
      | Some lo, Some hi =>
          if (Z.ltb 0 lo && Z.leb 12 (ealignB bc le) && Z.leb hi (2 ^ 46))%bool then Some (le, lo, hi) else None
      | _, _ => None
      end
  end.

Lemma mmap_len_eq : forall cs, mmap_len cs = mmap_len_ref cs.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01eh11oh22csh31zi002hii013leni022loi031xp;1p;2p;4p;3p;6g00i8j18Tg03ocj1Xj2?Tg00bVj2CTg00FUR0j1@Tg003kj1>Tg05GIj2DTg02Acj2BTg05HLj1RTg00Pej1OTg03l2j47Tg00G7j2<Tg00n=j1WTg01`>j1=Tg01DAj25Tg03K?j2Gj1KTg03S\j2Fj1ITg040cj16Tg03Zkj14Tg03[Pj1;Tg01N<j22Tg019Ij20Tg04n`j2STg03MCj2Ej1MTg03T\j2Aj1NTg001kj33Tg00GYj2LTg03OAj1JTg00>Oj69Tg03UYj1PTg041Hj1Qj2TTg042Kj1HTg05IOj1UTg05JSj1VTf0R1#>#>p=1g00]=R2g00^=R3f1R4P1C7p=:g016FP3^02R5%81R6#X1C23R7/C3R8#@R9P0P3P9g01\Y#>#1#1#1#1#1R:,D4R;g00OER<P9g02E\R=/B1P7P3%R1R>#O/:>P>C7,<8%W8R>n0100000020000R?P0P3P9%84R@#=RA154:RB'GRCP0P3P9f2RD#8RE#=RF15D:RG'FP<P91B=4R=g03\KRH#6#4#4#;RIPDf3RD/5:RJO1'2'0%4HRH#;%6H#6#6#4#;'S,21RH'0P7P31:J4P1C7,<8RKP>n0100000020000P>n10110300021010000P>n10110300021010200n10110300021010100P0P3P9P;P?P0P3P91E@BP0P3P91AEGP<P9%8D/?J,2I,0=/0HPKP>n0100000020000RKP>n10110300021010000RJP>n10110300021010200n10110300021010100RD33X35%@3^02R2%N6P0P3P9P;P?P0P3P9PCP0P3P9P4PGO1PKP>n10110300021010000P>n10110300021010200n10110300021010100=39DX12P2%M6P0P3P9P;P?P0P3P9P1PBO1PJP>n10110300021010200n10110300021010100=39DX12P0P3P91D1:R2P?P0P3P9151:R:,E6P0P3P91A@BP<P91?EG,2I,0=/0HP7P31:G4P1C7,<8R8P>n0100000020000P>n10110300021010000P>n10110300021010200n10110300021010100R4,L9%=6R7#K%J6E9%I7%P6E9%Q7%H6E9P0P3P9P2P?P0P3P91G7:P0P3P91FABP<P91TFG,2I,0=/0HP8P>n0100000020000P>n10110300021010000P>n10110300021010200n10110300021010100=394e%U1%V1539eW2o"). Qed.


(* [comment removed for export] *)
Fixpoint inside_maps (k : list kentry) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  match ms with
  | [] => false
  | m :: rest => (negb (is_fog m) && xinside_sh k b off len (am_base m) 0 (am_len m)) || inside_maps k rest b off len   (* [comment removed for export] *)
  end.

Fixpoint inside_mapsB (bc : bctx) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  match ms with
  | [] => false
  | m :: rest => (negb (is_fog m) && xinside_shB bc b off len (am_base m) 0 (am_len m)) || inside_mapsB bc rest b off len
  end.

Lemma inside_mapsB_eqf : forall fk, inside_mapsB (mkbc fk) = inside_maps fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01bh13lenh23offh32msh42IHh52b1h62b2h72fkh82k1h92k2h:1mh;2n1h<2n2h=4restp;1p;2p;3p;4p;5p;7p;6p;8g00A2j1>Tg01`>j10Tg05K[j1Cj2Mj3Jj4Aj53Tg05Lcj1?j2Kj3Bj4@j51Tg001kj32Tg00fXj1LTg00GYj2=Tg04Toj1<Tg01NYj1;Tg00cSj18Tg00dVj17Tg04YUj7Ij1ETg019Ij24Tg00H3j26Tg04Z\j79j1DTg04^?j1FTg00>Oj6:Tg00Lej3GTg00`3j8HTg02DZj55Tg014B#>g015DR0#>R1g00]=R2g00^=R3g00OER4^12R5]2R6]0f0R7#0#C%?7P2P6f1R6#0/M71K67P3P5f2R5#0?J67AB567P2P4f3R8#0P5P6P7CAP8P5P6P7C@P0f8R9#0P8P5P6P7D3P9P8P5P6P7D1524^12^23^02X31f7%L0P5P6P7D1,=4X12X23X02f9R9#0P8P5P6P7D3P9P8P5P6P7D1524^12^23^02P4f:R9f4R:P5P6P7D1R;f6R<#<#;R=f;R>#0P8P5P6%8<R?g02E\R@%7<R<FI'4/67P>P8P5P6P?P@P<F9,4=P>f5R>P8P5P6D1RA'6RB524X04P4^<2^93^62^;2^83^52RC%D9P7P8P5P6P?P@P<O6,4=/6A=24BX0C%<>#;P9P5P6P7%8>P@%7>F9'4/6;,=4%09R;#E%F9E:P;P:P5P6P7D3P8P5P6P7O3E:P;AG0>:R>P5P6P7D3P9P>P5P6P7D1524eX12X23X02W4X=1X:0P8P5P6P7GHX12D5X23D5X02D5X31D5W7o"). Qed.
#[local] Hint Rewrite inside_mapsB_eqf : bceq.



(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sw_amaps : list (Z * Z) := [(SW_LO, 0x10000000); (0x8fff7000, 0x20000000000); (0x2008fff7000, 0xdfff0001000)].
Definition is_lit_map (b n : Z) (m : amap) : bool :=
  (negb (is_fog m) && expr_eqb (am_base m) (ELit b) && expr_eqb (am_len m) (ELit n))%bool.
Definition sw_tracked (ms : list amap) : bool := forallb (fun p => existsb (is_lit_map (fst p) (snd p)) ms) sw_amaps.

Definition safe_range (k : list kentry) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  ((match xhi k len, base_range k b with
    | Some lh, Some (lo, hi) =>
        (Z.leb (img_lo A) (lo + off) && Z.leb (hi + off + lh) (img_hi A))    (* [comment removed for export] *)
    | _, _ => false
    end) || xinside k b off len e_band 0 (ELit BANDLEN)                         (* [comment removed for export] *)
    || inside_maps k ms b off len
    || (xinside k b off len (ELit 0) SW_LO (ELit (KHI - SW_LO)) && sw_tracked ms))%bool.   (* [comment removed for export] *)

Definition safe_rangeB (bc : bctx) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  ((match xhiB bc len, base_rangeB bc b with
    | Some lh, Some (lo, hi) =>
        (Z.leb (img_lo A) (lo + off) && Z.leb (hi + off + lh) (img_hi A))    (* [comment removed for export] *)
    | _, _ => false
    end) || xinsideB bc b off len e_band 0 (ELit BANDLEN)                       (* [comment removed for export] *)
    || inside_mapsB bc ms b off len
    || (xinsideB bc b off len (ELit 0) SW_LO (ELit (KHI - SW_LO)) && sw_tracked ms))%bool.   (* [comment removed for export] *)

Lemma safe_rangeB_eqf : forall fk, safe_rangeB (mkbc fk) = safe_range fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bh11eh21oh32b1h42b2h52fkh62k1h72k2h83lenh92msh:2n1h;2n2h<3offh=1xi001xh>2x0h?2x1h@2x2i012hii022lhi032loi041pp;1p;2p;3p;4p;7p;5p;6g00A2j1ATg01`>j11Tg05Mjj1Jj2^j3Lj4Gj5XTg05O1j1Ej2Uj3Ij4Fj5YTg05Lcj1Dj5@Tg03S\j2Cj1RTg00bVR0j2BTg03cHj2]j1PTg03_?j1VTg01M_j24Tg01N<j28Tg03`Aj1TTg019Ij22Tg00Pej1:Tg03L?j7>j1\Tg00H3j20Tg02AFj2HTg05P7j1=Tg03T\j2;j1MTg03dOj2<j1NTg03N@j76j1KTg001kj35Tg00FUR1j1?Tg00GYj2OTg03eSj1QTg00>Oj67Tg03UYj1STg03PEj1[Tg05K[j1ZTg05Q=j1WTg02DZj59Tf2R2f1R3'0f0R4'0p=3g014B#Ag015D#AR5g00]=R6g00^=R7g00OER8^86R9]<R:]0R;%14#J%E4P6P:%13/^41U34P7P9%12?L34AI234P6P8f3R9#1P2P3P4CGP9P2P3P4CFP;^95R;f4R:#DP1P7P8f5R<#1R=/C3P11B77R>P8f6R?#1/]:P0P7P7P8P4p,1AR@#VRA143?'8144?/49%T@R@'8'2n2001104000120103101RBg00PERCn10110000021010400RDPCn10110000021010200REP=P9P2P3g05RIRFg02E\RGg05SK#:RHF>'0P4P:P9P2P3O4P=P9P2P3%:GR=g05TNRIg05UO/HI#:RJF>%=:RK'233P1P7P81;<3RLP1P>P81<?:PBPCn10110000021010400PCn10110000021010200P<P9P2P3PFPGPHF6R?'0P<P:P9P2P3D@RMP<P9P2P3P=PIPJF6/2KRN33RO558X0;P8^;6^77^46^:6^67^36R;%K:P4P9P2P3PFPGPHO6,0EP4P9P2P3P=PIPJO6/2K73M=58OX0;%?7^16R;%M:P1P7P8P4P3O1PDPCn10110000021010200/0??3MN=58OX2;%?>^16R;%N:P1P7P8PLP1P>P8P3P:O1PBPCn10110000021010400PCn10110000021010200/0??3MN=58OX2;P1P7P81;:4P1P>P81<<9P0P7P7P8P4143<,8A144</49/8@'2n2001104000120103101PCn10110000021010400PCn10110000021010200P:P2P3P4PFPGPHF6'0P:P9P2P3P4D@P:P2P3P4P=PIPJF6%=9'233,O8%1:RJ#P%Q:E7%RJ%S:E7%\J%[:E7%ZJ%W:E7PJP9P2P3P4DXP:P9P2P3P4DY558eX@6D9X?7D9X>6D9X=5D9W5o"). Qed.
#[local] Hint Rewrite safe_rangeB_eqf : bceq.



Definition grant_keep_b (k : list kentry) (ms : list amap) (K : kentry) : bool :=
  match K with
  | KWord (SA b o) w _ => Nat.leb w 8 && safe_range k ms b o (ELit (Z.of_nat w))
  | KZero (SA b o) l => safe_range k ms b o l
  | KBlob (SA b o) l _ => safe_range k ms b o l
  | KImg lo hi => true
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA b o) n => safe_range k ms b o n
  | KFill (SA b o) l _ => safe_range k ms b o l
  | KUnk (SA b o) l => safe_range k ms b o l
  end.

Definition grant_keep_bB (bc : bctx) (ms : list amap) (K : kentry) : bool :=
  match K with
  | KWord (SA b o) w _ => Nat.leb w 8 && safe_rangeB bc ms b o (ELit (Z.of_nat w))
  | KZero (SA b o) l => safe_rangeB bc ms b o l
  | KBlob (SA b o) l _ => safe_rangeB bc ms b o l
  | KImg lo hi => true
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA b o) n => safe_rangeB bc ms b o n
  | KFill (SA b o) l _ => safe_rangeB bc ms b o l
  | KUnk (SA b o) l => safe_rangeB bc ms b o l
  end.

Lemma grant_keep_bB_eqf : forall fk, grant_keep_bB (mkbc fk) = grant_keep_b fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bi001bh11Ki011Kh22fkh33lenh42msh53offh61xh72x0i021ai032a1i042a2i051ci061ei072hii081ki092k0i0:1li0;2loi0<1mi0=1ni0>2n1i0?2n2i0@1oi0A1vi0B1wp;1p;2p;5p;3p;6g00A2j14Tg01`>j13Tg05VNj1;j2Dj3>Tg05WWj17j2Aj3?Tg05O1j1<j51Tg003kj10Tg01@Ej2:Tg01M?j19Tg00Pej18Tg019Ij22Tg001kj36Tg00GYj2CTg05Mjj1BTg05X_j1@Tg00>Oj6=Tg02DZj55Tg014BR0#4g015D#4R1g00OER2^10f0R3#3#;%73P0P2f1R4#3/D31A43g00]=R5g00^=P2^35]5]0^41R5f2R6#<P0P2P4g018HR7P2P6f3R8g01\Y#0#0#0#0#0#0#0#0':R9f5R:f7R;P4P3%98#8R<O4'2n0110200012010010@P7P2P4f4f6R=P4P3P6O4n0110200012010010@R>P7P2P6P:P;P4P3P8O4n0110200012010010@R?g00OeR@P@P@P>P@P?P>n01101000:3010210B10A2010210:3010210:1082010;1072010610<3010610;1072010210=4010310>10410?3010210:1052010210:P0P2P4P7P2P6f8R>P;P4P3P<D1,29n0110200012010010@P7P2P4P;P=P4P3P6D1n0110200012010010@R?P7P2P6P>P;P4P3P8D1n0110200012010010@R>P@P@P@P?P@P>P?n01101000:3010210B10A2010210:3010210:1092010;1072010610<3010610;1072010210=4010310>10410?3010210:1052010210:562X05P0P2P3P7P2P6P;P=P4P3P<D1,29n0110200012010010@P7P2P4P=P:P4P3P6D1n0110200012010010@R:P7P2P6P;P=P4P3P8D1n0110200012010010@R8P@P@P@P:P@P8P:n01101000:3010210B10A2010210:3010210:1092010;1072010610<3010610;1072010210=4010310>10410?3010210:1052010210:,C2%36R:#B%@6E=A>:43A?643562eX70D5X61D5W2o"). Qed.
#[local] Hint Rewrite grant_keep_bB_eqf : bceq.



Definition kn_grant_filter (k : list kentry) (ms : list amap) : list kentry :=
  kimg_clip (List.filter (grant_keep_b k ms) k).

Definition kn_grant_filterB (bc : bctx) (ms : list amap) : list kentry :=
  kimg_clip (List.filter (grant_keep_bB bc ms) (bc_fk bc)).

Lemma kn_grant_filterB_eqf : forall fk, kn_grant_filterB (mkbc fk) = kn_grant_filter fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01Kh11bh22fkh31lh42msh51xp;1p;3p;2p;6p;5g00A2j17Tg01`>j13Tg05Yjj1;j2>Tg05[6j1:j2<Tg05WWj1Aj24Tg02REj16Tg01GLj31Tg05\Aj10Tg001kj32Tg00GYj29Tg02THj18Tg00>Oj65Tg05VNj1@Tg05]Fj1?Tg02DZj5=Tg014BR0#7R1g015D#7R2P1f0R3#3#;%:3g00OE^00^42R4f1R5#AP3P5O1f2R6#3#6510#01465R7=106#0R6521X14P1P5A1073#0=216X311453=105#0,91%35R0#6%85E5%@0%?5E51>031<53521eX52D=W2o"). Qed.
#[local] Hint Rewrite kn_grant_filterB_eqf : bceq.
(* [comment removed for export] *)
Definition kn_grant_filterM (k : list kentry) (ms : list amap) : list kentry := kn_grant_filterB (mkbc k) ms.
Lemma kn_grant_filterM_eq : kn_grant_filterM = kn_grant_filter.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h02msh11kh21lp;1p;2p;3p;6p;5g00A2j12Tg05^SR0j1;j25Tg05[6R1j10j23Tg001kj34Tg00GYj2:Tg01`>j19Tg05Yjj18Tg05__j17Tg00>Oj66Tg02DZj51Tg014B#2R2g015D#2R3P2]0R4P0P1P3P2f0R1#;%01P4f1R0#0P1P0O1f2/30542X241301R4,:2%90#8%70E61501=424eX03D1X12D1o"). Qed.



(* [comment removed for export] *)
Definition gap_ok (cs : acs) (nhi : Z) : bool :=
  let cnt := Z.of_nat (n_res A + length (a_maps cs))%nat in
  Z.leb (FLOOR + nhi + a_totsz cs + cnt * (nhi + 4095)) CEIL.

Definition budget_ok (cs : acs) (extra : Z) : bool :=
  Z.leb (a_eager cs + a_abytes cs + extra) LIMIT.

(* [comment removed for export] *)
Definition kdisj_new (ms : list amap) (nb : expr) (ne : expr) : list kentry :=
  flat_map (fun m => if is_fog m then [] else
                     match am_base m with
                     | ELit _ => []
                     | mb => [KDisj (SA mb 0) (am_len m) (SA nb 0) ne]
                     end) ms.

(* [comment removed for export] *)
Definition with_maps0 (cs : acs) (ms : list amap) : acs :=
  ACS (a_ss cs) ms (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).

(* [comment removed for export] *)
Definition add_entry (cs : acs) (sr : list expr) (k' : list kentry) (nx' : nat)
           (m : amap) (nhi : Z) (eager : bool) (ylo' : Z) : acs :=
  ACS (mk_ss (pc cs + 4) sr k' nx')
      (m :: a_maps cs) (a_totsz cs + nhi) ylo'
      (if eager then a_eager cs + nhi else a_eager cs)
      (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition null_kend (base ne : expr) (nlo : Z) : list kentry :=
  match ne with
  | ELit _ => []
  | _ => [KRange (eadd base ne) (4096 * (KHI / 4096 + 1) + nlo) CEIL]
  end.

Definition mmap_null (cs : acs) (kind : mkind) (eager visible : bool) : option acs :=
  match mmap_len cs with
  | Some (ne, nlo, nhi) =>
      if (fresh_ok cs && expr_vars_lt (nxt cs) ne
          && gap_ok cs nhi && (negb eager || budget_ok cs nhi)
          && Z.leb (KHI + 2 * nhi) (a_ylo cs) && Z.leb (a_ylo cs) FLOOR
          && no_holes (a_maps cs))%bool then     (* [comment removed for export] *)
        let v := nxt cs in
        let base := escale 4096 (EVar v) in
        let kfacts := KRange (EVar v) (KHI / 4096 + 1) ((CEIL - nlo) / 4096) :: null_kend base ne nlo ++ kdisj_new (a_maps cs) base ne in
        let kmem := [KWr (SA base 0) ne; KZero (SA base 0) ne] in
        let k' := kfacts ++ kn_grant_filterM (kn cs) (a_maps cs) in
        let cs1 := add_entry cs (sr_upd (s_regs (a_ss cs)) 10 base) k' (S v) (AM base ne kind) nhi eager (a_ylo cs - 2 * nhi) in
        if visible then vis_add cs1 base ne (kmem ++ kn cs1) else Some cs1
      else None
  | None => None
  end.

(* [comment removed for export] *)

Definition entails (cs : acs) (ch : acs) : bool :=
  (Z.eqb (pc cs) (pc ch)
   && match s_log (a_ss ch) with [] => true | _ => false end
   && list_eqb expr_eqb (s_regs (a_ss cs)) (s_regs (a_ss ch))
   && forallb (fun K => existsb (kentry_eqb K) (kn cs)) (kn ch)
   && list_eqb amap_eqb (a_maps cs) (a_maps ch)
   && list_eqb pair_eqb (a_vis cs) (a_vis ch)
   && list_eqb pair_eqb (a_ghost cs) (a_ghost ch)
   && expr_eqb (a_brk cs) (a_brk ch)
   && afd_eqb (a_fd cs) (a_fd ch)
   && Bool.eqb (a_tidset cs) (a_tidset ch)
   && Z.leb (a_totsz cs) (a_totsz ch) && Z.leb (a_ylo ch) (a_ylo cs)
   && Z.leb (a_eager cs) (a_eager ch) && Z.leb (a_abytes cs) (a_abytes ch))%bool.

(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint cover_down (ms : list amap) (hi : Z) (fuel : nat) : Z :=
  match fuel with
  | O => hi
  | S f =>
      match List.find (fun m => negb (is_fog m) &&
                                match am_base m, am_len m with
                                | ELit b, ELit l => Z.eqb (b mod two64 + l mod two64) hi && Z.ltb 0 (l mod two64)
                                | _, _ => false
                                end) ms with
      | Some m => match am_base m with ELit b => cover_down ms (b mod two64) f | _ => hi end
      | None => hi
      end
  end.

(* [comment removed for export] *)
Definition null_kend2 (base ne : expr) (nlo : Z) : list kentry :=
  match ne with
  | ELit _ => []
  | _ => [KRange (eadd base ne) (4096 + nlo) ATOPMAX]
  end.

(* [comment removed for export] *)
Definition vis_add2 (cs : acs) (b n : expr) (k : list kentry) (wl wh : kentry) (lowok highok : bool) : option acs :=
  if (lowok && highok)%bool then
    match vis_add (add_kn cs [wl]) b n k, vis_add (add_kn cs [wh]) b n k with
    | Some c1, Some c2 => if entails c2 c1 then Some c1 else None
    | _, _ => None
    end
  else if (lowok || highok)%bool then vis_add cs b n k
  else None.

(* [comment removed for export] *)
Definition null2_loc (cs : acs) : Z := cover_down (a_maps cs) KHI (length (a_maps cs)).
Definition null2_lowok (cs : acs) (nlo : Z) : bool := Z.leb (4096 + nlo) (null2_loc cs).
Definition null2_highok (nlo : Z) : bool := Z.leb (KHI + nlo) ATOPMAX.
(* [comment removed for export] *)
Definition null2_wl (cs : acs) (ne : expr) (nlo : Z) : kentry :=
  KRange (EVar (nxt cs)) 1 ((null2_loc cs - nlo) / 4096).
Definition null2_wh (cs : acs) (nlo : Z) : kentry := KRange (EVar (nxt cs)) (KHI / 4096) ((ATOPMAX - nlo) / 4096).
Definition null2_kw (cs : acs) (ne : expr) (nlo : Z) : list kentry :=
  if null2_lowok cs nlo then (if null2_highok nlo then [] else [null2_wl cs ne nlo])
  else (if null2_highok nlo then [null2_wh cs nlo] else []).
(* [comment removed for export] *)
Definition null2_kfacts (cs : acs) (ne : expr) (nlo : Z) : list kentry :=
  let base := escale 4096 (EVar (nxt cs)) in
  null2_kw cs ne nlo ++
  KRange (EVar (nxt cs)) 1 ((ATOPMAX - nlo) / 4096) :: null_kend2 base ne nlo ++ kdisj_new (a_maps cs) base ne
  ++ [KDisj (SA (ELit (null2_loc cs)) 0) (ELit (KHI - null2_loc cs)) (SA base 0) ne;
      KDisj (SA (ELit (img_lo A)) 0) (ELit (img_hi A - img_lo A)) (SA base 0) ne;
      KDisj (SA e_band 0) (ELit BANDLEN) (SA base 0) ne].
Definition null2_cs1 (cs : acs) (kind : mkind) (eager : bool) (ne : expr) (nhi nlo : Z) : acs :=
  add_entry cs (sr_upd (s_regs (a_ss cs)) 10 (escale 4096 (EVar (nxt cs))))
    (null2_kfacts cs ne nlo ++ kn_grant_filter (kn cs) (a_maps cs)) (S (nxt cs))
    (AM (escale 4096 (EVar (nxt cs))) ne kind) nhi eager (a_ylo cs).
Definition null2_kmem (cs : acs) (ne : expr) : list kentry :=
  [KWr (SA (escale 4096 (EVar (nxt cs))) 0) ne; KZero (SA (escale 4096 (EVar (nxt cs))) 0) ne].
(* [comment removed for export] *)
Definition null2_cs1M (cs : acs) (kind : mkind) (eager : bool) (ne : expr) (nhi nlo : Z) : acs :=
  add_entry cs (sr_upd (s_regs (a_ss cs)) 10 (escale 4096 (EVar (nxt cs))))
    (null2_kfacts cs ne nlo ++ kn_grant_filterM (kn cs) (a_maps cs)) (S (nxt cs))
    (AM (escale 4096 (EVar (nxt cs))) ne kind) nhi eager (a_ylo cs).
Lemma null2_cs1M_eq : null2_cs1M = null2_cs1.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h05eagerh14kindh22neh33nhih43nloh52csh61kh71lh82msp;1p;2p;3p;4p;5p;8p;6g05`oR0j1Sj2Jj3Qj4Lj5Hj6MTg05b5R1j1Rj2Fj3Oj4Ij5Gj6NTg00A2j1=Tg00g8j16Tg00h8j1:Tg03[Pj1PTg04o=j1<Tg00Roj1>Tg05c:j2?Tg05d<j3;Tg05e<j3ATg00i8j1BTg00j6j19Tg058aj34Tg003kj13Tg05fDj38Tg05:Aj17Tg05gFj85Tg05[6R2j2CTg001kj3@Tg00GYj2KTg00>Oj6ETg02DZj50Tg03Zkj1DTf0R3#3#3p=2%D3#Dp=1g016FR4g04XRR5g00OER6g00]=R7g00^=R8P4^48R9]3R:]2R;]0R<]1P0P1P5P<%S3%R3P6P;f1R;/J31F;3P7P:f2R:?Q;3AO:;3P8P9f3R9P:P;P3CLP9P:P;P3CIP8P4f4R<P9P:P;P3DHP<P9P:P;P3DGg014BR1#=R0g015D#=P0]8]6R0P2f6R2%62#:g01\Y#2#2#2#2#2R=g03\K#1#1#1#1#1#1#PR>%<2R?#>'?R@3;RAAA29;RBP3%B2RC%92RDO2541%3?R?f5RE98@9R@P:P<%72RFG5P2PA1CCD941BP?P@P:P<PFG55@4X70PE%6E#:%<ER0#>,?>R>7;=AAE:3%BE%9E'C541%30A8>:<P;P9%7EG5,K4g05^Sg05hKEEPEP<P9P:P;P3EMPEP<P9P:P;P3EN5@4eX48D0X38D0X27D0X06D0X15D0X54D0o"). Qed.

Definition null2_ok (cs : acs) (eager : bool) (ne : expr) (nlo nhi : Z) : bool :=
  (fresh_ok cs && expr_vars_lt (nxt cs) ne
   && gap_ok cs nhi && (negb eager || budget_ok cs nhi)
   && Z.ltb (null2_loc cs) KHI && Z.leb (img_hi A) (null2_loc cs) && Z.leb 0 nlo && Z.leb (a_ylo cs) KHI
   && no_holes (a_maps cs))%bool.

Definition mmap_null2 (cs : acs) (kind : mkind) (eager visible : bool) : option acs :=
  match mmap_len cs with
  | Some (ne, nlo, nhi) =>
      (* [comment removed for export] *)
      if (null2_ok cs eager ne nlo nhi && (negb (mkind_lazy kind) || Z.ltb (img_lo A - 4096) nlo))%bool then
        if visible then vis_add2 (null2_cs1M cs kind eager ne nhi nlo) (escale 4096 (EVar (nxt cs))) ne
                                 (null2_kmem cs ne ++ kn (null2_cs1M cs kind eager ne nhi nlo))
                                 (null2_wl cs ne nlo) (null2_wh cs nlo) (null2_lowok cs nlo) (null2_highok nlo)
        else if (null2_lowok cs nlo || null2_highok nlo)%bool then Some (null2_cs1M cs kind eager ne nhi nlo) else None
      else None
  | None => None
  end.

(* [comment removed for export] *)
Definition fixed_args (cs : acs) (top : Z) : option (expr * Z * expr * Z * Z) :=
  let k := kn cs in let a := reg cs 10 in
  let '(b, off) := split_lit a in
  match mmap_len cs, xlo k a, xhi k a with
  | Some (ne, nlo, nhi), Some alo, Some ahi =>
      if (page_aligned k a && Z.ltb 0 alo && Z.leb (img_hi A) alo && Z.leb (ahi + nhi) top && flat_x k b off ne)%bool then Some (b, off, ne, nlo, nhi) else None
  | _, _, _ => None
  end.

(* [comment removed for export] *)
Definition fixed_args_in (cs : acs) (top : Z) : option (expr * Z * expr * Z * Z) :=
  let k := kn cs in let a := reg cs 10 in
  let '(b, off) := split_lit a in
  match mmap_len cs, xlo k a, xhi k a with
  | Some (ne, nlo, nhi), Some alo, Some ahi =>
      if (page_aligned k a && Z.ltb 0 alo && Z.leb (ahi + nhi) top && flat_x k b off ne)%bool then Some (b, off, ne, nlo, nhi) else None
  | _, _, _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition same_val (k : list kentry) (a b : expr) : bool :=
  if expr_eqb a b then true
  else (if lin_ge0 k [(a, 0%Z)] [(b, 0%Z)] then lin_ge0 k [(b, 0%Z)] [(a, 0%Z)] else false).
(* [comment removed for export] *)
Definition find_hole (k : list kentry) (ms : list amap) (a ne : expr) : option amap :=
  List.find (fun m => is_hole m && same_val k a (am_base m) && same_val k ne (am_len m)) ms.
(* [comment removed for export] *)
Definition unhole (ms : list amap) (h : amap) : list amap :=
  List.map (fun m => if (is_hole m && amap_eqb m h)%bool then AM (am_base m) (am_len m) KFOG else m) ms.

(* [comment removed for export] *)
Definition mmap_fixed_grant (cs : acs) (ms0 : list amap) (b : expr) (off : Z) (ne : expr) (nhi : Z)
           (kind : mkind) (eager visible : bool) : option acs :=
  let k := kn cs in
  let a := reg cs 10 in
  let m := AM a ne kind in
  let kmem := [KWr (SA b off) ne; KZero (SA b off) ne] in
  let ksh := if mkind_eqb kind KRWLAZY then flat_map (fun p => shadow_facts k [m] (fst p) (snd p)) (a_vis cs) else [] in
  let k' := ksh ++ kn_grant_filterM k ms0 in
  let cs1 := add_entry (with_maps0 cs ms0) (s_regs (a_ss cs)) k' (nxt cs) m nhi eager (a_ylo cs) in
  if visible then vis_add cs1 a ne (kmem ++ kn cs1) else Some cs1.

Definition mmap_fixed_free (cs : acs) (kind : mkind) (eager visible : bool) : option acs :=
  let k := kn cs in
  let a := reg cs 10 in
  match fixed_args cs KHI with
  | Some (b, off, ne, nlo, nhi) =>
      if (no_fog (a_maps cs)
          && forallb (fun m => ranges_apart_x k b off ne (am_base m) 0 (am_len m)) (a_maps cs)
          && (negb eager || budget_ok cs nhi)
          && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) a)%bool
      then mmap_fixed_grant cs (a_maps cs) b off ne nhi kind eager visible
      else None
  | None =>
      (* [comment removed for export] *)
      match fixed_args cs CEIL with
      | Some (b, off, ne, nlo, nhi) =>
          match find_hole k (a_maps cs) a ne with
          | Some h =>
              let ms0 := unhole (a_maps cs) h in
              if (forallb (fun m => negb (is_hole m) || ranges_apart_x k b off ne (am_base m) 0 (am_len m)) ms0
                  && (negb eager || budget_ok cs nhi)
                  && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) a)%bool
              then mmap_fixed_grant cs ms0 b off ne nhi kind eager visible
              else None
          | None => None
          end
      | None => None
      end
  end.

(* [comment removed for export] *)
Definition kn_rezero (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.filter (fun K => match K with
                        | KWord _ _ _ | KBlob _ _ _ | KFill _ _ _ => kentry_apart_bp k sp ub uk un K
                        | _ => true
                        end) k.

Definition kn_rezeroB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  List.filter (fun K => match K with
                        | KWord _ _ _ | KBlob _ _ _ | KFill _ _ _ => kentry_apart_bpB bc sp ub uk un K
                        | _ => true
                        end) (bc_fk bc).

Lemma kn_rezeroB_eqf : forall fk, kn_rezeroB (mkbc fk) = kn_rezero fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01Ki001Kh12ukh22unh31bh42b1h52fkh62k1h71lh82n1i012n1h91sh:2sph;2ubh<1xh=2x0h>2x1i021ai032a1i042a2i051ci061ei072hii081ki092k0i0:2loi0;1mi0<1ni0=2n2i0>1vi0?1wp;1p;2p;3p;4p;6p;5g00A2j1ITg01`>j10Tg05iZj1<j2Hj3=j4CTg05j`j18j2Fj3;j4DTg02HEj1:j65Tg02Q@j49j1?Tg02REj16Tg01GLj31Tg02SFj47j1GTg001kj32Tg00GYj2ETg02THj1>Tg00>Oj63Tg02UNj1@Tg02G9j1ATg02VWj1BTg02DZj54Tg014BR0#IR1g00]=R2g00^=R3P1^22R4]1f0R5#0#<%85P3P4f1R4#0/H51F45P2P1f2R6#0?=45A;645g02M2R7g00OER8^00^22^13^;2]:R9f3R:#:P0P8P5f4R;f8R<#0f7R=f6R>f5R?C9P=P>P?P:O5R@g00OeRAP@PAPAPAPAPAP@PAn01100000:3010210?10>2010210<3010210<1082010:1072010610;3010610:1072010210<4010310110410=3010210<1052010210<X00%0;#6R@510P0P8P5P<P<P=P>P?C7P=P>P?P:E5RBPAPBPAPAPAPAPAPBPAn01100000:3010210?10>2010210<3010210<1092010:1072010610;3010610:1072010210<4010310110410=3010210<1052010210<X00=10;RC521X39P7^82^63^42R7%G:P0P8P5P<P;P=P>P?O3P=P>P?P:E5R<PAP<PAPAPAPAPAP<PAn01100000:3010210?10>2010210<3010210<1082010:1072010610;3010610:1072010210<4010310110410=3010210<1052010210<X00=10@=21CX97P1P:P0P8P5PBPAPBPAPAPAPAPAPBPAn01100000:3010210?10>2010210<3010210<1082010:1072010610;3010610:1072010210<4010310110410=3010210<1052010210<X00=105=21CX71P0P8P5P=P=P>P?P;C7P>P?P;P:E5R;PAP;PAPAPAPAPAP;PAn01100000:3010210?10>2010210<3010210<1092010:1072010610;3010610:1072010210<4010310110410=3010210<1052010210<X00=10:,E1%0:R0#6%>:E3%?0%@:E3%A0%B:E3P0P6P4P5CCP:P6P4P5CD521eX>2D4X=3D4X<2D4W5o"). Qed.
#[local] Hint Rewrite kn_rezeroB_eqf : bceq.

Definition kn_rezeroM (k : list kentry) := kn_rezeroB (mkbc k).
Lemma kn_rezeroM_eq : kn_rezeroM = kn_rezero.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01kh12ubh22ukh32unp;1p;3p;5g00A2j15Tg05kej14Tg05loR0j10Tg05j`R1j11Tg001kj33Tg02DZj52Tg014B#5R2g00]=R3g00^=P2^33]2]1R3P0P1f0R1#4%01%11533eX02D2o"). Qed.



(* [comment removed for export] *)
Definition rekind (ms : list amap) (m : amap) : list amap :=
  map (fun m' => if amap_eqb m' m then AM (am_base m') (am_len m') KRW else m') ms.

(* [comment removed for export] *)
Inductive fixed_in_arm := ArmE | ArmF | ArmG.

(* [comment removed for export] *)
Definition fixed_in_args_ref (cs : acs) (arm : fixed_in_arm) : option (expr * Z * expr * Z * Z * amap) :=
  match fixed_args_in cs ATOPMAX with
  | Some (b, off, ne, nlo, nhi) =>
      let k := kn cs in
      let kinds := match arm with ArmE => [KRW; KNONE; KNONELAZY] | ArmF => [KRWLAZY] | ArmG => [KRW; KNONE; KNONELAZY] end in
      match find_containing k (a_maps cs) kinds b off ne with
      | Some m =>
          if (expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then Some (b, off, ne, nlo, nhi, m) else None
      | None => None
      end
  | None => None
  end.
(* [comment removed for export] *)
Definition fixed_in_args (cs : acs) (arm : fixed_in_arm) : option (expr * Z * expr * Z * Z * amap) :=
  match fixed_args_in cs ATOPMAX with
  | Some (b, off, ne, nlo, nhi) =>
      let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
      let kinds := match arm with ArmE => [KRW; KNONE; KNONELAZY] | ArmF => [KRWLAZY] | ArmG => [KRW; KNONE; KNONELAZY] end in
      match find_containingB bc (a_maps cs) kinds b off ne with
      | Some m =>
          if (expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then Some (b, off, ne, nlo, nhi, m) else None
      | None => None
      end
  | None => None
  end.

Lemma fixed_in_args_eq : forall cs arm, fixed_in_args cs arm = fixed_in_args_ref cs arm.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h03armi003armh11bi011bh22csh35kindsh42msh51nh61oh73offi023offi031mi042nei053nhii063nloi071pi082p0i092p1i0:2p2i0;1xp;1p;2p;3p;4p;6g00A2j1<Tg00FUR0j1@Tg00i8j16Tg04Sdj1Aj6>Tg00bVR1j22Tg05n5j2=Tg00j6j1;Tg00fXj1DTg00Lej33Tg04o=j18Tg050<j24Tg01DAj27Tg019Ij2?Tg03l2j40Tg00G7j2KTg00n=j1JTg001kj35Tg00GYj2ITg01`>j19Tg04RXj1Hj6FTg05o>j1CTg00>Oj6ETg060Nj2BTg061Wj2GTg003kj1:Tf0R2#:#:p=1g016Fg062dR3g015DR4#<g04XRR5#<R6g00]=R7g00^=R8%@4^57]7]1]3]4R9f1R:#6R;#A1278R</27R=/28R>/28R?/24R@#@RAP0P?PAf2RBg063nRC'=RDP1P>P8PAP2P1P=P8PAP:P1P<P7PAP:P1P7P8PAP:P0P4PAf9REf;RF#;RGP3P6f:RHg0651g0664g0677%D5RI535535535RJg04kP=35IRIPJn011000003000000R5P:P2PBO5g00OERKPAf<RL#8RMf3RN'4g01\Y#1#1#1#1#1RO,7L,4M'?P?P4P>P8P=P8P<P7P7P8PBP:C0PNC0f5C0f7C0P2C0,K@RM%J@R@n0100000020000RLP@n10110;00021010300n200110:000120101102n200110900012010:104n2001108000120109106n2001107000121108105P@n10110;00021110700P0P?PAPDP1P>P8PAP2P1P=P8PAP:P1P<P7PAP:P1P7P8PAP:P0P4PA%6FPGP5P:P2PBE>PLP@n10110;00021010300n200110:000120101102n200110900012010:104n2001108000120109106n2001107000121108105P@n10110;0002111070035X69P0P?PA1=:CRCP1P>P8PAP2P1P=P8PAP:P1P<P7PAP:P1P7P8PAP:P0P4PA%6HR9%;HRHP3P6PEPJPIPJn011000003000000RJP:P2PBE>PKPA%8FRK/4N17FO,4K'?PMP@n0100000020000RMP@n10110;00021010300n200110:000120101102n200110900012010:104n2001108000120109106n2001107000121108105P@n10110;00021110700RK,IA%9;#H%C;EEP0P?PAPCP1P>P8PAP2P1P=P8PAP:P1P<P7PAP:P1P7P8PAP:P0P4PA%99PHPJP:P2PBEFPMP@n10110;00021010300n200110:000120101102n200110900012010:104n2001108000120109106n2001107000121108105P@n10110;00021110700=5AKe1B:21G:255AeW0W2o"). Qed.


(* [comment removed for export] *)
Definition mmap_fixed_in_ref (cs : acs) (arm : fixed_in_arm) : option acs :=
  match fixed_in_args cs arm with
  | Some (b, off, ne, nlo, nhi, m) =>
      let k := kn cs in
      if match arm with ArmE => budget_ok cs nhi | _ => true end then
        let k' := match arm with
                  | ArmE => kimg_clip (kn_unfill k b off ne)
                  | ArmF => kimg_clip (kn_rezero k b off ne)
                  | ArmG => kimg_clip (kn_cutout k b off ne)
                  end in
        let ms' := match arm with ArmF => a_maps cs | _ => rekind (a_maps cs) m end in
        let ss := a_ss cs in
        let cs1 := ACS (mk_ss (pc cs + 4) (s_regs ss) k' (s_next ss))
                       ms' (a_totsz cs) (a_ylo cs)
                       (match arm with ArmE => a_eager cs + nhi | _ => a_eager cs end)
                       (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) in
        match arm with ArmE => vis_add cs1 (reg cs 10) ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1) | _ => Some cs1 end
      else None
  | None => None
  end.
(* [comment removed for export] *)
Definition mmap_fixed_in (cs : acs) (arm : fixed_in_arm) : option acs :=
  match fixed_in_args cs arm with
  | Some (b, off, ne, nlo, nhi, m) =>
      let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
      if match arm with ArmE => budget_ok cs nhi | _ => true end then
        let k' := match arm with
                  | ArmE => kimg_clip (kn_unfillB bc b off ne)
                  | ArmF => kimg_clip (kn_rezeroB bc b off ne)
                  | ArmG => kimg_clip (kn_cutoutB bc b off ne)
                  end in
        let ms' := match arm with ArmF => a_maps cs | _ => rekind (a_maps cs) m end in
        let ss := a_ss cs in
        let cs1 := ACS (mk_ss (pc cs + 4) (s_regs ss) k' (s_next ss))
                       ms' (a_totsz cs) (a_ylo cs)
                       (match arm with ArmE => a_eager cs + nhi | _ => a_eager cs end)
                       (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) in
        match arm with ArmE => vis_add cs1 (reg cs 10) ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1) | _ => Some cs1 end
      else None
  | None => None
  end.

Lemma mmap_fixed_in_eq : forall cs arm, mmap_fixed_in cs arm = mmap_fixed_in_ref cs arm.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01lh13armi003armh22csh32ubh42ukh52uni011bi021mi032nei043nhii053nloi063offi071pi082p0i092p1i0:2p2i0;2p3i0<1xp;1p;2p;4p;;p;3p;6g00A2j1QTg00i8j12Tg03;Qj1]j4NTg00FUR0j1[Tg00bVR1j28Tg060Nj2MTg068:j2KTg057cj1CTg03Zkj1ATg03[Pj1\Tg01M_j2:Tg00g8j1>Tg00h8j1=Tg01`>j1;Tg02N3j4Rj1hTg05\Aj10Tg05iZj4Pj1fTg01c>j1OTg01hLj43Tg00j6j1STg069?j2LTg059>j1JTg05:Aj1BTg054Xj1DTg00k8j1ETg00l9j1FTg055[j1GTg00`Uj1HTg00aVj1@Tg05;Bj1ITg05<Fl;4Tg01DAj2?Tg00ojj2ZTg01UOj2YTg01O7j2XTg05@fj45Tg00n=j1WTg02O9j4Vj1jTg05j`j4Uj1kTg001kj39Tg00GYj2iTg02Wgj1gTg00>Oj6<Tg05kej1eTg03:Kj1cj4aTg03=_j1bTg06:Aj2`Tg06;Jj2dTg003kj1TTg00Lej3_Tg00G7j2^Tf0R2#T#Tp=7g014BR3f1R4;_2p=1g016FR5/^2p=6g062dR6g00]=R7g00^=R8%Q3R3^57]4]3R9%24R:#]%[5R;P01878R</87R=/88R>/88R?g015DR@'8RAP;f2RB/M4RCP1P?P@P;P2P1P>P8P;P4P1P=P8P;P4P1P<P7P;P4P1P7P8P;P4g00OERDP;P6PDf<REf=RFf6RG'Kg00OeRHPHn011000003000000RIP6P;PE%CFg03\K#A#A#\RJ':RK%>FRL#=RMP6P3PE%2FRN#;ROP4P2PBCR#0RPPOP4P2PBCP#0f;ROP4P2PBO3#0RQn011000003000000%OLRLC3P6%Q@RRPE%SFRSf8RT'LRUPSPUn011000003000000RU%JFRS%BFRVP6P8PE%DFRW/:GPWPWn011000003000000RW%EFRX%FFRY%GFRZ%HFR[%@FR\%IFR]M;4R^g01\Y#7#7#7#7#7R_,?FRFPB1Z42R`/YBRa1X`BR`%2^'1'1C5%6^R^P^n011000003000000%W5R^n0100000020100n200110;000121101106n200110:00012110;103n200110900012110:105n2001108000121109104n2001107000121108102P^n10110<00021110700P0PAP;PCP1P?P@P;P2P1P>P8P;P4P1P=P8P;P4P1P<P7P;P4P1P7P8P;P4PDP;PIP6P;PEPKPMP6P3PEPNP4P2PBCV#0PNP4P2PBCU#0RbPNP4P2PBCN#0RNn011000003000000PLC3PUPSPVPWPXPYPZP[P\P]M;4RcPFPB%2c,1`,1aC5%6cRcPcn011000003000000P^n0100000020100n200110;000121101106n200110:00012110;103n200110900012110:105n2001108000121109104n2001107000121108102P^n10110<00021110700Rc39X09P9%k:P0PAP;PCP1P?P@P;P2P1P>P8P;P4P1P=P8P;P4P1P<P7P;P4P1P7P8P;P4PDP;PIP6P;PEPKPMP6P3PEPPPQPNn011000003000000PLC3PUPSPVPWPXPYPZP[P\P]M;4RPPFPB%2P,1`,1aC5%6PRPPPn011000003000000P^n0100000020100n200110;000121101106n200110:00012110;103n200110900012110:105n2001108000121109104n2001107000121108102P^n10110<00021110700=9;cX09P9%j:P0PAP;PCP1P?P@P;P2P1P>P8P;P4P1P=P8P;P4P1P<P7P;P4P1P7P8P;P4PDP;PIP6P;PEPKPMP6P3PEPQPbPNn011000003000000PLC3PUPSPVPWPXPYPZP[P\P]M;4R]PFPB%2],1`,1aC5%6]R]P]n011000003000000P^n0100000020100n200110;000121101106n200110:00012110;103n200110900012110:105n2001108000121109104n2001107000121108102P^n10110<00021110700=9;cX09P0PAP;1M42R9P1P?P@P;P2P1P>P8P;P4P1P=P8P;P4P1P<P7P;P4P1P7P8P;P4PDP;P6PDPO1KEGPHPHn011000003000000RHP6P;PO%CE/:JRJ%>ERc#=R]P6P3PO%2ERFP4P2PBCV#0PFP4P2PBCU#0PFP4P2PBCN#0n011000003000000%OcRcC3P6PRPO%SERR/LTRTPRPTn011000003000000RT%JERR%BER\P6P8PO%DER[/:GP[P[n011000003000000R[%EERG%FERZ%GERY%HERX%@ERW%IERVM;4RS1?E_R_PB%2S,1`,1aC5%6SRSPSn011000003000000P^n0100000020100n200110;000121101106n200110:00012110;103n200110900012110:105n2001108000121109104n2001107000121108102P^n10110<00021110700RS,i;%;:RE#h%g:E<%fE%e:E<%cE%b:E<P0PAP;P9P1P?P@P;P2P1P>P8P;P4P1P=P8P;P4P1P<P7P;P4P1P7P8P;P4PDP;PHP6P;POPJP]P6P3PO%;FRFP4P2PBCR#0PFP4P2PBCP#0PFP4P2PBCa#0n011000003000000PcC3PTPRP\P[PGPZPYPXPWPVM;4RVP_PB%2V,1`,1aC5%6VRVPVn011000003010000P^n0100000020100n200110;000121101106n200110:00012110;103n200110900012110:105n2001108000121109104n2001107000121108102P^n10110<00021110700=9;Se1`421d4259;eW1X25o"). Qed.


(* [comment removed for export] *)
Definition ENOMEM_RET : Z := two64 - 12.

(* [comment removed for export] *)
Definition refuse (cs : acs) : acs := set_pc (set_reg cs 10 (ELit ENOMEM_RET)) (pc cs + 4).

(* [comment removed for export] *)
Definition replace_entry (ms : list amap) (m : amap) (pieces : list amap) : list amap :=
  flat_map (fun m' => if amap_eqb m' m then pieces else [m']) ms.

(* [comment removed for export] *)
Definition dest_lfact (a mb : expr) (lne : bool) : kentry :=
  if lne then KRange (esub a mb) 1 (two64 - 1) else KRange (esub a mb) 0 0.
Definition dest_rfact (a ne mb ml : expr) (rne : bool) : kentry :=
  if rne then KRange (esub (eadd mb ml) (eadd a ne)) 1 (two64 - 1) else KRange (esub (eadd mb ml) (eadd a ne)) 0 0.

Definition mmap_destroyed_with_ref (hole : bool) (cs : acs) (b : expr) (off : Z) (ne : expr) (m : amap) (lne rne : bool) : acs :=
  let k := kn cs in
  let a := reg cs 10 in
  let mb := am_base m in let ml := am_len m in
  let lp := if lne then [AM mb (esub a mb) (am_kind m)] else [] in
  let rp := if rne then [AM (eadd a ne) (esub (eadd mb ml) (eadd a ne)) (am_kind m)] else [] in
  let hp := if hole then [AM a ne KHOLE] else [] in      (* [comment removed for export] *)
  let ss := a_ss cs in
  ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit ENOMEM_RET))
             (dest_lfact a mb lne :: dest_rfact a ne mb ml rne :: kimg_clip (kn_cutout k b off ne)) (s_next ss))
      (hp ++ replace_entry (a_maps cs) m (lp ++ rp)) (a_totsz cs) (a_ylo cs) (a_eager cs)
      (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).
(* [comment removed for export] *)
Definition mmap_destroyed_with (hole : bool) (cs : acs) (b : expr) (off : Z) (ne : expr) (m : amap) (lne rne : bool) : acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  let a := reg cs 10 in
  let mb := am_base m in let ml := am_len m in
  let lp := if lne then [AM mb (esub a mb) (am_kind m)] else [] in
  let rp := if rne then [AM (eadd a ne) (esub (eadd mb ml) (eadd a ne)) (am_kind m)] else [] in
  let hp := if hole then [AM a ne KHOLE] else [] in      (* [comment removed for export] *)
  let ss := a_ss cs in
  ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit ENOMEM_RET))
             (dest_lfact a mb lne :: dest_rfact a ne mb ml rne :: kimg_clip (kn_cutoutB bc b off ne)) (s_next ss))
      (hp ++ replace_entry (a_maps cs) m (lp ++ rp)) (a_totsz cs) (a_ylo cs) (a_eager cs)
      (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).

Lemma mmap_destroyed_with_eq : forall hole cs b off ne m lne rne, mmap_destroyed_with hole cs b off ne m lne rne = mmap_destroyed_with_ref hole cs b off ne m lne rne.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bh12csh24holei004holeh31lh43lnei013lneh51mh62neh73offh83rnei023rneh92ubh:2ukh;2unp;1p;2p;3p;5p;4p;;p;6p;8g00A2j1HTg00i8j1TTg03;Qj1Zj4VTg057cj1>Tg03Zkj1WTg03[Pj1\Tg01M_j2FTg00g8j1BTg00h8j1@Tg00Pej1XTg05d<j3<Tg01DAj2;Tg00cSj1CTg06<Wj3STg00dVj1KTg06=]j5ITg05\Aj15Tg01c>j1ETg01hLj47Tg05fDj32Tg00fXj1YTg00j6j1DTg06>cj26Tg04V1j1GTg04cZj28Tg058aj34Tg06?cj3?Tg059>j1JTg05:Aj1=Tg054Xj1LTg00k8j1MTg00l9j1NTg055[j1OTg00`Uj1PTg00aVj1QTg05;Bj1RTg05<Fl;9Tg001kj3:Tg00GYj2cTg01`>j1bTg03:Kj1aj4^Tg03=_j1`Tg00>Oj6_Tg06@lj8]Tg06B;j8[Tg003kj1UTg00Lej3ATf0R0#U#Up=3g014BR1f1R2;A0p=0g015DR3?A20p=1g00OER4g016FR5g00]=R6g00^=R7%H1^;6^:7^96R7f6R1#TR8#Zf7R9#>g03\K#W#W#\R:'FR;%B9R<#@g01\Y#3#3#3#3#3R=g06CN#XR>3<R?1;9=R@f3RA#CRBf2RC3SRDP@f4REPB%KARFP2DIRGP0P1f5RHPEO3#5'0'0%E<R<C7P4%H3RIf8g06DTRJ92@E%Y3RK'1PKn0110000020000%D9P4PIPC16@B%GARL52B/1KPKn0110100020000P4PIP218@ER@18BF/6@;2L/1KPKn01102000200005437?A543RL%J9R@%=9RF%L9RB%M9RM%N9RN%O9RO%P9RP%Q9RQ%R9RRM;9P;P?%T9P1PHPECV#5,0G,0DP<C7PLP@PFPBPMPNPOPPPQPRM;95:5X37%>1/F:R:%B1R7#@?<=>R>1;1=R=%CCRR;S2RQP=PAPR%KCRPP0DIROP8PHPEPACV#5'0'0%E7R7C7P4PIP9A2=AJ/1KPKn0110000020000%D1P4PIP216=R%GCRJ52R/1KPKn0110100020000P4PIP018=AR=18RP/6=;2J/1KPKn01102000200005437?C543RK%J1RJ%=1R=%L1RP%M1RR%N1RI%O1RN%P1RM%Q1RB%R1RFM;9R@,c5%b8RL#a%`8E_P:P>PLPHPEPAC^#5,0O,0QP7C7PKPJP=PPPRPIPNPMPBPFM;9=:5@eP9P1PHPEPAPCP2P0G]P9P1PHPEPAPCP2P0G[5:5eX84X44X53X66W7W0W1W2o"). Qed.


(* [comment removed for export] *)
Definition dest_cases (cs : acs) (ne : expr) (m : amap) : list (bool * bool) :=
  let k := kn cs in
  let a := reg cs 10 in
  let mb := am_base m in let ml := am_len m in
  let ls := if lin_ge0 k [(a, -1)] [(mb, 0)] then [true]                                   (* [comment removed for export] *)
            else if (expr_eqb a mb || lin_ge0 k [(mb, 0)] [(a, 0)])%bool then [false]    (* [comment removed for export] *)
            else [true; false] in
  let rs := if lin_ge0 k [(mb, -1); (ml, 0)] [(a, 0); (ne, 0)] then [true]                 (* [comment removed for export] *)
            else if lin_ge0 k [(a, 0); (ne, 0)] [(mb, 0); (ml, 0)] then [false]           (* [comment removed for export] *)
            else [true; false] in
  flat_map (fun l => map (fun r => (l, r)) rs) ls.

Definition mmap_destroyed (hole : bool) (cs : acs) (b : expr) (off : Z) (ne : expr) (m : amap) : list acs :=
  map (fun lr => mmap_destroyed_with hole cs b off ne m (fst lr) (snd lr)) (dest_cases cs ne m).

(* [comment removed for export] *)
Definition mmap_gate (cs : acs) : option (Z * Z * bool) :=
  match reg_lit cs 17, reg_lit cs 12, reg_lit cs 13, reg_lit cs 14, reg_lit cs 15 with
  | Some 222, Some prot, Some flags, Some m1, Some 0 =>
      if negb (Z.eqb m1 (two64 - 1)) then None
      else Some (prot, flags, match reg_lit cs 10 with Some 0 => true | _ => false end)
  | _, _, _, _, _ => None
  end.

(* [comment removed for export] *)
Definition node_mmap2 (cs : acs) : option (acs * acs) :=
  match mmap_gate cs with
  | Some (prot, flags, isnull) =>
      let g := if isnull then
                 match prot, flags with
                 | 3, 0x22 => mmap_null2 cs KRW true true               (* [comment removed for export] *)      (* [comment removed for export] *)
                 | 3, 0x4022 => mmap_null2 cs KRWLAZY false true        (* [comment removed for export] *)
                 | 0, 0x22 => mmap_null2 cs KNONE false false           (* [comment removed for export] *)
                 | 0, 0x4022 => mmap_null2 cs KNONELAZY false false     (* [comment removed for export] *)
                 | _, _ => None
                 end
               else
                 match prot, flags with
                 | 3, 0x4032 => mmap_fixed_free cs KRWLAZY false false  (* [comment removed for export] *)
                 | 3, 0x32 => mmap_fixed_free cs KRW true true          (* [comment removed for export] *)
                 | 0, 0x4032 => mmap_fixed_free cs KNONELAZY false false (* [comment removed for export] *)
                 | 0, 0x32 => mmap_fixed_free cs KNONE false false      (* [comment removed for export] *)
                 (* [comment removed for export] *)
                 | 3, 0x104022 => mmap_fixed_free cs KRWLAZY false false (* [comment removed for export] *)
                 | 0, 0x104022 => mmap_fixed_free cs KNONELAZY false false (* [comment removed for export] *)
                 | _, _ => None
                 end in
      match g with Some csG => Some (refuse cs, csG) | None => None end
  | None => None
  end.

(* [comment removed for export] *)
Definition node_mmapin (hole : bool) (cs : acs) : option (acs * acs * list acs) :=
  match mmap_gate cs with
  | Some (prot, flags, false) =>
      let arm := match prot, flags with
                 | 3, 0x32 => Some ArmE
                 | 3, 0x4032 => Some ArmF
                 | 0, 0x32 => Some ArmG
                 | _, _ => None
                 end in
      match arm with
      | Some arm =>
          match fixed_in_args cs arm, mmap_fixed_in cs arm with
          | Some (b, off, ne, nlo, nhi, m), Some csO => Some (refuse cs, csO, mmap_destroyed hole cs b off ne m)
          | _, _ => None
          end
      | None => None
      end
  | _ => None
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition node_mprotect_ref (cs : acs) : option acs :=
  match reg_lit cs 17, reg_lit cs 12, fixed_args_in cs ATOPMAX with
  | Some 226, Some 3, Some (b, off, ne, nlo, nhi) =>
      let k := kn cs in
      match find_containing k (a_maps cs) [KNONE; KNONELAZY] b off ne with
      | Some m =>
          if (budget_ok cs nhi && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then
            let k' := kimg_clip (kn_unfill k b off ne) in
            let ss := a_ss cs in
            let cs1 := ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) k' (s_next ss))
                           (rekind (a_maps cs) m) (a_totsz cs) (a_ylo cs) (a_eager cs + nhi)
                           (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) in
            vis_add cs1 (reg cs 10) ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1)
          else None
      | None => None
      end
  | _, _, _ => None
  end.
(* [comment removed for export] *)
Definition node_mprotect (cs : acs) : option acs :=
  match reg_lit cs 17, reg_lit cs 12, fixed_args_in cs ATOPMAX with
  | Some 226, Some 3, Some (b, off, ne, nlo, nhi) =>
      let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
      match find_containingB bc (a_maps cs) [KNONE; KNONELAZY] b off ne with
      | Some m =>
          if (budget_ok cs nhi && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then
            let k' := kimg_clip (kn_unfillB bc b off ne) in
            let ss := a_ss cs in
            let cs1 := ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) k' (s_next ss))
                           (rekind (a_maps cs) m) (a_totsz cs) (a_ylo cs) (a_eager cs + nhi)
                           (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) in
            vis_add cs1 (reg cs 10) ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1)
          else None
      | None => None
      end
  | _, _, _ => None
  end.
Lemma node_mprotect_eq : forall cs, node_mprotect cs = node_mprotect_ref cs.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bi001bh12csh25kindsh31lh42msh51nh61oh73offi013offh82ubh92ukh:2uni021mi032nei043nhii053nloi061pi072p0i082p1i093p10i0:3p11i0;3p12i0<2p2i0=2p3i0>2p4i0?2p5i0@2p6i0A2p7i0B2p8i0C2p9i0D1xi0E1zi0F2z0p;1p;2p;3p;4p;;p;6g00A2j1ATg00FUR0j1LTg00i8j11Tg04Sdj1\j6VTg003kj1>Tg05GIj2=Tg00n=j1^Tg00bVR1j2:Tg05n5j2FTg00j6j1?Tg00fXj1[Tg00Lej3@Tg068:j2YTg04o=j1WTg050<j2<Tg019Ij29Tg01DAj2QTg057cj1NTg03Zkj1UTg03[Pj1_Tg01M_j27Tg00g8j1JTg00h8j1ITg00Pej1]Tg05d<j3GTg01`>j1;Tg02N3j4Hj1fTg05\Aj16Tg01c>j1KTg01hLj44Tg069?j2ETg059>j1DTg05:Aj1MTg054Xj1CTg00k8j1OTg00l9j1PTg055[j1BTg00`Uj1RTg00aVj1STg05;Bj1ZTg05<Fl;5Tg00ojj2kTg01UOj2jTg01O7j2iTg05@fj43Tg02O9j4Xj1hTg001kj38Tg00GYj2gTg02Wgj1eTg00>Oj6TTg04RXj1bj6dTg05o>j1cTg06EWj1aTg06F`j1`Tf0R2#>#>p=2g014BR3f1R4;@2p=0g016FR5g015DR6#Ag04XRR7#Ag00]=R8g00^=R9%L6^58]7]0]2]4R:%12R;#\%L5R<P0P9P<g01\Y#2#2#2#2#2R=#2R>#>#2#2R?,=4R@P9P<P2%^5R5g005nRAP<P2P5PAP<P2PAP<P2P5PAP<P2P5PAP<P2P5PAP<P2PAP<P2PAP<P2P5P5P0P9P<f:/=>RBP9P<P2P5PAP<P2PAP<P2P5P5P01:89RC/:8RD/:9RE/:9RFP<f=g063nRG'FRHP1PEP9P<P2P1PDP9P<P4P1PCP8P<P4P1P8P9P<P4P0P6P<fERIfFRJ#?RKg0664g0677%[75@75@7R7P4P2f2RLO5g00OERMP<fGRNf7RO'Y%WNRPf3RQ'<'91QN=RR,<P'9RP%NNg03\K#U#U#_RS'7RT%JNRU#Ig02E\#]RV7G=RW%1NRX#;PLP4PQCH#6%KURUC4%?N/E2RY%DNRZ%MNR[%CN/7OR\%ONR]%PNR^%BNR_%RNR`%SNRa%ZNRNM;5RbPRPQ1kL4Rc/jQRd1icQRc%1b'0'0C3P5n0100000020000P5n10110D00021010200n200110;000121100101n200110:00012110;103n200110900012110:105n200110C000121109104P5n10110D00021110C00n0110B00031010C1010C01P5P5n0110A00031110B1010B00P5n0110F0003001110A1010AP5n10110D00021110F00n0110@00031010A1010A01P5P5n0110?00031110@1010@00P5P5n0110>00031110?1010?00P5n0110=00031010>1110>00P5n0110<00031010=1110=00P5n0110800031010<1110<00P5P5n011070003111081010800P5n011060003101071110700P5n0110E0003001110610106P5n10110D00021110E00P0P9P<P@P9P<P2P5PAP<P2P5PAP<P2PAP<P2P5PAP<P2P5PAP<P2P5PAP<P2PAP<P2PAP<P2P5P5P0P9P<PBP9P<P2P5PAP<P2PAP<P2P5P5P0PFP<PHP1PEP9P<P2P1PDP9P<P4P1PCP8P<P4P1P8P9P<P4P0P6P<%1JRbPKP7P4P2PLEVRePMP<PPPTPWPXPLP4PQCX#6PUC4PYPZP[P\P]P^P_P`PaPNM;5RXPRPQ%1X,0c,0dC3P5n0100000020000P5n10110D00021010200n200110;000121100101n200110:00012110;103n200110900012110:105n200110C000121109104P5n10110D00021110C00n0110B00031010C1010C01P5P5n0110A00031110B1010B00P5n0110F0003001110A1010AP5n10110D00021110F00n0110@00031010A1010A01P5P5n0110?00031110@1010@00P5P5n0110>00031110?1010?00P5n0110=00031010>1110>00P5n0110<00031010=1110=00P5n0110800031010<1110<00P5P5n011070003111081010800P5n011060003101071110700P5n0110E0003001110610106P5n10110D00021110E00RX38X6:%A3^:8^99^88R3%h;P0P9P<P@P9P<P2P5PAP<P2P5PAP<P2PAP<P2P5PAP<P2P5PAP<P2P5PAP<P2PAP<P2PAP<P2P5P5P0P9P<PBP9P<P2P5PAP<P2PAP<P2P5P5P0PFP<PHP1PEP9P<P2P1PDP9P<P4P1PCP8P<P4P1P8P9P<P4P0P6P<PePMP<PPPTPWPJPLP4PQO3#6PUC4PYPZP[P\P]P^P_P`PaPNM;5RNPRPQ%1N,0c,0dC3P5n0100000020000P5n10110D00021010200n200110;000121100101n200110:00012110;103n200110900012110:105n200110C000121109104P5n10110D00021110C00n0110B00031010C1010C01P5P5n0110A00031110B1010B00P5n0110F0003001110A1010AP5n10110D00021110F00n0110@00031010A1010A01P5P5n0110?00031110@1010@00P5P5n0110>00031110?1010?00P5n0110=00031010>1110>00P5n0110<00031010=1110=00P5n0110800031010<1110<00P5P5n011070003111081010800P5n011060003101071110700P5n0110E0003001110610106P5n10110D00021110E00=8<XX33P0P9P<1=2?R?P9P<P2P5PAP<P2P5PAP<P2PAP<P2P5PAP<P2P5PAP<P2P5PAP<P2PAP<P2PAP<P2P5P5P0P9P<f9/=>R>P9P<P2P5PAP<P2PAP<P2P5P5P0PFP<f</FGRGP1PEP9P<P2P1PDP9P<P4P1PCP8P<P4P1P8P9P<P4P0P6P<%1IR3%?IRIP7P4P2PLEVPMP<1YJO%WJRX/<Q'91QJ=RN,<X'9RX%NJ/7SRS%JJRR#I?G=VRVPbPLP4PQCX#6%KRRRC41EK2RK%DJR=%MJRa%CJ/7ORO%OJR`%PJR_%BJR^%RJR]%SJR\%ZJRJM;5R[PNPQ%1[,0c,0dC3P5n0100000020000P5n10110D00021010200n200110;000121100101n200110:00012110;103n200110900012110:105n200110C000121109104P5n10110D00021110C00n0110B00031010C1010C01P5P5n0110A00031110B1010B00P5n0110F0003001110A1010AP5n10110D00021110F00n0110@00031010A1010A01P5P5n0110?00031110@1010@00P5P5n0110>00031110?1010?00P5n0110=00031010>1110>00P5n0110<00031010=1110=00P5n0110800031010<1110<00P5P5n011070003111081010800P5n011060003101071110700P5n0110E0003001110610106P5n10110D00021110E00R[,g<%;;RZ#f%e;ET%bZ%c;ETP0P9P<P?P9P<P2P5PAP<P2P5PAP<P2PAP<P2P5PAP<P2P5PAP<P2P5PAP<P2PAP<P2PAP<P2P5P5P0P9P<P>P9P<P2P5PAP<P2PAP<P2P5P5P0PFP<PGP1PEP9P<P2P1PDP9P<P4P1PCP8P<P4P1P8P9P<P4P0P6P<%;3PIP7P4P2PLEdPMP<PXPSPV%;bPLP4PQCH#6PRC4PKP=PaPOP`P_P^P]P\PJM;5RJPNPQ%1J,0c,0dC3P5n0100000020000P5n10110D00021010200n200110;000121100101n200110:00012110;103n200110900012110:105n200110C000121109104P5n10110D00021110C00n0110B00031010C1010C01P5P5n0110A00031110B1010B00P5n0110F0003001110A1010AP5n10110D00021110F00n0110@00031010A1010A01P5P5n0110?00031110@1010@00P5P5n0110>00031110?1010?00P5n0110=00031010>1110>00P5n0110<00031010=1110=00P5n0110800031010<1110<00P5P5n011070003111081010800P5n011060003101071110700P5n0110E0003001110610106P5n10110D00021110E00=8<[e%a2%`258<eW1o"). Qed.


(* [comment removed for export] *)
Definition node_mprotect2 (cs : acs) : option (acs * acs) :=
  match node_mprotect cs with Some csG => Some (refuse cs, csG) | None => None end.

(* [comment removed for export] *)

Definition amap_match (k : list kentry) (b : expr) (n : expr) (m : amap) : bool :=
  (negb (is_fog m) && expr_eqb b (am_base m) && len_eqb k n (am_len m))%bool.

Definition amap_matchB (bc : bctx) (b : expr) (n : expr) (m : amap) : bool :=
  (negb (is_fog m) && expr_eqb b (am_base m) && len_eqbB bc n (am_len m))%bool.

Lemma amap_matchB_eqf : forall fk, amap_matchB (mkbc fk) = amap_match fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01mh11nh21bh32fkh41xh52x0h62x1p;1p;2p;3p;6p;4p;5g00A2j1GTg01`>j11Tg06Gmj1=j2Fj3>j4ATg06I4j1:j2Ej3<j4BTg03gbj1;j38Tg04Toj14Tg01NYj13Tg00cSj17Tg01L=j26Tg019Ij20Tg00dVj19Tg001kj35Tg00GYj2DTg03f^j1CTg06J:j1?Tg00>Oj6@Tg02DZj52Tg014B#Gg00]=R0g015DR1g00OER2]0R3^10f0R4#1#=%:4P0P3f1R3#1/F41E34P1P2f2R5#1?>34A<534P2^00^10R6f3R7#;%43#3%73,67'0R8P4P5%93R9O2'0f4?859,08552X26%44#3%74,65'0%949873'0,D2%17R6#C%?7E@P6P5P3P4CAP7P5P3P4CB552eX61D2X50D2X40D2W3o"). Qed.
#[local] Hint Rewrite amap_matchB_eqf : bceq.



(* [comment removed for export] *)
Definition node_munmap_ref (cs : acs) : option acs :=
  match reg_lit cs 17, mmap_len cs with
  | Some 215, Some (ne, nlo, nhi) =>
      let b := reg cs 10 in let k := kn cs in
      let '(bb, bk) := split_lit b in
      let gone := List.filter (fun p => let '(pb, pk) := split_lit (fst p) in negb (ranges_apart_x k pb pk (snd p) bb bk ne)) (a_vis cs) in
      let kept := List.filter (fun p => let '(pb, pk) := split_lit (fst p) in ranges_apart_x k pb pk (snd p) bb bk ne) (a_vis cs) in
      if (existsb (amap_match k b ne) (a_maps cs) && page_aligned k b && flat_x k bb bk ne
          && match xhi k b with Some hi => Z.ltb (hi + nhi) two64 | None => false end
          && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                               let '(sb, sk, sn) := shadow_of k (fst p) (snd p) in
                               Z.leb 3 (ealign k (fst p)) && Z.leb 3 (ealign k (snd p))
                               && xinside k pb pk (snd p) bb bk ne && kzero_x k k sb sk sn)
                     gone)%bool then
        let k1 := fold_left (fun kk p => let '(sb, sk, sn) := shadow_of k (fst p) (snd p) in kn_unfill kk sb sk sn) gone (kn_unfill k bb bk ne) in
        let ss := a_ss cs in
        Some (ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) k1 (s_next ss))
                 (List.filter (fun m => negb (amap_match k b ne m)) (a_maps cs))
                 (a_totsz cs) (a_ylo cs) (a_eager cs) kept (gone ++ a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | _, _ => None
  end.
(* [comment removed for export] *)
Definition node_munmap (cs : acs) : option acs :=
  match reg_lit cs 17, mmap_len cs with
  | Some 215, Some (ne, nlo, nhi) =>
      let b := reg cs 10 in let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
      let '(bb, bk) := split_lit b in
      let gone := List.filter (fun p => let '(pb, pk) := split_lit (fst p) in negb (ranges_apart_xB bc pb pk (snd p) bb bk ne)) (a_vis cs) in
      let kept := List.filter (fun p => let '(pb, pk) := split_lit (fst p) in ranges_apart_xB bc pb pk (snd p) bb bk ne) (a_vis cs) in
      if (existsb (amap_matchB bc b ne) (a_maps cs) && page_alignedB bc b && flat_xB bc bb bk ne
          && match xhiB bc b with Some hi => Z.ltb (hi + nhi) two64 | None => false end
          && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                               let '(sb, sk, sn) := shadow_ofB bc (fst p) (snd p) in
                               Z.leb 3 (ealignB bc (fst p)) && Z.leb 3 (ealignB bc (snd p))
                               && xinsideB bc pb pk (snd p) bb bk ne && kzero_xB bc k sb sk sn)
                     gone)%bool then
        let k1 := fold_left (fun kk p => let '(sb, sk, sn) := shadow_ofB bc (fst p) (snd p) in kn_unfillM kk sb sk sn) gone (kn_unfillB bc bb bk ne) in
        let ss := a_ss cs in
        Some (ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) k1 (s_next ss))
                 (List.filter (fun m => negb (amap_matchB bc b ne m)) (a_maps cs))
                 (a_totsz cs) (a_ylo cs) (a_eager cs) kept (gone ++ a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | _, _ => None
  end.

Lemma node_munmap_eq : forall cs, node_munmap cs = node_munmap_ref cs.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01pi001ph11bh22kkh31mh41eh51nh61kh71lh82b1h92b2h:2csh;2k1h<2k2h=2n1h>2n2h?1oh@3offhA2ubhB2ukhC2unhD1zi011zi022bbi032bki042hii052nei063nhii073nloi082p0i092p1i0:2p2i0;2p3i0<2p4i0=2p5i0>2p6i0?2p7i0@2p8i0A2pbi0B2pki0C2sbi0D2ski0E2sni0F1xp%0p&0p;1p;2p;3p;4p;7p;5p;;p;6g00i8j1;Tg06I4k10Nj3\j4WTg00FUR0j1UTg003kj1LTg05GIj2_Tg00n=k10KTg00bVR1j2CTg05IOj1RTg01DAj2>Tg01E@j1GTg00j6j1eTg008Ij3DTg01`>j1=Tg03mRj2mk105Tg03aCj4jj1xTg03S\j2]k100Tg01M_j2JTg02Ack20JTg04_Jj3Bj1}Tg040ck10FTg03[Pj1TTg041Hj2Aj1vTg01N<j28Tg019Ij21Tg03L?j7Pk102Tg03V]j5Qj1zTg02B@j7Vk104Tg01NYj19Tg00k8j1OTg01GLj32Tg01>4j3<Tg057cj1ZTg03Zkj1nTg00g8j1MTg00h8j1STg00Pej1pTg05d<j3oTg00A2k10MTg02Y1S00k40LTg02N3j4lk10;Tg01c>j1kTg059>j1iTg05:Aj1hTg054Xj1dTg00l9j1^Tg058aj3@Tg055[j1`Tg00`Uj1aTg00aVj1bTg05;Bj1cTg05<Fl;5Tg03n[j2[k10=Tg03bFj4fk10DTg03T\j2gk108Tg04`Pj3Fk109Tg03ocj2Ek10ETg03N@j7Yk107Tg03Waj5Xk10>Tg02@>j7Nk10<Tg02O9S01j4Hk10CTg001kj33Tg00GYk203Tg00>Oj64Tg03PEj1~Tg03UYk101Tg04jFj1|Tg02CKj1{Tg06KBk106Tg06LOk10:Tg02Wgj1yTg05?_j1wTg042Kk10?Tg06Gmk10@k30Ak40BTg06MWj1uTg06Nbj1tTg06Oij1sTg000Nk30GTg00c6j3rTg007Lk50HTg01hLk40ITg00G7j2qTf0R2#L#Lp=:f2R3f1R4'1/12p=0g00]=R5@0G52p=IAr552p=Kf7R6f6R7f5R8f4R9f3R:P3P4I0HP2H0Ip=7g016FR;/q2p=6A<342,1:p=?g015DR<g00OER=]3^55^15R>%;2R?$0N%U;R@P0g00^=RAP@g01\Y#:#:#:#:#:RB#L#:#:#:S02,_4RCPAP@P2&0K;RDg005nREP@P2PEP@P2PEP@P2PEP@P2PDPEP@P2PEP@P2PDPEP@P2PEP@P2PDPDP01C5ARF/CARGP@f:RH#RRIP1PFPAP@P2P1P5PAP@P4P1P5PAP@f?/>B#GRJP=P@f@RKfARL/>BRMP:O2%eLRN5D<%;LRO#=RP/mMRQPPP4P2P:CjRR30P0PAP=1]PM1J28g02F:+0JRSg00PERTn10110F00021010400RU1C55RVP1P5PAP=%I2RW#GRXP1PFP5P=fD#;RY#=RZ%I3R[%K3R\3BR]P1P5PAP=P4g03\KR^$0F#TR_fH#;R`#=Ra%I7Rb'A'8%K7Rc,Aa,8_'1PaP8P9Pcf8RdP6PHFPRePaP`P4P2P3DQRa30n200110800012010C10Dn200110F00012010810En200110F00012010A10BX0VP1P5PAP=PXPZP4P2P\P9P:P7FVRZ#9n200110F00012010A10BX0V%OLRf52VRg3<30%ZL%n^#n#TS03'JR^%MLRh#Sg02E\#pS047oBRig014B$0MRjPVP1PFP5PjfCS05#;Rk#=S06%K2Rl7BWP1P5PAPjP4P8P4P2P3H0Ln200110800012010C10DS07n200110F00012010810EX0VX2jRmPgPPP4P2P:Cl%khRhG7S08PLfBRn/>BS09P9P2O3#9X3<=2<N%iLRo%hLRp%dLRqP1P5PAP=PXPZn200110F00012010A10BX0V=2VfRZ%^LRr9@VgRs%`LRt%aLRu%bLRv%cLRLM;5#6PDn0100000020100n200110F000121102103n200110@000121105107n200110?00012110@106PDn10110F00021110?00n0110>00031010?1010?01PDPDn0110=00031110>1010>00PDn0110<00031010=1110=00PDPDn0110;00031110<1010<00PDn0110:00031010;1110;00PDPDn0110900031110:1010:00PDPDn011080003111091010900PDPDn011000003111081010800PDn011010003001110010100PDn10110F00021110100P0PAP@PCPAP@P2PDPEP@P2PEP@P2PEP@P2PEP@P2PDPEP@P2PEP@P2PDPEP@P2PEP@P2PDPDP0PGP@PIP1PFPAP@P2P1P5PAP@P4P1P5PAP@PJP=P@A\OM:=D<NRw1[OMPOP4P2P:CfRx30RyP0PAP=1gOMPSPTn10110F00021010400'1S0:PVP1P5PAP=PXP1PFP5P=AFY[\S0;P1P5PAP=P41E`b,8_1E`c,8_'1RzP`P8P9PcPdP6PHFYP`P`P4P2P3DXR{30n200110800012010C10Dn200110F00012010810En200110F00012010A10BX0VP1P5PAP=PXPYP4P2P\P9P:P7FNRY#9n200110F00012010A10BX0V=2VfR|C?S0<P^PiPjPVP1PFP5PjAFkWlS0=P1P5PAPjP4P8P4P2P3CHn200110800012010C10DS0>n200110F00012010810EX0VX2jP|POP4P2P:CHR}PhG7%;nR~Q09P9P2CW#9X3<=2<NRNPoPpPqP1P5PAP=PXPYn200110F00012010A10BX0V=2VfS09A@V|rS0?PtPuPvPLM;5#6PDn0100000020100n200110F000121102103n200110@000121105107n200110?00012110@106PDn10110F00021110?00n0110>00031010?1010?01PDPDn0110=00031110>1010>00PDn0110<00031010=1110=00PDPDn0110;00031110<1010<00PDn0110:00031010;1110;00PDPDn0110900031110:1010:00PDPDn011080003111091010900PDPDn011000003111081010800PDn011010003001110010100PDn10110F00021110100RY33X1>PA^45R>&0E?P0PAP@PCPAP@P2PDPEP@P2PEP@P2PEP@P2PEP@P2PDPEP@P2PEP@P2PDPEP@P2PEP@P2PDPDP0PGP@PIP1PFPAP@P2P1P5PAP@P4P1P5PAP@PJP=P@11wQRQ/1RP1P5PAP=PXP1PFP5P=P]P1P5PAP=P4fGRRPbO1,8_PRPcO1,8_'1?0ean200110800012010C10Dn200110F00012010810En200110F00012010A10BX0V=<Vg70UQ08PNPoPpPqPZPsPtPuPvPLM;5#6S08PDn0100000020100n200110F000121102103n200110@000121105107n200110?00012110@106PDn10110F00021110?00n0110>00031010?1010?01PDPDn0110=00031110>1010>00PDn0110<00031010=1110=00PDPDn0110;00031110<1010<00PDn0110:00031010;1110;00PDPDn0110900031110:1010:00PDPDn011080003111091010900PDPDn011000003111081010800PDn011010003001110010100PDn10110F00021110100=3@YXD>P=^55^@A^15R>&0D?P0PAP@PCPAP@P2PDPEP@P2PEP@P2PEP@P2PEP@P2PDPEP@P2PEP@P2PDPEP@P2PEP@P2PDPDP0PGP@PIP1PFPAP@P2P1P5PAP@P4P1P5PAP@PJP=P@PKP4P2P:O3S0@,1QP1P5PAP=PXP1PFP5P=P]P1P5PAP=P411zeRe/1an200110800012010C10Dn200110F00012010810En200110F00012010A10BX0V=<VgS0A70UQ08PDn0100000020100n200110F000121102103n200110@000121105107n200110?00012110@106PDn10110F00021110?00n0110>00031010?1010?01PDPDn0110=00031110>1010>00PDn0110<00031010=1110=00PDPDn0110;00031110<1010<00PDn0110:00031010;1110;00PDPDn0110900031110:1010:00PDPDn011080003111091010900PDPDn011000003111081010800PDn011010003001110010100PDn10110F00021110100=3@YX1>Pj^C5^BA^A5Ra&0C?P0PAP@PCPAP@P2PDPEP@P2PEP@P2PEP@P2PEP@P2PDPEP@P2PEP@P2PDPEP@P2PEP@P2PDPDP0PGP@PIP1PFPAP@P2P1P5PAP@P4P1P5PAP@PJP=P@A0QxURQQ0A'1P^PiPjPVPmPgQ0@PhG7PNPoPpPqPZPsPtPuPvPLM;5#6PDn0100000020100n200110F000121102103n200110@000121105107n200110?00012110@106PDn10110F00021110?00n0110>00031010?1010?01PDPDn0110=00031110>1010>00PDn0110<00031010=1110=00PDPDn0110;00031110<1010<00PDn0110:00031010;1110;00PDPDn0110900031110:1010:00PDPDn011080003111091010900PDPDn011000003111081010800PDn011010003001110010100PDn10110F00021110100=3@YX7aP>^6jR>&0>?P0PAP@PCPAP@P2PDPEP@P2PEP@P2PEP@P2PEP@P2PDPEP@P2PEP@P2PDPEP@P2PEP@P2PDPDP0PGP@PIP1PFPAP@P2P1P5PAP@P4P1P5PAP@PJP=P@PQPVP1P5PAP=PXP1PFP5P=P]P1P5PAP=P4PRP`P4P2P3O4,1en200110800012010C10Dn200110F00012010810En200110F00012010A10BX0VPgC?P^PiPjPVPmPgP}PhG7PNPoPpPqPZPsPtPuPvPLM;5#6RsPDn0100000020100n200110F000121102103n200110@000121105107n200110?00012110@106PDn10110F00021110?00n0110>00031010?1010?01PDPDn0110=00031110>1010>00PDn0110<00031010=1110=00PDPDn0110;00031110<1010<00PDn0110:00031010;1110;00PDPDn0110900031110:1010:00PDPDn011080003111091010900PDPDn011000003111081010800PDn011010003001110010100PDn10110F00021110100=3@YX1>P=^45R>&0=?P0PAP@PCPAP@P2PDPEP@P2PEP@P2PEP@P2PEP@P2PDPEP@P2PEP@P2PDPEP@P2PEP@P2PDPDP0PGP@PIP1PFPAP@P2P1P5PAP@P4P1P5PAP@PJP=P@PKPMO1RZ=0wxP1P5PAP=PXP1PFP5P=P]P1P5PAP=P411e{n200110800012010C10DRen200110F00012010810En200110F00012010A10BX0VR]=<Vg70UPsPDn0100000020100n200110F000121102103n200110@000121105107n200110?00012110@106PDn10110F00021110?00n0110>00031010?1010?01PDPDn0110=00031110>1010>00PDn0110<00031010=1110=00PDPDn0110;00031110<1010<00PDn0110:00031010;1110;00PDPDn0110900031110:1010:00PDPDn011080003111091010900PDPDn011000003111081010800PDn011010003001110010100PDn10110F00021110100=3@YX1>P=^>5^<A^95^=5^;A^85R>&0<?P0PAP@PCPAP@P2PDPEP@P2PEP@P2PEP@P2PEP@P2PDPEP@P2PEP@P2PDPEP@P2PEP@P2PDPDP0PGP@PIP1PFPAP@P2P1P5PAP@P4P1P5PAP@PJP=P@11yURUPVP]P1P5PAP=PXQ05P4P2P\P9P:P7O6R]#9n200110F00012010A10BX0V=2VfRsC?P^PiPjPVPmPsP}PhG7PNPoPpPqP1P5PAP=PXP]n200110F00012010A10BX0V=2VfA@VsrPtPuPvPLM;5#6PDn0100000020100n200110F000121102103n200110@000121105107n200110?00012110@106PDn10110F00021110?00n0110>00031010?1010?01PDPDn0110=00031110>1010>00PDn0110<00031010=1110=00PDPDn0110;00031110<1010<00PDn0110:00031010;1110;00PDPDn0110900031110:1010:00PDPDn011080003111091010900PDPDn011000003111081010800PDn011010003001110010100PDn10110F00021110100=3@YX1>1CF5^55^15Rs&09?P0PAP@PCPAP@P2PDPEP@P2PEP@P2PEP@P2PEP@P2PDPEP@P2PEP@P2PDPEP@P2PEP@P2PDPDP0PGP@PIP1PFPAP@P2P1P5PAP@P4P1P5PAP@PJP=P@PUPVP1P5PAP=PXP1PFP5P=Q05P[P\O2Pen200110F00012010810En200110F00012010A10BX0VP|C?P^PiPjPVP1PFP5PjPnPWPlO2Q07n200110F00012010810EX0VX2jP|P}PhG7PNPoPpPqQ09Q0?PtPuPvPLM;5#6PDn0100000020100n200110F000121102103n200110@000121105107n200110?00012110@106PDn10110F00021110?00n0110>00031010?1010?01PDPDn0110=00031110>1010>00PDn0110<00031010=1110=00PDPDn0110;00031110<1010<00PDn0110:00031010;1110;00PDPDn0110900031110:1010:00PDPDn011080003111091010900PDPDn011000003111081010800PDn011010003001110010100PDn10110F00021110100=3@YX0s%UA^45Rs&08?P0PAP@PCPAP@P2PDPEP@P2PEP@P2PEP@P2PEP@P2PDPEP@P2PEP@P2PDPEP@P2PEP@P2PDPDP0PGP@PIP1PFPAP@P2P1P5PAP@P4P1P5PAP@PJP=P@P0PAP=PZPSPTn10110F00021010400P1P5PAP=PXP1PFP5P=Q0;Pen200110F00012010810En200110F00012010A10BX0V=<V|50yP^PiPjPVP1PFP5PjQ0=Q07n200110F00012010810EX0VX2jP|P}PhG7PNPoPpPqQ09Q0?PtPuPvPLM;5#6RyPDn0100000020100n200110F000121102103n200110@000121105107n200110?00012110@106PDn10110F00021110?00n0110>00031010?1010?01PDPDn0110=00031110>1010>00PDn0110<00031010=1110=00PDPDn0110;00031110<1010<00PDn0110:00031010;1110;00PDPDn0110900031110:1010:00PDPDn011080003111091010900PDPDn011000003111081010800PDn011010003001110010100PDn10110F00021110100=3@YX?sP>&07?P0PAP@PCPAP@P2PDPEP@P2PEP@P2PEP@P2PEP@P2PDPEP@P2PEP@P2PDPEP@P2PEP@P2PDPDP0PGP@PIP1PFPAP@P2P1P5PAP@P4P1P5PAP@PJP=P@Q0:PVP1P5PAP=PXP1PFP5P=Q0;P1P5PAP=P4PRP8P9PcPdP6PHO6=0z{n200110800012010C10Dn200110F00012010810En200110F00012010A10BX0VP|C?PyPDn0100000020100n200110F000121102103n200110@000121105107n200110?00012110@106PDn10110F00021110?00n0110>00031010?1010?01PDPDn0110=00031110>1010>00PDn0110<00031010=1110=00PDPDn0110;00031110<1010<00PDn0110:00031010;1110;00PDPDn0110900031110:1010:00PDPDn011080003111091010900PDPDn011000003111081010800PDn011010003001110010100PDn10110F00021110100=3@YX1>Pa^6jRaQ01P0PAP@PCPAP@P2PDPEP@P2PEP@P2PEP@P2PEP@P2PDPEP@P2PEP@P2PDPEP@P2PEP@P2PDPDP0PGP@PIP1PFPAP@P2P1P5PAP@P4P1P5PAP@PJP=P@Q0<P^PiPjPVP1PFP5PjQ0=P1P5PAPjP4fFP8P4P2P3O4n200110800012010C10Dn200110F00012010810EX0VX2jP|P}PhG7PNPoPpPqQ09Q0?PtPuPvPLM;5#6PDn0100000020100n200110F000121102103n200110@000121105107n200110?00012110@106PDn10110F00021110?00n0110>00031010?1010?01PDPDn0110=00031110>1010>00PDn0110<00031010=1110=00PDPDn0110;00031110<1010<00PDn0110:00031010;1110;00PDPDn0110900031110:1010:00PDPDn011080003111091010900PDPDn011000003111081010800PDn011010003001110010100PDn10110F00021110100=3@YX7aP0PAP@Q02,_2RaPAP@P2PDPEP@P2PEP@P2PEP@P2PEP@P2PDPEP@P2PEP@P2PDPEP@P2PEP@P2PDPDP0PGP@f9#RRYP1PFPAP@P2P1P5PAP@P4P1P5PAP@f>/>B#GRLP=P@%;KRv1>KBRu;\:%eKRt5D<1[vuPvP4P2P:Cf30P0PAP=1gvuPSPTn10110F00021010400P1P5PAP=PXP1PFP5P=AFk[\P1P5PAP=P4%;RRR/Eb,8_1ERc,8_'1PRP8P9PcPdP6PHFYPRPRP4P2P3DX30n200110800012010C10Dn200110F00012010810En200110F00012010A10BX0VP1P5PAP=PXPkP4P2P\P9P:P7FNRk#9n200110F00012010A10BX0V%OKRq52VRp5<V30%ZKQ03'JRo%MKRN#SQ047oBRBPjPVP1PFP5PjAF~WlQ0>n200110F00012010810EX0VX2jPpPvP4P2P:CH%kNRNG7POPMP9P2CW#9X3<=2<t%iKRO%hKRh%dKR}P1P5PAP=PXPkn200110F00012010A10BX0V=2Vq%^KRk9@Vp%`KRp%aKR|%bKRi%cKRKM;5#6PDn0100000020100n200110F000121102103n200110@000121105107n200110?00012110@106PDn10110F00021110?00n0110>00031010?1010?01PDPDn0110=00031110>1010>00PDn0110<00031010=1110=00PDPDn0110;00031110<1010<00PDn0110:00031010;1110;00PDPDn0110900031110:1010:00PDPDn011080003111091010900PDPDn011000003111081010800PDn011010003001110010100PDn10110F00021110100R^-03@Q00g06Q4E4%=?RJ$02%~?E4&00J&01?E4%}J%|?E4&04J%{?E4&05J&06?E4%zJ&0:?E4&0;J%y?E4%xJ%w?E4%vJ&0??E4&0@J%u?E4P0PAP@PaPAP@P2PDPEP@P2PEP@P2PEP@P2PEP@P2PDPEP@P2PEP@P2PDPEP@P2PEP@P2PDPDP0PGP@PYP1PFPAP@P2P1P5PAP@P4P1P5PAP@PLP=P@%=vRv@0Au:=D<t1mvuPvP4P2P:Cj30P0PAP=1]vuPSPTn10110F00021010400P1P5PAP=PXP1PFP5P=Q06?B[\P1P5PAP=P4%=RR[/Ab,8_1A[c,8_'1P[P8P9PcPdP6PHFPP[PRP4P2P3DQ30n200110800012010C10Dn200110F00012010810En200110F00012010A10BX0VP1P5PAP=PXQ06P4P2P\P9P:P7FVR7#9n200110F00012010A10BX0V=2VqR\5<V30PoPBPjPVP1PFP5Pj%=~?BWlQ07n200110F00012010810EX0VX2jP\PvP4P2P:ClPNG7PPPMP9P2H0B#9X3<=2<tPOPhP}P1P5PAP=PXP7n200110F00012010A10BX0V=2VqA@V\kPpP|PiPKM;5#6PDn0100000020100n200110F000121102103n200110@000121105107n200110?00012110@106PDn10110F00021110?00n0110>00031010?1010?01PDPDn0110=00031110>1010>00PDn0110<00031010=1110=00PDPDn0110;00031110<1010<00PDn0110:00031010;1110;00PDPDn0110900031110:1010:00PDPDn011080003111091010900PDPDn011000003111081010800PDn011010003001110010100PDn10110F00021110100=3@^e%t2%s253@eX:;o"). Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition brk_req (cs : acs) : option Z :=
  match lit_diff (reg cs 10) (a_brk cs) with
  | Some d => if (Z.ltb 0 d && Z.eqb (d mod 4096) 0 && Z.leb d (2 ^ 40))%bool then Some d else None
  | None => None
  end.

(* [comment removed for export] *)
Definition brk_base_ok (cs : acs) (d : Z) : bool :=
  let k := kn cs in let b := a_brk cs in
  (page_aligned k b
   && match xlo k b, xhi k b with
      | Some lo, Some hi => Z.ltb 0 lo && Z.leb (img_hi A) lo && Z.leb (hi + d) KHI
      | _, _ => false
      end)%bool.

(* [comment removed for export] *)
Definition brk_grow_possible (cs : acs) (d : Z) : bool :=
  let k := kn cs in let '(bb, bk) := split_lit (a_brk cs) in
  (brk_base_ok cs d && no_fog (a_maps cs)
   && forallb (fun m => ranges_apart_x k bb bk (ELit (d + 4096)) (am_base m) 0 (am_len m)) (a_maps cs)  (* [comment removed for export] *)
   && budget_ok cs d)%bool.

(* [comment removed for export] *)
Definition brk_grow_blocked (cs : acs) (d : Z) : bool :=
  let k := kn cs in let b := a_brk cs in
  (brk_base_ok cs d
   && existsb (fun m => negb (is_fog m)
                        && lin_ge0 k [(am_base m, -1); (am_len m, 0)] [(b, 0)]      (* [comment removed for export] *)
                        && lin_ge0 k [(b, d - 1)] [(am_base m, 0)])               (* [comment removed for export] *)
              (a_maps cs))%bool.

(* [comment removed for export] *)
Definition node_brk1 (cs : acs) : option acs :=
  match reg_lit cs 17 with
  | Some 214 =>
      let ok := match reg_lit cs 10 with
                | Some 0 => true
                | _ => match brk_req cs with Some d => brk_grow_blocked cs d | None => false end
                end in
      if ok then Some (set_pc (set_reg cs 10 (a_brk cs)) (pc cs + 4)) else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition node_brk2 (cs : acs) : option (acs * acs) :=
  match reg_lit cs 17, brk_req cs with
  | Some 214, Some d =>
      if (brk_grow_possible cs d && expr_vars_lt (nxt cs) (reg cs 10))%bool then
        let k := kn cs in let b := a_brk cs in let '(bb, bk) := split_lit b in
        let csA := set_pc (set_reg cs 10 b) (pc cs + 4) in
        let k' := kn_grant_filterM k (a_maps cs) in
        let ss := a_ss cs in
        let csB := ACS (mk_ss (pc cs + 4) (s_regs ss) k' (s_next ss))
                       (AM b (ELit d) KRW :: a_maps cs) (a_totsz cs + d) (a_ylo cs) (a_eager cs + d)
                       (a_vis cs) (a_ghost cs) (a_abytes cs) (reg cs 10) (a_fd cs) (a_tidset cs) in
        match vis_add csB b (ELit d) (KWr (SA bb bk) (ELit d) :: KZero (SA bb bk) (ELit d) :: kn csB) with
        | Some csB' => Some (csA, csB')
        | None => None
        end
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition node_brk2s (cs : acs) : option (acs * acs) :=
  match reg_lit cs 17, brk_req cs with
  | Some 214, Some d =>
      if (brk_base_ok cs d && no_fog (a_maps cs) && budget_ok cs d && expr_vars_lt (nxt cs) (reg cs 10))%bool then
        let k := kn cs in let b := a_brk cs in let '(bb, bk) := split_lit b in
        let csA := set_pc (set_reg cs 10 b) (pc cs + 4) in
        (* [comment removed for export] *)
        (* [comment removed for export] *)
        let k' := direct_fact k b 0 (ELit d) (ELit (null2_loc cs)) 0
                  ++ [KDisj (SA (ELit (null2_loc cs)) 0) (ELit (KHI - null2_loc cs)) (SA b 0) (ELit d)]
                  ++ kdisj_new (a_maps cs) b (ELit d) ++ kn_grant_filterM k (a_maps cs) in
        let ss := a_ss cs in
        let csB := ACS (mk_ss (pc cs + 4) (s_regs ss) k' (s_next ss))
                       (AM b (ELit d) KRW :: a_maps cs) (a_totsz cs + d) (a_ylo cs) (a_eager cs + d)
                       (a_vis cs) (a_ghost cs) (a_abytes cs) (reg cs 10) (a_fd cs) (a_tidset cs) in
        match vis_add csB b (ELit d) (KWr (SA bb bk) (ELit d) :: KZero (SA bb bk) (ELit d) :: kn csB) with
        | Some csB' => Some (csA, csB')
        | None => None
        end
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)

Definition node_settid (cs : acs) : option acs :=
  match reg_lit cs 17 with
  | Some 96 =>
      if (negb (a_tidset cs) && fresh_ok cs)%bool then
        let v := nxt cs in let ss := a_ss cs in
        Some (ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (EVar v)) (KRange (EVar v) 1 (PID_MAX - 1) :: s_know ss) (S v))
                 (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) true)
      else None
  | _ => None
  end.

Definition node_exit (cs : acs) : option Z :=
  match reg_lit cs 17, reg_lit cs 10 with
  | Some 94, Some code => Some (Z.land code 255)
  | Some 93, Some code => Some (Z.land code 255)
  | _, _ => None
  end.

(* [comment removed for export] *)

Fixpoint list_set_nth {T} (i : nat) (x : T) (l : list T) : list T :=
  match l, i with
  | [], _ => []
  | _ :: r, O => x :: r
  | y :: r, S i' => y :: list_set_nth i' x r
  end.
Fixpoint list_insert_nth {T} (i : nat) (x : T) (l : list T) : list T :=
  match i, l with
  | O, _ => x :: l
  | S i', y :: r => y :: list_insert_nth i' x r
  | S _, [] => [x]
  end.

Definition fog_token (sz : Z) : amap := AM (ELit 0) (ELit sz) KFOG.

Definition with_maps (cs : acs) (ms : list amap) : acs :=
  ACS (a_ss cs) ms (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).

(* [comment removed for export] *)
Definition node_fog (cs : acs) (i : nat) (sz : Z) : option acs :=
  match nth_error (a_maps cs) i with
  | Some m =>
      if (negb (is_fog m) && Z.leb 0 sz && Z.ltb sz two64
          && match xhi (kn cs) (am_len m) with Some h => Z.leb h sz | None => false end)%bool
      then Some (with_maps cs (list_set_nth i (fog_token sz) (a_maps cs)))
      else None
  | None => None
  end.

(* [comment removed for export] *)
Definition node_fognew (cs : acs) (i : nat) (sz : Z) : option acs :=
  if (Nat.leb i (length (a_maps cs)) && Z.leb 0 sz && Z.ltb sz two64)%bool
  then Some (with_maps cs (list_insert_nth i (fog_token sz) (a_maps cs)))
  else None.

(* [comment removed for export] *)
Definition node_ghost (cs : acs) (b n : expr) : option acs :=
  match xhi (kn cs) n with
  | Some nhi =>
      if (expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n && Z.leb (a_eager cs + a_abytes cs + vis_cost nhi) LIMIT)%bool
      then Some (ACS (a_ss cs) (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs ++ [(b, n)])
                     (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | None => None
  end.

(* [comment removed for export] *)
Definition vis_here (b n : expr) (p : expr * expr) : bool := (expr_eqb (fst p) b && expr_eqb (snd p) n)%bool.

Definition node_unvis_ref (cs : acs) (b n : expr) : option acs :=
  let k := kn cs in
  let '(bb, bk) := split_lit b in
  let '(sb, sk, sn) := shadow_of k b n in
  match xhi k b, xhi k n with
  | Some bh, Some nh =>
      if (existsb (vis_here b n) (a_vis cs)
          && Z.leb 3 (ealign k b) && Z.leb 3 (ealign k n) && flat_x k bb bk n && Z.leb (bh + nh) ATOPMAX   (* [comment removed for export] *)
          && flat_x k sb sk sn && kzero_x k k sb sk sn
          (* [comment removed for export] *)
          && ranges_apart_x k bb bk n (ELit SW_LO) 0 (ELit (KHI - SW_LO)))%bool
      then
        let k1 := kn_unfill k bb bk n in
        let k2 := kn_unfill k1 sb sk sn in
        let ss := a_ss cs in
        Some (ACS (mk_ss (s_pc ss) (s_regs ss) k2 (s_next ss))
                  (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                  (List.filter (fun p => negb (vis_here b n p)) (a_vis cs)) (a_ghost cs ++ [(b, n)])
                  (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | _, _ => None
  end.
(* [comment removed for export] *)
Definition node_unvis (cs : acs) (b n : expr) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  let '(bb, bk) := split_lit b in
  let '(sb, sk, sn) := shadow_ofB bc b n in
  match xhiB bc b, xhiB bc n with
  | Some bh, Some nh =>
      if (existsb (vis_here b n) (a_vis cs)
          && Z.leb 3 (ealignB bc b) && Z.leb 3 (ealignB bc n) && flat_xB bc bb bk n && Z.leb (bh + nh) ATOPMAX   (* [comment removed for export] *)
          && flat_xB bc sb sk sn && kzero_xB bc k sb sk sn
          && ranges_apart_xB bc bb bk n (ELit SW_LO) 0 (ELit (KHI - SW_LO)))%bool   (* [comment removed for export] *)
      then
        let k1 := kn_unfillB bc bb bk n in
        let k2 := kn_unfillM k1 sb sk sn in
        let ss := a_ss cs in
        Some (ACS (mk_ss (s_pc ss) (s_regs ss) k2 (s_next ss))
                  (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                  (List.filter (fun p => negb (vis_here b n p)) (a_vis cs)) (a_ghost cs ++ [(b, n)])
                  (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | _, _ => None
  end.

Lemma node_unvis_eq : forall cs b n, node_unvis cs b n = node_unvis_ref cs b n.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bh11nh21pi001ph31eh41kh51lh62b1h72b2h82csh92k1h:2k2h;2n1h<2n2h=1oh>3offh?2ubh@2ukhA2unhB1zi012bbi022bhi032bki042nhi052sbi062ski072sni081xp&0p;1p;2p;3p;4p;5p;7p;;p;6g00i8j19Tg03ock104j2=Tg00FUR0j1VTg01E@j1DTg00bVR1j2ATg01`>j14Tg04_Jj3Lj1lTg03S\j2<j1nTg06R=j2Yj3NTg00k8j1GTg008Ij3FTg040cj1fTg03[Pj1eTg01N<j26Tg03aCj4>j1jTg01M_k202Tg03V]j5[j1sTg00Pej1ZTg02AFj2yTg02B@j7Wj1pTg00g8j1HTg01b@j1UTg00h8j1TTg02N3j4Xj1uTg02Y1R2j4:Tg01c>j1KTg01hLj45Tg00j6j1ITg059>j1JTg05:Aj1ETg054Xj1MTg01NYj1OTg01GLj3PTg00l9j1QTg03l2j4CTg00fXj1dTg00Lej3STg058aj3cTg055[j1bTg00`Uj1aTg00aVj1`Tg05;Bj1_Tg05<Fl;7Tg00n=k103Tg04`Pj3^j1xTg03T\j2?j1wTg03bFj4@k101Tg019Ij22Tg03Waj5]j1{Tg02@>j7\j1tTg02O9R3j4;j1|Tg001kj31Tg00A2j1}Tg00GYj2qTg02CKj1oTg00>Oj63Tg03UYj1mTg04jFj1rTg06LOj1kTg02Wgj1vTg05?_j1iTg041Hj1zj2RTg042Kj1hTg06SAj3~Tg06TGj3gTg00G7k200Tf2R4f1R5f0R6'6'2p=B1245/26p=0g016FR70006p=8g00]=R8g00^=R9^38R:%94R;$04%V7R<P1P8P9P<%D4R=P11A89R>P8P<f5#9R?#4f4R@f3RA3LRBP1P8P9P<P5P0P9P<f9RC#9RD#4REf8RF'<RGP0P9P<f:RH#9RI#4RJ/<FRKg00OERLP<1A88RM1YHCf;RN#GRO3FRPg03\K#f#eRQPFPHO13BPFPCO1,6Q%9NRR#4RSf7RTf6RUPCC>3020256g063n'6RVPSPAP4P@C>30PSPRPAP4P@D[RWPSPTPUPCg05TNRX#ZRYg02E\RZg05UO/yX#ZRXFWR[30%HNR\#UR]%T\R^PSPTPUPCCXPAP4P@C:%K\R\C5%INRS%JNR_%ENR`%MNRaANNH6#OX2M=PMORO%QNP8P8PHPCCC%dMRb5SM5cMRc%bNRd%aNRe%`NRf%_NRNM;7#8Rg&037Rhn0100000020000Phn10110800021010400Phn10110800021010200n2001100000120105106n2001108000120100107n2001108000120101103P1P8P9P<P=P1P>P8P<A^?@AR?P1P8P9P<P5P0P9P<1?DFRiP0P9P<1?IFRjPLP<1=RH,6Q1=RC,6Q50PRPPRPTPUPCC@'2PRPAP4P@C@70VRkPRPRPAP4P@D]'2RlPRPTPUPCPYPZPXF\'2P]P^PRPTPUPCC;RmPAP4P@C;P\C5PSP_P`PaPOPcPdPePfPNM;7#8RnPhn0100000020000Phn10110800021010400Phn10110800021010200n2001100000120105106n2001108000120100107n2001108000120101103Ro31XB:PL^18^>9^08R:&01;P1P8P9P<P=P1P>P8P<PBP1P8P9P<P5P0P9P<PGP0P9P<PKPLP<PFPTPUPCO3Rp,2PPFPAP4P@O370V?0W[PgPhn0100000020000Phn10110800021010400Phn10110800021010200n2001100000120105106n2001108000120100107n2001108000120101103=1<oX0:g014B#}Rg^A8^@9^?8RP%|;P1P8P9P<P=P1P>P8P<PBP1P8P9P<P5P0P9P<PGP0P9P<PKPLP<A0kW[P]P^PpPAP4P@C:P\C5PSP_P`PaPOPcPdPePfPNM;7#8Phn0100000020000Phn10110800021010400Phn10110800021010200n2001100000120105106n2001108000120100107n2001108000120101103=1<oX5PP:^4gR:%{;P1P8P9P<P=P1P>P8P<PBP1P8P9P<P5P0P9P<PGP0P9P<PKPLP<PFPRPAP4P@O4=0k[P]P^PmPAP4P@C:P\C5PSP_P`PaPOPcPdPePfPNM;7#8RkPhn0100000020000Phn10110800021010400Phn10110800021010200n2001100000120105106n2001108000120100107n2001108000120101103=1<oX0:1A>8^18^08R:%x;P1P8P9P<P=P1P>P8P<P4P@PAO2P1P8P9P<P5P0P9P<PGP0P9P<PKPLP<12l[R[PkPhn0100000020000RkPhn10110800021010400Phn10110800021010200n2001100000120105106n2001108000120100107n2001108000120101103=1<oX2:%V9^38R:%w;P1P8P9P<P=P1P>P8P<P?P1P8P9P<P5P0P9P<PUPFO1P0P9P<PTPFO1PkPhn10110800021010400Phn10110800021010200n2001100000120105106n2001108000120100107n2001108000120101103=1<oX=:PP^4gRgP3P1P8P9P<P=P1P>P8P<P?P1P8P9P<P5P0P9P<PiP0P9P<PjPLP<P[P]P^PFPmPAP4P@O4P\C5PSP_P`PaPOPcPdPePfPNM;7#8Phn0100000020000Phn10110800021010400Phn10110800021010200n2001100000120105106n2001108000120100107n2001108000120101103=1<oX5gPL^<8^:9^78^;8^99^68Rg%t;P1P8P9P<P=P1P>P8P<P?P1P8P9P<P5P0P9P<PiP0P9P<PjPLP<PFPTPUPCPYPZPXO6,2lPnPhn0100000020000Phn10110800021010400Phn10110800021010200n2001100000120105106n2001108000120100107n2001108000120101103=1<oX0gP1P8P9P<%D5RgP1P>P8P<%9@Ro?^A4P1P8P9P<P5P0P9P<%9FRn/?TP0P9P<1?DTPLP<1YCF%GHRD5FMRl1=IC7BQ1=IF,6QPIPTPUPFC@30PIPAP4P@C@70VPIPIPAP4P@D]PIPTPUPFPYPZPXF\30%HHRj#URi%TjR?PIPTPUPFC;PAP4P@C;%KjRjC5%IHR=%JHRN%EHRf%MHReANHC6#OX2M=PMDRD%QHP8P8PCPFCC=SMb5cMRM%bHRb%aHRd%`HRc%_HRHM;7#8Phn0100000020000Phn10110800021010400Phn10110800021010200n2001100000120105106n2001108000120100107n2001108000120101103RO,q<%4;Ra#p%o;E3P2g06Q4E3%na%m;E3%la%r;E3%sa%k;E3%ua%v;E3%ja%i;E3%za%h;E3P1P8P9P<PgP1P>P8P<%4o?LA4P1P8P9P<P5P0P9P<%4n/<TP0P9P<1<ETPLP<1RJC9BlQ1RJF,6QPJPTPUPFC>30PJPAP4P@C>70VPJPIPAP4P@D[PJPTPUPFPYPZPXFW30PiP?PJPTPUPFCXPAP4P@C:PjC5P=PNPfPePDPMPbPdPcPHM;7#8Phn0100000020000Phn10110800021010400Phn10110800021010200n2001100000120105106n2001108000120100107n2001108000120101103=1<OeA~456Ag45651<eX18W0X87o"). Qed.


(* [comment removed for export] *)
Definition node_havocbrk (cs : acs) (lo hi : Z) : option acs :=
  match xlo (kn cs) (a_brk cs), xhi (kn cs) (a_brk cs) with
  | Some l, Some h =>
      if (fresh_ok cs && Z.leb lo l && Z.leb h hi)%bool then
        let v := nxt cs in let ss := a_ss cs in
        Some (ACS (mk_ss (s_pc ss) (s_regs ss) (KRange (EVar v) lo hi :: s_know ss) (S v))
                  (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (EVar v) (a_fd cs) (a_tidset cs))
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition node_intro (cs : acs) (lo hi : Z) : option acs :=
  if (fresh_ok cs && Z.leb 0 lo && Z.leb lo hi && Z.ltb hi two64)%bool then
    let v := nxt cs in let ss := a_ss cs in
    Some (with_ss cs (mk_ss (s_pc ss) (s_regs ss) (KRange (EVar v) lo hi :: s_know ss) (S v)))
  else None.

(* [comment removed for export] *)
Definition introw_eval (v : nat) (w : Z) (e : expr) : option Z :=
  match eval_closed (esubst (EVar v) (ELit w) e) with Some z => Some (z mod two64)%Z | None => None end.
Definition introw_fact_ok (v : nat) (w : Z) (K : kentry) : bool :=
  match K with
  | KRange e lo hi => match introw_eval v w e with Some z => (Z.leb lo z && Z.leb z hi)%bool | None => false end
  | KAlign e m => match introw_eval v w e with Some z => (Z.ltb 0 m && Z.eqb (z mod m) 0)%bool | None => false end
  | KDisj (SA b1 o1) n1 (SA b2 o2) n2 =>
      match introw_eval v w b1, introw_eval v w n1, introw_eval v w b2, introw_eval v w n2 with
      | Some x1, Some l1, Some x2, Some l2 => (Z.leb (x1 + o1 + l1) (x2 + o2) || Z.leb (x2 + o2 + l2) (x1 + o1))%bool
      | _, _, _, _ => false
      end
  | _ => false
  end.
Definition node_introw (cs : acs) (w : Z) (fs : list kentry) : option acs :=
  let v := nxt cs in
  if (fresh_ok cs && Z.leb 0 w && Z.ltb w two64 && forallb (introw_fact_ok v w) fs)%bool then
    let ss := a_ss cs in
    Some (with_ss cs (mk_ss (s_pc ss) (s_regs ss) (fs ++ s_know ss) (S v)))
  else None.

(* [comment removed for export] *)
Definition SPIN_WORD : Z := 0x6f.
Definition node_spin (cs : acs) : bool :=
  (Z.leb 0 (pc cs) && Z.ltb (pc cs + 4) two64 &&
  match fetch_word segs (Z_to_bv 64 (pc cs)) with
  | Some w => Z.eqb (bv_unsigned w) SPIN_WORD
  | None => false
  end)%bool.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition summary_fill_ref (cs : acs) (entry : Z) (cmax : Z) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) entry) then None else
  match ret_lit cs, reg_lit cs 11 with
  | Some ret, Some c =>
      if negb (Z.ltb c cmax) then None else
      let dst := reg cs 10 in let ne := reg cs 12 in
      let '(db, dk) := split_lit dst in
      let c8 := c mod 256 in
      match xlo k ne, xhi k ne, xhi k dst with
      | Some nlo, Some nhi, Some dhi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.ltb (dhi + nhi) two64)%bool then
            if (Z.eqb nhi 0) then after_call cs ret (Some dst) k else
            if (Z.eqb c8 0 && kzero_x k k db dk ne && kwritable_x k k db dk ne)%bool then after_call cs ret (Some dst) k else
            match (if off_image_x k db dk ne then Some k
                   else match dst, ne with ELit d, ELit n => Some (kimg_cut k (d mod two64) n) | _, _ => None end) with
            | None => None
            | Some k0 =>
            if kwritable_x k k db dk ne then
              let k1 := kn_havoc k0 db dk ne in
              let k2 := if Z.ltb 0 nlo then (if Z.eqb c8 0 then KZero (SA db dk) ne else KFill (SA db dk) ne c8) :: k1 else k1 in
              after_call cs ret (Some dst) k2
            else None
            end
          else None
      | _, _, _ => None
      end
  | _, _ => None
  end.
(* [comment removed for export] *)
Definition summary_fill (cs : acs) (entry : Z) (cmax : Z) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  if negb (Z.eqb (pc cs) entry) then None else
  match ret_lit cs, reg_lit cs 11 with
  | Some ret, Some c =>
      if negb (Z.ltb c cmax) then None else
      let dst := reg cs 10 in let ne := reg cs 12 in
      let '(db, dk) := split_lit dst in
      let c8 := c mod 256 in
      match xloB bc ne, xhiB bc ne, xhiB bc dst with
      | Some nlo, Some nhi, Some dhi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.ltb (dhi + nhi) two64)%bool then
            if (Z.eqb nhi 0) then after_call cs ret (Some dst) k else
            if (Z.eqb c8 0 && kzero_xB bc k db dk ne && kwritable_xB bc k db dk ne)%bool then after_call cs ret (Some dst) k else
            match (if off_image_xB bc db dk ne then Some k
                   else match dst, ne with ELit d, ELit n => Some (kimg_cut k (d mod two64) n) | _, _ => None end) with
            | None => None
            | Some k0 =>
            if kwritable_xB bc k db dk ne then
              let k1 := kn_havocM k0 db dk ne in
              let k2 := if Z.ltb 0 nlo then (if Z.eqb c8 0 then KZero (SA db dk) ne else KFill (SA db dk) ne c8) :: k1 else k1 in
              after_call cs ret (Some dst) k2
            else None
            end
          else None
      | _, _, _ => None
      end
  | _, _ => None
  end.

Lemma summary_fill_eq : forall cs entry cmax, summary_fill cs entry cmax = summary_fill_ref cs entry cmax.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bi001bh11kh21oh34cmaxh42csh51ei011eh65entryh71lh81ni021nh93offh:2ubh;2ukh<2uni031ai041ci051di062dbi073dhii082dki093dsti0:1ii0;2k0i0<2loi0=2nei0>3nhii0?3nloi0@2opi0A3reti0B2sxi0C1xp;1p;2p;4p;5p;3p;6g00A2j1nTg00i8j12Tg03RUj1[j5BTg00FUR0j1DTg057cj1UTg03[nj2:Tg01NYj1=Tg00n=j1MTg06UQj1LTg003kj1>Tg05GIj2GTg02Acj2@Tg01DAj20Tg01E@j1TTg01`>j16Tg03K?j2Qj1gTg03S\j2?j1cTg01N<j2PTg03Zkj19Tg03[Pj1ETg040cj1\Tg04n`j2ZTg019Ij21Tg01M_j2YTg00G7j24Tg06VTj45Tg03C9j2CTg03V]j5Jj1dTg03]0j4Kj1aTg06WZj3ITg00ojj2XTg01O7j2HTg01WSj3NTg02ncR1j4OTg00Lej3;Tg03MCj2Fj1jTg03T\j2Aj1kTg03Waj5Sj1mTg03^8j4Wj1lTg02kNR2j4VTg001kj33Tg00GYj2hTg00>Oj67Tg03OAj1fTg03UYj1bTg06X^j1`Tg06LOj1eTg03QMj1_j5RTg06Yjj1^Tg06[6j3]Tg06\>j3iTf0R3#>#>p=8%93#9p=<g016FR4g00^=R5g014BR6#nR7g00]=R8g00OER9^88^95]0R:]1R;f2R<#2R=#[%D4R>P9P>f3R?#U/:<#=R@%M4R4P0P5P>%L?RAP0P5P>f4RBg01\Y#8#8#8#8#8RC#>RD'GREP9P>1@3?#=RFP4g00bVRGP8P5P>f5RH/0C#TRIP0P5P>f7RJ#2RK#6RL%>DRM,0JRN'QROP0P5P>f8RP#2RQ#6RR10PMRS'?RTP0P5P>f9RU#2RV#6RW10UCRX'?RYP9P>g02E\RZ/P<f1R[g03\K#9R\#E%\\#9#<#E'Z'P'11Y3[g02F:R]'@'1R^P9P>1:[ZR_f:R`f6Ra10`CRb,48Rc%2`RdC5ReP9P>%9\#<#<#<#ER\,CH/:ZRf%6dRgPdPBP?10`MRhDJ'1PJPdPBP?PhO4Ri'1PeP0P7P>P9%D7RjPgPBP?PhCK147dRkP8PjPbP8Pjf;Rb/0MRlf<#21C[]R];I3,47%M7RmPmPmPmPmPmPmn0110=000810102101023010@1031003010@1031003010@1031003010@1031004010B10<1021014010B10;10:102PmPmPmPmPmPmPmn01109000810105101023010@1031003010@1031003010@1031003010@1031004010B10<1021014010B10;10:102Rnn0100000020000RoP9P>PP%2bRpPHPBPlO4PbPJ10bC,48RqP9P71@Z?RrP9P61Ca\R\/:ZRZ1XHBRs/HlANsl\n0100000020000RtP3PHPBPlCORu5;6Pun0100000020000C5RuP4n0100000020000P4n10110C00021010;00n0100000020001n0100000020001P4n0100000020100P4n10110C00021110700P4n10110C00021110>00P4n10110C00021110?00n200110C000121106108n0100000020001P4n10110C00021110400P4n10110C00021110A00n0100000020001P9P>P@P4P0P5P>PAP0P5P>PEP9P>PFP4PGP8P5P>PIP0P5P>1FKNRvP0P5P>1AQSRwP0P5P>1AVXRxP9P>P^P9P>P_PeP9P>PdPdPBP?PhDS,1fPdPdPBP?PhDBRy'1RzPeP0P7P>P9PjPdPBP?PhCWPkPnn0100000020000R{P9P>PpPpPHPBPlDBR|PbPJPqP9P7PrP3PHPBPlCVR}9;6tP}n0100000020000C5P4n0100000020000P4n10110C00021010;00n0100000020001n0100000020001P4n0100000020100P4n10110C00021110700P4n10110C00021110>00P4n10110C00021110?00n200110C000121106108n0100000020001P4n10110C00021110400P4n10110C00021110A00n0100000020001R}33X0;P;%m=P9P>P@P4P0P5P>PAP0P5P>PEP9P>PFP4PGP8P5P>PIP0P5P>POP0P5P>PTP0P5P>PYP9P>P^P9P>P_PeP9P>11fi/1yPeP0P7P>PoP9P>P|PuP4n0100000020000RuP4n10110C00021010;00n0100000020001n0100000020001P4n0100000020100P4n10110C00021110700P4n10110C00021110>00P4n10110C00021110?00n200110C000121106108n0100000020001P4n10110C00021110400P4n10110C00021110A00n0100000020001=3>}X0;P:%l=P9P>P@P4P0P5P>PAP0P5P>PEP9P>PFP4PGP8P5P>PIP0P5P>POP0P5P>PTP0P5P>PYP9P>P^P9P>P_PeP9P>PzPeP0P7P>P9PjPJPBP?PhO3PkPnn0100000020000PuP4n10110C00021010;00n0100000020001n0100000020001P4n0100000020100P4n10110C00021110700P4n10110C00021110>00P4n10110C00021110?00n200110C000121106108n0100000020001P4n10110C00021110400P4n10110C00021110A00n0100000020001=3>}X0:%D5^58R:%k=P9P>P@P4P0P5P>PAP0P5P>PEP9P>PFP4PGP8P5P>PIP0P5P>POP0P5P>PHPSO1P0P5P>PaPXO1P9P>P^P9P>P_PeP9P>PzPeP0P7P>P{PuP4n10110C00021010;00n0100000020001n0100000020001P4n0100000020100RuP4n10110C00021110700P4n10110C00021110>00P4n10110C00021110?00n200110C000121106108n0100000020001P4n10110C00021110400P4n10110C00021110A00n0100000020001=3>}X2:P:%j=P9P>P@P4P0P5P>PAP0P5P>PEP9P>PFP4PGP8P5P>PIP0P5P>PBPNO1P0P5P>PwP0P5P>PxPuP4n10110C00021110700P4n10110C00021110>00P4n10110C00021110?00n200110C000121106108n0100000020001P4n10110C00021110400P4n10110C00021110A00n0100000020001=3>}X2:P7^<8^;5^:8^17R:P2P9P>P@P4P0P5P>PAP0P5P>PEP9P>PFP4PGP8P5P>PIP0P5P>PvP0P5P>PwP0P5P>PxP9P>P^P9P>P_PeP9P>PzPeP0P7P>P{P9P>P|PbPJPqP9P7PrPPP3PHPBPlO4Rl9;6tPln0100000020000C5P4n0100000020000P4n10110C00021010;00n0100000020001n0100000020001P4n0100000020100P4n10110C00021110700P4n10110C00021110>00P4n10110C00021110?00n200110C000121106108n0100000020001P4n10110C00021110400P4n10110C00021110A00n0100000020001=3>}X7:P9P>%U</:[#=R:P4P0P5P>%L<R}P0P5P>1G?DRDP9P>1@3<#=RlP4PGP8P5P>10BC#TRtP0P5P>%2aRq10aMRb'FP0P5P>1AKNP0P5P>10PCRP,AQP9P>P^P9P>P_PUPa148XPVC5RaP9P>PVPVPBP?10UMRUDS,1fPVPVPBP?PUDB'1PaP0P7P>P9PjPVPBP?PUCW147VRMP8PjPXP8PjPhAIp]3,47PmPmPmPmPmPmPmn0110=000810102101023010@1031003010@1031003010@1031003010@1031004010B10<1021014010B10;10:102PmPmPmPmPmPmPmn01109000810105101023010@1031003010@1031003010@1031003010@1031004010B10<1021014010B10;10:102Rmn0100000020000P9P>PdPdPHPBPhDBP`PJPcP9P7PrP9P6PZ1HshANsh\n0100000020000RsP3PHPBPhCVR\5;6P\n0100000020000C5P4n0100000020000P4n10110C00021010;00n0100000020001n0100000020001P4n0100000020100P4n10110C00021110700P4n10110C00021110>00P4n10110C00021110?00n200110C000121106108n0100000020001P4n10110C00021110400P4n10110C00021110A00n0100000020001R\,h>P1g06]JE7%6=R1#g%f=E7%c1%b=E7%a1%`=E7%d1%e=E7%_1%^=E7P9P>P:P4P0P5P>P}P0P5P>PDP9P>PlP4PGP8P5P>PtP0P5P>%6q/QbP0P5P>1?LNP0P5P>1?RPP9P>P^P9P>P_PaP9P>PWPVPBP?PUDJ,1fPWPVPBP?PUDR'1PaP0P7P>P9PjPWPBP?PUCKPMPmn0100000020000P9P>PgPdPHPBPhDRP`PJPcP9P7PrP3PHPBPhCORh9;6sPhn0100000020000C5P4n0100000020000P4n10110C00021010;00n0100000020001n0100000020001P4n0100000020100P4n10110C00021110700P4n10110C00021110>00P4n10110C00021110?00n200110C000121106108n0100000020001P4n10110C00021110400P4n10110C00021110A00n0100000020001=3>\eA]<[3Ai<[353>eX35W6W4o"). Qed.


(* [comment removed for export] *)
Fixpoint copy_facts (fuel : nat) (k : list kentry) (sb : expr) (sk : Z) (db : expr) (dk : Z) (n : Z)
  : option (list kentry) :=
  match fuel with
  | O => Some []
  | S f =>
      if (Z.leb 8 n &&
          match kread8e k sb sk with Some _ => true | None => match kread_bytes 8 k sb sk with Some _ => true | None => false end end)%bool then
        match (match kread8e k sb sk with
               | Some v => Some v
               | None => match kread_bytes 8 k sb sk with
                         | Some bs => Some (ELit (zbytes_le_to_Z bs))
                         | None => None
                         end
               end), copy_facts f k sb (sk + 8) db (dk + 8) (n - 8) with
        | Some v, Some rest => Some (KWord (SA db dk) 8 v :: rest)
        | _, _ => None
        end
      else if Z.leb 1 n then (* [comment removed for export] *)
        match know_lookup segs k sb sk 1 false [] [], copy_facts f k sb (sk + 1) db (dk + 1) (n - 1) with
        | LHit v [] _, Some rest => Some (KWord (SA db dk) 1 v :: rest)
        | _, _ => None
        end
      else Some []
  end.

Fixpoint copy_factsB (bc : bctx) (fuel : nat) (sb : expr) (sk : Z) (db : expr) (dk : Z) (n : Z)
  : option (list kentry) :=
  match fuel with
  | O => Some []
  | S f =>
      if (Z.leb 8 n &&
          match kread8eB bc sb sk with Some _ => true | None => match kread_bytesB bc 8 sb sk with Some _ => true | None => false end end)%bool then
        match (match kread8eB bc sb sk with
               | Some v => Some v
               | None => match kread_bytesB bc 8 sb sk with
                         | Some bs => Some (ELit (zbytes_le_to_Z bs))
                         | None => None
                         end
               end), copy_factsB bc f sb (sk + 8) db (dk + 8) (n - 8) with
        | Some v, Some rest => Some (KWord (SA db dk) 8 v :: rest)
        | _, _ => None
        end
      else if Z.leb 1 n then (* [comment removed for export] *)
        match know_lookupB segs bc sb sk 1 false [] [], copy_factsB bc f sb (sk + 1) db (dk + 1) (n - 1) with
        | LHit v [] _, Some rest => Some (KWord (SA db dk) 1 v :: rest)
        | _, _ => None
        end
      else Some []
  end.

Lemma copy_factsB_eqf' : forall fk fuel, copy_factsB (mkbc fk) fuel = copy_facts fuel fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h04fuelh11oh21bh31nh43offh51xi001xh62x0h72x1h82x2h92x3h:2IHh;3acch<2dbh=2dkh>1fh?2fkh@5hintsi015hintshA1li021lhB2rbhC2rkhD2sbhE2skhF2sxi032bsi041ei054resti061si073scsi081vp;1p;2p;3p;4p;5p;6p;7p;8g00A2R0j19Tg00FUR1j1DTg01`>j11Tg06^Rj2Aj3Pj4Lj5Hj6Kj7ZTg06_Yj2<j3Nj4Jj5Fj6Rj76Tg001kj34Tg00GYj2QTg02DZj58Tg003kj10Tg03Zkj1CTg03[Pj1OTg01N<j2?Tg03Fmj3Xj1^Tg04MTj4Wj1\Tg019Ij27Tg00G7j23Tg06`_j1VTg00Pej1UTg00n=j1ITg01M_j22Tg02AFj2:Tg00ojj2;Tg01K;j3@Tg00Lej3=Tg00fXj1BTg03CYj8Tj2`Tg03H1j3Gj1bTg04N\j4Ej2STg03B4j8Mj2aTg03Daj2_Tg00>Oj6>Tg06agj1]Tg06boj1[Tg04Pjj4YTg00^=R2f3R3f2R4f1R5f0R6D8p=5g014BR7#9R8g005OR9g00]=R:%D8R;^32R<^=2R=^<:R>^E2R?]DR@%14RA/A61<6434RBX09P:P?%15g01\YRC'A1<C5P>APAC6ANC46P:P=%13RAPCP5P6CLPCP3P5P6CJP<f4RD#1REPCP4P5P6DHPCPDP4P5P6DFP;f5RF#1RGPCP3P4P5P6EKPCPFP3P4P5P6ERPCf6RHPDP3P4P5P6F6,Q;X92C5X82C5X7:D8X62C5X5:D8P:P?%05R?,AA1<?3P>%04R>=PE6AN>D6P:P=PG%03RGP5P6CLPGPFP5P6CJP<%1H%0DR<P4P5P6DHP<PHP4P5P6DFP;f7R<#1%0FRGP3P4P5P6EKPGP<P3P4P5P6ERP@f8RG,<Hg00OER=P;g03\KR>#C#C#C#ORE/?5R?P1P:P=f9RA#1RI?XFDRJg00OeRKP1%92RLP=PI%0CRC#0#0#0#0#0#0#0RMPFPDCWRNPKg00PEROn10110000021010200n10110000021010400'7P1P:P;P1P:%D:RPPJ13:6RQP1PLPPPN%V6#U,3:RN%I:RRn10110000021010300n10110000021010800P1P8P;P5PH12FERSPD123ERT1:4ERUO51;FD?@M5==76,38RV%I8RWn10110000021010500PWn10110000021010800P=P;%O>R>/?5RXg03EmRYP;p,4segsRZPIPFPDPCPO%B=RIg029\R[#BR\GTR]P0P[P;P5P1P8P;P3PG12<>R^PH12F>R_1:D>R`O51;<H?@C3==76,38RaPWn10110000021010500PWn10110700020020106102PWPWn011000003301081071012010710100%B7,38Rbn0100000020000n0100000020000P=P;P1P:P=AGAFDRcPKP1PLP=PMPAPFPDCERdPKPOn10110000021010200Ren10110000021010400,7?RfP1P:P;P1P:PPPcPQP1PLPPPdPNPRn10110000021010300Rdn10110000021010800P1P8P;PGf:RcPHPSPDPTPUF6PVPWn10110000021010500RVPWn10110000021010800RUP=P;PXPYP;PZPAPFPDPCPOPIP\GMP0P[P;P5P1P8P;Pcf<PGP^PHP_P`F6PaPWn10110000021010500PWn10110700020020106102RaPWPWn011000003301081071012010710100Pbn0100000020000n0100000020000R`54;X1@%DL^42^2:^09R@1S6AX09P=P;P1P:P=PJPKP1PLP=P6PMPFPDO3R_PKPOn10110000021010200n10110000021010400,7?P1P:P;P1P:PPPJPQP1PLPPP_PNPRn10110000021010300n10110000021010800PVPWn10110000021010800P=P;PXPYP;P]PaPWPWn011000003301081071012010710100Pbn0100000020000R]n0100000020000=4;`X1@PP^42^2:R@%bGP=P;P1P:P=P6PFPDO2R_PKPen10110000021010400,7?P1P:P;P1P:PPP_PQPdn10110000021010800PVPWn10110000021010800P]n0100000020000=4;`X1@%9=%9[PY];]@^F=^39^C2^B:R@1aZGP=P;PfPUP=P;PXPYP;P6PFPDPCPOPIP\O6PaPWPWn011000003301081071012010710100Pbn0100000020000n0100000020000=4;`XA@P=P;1?E6P1P:P=AGGD3R@PKP1PLP=PMPGPDP3CER`PKPOn10110000021010200n10110000021010400'7P1P:P;P1P:PPP@PQP1PLPPP`PNPRn10110000021010300n10110000021010800P1P8P;P<PAPF12DEP3124E1:5EF61;D3?@M5==76,38PWn10110000021010500PWn10110000021010800P=P;1?>6PYP;PZPGPDP3PCPOPIP\GMP0P[P;P5P1P8P;PAf;P<12H>PF12D>1:3>F61;HF?@C3==76,38PWn10110000021010500PWn10110700020020106102PWPWn011000003301081071012010710100Pbn0100000020000n0100000020000,Q;%1GRb,`Z1_GZE>%^b%]GE>%\b%[GE>1AbHPFE>Pb%0HRHPDP3P4P5P6FZPHPGPDP3P4P5P6F654;eX92C5X82C5X7:D8X62C5X5:D8X:BX>9P6CYW0W?o"). Qed.
Lemma copy_factsB_eqf : forall fk, copy_factsB (mkbc fk) = (fun fuel => copy_facts fuel fk).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h04fuelh12dbh22dkh32fkh41nh52sbh62skp;1p;2p;5g00A2j16Tg00FUj15Tg01`>j10Tg06^Rj11Tg06_Yj24Tg06d;j22Tg02DZj53Tg014B#6R0g005OR1g00]=R2g00^=R3%50^43^23^12]6]5f0R2#0#1f1R3,42X011232X01D3W3o"). Qed.
#[local] Hint Rewrite copy_factsB_eqf' copy_factsB_eqf : bceq.



(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kblob_prefix (k : list kentry) (sb : expr) (sk : Z) (db : expr) (dk : Z) (nlo : Z) : list kentry :=
  match List.find (fun K => match K with
                             | KBlob (SA b o) (ELit n0) _ => expr_eqb b sb && Z.eqb o sk && Z.ltb 0 n0 && Z.leb n0 nlo
                             | _ => false
                             end) k with
  | Some (KBlob _ (ELit n0) j) => [KBlob (SA db dk) (ELit n0) j]
  | _ => []
  end.

Definition summary_copy_ref (cs : acs) (entry : Z) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) entry) then None else
  match ret_lit cs with
  | Some ret =>
      let dst := reg cs 10 in let src := reg cs 11 in let ne := reg cs 12 in
      let '(db, dk) := split_lit dst in let '(sb, sk) := split_lit src in
      match xlo k ne, xhi k ne, xhi k dst, xhi k src with
      | Some nlo, Some nhi, Some dhi, Some shi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.ltb (dhi + nhi) two64 && Z.ltb (shi + nhi) two64)%bool then
            if Z.eqb nhi 0 then after_call cs ret (Some dst) k else
            match (if off_image_x k db dk ne then Some k
                   else match dst, ne with ELit d, ELit n => Some (kimg_cut k (d mod two64) n) | _, _ => None end) with
            | None => None
            | Some k0 =>
            if (kwritable_x k k db dk ne && ranges_apart_x k db dk ne sb sk ne)%bool then
              let k1 := kn_havoc k0 db dk ne in
              (* [comment removed for export] *)
              let nx := nxt cs in
              let words := if (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool then Z.to_nat (nhi / 8) else 0%nat in
              let kfresh := map (fun i => KWord (SA db (dk + 8 * Z.of_nat i)) 8 (EVar (nx + NCS + i)%nat)) (seq 0 words) in
              let havoc_src := if (kwritable_x k k sb sk ne && flat_x k sb sk ne)%bool
                               then after_call2 cs ret (Some dst) (kfresh ++ kblob_prefix k sb sk db dk nlo ++ (if Z.ltb 0 nlo then KUnk (SA db dk) ne :: k1 else k1)) words else None in
              if (Z.ltb 0 nlo && kzero_x k k sb sk ne)%bool then after_call cs ret (Some dst) (KZero (SA db dk) ne :: k1)
              else match ne with
                   | ELit _ =>
                       if (Z.leb nhi 2048 && flat_x k sb sk ne)%bool then
                         match copy_facts (Z.to_nat nhi) k sb sk db dk nhi with
                         | Some kc => after_call cs ret (Some dst) (kc ++ k1)
                         | None => havoc_src
                         end
                       else havoc_src
                   | _ => havoc_src
                   end
            else None
            end
          else None
      | _, _, _, _ => None
      end
  | None => None
  end.
(* [comment removed for export] *)
Definition summary_copy (cs : acs) (entry : Z) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  if negb (Z.eqb (pc cs) entry) then None else
  match ret_lit cs with
  | Some ret =>
      let dst := reg cs 10 in let src := reg cs 11 in let ne := reg cs 12 in
      let '(db, dk) := split_lit dst in let '(sb, sk) := split_lit src in
      match xloB bc ne, xhiB bc ne, xhiB bc dst, xhiB bc src with
      | Some nlo, Some nhi, Some dhi, Some shi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.ltb (dhi + nhi) two64 && Z.ltb (shi + nhi) two64)%bool then
            if Z.eqb nhi 0 then after_call cs ret (Some dst) k else
            match (if off_image_xB bc db dk ne then Some k
                   else match dst, ne with ELit d, ELit n => Some (kimg_cut k (d mod two64) n) | _, _ => None end) with
            | None => None
            | Some k0 =>
            if (kwritable_xB bc k db dk ne && ranges_apart_xB bc db dk ne sb sk ne)%bool then
              let k1 := kn_havocM k0 db dk ne in
              (* [comment removed for export] *)
              let nx := nxt cs in
              let words := if (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool then Z.to_nat (nhi / 8) else 0%nat in
              let kfresh := map (fun i => KWord (SA db (dk + 8 * Z.of_nat i)) 8 (EVar (nx + NCS + i)%nat)) (seq 0 words) in
              let havoc_src := if (kwritable_xB bc k sb sk ne && flat_xB bc sb sk ne)%bool
                               then after_call2 cs ret (Some dst) (kfresh ++ kblob_prefix k sb sk db dk nlo ++ (if Z.ltb 0 nlo then KUnk (SA db dk) ne :: k1 else k1)) words else None in
              if (Z.ltb 0 nlo && kzero_xB bc k sb sk ne)%bool then after_call cs ret (Some dst) (KZero (SA db dk) ne :: k1)
              else match ne with
                   | ELit _ =>
                       if (Z.leb nhi 2048 && flat_xB bc sb sk ne)%bool then
                         match copy_factsB bc (Z.to_nat nhi) sb sk db dk nhi with
                         | Some kc => after_call cs ret (Some dst) (kc ++ k1)
                         | None => havoc_src
                         end
                       else havoc_src
                   | _ => havoc_src
                   end
            else None
            end
          else None
      | _, _, _, _ => None
      end
  | None => None
  end.

Lemma summary_copy_eq : forall cs entry, summary_copy cs entry = summary_copy_ref cs entry.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bi001bh11ii011ih21oh34fuelh41kh51ni021nh62b1h72b2h82csh92dbi032dbh:2dki042dkh;1ei051eh<5entryh=2k1h>2k2i062k2h?1lh@2n1hA2n2hB3offhC2sbi072sbhD2ski082skhE2ubhF2ukhG2uni091ai0:1di0;3dhii0<3dsti0=2k0i0>2kci0?2loi0@2nei0A3nhii0B3nloi0C2opi0D3reti0E3shii0F2sxi0G1xi0H1zp%0p&0p;1p;2p;4p;3p;5p;7p;6g00A2k10@Tg00FUR0j1\Tg00i8j14Tg06_Yj2nj7cTg057cj1kTg03[nj2<Tg01NYj1eTg00n=j1aTg06UQj1`Tg01DAj21Tg01E@j1UTg003kj1TTg01`>j16Tg03K?j2jj1yTg03S\j2Kj1wTg01N<j2JTg03Zkj1FTg03[Pj1PTg040ck10=Tg04n`k20<Tg019Ij20Tg01M_j2MTg02Acj2@Tg06VTj45Tg03]0j4ij1tTg00G7j2NTg03C9j2VTg06WZj3bTg03QMj5>k100Tg02B@j7_j1uTg03V]j5^j1|Tg00ojj2ATg01O7j2]Tg02ncS00j48Tg03aCj4Dj1rTg06eGj1XTg01M?k10?Tg06egk20>Tg04o=j1RTg06fDj2:Tg00Roj1QTg01K;j3BTg06f[j2[Tg06g8j2ZTg06gTj6HTg01XUj2ITg03MCj2gj1~Tg03T\j2Gk102Tg03^8j4fk104Tg03RUj5=k10:Tg02@>j7dk103Tg03Waj5hk109Tg02kNS01j49Tg03bFj4Ck10;Tg001kj37Tg00GYj2}Tg00>Oj6;Tg03OAj1xTg03UYj1vTg02CKj1zTg06X^j1{Tg06LOj1sTg06Yjk101Tg05?_j1qTg06^Rk105k706Tg06h\j1pTg06igk207Tg06joj2oTg00Lek308Tg058aj3YTg006Sj4mTg06l;j5lTf0R1#T#Tp=O%F1#Fp=Lf2R2f1R3'0/01p=Wg00]=R4/N1p=?g014BR5@0831p=2AY531p=Sg005OR6P5P3P1Cmp=Ef6R7f5R8f4R9f3R:AY5235Y5P1Dlp=3g016FR;g00^=R<&0@5R5#\R=^5<^:<^94^D<^C4^36R>%42,n1X36%\;R?g00OER@P?%k2/<3#eRA%a;R;P0P<P?%`2RBg00bVRCP4P<P?g01\YRD#O#O#O#ORE#ORF,1:#URGPCP4P<P?%TFRH,18#URIP0P<P?f7RJ#4S02#6S03%THRK,1JRL'jRMP0P<P?f8RN#4RO#6S0411NKS05'KRPP0P<P?f9RQ#4RR#6S0611QFS07'KRSP0P<P?f:RT#4RU#6S0811THS09'KRVP@P?g02E\RW/J:g03\K#FRX#P&0=X#F#L#P+0<,J2'01M32g02F:RY'@1M12/@Y3WRZP@P?1<2WR[f;R\PN11\FR]#?S0:%4\R^C5R_P0P5P?P@P=%6^S0;PJP711\KR`Ci1N5^S0<P4P=P]P4P=f<R]/1KRaf=Rb#4Rc1V3YS0=;b1,N5%a5RYPYPYPYPYPYPYn0110@000810102101023010C1091003010C1091003010C1091003010C1091004010F10?1021054010F10=101102PYPYPYPYPYPYPYn0110<00081010:101023010C1091003010C1091003010C1091003010C1091004010F10?1021054010F10=101102S0>n0100000020000S0?P@P?%4]Rd#6RePdPNPJPaD>PePNPJPaP7P8PaF_Rf'0RgP@P?1@W9RhPePdP7P8PaD^'0S0@P]PQ11]F#?S0A1ANJS0B/]aRiP1PNPJPaC8'2C5RjP4P?PaP@P?%LXRX#F#L#LRk#F#L#P,J9Rl%6cRmPJP711bKRnCDRo'0P0P5P?P\%X9S0CPJP7PQPNP9O6f>RpP\11pF#?S0DP2PTPQ11pKRqC8,S1C5S0EP@P?PmPcPJP7PnD>S0F/0oPbPT11bF#?S0G%PXRX&0?1+0>Ro,MQ,ATS0H%Rpg06mBRm':/:1#Q7BEX16P@P61<891V9X/<W'0%PkRk,J9;Wh1[9X#XPDn0100000020000Rr,ZDS0I'ES0JPcPJP7PQPNP8EHS0KP@P51@W8S0L1AQNS0M/InRsP3PQPNPnC8Rt'2Ptn0100000020000PrF3S0NP;n0100000020100Rtn10110G00021010>01Ptn0100000020101PtP@P?f?Rt#4Ru#6S0OPuPQPN11tKRvD>S0PQ0OPQPNPvCD'0PtP]11tF#?S0Q1M\o,A]S0Rf@Rw#R/:m/:1#QS0S7BEX16P@P61<J71V7X/<W'01J7k1@W73W1[7X#XPDn0100000020000Rx,ZDS0T'ES0UPuPQPNP\PTPJEHS0VP@P51@WJRy1A\TS0W/IvRzP:P\PTPvC8R{'2P{n0100000020000PxF3S0XP;n0100000020100R{P{P{P{P@P?%4wR{#6R|P{PTPQ11wKR}D>S0YP|PTPQP}CD'0PwPb11wF#?S0Z1M]o,AbS0[fA#R/:m/:1#Q7BEX16P@P61<NJ1VJX/<W'01JJk;Wy1[JX#XPDn0100000020000RX,ZDS0\'ES0]P{PTPQP]P\PNEHS0^P@P51@WNS0_1A]\S0`/I}RWP9P]P\P}C8RD'2PDn0100000020000PXF3S0aP;n0100000020100RDPDn0110@00081110H111023110C1091003110C1091003110C1091003110C1091004110F10?1021054110F106101102n0100000020001P;n0100000020100P;n10110G00021110=00n0100000020001P;n0100000020100P;n10110G00021110E00P;n10110G00021110;00P;n10110G00021110A00P;n10110G00021110B00n200110G000121107108n200110G000121103104P;n10110G00021110D00n0100000020001P@P?PAP;P0P<P?PBPCP4P<P?PGPCP4P<P?PIP0P<P?Q02/gLS0bP0P<P?Q05,GOS0cP0P<P?Q07,GRS0dP0P<P?Q09,GUS0eP@P?PZP@P?P[P_P0P5P?P@P=P^PJP7P`CfQ0<Q0>n0100000020000S0fP@P?PdPdPNPJPaD=RDPdPNPJPaP7P8PaFd'0S0gP@P?PdPdP7P8PaDh,0hS0hP]PQQ0AP1PNPJPaC9,2iC5P4P?PaP@P?PcPJP7PnCCRk,0lS0iP0P5P?Q0CPcPJP7PQPNP9FcRoPpP\Q0DP2PTPQPqC9,S1C5P@P?PcPcPJP7PnD=/0kS0jPbPTQ0GQ0JQ0KP@P5Q0LP3PQPNPnC9R|,2sP|n0100000020000PrF3P;n0100000020100R|n10110G00021010>01P|n0100000020101P|P@P?PuPuPQPNPvD=PuPQPNPvCCS0k'0S0lPtP]Q0QQ0UQ0VP@P5PyP:P\PTPvC9R|,2zP|n0100000020000PxF3P;n0100000020100R|P|P|P|P@P?P{P{PTPQP}D=P{PTPQP}CCS0m'0S0nPwPbQ0ZQ0]Q0^P@P5Q0_P9P]P\P}C9R|,2WP|n0100000020000PXF3P;n0100000020100R|P|n0110@00081110H111023110C1091003110C1091003110C1091003110C1091004110F10?1021054110F106101102n0100000020001P;n0100000020100P;n10110G00021110=00n0100000020001P;n0100000020100P;n10110G00021110E00P;n10110G00021110;00P;n10110G00021110A00P;n10110G00021110B00n200110G000121107108n200110G000121103104P;n10110G00021110D00n0100000020001R|37X2>P@^54^B<^04R>%43R~$0;P@P?PAP;P0P<P?PBPCP4P<P?PGPCP4P<P?PIP0P<P?PMP0P<P?PPP0P<P?PSP0P<P?PVP@P?PZP@P?P[P_P0P5P?Q0?P@P?PgP@P?Q0@PjP4P?PaP@P?P\PJP7PnO3Rg,0lP0P5P?PoQ0EP@P?Q0F/0gQ0NP;n0100000020100Rgn10110G00021010>01Pgn0100000020101PgP@P?Q0PPbPQPNPvO3'0Q0XP;n0100000020100RgPgPgPgP@P?Q0YPpPTPQP}O3'0Q0aP;n0100000020100RgPgn0110@00081110H111023110C1091003110C1091003110C1091003110C1091004110F10?1021054110F106101102n0100000020001P;n0100000020100P;n10110G00021110=00n0100000020001P;n0100000020100P;n10110G00021110E00P;n10110G00021110;00P;n10110G00021110A00P;n10110G00021110B00n200110G000121107108n200110G000121103104P;n10110G00021110D00n0100000020001=7?|X0>P>^45Rg&0:~P@P?PAP;P0P<P?PBPCP4P<P?PGPCP4P<P?PIP0P<P?PMP0P<P?PPP0P<P?PSP0P<P?PVP@P?PZP@P?P[P_P0P5P?Q0?P@P?PTPdPNPJPaO4/0fP@P?Q0@PjP4P?PaP@P?Q0iP0P5P?PoQ0EP@P?P\PcPJP7PnO4/0kQ0NP;n0100000020100Rkn10110G00021010>01Pkn0100000020101PkP@P?PbPuPQPNPvO4Q0k'0Q0XP;n0100000020100RkPkPkPkP@P?PpP{PTPQP}O4Q0m'0Q0aP;n0100000020100R{P{n0110@00081110H111023110C1091003110C1091003110C1091003110C1091004110F10?1021054110F106101102n0100000020001P;n0100000020100P;n10110G00021110=00n0100000020001P;n0100000020100P;n10110G00021110E00P;n10110G00021110;00P;n10110G00021110A00P;n10110G00021110B00n200110G000121107108n200110G000121103104P;n10110G00021110D00n0100000020001=7?|X0gPg&09~P@P?PAP;P0P<P?PBPCP4P<P?PGPCP4P<P?PIP0P<P?PMP0P<P?PPP0P<P?PSP0P<P?PVP@P?PZP@P?P[P_P0P5P?Q0?P@P?10DfRfP@P?PTPdP7P8PaO4,0hPjP4P?PaP@P?Q0iP0P5P?PoQ0EP@P?Q0jQ0NP;n0100000020100R{n10110G00021010>01P{n0100000020101P{P@P?Q0lQ0XP;n0100000020100R{P{P{P{P@P?Q0nQ0aP;n0100000020100R{P{n0110@00081110H111023110C1091003110C1091003110C1091003110C1091004110F10?1021054110F106101102R{n0100000020001P;n0100000020100P;n10110G00021110=00n0100000020001P;n0100000020100P;n10110G00021110E00P;n10110G00021110;00P;n10110G00021110A00P;n10110G00021110B00n200110G000121107108n200110G000121103104P;n10110G00021110D00n0100000020001=7?|X0gP>&04~P@P?PAP;P0P<P?PBPCP4P<P?PGPCP4P<P?PIP0P<P?PMP0P<P?PPP0P<P?PSP0P<P?PVP@P?PZP@P?P[P_P0P5P?P@P=PQPJP7P`O3Q0<Q0>n0100000020000P@P?PfP@P?Q0hPjP{n0100000020001R{P;n0100000020100P;n10110G00021110=00n0100000020001P;n0100000020100P;n10110G00021110E00P;n10110G00021110;00P;n10110G00021110A00P;n10110G00021110B00n200110G000121107108n200110G000121103104P;n10110G00021110D00n0100000020001=7?|X0>P@^A4^><^74^@4^=<^64R>&03~P@P?PAP;P0P<P?PBPCP4P<P?PGPCP4P<P?PIP0P<P?PMP0P<P?PPP0P<P?PSP0P<P?PVP@P?PZP@P?P[P_P0P5P?Q0fP@P?PTPNPJPaP7P8PaO6,0DP{P;n0100000020100P;n10110G00021110=00n0100000020001P;n0100000020100P;n10110G00021110E00P;n10110G00021110;00P;n10110G00021110A00P;n10110G00021110B00n200110G000121107108n200110G000121103104P;n10110G00021110D00n0100000020001=7?|X0>%\<^;4R>&02~P@P?PAP;P0P<P?PBPCP4P<P?PGPCP4P<P?PIP0P<P?PMP0P<P?P7Q05O1P0P<P?PJQ07O1P0P<P?PNQ09O1P@P?PZP@P?P[P_P0P5P?Q0fP@P?Q0gP{P;n0100000020100P;n10110G00021110=00n0100000020001P;n0100000020100R{P;n10110G00021110E00P;n10110G00021110;00P;n10110G00021110A00P;n10110G00021110B00n200110G000121107108n200110G000121103104P;n10110G00021110D00n0100000020001=7?|X2>P>%~~P@P?PAP;P0P<P?PBPCP4P<P?PGPCP4P<P?PIP0P<P?P8PLO1P0P<P?Q0cP0P<P?Q0dP0P<P?Q0eP{P;n10110G00021110E00P;n10110G00021110;00P;n10110G00021110A00P;n10110G00021110B00n200110G000121107108n200110G000121103104P;n10110G00021110D00n0100000020001=7?|X2>P5^G4^F<^E4^45R>Q01P@P?PAP;P0P<P?PBPCP4P<P?PGPCP4P<P?PIP0P<P?Q0bP0P<P?Q0cP0P<P?Q0dP0P<P?Q0eP@P?PZP@P?P[P_P0P5P?Q0fP@P?Q0gP@P?Q0hP]PQQ0APTP1PNPJPaO4,2iC5P4P?PaP@P?Q0iP0P5P?PoPpP\Q0DP]P2PTPQPqO4,S1C5P@P?Q0jPbPTQ0GQ0JQ0KP@P5Q0LP\P3PQPNPnO4Ro,2sPon0100000020000PrF3P;n0100000020100Ron10110G00021010>01Pon0100000020101PoP@P?Q0lPtP]Q0QQ0UQ0VP@P5PyPbP:P\PTPvO4Ro,2zPon0100000020000PxF3P;n0100000020100RoPoPoPoP@P?Q0nPwPbQ0ZQ0]Q0^P@P5Q0_PpP9P]P\P}O4R},2WP}n0100000020000PXF3P;n0100000020100R}P}n0110@00081110H111023110C1091003110C1091003110C1091003110C1091004110F10?1021054110F106101102n0100000020001P;n0100000020100P;n10110G00021110=00n0100000020001P;n0100000020100P;n10110G00021110E00P;n10110G00021110;00P;n10110G00021110A00P;n10110G00021110B00n200110G000121107108n200110G000121103104P;n10110G00021110D00n0100000020001=7?|X?>P@P?%k3/<1#eR>P;P0P<P?%`3R|PCP4P<P?112F#UR}PCP4P<P?119H#URWP0P<P?%47Rw117KRo'gP0P<P?Q02/GLP0P<P?11NFRz,GOP0P<P?11QHRH,GRP@P?PZP@P?P[PTPN11TFRF#?PUC5RRP0P5P?P@P=PUPJP711TKRKCf1N5URUP4P=PFP4P=P`Q0==bd1,N5PYPYPYPYPYPYPYn0110@000810102101023010C1091003010C1091003010C1091003010C1091004010F10?1021054010F10=101102PYPYPYPYPYPYPYn0110<00081010:101023010C1091003010C1091003010C1091003010C1091004010F10?1021054010F10=101102RYn0100000020000P@P?P^P^PNPJP`D=P^PNPJP`P7P8P`Fd'0P@P?P^P^P7P8P`Dh,0hP\PQQ0:Q0B/]`RFP1PNPJP`C9'2C5P4P?P`P@P?PdPJP7PaCCRO,0lP0P5P?Q0CPdPJP7PQPNP9FcPbP\Q0GP2PTPQPnC9,S1C5P@P?PdPdPJP7PaD=/0OP]PTQ0AQ0H%Rb/:m/:1#Q7BEX16Q0I'EROPdPJP7PQPNP8EHRsP@P5Q0LQ0M/IaRiP3PQPNPaC9R_'2P_n0100000020000PrF3P;n0100000020100R_n10110G00021010>01P_n0100000020101P_P@P?%4pR_P_PQPNPqD=P_PQPNPqCC'0PpP]Q0DQ0R%Rt/:m/:1#Q7BEX16Q0T'ERmP_PQPNP\PTPJEHRIP@P5PyQ0W/IqRGP:P\PTPqC9RB'2PBn0100000020000PxF3P;n0100000020100RBPBPBPBP@P?PuPuPTPQPvD=PuPTPQPvCC'0PtPbQ0QQ0[Q0S7BEX16Q0\'ER6PuPTPQP]P\PNEHREP@P5Q0_Q0`/IvRBP9P]P\PvC9RA'2PAn0100000020000PXF3P;n0100000020100RAPAn0110@00081110H111023110C1091003110C1091003110C1091003110C1091004110F10?1021054110F106101102n0100000020001P;n0100000020100P;n10110G00021110=00n0100000020001P;n0100000020100P;n10110G00021110E00P;n10110G00021110;00P;n10110G00021110A00P;n10110G00021110B00n200110G000121107108n200110G000121103104P;n10110G00021110D00n0100000020001RA,}?Q00g06]JE;%6~R{#y%x~E;%w{%v~E;%u{%z~E;%t{%{~E;%|{%s~E;&00{&01~E;%r{%q~E;&05{%p~E;P@P?P>P;P0P<P?P|PCP4P<P?P}PCP4P<P?PWP0P<P?%6w/joP0P<P?Q03/KLP0P<P?Q04/KzP0P<P?Q06/KHP@P?PZP@P?P[PRP0P5P?P@P=Q08PJP7PKCiPUPYn0100000020000P@P?Q0;P^PNPJP`D>Q0;PNPJP`P7P8P`F_'0P@P?Q0;P^P7P8P`D^,0hP\PQQ0:P1PNPJP`C8,2FC5P4P?P`P@P?PePJP7PaCDR`,0lP0P5P?PeQ0CPJP7PQPNP9K06PbP\Q0GP2PTPQPnC8,S1C5P@P?PePdPJP7PaD>/0`P]PTQ0APOPsP@P5Q0LP3PQPNPaC8Ra,2iPan0100000020000PrF3P;n0100000020100Rrn10110G00021010>01Prn0100000020101PrP@P?%6_RrP_PQPNPqD>PrPQPNPqCD'0PpP]Q0DPmPIP@P5PyP:P\PTPqC8Rq,2GPqn0100000020000PxF3P;n0100000020100RxPxPxPxP@P?Q0OPuPTPQPvD>Q0OPTPQPvCD'0PtPbQ0QP6PEP@P5Q0_P9P]P\PvC8Rv,2BPvn0100000020000PXF3P;n0100000020100RXPXn0110@00081110H111023110C1091003110C1091003110C1091003110C1091004110F10?1021054110F106101102n0100000020001P;n0100000020100P;n10110G00021110=00n0100000020001P;n0100000020100P;n10110G00021110E00P;n10110G00021110;00P;n10110G00021110A00P;n10110G00021110B00n200110G000121107108n200110G000121103104P;n10110G00021110D00n0100000020001=7?Ae207311o3157?eW<W8o"). Qed.


(* [comment removed for export] *)
Definition summary_miz_ref (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (x_memiszero A)) then None else
  match ret_lit cs with
  | Some ret =>
      let beg := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
      let '(bb, bk) := split_lit beg in
      let spm := eaddz sp (-16) in let '(qb, qk) := split_lit spm in
      match xlo k ne, xhi k ne, xhi k beg, xlo k sp, xhi k sp with
      | Some nlo, Some nhi, Some bhi, Some splo, Some sphi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.leb (bhi + nhi + 8) two64
              && Z.leb 16 splo && Z.ltb sphi two64
              && kwritable k k qb qk 16
              && ranges_apart_x k qb qk (ELit 16) bb bk ne && kzero_x k k bb bk ne)%bool
          then after_call cs ret (Some (ELit 1)) (kn_havoc k qb qk (ELit 16))
          else None
      | _, _, _, _, _ => None
      end
  | None => None
  end.
(* [comment removed for export] *)
Definition summary_miz (cs : acs) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  if negb (Z.eqb (pc cs) (x_memiszero A)) then None else
  match ret_lit cs with
  | Some ret =>
      let beg := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
      let '(bb, bk) := split_lit beg in
      let spm := eaddz sp (-16) in let '(qb, qk) := split_lit spm in
      match xloB bc ne, xhiB bc ne, xhiB bc beg, xloB bc sp, xhiB bc sp with
      | Some nlo, Some nhi, Some bhi, Some splo, Some sphi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.leb (bhi + nhi + 8) two64
              && Z.leb 16 splo && Z.ltb sphi two64
              && kwritableB bc k qb qk 16
              && ranges_apart_xB bc qb qk (ELit 16) bb bk ne && kzero_xB bc k bb bk ne)%bool
          then after_call cs ret (Some (ELit 1)) (kn_havocB bc qb qk (ELit 16))
          else None
      | _, _, _, _, _ => None
      end
  | None => None
  end.

Lemma summary_miz_eq : forall cs, summary_miz cs = summary_miz_ref cs.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bh11kh21nh31oh43offh52b1h62b2h72csh81eh92k1h:2k2h;1lh<2n1h=2n2h>2ubh?2ukh@2uni002bbi013bhii022bki033nhii043nloi052qbi062qki073reti084sphii094sploi0:1xp;1p;2p;5p;7p;4p;3p;6g00A2j1nTg00i8j14Tg02kNj1Vj4KTg00FUR0j1ETg057cj1PTg06nAj1]Tg03[nj2OTg01NYj1MTg00n=j1STg06UQj1FTg01DAj20Tg01E@j1<Tg03Zkj16Tg06oHj1kTg06ofj2NTg01`>j12Tg003kj1ATg03K?j2?j1bTg03S\j28j1\Tg01N<j2=Tg03[Pj1:Tg040cj1UTg04n`j2TTg01M_j2HTg02Acj2RTg03I4j5Gj1dTg019Ij25Tg00Pej1ITg02B@j7Jj1[Tg03V]j5Dj1aTg00G7j2QTg06VTj4@Tg03MCj2>j1fTg03T\j27j1hTg03J:j5Cj1mTg02@>j7Bj1jTg03Waj5Lj1lTg001kj33Tg00GYj2cTg03OAj1_Tg00>Oj69Tg03UYj1^Tg02CKj1`Tg06LOj1ZTg070gj1eTg02jIj1Yj4gTg02mZj1XTg0721j1WTg0738j1iTf0R1#A#Ap=;f2R2f1R3'5/51p=1g016FR4g00]=R5g00^=R6g014B#nR7^@5]?]>R8%41R9#V%E4R:g00OER;P:%P3p,1A#]R<'O#MR=%S4R4P0P6P:%F3R>g00bVR?P5P6P:g01\Y#;R@#;#;#;#;RA,02#<RBP?P5P6P:f4RC/0@g03\KRD#6RE#6#6RF#6RG#kRH'N#<RIP0P6P:f6RJ#4RK#2RL%AARM,0JRN'?ROP0P6P:f7RP#4RQ#2RR10PMRS'8RTP0P6P:f8RU#4RV#2RW10UARX'8RYP0P6P:f9RZ#4R[#2R\10Z@R]'?R^P0P6P:f:R_#4R`#2Ra10_@Rb'8RcP;P:g02E\/=Cf3RC%:E%UE#6#6#6#:'T'=1H2C%:F'Hg02F:RF'=31%:GRG/=31R1F31RFf;R2#4RE#2RdPEPJf5RePGDG'5PdPJPe%IGRfPUPP102MRgFJRhPdPEPUPPPgDDRd31P2PZ%:D#I,Q5RDP_PJPePfO3C@P4n0100000020000P4n10110:00021010800P4n10110:00021010900P4n10110:00021010100P4n10110:00021110300P4n10110:00021110400n200110:000121105106n200110:000121100102P4n10110:00021110700n0100000020001P;P:P=P4P0P6P:P>P?P5P6P:PBP?P5P6P:PIP0P6P:1>KNP0P6P:17QSRiP0P6P:17VXRjP0P6P:1>[]P0P6P:17`bP;P:PEPEPJPePGDC,5FRkPEPJPePfPUPPPgFBPEPEPUPPPgDLRl31P2PZPDPEPJPePfCKC@R2P4n0100000020000RmP4n10110:00021010800RnP4n10110:00021010900P4n10110:00021010100P4n10110:00021010300P4n10110:00021110400n200110:000121105106n200110:000121100102P4n10110:00021110700n0100000020001Ro33X;8P;^26^46^05^17R8%m9P;P:P=P4P0P6P:P>P?P5P6P:PBP?P5P6P:PIP0P6P:POP0P6P:PTP0P6P:PYP0P6P:P^P0P6P:PcP;P:P_PEPJPePGO4,5F?1hdP2P4n0100000020000P4n10110:00021010800P4n10110:00021010900P4n10110:00021010100P4n10110:00021110300P4n10110:00021110400n200110:000121105106n200110:000121100102P4n10110:00021110700n0100000020001=3:oX08P;^25^46^05^17R7%l9P;P:P=P4P0P6P:P>P?P5P6P:PBP?P5P6P:PIP0P6P:POP0P6P:PTP0P6P:PYP0P6P:P^P0P6P:PcP;P:P_PEPUPPPgO491khP2P4n0100000020000P4n10110:00021010800P4n10110:00021010900P4n10110:00021010100P4n10110:00021110300P4n10110:00021110400n200110:000121105106n200110:000121100102P4n10110:00021110700n0100000020001=3:oX07P;^=5^:6^65^<5^96^55R7%j9P;P:P=P4P0P6P:P>P?P5P6P:PBP?P5P6P:PIP0P6P:POP0P6P:PTP0P6P:PYP0P6P:P^P0P6P:PcP;P:P_PJPePfPUPPPgO6=1klP2P4n0100000020000P4n10110:00021010800P4n10110:00021010900P4n10110:00021010100P4n10110:00021110300P4n10110:00021110400n200110:000121105106n200110:000121100102P4n10110:00021110700n0100000020001=3:oX07%E6^85R7%h9P;P:P=P4P0P6P:P>P?P5P6P:PBP?P5P6P:PIP0P6P:POP0P6P:PJPSO1P0P6P:PPPXO1P0P6P:P^P0P6P:PZPbO1PmP4n10110:00021010800P4n10110:00021010900P4n10110:00021010100P4n10110:00021010300P4n10110:00021110400n200110:000121105106n200110:000121100102P4n10110:00021110700n0100000020001=3:oX37P7%f9P;P:P=P4P0P6P:P>P?P5P6P:PBP?P5P6P:PIP0P6P:PePNO1P0P6P:PiP0P6P:PjP0P6P:PUP]O1PnP4n10110:00021010900P4n10110:00021010100P4n10110:00021010300P4n10110:00021110400n200110:000121105106n200110:000121100102P4n10110:00021110700n0100000020001=3:oX37P;P:%P1/O<#MR<P4P0P6P:%F1R7P?P5P6P:103A#<R3P?P5P6P:10C@/NH#<RHP0P6P:%4eRC10eMRo'>P0P6P:17KNP0P6P:10PARA,7QP0P6P:10U@R@,>VP0P6P:17[]P;P:P`P`PJPePGDC,5FP`PJPePfPUPP10_MRMFBP`P`PUPPPMDL31P_PZPDP`PJPePfCKC@P4n0100000020000P4n10110:00021010800P4n10110:00021010900P4n10110:00021010100P4n10110:00021010300P4n10110:00021110400n200110:000121105106n200110:000121100102P4n10110:00021110700n0100000020001R[,c:%29RV#b%_9E9%\V%^9E9%[V%`9E9%aV%Z9E9%dV%e9E9%YV%X9E9P;P:P<P4P0P6P:P7P?P5P6P:P3P?P5P6P:PHP0P6P:%2C/?oP0P6P:18LNP0P6P:18RAP0P6P:1?W@P0P6P:18\]P;P:PaP`PJPePGDG,5FPaPJPePfPUPPPMFJPaP`PUPPPMDD31P_PZPDPaPJPePfCgC@P4n0100000020000P4n10110:00021010800P4n10110:00021010900P4n10110:00021010100P4n10110:00021110300P4n10110:00021110400n200110:000121105106n200110:000121100102P4n10110:00021110700n0100000020001=3:[e%W1%i153:eW7o"). Qed.


(* [comment removed for export] *)
Definition img_cov (k : list kentry) (a b : Z) : bool :=
  existsb (fun K => match K with KImg lo hi => Z.leb lo a && Z.leb b hi | _ => false end) k.

Definition img_covB (bc : bctx) (a b : Z) : bool :=
  existsb (fun K => match K with KImg lo hi => Z.leb lo a && Z.leb b hi | _ => false end) (bc_fk bc).
Lemma img_covB_eqf : forall fk, img_covB (mkbc fk) = img_cov fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01Ki001Kh11bh22fkh31lh41xh52x0i012a0i022a1i032a2i041ci051ei062hii071ki082k0i092loi0:1mi0;1ni0<2n1i0=2n2i0>1vi0?1wp;1p;2p;3p;6p;5g00A2j1@Tg01`>j12Tg074Cj17j2?j3=Tg075Gj16j2;j3<Tg01N<j20Tg019Ij23Tg008Ij31Tg001kj34Tg00GYj28Tg02REj19Tg02THj1:Tg00>Oj6>Tg02DZj55Tg014BR0#@R1g00^=R2g00OER3^12f0R4#2#7%64P2P3f1R5#2/?41;54P1f2R6P0P3P4g00PER7P7P7f5,05f4R8/04'3R9P7P7P7P7P7P7n01100000:3010110?10>2010110;3010110;107201091062010510:301051091062010110;4010210<10310=3010110;1042010110;X00=104P0P3P4P7P7P7P9P7P7P7P7P7P7n01100000:3010110?10>2010110;3010110;108201091062010510:301051091062010110;4010210<10310=3010110;1042010110;X00f3R9510543X31P0P3P4P7P7P710581094'3P7P7P7P7P7P7n01100000:3010110?10>2010110;3010110;108201091062010510:301051091062010110;4010210<10310=3010110;1042010110;X00=106,83%26R0#9%:6E>A=054A<654543eX52D5X42D5W2o"). Qed.
#[local] Hint Rewrite img_covB_eqf : bceq.



(* [comment removed for export] *)
Definition SEALED_W : Z := 0x3e64656c6165733c.

(* [comment removed for export] *)
Definition summary_istrncpy_ref (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (x_istrncpy A)) then None else
  match ret_lit cs, reg_lit cs 11, reg_lit cs 12 with
  | Some ret, Some src, Some n =>
      if negb (Z.eqb src (x_sealed A) && Z.eqb n 4095)%bool then None else
      let dst := reg cs 10 in
      let '(db, dk) := split_lit dst in
      match xhi k dst with
      | Some dhi =>
          match (if off_image_x k db dk (ELit 4095) then Some k
                 else match dst with ELit d => Some (kimg_cut k (d mod two64) 4095) | _ => None end) with
          | None => None
          | Some k0 =>
              if (Z.ltb (dhi + 4095) two64 && Z.leb 0 (x_sealed A) && Z.ltb (x_sealed A + 9) two64
                  && kwritable_x k k db dk (ELit 4095) && img_cov k0 (x_sealed A) (x_sealed A + 9)
                  && ranges_apart_x k db dk (ELit 4095) (ELit 0) (x_sealed A) (ELit 9))%bool then
                after_call cs ret (Some dst)
                  (KWord (SA db dk) 8 (ELit SEALED_W) :: KZero (SA db (dk + 8)) (ELit 4087) :: kn_havoc k0 db dk (ELit 4095))
              else None
          end
      | None => None
      end
  | _, _, _ => None
  end.
(* [comment removed for export] *)
Definition summary_istrncpy (cs : acs) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  if negb (Z.eqb (pc cs) (x_istrncpy A)) then None else
  match ret_lit cs, reg_lit cs 11, reg_lit cs 12 with
  | Some ret, Some src, Some n =>
      if negb (Z.eqb src (x_sealed A) && Z.eqb n 4095)%bool then None else
      let dst := reg cs 10 in
      let '(db, dk) := split_lit dst in
      match xhiB bc dst with
      | Some dhi =>
          match (if off_image_xB bc db dk (ELit 4095) then Some k
                 else match dst with ELit d => Some (kimg_cut k (d mod two64) 4095) | _ => None end) with
          | None => None
          | Some k0 =>
              if (Z.ltb (dhi + 4095) two64 && Z.leb 0 (x_sealed A) && Z.ltb (x_sealed A + 9) two64
                  && kwritable_xB bc k db dk (ELit 4095) && img_cov k0 (x_sealed A) (x_sealed A + 9)
                  && ranges_apart_xB bc db dk (ELit 4095) (ELit 0) (x_sealed A) (ELit 9))%bool then
                after_call cs ret (Some dst)
                  (KWord (SA db dk) 8 (ELit SEALED_W) :: KZero (SA db (dk + 8)) (ELit 4087) :: kn_havocM k0 db dk (ELit 4095))
              else None
          end
      | None => None
      end
  | _, _, _ => None
  end.

Lemma summary_istrncpy_eq : forall cs, summary_istrncpy cs = summary_istrncpy_ref cs.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bi001bh11kh22b1h32b2h42csh51ei011eh62k1h72k2h81lh91ni021nh:2n1h;2n2h<1oh=3offh>2ubh?2ukh@2uni031ai041di052dbi063dhii072dki083dsti091ii0:2k0i0;2loi0<2n0i0=2opi0>3reti0?3srci0@2sxi0A1xp;1p;2p;4p;3p;7p;5p;6g00A2j1nTg00i8j18Tg03RUj1Zj5ITg00FUR0j1CTg057cj1STg076Jj1dTg03[nj2@Tg01NYj1ETg00n=j1LTg06UQj1JTg003kj1BTg05GIj2>Tg077Pj1mTg040cj16Tg03[Pj1ATg019Ij20Tg01DAj25Tg01E@j1OTg01`>j1:Tg03S\j2Nj1bTg00Pej19Tg03]0j4Mj1^Tg00G7j24Tg03C9j2YTg06WZj3KTg01M_j2DTg02Acj2HTg01N<j2XTg03Zkj1?Tg075Gj3WTg02B@j7Gj1`Tg00ojj2FTg01K;j3VTg01O7j2UTg02ncR1j4TTg06VTj4=Tg03T\j2Rj1hTg03^8j4Qj1kTg02@>j7Pj1jTg02kNR2j4lTg001kj31Tg00GYj2cTg00>Oj67Tg03UYj1_Tg02CKj1aTg06X^j1eTg03QMj1fj5\Tg06Yjj1]Tg078Tj1gTg079`j1[Tg00Lej3iTf0R3#B#Bp=;%63#6p=3f2R4f1R5'0/03p=<g014BR6?i53p=2g016FR7%n6R6g00]=R8g00^=R9g00OER:^98]=]0R;]1R<%83R=#Z%C7R>P:P>%S5p,1AR?#dR@'@#ERA%L7R7P0P9P>%J5RBP0P9P>g01\Y#;#;#;#;RC#;RD#BRE,>4RFP0P9P>f3RG%BERH'>RIP:P>%m?R?,@5g03\KRJ#6#3#3#3RK#3#3#ARL,@3'0#ERMP7g00bVRNP8P9P>f4/5D#OROP0P9P>f6RP#8RQ#:RR15PDRS'NRTP0P6P>P:%C6RUf7RV#8RW#:RXP4P5%9LRYCM146WRZP8PU15VDR[f8R\#8R]g02F:R^,Y3R_;KL,46%L6R`P`P`P`P`P`P`n011080008101041010<3010=1031003010=1031003010=1031003010=1031004010@10;10<1014010@10:10910<Ran0100000020000P:P>1D5L/H^g02E\Rb/X?%?J#?RJ#6#ARc,D?Rd/H^3<R^PVP]PGP4PYO4'0AW3?dRd%:]PGP4PY%9bRbP?%9cRcFGRe3<P\PP15\D,48Rf1FG4g07;0#97VCRC%?J#A,D4,FG%?K#6#3#A#9'URKP3PGP4PYCT'2'2RJC=RgP7n0100000020000P7n10110A00021110:00P7n10110A00021110600n200110A000121105107n0100000020001P7n10110A00021110200P7n10110A00021110?00P7n10110A00021110>00n0100000020001P:P>PAP7P0P9P>PBP0P9P>PFP0P9P>PIP:P>PMP7PNP8P9P>POP0P9P>1RQSRhP0P6P>P:PUPWP4P5PYCQPZPan0100000020000RiP:P>P]P]PGP4PYDI=<^dRjP]PGP4PYPbP?PcFP'0R]P\PPPfP3PGP4PYCl,2K,2CRkC=P7n0100000020000P7n10110A00021110:00P7n10110A00021110600n200110A000121105107n0100000020001P7n10110A00021110200P7n10110A00021110?00P7n10110A00021110>00n0100000020001Rl31X0<P;%k=P:P>PAP7P0P9P>PBP0P9P>PFP0P9P>PIP:P>PMP7PNP8P9P>POP0P9P>PTP0P6P>P:PUPPP4P5PYO3PZPan0100000020000P:P>10jePgP7n0100000020000P7n10110A00021110:00P7n10110A00021110600n200110A000121105107n0100000020001P7n10110A00021110200P7n10110A00021110?00P7n10110A00021110>00n0100000020001=1>lX0;P:^;8^79^38^:8^69^28R;%j=P:P>PAP7P0P9P>PBP0P9P>PFP0P9P>PIP:P>PMP7PNP8P9P>POP0P9P>PTP0P6P>PiP:P>PVPGP4PYPbP?PcO6,0jPgP7n0100000020000P7n10110A00021110:00P7n10110A00021110600n200110A000121105107n0100000020001P7n10110A00021110200P7n10110A00021110?00P7n10110A00021110>00n0100000020001=1>lX0;%C9^58R;%h=P:P>PAP7P0P9P>PBP0P9P>PFP0P9P>PIP:P>PMP7PNP8P9P>POP0P9P>f5RjPSO1P0P6P>PiP:P>P]PgP7n0100000020000P7n10110A00021110:00P7n10110A00021110600n200110A000121105107n0100000020001P7n10110A00021110200P7n10110A00021110?00P7n10110A00021110>00n0100000020001=1>lX<;P6^@8^?9^>8^16R;P2P:P>PAP7P0P9P>PBP0P9P>PFP0P9P>PIP:P>PMP7PNP8P9P>POP0P9P>PhP0P6P>PiP:P>P]P\PPPfPVP3PGP4PYO4,2K,2CC=P7n0100000020000P7n10110A00021110:00P7n10110A00021110600n200110A000121105107n0100000020001P7n10110A00021110200P7n10110A00021110?00P7n10110A00021110>00n0100000020001=1>lX8;P:P>%S3/@@#ER@P7P0P9P>%J3R;P0P9P>1>5EREP0P9P>1>4HRHP:P>PMP7PNP8P9P>15GD#ORlP0P9P>%8jRC15jDRj'RP0P6P>P:PUPQP4P5PYCQ146QRQP8PUPSAKW_L,46P`P`P`P`P`P`P`n011080008101041010<3010=1031003010=1031003010=1031003010=1031004010@10;10<1014010@10:10910<R`n0100000020000P:P>PWPWPGP4PYDI,0^PWPGP4PYPbP?PcFP7<dPVPP148[R[PkC=P7n0100000020000P7n10110A00021110:00P7n10110A00021110600n200110A000121105107n0100000020001P7n10110A00021110200P7n10110A00021110?00P7n10110A00021110>00n0100000020001Rk,c>P1g06]JE7%:=R1#b%_=E7%`1%a=E7%^1%e=E7%f1%]=E7P:P>P@P7P0P9P>P;P0P9P>PEP0P9P>PHP:P>PMP7PNP8P9P>PlP0P9P>%:C/NjP0P6P>P:PUPRP4P5PYCMPQP`n0100000020000P:P>PXPWPGP4PYD\,0^PXPGP4PYPbP?PcFG7<dPVPPP[PJC=P7n0100000020000P7n10110A00021110:00P7n10110A00021110600n200110A000121105107n0100000020001P7n10110A00021110200P7n10110A00021110?00P7n10110A00021110>00n0100000020001=1>ke%g3%[351>eW4o"). Qed.


(* [comment removed for export] *)
Definition popfree_facts (lb : expr) (lk : Z) (cnt c s : Z) (K : nat) : list kentry :=
  map (fun t => KWord (SA lb (lk + 4 * (cnt - 1 - Z.of_nat t))) 4 (ELit ((c + Z.of_nat t * s) / 16))) (seq 0 K).
Definition summary_popfree (cs : acs) (args : list expr) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (x_popfree A)) then None else
  match args, reg_lit cs 10, reg_lit cs 12, reg_lit cs 21, reg_lit cs 19 with
  | [ELit K], Some i, Some c, Some s, Some n =>
      let e := reg cs 11 in
      let cnt := n - i in
      let lo := eaddz e (- (4 * n)) in
      let '(lb, lk) := split_lit lo in
      match xlo k e, xhi k e with
      | Some el, Some eh =>
          if (Z.leb 0 i && Z.ltb i n && Z.leb (4 * n) el && Z.ltb eh two64 && Z.leb 0 c && Z.leb 0 s
              && Z.ltb (c + cnt * s) two64 && Z.leb 0 K && Z.leb K cnt && Z.ltb (pc cs + 32) two64
              && fresh_ok cs && kwritable_x k k lb lk (ELit (4 * cnt)) && off_image_x k lb lk (ELit (4 * cnt)))%bool then
            let k1 := kn_havoc k lb lk (ELit (4 * cnt)) in
            let kunk := if Z.ltb K cnt then [KUnk (SA lb lk) (ELit (4 * (cnt - K)))] else [] in
            let sr := s_regs (a_ss cs) in
            let sr' := sr_upd (sr_upd (sr_upd (sr_upd sr 10 (ELit n)) 12 (ELit (c + cnt * s)))
                                      14 (ELit ((c + (cnt - 1) * s) / 16))) 15 lo in
            Some (with_ss cs (mk_ss (pc cs + 32) sr' (popfree_facts lb lk cnt c s (Z.to_nat K) ++ kunk ++ k1) (nxt cs)))
          else None
      | _, _ => None
      end
  | _, _, _, _, _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kn_readable_x (k : list kentry) (rb : expr) (rk : Z) (ne : expr) : bool :=
  existsb (fun K => match K with
                    | KUnk (SA kb kk) len | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
                        xinside k rb rk ne kb kk len
                    | _ => false
                    end) k.

Definition summary_sniff_ref (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (x_sniff A)) then None else
  match ret_lit cs with
  | Some ret =>
    let buf := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
    let '(bb, bk) := split_lit buf in
    let '(qb, qk) := split_lit (eaddz sp (-8)) in
    match xhi k ne, xhi k buf, xlo k sp, xhi k sp with
    | Some nhi, Some bhi, Some splo, Some sphi =>
      let m := Z.min nhi 8 in
      if (Z.ltb (bhi + 8) two64 && Z.leb 32 splo && Z.ltb sphi two64 && Z.leb (sniff_tab A + 16 + 8) splo
          && flat_x k qb qk (ELit 8) && kwritable k k qb qk 8
          && flat_x k bb bk (ELit 8)
          && ranges_apart_x k qb qk (ELit 8) bb bk (ELit 8)
          && ranges_apart_x k qb qk (ELit 8) (ELit 0) (sniff_cell A) (ELit 8)
          && (Z.eqb m 0 || (flat_x k bb bk (ELit m) && kn_readable segs k k bb bk (Z.to_nat m))
              || kn_readable_x k bb bk ne)             (* [comment removed for export] *)
          && img_cov k (sniff_tab A) (sniff_tab A + 16)
          && (Z.leb nhi 2 ||
              (Z.leb 3 (ealign k buf) && flat_x k (ELit 0) (sniff_cell A) (ELit 8)
               && match xlo k buf with Some blo => Z.ltb 0 blo | None => false end &&
               match know_lookup segs k (ELit 0) (sniff_cell A) 8 false [] [] with
               | LHit esb [] _ =>
                 let sa := eadd esb (mkSrl k buf 3) in let '(hb, hk) := split_lit sa in
                 match xhi k esb with
                 | Some ehi =>
                     Z.ltb (ehi + bhi / 8 + 1) two64
                     && flat_x k hb hk (ELit 1)
                     && ranges_apart_x k qb qk (ELit 8) hb hk (ELit 1)
                     && match know_lookup segs k hb hk 1 false [] [] with
                        | LHit v0 [] _ =>
                                        (* [comment removed for export] *)
                                        let v := extK k v0 in
                                        match erange k v with
                                        | Some (lo, hi) => Z.eqb hi 0 || (Z.leb m lo && Z.leb hi 127)
                                                           (* [comment removed for export] *)
                                                           || (Z.leb hi 127 && lin_ge0 k [(v, 0%Z)] [(ne, 0%Z)])
                                        | None => false
                                        end
                        | _ => false
                        end
                 | None => false
                 end
               | _ => false
               end)))%bool
      then after_call cs ret None (kn_havoc k qb qk (ELit 8))
      else None
    | _, _, _, _ => None
    end
  | None => None
  end.
(* [comment removed for export] *)
Definition summary_smear (cs : acs) : option acs :=
  if negb (Z.eqb (pc cs) (x_sniff A)) then None else
  match erange (kn cs) (reg cs 10) with
  | Some (lo, hi) =>
      if (Z.leb (2 ^ 46) lo && Z.ltb hi (2 ^ 47))%bool then
        let ss := a_ss cs in
        let sr := sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (s_regs ss)
                    10 (ELit (2 ^ 47 - 1))) 11 (ELit 0x5555555555555555)) 12 (ELit 0x3333333333333333))
                    13 (ELit 0x0f0f0f0f0f0f0f0f)) 14 (ELit 0x0101010101010101)) 15 (ELit 0x7fff) in
        Some (with_ss cs (mk_ss (x_sniff A + 0x70) sr (s_know ss) (s_next ss)))
      else None
  | None => None
  end.

(* [comment removed for export] *)
Definition HS_FUEL : nat := 1024%nat.   (* [comment removed for export] *)
Definition hs_facts (T : Z) (ws : list Z) : list kentry :=
  map (fun i => KWord (SA (ELit 0) (T + 8 * Z.of_nat i)) 8 (ELit (nth i ws 0))) (seq 0 (length ws)).
(* [comment removed for export] *)
Definition kwidx (T L : Z) (k : list kentry) : tree (nat * Z) :=
  fold_left (fun t K => match K with
                        | KWord (SA (ELit 0) a) w (ELit v) =>
                            if (Z.leb T a && Z.ltb a (T + L))%bool then tset (Z.to_pos (a - T + 1)) (w, v mod two64) t else t
                        | _ => t
                        end) k TEmpty.
Fixpoint idx_byte_go (t : tree (nat * Z)) (j : Z) (d : nat) : option Z :=
  match d with
  | O => None
  | S d' => if Z.leb (Z.of_nat d') j then
              match tget (Z.to_pos (j - Z.of_nat d' + 1)) t with
              | Some (w, v) => if Nat.ltb d' w then Some (Z.land (Z.shiftr v (8 * Z.of_nat d')) 255) else idx_byte_go t j d'
              | None => idx_byte_go t j d'
              end
            else idx_byte_go t j d'
  end.
Definition hs_table (k : list kentry) (T L : Z) : option (list Z) :=
  let t := kwidx T L k in
  let bs := map (fun j => match idx_byte_go t (Z.of_nat j) 8 with
                          | Some b => Some b
                          | None => know_byte_lit segs k (ELit 0) (T + Z.of_nat j)
                          end) (seq 0 (Z.to_nat L)) in
  if forallb (fun o => match o with Some _ => true | None => false end) bs
  then Some (map (fun o => match o with Some b => b | None => 0 end) bs) else None.

Definition summary_hsort (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (x_hsort A)) then None else
  match reg_lit cs 10, reg_lit cs 11, ret_lit cs with
  | Some T, Some n, Some ret =>
      let L := 16 * n in
      if (Z.leb 1 n && Z.leb n 512 && Z.leb (img_lo A) T && Z.leb (T + L) (img_hi A) && Z.leb 0 T
          && Z.ltb (x_hsort A) two64 && Z.leb 0 (x_hsort A)
          && kwritable_x k k (ELit 0) T (ELit L))%bool then
        match hs_table k T L with
        | Some tz =>
            match AsanHeapSortDef.hs_run (x_hsort A) T HS_FUEL
                    (AsanHeapSortDef.ZS (x_hsort A) (AsanHeapSortDef.hs_regs0 ret T n) (AsanHeapSortDef.chunk16 (Z.to_nat n) tz)) with
            | Some st' =>
                if Z.eqb (AsanHeapSortDef.z_pc st') ret then
                  after_call cs ret None (hs_facts T (AsanHeapSortDef.hs_words (AsanHeapSortDef.z_tbl st'))
                                          ++ kn_havoc (kimg_cut k T L) (ELit 0) T (ELit L))
                else None
            | None => None
            end
        | None => None
        end
      else None
  | _, _, _ => None
  end.

(* [comment removed for export] *)
Definition summary_sniff (cs : acs) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  if negb (Z.eqb (pc cs) (x_sniff A)) then None else
  match ret_lit cs with
  | Some ret =>
    let buf := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
    let '(bb, bk) := split_lit buf in
    let '(qb, qk) := split_lit (eaddz sp (-8)) in
    match xhiB bc ne, xhiB bc buf, xloB bc sp, xhiB bc sp with
    | Some nhi, Some bhi, Some splo, Some sphi =>
      let m := Z.min nhi 8 in
      if (Z.ltb (bhi + 8) two64 && Z.leb 32 splo && Z.ltb sphi two64 && Z.leb (sniff_tab A + 16 + 8) splo
          && flat_xB bc qb qk (ELit 8) && kwritableB bc k qb qk 8
          && flat_xB bc bb bk (ELit 8)
          && ranges_apart_xB bc qb qk (ELit 8) bb bk (ELit 8)
          && ranges_apart_xB bc qb qk (ELit 8) (ELit 0) (sniff_cell A) (ELit 8)
          && (Z.eqb m 0 || (flat_xB bc bb bk (ELit m) && kn_readableB segs bc k bb bk (Z.to_nat m))
              || kn_readable_x k bb bk ne)             (* [comment removed for export] *)
          && img_covB bc (sniff_tab A) (sniff_tab A + 16)
          && (Z.leb nhi 2 ||
              (Z.leb 3 (ealignB bc buf) && flat_xB bc (ELit 0) (sniff_cell A) (ELit 8)
               && match xloB bc buf with Some blo => Z.ltb 0 blo | None => false end &&
               match know_lookupB segs bc (ELit 0) (sniff_cell A) 8 false [] [] with
               | LHit esb [] _ =>
                 let sa := eadd esb (mkSrlB bc buf 3) in let '(hb, hk) := split_lit sa in
                 match xhiB bc esb with
                 | Some ehi =>
                     Z.ltb (ehi + bhi / 8 + 1) two64
                     && flat_xB bc hb hk (ELit 1)
                     && ranges_apart_xB bc qb qk (ELit 8) hb hk (ELit 1)
                     && match know_lookupB segs bc hb hk 1 false [] [] with
                        | LHit v0 [] _ =>
                                        (* [comment removed for export] *)
                                        let v := extKB bc v0 in
                                        match erangeB bc v with
                                        | Some (lo, hi) => Z.eqb hi 0 || (Z.leb m lo && Z.leb hi 127)
                                                           (* [comment removed for export] *)
                                                           || (Z.leb hi 127 && lin_ge0B bc [(v, 0%Z)] [(ne, 0%Z)])
                                        | None => false
                                        end
                        | _ => false
                        end
                 | None => false
                 end
               | _ => false
               end)))%bool
      then after_call cs ret None (kn_havocB bc qb qk (ELit 8))
      else None
    | _, _, _, _ => None
    end
  | None => None
  end.

Lemma summary_sniff_eq : forall cs, summary_sniff cs = summary_sniff_ref cs.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bh11eh21nh31oh41ah51li001lh63offh72rbh82rkh93acch:2b1h;2b2h<2csh=5hintsi015hintsh>1kh?2k1h@2k2hA2knhB2n1hC2n2hD3neghE3poshF1si021shG2sxhH2ubhI2ukhJ2unhK1vhL1zi032bbi043bhii052bki063bloi073ehii083esbi092hbi0:2hii0;2hki0<2loi0=3nhii0>1pi0?2qbi0@2qki0A3reti0B3scsi0C4sphii0D4sploi0E2v0i0F1xp%0p&0p;1p;2p;4p;5p;7p;6p;3p;8g00i8j13Tg03ock10Uj2eTg00FUR0j1YTg057cj1^Tg07<4k10TTg03[nj2RTg01NYj1gTg00n=j1bTg06UQj1_Tg003kj19Tg01DAj22Tg01E@j1=Tg03Zkj1LTg06oHk10STg06ofj2nTg01`>j15Tg03S\j2@k104Tg03K?j2Pk101Tg03[Pj1ETg01M_j2KTg02Acj2VTg01N<j2>Tg07=7k10OTg00Pej1NTg03aCj4:k10FTg03I4j5]j1zTg02B@j7Fk105Tg07><k100Tg04Bgj2\Tg06eGj1|Tg07?Bj6[k20ATg07@Jj4`Tg00H3j2CTg074Cj3aj1vTg040cj1GTg00fXj1ZTg03CYj8Mj2xTg04dZj3ok107Tg04cZj2ITg06f[k20RTg00bVR1j2mTg07ASj2Uk10GTg047Wj2lj1sTg00Lej3BTg03ifj3Sk109Tg019Ij20Tg02jIj4jk10BTg06VTj4JTg03T\j2Ak10:Tg03MCj2Qk103Tg03bFj4;k10LTg03J:j5ik10>Tg02@>j7Hk10;Tg07BTj6fk20DTg075Gj3hk10ITg03B4j8Tk20?Tg04aUj3kk10<Tg07CYj2Ok10MTg04:>j2Wk10NTg03hej3dk10=Tg02kNj4ck10ETg001kj34Tg00A2R2j1XTg00GYk202Tg03OAj1~Tg00>Oj66Tg03UYj1}Tg02CKk106Tg04e\k108Tg03jjj1{Tg070gj1yTg03Dak20@Tg07DWj2wTg02mZk10CTg07Ecj1uTg05?_j1tTg07Fkk10HTg04<Bk10JTg041Hk10Kj2qTg042Kj1rTg07H0k10PTg07I9j1pTg03l2k40QTf3R3f2R4'0f1R5'0f0R6'0p=?1056,C4p=1f4R7/03/04/05/06p=81045/06p=7g00]=R8g00^=R9P6g02E\R:H0Qp=D1C56,04p=<g016FR;P9^18S00%36R<$0UQ00%Y;R=g00OER>P=%^5p,1AR?$0TS01'R#gR@%b;R;P0P9P=%_5RAP1P8P9P=g01\Y#9RB#9RC#9#9#9#9#9#9RD#9#9RE,24#=RFP1P8P9P=127Cg03\KRG#LRH#L#LRI$0SS02'n#=RJP0P9P=f6RK#3S03#5S04%9ERL,2KS05'@RMP0P9P=f7RN#3S06#5S0712NES08'@ROP0P9P=f8RP#3S09#5S0:12PCRQ'PRRP0P9P=f9RS#3RT#5RU12SCS0;'@RVP>P=%EIRW,K4g02F:RX'V%LIRI#L#E/>51V6X&0O?RY%EI'KRI/KW/>5C?RZf:R[#3R\#5R]f5R^P7%NWR_C:P]P\P^P7PWD]S0<P]PNPKP_C:C?P]P^P7P_PNPKP_FFS0=P]P^P7P_%N:R`&00?R?P_FFS0>1\3WRa/R:RbP]PNPK%NaS0?C:p,4segsRcP]P\PNPK%|aS0@E[S0A31P\PNPK12[LC`Ra'CAa]YIS0BD8Rd%EH,>3RH%GGRe#ERfPS12[ERgO1S0C'>P]P`P?P_C:S0DP0P9P>1P]g1V:6S0Eg00PERhn10110F00021010600Rig03EmRjP>PcP]P`P?PDPh%Z>Rkg029\Rl#ZRmGMRnP2PlP>P5P1P8P9P>f=Ro#3S0F#512oES0G;of,I4#=RoP0P9P>f?Rp#3Rq#5S0H/@7Rr20RPW,K6%EGRG'K/VXRXf@#3Rs#5RtP4P5%NGRGC:Ptf;S0IP[P_P4P5PGFFS0J37RuPjP>PcPtP4P5PBPhPkPmGMS0KP2PlP>P5P01m99RtP>fC#3Rv#5Rw1Uw4S0L'lP1P9P9P>P61R6:1\pW/>5%Ge#G#G#G#G#E,>6Re31R:fFRw#3Rx#5Ry1m89Rz1Uy^#D%ZzR{3B12wL#D=Bz{Rw3S71en200110>00012010<10:S0MPhn10110F00021010>00Phn10110B00020020102100PhPhn0110F00033010E10B1012010B10100'0Phn10110F00021010700n200110F00012010910;Phn10110B00020120102100PhPhn0110F00033110810B1012010B10100C?3<P[PP%b8S0NP]P^P7P_CjCJR]P;n0100000020000P;n10110F00021110C00P;n10110F00021110D00P;n10110F00021110400P;n10110F00021110=00n200110F00012110?10@n200110F000121103105P;n10110F00021110A00n0100000020001P>P=P@P;P0P9P=PAP1P8P9P=PFP1P8P9P=PJP0P9P=Q03Q05'AS0OP0P9P=Q06Q08'AS0PP0P9P=Q09/QQP0P9P=Q0;,ATS0QP>P=P\P^P7P_C;,0ZS0RP\P\P^P7PWDiP\PNPKP_C;S0S37S0TP\P^P7P_PNPKP_FHP\P^P7P_P`P?P_FHP\PNPKQ0?C;R|PcP\P\PNPKQ0@Ef51b/CaS0UAh\YIR}D8S0V1e\g,>fR~P\P`P?P_C;'0S0WP0P9P>1Q\gQ0EPhn10110F00021010600PjP>PcP\P`P?PDPhPkPmGTRgP2PlP>P5P1P8P9P>Q0FQ0G;kf,I4#=S0FP0P9P>1Aq7PsP4P5PGC;,0XS0XPsQ0IP[P_P4P5PGFHPjP>PcPsP4P5PBPhPkPmGTS0YP2PlP>P5P0PtP>1Ov4,WvS0ZP1P9P9P>P61Ox^#D=Bz{S0[=dxw91:en200110>00012010<10:Phn10110F00021010>00Phn10110B00020020102100PhPhn0110F00033010E10B1012010B10100S0\37S0]Phn10110F00021010700n200110F00012010910;Phn10110B00020120102100PhPhn0110F00033110810B1012010B10100S0^377<HP[PPQ0NP\P^P7P_CcCJRxP;n0100000020000P;n10110F00021110C00P;n10110F00021110D00P;n10110F00021110400P;n10110F00021110=00n200110F00012110?10@n200110F000121103105P;n10110F00021110A00n0100000020001Rs34WL%Yt^18S00&0N<Q00P>P=P@P;P0P9P=PAP1P8P9P=PFP1P8P9P=PJP0P9P=PMP0P9P=POP0P9P=PRP0P9P=PVP>P=Q0D=7~iS0DPjP>PnP2PlP>P5P1P8P9P>PoP0P9P>PrPjP>Q0KP2PlP>P5P0PtP>fBS0_Q0LO1Q0MPhn10110F00021010>00Phn10110B00020020102100PhPhn0110F00033010E10B1012010B10100,0uPhn10110F00021010700n200110F00012010910;Phn10110B00020120102100PhPhn0110F00033110810B1012010B10100'09<dHP]P;n0100000020000P;n10110F00021110C00P;n10110F00021110D00P;n10110F00021110400P;n10110F00021110=00n200110F00012110?10@n200110F000121103105P;n10110F00021110A00n0100000020001=4=sW3P8^K8S00&0M<Q00P>P=P@P;P0P9P=PAP1P8P9P=PFP1P8P9P=PJP0P9P=PMP0P9P=POP0P9P=PRP0P9P=PVP>P=Q0DPjP>PnP2PlP>P5P1P8P9P>PoP0P9P>PrPjP>Q0KP2PlP>P5P0PtP>Q0_P4O1,WvP1P9P9P>P6fERvP^O1#D=Bz{=Syw91:en200110>00012010<10:Phn10110F00021010>00Phn10110B00020020102100PhPhn0110F00033010E10B1012010B10100,0uPhn10110F00021010700n200110F00012010910;Phn10110B00020120102100PhPhn0110F00033110810B1012010B10100'09<dHP]P;n0100000020000P;n10110F00021110C00P;n10110F00021110D00P;n10110F00021110400P;n10110F00021110=00n200110F00012110?10@n200110F000121103105P;n10110F00021110A00n0100000020001=4=sW1P>^28^69^08Rd&0L<P>P=P@P;P0P9P=PAP1P8P9P=PFP1P8P9P=PJP0P9P=PMP0P9P=POP0P9P=PRP0P9P=PVP>P=PZPSP^P7P_O3S00Q0<PSPNPKP_O3Q0=D8Q0>PSPNPKQ0?O3Q0A51b/CaQ0BPSP`P?P_O3=7~iPjP>PnP2PlP>P5P1P8P9P>PoP0P9P>PrPXPpP4P5PGO3Q0JPjP>Q0KP2PlP>P5P0PtP>Q0ZP1P9P9P>P6Q0[=Syw91:en200110>00012010<10:Phn10110F00021010>00Phn10110B00020020102100S0KPhPhn0110F00033010E10B1012010B10100RyC?Phn10110F00021010700n200110F00012010910;Phn10110B00020120102100PhPhn0110F00033110810B1012010B1010051HD8P]P;n0100000020000P;n10110F00021110C00P;n10110F00021110D00P;n10110F00021110400P;n10110F00021110=00n200110F00012110?10@n200110F000121103105P;n10110F00021110A00n0100000020001=4=sX0dP>^09^49Rd&0I<P>P=P@P;P0P9P=PAP1P8P9P=PFP1P8P9P=PJP0P9P=PMP0P9P=POP0P9P=PRP0P9P=PVP>P=Q0RQ0<Q0SQ0=Q0>D8R~Q0A91b|;<aRuPSPYPIO2Q0W/0iRiPjP>PnP2PlP>P5P1P8P9P>PoP0P9P>PrQ0XQ0J'0Rn/0yPhn10110F00021010700n200110F00012010910;Phn10110B00020120102100PhPhn0110F00033110810B1012010B1010051HRy37P]P;n0100000020000P;n10110F00021110C00P;n10110F00021110D00P;n10110F00021110400P;n10110F00021110=00n200110F00012110?10@n200110F000121103105P;n10110F00021110A00n0100000020001=4=sX0dg014B#XRd^J8^I9^H8R]&0E<P>P=P@P;P0P9P=PAP1P8P9P=PFP1P8P9P=PJP0P9P=PMP0P9P=POP0P9P=PRP0P9P=PVP>P=A7u}yP[PPQ0NQ00CJP;n0100000020000P;n10110F00021110C00P;n10110F00021110D00P;n10110F00021110400P;n10110F00021110=00n200110F00012110?10@n200110F000121103105P;n10110F00021110A00n0100000020001=4=sX5]g005OR]P>]2^89^78^AdRu20Dc<P>P=P@P;P0P9P=PAP1P8P9P=PFP1P8P9P=PJP0P9P=PMP0P9P=POP0P9P=PRP0P9P=PVP>P=PSP\PNPKQ0@O491b|=<~a?7}yPxP;n0100000020000P;n10110F00021110C00P;n10110F00021110D00P;n10110F00021110400P;n10110F00021110=00n200110F00012110?10@n200110F000121103105P;n10110F00021110A00n0100000020001=4=sX0u%X>%XlPj]9]=^G>^2]^89^78R]20?c<P>P=P@P;P0P9P=PAP1P8P9P=PFP1P8P9P=PJP0P9P=PMP0P9P=POP0P9P=PRP0P9P=PVP>P=P~Q0UP}PjP>PSP`P?PDPhPkPmO6P2PlP>P5P1P8P9P>PoP0P9P>PrPjP>PpP4P5PBPhPkPmO6Q0KPhPhn0110F00033010E10B1012010B10100,0nPhn10110F00021010700n200110F00012010910;Phn10110B00020120102100PhPhn0110F00033110810B1012010B1010091HiC?PxP;n0100000020000P;n10110F00021110C00P;n10110F00021110D00P;n10110F00021110400P;n10110F00021110=00n200110F00012110?10@n200110F000121103105P;n10110F00021110A00n0100000020001=4=sX5]P>^29^69^08^>dRd&0><P>P=P@P;P0P9P=PAP1P8P9P=PFP1P8P9P=PJP0P9P=PMP0P9P=POP0P9P=PRP0P9P=PVP>P=Q0RPSP\P^P7PWO4Q0SQ0=C?Q0>Q0UP}PjP>PgP2PlP>P5P1P8P9P>PoP0P9P>PrPjP>Q0YQ0KPhPhn0110F00033010E10B1012010B10100,0nPhn10110F00021010700n200110F00012010910;Phn10110B00020120102100PhPhn0110F00033110810B1012010B1010091HiD8PxP;n0100000020000P;n10110F00021110C00P;n10110F00021110D00P;n10110F00021110400P;n10110F00021110=00n200110F00012110?10@n200110F000121103105P;n10110F00021110A00n0100000020001=4=sX0dg03lRRdP>^Dd]ERd&0=<P>P=P@P;P0P9P=PAP1P8P9P=PFP1P8P9P=PJP0P9P=PMP0P9P=POP0P9P=PRP0P9P=PVP>P=Q0TQ0=Q0>Q0UP}D8R\PjP>PgP2PlP>P5P1P8P9P>PoP0P9P>PrPjP>Q0YP2PlP>P5P0PtP>Q0ZP1P9P9P>P6PvQ0[PwO291:en200110>00012010<10:Phn10110F00021010>00Phn10110B00020020102100PhPhn0110F00033010E10B1012010B10100,0nPhn10110F00021010700n200110F00012010910;Phn10110B00020120102100PhPhn0110F00033110810B1012010B10100,0i7<HPxP;n0100000020000P;n10110F00021110C00P;n10110F00021110D00P;n10110F00021110400P;n10110F00021110=00n200110F00012110?10@n200110F000121103105P;n10110F00021110A00n0100000020001=4=sX0dP8^F9^48Rd&0<<P>P=P@P;P0P9P=PAP1P8P9P=PFP1P8P9P=PJP0P9P=PMP0P9P=POP0P9P=PRP0P9P=PVP>P=PjP>PgP2PlP>P5P1P8P9P>f<RwQ0GPfO2,I4#=P0P9P>PrQ0\,0nPhn10110F00021010700n200110F00012010910;Phn10110B00020120102100PhPhn0110F00033110810B1012010B10100,0i9<\HPxP;n0100000020000P;n10110F00021110C00P;n10110F00021110D00P;n10110F00021110400P;n10110F00021110=00n200110F00012110?10@n200110F000121103105P;n10110F00021110A00n0100000020001=4=sX1dP>^C8^@9^;8^B8^?9^:8Rd&0;<P>P=P@P;P0P9P=PAP1P8P9P=PFP1P8P9P=PJP0P9P=PMP0P9P=POP0P9P=PRP0P9P=PVP>P=Q0TPSP^P7P_PNPKP_O6'0PSP^P7P_P`P?P_O6Q0UP}PjP>PgP2PlP>P5P1P8P9P>Q0FP0P9P>PrQ0XPpQ0IP[P_P4P5PGO6Q0\37Phn10110F00021010700n200110F00012010910;Phn10110B00020120102100PhPhn0110F00033110810B1012010B1010091HiD8PxP;n0100000020000P;n10110F00021110C00P;n10110F00021110D00P;n10110F00021110400P;n10110F00021110=00n200110F00012110?10@n200110F000121103105P;n10110F00021110A00n0100000020001=4=sX0d%Y9^18Rd&0:<P>P=P@P;P0P9P=PAP1P8P9P=PFP1P8P9P=PJP0P9P=P^Q05O1P0P9P=PKQ08O1P0P9P=PRP0P9P=PPQ0;O1P>P=Q0VPjP>PgP2PlP>P5P1P8P9P>Q0FP0P9P>f>RgP7O1Q0]Phn10110F00021010700n200110F00012010910;Phn10110B00020020102100PhPhn0110F00033110810B1012010B10100,0i7<HPxP;n0100000020000P;n10110F00021110C00P;n10110F00021110D00P;n10110F00021110400P;n10110F00021110=00n200110F00012110?10@n200110F000121103105P;n10110F00021110A00n0100000020001=4=sX3dPd&03<P>P=P@P;P0P9P=PAP1P8P9P=PFP1P8P9P=PJP0P9P=Q0OP0P9P=Q0PP0P9P=PNPQO1P0P9P=Q0QP>P=Q0VQ0WP0P9P>Q0CQ0EPhn10110F00021010600Q0^377<HPxP;n0100000020000P;n10110F00021110C00P;n10110F00021110D00P;n10110F00021110400P;n10110F00021110=00n200110F00012110?10@n200110F000121103105P;n10110F00021110A00n0100000020001=4=sX3dP>P=%^6Q01'R#gRdP;P0P9P=%_6RsP1P8P9P=125E#=RxP1P8P9P=123CQ02'n#=R3P0P9P=%3^RJ12^LRF'AP0P9P=Q0312KERA'AP0P9P=Q0612NCRC'QP0P9P=Q09/AQP>P=PZPTP^P7P_C;PTPTP^P7PWDiPTPNPKP_C;PTP^P7P_PNPKP_FHD8PTP^P7P_P`P?P_FHPTPNPKQ0?C;PcPTPTPNPKQ0@Ef51bPTPNPK12SLC`R@'CAhTYI12SERi,eT,>fPTP`P?P_C;P0P9P>1QTiQ0EPhn10110F0002101060037PjP>PcPTP`P?PDPhPkPmGTP2PlP>P5P1P8P9P>%3wRR12wERw;kf,I4#=P0P9P>%3gRg/A7PXPqP4P5PGC;PqQ0IP[P_P4P5PGFHPjP>PcPqP4P5PBPhPkPmGTP2PlP>P5P0PtP>Q0_#3Rq1Oq4'WP1P9P9P>P6%3vRE1OE^#D=Bz{12vL#D=Bz{Rv3d91:en200110>00012010<10:Phn10110F00021010>00Phn10110B00020020102100PhPhn0110F00033010E10B1012010B10100C?Phn10110F00021010700n200110F00012010910;Phn10110B00020120102100PhPhn0110F00033110810B1012010B1010051HD8PSPPQ0NPTP^P7P_CcCJP;n0100000020000P;n10110F00021110C00P;n10110F00021110D00P;n10110F00021110400P;n10110F00021110=00n200110F00012110?10@n200110F000121103105P;n10110F00021110A00n0100000020001RL-02=%5<Rp$01%~<E6&04p%}<E6&05p&06<E6&07p&08<E6&09p%{<E6%zp%y<E61xcp20@<cE620Acp1wc<E6&0Bp&0C<E6%vp%u<E6&0Fp%t<E6&0Gp&0H<E6%sp&0J<E6&0Kp%r<E6P>P=PdP;P0P9P=PsP1P8P9P=PxP1P8P9P=P3P0P9P=%5J/@FP0P9P=Q04/@AP0P9P=Q07/PCP0P9P=Q0:/@QP>P=PZPUP^P7P_C:PUPTP^P7PWD]PUPNPKP_C:PUP^P7P_PNPKP_FFD8PUP^P7P_P`P?P_FFPUPNPKQ0?C:PcPUPTPNPKQ0@E[51b/C@AaUYI1qUi,>fPUP`P?P_C:P0P9P>1PUiQ0EPhn10110F0002101060037PjP>PcPUP`P?PDPhPkPmGMP2PlP>P5P1P8P9P>%5R?owf,I4#=P0P9P>%5g/@7PXQ0HP4P5PGC:Q0HQ0IP[P_P4P5PGFFPjP>PcQ0HP4P5PBPhPkPmGMP2PlP>P5P0PtP>%5qRq1Uq4'lP1P9P9P>P6%5ERE1UE^#D=Bz{;Sv91:en200110>00012010<10:Phn10110F00021010>00Phn10110B00020020102100PhPhn0110F00033010E10B1012010B10100C?Phn10110F00021010700n200110F00012010910;Phn10110B00020120102100PhPhn0110F00033110810B1012010B1010051HD8PSPPQ0NPUP^P7P_CjCJP;n0100000020000P;n10110F00021110C00P;n10110F00021110D00P;n10110F00021110400P;n10110F00021110=00n200110F00012110?10@n200110F000121103105P;n10110F00021110A00n0100000020001=4=Le&0P6%p654=eW<o"). Qed.


(* [comment removed for export] *)
Definition V_S1 : nat := 0.     (* [comment removed for export] *)
Definition V_ARGC : nat := 1.
Definition V_ENVC : nat := 2.
Definition V_L0 : nat := 3.     (* [comment removed for export] *)
Definition V_W : nat := 4.      (* [comment removed for export] *)
Definition V_BRK : nat := 5.    (* [comment removed for export] *)
Definition V_S2 : nat := 6.     (* [comment removed for export] *)
Definition V_L1 : nat := 7.     (* [comment removed for export] *)
Definition V_UID : nat := 8.    (* [comment removed for export] *)
Definition V_HW : nat := 9.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition e_sp0 : expr := eadd (escale 32768 (EVar V_S1)) (escale 16 (EVar V_S2)).
(* [comment removed for export] *)
Definition e_envp : expr := eadd e_sp0 (eadd (escale 8 (EVar V_ARGC)) (ELit 16)).
Definition e_auxv : expr := eadd e_envp (eadd (escale 8 (EVar V_ENVC)) (ELit 8)).
Definition e_str0 : expr := eaddz e_auxv 160.
Definition e_str1 : expr := eadd e_str0 (eaddz (EVar V_L0) 1).
Definition e_atrandom : expr := eadd e_str0 (escale 8 (EVar V_W)).
(* [comment removed for export] *)
Definition e_atr8 : expr :=
  eadd (eadd (escale 4096 (EVar V_S1)) (escale 2 (EVar V_S2))) (eadd (EVar V_ARGC) (eadd (EVar V_ENVC) (EVar V_W))).

(* [comment removed for export] *)
Definition e_argv1w : expr := EMd M_MUL (EAlu ALU_SLTU (ELit 1) (EVar V_ARGC)) e_str1.

(* [comment removed for export] *)
Definition node_envscan (cs : acs) : option acs :=
  let k := kn cs in
  if (Z.eqb (pc cs) (x_envscan A) && len_eqb k (reg cs 9) e_envp)%bool then
    Some (set_pc (set_reg (set_reg cs 9 (eadd (reg cs 9) (eadd (escale 8 (EVar V_ENVC)) (ELit 8)))) 10 (ELit 0)) (x_envscan_k A))
  else None.

(* [comment removed for export] *)
Definition node_pnscan (cs : acs) : option acs :=
  let k := kn cs in
  match reg_lit cs 10, reg_lit cs 12 with
  | Some p, Some 47 =>
      if (Z.eqb (pc cs) (x_pnscan A) && len_eqb k (reg cs 11) (eaddz e_str0 1)
          && kwritable k k (ELit 0) p 8 && Z.leb (img_lo A) p && Z.leb (p + 8) (img_hi A) && fresh_ok cs)%bool then
        let v := nxt cs in
        let k' := kn_havoc (kimg_cut k p 8) (ELit 0) p (ELit 8) in
        let ss := a_ss cs in
        Some (with_ss cs (mk_ss (x_pnscan_k A) (sr_upd (sr_upd (s_regs ss) 11 (EVar v)) 13 (ELit 0)) k' (S v)))
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition kw_argv1 (v : expr) : kentry := KWord (SA e_sp0 16) 8 v.

Definition node_layout (cs : acs) (args : list expr) : option acs :=
  let k := kn cs in
  if negb (existsb (kentry_eqb (kw_argv1 e_argv1w)) k) then None else
  let k' := List.filter (fun K => negb (kentry_eqb (kw_argv1 e_argv1w) K)) k in
  match args with
  | [ELit 1] => match xlo k (EVar V_ARGC) with
                | Some lo => if Z.leb 2 lo then Some (set_kn cs (kw_argv1 e_str1 :: k')) else None
                | None => None
                end
  | [ELit 0] => match xhi k (EVar V_ARGC) with
                | Some hi => if Z.leb hi 1 then Some (set_kn cs (kw_argv1 (ELit 0) :: k')) else None
                | None => None
                end
  | _ => None
  end.


(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint esubst (J : nat) (e : expr) (x : expr) : expr :=
  match x with
  | ELit _ => x
  | EVar n => if Nat.eqb n J then e else x
  | EAlu op a b => mkAlu op (esubst J e a) (esubst J e b)
  | EAluw op a b => mkAluw op (esubst J e a) (esubst J e b)
  | EMd op a b => mkMd op (esubst J e a) (esubst J e b)
  | EMdw op a b => mkMdw op (esubst J e a) (esubst J e b)
  | EExt sx lo n a => EExt sx lo n (esubst J e a)
  | EBlob _ _ _ _ => x
  end.
(* [comment removed for export] *)
Definition asubst (J : nat) (e : expr) (a : saddr) : saddr := SA (esubst J e (a_base a)) (a_off a).
Definition ksubst (J : nat) (e : expr) (K : kentry) : kentry :=
  match K with
  | KWord a w v => KWord (asubst J e a) w (esubst J e v)
  | KZero a n => KZero (asubst J e a) (esubst J e n)
  | KBlob a n k => KBlob (asubst J e a) (esubst J e n) k
  | KImg lo hi => K
  | KAlign x m => KAlign (esubst J e x) m
  | KRange x lo hi => KRange (esubst J e x) lo hi
  | KWr a n => KWr (asubst J e a) (esubst J e n)
  | KDisj a1 n1 a2 n2 => KDisj (asubst J e a1) (esubst J e n1) (asubst J e a2) (esubst J e n2)
  | KFill a n c => KFill (asubst J e a) (esubst J e n) c
  | KUnk a n => KUnk (asubst J e a) (esubst J e n)
  end.
Definition psubst (J : nat) (e : expr) (p : expr * expr) : expr * expr := (esubst J e (fst p), esubst J e (snd p)).
Definition msubst (J : nat) (e : expr) (m : amap) : amap := AM (esubst J e (am_base m)) (esubst J e (am_len m)) (am_kind m).
Definition fsubst (J : nat) (e : expr) (f : afd) : afd :=
  match f with FdFile k l o => FdFile k (esubst J e l) (esubst J e o) | _ => f end.
(* [comment removed for export] *)
Definition inst (inv : acs) (J : nat) (e : expr) : acs :=
  ACS (mk_ss (pc inv) (map (esubst J e) (s_regs (a_ss inv))) (map (ksubst J e) (kn inv)) (nxt inv))
      (map (msubst J e) (a_maps inv)) (a_totsz inv) (a_ylo inv) (a_eager inv)
      (map (psubst J e) (a_vis inv)) (map (psubst J e) (a_ghost inv)) (a_abytes inv)
      (esubst J e (a_brk inv)) (fsubst J e (a_fd inv)) (a_tidset inv).

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint nt_set (t : list (option nat)) (i : nat) (d : nat) {struct i} : list (option nat) :=
  match i, t with
  | O, [] => [Some d]
  | O, _ :: rest => Some d :: rest
  | S j, [] => None :: nt_set [] j d
  | S j, x :: rest => x :: nt_set rest j d
  end.
Definition nt_get (t : list (option nat)) (i : nat) : option nat := nth i t None.
Lemma nt_get_set : forall t i d j, nt_get (nt_set t i d) j = if Nat.eqb j i then Some d else nt_get t j.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01jh11th21dh31ih44resth51xh62IHh71bi001bh81oi011oi021li031mi041np;1p;3p;2p;4p;6p;5g00FUj1BTg00A2R0j1ATg07JFj32Tg00n=j1<Tg00E5j20Tg07KHj44Tg00fXj1=Tg00GYj25Tg001kj33Tg003kj17Tg00Lej3:Tg00>Oj6@Tg04Pjj5>Tg07Kdj2;Tg00G7j2?Tg005OR1f0R2'?p=8f5R3f4R4f3R5f2R6f1R7C4;32p=1g01\YR8=272p=6P6P8P7P2C4p=9%B1R9#AR:P9P9P2A2657%<1R;g00OER<P91025%87R=P9P2P6P;C4R>n0100000020000E1^01^21^1:R?X31P0P9P9P9P71626P;P<P91078%86R@P9P7P2P;C4RAn0100000020000E1P6P1P9P9P2%=9RB/66P;P<P91028RCP@P9P2PBP;C4RDn0100000020000E1P2159=16B7=99;P<P91088REP=A99B;RFn0100000020000539eP1P1P9P2P;P;n0110400020010103=39;P2159;RGPGX01P2O1RHn0110400020010104P9P9%72RI16B5P;P<P910I8RJ%85RKP9PIPBP;C4RLn0100000020000E1eX01P2O1n0110400020010104P1P9P9P2A:967RMf6RN'6P;P<P9PC%8NRCP9P2PMP;C4ROn0100000020000E1P4%83RP,59A:972RQ/63=99;P<P9PEPPA99Q;REn0100000020000539e159>P9P9PIA:956R>f7RR'6P;P<P9PJ%8RRJP9PIP>P;C4RSn0100000020000E1eX01P2O1n0110400020010104X4:X59P7P2O2n10110200020020101102X01X21X1:P0P9P9P9P7%73R0=226P;P<P91070P@PAn0100000020000E1P6P1P9P9P2A2B06P;P<P91020P@PDn0100000020000E1P2PG%74R@=2B7=99;P<P9108@P=PFn0100000020000539eP9P<P9102NRFPKPDn0100000020000P<P9107R%84R@P;n01000000200009392X89PFP<P<P<P9P2PPP9P6PBP;C4n0100000020000P<P9P2PPP;n0100000020000539P2P1A39PPP7159@159CX01P2O1n0110400020010104P1A39D;P7PGPHn0110400020010104n0110000020000b7P9P2A2BN5P;C4P3PBP5P2O3E@P9P9PI%7NRH=2B5P;P<P910IHPKPLn0100000020000E1eX01P2O1n0110400020010104P1P9P9P2f9RL#7RK=2MNP;P<P9102KPCPOn0100000020000E1P41597f8#7R4=2Q3=99;P<P91084PPPEn0100000020000539ePLP6PRP2O3P9P9PIf:#7RL=2>RP;P<P910ILPJPSn0100000020000E1eX01P2O1n0110400020010104X4:X59P7P2O2n10110200020120101102X01X21X1:X6?X31P2P7D>X31W1A2567/;2P<P91026P=1;52n0100000020000539^01^21^31^1:eo"). Qed.
(* [comment removed for export] *)
Fixpoint mk_fwd (m : list (nat * nat)) : option (list (option nat)) :=
  match m with
  | [] => Some []
  | (s, d) :: rest =>
      match mk_fwd rest with
      | Some t => match nt_get t s with None => Some (nt_set t s d) | Some _ => None end
      | None => None
      end
  end.
(* [comment removed for export] *)
Fixpoint mk_bwd (m : list (nat * nat)) : option (list (option nat)) :=
  match m with
  | [] => Some []
  | (s, d) :: rest =>
      match mk_bwd rest with
      | Some t => match nt_get t d with None => Some (nt_set t d s) | Some _ => None end
      | None => None
      end
  end.

Fixpoint erename (t : list (option nat)) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | EVar v => match nt_get t v with Some d => EVar d | None => e end
  | EAlu op a b => EAlu op (erename t a) (erename t b)
  | EAluw op a b => EAluw op (erename t a) (erename t b)
  | EMd op a b => EMd op (erename t a) (erename t b)
  | EMdw op a b => EMdw op (erename t a) (erename t b)
  | EExt sx lo n a => EExt sx lo n (erename t a)
  | EBlob _ _ _ _ => e
  end.
Definition arename (t : list (option nat)) (a : saddr) : saddr := SA (erename t (a_base a)) (a_off a).
Definition krename (t : list (option nat)) (K : kentry) : kentry :=
  match K with
  | KWord a w v => KWord (arename t a) w (erename t v)
  | KZero a n => KZero (arename t a) (erename t n)
  | KBlob a n k => KBlob (arename t a) (erename t n) k
  | KImg lo hi => K
  | KAlign x m => KAlign (erename t x) m
  | KRange x lo hi => KRange (erename t x) lo hi
  | KWr a n => KWr (arename t a) (erename t n)
  | KDisj a1 n1 a2 n2 => KDisj (arename t a1) (erename t n1) (arename t a2) (erename t n2)
  | KFill a n c => KFill (arename t a) (erename t n) c
  | KUnk a n => KUnk (arename t a) (erename t n)
  end.
Definition prename (t : list (option nat)) (p : expr * expr) : expr * expr := (erename t (fst p), erename t (snd p)).
Definition mrename (t : list (option nat)) (m : amap) : amap := AM (erename t (am_base m)) (erename t (am_len m)) (am_kind m).
Definition frename (t : list (option nat)) (f : afd) : afd :=
  match f with FdFile k l o => FdFile k (erename t l) (erename t o) | _ => f end.

(* [comment removed for export] *)
Fixpoint evars_all (ok : nat -> bool) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar v => ok v
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => evars_all ok a && evars_all ok b
  | EExt _ _ _ a => evars_all ok a
  | EBlob _ _ _ _ => true
  end.
Definition kvars_all (ok : nat -> bool) (K : kentry) : bool :=
  match K with
  | KWord a _ v => evars_all ok (a_base a) && evars_all ok v
  | KZero a n | KBlob a n _ | KWr a n | KFill a n _ | KUnk a n => evars_all ok (a_base a) && evars_all ok n
  | KImg _ _ => true
  | KAlign x _ | KRange x _ _ => evars_all ok x
  | KDisj a1 n1 a2 n2 => evars_all ok (a_base a1) && evars_all ok n1 && evars_all ok (a_base a2) && evars_all ok n2
  end%bool.
Definition csvars_all (ok : nat -> bool) (cs : acs) : bool :=
  (forallb (evars_all ok) (s_regs (a_ss cs)) && forallb (kvars_all ok) (kn cs)
   && forallb (fun m => evars_all ok (am_base m) && evars_all ok (am_len m)) (a_maps cs)
   && forallb (fun p => evars_all ok (fst p) && evars_all ok (snd p)) (a_vis cs)
   && forallb (fun p => evars_all ok (fst p) && evars_all ok (snd p)) (a_ghost cs)
   && evars_all ok (a_brk cs)
   && match a_fd cs with FdFile _ l o => evars_all ok l && evars_all ok o | _ => true end)%bool.

(* [comment removed for export] *)
Fixpoint emaxv (e : expr) (acc : nat) : nat :=
  match e with
  | ELit _ => acc
  | EVar v => Nat.max acc (S v)
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => emaxv a (emaxv b acc)
  | EExt _ _ _ a => emaxv a acc
  | EBlob _ _ _ _ => acc
  end.
Definition kmaxv (K : kentry) (acc : nat) : nat :=
  match K with
  | KWord a _ v => emaxv (a_base a) (emaxv v acc)
  | KZero a n | KBlob a n _ | KWr a n | KFill a n _ | KUnk a n => emaxv (a_base a) (emaxv n acc)
  | KImg _ _ => acc
  | KAlign x _ | KRange x _ _ => emaxv x acc
  | KDisj a1 n1 a2 n2 => emaxv (a_base a1) (emaxv n1 (emaxv (a_base a2) (emaxv n2 acc)))
  end.
Definition csmaxv (cs : acs) : nat :=
  let acc := fold_right emaxv 0%nat (s_regs (a_ss cs)) in
  let acc := fold_right kmaxv acc (kn cs) in
  let acc := fold_right (fun m acc => emaxv (am_base m) (emaxv (am_len m) acc)) acc (a_maps cs) in
  let acc := fold_right (fun p acc => emaxv (fst p) (emaxv (snd p) acc)) acc (a_vis cs) in
  let acc := fold_right (fun p acc => emaxv (fst p) (emaxv (snd p) acc)) acc (a_ghost cs) in
  let acc := match a_fd cs with FdFile _ l o => emaxv l (emaxv o acc) | _ => acc end in
  emaxv (a_brk cs) acc.

Definition rename_cs (t : list (option nat)) (cs : acs) (nx : nat) : acs :=
  ACS (mk_ss (pc cs) (map (erename t) (s_regs (a_ss cs))) (map (krename t) (kn cs)) nx)
      (map (mrename t) (a_maps cs)) (a_totsz cs) (a_ylo cs) (a_eager cs)
      (map (prename t) (a_vis cs)) (map (prename t) (a_ghost cs)) (a_abytes cs)
      (erename t (a_brk cs)) (frename t (a_fd cs)) (a_tidset cs).

(* [comment removed for export] *)
Definition node_rename (gb : nat) (cs : acs) (m : list (nat * nat)) : option acs :=
  if forallb (fun p => Nat.leb gb (fst p) && Nat.leb gb (snd p)) m then
    match mk_fwd m, mk_bwd m with
    | Some fw, Some bw =>
        let ok (v : nat) := match nt_get fw v with Some _ => true | None => match nt_get bw v with Some _ => false | None => true end end in
        if (csvars_all ok cs && match s_log (a_ss cs) with [] => true | _ => false end)%bool then
          let cs1 := rename_cs fw cs 0%nat in
          Some (with_ss cs1 (mk_ss (pc cs1) (s_regs (a_ss cs1)) (kn cs1) (Nat.max gb (csmaxv cs1))))
        else None
    | _, _ => None
    end
  else None.

(* [comment removed for export] *)
Fixpoint bt_set (t : list bool) (i : nat) {struct i} : list bool :=
  match i, t with
  | O, [] => [true]
  | O, _ :: rest => true :: rest
  | S j, [] => false :: bt_set [] j
  | S j, x :: rest => x :: bt_set rest j
  end.
Definition bt_get (t : list bool) (i : nat) : bool := nth i t false.
(* [comment removed for export] *)
Fixpoint evars_fo (gb : nat) (e : expr) (acc : list nat * list bool) : list nat * list bool :=
  match e with
  | ELit _ => acc
  | EVar v => if Nat.ltb v gb then acc else if bt_get (snd acc) v then acc else (v :: fst acc, bt_set (snd acc) v)
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => evars_fo gb b (evars_fo gb a acc)
  | EExt _ _ _ a => evars_fo gb a acc
  | EBlob _ _ _ _ => acc
  end.
Definition kvars_fo (gb : nat) (K : kentry) (acc : list nat * list bool) : list nat * list bool :=
  match K with
  | KWord a _ v => evars_fo gb v (evars_fo gb (a_base a) acc)
  | KZero a n | KBlob a n _ | KWr a n | KFill a n _ | KUnk a n => evars_fo gb n (evars_fo gb (a_base a) acc)
  | KImg _ _ => acc
  | KAlign x _ | KRange x _ _ => evars_fo gb x acc
  | KDisj a1 n1 a2 n2 => evars_fo gb n2 (evars_fo gb (a_base a2) (evars_fo gb n1 (evars_fo gb (a_base a1) acc)))
  end.
Definition csvars_fo (gb : nat) (cs : acs) : list nat :=
  let acc := fold_left (fun acc e => evars_fo gb e acc) (s_regs (a_ss cs)) ([], []) in
  let acc := fold_left (fun acc K => kvars_fo gb K acc) (kn cs) acc in
  let acc := fold_left (fun acc m => evars_fo gb (am_len m) (evars_fo gb (am_base m) acc)) (a_maps cs) acc in
  let acc := fold_left (fun acc p => evars_fo gb (snd p) (evars_fo gb (fst p) acc)) (a_vis cs) acc in
  let acc := fold_left (fun acc p => evars_fo gb (snd p) (evars_fo gb (fst p) acc)) (a_ghost cs) acc in
  let acc := match a_fd cs with FdFile _ l o => evars_fo gb o (evars_fo gb l acc) | _ => acc end in
  let acc := evars_fo gb (a_brk cs) acc in
  rev (fst acc).
Fixpoint number_from (i : nat) (l : list nat) : list (nat * nat) :=
  match l with [] => [] | v :: rest => (v, i) :: number_from (S i) rest end.
Definition compact_map (gb : nat) (cs : acs) : list (nat * nat) := number_from gb (csvars_fo gb cs).
Definition node_compact (gb : nat) (cs : acs) : option acs := node_rename gb cs (compact_map gb cs).

(* [comment removed for export] *)
Fixpoint regs_match_h (lo hi : nat) (seen : list nat) (rs ts : list expr) : bool :=
  match rs, ts with
  | [], [] => true
  | r :: rs', t :: ts' =>
      match t with
      | EVar v => if (Nat.leb lo v && Nat.ltb v hi)%bool
                  then (negb (existsb (Nat.eqb v) seen) && regs_match_h lo hi (v :: seen) rs' ts')%bool
                  else (expr_eqb r t && expr_vars_lt lo t && regs_match_h lo hi seen rs' ts')%bool
      | _ => (expr_eqb r t && expr_vars_lt lo t && regs_match_h lo hi seen rs' ts')%bool
      end
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition saddr_eqb_h (x y : saddr) : bool :=
  saddr_eqb x y || expr_eqb (eaddz (a_base x) (a_off x)) (eaddz (a_base y) (a_off y)).
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint cover1 (k : list kentry) (b : expr) (i : Z) : option Z :=
  match k with
  | [] => None
  | K :: rest =>
      let hit := match K with
                 | KWord (SA kb kk) w _ =>
                     if (expr_eqb b kb && Z.leb kk i && Z.ltb i (kk + Z.of_nat w))%bool then Some (kk + Z.of_nat w) else None
                 | KZero (SA kb kk) (ELit l) | KFill (SA kb kk) (ELit l) _ | KBlob (SA kb kk) (ELit l) _ | KUnk (SA kb kk) (ELit l) =>
                     if (expr_eqb b kb && Z.leb 0 l && Z.ltb l two64 && Z.leb kk i && Z.ltb i (kk + l))%bool then Some (kk + l) else None
                 | _ => None
                 end in
      match hit with Some e => Some e | None => cover1 rest b i end
  end.
Fixpoint cover_x (fuel : nat) (k : list kentry) (b : expr) (i : Z) (stop : Z) : bool :=
  match fuel with
  | O => false
  | S f => if Z.leb stop i then true else
           match cover1 k b i with
           | Some e => if Z.ltb i e then cover_x f k b e stop else false
           | None => false
           end
  end.
(* [comment removed for export] *)
Definition kunk_covered (k : list kentry) (K : kentry) : bool :=
  match K with
  | KUnk (SA b o) (ELit n) =>
      (Z.ltb 0 n && Z.leb n (2 ^ 40) && Z.leb (img_lo A) (img_hi A) && flat_x k b o (ELit n) && off_image_x k b o (ELit n) && cover_x (S (length k)) k b o (o + n))%bool
  | _ => false
  end.

Definition kentry_eqb_h (x y : kentry) : bool :=
  kentry_eqb x y ||
  match x, y with
  | KWord a w v, KWord a' w' v' => saddr_eqb_h a a' && Nat.eqb w w' && expr_eqb v v'
  | KZero a n, KZero a' n' => saddr_eqb_h a a' && expr_eqb n n'
  | KBlob a n k, KBlob a' n' k' => saddr_eqb_h a a' && expr_eqb n n' && Nat.eqb k k'
  | KWr a n, KWr a' n' => saddr_eqb_h a a' && expr_eqb n n'
  | KFill a n c, KFill a' n' c' => saddr_eqb_h a a' && expr_eqb n n' && Z.eqb c c'
  | KUnk a n, KUnk a' n' => saddr_eqb_h a a' && expr_eqb n n'
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition kflat_h (k : list kentry) (K : kentry) : bool :=
  match K with
  | KWord (SA b o) w _ => flat_x k b o (ELit (Z.of_nat w))
  | KZero (SA b o) n | KBlob (SA b o) n _ | KWr (SA b o) n | KFill (SA b o) n _ | KUnk (SA b o) n => flat_x k b o n
  | _ => true
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kimg_sub_covered (k : list kentry) (K : kentry) : bool :=
  match K with
  | KImg lo hi => existsb (fun X => match X with KImg lo' hi' => Z.leb lo' lo && Z.leb hi hi' | _ => false end) k
  | _ => false
  end.
Definition kn_incl1_h (k : list kentry) (K : kentry) : bool :=
  if existsb (fun X => kentry_eqb X K) k then true
  else if (if kflat_h k K then existsb (fun X => kentry_eqb_h X K) k else false) then true
  else if kimg_sub_covered k K then true
  else kunk_covered k K.
Definition kn_incl_h (k : list kentry) (tk : list kentry) : bool := forallb (kn_incl1_h k) tk.

Definition entails_h (lo hi : nat) (cs : acs) (ch : acs) : bool :=
  (Z.eqb (pc cs) (pc ch)
   && match s_log (a_ss ch) with [] => true | _ => false end
   && match s_resv (a_ss ch) with None => true | _ => false end
   && regs_match_h lo hi [] (s_regs (a_ss cs)) (s_regs (a_ss ch))
   && kn_incl_h (kn cs) (kn ch)
   && kn_vars_lt lo (kn ch) && maps_vars_lt lo (a_maps ch) && pairs_vars_lt lo (a_vis ch) && pairs_vars_lt lo (a_ghost ch)
   && expr_vars_lt lo (a_brk ch) && fd_vars_lt lo (a_fd ch)
   && list_eqb amap_eqb (a_maps cs) (a_maps ch)
   && list_eqb pair_eqb (a_vis cs) (a_vis ch)
   && list_eqb pair_eqb (a_ghost cs) (a_ghost ch)
   && expr_eqb (a_brk cs) (a_brk ch)
   && afd_eqb (a_fd cs) (a_fd ch)
   && Bool.eqb (a_tidset cs) (a_tidset ch)
   && Z.leb (a_totsz cs) (a_totsz ch) && Z.leb (a_ylo ch) (a_ylo cs)
   && Z.leb (a_eager cs) (a_eager ch) && Z.leb (a_abytes cs) (a_abytes ch))%bool.

(* [comment removed for export] *)
Inductive loopctx : Type :=
| LC (lc_head : Z) (lc_next : acs) (lc_lo lc_hi : nat)
| JC (jc_id : nat) (jc_st : acs) (jc_sh : shape) (jc_b jc_lo : nat).
Definition lc_bnd (c : loopctx) : nat := match c with LC _ _ _ hi => hi | JC _ _ _ b _ => b end.

(* [comment removed for export] *)
Definition loop_ok (cs0 : acs) (J : nat) (N : expr) (inv : acs) : option Z :=
  let lo := S J in let hi := nxt inv in
  if (fresh_ok cs0 && Nat.leb (nxt cs0) J && Nat.ltb J hi && fresh_ok inv
      && expr_vars_lt (nxt cs0) N
      && match s_log (a_ss inv) with [] => true | _ => false end
      && Nat.eqb (length (s_regs (a_ss inv))) 32
      && kn_vars_lt lo (kn inv) && maps_vars_lt lo (a_maps inv) && pairs_vars_lt lo (a_vis inv) && pairs_vars_lt lo (a_ghost inv)
      && expr_vars_lt lo (a_brk inv) && fd_vars_lt lo (a_fd inv)
      && forallb (fun r => match r with EVar v => true | _ => expr_vars_lt lo r end) (s_regs (a_ss inv))
      && regs_match_h lo hi [] (s_regs (a_ss inv)) (s_regs (a_ss inv)))%bool
  then match xhi (kn cs0) N with Some nhi => if Z.ltb nhi two64 then Some nhi else None | None => None end
  else None.

(* [comment removed for export] *)
Definition loop_body_state (J : nat) (N : expr) (nhi : Z) (inv : acs) : acs :=
  add_kn inv [KRange (EVar J) 0 (nhi - 1); KRange (esub N (EVar J)) 1 nhi].

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition branch_probe (cs : acs) : option expr :=
  match itab_lookup IT (pc cs) with
  | Some (Branch c rs1 rs2 _) =>
      Some (fst (cond_probe c (sr_get (s_regs (a_ss cs)) rs1) (sr_get (s_regs (a_ss cs)) rs2)))
  | _ => None
  end.

(* [comment removed for export] *)
Fixpoint diff_regs (i : nat) (ra rb : list expr) : list nat :=
  match ra, rb with
  | a :: ra', b :: rb' => if expr_eqb a b then diff_regs (S i) ra' rb' else i :: diff_regs (S i) ra' rb'
  | _, _ => []
  end.

(* [comment removed for export] *)
Definition node_diamond_join (nx : nat) (joinpc : Z) (rs : list nat) (ca cb : acs) : option acs :=
  let hv := nodup Nat.eq_dec (diff_regs 0 (s_regs (a_ss ca)) (s_regs (a_ss cb)) ++ rs) in
  let v0 := Nat.max nx (Nat.max (nxt ca) (nxt cb)) in
  let hi := (v0 + length hv)%nat in
  let regsJ := sr_fresh (s_regs (a_ss ca)) hv v0 in
  let knJ := List.filter (fun K => existsb (fun X => kentry_eqb X K) (kn cb)) (kn ca) in
  let csJ := with_ss ca (mk_ss joinpc regsJ knJ hi) in
  if (Z.eqb (pc ca) joinpc && Z.eqb (pc cb) joinpc
      && forallb (fun r => Nat.ltb 0 r && Nat.ltb r 32) hv
      && Nat.eqb (length regsJ) 32
      && Nat.leb nx0 v0
      && entails_h v0 hi ca csJ && entails_h v0 hi cb csJ)%bool
  then Some csJ else None.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition via_ok (cs js : acs) (lo : nat) : bool :=
  (match s_log (a_ss js) with [] => true | _ => false end
   && Nat.eqb (length (s_regs (a_ss js))) 32
   && Nat.leb nx0 (nxt cs) && Nat.leb (nxt cs) lo && Nat.leb lo (nxt js))%bool.

(* [comment removed for export] *)
Definition node_abstractcell (cs : acs) (b : expr) (n : Z) : option acs :=
  let '(bb, bo) := split_lit b in
  let K := KUnk (SA bb bo) (ELit n) in
  if kunk_covered (kn cs) K then Some (set_kn cs (K :: kn_cutout (kn cs) bb bo (ELit n))) else None.

(* [comment removed for export] *)
Definition respell_ok (k : list kentry) (a e : expr) : bool :=
  match decide_branch k BC_EQ a e with
  | Some true => true
  | _ => (* [comment removed for export] *)
      match erange k (mkAlu ALU_SUB a e) with
      | Some (lo, hi) => Z.eqb lo 0 && Z.eqb hi 0
      | None => false
      end
  end.
Definition node_respell (cs : acs) (r : nat) (e : expr) : option acs :=
  if (Nat.ltb 0 r && Nat.ltb r 32 && expr_vars_lt (nxt cs) e && respell_ok (kn cs) (reg cs r) e)%bool
  then Some (set_reg cs r e) else None.

(* [comment removed for export] *)
Definition sa_of (b : expr) : saddr := let '(bb, bo) := split_lit b in SA bb bo.
Fixpoint hw_apply (k : list kentry) (a : saddr) (x : nat) (found : bool) : list kentry :=
  match k with
  | [] => []
  | KWord a' w v :: r =>
      if saddr_eqb a' a then (if found then hw_apply r a x true else KWord a' w (EVar x) :: hw_apply r a x true)
      else KWord a' w v :: hw_apply r a x found
  | K :: r => K :: hw_apply r a x found
  end.
(* [comment removed for export] *)
Fixpoint hw_val (k : list kentry) (a : saddr) : expr :=
  match k with
  | [] => ELit 0
  | KWord a' _ v :: r => if saddr_eqb a' a then v else hw_val r a
  | _ :: r => hw_val r a
  end.
Fixpoint hw_go (k : list kentry) (bs : list expr) (x : nat) : list kentry :=
  match bs with
  | [] => k
  | b :: r => hw_go (hw_apply k (sa_of b) x false) r (S x)
  end.
Definition node_havocwords (cs : acs) (bs : list expr) : option acs :=
  if fresh_ok cs then
    let ss := a_ss cs in
    Some (with_ss cs (mk_ss (s_pc ss) (s_regs ss) (hw_go (s_know ss) bs (s_next ss)) (s_next ss + length bs)))
  else None.

(* [comment removed for export] *)
Definition node_havoccell (cs : acs) (b : expr) (n : nat) : option acs :=
  let '(bb, bo) := split_lit b in
  let k := kn cs in
  if (fresh_ok cs && Nat.leb 1 n && Nat.leb n 8 && expr_vars_lt (nxt cs) bb && kn_readable segs k k bb bo n)%bool then
    Some (add_kn (bump cs 1) [KWord (SA bb bo) n (EVar (nxt cs))])
  else None.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition STOPS : list Z :=
  [x_imemset A; x_imemcpy A; x_memset A; x_memcpy A; x_memiszero A; x_envscan A; x_pnscan A] ++ stops_more A.

(* [comment removed for export] *)
Fixpoint mk_itab_ranges_acc (rs : list (Z * nat)) (t : itab) : itab :=
  match rs with
  | [] => t
  | (lo, n) :: rs' => mk_itab_ranges_acc rs' (mk_itab_fuel segs n lo t)
  end.
Definition mk_itab_ranges (rs : list (Z * nat)) : itab := mk_itab_ranges_acc rs PTLeaf.

End WithSegs.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition BRK_ASLR : Z := 0x80000000.
Definition NX0 : nat := 10.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition K_RND : nat := 25.

(* [comment removed for export] *)
Definition e_auxb : expr * Z := split_lit e_auxv.
Definition e_atrb : expr * Z := split_lit e_atrandom.
Definition auxw (i : Z) (ty : Z) (v : expr) : list kentry :=
  [KWord (SA (fst e_auxb) (snd e_auxb + 16 * i)) 8 (ELit ty); KWord (SA (fst e_auxb) (snd e_auxb + 16 * i + 8)) 8 v].

(* [comment removed for export] *)
Definition init_kn_with (atr : kentry) (A : atable) : list kentry :=
  [KRange (EVar V_S1) 0xFFFF0000 0xFFFFFFFF; KRange (EVar V_S2) 0 2047;
   KRange (eaddz e_atrandom 16) 0x7fff800000c0 0x800000000000; KRange e_atr8 0xFFFF0000001 0xFFFFFFFFFE7;
   KRange e_sp0 0x7fff80000000 0x7fffffffff40;
   KRange (eadd (escale 4096 (EVar V_S1)) (escale 2 (EVar V_S2))) 0xFFFF0000000 0xFFFFFFFFFE8;
   KRange (EVar V_ARGC) 1 1024; KRange (EVar V_ENVC) 0 256; KRange (EVar V_L0) 0 131071; KRange (EVar V_L1) 0 131071;
   KRange (EVar V_UID) 0 0xFFFFFFFE;
   KRange (EVar V_W) 0 280000; KRange (EVar V_BRK) (img_hi A / 4096) ((img_hi A + BRK_ASLR) / 4096);
   KWr (SA e_sp0 (-8388608)) (ELit 8388608); KZero (SA e_sp0 (-8388608)) (ELit 8388608);
   KWord (SA e_sp0 0) 8 (EVar V_ARGC); KWord (SA e_sp0 8) 8 e_str0; kw_argv1 e_argv1w]
  (* [comment removed for export] *)
  ++ auxw 0 3 (ELit (ph_addr_z A)) ++ auxw 1 4 (ELit (ph_ent_z A)) ++ auxw 2 5 (ELit (ph_num_z A)) ++ auxw 3 16 (EVar V_HW) ++ auxw 4 6 (ELit 4096)
  ++ auxw 5 11 (EVar V_UID) ++ auxw 6 12 (EVar V_UID) ++ auxw 7 23 (ELit 0) ++ auxw 8 25 e_atrandom ++ auxw 9 0 (ELit 0)
  ++ [atr;
      KImg (img_lo A) (img_hi A); KWr (SA (ELit 0) (rw_lo A)) (ELit (rw_len A))].

(* [comment removed for export] *)
Definition atr_entry : kentry := KBlob (SA (fst e_atrb) (snd e_atrb)) (ELit 16) K_RND.
Definition atr_entry_zero : kentry := KZero (SA (fst e_atrb) (snd e_atrb)) (ELit 16).
(* [comment removed for export] *)
Definition init_kn (A : atable) : list kentry := init_kn_with atr_entry A.
(* [comment removed for export] *)
Definition init_kn_zero (A : atable) : list kentry := init_kn_with atr_entry_zero A.

Definition init_regs : list expr := sr_upd (repeat (ELit 0) 32) 2 e_sp0.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition e_bandlen : expr := esub (ELit (2 ^ 47 + 8388608)) e_sp0.
Definition init_vis (A : atable) : list (expr * expr) :=
  [(ELit (img_lo A), ELit (img_hi A - img_lo A)); (e_band, e_bandlen)].

Definition init_acs_of_with (kn0 : list kentry) (A : atable) : acs :=
  ACS (mk_ss (a_entry A) init_regs kn0 NX0) [] (img_hi A - img_lo A) KHI 0 (init_vis A) []
      (vis_cost (img_hi A - img_lo A) + vis_cost BANDLEN) (escale 4096 (EVar V_BRK)) FdStd false.
Definition init_acs_of (A : atable) : acs := init_acs_of_with (init_kn A) A.        (* [comment removed for export] *)
Definition init_acs_of_zero (A : atable) : acs := init_acs_of_with (init_kn_zero A) A.  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ASAN : atable :=
  {| img_lo := 0x10000; img_hi := 0x671000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x4ba64; rw_lo := 0x142000; rw_len := 0x52f000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0xe1ea4; x_imemcpy := 0xe1e28; x_memset := 0x116934; x_memcpy := 0x116530; x_memiszero := 0xe2508;
     x_istrncpy := 0xe23b8; x_sealed := 0x1205f; x_popfree := 0x52a70;
     x_sniff := 0x1414dc; sniff_tab := 0x24f40; sniff_cell := 0x14bf00;
     x_envscan := 0x10d5e4; x_envscan_k := 0x10d5f0; x_pnscan := 0x10d6a8; x_pnscan_k := 0x10d6b4;
     stops_more := [0x506e4; 0x51d08; 0xddd88; 0xee070; 0xee200]  (* [comment removed for export] *); x_hsort := 0 |}.

(* [comment removed for export] *)
Definition ASAN_TEXT_LO : Z := 0x4ba64.
Definition ASAN_TEXT_N : nat := 252263.
Definition asan_init : acs := init_acs_of ASAN.

(* [comment removed for export] *)
Definition BOTH : atable :=
  {| img_lo := 0x10000; img_hi := 0x671000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x4ba54; rw_lo := 0x142000; rw_len := 0x52f000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0xe1e94; x_imemcpy := 0xe1e18; x_memset := 0x116924; x_memcpy := 0x116520; x_memiszero := 0xe24f8;
     x_istrncpy := 0xe23a8; x_sealed := 0x1205f; x_popfree := 0x52a60;
     x_sniff := 0x1414cc; sniff_tab := 0x24f40; sniff_cell := 0x14bf80;   (* [comment removed for export] *)
     x_envscan := 0x10d5d4; x_envscan_k := 0x10d5e0; x_pnscan := 0x10d698; x_pnscan_k := 0x10d6a4;
     stops_more := [0x506d4; 0x51cf8; 0xddd78; 0xee060; 0xee1f0]; x_hsort := 0 |}.
Definition BOTH_TEXT_LO : Z := 0x4ba54.
Definition BOTH_TEXT_N : nat := 252267.
Definition both_init : acs := init_acs_of BOTH.

End APC.
