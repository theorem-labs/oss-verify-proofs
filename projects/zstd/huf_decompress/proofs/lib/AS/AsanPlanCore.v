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
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import PropExec.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import AxSymExec3 AxSymExec3B.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AsanPlanCore () := "C47Corelib7Program6Basics4flipC47Corelib4Init9Datatypes3fstc69OSSVerify5KrLib2AS<AsanPlanCore3APC4vkeyC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C56Stdlib6PArith6BinPos3Pos;of_succ_natC47Corelib4Init5Logic7f_equalC56Stdlib6PArith6BinPos3Pos6to_natK47Corelib4Init9Datatypes3nat02C56Stdlib6PArith4Pnat;SuccNat2Pos7id_succC47Corelib4Init5Logic6eq_indI47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums8positive00C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List9fold_leftC46Stdlib5Lists4List:fold_rightC46Stdlib5Lists4List7existsbC69OSSVerify5KrLib2AS:AxSymExec33AX25sfactC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib7Classes9MorphismsCeq_rewrite_relationC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C69OSSVerify5KrLib2AS:AxSymExec33AX26pt_gssC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib2AS:AxSymExec33AX26pt_gsoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX2;pt_get_leafC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00I69OSSVerify5KrLib2AS:AxSymExec33AX25ptree00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC:live_agreeC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib5Arith8PeanoNat3Nat3eqbC69OSSVerify5KrLib2AS:AxSymExec33AX26pt_getC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01K47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes3orbC56Stdlib5Arith8PeanoNat3Nat8eqb_reflC56Stdlib5Arith8PeanoNat3Nat8eqb_specI47Corelib4Init9Datatypes7reflect00C47Corelib4Init5Logic9False_indc69OSSVerify5KrLib2AS<AsanPlanCore3APC9in_live_tC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC8vkey_injC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib2AS:AxSymExec33AX26pt_setC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02K69OSSVerify5KrLib2AS:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC>live_agree_varC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC9expr_varsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC;expr_vars_tC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS:AxSymExec33AX24expr04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS:AxSymExec33AX24expr06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS:AxSymExec33AX24expr07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS:AxSymExec33AX24expr08C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX28expr_indC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2AS:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics5Riscv5Instr5aluop00I4ELinuxProcessSemantics5Riscv5Instr5mulop00C47Corelib4Init9Datatypes8list_indc69OSSVerify5KrLib2AS<AsanPlanCore3APC5a_brkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC4a_fdC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3sndc69OSSVerify5KrLib2AS<AsanPlanCore3APC7am_baseC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC6am_lenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX26a_baseC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01c69OSSVerify5KrLib2AS<AsanPlanCore3APC4a_ssC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX26s_regsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC2knC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC6a_mapsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC5a_visC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC7a_ghostC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS:AxSymExec33AX25ptree01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02c69OSSVerify5KrLib2AS<AsanPlanCore3APC?live_agree_exprC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC?live_agree_foldC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC9live_varsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC;live_vars_tC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2AS:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib2AS<AsanPlanCore3APC4amap00C1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib2AS<AsanPlanCore3APC3acs00C1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib2AS<AsanPlanCore3APC3afd00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2AS:AxSymExec33AX25saddr00C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC46Stdlib5Lists4List2InI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsC56Stdlib5Arith8PeanoNat3Nat6eqb_eqC46Stdlib5Lists4List>forallb_forallC47Corelib4Init5Logic5proj1C46Stdlib4Bool4Bool;andb_true_rC46Stdlib4Bool4Bool:andb_assocC46Stdlib5Lists4List7forallbI47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C56Stdlib5Arith8PeanoNat3Nat3ltbC56Stdlib5Arith8PeanoNat3Nat3lebc69OSSVerify5KrLib2AS<AsanPlanCore3APC?expr_all_live_tC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APCAforallb_expr_varsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC8all_liveC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC3regC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX29split_litC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC=kn_gc_entry_tC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6filterc69OSSVerify5KrLib2AS<AsanPlanCore3APC6set_knC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC;kn_gc_entryC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC?live_vars_agreeC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX28expr_eqbC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4negbK69OSSVerify5KrLib2AS:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS:AxSymExec33AX26kentry03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APCBexpr_all_live_t_eqC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS:AxSymExec33AX26kentry09C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:filter_extC35stdpp7tactics<f_equal_helpc69OSSVerify5KrLib2AS<AsanPlanCore3APC5cs_gcC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC9cs_gc_refC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01c69OSSVerify5KrLib2AS<AsanPlanCore3APC8fresh_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX26s_knowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX28facts_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B4mkbcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B6mk_kixC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX24s_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX26s_nextC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2AS:AxSymExec33AX29sym_state01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B<sym_execTXBIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX25s_logC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC6log_ddC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B6carryKC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC5mk_ssC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC7with_ssC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX2:sym_execTXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX25carryC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC69OSSVerify5KrLib2AS;AxSymExec3B4AX2B?sym_execTX_knowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B9carryK_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B?sym_execTXBI_eqC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC9run_blockC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC=run_block_refC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2AS:AxSymExec33AX28sidecond00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2AS:AxSymExec33AX26sentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2AS:AxSymExec33AX29sym_state00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2AS;AxSymExec3B4AX2B4bctx00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC?kentry_apart_bBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC>kentry_apart_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX2>ranges_apart_xC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3ltbC69OSSVerify5KrLib2AS;AxSymExec3B4AX2B?ranges_apart_xBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2BCranges_apart_xB_eqfC1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityK47Corelib7Numbers7BinNums1Z01C69OSSVerify5KrLib2AS:AxSymExec33AX25two64C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC@kentry_apart_bpBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC?kentry_apart_bpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX2>ranges_apart_pC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B?ranges_apart_pBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2BCranges_apart_pB_eqfC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2AS:AxSymExec33AX25sprep00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC:kn_unfillBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC9kn_unfillC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC6kimg_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B9mk_sprepBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B5bc_fkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX28mk_sprepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B:bc_fk_mkbcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B=mk_sprepB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APCDkentry_apart_bpB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC>kn_unfillB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC:kn_unfillMC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC7havoc1BC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC6havoc1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC5kwr_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B:kzero_cutBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B:kfill_cutBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B9kunk_cutBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX29kzero_cutC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX29kfill_cutC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX28kunk_cutC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B>kzero_cutB_eqfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B>kfill_cutB_eqfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B=kunk_cutB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APCCkentry_apart_bB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC8havoc1pBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC7havoc1pC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC9kn_havocBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC8kn_havocC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC<havoc1pB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC=kn_havocB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC9kn_havocMC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC8kwr_cutBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC7kwr_cutC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX24kcutC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B5kcutBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B9kcutB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC8cutout1BC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC7cutout1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC<kwr_cutB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC9cutout1pBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC8cutout1pC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC:kn_cutoutBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC9kn_cutoutC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC=cutout1pB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC>kn_cutoutB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC:kn_cutoutMC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC7kreadZBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC6kreadZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX2;know_lookupC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib2AS;AxSymExec3B4AX2B<know_lookupBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B@know_lookupB_eqfC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2AS:AxSymExec33AX24lres00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC8kread8eBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC7kread8eC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC:kwritableBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC9kwritableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B4xloBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B8xinsideBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX23xloC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX27xinsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B8xloB_eqfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B<xinsideB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC<kwritable_xBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC;kwritable_xC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B4xhiBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX23xhiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B8xhiB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC8kzero_xBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC7kzero_xC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC8kfill_xBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC7kfill_xC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3eqbK47Corelib7Numbers7BinNums8positive03c69OSSVerify5KrLib2AS<AsanPlanCore3APC<off_image_xBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC;off_image_xC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC6img_loC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC6img_hiC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC7flat_xBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC6flat_xC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B;base_rangeBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX2:base_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B?base_rangeB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC8len_eqbBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC7len_eqbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX27lin_ge0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B8lin_ge0BC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B<lin_ge0B_eqfC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib2AS:AxSymExec33AX26xtermsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC=page_alignedBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC<page_alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX26ealignC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B7ealignBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B;ealignB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC5xlo1BC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC4xlo1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX2:lin_brangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX26zlit64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B7erangeBC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC69OSSVerify5KrLib2AS;AxSymExec3B4AX2B;lin_srangeBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX26erangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX2:lin_srangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B;erangeB_eqfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B?lin_srangeB_eqfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B;lin_brangeBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B?lin_brangeB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC5xhi1BC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC4xhi1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3minc69OSSVerify5KrLib2AS<AsanPlanCore3APC4xb2BC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC3xb2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC5deandC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC9xlo1B_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC9xhi1B_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC5xlo2BC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC4xlo2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC8xb2B_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC5xhi2BC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC4xhi2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC<kread_bytesBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC;kread_bytesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC;kreadZB_eqfC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indc69OSSVerify5KrLib2AS<AsanPlanCore3APCAkread_bytesB_eqf'C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC@find_containingBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC?find_containingC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC6is_fogC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC7am_kindC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC9mkind_eqbC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4findi69OSSVerify5KrLib2AS<AsanPlanCore3APC5mkind00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC:shadow_ofBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC9shadow_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX25mkSrlC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC:shadow_offC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC4eaddC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B6mkSrlBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS;AxSymExec3B4AX2B:mkSrlB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC8end_hi2BC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC7end_hi2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC?shadow_band_okBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC>shadow_band_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC9lit_entryC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divc69OSSVerify5KrLib2AS<AsanPlanCore3APC;flat_xB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC>shadow_ofB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC<end_hi2B_eqfC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib2AS<AsanPlanCore3APC5mkind02C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC5LS_LOC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC6LS_LENC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC6MID_LOC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC3KHIC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC5HS_LOC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC5TWO47C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC=shadow_factsBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC<shadow_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APCDfind_containingB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APCCshadow_band_okB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC3nxtC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC<expr_vars_ltC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC7a_eagerC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC8a_abytesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC8vis_costC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC2pcC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appc69OSSVerify5KrLib2AS<AsanPlanCore3APC7a_totszC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC5a_yloC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC8a_tidsetC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib2AS<AsanPlanCore3APC3acs01C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APCAshadow_factsB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC7vis_addC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC;vis_add_refC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powc69OSSVerify5KrLib2AS<AsanPlanCore3APC6add_knC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC;node_shdisjC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC?node_shdisj_refC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC7reg_litC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC7page_upC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC8mmap_lenC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC<mmap_len_refC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC<inside_mapsBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC;inside_mapsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC8in_bandBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC7in_bandC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC<band_coveredC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC;safe_rangeBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC:safe_rangeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC@inside_mapsB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC<in_bandB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC5e_sp0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC7STK_OFFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC7STK_LENC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC=grant_keep_bBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC<grant_keep_bC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC?safe_rangeB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC@kn_grant_filterBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC?kn_grant_filterC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC9kimg_clipC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APCAgrant_keep_bB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC4esubC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC6pd_okBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC5pd_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC4e_pdC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC:kn_rezeroBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC9kn_rezeroC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC>kn_rezeroB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC:kn_rezeroMC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC:fixed_argsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC=fixed_in_argsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APCAfixed_in_args_refC1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib2AS<AsanPlanCore3APC<fixed_in_arm00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC6TOPMAXC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib2AS<AsanPlanCore3APC5mkind01C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib2AS<AsanPlanCore3APC5mkind03C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib2AS<AsanPlanCore3APC5mkind04C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC9budget_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC6rekindC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC=mmap_fixed_inC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APCAmmap_fixed_in_refC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX26sr_updC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC:dest_lfactC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC:dest_rfactC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib2AS<AsanPlanCore3APC4amap01C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC=replace_entryC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APCCmmap_destroyed_withC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APCGmmap_destroyed_with_refC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC:ENOMEM_RETC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib2AS<AsanPlanCore3APC5mkind06C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC=node_mprotectC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APCAnode_mprotect_refC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC;amap_matchBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC:amap_matchC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC<len_eqbB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APCApage_alignedB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC<kzero_xB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC?amap_matchB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC;node_munmapC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC?node_munmap_refC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC=kn_unfillM_eqC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC5eaddzC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC;stack_sideBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC:stack_sideC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC8vis_hereC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC?stack_sideB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC:node_unvisC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC>node_unvis_refC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC7ret_litC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC:after_callC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC8kimg_cutC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC@off_image_xB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC@kwritable_xB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC<summary_fillC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC@summary_fill_refC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC<kn_havocM_eqC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC;copy_factsBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC:copy_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS:AxSymExec33AX2>zbytes_le_to_ZC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC<kread8eB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC@kread_bytesB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC@copy_factsB_eqf'C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3mulC47Corelib4Init3Nat3addC47Corelib5Lists7ListDef3seqc69OSSVerify5KrLib2AS<AsanPlanCore3APC<kblob_prefixC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC?copy_factsB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC<summary_copyC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC@summary_copy_refC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC;after_call2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC3NCSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC;x_memiszeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03c69OSSVerify5KrLib2AS<AsanPlanCore3APC>kwritableB_eqfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC;summary_mizC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC?summary_miz_refC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC8img_covBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC7img_covC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC:x_istrncpyC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC8x_sealedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC@summary_istrncpyC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APCDsummary_istrncpy_refC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC8SEALED_WC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2AS<AsanPlanCore3APC6nt_setC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthc69OSSVerify5KrLib2AS<AsanPlanCore3APC6nt_getC1?~~~~~~~~~~~~~~~".
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
Definition TOPMAX : Z := 0x7fffff800000.
(* [comment removed for export] *)
Definition KHI : Z := 0x10007fff8000.
Definition MID_LO : Z := 0x7fff7000.
(* [comment removed for export] *)
Definition FLOOR : Z := KHI.
(* [comment removed for export] *)
Definition MBASE_MIN : Z := 0x154555557000.
(* [comment removed for export] *)
Definition STK_OFF : Z := - 0x800000.
Definition STK_LEN : Z := 0xC00000.
(* [comment removed for export] *)
Definition STK_VLEN : Z := 0x800000.
(* [comment removed for export] *)
Definition STK_WTOP : Z := 0x800000000000 - STK_OFF.
Definition STK_WMAX : Z := 0x800000000000 - STK_OFF - 0x7fff80000000.

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
Definition V_SP : nat := 10.    (* [comment removed for export] *)
Definition NX0 : nat := 11.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition e_sp0 : expr := mkAlu ALU_ADD (mkMd M_MUL (ELit 32768) (EVar V_S1)) (mkAlu ALU_ADD (mkMd M_MUL (ELit 16) (EVar V_S2)) (mkMd M_MUL (ELit 4096) (EVar V_SP))).
(* [comment removed for export] *)
Definition e_pd : expr := mkAlu ALU_ADD (mkMd M_MUL (ELit 32768) (EVar V_S1)) (mkMd M_MUL (ELit 4096) (EVar V_SP)).

(* [comment removed for export] *)
Definition PID_MAX : Z := 4194304.

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
  x_maxva : Z;
  (* [comment removed for export] *)
  x_envscan : Z; x_envscan_k : Z; x_pnscan : Z; x_pnscan_k : Z;
  stops_more : list Z              (* [comment removed for export] *)
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

Definition salt2 (a b : shape) : shape :=
  match a, b with SNil, _ => b | _, SNil => a | _, _ => SAlt2 a b end.

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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01Hh11ni001nh21ah31bh41tp;1p;3p;6p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1000NR1p4p710p8P0P1p4p7210p8g000kj16Tg001hj30Tg002Bj12Tg002ij64Tg003FR1j13Tg003hj11Tg004Gj17Tg0050j65Tg005LR0g005kR2f1R3#6f0R4#630P2P0P1f2#2R1%23R3P4E4%31R1%33500P0f3R3#2#3R2A0042X10P4%13R5%73R3E5A0051P0P2f5#1R2=004X10P4P5P3E5f4#1R3=005P0P0P0P0P4f6P4n0110000020010000X40P2P3P4E4b0b0b0W0X30W2o"). Qed.
Lemma live_agree_var : forall acc t n,
  live_agree acc t -> live_agree (if existsb (Nat.eqb n) acc then acc else n :: acc) (pt_set (vkey n) tt t).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bi001bh11Eh21ei011eh31oh41vh51Hh62HKh72NEh83acch91ni021nh:2n0h;1ri031rh<1si041sh=1ti051ui061xp;1p;2p;3p;6p;4p-1R0p1006PR1p4p710p8P0P1p4p7210p8P0p1006lR1p4p710p8P0P1p4p7210p8P0p1007Ip4p7210p8P0p1007gp4p7210p8P0g008FR0p4p710p8p1008bp4p70R1p1009^p4p710p8P1p100:Ap4p710p8P1p100:mR2p4p7210p8P1P2p4p710p8P1p100;ap4p710p8P1p100<Qp4p710p8g00=IR1p4p710g00>FR2p4p710R3p8g00>dR4p4p710P3p8p100?ap4p710P3p8g00@cj1RTg00ACj1QTg00BAj2ATg00CDj2ETg00Cgj19Tg00D@R3j2MTg00D`j11j2>Tg000kj14Tg00E@j37Tg00F=R5j1PTg00F_j2OTg00GAj2=Tg001hj35Tg00G[j2?Tg00H8j1KTP2j6<TP1j4JTg00H]j2ITg00IBR1j2HTg00Iej2GTg00JDj2@Tg0050j6FTg00KFj3LTP4j6DTP0j3BTg00LGj3NTg00Lgj4CTg005LR0f1R4f0R235p=6AB042p=0AN042p=2g00MdR6P4g00NDR7P2CCp=:g00NdR8f2R9=B04;52p=3A5842p=8g00ODR:9582p=;%R0R;%Q61A941E291629R<%9<'MP3f3R3,64R<%9<%19R<P8P;f4R=#1R>f6R?'0P?12=?n0100000020000P5P6P8%4=f5R@':%49RA576P:g00OdRBn1011060002101050033P2169=RCP0P@%12RDP8P;%1?REf8RF'0RGPF12?FRHn0100000020000RIP5P6P8%4?f7RJ':%42576P:PBn1011060002101050033X40%P6RK1O67P5P6P8P2P:PBn10110600021010500RL93EIX3K%1@RE/0JRMP81=8218G2P8%1FRGf:RN;32f9RO#1RPP8P;P4f;RQ12OQn0100000020000'0#;]1P4%1J/0ORR#;P2W1A58RBP8P:10PQ,?2#;X081=8:1>FF%KFE<12FN,0G#;eW1n0110000020000P2O1b1b0%4@RN/:?RQ=76NP6PNP7P?CJE<P3P2E<W2P2O1%9CPK%43RC976?RP10>IRI/8LX3KP8%13RK/0J18I2X08PMP8P8P8P;P2PO12JOn010000002000010EO53EP210>FRE,=81I=?16=?1>=?'H1>@JP8P116?Ff<,0GRG,?4/8GP416JORO1?:G/8GP@P2O1'GW2P2O1%9O1=8GW:P2O1n10210010300021010110102b0b;A3>HEen0110000020000b01@?3P=P3O1EFP8P;PMPJ12@Jn0100000020000P5P6P8PPP:PBn1011060002101050053KeA76QCP6PCPNP7P?g005k?5CNRCP4AL=?2O1W6%9CeEDE<W7P2O1n200110400021010111102b<P8P;10<=P=129=n01000000200001:A3/@253DeX40P8P;%14/03P31243n0100000020000%44/:9'AeW5X90W=W8o"). Qed.
Lemma live_agree_expr : forall e acc t, live_agree acc t -> live_agree (expr_vars e acc) (expr_vars_t e t).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h03acch11th21Hh34IHe1h44IHe2h52e1h62e2h72oph81eh91nh:2sxh;3IHeh<1ih=1kh>2loh?1zp;1p;2p;4p;3p;:g00@cj1?Tg00ACj1>Tg00BAj23Tg00PDj1=Tg00QAj47Tg00RHj16Tg00SEj21Tg00TGj22Tg00UKj35Tg00VHj34Tg00WEj38Tg00XBj39Tg00Y?j4<Tg00Z<j4:Tg00[9l:;Tf3R0f2R1'1f1R2f0R3'2'3p=0g00\8R4g005LR5#?R6g00Md#>R71323R8P0P1P0P2C0[]1]0R9X84g00]5R:P3%=0R;P1P;P2C0eX28X17X06W?P1P2P0P3C7%60R;P1P;P2C0eX28X17X06X95g00]SR;f5R<f4R=/1112=2P0P1P2P3O3R>O3R?f7R@f6RA;5=RBP1PBP2C0eX28X17X06X49X64X39X54W7P?A4@A=RBP1PBP2C0eX28X17X06X49X64X39X54X7;g00^?R;P?A8@A=RBP1PBP2C0eX28X17X06X49X64X39X54W7P?A9@A=R?P1P?P2C0eX28X17X06X49X64X39X54X7;g00NdR;P>P@PAP<P=C<R@P1P@P2C0eX28X17X06X;9X84X95X>5W:P3PAP<P=P0C:R0P1P0P2C0eX28X17X06X95X<:X=5X:;P3M:;W8o"). Qed.
Lemma live_agree_fold : forall (X : Type) (f : X -> list nat -> list nat) (g : X -> ptree unit -> ptree unit) (l : list X) acc t,
  (forall a acc t, live_agree acc t -> live_agree (f a acc) (g a t)) ->
  live_agree acc t -> live_agree (fold_right f acc l) (fold_right g t l).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01ah13acch21lh31th41Hh53Hfgh62IHh71Xh81fh91gh:1rp;1p;2p;5p;3p200R0g00^kR1p4p710p8P0g007gR2p4p7210p8g00@cj12Tg00ACj15Tg00BAj21TP2j50Tg00LGj34TP1j53Tf0R1g005L#2R2P2[[f1R3g00Md#5R4P4[[f2R5#2f5R61131f8R7f3R8P5O2f7R9P8P3O2'1[^34^12]01153P9%29P2P7P9f4R:P1D0P4P7f6R;P8P1D0'1W2P1%27P2f9R8P7P6P1D0P4P8P9P:P1D0'1P:P5P2f:R<P8P;P3D0P4P<P7P6P3D0P1O4P2P<P8P;A4<53R5D0P4P<P7P6P5D0'1eW6W:X09P:D3W4W5X34X12W2W9W8X70o"). Qed.
Lemma live_vars_agree : forall cs, live_agree (live_vars cs) (live_vars_t cs).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h03acch11ai001ah21ni011nh31th47a_base0h56a_off0h61ki021kh71mi031mh81vi041vh91Hh:1Ki051Kh;1ci061ch<1ei071eh=2hii082hih>2loi092loh?1ph@1wi0:1whA2A0hB2A5hC2a1i0;2a1hD2a2i0<2a2hE2cshF3leni0=3lenhG2n1i0>2n1hH2n2i0?2n2hI1oi0@1ohJ3offi0A3offi0B6a_basei0C5a_offi0D1li0E1si0F1ui0G1xp;1p;2p;3p;5p;6p;4p;8g00_Mj1[Tg00@cj1ZTg00`Kj1GTg00aHj2RTg000Nj3KTg00ahj3ITg00bEj1FTg00cEj1ETg00dDj1:Tg00eAj1QTg00eaj1<Tg00f^j1;Tg00g[j1ATg00hVj1@Tg00iUj1?Tg007gj50Tg00jSj1>Tg00ACj1WTg00kSj1VTg00F=R0j1UTg00lQj1TTg00D`j1HTg008Fj3DTg001hj3CTg00GAj2STg000kj1PTg00E@j3NTg00?aj2MTg00>Fj6LTg00JDj2OTg00BAj25Tg00SER1j22Tg00TGR2j21Tg00m3j43Tg00n;j2JTg00o9j89Tg010Aj1YTg011Cj1XTf2R3f1R4f0R5'2'2p=4P3g00\8R6P1P4P5D0p=Bf3R7g012GR8P3P4P5D0p=8P7g013FR9P3P4P5D0p=71145,13p=6P3P6P2P4P5D0p==g014E%[5g015CR:g005LR;#ZR<%G5R=P<1R66R>AK664R?AI664R@;45X0<X?>RAP<P>PAP<%F4RB%E4RC;45X0<X79RDP<P8P<P4%:3RE?457%:4RF?453RGA4E47RHP3P3P7PGf4RIPHPGn01105000:3010010:1042010010130100101102201091082010710330107109108201001014010;10>10<10?3010010110620100101X0<X:8RG%Q;RH%<5#;RJ5B<%A5RKC8%@5RLC7%?5RMD0%>5RND0ROP<P>PAP<P>PAP<PDP<PG%<7#;RP9B<H%A7RQC8%@7RRC7%?7RSD0%>7RTD09445POn0110G0003003010210D10@00P:g00MdRO#WRUP=PUP>A6?@5X0UX?>R@PUP>P@PUA6BC5X0UX79RCPUP8PUP4A6E57A6F53RBA6E47R?P3P3P7PBPIP?PBn01105000:3010010:1042010010130100101102201091082010710330107109108201001014010;10>10<10?3010010110620100101X0UX:8RB%VOR?==UJPKC8PLC7PMD0PND0RNPUP>P@PUP>P@PUPCPUPBA=U?PPQC8PRC7PSD0PTD09645PNn0110G0003003010210D10@00%UORN%TOg00NdRT%H4=D;HP0POPTP5g00ODg00OdR0n10110G00021010F003CXIN1ST0%P5R09NO?1MO0EL%H5=D;H1O?55CTeX8;15H?RTePT1545RT%GIR0P:P:P:P<P5PIf7RO,25RN,24PIn0110G0003003010210D10@00P:PUP5P7f6RS,15RR,14P7n0110G0003003010210D10@00'5P5P4P4f9RQ,25RPf8RM,15RLP5PQPMPOC3C3XJ6XF6X6;P3P4P5O3P4n011000003003010210=10A00b1W9X3UX0<P:P<P0P3f5RK,25RJ,24P3n0110G0003003010210D10@00P:PUP0P4115IR0,14P4n0110G0003003010210D10@00'5\T^3U^0<P5P<P>PAP<P>PAP<PDP<PG%<3#;R:9B<HR=%A3RVC8RW%@3RXC7RY%?3RZD0R[%>3R\D0PUP>P@PUP>P@PUPCPUPBA=U?:R]PVC8R^PXC7R_PZD0R`P\D0P>PAP@P\P[P`AK667AI667R`/2311`4P`P3P4P5C3C3VTX3UX0<X1>R`P>PAP@PZPYP_P`P9PDPCPXPWP^%F7%E7R^/2311^4P^P3P4P5C3C3VTX3UX0<X19P8PGPBPVP=P]P8P8P<P5A4E5S12FJRJA4E4SR]PKPKPSPJPOP]PJn01105000:3010010:1042010010130100101102201091082010710330107109108201001014010;10>10<10?3010010110620100101P8PUP5A6E5K11F0R0A6E4KRJPIPIPKP0PSPJP0n01105000:3010010:1042010010130100101102201091082010710330107109108201001014010;10>10<10?3010010110620100101'5P7g016AR0P012EP11EL'5^86^@;P5g00]5RL1J73#:RPf<RJ,25f;RK,15P5PJPKf:R]C3C3X86X@;W5X46P4P5O2n0110E00012010B10CW1P3P4P5O3P012FN11FR'5^26P51J34#:125]115QP5P]PQPMC3C3X26X5LX46P4P5O2n0110E00012010B10CX10P4P5O2RRP0A4E4QA6E4M'5RE^6;^26P5PP124J114KP4PJPKP]C3C3R]X6;X26X5LX46P4P5O2n0110E00012010B10CX10P3P4P5O3PIX=LX>LP4P5O2PIX7LX<6P4P5O2PSX=LX>LX<6P3P4P5O3PRPMXH6XD0XG6XC0P7P3P4P5O4P0PE^;L^26P5P]X;LX26X5LX46P4P5O2n0110E00012010B10CX10P3P4P5O3PRn01102000:3010010:1042010010130100101102201091082010710330107109108201001014010;10>10<10?3010010110620100101X9TX3UX0<X18P6P1P2P:PHP?P7P3P4P5C3VTX3UX0<X16P4G9G9G9G9G9O3bBbAC3%Y5%X5'5eWEo"). Qed.
Lemma forallb_expr_vars : forall P e acc,
  forallb P (expr_vars e acc) = (forallb P (expr_vars e []) && forallb P acc)%bool.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h03acch11bi001bh21xi011xh31Eh41nh51Fh61Hh74IHe1h84IHe2h92Pnh:1eh;2e1h<2e2h=2oph>2Hxh?1Ah@1ChA2ExhB1fhC1lhD1mhE2sxhF3IHehG1PhH1ihI1khJ2lohK1zp;1p;2p;3p;6p;7p;4p;:g00@cj1LTg00SEj27Tg00eAj1XTg00PDj1WTg00D`j1>j29Tg00LGj3@Tg017?j21Tg001hj33Tg008FR0j3FTg017]j3BTg0184R1j2=Tg018OR2j2ATg018ij3VTg019Lj2UTg019oj3TTg01:Rj6QTg0050j6Jj7PTg00Iej2ITg00GAj2HTg01:mj1OTg00RHj1NTg01;Lj3RTg00UKj3STg00VHj3_Tg00WEj3^Tg00XBj3]Tg00Y?j4\Tg00Z<j4[Tg00[9l:ZTg01;jj36Tg00>Fj6YTg005LR3f1R4f0R536p=2g00NdR6f4R7f3R8563f2R9=634/1533p=EA6394/15p=G1H65p=<f6R:f5R;/7756317949638/15536p=8AF345p=:A3645p=4g00ODR<9365p=011459369p=Dg00OdR=9365p=CA6394=365p=KAB345p=5P6P7P8P9P4P5EYp=;17459639p=?17949638/15p=MP6\3g00\8R>%L3R?P81745R@P8%X3RA,74RB1285RCDE]0X:>g00]5RDAG8AC#<P8%W4REP5P8PEPAPCF8eX0?WK%>4/:5P6%<5RE%>9/:4/45P6%>7RF/:8/45f7RGP6P?P4P7A@3;7n0100000020000PGP6P?%>;/:APAA@3;An010000002000012G7RHDE]3P4%>8/:9RI#0P:P7O1RJ115HRK,4HX16PJP6PEPGP;O1RL/45P6f9RMPGO1/45f:RN/2GRO?D4O]9P4f8RPP:O1RQ#012M:RR,1<#<W9%CQPRP6PE14O5P6f<RO?KM5%C4]5P4f;RM/2PRE#0A36<=P0p4p710R0P6\5RQ%L4RSP1AF945#0AB759P8P5O1#0'=X28,A8[RTAB854P9P5O1#0'=X29,A9AF894#0RU[AB;58P7P5O1#0'=X27,A7\UAV945P4n2001000000120000000WCWBW?PT^CS^BQ^?0P5P3%>MPNPGO4155M19O5#0'=X23,A3P2P3155Of=RO/95#0'=X23g01<FR2P5f>,55f?RM/95#0'=P1154Mf@/94#0P2P5fARM,58fC/97#0P11945#0A3394[R1A33451994#0RN[A3389\N1U45P4n2001000000120000000XD3X43P1^D3^43P5fER1P:P4O3A331:P3fFRN155NP2]>X2315N1fIR1/2N#0fHR0,55fLP4O1#0[^23[fGRQ,55fKP4O1#0[^23fJRS/2Q#0[AT31NPOPQP5EQP1PQO1#0P6PSP0O1%05X16P5P=PMEJA36=<P6P=P6p-0P5P2g01<cn0110000020000X:6g01=?P<P5EJP21I25b6b@b@W>PGP5P8FPbAb6WAW>P4P5O2n2001000000120000000W6X23P4P5O2n2001000000120101000b3b6'IW5%CE1H6=W5n0110000020100P5O1b5b1ADR=ReW9n0110000020001P5O1b9b111J<R<%OJRRD;12:8R=P6P?1:FAPAA@37An0100000020000=G:=RF'4eW3%CIPJ11LH/4KX1611J=#<P<PRD;A@378=K:FeW3n0110000020100P5O1b3b1P8%N4RFP5P8PFPAPCF8eX0?X43g00]SRCP7P@P7PB1275DE^0?RFP:P@P:PB12:5RBDE^0?R@A?G7ARR1795R<,2GR='1PPP;178ARJ12P4RKCMRL,45X16179ARH,2GRI12G5RE'1R2A?P;ARM/15/4LX1611RIRL12PJRJ/1K,1M?D5KX1611LERL11MJ=D5KX16%<L11R2ARRIED;A?G7HP8PHO1D;P=P4P5O1R=D;A?G7<P8P<O1D;R<PGAS;79RHP5PGPHPAPEF8eX0?W8X<>W7X;>W=P<PGA_;79RHP5PGPHPAPEF8eX0?X8@X<>X7FX;>X=Cg00^?RCP<PGA^;79RHP5PGPHPAPEF8eX0?X8@X<>X7FX;>W=P<PGA];79R<P5PGP<PAPEF8eX0?X8@X<>X7FX;>X=CP=PGP;P7P8P9C\R;P5PGP;PAPEF8eX0?XF@X:>X43XJ3XE6AG:AB#<P:P7P8P9P4C[R4P5P:P4PAPBF8eX0?X43XHDXI3XE6P5M:ZW:WGo"). Qed.
Lemma expr_all_live_t_eq : forall acc t e, live_agree acc t -> expr_all_live_t t e = all_live acc e.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h04IHe1h11bi001bh21vh34IHe2h42e1h52e2h62oph71eh81nh92sxh:1Hh;3IHeh<3acch=1ih>1kh?2loh@1thA1zi011mi022m'p;1p;2p;6p;3p;4p;:g00@cj1STg00ACj1RTg00BAj2JTg01=[j2@Tg00D`j1>Tg00G[j20Tg00eAj1ITg00SEj26Tg00GAj2;Tg00PDj1ATg017?j23Tg01>;j2=Tg01:mj1QTg00>Fj6:Tg00JDj2PTg0050j6OTg00RHj1NTg01>[j27Tg001hj39Tg01?cj3FTg00UKj3GTg00VHj3HTg00WEj3ETg00XBj3KTg00Y?j4LTg00Z<j4DTg00[9l:CTg01@mj2MTg008Fj3BTg01;jj3<Tg005LR0f1R1f0R23Bp=1A<012p=2g00NdR3f2R4/71;92p=8f4R5f3R6'716129<04593p=5A9312p=416129<04p=?%S0g00Md#Rg00\8R71J41p,3nx0R8,@2R9%>2R:f5R;'1'0X20R<%I0R=,62R>'29862X77g00]5R?g00ODR@,;3RAP6%A2RBP<PBP=D5eWAP311:5RBP3P31@18RCP@P2n0100000020000%>1/1;RD,0C/3@'4X13P3P0P3P8g00OdRC1=12n0110100020010102/0BREP3P3P0P3P8PC1=42n0110100020010102RFP@PDn0100000020000/42X13P9P3P3P3P3P0P3P8PC1=62n0110100020010102R8P@%>4f6RG'1RHn0100000020000108H'4P210FD,;3RFPFn0110000020000b113E@%QEE:P3P3P9P@PBn0100000020000109B/3@'4e1P62P1P2O1EOP6%N2RBP<PBP=D5eX80g00]SRB11:G,09X20/2>9852R<f8RE,1:,09X20RF/2>98G2R>P3f9RD,1:,09X20RH166=R8'2RI161=RJ,2HRK'3P3P317E5RL17E4REPCn0100000020000/42X13P3PIP3P3P2PEPCn0100000020000f:,1:,09X20RE165=RM'2RNA?E4='3RE'4X13P3PKP3P3PNP2PCn0100000020000/4EX13PIP3P3A8D;2P3P3P1f<,1:,09X20/2MRMPCn0100000020000131M'4]0P2A93L@f;,1:,09X20/28R8,3@,;3W0A93LC13C8,;3W0n0110000020000P6O1b1f7R8/71P2E:1786P4E:A?H6JAFH6JE:RJP8AG561RCPHPCP=D5eW3X57W0X47W6PJP8AH561RCPHPCP=D5eX3>X57X0<X47X6Bg00^?RBPJP8AE561RCPHPCP=D5eX3>X57X0<X47W6PJP8AK561RJPHPJP=D5eX3>X57X0<X47X6BP2P8P5P6P4P1CLR5PHP5P=D5eX;>X77X80X?0X93PAPGP6P4P1P2CDR2PFP2P=D5eX80X=?X>0X93P1M:C1M619841eW:W7W@W<o"). Qed.
Lemma cs_gc_eq : forall cs, cs_gc cs = cs_gc_ref cs.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bh11ai001ah22kkh31ni011nh41lh51ci021ch61ei031eh72hii042hih82loi052loh91vi061vh:1wi071wh;1Hh<1Kh=2a1i082a1h>2a2i092a2h?2bkh@2cshA1ki0:1khB1mi0;1mhC2n1i0<2n1hD2n2i0=2n2hE1pi0>1phF3spbi0?3spbhG3spki0@3spki0A2a0i0B6a_basei0C5a_offi0D2b0i0E1ii0F2k0i0G2k1i0H2n0i0I2opi0J1si0K2sxi0L1xi0M1zp;1p;2p;3p;4p;5p;8p;6g003hj1MTg01Anj2`Tg01Bjj1STg00aHR0j2PTg011Cj13Tg01Cjj3Jj4YTg00g[j1FTg01E0j3:Tg01EKj2Ej1_Tg010Aj14Tg01FJj3Bj4ZTg001hj3<Tg00@cj1NTg00GAj2ATg01GNj1WTg00BAj2VTg01HVj3HTg01IUj2@Tg01JTj1UTg01K4j2>Tg01KQj2?Tg017?j20Tg01Knj1=Tg00n;j2DTg01LLj2GTg01MKj3CTg01NJj2RTg01@mj22Tg01>[j25Tg01OIj48Tg01PTj2OTg01QSj3QTg01RRj2KTg00dDj1;Tg01SQj4TTg01TPj3LTg01UOj2ITg01VNj5^Tg01Vmj8]Tg01WJj1\Tg01XHj1XTg00>Fj6[Tg00NdR1f7R2f6R3f5R4f4R5CYf3R6f2R7f1R8f0R9CZ3<p=11A19p=6A<189p=7P1P5P6P7P8P9E[p=9g014ER:g01YJ#M#M,`9#Sg00\8R;g00]5R<'PP0P;P<P0P;P<P:P9g012GR=%359J89%F5R>3:,E5n200110L00012010?10@P0P;P<P:P9%459B89=:=>,E5n200110L00012010?10@5<:P9%N=R>P:%_4R0P0%349J89R?%F4R@5:=%449B89R4=:=@P:\>/A0P=P?P4%W3%43%33'VP=P5P6f8R4#3P9P5P6%44P9G1P8g016AR?P?g005LR0f:R>f9RAf>RB#3RCAH789RDP>PA%4BREPDG1^9;]:P9f=RD,@6%U8,>7f<RF'?'0#=#6PDPFfARG#3RH1D67RI?H89RJPDPF%4GRGPJG1eX9;X:0X2<X0;P8P9O2n0110J00012010B10CW1P7P8P9O3P?P4P2%3FRJ1G89RKP4P2%4FRLPKG1^3;P9P;P1P91@6F1>79f;RK'?'0#=g00ODRMPMPMPMPMPMPMn0110H000810101101013010I10A10D3010I10A10D3010I10A10D3010I10A10D4010K1051011034010K10F10E101#6RNPKP>f?RO#3RP1D78RQ/G9RRPKP>%4OROPRG1eX4;X2<X0;P8P9O2n0110J00012010B10CX1?P8P9O2P?P>PAPCAC789RRP>PAPEPRG1^A0^3;P9P;P1P81@5B1>69/?D'0#=RBPMPMPMPMPMPMPMn0110H000810101101013010I10A10D3010I10A10D3010I10A10D3010I10A10D4010K1051011034010K10G10E101#6PDPFPHACI89RRPDPFPGPRG1eX?0X4;X2<X0;P8P9O2n0110J00012010B10CX1?P7P8P9O31A1MR0P2P3%3KRR1R89RSP2P3%4KRTPSG1eX7<X8<P8P9O212T8RS12L7,79X01%6S15R8PTPRP8P5C8D9P2P3PR1O89RRP2P3PTPRG1eXB<X6;P8P9O2%4DRR/27RT12E6,79X01%6T%3DRT/57PRPTP7P3C8D9PAP4PTAQ789RTPAP4PRPTG1eX7<X8<X6;P7P8P9O3P?P4P2PJ1K89RTP4P2PLPTG1^3;P9P0PKP>PP1KQ9R0PKP>POP0G1eX3;X2<X0;P8P9O2n0110J00012010B10CX1?P8P9O2%;6R0,2ORTf@RR#3R3/56,09%;7RS,53RU'01538R3'0%4RRR%;5'2R512R6'0RV12RS'0RS12R8'0RR'7X0112O7RW1059/0U/03/7RX01%;8RU,2OR510V9/03/7RX0112O9R310S9/7RX0110TW/05/03#615P9POPPP9P4C8D915PUPOPPPUP4C8D915P7POPPP7P4C8D915P0POPPP0P4C8D9PKP>PPP6P7P8P9CTR0PKP>POP0G1eXD;X>?XC;X=?P6P7P8P9O4P?P>PAPCAL789RCP>PAPEPCG1^5<^3;P9P;P1P8PBPMPMPMPMPMPMPMn0110H000810101101013010I10A10D3010I10A10D3010I10A10D3010I10A10D4010K1051011034010K10F10E101#6PDPFPHALI89RIPDPFPGPIG1eX5<X4;X2<X0;P8P9O2n0110J00012010B10CX1?P7P8P9O3P?P4P2PJ1I89RJP4P2PLPJG1^3;P9PNPKP>PP1IQ9RQPKP>POPQG1eX4;X2<X0;P8P9O2n0110J00012010B10CX1?P8P9O2n0110:000:30100107106201001013010010110:201051042010310;30103105104201001014110810<10910=3010010110220100101b;X<=P@D^G]XG<XF;P8P9O2n200110>00012110310MbE%\9%X95<:eW@o"). Qed.


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
  && expr_vars_lt v (a_brk cs) && fd_vars_lt v (a_fd cs) && Nat.leb nx0 v && Nat.leb NX0 v.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dd_key (a : saddr) : option positive :=
  match a with SA (ELit Z0) (Zpos p) => Some p | _ => None end.
Record ddseen : Type := DDS { dd_lit : ptree (list nat); dd_oth : list (saddr * nat) }.
Definition dd_has (s : ddseen) (a : saddr) (w : nat) : bool :=
  match dd_key a with
  | Some p => match pt_get (dd_lit s) p with Some ws => existsb (Nat.eqb w) ws | None => false end
  | None => existsb (fun aw => saddr_eqb a (fst aw) && Nat.eqb w (snd aw))%bool (dd_oth s)
  end.
Definition dd_add (s : ddseen) (a : saddr) (w : nat) : ddseen :=
  match dd_key a with
  | Some p => DDS (pt_set p (w :: match pt_get (dd_lit s) p with Some ws => ws | None => [] end) (dd_lit s)) (dd_oth s)
  | None => DDS (dd_lit s) ((a, w) :: dd_oth s)
  end.
Fixpoint log_dd_go (s : ddseen) (log : list sentry) : list sentry :=
  match log with
  | [] => []
  | SE a w v :: older => if dd_has s a w then log_dd_go s older else SE a w v :: log_dd_go (dd_add s a w) older
  end.
Definition log_dd (log : list sentry) : list sentry := log_dd_go (DDS PTLeaf []) log.

Definition run_block_ref (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  if fresh_ok cs then
    let ss := a_ss cs in
    let ss' := sym_execTX segs IT K fuel true stops (SS (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss)) in
    match carry (log_dd (s_log ss')) (s_know ss') [] with
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
    match carryK bc (log_dd (s_log ss')) (s_know ss') [] with
    | (kn', [], _) => Some (with_ss cs (mk_ss (s_pc ss') (s_regs ss') kn' (s_next ss')))
    | _ => None
    end
  else None.
Lemma run_block_eq : forall K fuel stops cs, run_block K fuel stops cs = run_block_ref K fuel stops cs.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h02knh11Kh21bi001bh32bch42csh52fkh64fuelh75hintsh85lemmah93logh:1pi011ph;1si021sh<5stopsi033kn'i041li052l0i062l1i071xp;1p;2p;6p;9p;4p;7p;3p;@g00@cR0j1CTg01Yij1]Tg00F=j1WTg00aHR1j2LTg00eaj1>Tg01Zjj12Tg01[gR2j18Tg01\fR3j1=Tg01]cj1ETg01^bj11Tg00f^j13Tg00eAj1JTg01_]j10Tg00lQj1OTg01`Zj6BTg01a\l9FTg01baj1ATg01c]j1@Tg01d\R4j4;Tg01e[j4:Tg01fYj2<Tg01gYj7?Tg01hZj3MTg001hj35j16Tg01iVj1VTg01jFj49Tg01jmj1GTg01k\j44Tg01lSj3HTg01mIj1UTg01n8j6TTg01ncj7Kl@RTg01oPj2DTg002ij6QTg020<l9PTg0216j7STg00GAj2ITg022>j3\Tg00>Fj6NTg023@l9[Tg024Hj4ZTg025Jj4YTg00F_j2XTg014ER5f0R6'Xp=7g005LR7g00]5#C%]6g00NdR8P8%W5R9P8P9P6P1g012G#CR:g026PR;#CR<'LR=%C8R>P9f2R?#>R@#2RA#8RB#=RCp,4segsRDPC%EAp,2ITREf5RFf4RGg00ODRHf3RI%1@%3@g027QRJ#JRKPA%0@g016A#OR@EBRLM9FRM#A#@%2M%J8RMC;P1P:P<P9f1RNP0P;P9P6f6ROPD%>ORP#2RQ#8#=%EQPEf9RRf8RSPHf7RT%1P%3PPKPQ%0PP@EBRPM9FRQ#1%3QPN%0QC:'<#7%O5RQn10110500020020102106n2001101000120103105n2001107000120101104PQn0100000020100P8P9P6P1P=P>P9PDPEPFPGPHPIPLF?RL#A#@R8%2LRL;MMP1P:P<P9PNP0P;P9P6PDPEPRPSPHPTPPF?RP#1%3PPN%0PC:,<O#7PQn10110500020020102106n2001101000120103105RPn2001107000120101104RUPQn010000002000035P6g028PRVPDPEPGPIPHP?%>NRW#1%3WPK%2WRX%0WP@EBRWF?RYP1P=P>P9PC%A6#@%26PMC;P1P:P<P9PNP0P;P9P6%1G%3GPN%0GC:,<O#7PQn10110500020020102106n2001101000120103105n2001107000120101104=59UX;V%2YRV%2W55:P9%69%V9P1P=P>P9PCP8PLPMC;RZPPn2001107000120101104P1P=P>P9%8LR[#=R\P8PLPMC;R]PPn20011070001201011041L=>R^P9P1P=P>P9P6P1P:P<P9PNP0P;P9P6PDPEf:PRPHPS%>TRR#1%3RPK%2R%0RP@EBF?RR#1%3RPN%0RC:,<T#7PQn10110500020020102106n2001101000120103105n2001107000120101104V^PZP]g029RR]%CJRJP^^7>RZ^0:RR]9R_]3R`P]P_%6]RaPJPR%6JP:PZ%6:RbP>P^%6>%6^RcC9RdC9ReC9RfC9RgP]P_PfPJPRPeP:PZPdP>P^Pc%G^C4C4C4C49H`gP4PCP\P]^5:R\P:P]PbPaC9RCP:P]Pa%G]C49H\CP3PBP[P:^0:R[P:P:PbPbC9RBP:P:Pb%G:C49H[BP2PAPLP:Pb%U:PLPAP6ETFKFKP8P81DJ8PLPL1D:LPMPM1D>MM@REQPUPU1D9UM9PW8PDPEPGPIPHP?PWFSP^%AY#@RY?MVMRLP1P=P>P9P6PPn2001107000120101104=59UX:^P1P=P>P9PLP1P:P<P9PNP0P;P9P6PDPEPSPTPHPO%>FRL#1%3LPK%2LRK%0LP@EBR@F?RL#1%3LPN%0LC:,<F#7PQn10110500020020102106n2001101000120103105n2001107000120101104RL,I9%8V#=PYPVPMC;A\YVMENO2PD%8X#=RY%EXPEPGPIPHP?PWM9FRVPDPXPEPGPIPHP?PW1I:XM9[ENP1P=P>P9PY%AV#@%2VPMC;P1P:P<P9PNP0P;P9P6PD%8K#=%EKPEPSPTPHPOP@M9FR@#1%3@PN%0@C:,<F#7PQn10110500020020102106n2001101000120103105n2001107000120101104=59Le1I9Qn0110001020100b2PIP?PNP6CZPIP?PNP6CY559eX45W<X67W1o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01Ki001Kh11bi011bh22b1h32b2h42fkh52k1h62k2h72n1i022n1h82n2i032n2h92ukh:2unh;1xh<2x0h=2x1h>2x2i041ai052a1i062a2i071ci081ei092hii0:1ki0;2k0i0<1li0=2loi0>1mi0?1ni0@1vi0A1wp;1p;2p;3p;4p;7p;6p;5g00@cj1KTg01\fj13Tg02:Qj1>j2Jj3?j4<j5ETg02;Yj19j2Hj3=j4;j5FTg02<`j18j70Tg003hj11Tg01>;j2:Tg01JTj1ITg00PDj15Tg017?j22Tg01KQj27Tg02=ej2GTg02>Bj2@Tg001hj36Tg00GAj2ATg02>_j1BTg02?gj1CTg00>Fj6DTg02A3j54Tg012GR0#Kg00\8R1g00]5R2g00NdR3^00R4^:1R5]9f0R6#3#>%96P2P5f1R5#3/J61H56P1P4f2R4#3??56A=456P0P3f3R7#3P4P5P6C<P7P4P5P6C;P3^81^62^31^71^52^21R8f4R9#8P0P3P5g016AR:P3P4g01YJ#1#1#1#1#1#1#1#1,:7R;f5R<f9R=f8R>f7R?P5P6%I7#5R@O6'2n0110400012010110:P:P3P5P9P>P?f6RAP5P6P4O6n0110400012010110:RBP:P3P4P<P=P>P?P5P6P7O6n0110400012010110:RCg02B5RD/751756'21G65REg02BS'@'2RFP4PAP<P9%5DRDP5%5EREO6'2g00ODRGPGPBPGPCPBn01100000:3010410A10@2010410<3010410<10;2010=1092010810>3010810=1092010410?401051021061033010410<1072010410<P0P3P5P:P3P4f:RBP=P>P?P5P6P@F0,2;n0110400012010110:P:P3P5P=P>P?PAP5P6P4F0n0110400012010110:RCP:P3P4PBP=P>P?P5P6P7F0n0110400012010110:RBP?PAP<P9PDP5PEF0,2FPGPGPCPGPBPCn01100000:3010410A10@2010410<3010410<10;2010=1092010810>3010810=1092010410?401051021061033010410<1072010410<563X18P0P3P6P:P3P4P=P>P?PAP5P6P@F0,2;n0110400012010110:P:P3P5P>P?PAP<P5P6P4F0n0110400012010110:R;P:P3P4P=P>P?PAP5P6P7F0n0110400012010110:R?PAP<P9P7PDP5PEF0,2FPGPGP;PGP?P;n01100000:3010410A10@2010410<3010410<10;2010=1092010810>3010810=1092010410?401051021061033010410<1072010410<,A3%39R;#B%C9EDP;P7P4P5P6DEP9P7P4P5P6DF563eX>0D4X=1D4X<2D4X;1D4W4o"). Qed.
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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01Ki001Kh11bi011bh22b1h32b2h42fkh52k1h62k2h72n1i022n1h82n2i032n2h92sph:2ubh;2ukh<2unh=1xh>2x0h?2x1h@2x2hA2x3i041ai052a1i062a2i071ci081ei092hii0:1ki0;2k0i0<1li0=2loi0>1mi0?1ni0@1vi0A1wp;1p;2p;3p;4p;5p;8p;6g00@cj1MTg01\fj13Tg02COj1?j2Lj3Bj4=j5:j6HTg02DXj1;j2Cj3>j4<j58j6ITg02E`j19j80Tg003hj12Tg01>;j2KTg01JTj1JTg00PDj15Tg017?j21Tg01KQj26Tg02=ej2ATg02>Bj2@Tg001hj37Tg00GAj2DTg02Fej1ETg02Gmj1FTg00>Fj6GTg02A3j54Tg012GR0#Mg02I9R1g00\8R2g00]5R3g00NdR4^00R5^<2R6];R7]:f0R8#3#?%;8P2P7f1R7#3/L81C78P3P6f2R6#3?B78A>678P2P5f3R5#3P6P7P8C=P5P6P7P8C<P0P4f4R9#3P5P6P7P8D:P9P5P6P7P8D8P4^82^63^32^72^53^22^91R:f5R;#9P0P4P7g016AR<P4P6g01YJ#2#2#2#2#2#2#2#2,K5R=P;f:R>f9R?f8R@f7RAP7P8%J5#5RBO7'1n0110400012010110:P<P4P7P9P?P@PAf6RCP7P8P6O7n0110400012010110:RDP<P4P6P;P>P?P@PAP7P8P5O7n0110400012010110:REg02B5RF/671678'11A87RGg02BS'@'1RHP6PAPCP;P9%5FRFP7%5GRGO7'1g00ODRIPIPDPIPEPDn01100000:3010410A10@2010410<3010410<10;2010=1092010810>3010810=1092010410?401051021061033010410<1072010410<P0P4P7P<P4P6f;RDP>P?P@PAP7P8PBG0,1=n0110400012010110:P<P4P7P>P?P@PAPCP7P8P6G0n0110400012010110:REP<P4P6PDP>P?P@PAP7P8P5G0n0110400012010110:RDP@PAPCP;P9PFP7PGG0,1HPIPIPEPIPDPEn01100000:3010410A10@2010410<3010410<10;2010=1092010810>3010810=1092010410?401051021061033010410<1072010410<574X1:P0P4P8P<P4P6P>P?P@PAPCP7P8PBG0,1=n0110400012010110:P<P4P7P?P@PAPCP;P7P8P6G0n0110400012010110:R=P<P4P6P>P?P@PAPCP7P8P5G0n0110400012010110:R@PAPCP;P9P5PFP7PGG0,1HPIPIP=PIP@P=n01100000:3010410A10@2010410<3010410<10;2010=1092010810>3010810=1092010410?401051021061033010410<1072010410<,D4%3;R=#E%F;EGP=P9P5P6P7P8EHP;P9P5P6P7P8EI574eXA0D4X@2D4X?3D4X>2D4X=1D4W4o"). Qed.
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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01Kh12ukh22unh31bh42b1h52fkh62k1h71lh82n1h91sh:2sph;2ubh<1xh=2x0h>2x1p;1p;2p;3p;4p;6p;5g00@cj1KTg01\fj10Tg02J7j1>j2Jj3?j4ETg02K:j1:j2Ij3=j4FTg02DXj1<j66Tg02L<j1;Tg02M;j49j1ATg00G[j22Tg02N=j17Tg01E0j31Tg02O;j48j1HTg001hj33Tg00GAj2GTg02P:j1@Tg00>Fj64Tg02Q=j1BTg02COj1CTg02RCj1DTg02A3j55Tg012GR0#KR1g00\8R2g00]5R3P1^22R4]1f0R5#0#>%:5P3P4f1R4#0/J51I45P2P1f2R6#0??45A=645g02I9R7g00Nd^00^22^13^;2]:R8f3R9#<%;5R:P4f5R;#0f4R<P9P6C9P<P9P6P5O5'2X00%0<#7R=510P;P;P<P9P6C8P<P9P6P5E6,2:X00R>=10<R?531X38P7^82^63^42R7%H9P;P4P<P9P6O3P<P9P6P5E6,2:X00=10==31?X97P1P9A10>5=31?X71P<P<P9P6P4C8P9P6P4P5E6,2:X00=109,G1%09R0#7%@9E4%A0%B9E4%C0%D9E4P0P6P4P5CEP9P6P4P5CF531eX>2D5X=3D5X<2D5W5o"). Qed.
#[local] Hint Rewrite kn_unfillB_eqf : bceq.

Definition kn_unfillM (k : list kentry) := kn_unfillB (mkbc k).
Lemma kn_unfillM_eq : kn_unfillM = kn_unfill.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01kh12ubh22ukh32unp;1p;3p;5g00@cj15Tg02SPj14Tg02TWR0j10Tg02K:R1j11Tg001hj33Tg02A3j52Tg012G#5R2g00\8R3g00]5P2^33]2]1R3P0P1f0R1#4%01%11533eX02D2o"). Qed.



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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01lh11Ki001Kh21ci011ch32ukh42unh51bh62fkh72kbi022kbh82kki032kkh93leni043lenh:2ubh;2wbh<2wkh=2wnh>1xh?2x0h@2x1hA2x2i051ai062a1i072a2i081ei092hii0:1ki0;2k0i0<2loi0=1mi0>1ni0?2n1i0@2n2i0A1vi0B1wp;1p;2p;3p;4p;7p;8p;5p;6g00@cj1VTg01\fj10Tg02UZj1Bj2Uj3Cj4@j5PTg02VZj1>j2Rj3Aj4?j5;Tg02;Yj1=j56Tg02WYj18Tg00G[j24Tg00eAj1TTg00LGj3:Tg02XWj7Sj1HTg02YZj8Qj1JTg02Z]j7Nj1LTg02[_j77j1FTg02\_j89j2ETg02]_j75j1DTg001hj31Tg00GAj2GTg02^^j1ITg00>Fj62Tg02_ej1KTg02`lj1MTg02:Qj1<Tg02b2j1OTg02A3j53Tg012GR0#VR1g00\8R2g00]5R3P1^10R4^42R5]3f0R6#0#B%>6P3P5f1R5#0/U61R56P2P4f2R4#0?C56AA456P0P1f3R7#0P4P5P6C@P7P4P5P6C?g00NdR8^10^42^33^:2R9f4R:#=P8P1%85R;P6P:P7P4P5O4'4%T0R<9:05R=P0P1P5P<g016AR>P1P5f9R?#0R@f8RAf7RBf6RCP5P6P4FSn01105000120102103RDP<P<P<P<P<P<P>P1P4f:RE#0P4P?PAPBP5P6P7GQn01105000120102103RFP>P1P5P@PAPBPCP5P6P4FNn01105000120102103n01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<1092010510>4010610?10710@3010510410120105104n0100000020000P8P1f5R@P:P7P4P5D6,4;R;P=P0P1P5P<P>P1P5P?PAPBPCP5P6P4F7n01105000120102103P<P<P<P<P<P<P>P1P4P4PEP?PAPBP5P6P7G9n01105000120102103REP>P1P5P?PAPBPCP5P6P4F5n01105000120102103RGn01100000:3010510B10A201051043010510>10;2010<1092010810=3010810<1092010510>4010610?10710@3010510410120105104n0100000020000RH511X59P1^92^83^72^=2^<3^;2R9%D:P8P1P;P=P0P1P5P<PDP<P<P<P<P<P<PFP>P1P5P:PAPBPCP5P6P4O6n01105000120102103RFn01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<1092010510>4010610?10710@3010510410120105104n0100000020000=11HX09P9^23RI1E6@X23P8P1P;P=P0P1P5P<PDP<P<P<P<P<P<P>P1P4P@P4P?PAPBP5P6P7O7n01105000120102103PGn01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<1092010510>4010610?10710@3010510410120105104n0100000020000=11HX0IP9%F:P8P1P;P=P0P1P5P<PFP<P<P<P<P<P<PEPGn01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<1092010510>4010610?10710@3010510410120105104n0100000020000=11HX09P8P1%86P:P7P4P5P6D6'4A:06<P0P1P6P<P>P1P5PAPBPCP@P5P6P4F7n01105000120102103P<P<P<P<P<P<P>P1P4P4P?PAPBPCP5P6P7G9n01105000120102103P>P1P5PAPBPCP@P5P6P4F5n01105000120102103n01100000:3010510B10A201051043010510>10;2010<1092010810=3010810<1092010510>4010610?10710@3010510410120105104n0100000020000,G1%0:R@#H%I:E2%J@%K:E2%L@%M:E2%<@%O:E2P@P7P4P5P6DPP:P7P4P5P6D;511eXA0D3X@2D3X?3D3X>2D3W6o"). Qed.
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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01lh11Ki001Kh21ci011ch32ubh42ukh52unh61bh72fkh82kbi022kbh92kki032kkh:3leni043lenh;2sph<2wbh=2wkh>2wnh?1xh@2x0hA2x1hB2x2hC2x3i051ai062a1i072a2i081ei092hii0:1ki0;2k0i0<2loi0=1mi0>1ni0?2n1i0@2n2i0A1vi0B1wp;1p;2p;3p;4p;5p;7p;8p;6g00@cj1XTg01\fj10Tg02c>j1Bj2Wj3Dj4@j5=j6RTg02d?j1>j2Uj3Aj4?j5<j6STg02DXj1;j69Tg02WYj1:Tg00G[j24Tg00eAj1VTg00LGj38Tg02XWj7Tj1ITg02YZj8Kj1LTg02Z]j7Cj1NTg02[_j76j1GTg02\_j87j2FTg02]_j75j1ETg001hj31Tg00GAj2HTg02^^j1JTg00>Fj63Tg02_ej1MTg02`lj1OTg02COj1PTg02RCj1QTg02A3j52Tg012GR0#XR1g02I9R2g00\8R3g00]5R4P1^10R5^53R6]4R7]3f0R8#0#B%>8P3P7f1R7#0/W81U78P4P6f2R6#0?D78AA678P3P5f3R5#0P6P7P8C@P5P6P7P8C?P0P1f4R9#0P5P6P7P8D=P9P5P6P7P8D<g00NdR:^10^53^44^33^;2R;f5R<#;P:P1%:7R=P8P<P9P5P6P7O5'4%V0R>9807R?P0P1P7P>g016AR@P1P7f:RA#0RBf8RCf7RDf6REP7P8P6FTn01105000120102103RFP>P>P>P>P>P>P@P1P6f;RG#0P6f9RHPCPDP7P8P5GKn01105000120102103RIP@P1P7PBPCPDPEP7P8P6FCn01105000120102103n01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<1092010510>4010610?10710@3010510410120105104n0100000020000P:P1PEP<P9P5P6P7E9,4=R=P?P0P1P7P>P@P1P7PAPCPDPEP7P8P6F6n01105000120102103P>P>P>P>P>P>P@P1P6P6PGPHPCPDP7P8P5G7n01105000120102103RGP@P1P7PAPCPDPEP7P8P6F5n01105000120102103RBn01100000:3010510B10A201051043010510>10;2010<1092010810=3010810<1092010510>4010610?10710@3010510410120105104n0100000020000RJ511X6;P1^:3^94^83^>3^=4^<3R;%E<P:P1P=P?P0P1P7P>PFP>P>P>P>P>P>PIP@P1P7P9PCPDPEP7P8P6O6n01105000120102103RIn01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<1092010510>4010610?10710@3010510410120105104n0100000020000=11JX0;P;^24RK1F8EX24P:P1P=P?P0P1P7P>PFP>P>P>P>P>P>P@P1P6P<P6PHPCPDP7P8P5O7n01105000120102103PBn01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<1092010510>4010610?10710@3010510410120105104n0100000020000=11JX0KP;%G<P:P1P=P?P0P1P7P>PIP>P>P>P>P>P>PGPBn01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<1092010510>4010610?10710@3010510410120105104n0100000020000=11JX0;P:P1%:8P<P9P5P6P7P8E9'4A808>P0P1P8P>P@P1P7PHPDPEP<P7P8P6F6n01105000120102103P>P>P>P>P>P>P@P1P6P6PAPCPDPEP7P8P5G7n01105000120102103P@P1P7PHPDPEP<P7P8P6F5n01105000120102103n01100000:3010510B10A201051043010510>10;2010<1092010810=3010810<1092010510>4010610?10710@3010510410120105104n0100000020000,H1%0<RE#I%J<E3%LE%M<E3%NE%O<E3%PE%Q<E3PEP9P5P6P7P8ERP<P9P5P6P7P8ES511eXC0D2XB3D2XA4D2X@3D2X?2D2W7o"). Qed.
#[local] Hint Rewrite havoc1pB_eqf : bceq.


Definition kn_havoc (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.flat_map (havoc1p k sp ub uk un) k.

Definition kn_havocB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  List.flat_map (havoc1pB bc sp ub uk un) (bc_fk bc).

Lemma kn_havocB_eqf : forall fk, kn_havocB (mkbc fk) = kn_havoc fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01lh12ukh22unh31Kh42b1h52fkh62k1h72n1h81sh92sph:2ubh;1xh<2x0h=2x1p;1p;2p;3p;4p;5p;6g00@cj1JTg01\fj11Tg02e?j1<j2Ij3=j4CTg02fAj18j2Fj3;j4DTg02d?j1:j55Tg02M;j49j1?Tg02N=j16Tg02O;j47j1HTg001hj32Tg00GAj2ETg02P:j1>Tg00>Fj63Tg02Q=j1@Tg02c>j1ATg02gBj1BTg02A3j54Tg006lj4GTg012GR0P0f1R1f0R2CGp=0%J0R3g00\8R4g00]5R5P3^24R6]1%12#<%82P5P6%11/I21F12P4P3f2R6#1?=12A;612g02I9R7P3^30^24^15^:4]9R0f3R8#:P2f4R9#1R:P8P6P1C9P8P6P1O4%6:R:'0P9P9P8P6P1C7P8P6P1D5R;/09R<523X00P7^74^65^44R7%H8P9P2P8P6P1O3P8P6P1D5/0:=23<X87P3P810;2=23<X03P8P8P6P1P2C7P6P1P2D5/08,E3%18R<#6%>8E3%?<%@8E3%A<%B8E3P<P6P1P2CCP8P6P1P2CD523eX=4D4X<5D4X;4D4W5o"). Qed.
#[local] Hint Rewrite kn_havocB_eqf : bceq.

Definition kn_havocM (k : list kentry) := kn_havocB (mkbc k).
Lemma kn_havocM_eq : kn_havocM = kn_havoc.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01kh12ubh22ukh32unp;1p;3p;5g00@cj15Tg02hGj14Tg02iMR0j10Tg02fAR1j11Tg001hj33Tg02A3j52Tg012G#5R2g00\8R3g00]5P2^33]2]1R3P0P1f0R1#4%01%11533eX02D2o"). Qed.



(* [comment removed for export] *)
Definition kwr_cut (k : list kentry) (ub : expr) (uk : Z) (un : expr) (kb : expr) (kk : Z) (len : expr) : list kentry :=
  kcut KWr k ub uk un kb kk len.

Definition kwr_cutB (bc : bctx) (ub : expr) (uk : Z) (un : expr) (kb : expr) (kk : Z) (len : expr) : list kentry :=
  kcutB bc KWr ub uk un kb kk len.

Lemma kwr_cutB_eqf : forall fk, kwr_cutB (mkbc fk) = kwr_cut fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h02mkh12fkh22kbh32kkh41lh53lenh62ukh72unh82wbh92wkh:2wnh;1xh<2x0h=2x1h>2x2h?2x3h@2x4p;1p;2p;3p;4p;5p;6p;8p;7g00@cj1GTg01\fj10Tg02jOj1;j2Fj3<j45j57j69j7BTg02kPj14j2=j3:j46j58j6Ej7CTg02lPj2Dj83Tg001hj32Tg00GAj2>Tg02mKj1?Tg02nIj1@Tg00>Fj6ATg02A3j51Tg012GR0#GR1g00\8R2g00]5R3P1^52R4^33R5^22R6^72R7]6f0R8#0#;%48P3P7f1R7#0/F81=78P2P6f2R9#0?<78A:978P2P5f3R5#0P9P7P8C5P5P9P7P8C6P3P4f4R4#0P5P9P7P8D7P4P5P9P7P8D8P2P1f5R:#0P4P5P9P7P8E9P:P4P5P9P7P8EEg016AP0\2[R0P6^:2^93^82]0R6f7R;,D8X00P8g01RRR0f6R<P:P4P5P9P7O7P0P;P<P:P4P5P9P7G3521X46P0P<P:P4P5P9P7P8G3,>1%0<R0#?%@<EAP0P:P4P5P9P7P8FBP<P:P4P5P9P7P8FC521eX@2D1X?3D1X>2D1X=2D1X<3D1X;2D1W1o"). Qed.
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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01lh12ukh22unh31Ki001Kh41ci011ch52ubh61bh72fkh82kbi022kbh92kki032kkh:3leni043lenh;2wbh<2wkh=2wnh>1xh?2x0h@2x1hA2x2i051ai062a1i072a2i081ei092hii0:1ki0;2k0i0<2loi0=1mi0>1ni0?2n1i0@2n2i0A1vi0B1wp;1p;2p;3p;4p;5p;7p;8p;6g00@cj1YTg01\fj10Tg02oKj1Aj2Xj3Bj4?j5TTg030Lj1=j2Kj3@j4>j5WTg02kPj1<j76Tg02:Qj5;j1PTg00eAj1:Tg00LGj39Tg02XWj7Vj1HTg02YZj8Uj1LTg02Z]j7Jj1NTg02;Yj57j1CTg02[_j74j1FTg02\_j88j2ETg02]_j75j1DTg001hj31Tg00GAj2GTg02^^j1ITg00>Fj62Tg02_ej1MTg02`lj1OTg02b2j1QTg02jOj1RTg031Lj1STg02A3j53Tg012GR0#YR1g00\8R2g00]5R3P1^30R4^22R5]1f0R6#0#A%=6P3P5f1R5#0/X61K56P2P4f2R4#0?B56A@456P0P1f3R7#0P4P5P6C?P7P4P5P6C>P1^:2^93^82R8^22^13^52R9f4R:#<g00NdR;P1f5R<#0P:P7P4P5D;%:0R=9905R>P0P1P5P=g016AR?P1P5f9R@#0RAf8RBf7RCf6RDP5P6P4FVn01105000120102103REP=P=P=P=P?P1P5P:PBPCPDP5P6P4O6n01105000120102103RFP=P?P1P4f:RG#0P4P@PBPCP5P6P7GUn01105000120102103RHP?P1P5PAPBPCPDP5P6P4FJn01105000120102103RAn01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<109201051044010610?10710@3010510410120105104n0100000020000P;P1P<P:P7P4P5D7RIP>P0P1P5P=P?P1P5P@PBPCPDP5P6P4F4n01105000120102103P=P=P=P=P?P1P5P@PBPCPDP5P6P4F6n01105000120102103RJP=P?P1P4P4PGP@PBPCP5P6P7G8n01105000120102103RGP?P1P5P@PBPCPDP5P6P4F5n01105000120102103RKn01100000:3010510B10A201051043010510>10;2010<1092010810=3010810<109201051044010610?10710@3010510410120105104n0100000020000RL511X09P;^30^22^13^52R9%C:P;P1P6P:P7P4P5O4P>P0P1P5P=PEP=P=P=P=PJP=PHPAn01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<109201051044010610?10710@3010510410120105104n0100000020000=11LX69P8^=2^<3^;2R8%D:P;P1PIP>P0P1P5P=PEP=P=P=P=PJP=PHPFn01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<109201051044010610?10710@3010510410120105104n0100000020000=11LX08P8^43RH1E6<X43P;P1PIP>P0P1P5P=PEP=P=P=P=PJP=P?P1P4P<P4P@PBPCP5P6P7O7n01105000120102103PKn01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<109201051044010610?10710@3010510410120105104n0100000020000=11LX0HP8%F:P;P1PIP>P0P1P5P=PFP=P=P=P=PJP=PGPKn01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<109201051044010610?10710@3010510410120105104n0100000020000=11LX08P;P1P:P7P4P5P6D7A906=P0P1P6P=P?P1P5PBPCPDP<P5P6P4F4n01105000120102103P=P=P=P=P?P1P5PBPCPDP<P5P6P4F6n01105000120102103P=P?P1P4P4P@PBPCPDP5P6P7G8n01105000120102103P?P1P5PBPCPDP<P5P6P4F5n01105000120102103n01100000:3010510B10A201051043010510>10;2010<1092010810=3010810<109201051044010610?10710@3010510410120105104n0100000020000,G1%0:R<#H%I:E2%L<%M:E2%N<%O:E2%P<%Q:E2%R<%S:E2P<P7P4P5P6DTP:P7P4P5P6DW511eXA0D3X@2D3X?3D3X>2D3W7o"). Qed.
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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01lh12ubh22ukh32unh41Ki001Kh51ci011ch61bh72fkh82kbi022kbh92kki032kkh:3leni043lenh;2sph<2wbh=2wkh>2wnh?1xh@2x0hA2x1hB2x2hC2x3i051ai062a1i072a2i081ei092hii0:1ki0;2k0i0<2loi0=1mi0>1ni0?2n1i0@2n2i0A1vi0B1wp;1p;2p;3p;4p;5p;6p;7p;8g00@cj1[Tg01\fj10Tg032Qj1Aj2Zj3Bj4?j5<j6WTg033Sj1=j2Mj3@j4>j5;j6VTg02kPj1:j75Tg02COj6Yj1RTg00eAj1UTg00LGj39Tg02XWj7Lj1JTg02YZj8Dj1NTg02Z]j7Cj1PTg02DXj66j1ETg02[_j78j1HTg02\_j84j2GTg02]_j77j1FTg001hj31Tg00GAj2ITg02^^j1KTg00>Fj63Tg02_ej1OTg02`lj1QTg02RCj1STg02jOj1TTg031Lj1XTg02A3j52Tg012GR0#[R1g02I9R2g00\8R3g00]5R4P1^40R5^33R6]2R7]1f0R8#0#A%=8P3P7f1R7#0/Z81M78P4P6f2R6#0?B78A@678P3P5f3R5#0P6P7P8C?P5P6P7P8C>P0P1f4R9#0P5P6P7P8D<P9P5P6P7P8D;P1^:3^94^83R:^33^24^13R;f5R<#:g00NdR=P1f6R>#0P<P9P5P6P7EY%U0R?9907R@P0P1P7P?g016ARAP1P7f:RB#0RCf8RDf7REP>P7P8P6FLn01105000120102103RFP?P?P?P?PAP1P7P9PDPEP>P7P8P6O6n01105000120102103RGP?PAP1P6f;RH#0P6f9RIPDPEP7P8P5GDn01105000120102103RJPAP1P7PCPDPEP>P7P8P6FCn01105000120102103RCn01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<109201051044010610?10710@3010510410120105104n0100000020000P=P1P>P<P9P5P6P7E6RKP@P0P1P7P?PAP1P7PBPDPEP>P7P8P6F8n01105000120102103P?P?P?P?PAP1P7PBPDPEP>P7P8P6F5n01105000120102103RLP?PAP1P6P6PHPIPDPEP7P8P5G4n01105000120102103RHPAP1P7PBPDPEP>P7P8P6F7n01105000120102103RMn01100000:3010510B10A201051043010510>10;2010<1092010810=3010810<109201051044010610?10710@3010510410120105104n0100000020000RN511X0;P=^40^33^24^13^;2R;%E<P=P1P8P<P9P5P6P7O5P@P0P1P7P?PFP?P?P?P?PLP?PJPCn01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<109201051044010610?10710@3010510410120105104n0100000020000=11NX6;P:^>3^=4^<3R:%F<P=P1PKP@P0P1P7P?PFP?P?P?P?PLP?PJPGn01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<109201051044010610?10710@3010510410120105104n0100000020000=11NX0:P:^54RJ1G8>X54P=P1PKP@P0P1P7P?PFP?P?P?P?PLP?PAP1P6P<P6PIPDPEP7P8P5O7n01105000120102103PMn01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<109201051044010610?10710@3010510410120105104n0100000020000=11NX0JP:%H<P=P1PKP@P0P1P7P?PGP?P?P?P?PLP?PHPMn01100000:3010510B10A201051043010510>10:2010<1092010810=3010810<109201051044010610?10710@3010510410120105104n0100000020000=11NX0:P=P1P<P9P5P6P7P8E6A908?P0P1P8P?PAP1P7PIPEP>P<P7P8P6F8n01105000120102103P?P?P?P?PAP1P7PIPEP>P<P7P8P6F5n01105000120102103P?PAP1P6P6PBPDPEP>P7P8P5G4n01105000120102103PAP1P7PIPEP>P<P7P8P6F7n01105000120102103n01100000:3010510B10A201051043010510>10;2010<1092010810=3010810<109201051044010610?10710@3010510410120105104n0100000020000,I1%0<R>#J%K<E3%N>%O<E3%P>%Q<E3%R>%S<E3%T>%X<E3P>P9P5P6P7P8EWP<P9P5P6P7P8EV511eXC0D2XB3D2XA4D2X@3D2X?2D2W7o"). Qed.
#[local] Hint Rewrite cutout1pB_eqf : bceq.


Definition kn_cutout (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.flat_map (cutout1p k sp ub uk un) k.

Definition kn_cutoutB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  List.flat_map (cutout1pB bc sp ub uk un) (bc_fk bc).

Lemma kn_cutoutB_eqf : forall fk, kn_cutoutB (mkbc fk) = kn_cutout fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01lh12ukh22unh31Kh42b1h52fkh62k1h72n1h81sh92sph:2ubh;1xh<2x0h=2x1p;1p;2p;3p;4p;5p;6g00@cj1JTg01\fj11Tg034Tj1<j2Ij3=j4CTg035Wj18j2Fj3;j4DTg033Sj1:j55Tg02M;j49j1?Tg02N=j16Tg02O;j47j1HTg001hj32Tg00GAj2ETg02P:j1>Tg00>Fj63Tg02Q=j1@Tg032Qj1ATg036Yj1BTg02A3j54Tg006lj4GTg012GR0P0f1R1f0R2CGp=0%J0R3g00\8R4g00]5R5P3^24R6]1%12#<%82P5P6%11/I21F12P4P3f2R6#1?=12A;612g02I9R7P3^30^24^15^:4]9R0f3R8#:P2f4R9#1R:P8P6P1C9P8P6P1O4%6:R:'0P9P9P8P6P1C7P8P6P1D5R;/09R<523X00P7^74^65^44R7%H8P9P2P8P6P1O3P8P6P1D5/0:=23<X87P3P810;2=23<X03P8P8P6P1P2C7P6P1P2D5/08,E3%18R<#6%>8E3%?<%@8E3%A<%B8E3P<P6P1P2CCP8P6P1P2CD523eX=4D4X<5D4X;4D4W5o"). Qed.
#[local] Hint Rewrite kn_cutoutB_eqf : bceq.

Definition kn_cutoutM (k : list kentry) := kn_cutoutB (mkbc k).
Lemma kn_cutoutM_eq : kn_cutoutM = kn_cutout.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01kh12ubh22ukh32unp;1p;3p;5g00@cj15Tg037_j14Tg038fR0j10Tg035WR1j11Tg001hj33Tg02A3j52Tg012G#5R2g00\8R3g00]5P2^33]2]1R3P0P1f0R1#4%01%11533eX02D2o"). Qed.



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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01nh13acch22fkh35hintsi005hintsh41li011lh53offh62rbh72rkh82sxi022sxh91xi031xh:2x0h;2x1i041ai052b0i061ei071ii081ki092k0i0:2loi0;2n0i0<2opi0=1si0>3scsi0?1vi0@1zp;1p;2p;3p;8p;6p;4p;5g00@cR0j12Tg00F=j1FTg01\fj10Tg039ij16j2Cj3;j4@Tg03:ij1Ej2<j3:j4ATg03;hj27j85Tg00eAj13Tg03<jj28Tg00F_j29Tg00lQj1DTg001hj34Tg00GAj2BTg03=Jj2=Tg03>Oj2>Tg00>Fj6?Tg02A3j51Tg012G#2g00\8R1g00]5R2g005LR3%F2R4]0R5]5f0R6#0#6%E6P2P5f1R5#0/C61<56P3P4f2R7#0?;56A:756g00NdR8%28g026PR9#2g03?XR:]1]3]8^03^72^61R;p,4segsR<f3R='7P:P4P6P=P7P5g00OdR>%38R8%39R?O6P1P4P7P0P9P4P7g02BS,86,92%D2R9n10110>0002002010=101R0P9P9P9P9P9P9P9n0110?00081010@1010;3010<1041053010<1041053010<1041053010<1041054010210:10;1064010210810710;P9P9n0110300033010?10>1002010>10000P:P4P<f4P=P7P5P>P8P?G5P1P4P7P0P9P9P9P9P9P9P9n0110?00081010@1010;3010<1041053010<1041053010<1041053010<1041054010210:10;1064010210910710;R0P9P9n0110300033010?10>1002010>10000544X4;P:P4P<P=P7P5P6P>P8P?G5P0P9P9n0110300033010?10>1002010>10000,B4%0=R9,=<1>=<E?P9P7P5P6C@P=P7P5P6CA544eX;3D1X:2D1X91D1W2o"). Qed.
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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h03acch12fkh25hintsi005hintsh31li011lh41nh53offh62rbh72rkh82sxh91xi021xh:2x0i031si043scsi051vp;1p;2p;8p;3p;6p;5g00@cR0j11Tg00F=j1DTg01\fj12Tg03@Uj17j2<j3?Tg03AVj1Cj2;j3@Tg03;hj2:j85Tg003hj10Tg00eAj13Tg00F_j28Tg00lQj19Tg001hj36Tg00GAj2BTg03=Jj2ATg03>Oj2=Tg00>Fj6>Tg02A3j54Tg012G#1g00\8R1g00]5R2%D1R3]5f0R4#2#7%C4P2P3f1R5#2/<41;54g005Lg00NdR6%16g026PR7#1g03?XR8]0]2]8]4^72^61R9p,4segsR:f2R;':P8P3P4P;P5g01YJ#0#0#0#0#0#0#0#0R<g00OdR=%36R6%37R>O6P0P7P3P5181;%91R7n10110400020020103101R0P7P7n011020003301051041002010410000P8P3P:f3P;P5P<P=P6P>G5P0P7P7n011020003301051041002010410000563X39P8P3P:P;P5P4P<P=P6P>G5P0P7P7n011020003301051041002010410000,B3%2;R7,A:1=;:E>A?754A@;54563eX:2D4X91D4W1o"). Qed.
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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bh11nh23offh31kh42IHh51Kh62b1h72b2h81ei001eh92fkh:2k1i012k1h;2k2h<2n1i022n1h=2n2i032n2h>1oh?4resti041ai052a1i062a2i071ci082hii092k0i0:2loi0;1mi0<2n0i0=1vi0>1wi0?2wbi0@2wki0A2wli0B2wni0C1xp;1p;2p;3p;4p;5p;7p;6p;8g00@cj1TTg01\fj12Tg03BVj1Fj2Sj3Lj4Cj55Tg03CYj1Aj2Pj3Ej4Bj50Tg00eAj1RTg00GAj2>Tg01IUj2=Tg01KQj24Tg017?j21Tg03D[j2Oj1JTg01K4j28Tg02>Bj2;Tg00PDj19Tg03EXj7Dj1@Tg03FYj2:j1ITg03GSj7<j1GTg00F=R0j1HTg03HQj1KTg00>Fj67Tg03IRj1MTg00LGj3NTg00^kj8?Tg02A3j56Tg001hj3QTg00NdR1f1R2f0R33Qp=3g012GR4#TR5P5g00\8R6g00]5R7P1^17R8]2R9]0%23#F%A3P6P9%22/S31P23P7P8f2R8#2?L23AE823P7P1f3R9#2P8P2P3CCP9P8P2P3CBP4f8R:#2P9P8P2P3D5P:P9P8P2P3D0'3^17^27^06X35f7R;%R4P8P2P3D0,>1X17X27X06f9R<#2P9P8P2P3D5P<P9P8P2P3D0'3^17^27^06P1f:R=f4R>P8P2P3D0P4P1f6R?P9P8P9P8P8P9g016AR@P1P2P1P1P1P11=;2143?'1RAP0P7P1f?RB#2RC/O818;?1823RD'4REg00OdRFn10110C00021010A00PFn0100000020000RGg00ODRHP1P1g02B5RIf5RJ'4g02BSRK,;J'1RLPCP;P?%9JRCP2P3P8FD'1PHP>n0100000020000n0100000020000n0110400012010?10@P>P9P8n01109000:3010410>10=2010410<3010410<1012010:1082010010;3010010:1082010410B401051021061033010410<1072010410<P4P1P?f>RMP:P?PJP>D0R:f=P;PJP>P9D0RNP:PNPNP:P@P1P2P1P1P1P1PAP0P7P11:B8PEPFn10110C00021010A00PFn0100000020000PHP1P1PBP;P?PCP2P3P8F<,1LPHPBP<P;P?PJD0R<n0100000020000RBn0100000020000n0110400012010?10@P<P:PNn01109000:3010410>10=2010410<3010410<1012010:1082010010;3010010:1082010410B401051021061033010410<1072010410<RO'3X01P1^=6^;7^76^<6^:7^66RP%G=P4P1P?P:PNP:PNPNP:P@P1P2P1P1PGPHP1P1P>P;P?PCP2P3P8O6,1LPHP<n0100000020000n0100000020000n0110400012010?10@P<P:PNn01109000:3010410>10=2010410<3010410<1012010:1082010010;3010010:1082010410B401051021061033010410<1072010410</3OX0P%H7^86RP%I=P4P1P?P:PNP:PNPNP:P@P1P2P1P1P1P1PAP0P7P1P>P8O1PEPFn10110C00021010A00PFn0100000020000PHPBn0100000020000n0110400012010?10@P<P:PNn01109000:3010410>10=2010410<3010410<1012010:1082010010;3010010:1082010410B401051021061033010410<1072010410</3OX>PP4P1PJPNf<P?P>P9P8D0RPPNPPPPPNP@P1P2P1P1P1P11=?2143J'1P0P7P11:M818?J/4DPFn10110C00021010A00PFn0100000020000PHP1P114I>1;>K'1PMP?PJ%9>P2P3P8F<'1PHP:n0100000020000n0100000020000n0110400012010?10@P:PNPPn01109000:3010410>10=2010410<3010410<1012010:1082010010;3010010:1082010410B401051021061033010410<1072010410<,>1%2=R1#J%K=E7%@1%M=E7P1P>P8P2P3D5P9P8P2P3O3E7P1AN4J>RJP8P2P3D5P=PJP8P2P3D0'3eX17X27X06W4X?5X54P9P8P2P3G?X17D6X27D6X06D6X35D6W9o"). Qed.
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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bh11nh23offh31kh41oh52IHh61Kh72b1h82b2h91ei001eh:2fkh;2k1i012k1h<2k2h=2n1i022n1h>2n2i032n2h?4resti041ai052a1i062a2i071ci082hii092k0i0:2loi0;1mi0<2n0i0=2nhi0>1vi0?1wi0@2wbi0A2wki0B2wli0C2wni0D1xp;1p;2p;3p;4p;5p;7p;6p;8g00@cj1WTg01\fj10Tg03JWj1Ej2Vj3Oj4Cj53Tg03K\j1Aj2Sj3Dj4Bj51Tg00eAj1UTg00GAj2=Tg01IUj2<Tg01KQj25Tg017?j2;Tg03L`j2Rj1@Tg03D[j2Nj1JTg01K4j27Tg03EXj7Lj1?Tg03M]j29j1HTg03FYj28j1ITg03GSj7:j1FTg00F=R0j1GTg03HQj1KTg00>Fj64Tg03NWj1MTg03IRj1PTg00LGj3QTg00^kj8>Tg02A3j56Tg001hj3TTg00NdR1f1R2f0R33Tp=2g012GR4#WR5P5g00\8R6g00]5R7P1^16R8]2R9]0%03#E%A3P6P9%02/V31S23P7P8f2R8#0?O23AD823P6P1f3R9#0P8P2P3CCP9P8P2P3CBP4f8R:#0P9P8P2P3D3P:P9P8P2P3D1'2^16^27^06X35f7R;%U4P8P2P3D1,=1X16X27X06f9R<#0P9P8P2P3D3P<P9P8P2P3D1'2^16^27^06P1f:R=f4R>P8P2P3D1P4P1f6R?P9P8P9P8P8P9g016AR@P1P2P1P1P1P11<;2153?';RAP0P7P1f?RB#0RCf5RD'RP0P7P1f@RE#0/N917:21783RF'5RGg00OdRHn10110D00021010B00RIPHn10110D00021010=00PHn0100000020000RJg00ODRKP1P1PCP;P?PDP2P3P8FLPKP>n0100000020000n0100000020000n0110400012010@10AP>P9P8n01109000:3010410?10>2010410<3010410<1012010:1082010010;3010010:1082010410C401051021061033010410<1072010410<P4P1P?f>RCP:P?PDP>D1R:f=P;PDP>P9D1RLP:PLPLP:P@P1P2P1P1P1P1PAP0P7P119BDRMP0P7P118E9PGPHn10110D00021010B00PHn10110D00021010=00PHn0100000020000PKP1P1PBP;P?PDP2P3P8F:PKPBP<P;P?PDD1R<n0100000020000REn0100000020000n0110400012010@10AP<P:PLn01109000:3010410?10>2010410<3010410<1012010:1082010010;3010010:1082010410C401051021061033010410<1072010410<RN'2X01P1^>6^<7^86^=6^;7^76RO%F=P4P1P?P:PLP:PLPLP:P@P1P2P1P1PJPKP1P1P>P;P?PDP2P3P8O6PKP<n0100000020000n0100000020000n0110400012010@10AP<P:PLn01109000:3010410?10>2010410<3010410<1012010:1082010010;3010010:1082010410C401051021061033010410<1072010410</2NX0O%G7^96RO%H=P4P1P?P:PLP:PLPLP:P@P1P2P1P1P1P1PAP0P7P1P>PDO1PIPHn10110D00021010=00PHn0100000020000PKPEn0100000020000n0110400012010@10AP<P:PLn01109000:3010410?10>2010410<3010410<1012010:1082010010;3010010:1082010410C401051021061033010410<1072010410</2NX4OPO%I=P4P1P?P:PLP:PLPLP:P@P1P2P1P1P1P1PAP0P7P1PMP0P7P1PDP9O1PGPHn10110D00021010B00PHn10110D00021010=00PHn0100000020000PKPEn0100000020000n0110400012010@10AP<P:PLn01109000:3010410?10>2010410<3010410<1012010:1082010010;3010010:1082010410C401051021061033010410<1072010410</2NX4OP4P1PDPLf<P?P>P9P8D1ROPLPOPOPLP@P1P2P1P1P1P11<?2153D';P0P7P119C>P0P7P118B917;2/5FPHn10110D00021010B00PHn10110D00021010=00PHn0100000020000PKP1P1PCP?PDP>P2P3P8F:PKP:n0100000020000n0100000020000n0110400012010@10AP:PLPOn01109000:3010410?10>2010410<3010410<1012010:1082010010;3010010:1082010410C401051021061033010410<1072010410<,=1%0=R1#J%K=E4%@1%M=E4%?1%P=E4P1P>P8P2P3D3P9P8P2P3O3E4P1AQ4D>RDP8P2P3D3P=PDP8P2P3D1'2eX16X27X06W5X?5X64P9P8P2P3G>X16D6X27D6X06D6X35D6W:o"). Qed.
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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bh11nh23offh31kh41oh52IHh61Kh72b1h82b2h91ei001eh:2fkh;2k1i012k1h<2k2h=2n1i022n1h>2n2i032n2h?4resti041ai052a1i062a2i071ci082hii092k0i0:2loi0;1mi0<2n0i0=2nhi0>1vi0?1wi0@1xi0A2zbi0B2zki0C2zli0D2znp;1p;2p;3p;4p;5p;7p;6p;8g00@cj1WTg01\fj10Tg03OXj1Ej2Vj3Oj4Cj53Tg03PYj1Aj2Sj3Dj4Bj51Tg00eAj1UTg00GAj2=Tg01IUj2<Tg01KQj25Tg017?j2;Tg03L`j2Rj1@Tg03D[j2Nj1JTg01K4j27Tg03EXj7Lj1?Tg03M]j29j1HTg03FYj28j1ITg03GSj7:j1FTg00F=R0j1GTg03HQj1KTg00>Fj64Tg03NWj1MTg03IRj1PTg00LGj3QTg00^kj8>Tg02A3j56Tg001hj3TTg00NdR1f1R2f0R33Tp=2g012GR4#WR5P5g00\8R6g00]5R7P1^16R8]2R9]0%03#E%A3P6P9%02/V31S23P7P8f2R8#0?O23AD823P6P1f3R9#0P8P2P3CCP9P8P2P3CBP4f8R:#0P9P8P2P3D3P:P9P8P2P3D1'2^16^27^06X35f7R;%U4P8P2P3D1,=1X16X27X06f9R<#0P9P8P2P3D3P<P9P8P2P3D1'2^16^27^06P1f:R=f4R>P8P2P3D1P4P1f6R?P9g016AR@P1P2P1P1P1P11<;2153?';RAP0P7P1f?RB#0RCf5RD'RP0P7P1f@RE#0/N917:21783RF'5RGg00OdRHn10110@00021010C00RIPHn10110@00021010=00PHn0100000020000RJg00ODRKP1P1PCP;P?PDP2P3P8FLPKP>n0100000020000n0100000020000n0110400012010A10BP9P8P8P9P8P>P9P8n01109000:3010410?10>2010410D3010410<1012010:1082010010;3010010:1082010410<401051021061033010410<1072010410<P4P1P?f>RCP:P?PDP>D1R:P@P1P2P1P1P1P1PAP0P7P119BDRLP0P7P118E9PGPHn10110@00021010C00PHn10110@00021010=00PHn0100000020000PKP1P1PBP;P?PDP2P3P8F:PKPBP<P;P?PDD1R<n0100000020000REn0100000020000n0110400012010A10BP:f=P;PDP>P9D1RMPMP:PMP<P:PMn01109000:3010410?10>2010410D3010410<1012010:1082010010;3010010:1082010410<401051021061033010410<1072010410<RN'2X01P1^>6^<7^86^=6^;7^76RO%F=P4P1P?P:P@P1P2P1P1PJPKP1P1P>P;P?PDP2P3P8O6PKP<n0100000020000n0100000020000n0110400012010A10BP:PMPMP:PMP<P:PMn01109000:3010410?10>2010410D3010410<1012010:1082010010;3010010:1082010410<401051021061033010410<1072010410</2NX0O%G7^96RO%H=P4P1P?P:P@P1P2P1P1P1P1PAP0P7P1P>PDO1PIPHn10110@00021010=00PHn0100000020000PKPEn0100000020000n0110400012010A10BP:PMPMP:PMP<P:PMn01109000:3010410?10>2010410D3010410<1012010:1082010010;3010010:1082010410<401051021061033010410<1072010410</2NX4OPO%I=P4P1P?P:P@P1P2P1P1P1P1PAP0P7P1PLP0P7P1PDP9O1PGPHn10110@00021010C00PHn10110@00021010=00PHn0100000020000PKPEn0100000020000n0110400012010A10BP:PMPMP:PMP<P:PMn01109000:3010410?10>2010410D3010410<1012010:1082010010;3010010:1082010410<401051021061033010410<1072010410</2NX4OP4P1PDPMP@P1P2P1P1P1P11<?2153D';P0P7P119C>P0P7P118B917;2/5FPHn10110@00021010C00PHn10110@00021010=00PHn0100000020000PKP1P1PCP?PDP>P2P3P8F:PKP:n0100000020000n0100000020000n0110400012010A10BPMf<P?P>P9P8D1R?P?PMP?P:PMP?n01109000:3010410?10>2010410D3010410<1012010:1082010010;3010010:1082010410<401051021061033010410<1072010410<,=1%0=R1#J%K=E4%@1%M=E4%?1%P=E4P1P>P8P2P3D3P9P8P2P3O3E4P1AQ4D>RDP8P2P3D3P=PDP8P2P3D1'2eX16X27X06W5X?5X64P9P8P2P3G>X16D6X27D6X06D6X35D6W:o"). Qed.
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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bh11ch21nh33offh41kh51oh62IHh71Kh82b1h92b2h:1ei001eh;2fkh<2k1i012k1h=2k2h>2n1i022n1h?2n2i032n2h@4resti041ai052a1i062a2i072c'i082hii092k0i0:2loi0;1mi0<2n0i0=2nhi0>1vi0?1wi0@1xi0A2zbi0B2zki0C2zli0D2znp;1p;2p;3p;4p;5p;6p;7p;9g00@cj1]Tg01\fj10Tg03QYj1Kj2\j3Rj4Gj5Cj66Tg03RZj1Dj2Uj3Jj4Ej5Bj61Tg00eAj1VTg00GAj2@Tg03SZj13Tg03T?j1TTg03<jj29Tg03T]j2>Tg01IUj2<Tg017?j22Tg01KQj27Tg03L`j2Ij1ATg03D[j2Fj1PTg01K4j2:Tg03EXj7Hj1[Tg03M]j2=j1NTg03FYj2?j1OTg03GSj7;j1LTg00F=R0j1MTg03HQj1QTg00>Fj68Tg03NWj1STg03IRj1ZTg00LGj3YTg00^kl9WTg02A3j55Tg001hj3XTg00NdR1f1R2f0R33Xp=4g012GR4#]R5P5g00\8R6g00]5R7P1^17R8^26R9]3R:]0%03#K%D3P6P:%02/\31U23P7P9f2R9#0?R23AJ923P6P8f3R8#0P9P2P3CGP8P9P2P3CEP7P1f4R:#0P8P9P2P3DCP:P8P9P2P3DBP4f:R;#0P:P8P9P2P3E6P;P:P8P9P2P3E1'4^17^26^37^06X45f9R<%V4P8P9P2P3E1,@1X17X26X37X06f;R=#0P:P8P9P2P3E6P=P:P8P9P2P3E1'4^17^26^37^06P1f<R>f5R?P8P9P2P3E1P4P1f7R@P8P9P8P9P9P8P9P:g016ARAP1P9P1P1P1P1g03U:#3#3#3#3#3#3#3#3#TRB,99RCf6RD/9B'>RE1<<2'2f8RF,73'2RGP0P7P1fBRH#0RI/I@P0P7P1fCRJ#0/F:1:;21:93RK'7RLg00OdRMn10110@00021010C00RNPMn10110@00021010=00PMn0100000020000ROg00ODRPP1P1PIP<PFP@P2P3P8FH,2EPPP?n0100000020000n0100000020000n0110400012010A10BP9n01109000:3010410?10>2010410<3010410<1012010:1082010010;3010010:1082010410<401051021061033010410D1072010410<P4P1P@f@P<P@PDP?P:E1RIf?PFPDP?P:P8E1RQPIPQPQPIPQfARRP;PFP@PDP?E1R;PAP1P9P1P1P1P1PGP0P7P11=H@RSP0P7P11?J:PLPMn10110@00021010C00PMn10110@00021010=00PMn0100000020000PPP1P1PHP<PFP@P2P3P8F;,2EPPPHP=P<PFP@PDE1R=n0100000020000RJn0100000020000n0110400012010A10BPQn01109000:3010410?10>2010410<3010410<1012010:1082010010;3010010:1082010410<401051021061033010410D1072010410<RT'4X01P1^?6^=7^96^>6^<7^86RU%L>P4P1P@PIPQPIPQPQPIPQP;PAP1P9P1P1POPPP1P1P?P<PFP@P2P3P8O6,2EPPP=n0100000020000n0100000020000n0110400012010A10BPQn01109000:3010410?10>2010410<3010410<1012010:1082010010;3010010:1082010410<401051021061033010410D1072010410</4TX0U%M7^:6RU%N>P4P1P@PIPQPIPQPQPIPQP;PAP1P9P1P1P1P1PGP0P7P1P?P@O1PNPMn10110@00021010=00PMn0100000020000PPPJn0100000020000n0110400012010A10BPQn01109000:3010410?10>2010410<3010410<1012010:1082010010;3010010:1082010410<401051021061033010410D1072010410</4TX5UPU%O>P4P1P@PIPQPIPQPQPIPQP;PAP1P9P1P1P1P1PGP0P7P1PSP0P7P1PDP:O1PLPMn10110@00021010C00PMn10110@00021010=00PMn0100000020000PPPJn0100000020000n0110400012010A10BPQn01109000:3010410?10>2010410<3010410<1012010:1082010010;3010010:1082010410<401051021061033010410D1072010410</4TX5UP4P1PDPQf>P@P?P:P8P9E1RUPQPUPUPQPUPIPAP1P9P1P1P1P119?B,>CRC1<F2'2173@'2P0P7P11=RDP0P7P11?H:1:<2/7KPMn10110@00021010C00PMn10110@00021010=00PMn0100000020000PPP1P1PRPFP@PDP2P3P8F;,2CPPP;n0100000020000n0100000020000n0110400012010A10BPUn01109000:3010410?10>2010410<3010410<1012010:1082010010;3010010:1082010410<401051021061033010410D1072010410<,@1%0>R1#P%Q>E8%A1%S>E8%[1%Z>E8P1P?P8P9P2P3E6P:P8P9P2P3O4E8P1AY4D?RDP8P9P2P3E6P>PDP8P9P2P3E1'4eX17X26X37X06W6X@5X74P:P8P9P2P3M9WX17D5X26D5X37D5X06D5X45D5W;o"). Qed.
#[local] Hint Rewrite kfill_xB_eqf : bceq.



(* [comment removed for export] *)
Definition off_image_x (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  ranges_apart_x k b off n (ELit 0) (img_lo A) (ELit (img_hi A - img_lo A)).

Definition off_image_xB (bc : bctx) (b : expr) (off : Z) (n : expr) : bool :=
  ranges_apart_xB bc b off n (ELit 0) (img_lo A) (ELit (img_hi A - img_lo A)).

Lemma off_image_xB_eqf : forall fk, off_image_xB (mkbc fk) = off_image_x fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01bh12b1h22b2h32fkh42k1h52k2h61nh72n1h82n2h93offh:1xh;2x0h<2x1p;1p;2p;3p;7p;6p;4p;5g00@cj1ETg01\fj10Tg03U_j1;j2Dj3<j4?Tg03Vdj15j2Bj3:j4@Tg02<`j16j74Tg00PDj13Tg03Whj17Tg03Xgj18Tg02=ej29Tg001hj32Tg00GAj2CTg02>_j1ATg02?gj1=Tg00>Fj6>Tg02A3j51Tg012G#Eg00\8R0g00]5R1g00NdR2^60R3]9f0R4#0#;%54P1P3f1R3#0/D41B34P0P2f2R5#0?<34A:534P2^80^51^20^70^41^10R6f3R7#6P4P7P5P3g02B5#3R8p,1AR9#7R:%89/9:#3R9O6f4P7P5P3P8P:P9F4522X06P7P5P3P4P8P:P9F4,C2%07R9#A%=7E>P9P5P3P4C?P7P5P3P4C@522eX<0D1X;1D1X:0D1W3o"). Qed.
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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01oh11eh22fkh31nh43offh51xi001xh62x0h72x1i012hii022loi032nhi042nli051pp;1p;2p;3p;6p;4p;5g00@cj1QTg01\fj11Tg03Yfj1Bj2Pj3Gj4LTg03Zfj1>j2Oj3Aj4MTg00F=R0j17Tg03M]j1?j28Tg00aHR1j2=Tg03[ej2<j1ETg03D[j2;j1HTg01K4j20Tg01KQj24Tg017?j22Tg02>Bj2NTg03\ij2:j1CTg03FYj29j1FTg001hj33Tg00GAj2DTg03]jj1@Tg00>Fj66Tg03HQj1ITg03L`j1JTg03NWj1KTg02A3j55Tg012G#Qg00\8R2g00]5R3g00NdR4^32R5]4f0R6#1#B%>6P3P5f1R5#1/P61O56P2P4f2R7#1?G56AA756%73^12R8f3R9#?P01=33R:P4f4R;#1/<9R<P1P3P3P4P6P0P3P4f7R=#1/;;P0P3P4P;f5R>O1g02B5R?109='4107=/06g02BSR@'4'21N?5RA'2RBg00OdRCn10110000021010300PCn10110000021010400n2001105000120102101PCn10110000021010500P0P:P41:;9P1P3P3P4P6P0P3P419=;P0P3P4f8/8>PBPCn10110000021010300RBPCn10110000021010400n2001105000120102101R>PCn10110000021010500RD534X08P8%F9P0P:P4P<P1P3P3P4P6P0P3P4P9P;O1PBPCn10110000021010400n2001105000120102101PCn10110000021010500=34DX08%7:^12R8%C9P0P:P4P6P9O1P>PCn10110000021010500=34DX08P0P:P41:97P1P3P3P4P6P0P3P4f6R1/99P0P3P418=;1091,4?1071/06/4@'2/2APCn10110000021010300PCn10110000021010400n2001105000120102101PCn10110000021010500,D4%19RC#E%@9E6%HC%I9E6%JC%K9E6PCP7P5P6CLP9P7P5P6CM534eX72D5X63D5X52D5W2o"). Qed.
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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01bh12fkh21mh33negh43posh51xh62x0p;1p;2p;3p;6p;5p;4g00@cj1GTg01\fj12Tg03_2j1=j2Fj3@Tg03`3j1:j2Ej3ATg03a3j1>j30Tg01IUj27Tg00aHj2;Tg00eAj19Tg00LGj31Tg017?j23Tg00G[j25Tg001hj38Tg00GAj2DTg03b1j1CTg03c2j1BTg00>Fj6?Tg02A3j56Tg03d7j4<Tg00\8R0g00]5R1f0R2g02B5C<p=4g012G#GP0g00NdR3^20%22#=%:2P0P3f1R4#2/F21E42g03dWR5P3^35]4R5f2R6#>1764R7P21;01R1%46%91R831R9%44=118R:O2P2P:P9O2'3'5f3R;?09:A0;:9'3,57583X051742%42=118R8906:A068:'3'5,D3%26R8#C%B6E?A@842AA642583eX60D6X50D6W1o"). Qed.
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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01ei001eh12fkh21xh31zi011zi021ai031bi042e0i051ii061ki072k0i082loi091ni0:2opi0;2sxp;1p;2p;3p;6p;5g00@cj1DTg01\fj16Tg03eTj1;j2>Tg03fZj17j2?Tg03g_j1Cj22Tg03T?j15Tg03<jj2:Tg03T]j29Tg03h\j18Tg01KQj20Tg001hj33Tg00GAj2BTg03iAj1ATg03jAj1@Tg00>Fj6=Tg02A3j5<Tg03SZj14Tf0R0#4#4p=1g012G#Dg00\8R1g00NdR2%60#;%70g00]5^01R3f1R4#CP1P2P4g03U:R5#1#1#1#1#1#1#5,:0g02B5'9R6%85#1#5R5P4f2R7O1'0f3R8f4R9O1,05R:P:P:P:P9f5R:O1,05R;P;n01100000810101101093010:1021033010:1021033010:1021033010:1021034010;1081091044010;106105109P1P2P4P61287,0512:9,05R;P;P;P;f6/2:,05R:P:n01100000810101101093010:1021033010:1021033010:1021033010:1021034010;1081091044010;107105109532X33P1P2P0P61274,051298,05R5P5P5P5P;P;n01100000810101101093010:1021033010:1021033010:1021033010:1021034010;1081091044010;107105109,B2%64R;#A%@4E=1>;01?40532eX21D<W1o"). Qed.
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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01oh11ei001eh22fkh31xi011xi021ai031bi042e0i051ii061ki072k0i082loi093lo'i0:1ni0;2opi0<1pi0=2p0i0>2sxi0?1zi0@2z0p;1p;2p;3p;6p;5g00@cj1MTg00F=R0j19Tg01\fj12Tg03kEj1<j2GTg03lCj1Lj2=Tg00aHR1j2KTg03m@j1Dj20Tg03nAj1@Tg00F_j28Tg03o>j27j1BTg040>j2;Tg040[j25j1?Tg00lQj1:Tg041_j23j1HTg042\j21j1JTg001hj34Tg00GAj2CTg043]j1ATg00>Fj66Tg044aj1ETg045ij1>Tg046mj1FTg02A3j5ITg012G#Mg00\8R2g00]5R3#9R4f0R5#2#<%L51K33R6#9^12R7f1R8#DP2P4P8%@5,83R9P0P6P4f3R:#2R;f2R<'7R=P1P3P3P4P5P0P6P4f4R>f5R?O1R@P1P3P3P4P51;>8,83n200110=00012010910@RA1838RBn10110100021010=00n200110<00012010810?P0P6P4P8P<O1RCP1P3P3P4P5PBn200110<00012010910?RDP0P6P415;<P1P3P3P4P5PBn200110<00012010810?R;%:3REn10110100021010<00n10110100021010<00n10110100021010<00P0P6P4%2?RF/7>RGP1P3P3P4P5P0P6P4f6RHf7RIO1PAPBn10110100021010=00n200110<00012010810?P0P6P4P:P>O1RJPDP0P6P415F>P;PEn10110100021010<00n10110100021010<00n10110100021010<00RFPFPFPFP0P6P4%2HRF/7?RKP1P3P3P4P5P0P6P4PIf8RLO1PAPBn10110100021010=00n200110<00012010810?P0P6P4P@PDP0P6P415F?P;PEn10110100021010<00n10110100021010<00n10110100021010<00RFPFn0110000081010?1010:3010;1021033010;1021033010;1021033010;1021034010>10810:1044010>10610510:P2P4P8P9P0P6P413:<P1P3P3P4P5P0P6P410H?RFPAPBn10110100021010=00n200110<00012010810?RMP0P6P410:<RNPDP0P6P411:<P;PEn10110100021010<00n10110100021010<00ROn10110100021010<00P0P6P413?>P1P3P3P4P5P0P6P410LIPAPBn10110100021010=00n200110<00012010810?RPP0P6P410?>RQPDP0P6P411?>P;PEn10110100021010<00n10110100021010<00RRn10110100021010<00RSPSPSPSP0P6P413H?P1P3P3P4P5P0P6P4f9/0LPAPBn10110100021010=00n200110<00012010810?RLP0P6P4PFPDP0P6P411H?P;PEn10110100021010<00n10110100021010<00R?n10110100021010<00RTPTn0110000081010?1010:3010;1021033010;1021033010;1021033010;1021034010>10810:1044010>10710510:RT544X07P7%J8P2P4P8P9P0P6P4P=PMP0P6P4PNPDP0P6P4PCP;PEn10110100021010<00n10110100021010<00n10110100021010<00P0P6P4PGPPP0P6P4PQPDP0P6P4PJP;PEn10110100021010<00n10110100021010<00n10110100021010<00RGPGPGPGP0P6P4PKPLP0P6P4PFPDP0P6P4P@P;PEn10110100021010<00n10110100021010<00n10110100021010<00RFPFn0110000081010?1010:3010;1021033010;1021033010;1021033010;1021034010>10810:1044010>10610510:=44TX07P7%H8P2P4P8P9P0P6P4PCPMPOn10110100021010<00P0P6P4PJPPPRn10110100021010<00RRPRPRPRP0P6P4P@PLP?n10110100021010<00R?P?n0110000081010?1010:3010;1021033010;1021033010;1021033010;1021034010>10810:1044010>10610510:=44TX07P2P4P5P9P0P6P413<8P1P3P3P4P5P0P6P4PQPAPBn10110100021010=00n200110<00012010810?P0P6P410<8PDP0P6P411<8P;PEn10110100021010<00n10110100021010<00n10110100021010<00P0P6P413>:P1P3P3P4P5P0P6P410IHPAPBn10110100021010=00n200110<00012010810?P0P6P410>:PDP0P6P411>:P;PEn10110100021010<00n10110100021010<00n10110100021010<00REPEPEPEPSPSn0110000081010?1010:3010;1021033010;1021033010;1021033010;1021034010>10810:1044010>10710510:,C4%28RS#B%A8E6%?S%E8E6%>S%F8E61GS51=85544eX32DIW2o"). Qed.
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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01oh11ei001eh22fkh31xi011xi021ai031bi042e0i052hii063hi'i071ii081ki092k0i0:2loi0;1ni0<2opi0=1pi0>2p0i0?2sxi0@1zi0A2z0p;1p;2p;3p;6p;5g00@cj1MTg00F=R0j19Tg01\fj12Tg0485j1<j2GTg0493j1Lj2=Tg00aHR1j2KTg03m@j1Dj20Tg03nAj1@Tg00F_j28Tg03o>j27j1BTg04:0j2;Tg040[j25j1?Tg00lQj1:Tg041_j23j1HTg042\j21j1JTg001hj34Tg00GAj2CTg043]j1ATg00>Fj66Tg044aj1ETg045ij1>Tg046mj1FTg02A3j5ITg012G#Mg00\8R2g00]5R3#9R4f0R5#2#<%L51K33R6#9^12R7f1R8#DP2P4P8%@5,83R9P0P6P4f3R:#2R;f2R<'7R=P1P3P3P4P5P0P6P4f4R>f5R?O1R@P1P3P3P4P51;:5,83n200110>00012010A106RA1835RBn10110100021010>00n200110=00012010@105P0P6P4P8P<O1RCP1P3P3P4P5PBn200110=00012010@106RDP0P6P415;<P1P3P3P4P5PBn200110=00012010@105R;%:3REn10110100021010=00n10110100021010=00n10110100021010=00P0P6P4%2?RF/7>RGP1P3P3P4P5P0P6P4f6RHf7RIO1PAPBn10110100021010>00n200110=00012010@105P0P6P4P:P>O1RJPDP0P6P415F>P;PEn10110100021010=00n10110100021010=00n10110100021010=00RFPFPFPFP0P6P4%2HRF/7?RKP1P3P3P4P5P0P6P4PIf8RLO1PAPBn10110100021010>00n200110=00012010@105P0P6P4P@PDP0P6P415F?P;PEn10110100021010=00n10110100021010=00n10110100021010=00RFPFn0110000081010@1010;3010<1021033010<1021033010<1021033010<1021034010?10:10;1044010?10810710;P2P4P8P9P0P6P413:<P1P3P3P4P5P0P6P410H?RFPAPBn10110100021010>00n200110=00012010@105RMP0P6P410:<RNPDP0P6P411:<P;PEn10110100021010=00n10110100021010=00ROn10110100021010=00P0P6P413?>P1P3P3P4P5P0P6P410LIPAPBn10110100021010>00n200110=00012010@105RPP0P6P410?>RQPDP0P6P411?>P;PEn10110100021010=00n10110100021010=00RRn10110100021010=00RSPSPSPSP0P6P413H?P1P3P3P4P5P0P6P4f9/0LPAPBn10110100021010>00n200110=00012010@105RLP0P6P4PFPDP0P6P411H?P;PEn10110100021010=00n10110100021010=00R?n10110100021010=00RTPTn0110000081010@1010;3010<1021033010<1021033010<1021033010<1021034010?10:10;1044010?10910710;RT544X07P7%J8P2P4P8P9P0P6P4P=PMP0P6P4PNPDP0P6P4PCP;PEn10110100021010=00n10110100021010=00n10110100021010=00P0P6P4PGPPP0P6P4PQPDP0P6P4PJP;PEn10110100021010=00n10110100021010=00n10110100021010=00RGPGPGPGP0P6P4PKPLP0P6P4PFPDP0P6P4P@P;PEn10110100021010=00n10110100021010=00n10110100021010=00RFPFn0110000081010@1010;3010<1021033010<1021033010<1021033010<1021034010?10:10;1044010?10810710;=44TX07P7%H8P2P4P8P9P0P6P4PCPMPOn10110100021010=00P0P6P4PJPPPRn10110100021010=00RRPRPRPRP0P6P4P@PLP?n10110100021010=00R?P?n0110000081010@1010;3010<1021033010<1021033010<1021033010<1021034010?10:10;1044010?10810710;=44TX07P2P4P5P9P0P6P413<8P1P3P3P4P5P0P6P4PQPAPBn10110100021010>00n200110=00012010@105P0P6P410<8PDP0P6P411<8P;PEn10110100021010=00n10110100021010=00n10110100021010=00P0P6P413>:P1P3P3P4P5P0P6P410IHPAPBn10110100021010>00n200110=00012010@105P0P6P410>:PDP0P6P411>:P;PEn10110100021010=00n10110100021010=00n10110100021010=00REPEPEPEPSPSn0110000081010@1010;3010<1021033010<1021033010<1021033010<1021034010?10:10;1044010?10910710;,C4%28RS#B%A8E6%?S%E8E6%>S%F8E61GS51=85544eX32DIW2o"). Qed.
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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01oh11eh22fkh31xi001xi012e'i022hii033hi'i042loi053lo'i061pi075plaini081sp;1p;2p;3p;6p;5p;4g00@cj1NTg00aHR0j2MTg00F=R1j19Tg01\fj12Tg04:Mj1Lj2GTg04;Jj1Dj2<Tg0493j1@j20Tg04<Fj18Tg03T]j2=Tg03kEj23j1?Tg00F_j26Tg00lQj1;Tg01KQj2KTg02=ej2:Tg040>j2HTg04:0j2CTg03lCj21j1ATg001hj35Tg00GAj2BTg04=Dj1>Tg00>Fj67Tg0485j1ETg04>Fj1FTg02A3j5ITg03d7j4JTg00]5R2P2f1R3f0R4CJp=4g012G#Ng00\8R51M22R6#9R7%24#L%D4%92^15R8%@3P0P5P2P7%83R9g00NdR:P7g02B5,=4R;P1P2P7f4R<#2R=f3R>'3P1P2P7P>P<O1R?1434,66R@%;6RAn10110000021010200PAn10110000021010400RBP1P2P713=3P1P2P7P>f2R=O1P:P71K=3RCP1P6P7P1P2P7f6RD#2f5RE'3P1P2P7PEPDO1P@PAn10110000021010200PAn10110000021010400RFP0P2P2P7P41:<E,H31C4>'4,66n2001106000120104102RG1:3=/44,66RHn10110700021010600PFn0100000020000P1P2P7%2E/3<P1P2P7P<PEO1RFP@PAn10110000021010200PAn10110000021010400n10110000021010300PBn10110000021010500n0100000020000n2001100000121101108P0P5P2P7P9P:P7P;P1P2P711<>P1P2P710E<P@PAn10110000021010200RBPAn10110000021010400RIP1P2P711<3P1P2P710E=RJP:P7PCP1P6P7P1P2P711DEP1P2P7f7/0DP@PAn10110000021010200RKPAn10110000021010400RLPGPHn10110700021010600PLn0100000020000P1P2P711E<P1P2P710DEP@PAn10110000021010200REPAn10110000021010400RDn10110000021010300PIn10110000021010500n0100000020000n2001100000121101108RL557X08P8%A3P0P5P2P7P9P:P7P;P1P2P7P=P>O1PBPAn10110000021010400RBP1P2P7P=P3O1P1P2P7PJP:P7PCP1P6P7P1P2P7PFPKPAn10110000021010400RKPGPHn10110700021010600PKn0100000020000P1P2P7P?PEPAn10110000021010400n10110000021010300PBn10110000021010500n0100000020000n2001100000121101108=57LX08P0P5P2P7%84P:P7P;P1P2P711>=P1P2P710<>P@PAn10110000021010200PAn10110000021010400RAP1P2P711>3P1P2P710<=P:P7PCP1P6P7PDPGPHn10110700021010600PDn0100000020000PIn10110000021010300PAn10110000021010500n0100000020000n2001100000121101108,B7%23RA#?%>3E7%EA%F3E71GA41<34557eX35DIW2o"). Qed.
#[local] Hint Rewrite xb2B_eqf : bceq.


Definition xlo2 (k : list kentry) (e : expr) : option Z := match xb2 k e with Some (lo, _) => Some lo | None => None end.

Definition xlo2B (bc : bctx) (e : expr) : option Z := match xb2B bc e with Some (lo, _) => Some lo | None => None end.

Lemma xlo2B_eqf : forall fk, xlo2B (mkbc fk) = xlo2 fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01eh12fkh21oh31xi001xi012loi021pi031zp;1p;2p;3p;6p;5g00@cj1ATg00F=R0j13Tg01\fj12Tg04?Hj14j2;Tg04@Fj1@j2<Tg00aHR1j2:Tg04;Jj17j20Tg00F_j25Tg00lQj16Tg001hj31Tg00GAj28Tg04:Mj19Tg04ACj1?Tg00>Fj6>Tg02A3j5=Tg012G#Ag00\8R2g00]5R3#3R4f0R5#2#4%@51:33R6#3^02R7f1R8#7P0P6P4P5P8O1P1P3P3P4P51538n2001102000120101103R1%63R3n10110000021010200P0P6P4f2/08P1P3n10110000021010200514X27P0P6P41085P1P3n10110000021010200,84%28R3#9%?8E>1;351<85514eX32D=W1o"). Qed.
#[local] Hint Rewrite xlo2B_eqf : bceq.


Definition xhi2 (k : list kentry) (e : expr) : option Z := match xb2 k e with Some (_, hi) => Some hi | None => None end.

Definition xhi2B (bc : bctx) (e : expr) : option Z := match xb2B bc e with Some (_, hi) => Some hi | None => None end.

Lemma xhi2B_eqf : forall fk, xhi2B (mkbc fk) = xhi2 fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01eh12fkh21oh31xi001xi012hii021pi031zp;1p;2p;3p;6p;5g00@cj1ATg00F=R0j13Tg01\fj12Tg04BDj14j2;Tg04CBj1@j2<Tg00aHR1j2:Tg04;Jj17j20Tg00F_j25Tg00lQj16Tg001hj31Tg00GAj28Tg04:Mj19Tg04ACj1?Tg00>Fj6>Tg02A3j5=Tg012G#Ag00\8R2g00]5R3#3R4f0R5#2#4%@51:33R6#3^02R7f1R8#7P0P6P4P5P8O1P1P3P3P4P51535n2001102000120103101R1%63R3n10110000021010200P0P6P4f2/08P1P3n10110000021010200514X27P0P6P41085P1P3n10110000021010200,84%28R3#9%?8E>1;351<85514eX32D=W1o"). Qed.
#[local] Hint Rewrite xhi2B_eqf : bceq.



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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bh14fuelh21oh33offh41xi001xh52x0h62IHh71fh82fkh91ni014resti021zp;1p;2p;3p;4p;5p;6g00@cj1>Tg00F=R0j1;Tg01\fj10Tg04D?j24j39j4ATg04EDj26j38j42Tg001hj35Tg00GAj27Tg02A3j51Tg003hj13Tg039ij4?j1CTg03T?j1HTg01K4j2=Tg00LGj3GTg00F_j2FTg00lQj1ETg03:ij4:j1DTg04FHj1BTg00>Fj6<Tg04GLj4@Tg012G#>g005LR1g00\8R2g00]5R3%>3R4#;R5]3R6]0R7f2R8#0R9f0R:'416:835R;X11P2P6f1R<#0g01YJR='416=<P3P5A99=:A8=8:P=f3R9P<P:C2,75X53D1X42D1P2P6%09%3<R6'41669P3P5f4R6#0%38R>;9:A8>6:P7f5R>,69P0P3P5f6R?#0P8P<%3=R=C?P0P4P5P<P9g03U:#HR@,=8RAO2AG3<:,F4RB%E4RCn10110000021010100PCn10110000021010200P0P3P5P?P8P<P=C:P0P4P5P>f7P9PAC2PBPCn10110000021010100RAPCn10110000021010200RD555X27%;3^91^33^02R7%D>P0P3P5P:P8P<P=O3PAPCn10110000021010200=55DX27P0P3P5P>P<P:P=C:P0P4P5P6P?P81=<@C2PBPCn10110000021010100PCn10110000021010200,75%0>RC#C%B>E<14C9P8E<PC%39R9P<P:CAP9P>P<P:C2555eX53D1X42D1X6;X71P:C@W1W8o"). Qed.
Lemma kread_bytesB_eqf : forall fk, kread_bytesB (mkbc fk) = (fun fuel => kread_bytes fuel fk).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h04fuelh11bh22fkh33offp;1p;2p;5g00@cj10Tg00F=j16Tg01\fj12Tg04D?j11Tg04EDj25Tg04Gmj24Tg02A3j53Tg012G#0g005LR0g00\8g00]5R1%01#6]3]1f0R1#2#1f1R2,51X001421X00D3W2o"). Qed.
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
  let '(bb, bk) := split_lit b in set_kn cs (kn_havoc (kn cs) bb bk n).

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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01mh11bh22b1h32b2h42fkh52k1h62k2h75kindsh81nh92n1h:2n2h;3offh<1xh=2x0h>2x1h?2x2h@2x3p;1p;2p;3p;4p;5p;7p;6g00@cj14Tg00F=j1OTg01\fj10Tg04I7j1;j2Dj3>j4<j58j6ITg04J@j1Nj2?j3=j4:j59j6JTg03GSj1Mj75Tg04KHj1LTg01Knj1KTg04LGj1CTg04MGj1BTg008Fj36Tg017?j22Tg00bEj1@Tg00cEj1ATg04NIj33Tg001hj37Tg00GAj2ETg03EXj1FTg03IRj1GTg00>Fj6HTg02A3j51Tg012G#4g013FR0#4R1g04NbR2#4R3g00\8R4g00]5R5%O0R6^84R7];R8]1R9]7f0R:#0#;%N:P3P9f1R9#0/D:1?9:P4P8f2R8#0?>9:A=89:P5P7f3R7#0P8P9P:C<P7P8P9P:C:P4P6f4R;#0P7P8P9P:D8P;P7P8P9P:D9g00Nd^:4^65^34^94^55^24R<f5R=#M%L:#KR>%C:#BR?=62='2R@P9P;P7P8%@:RAg02B5RB%A:RCO6'2X00=30=f7P;P7P8PAPBPCF5,2@X00=30=576X1<A62?;,2>f6P7P8P9PAPBPCF5'2X00=30;,E6%0=R0#F%G=EHP0P;P7P8P9P:EIP=P;P7P8P9P:EJ576eX@4D1X?5D1X>4D1X=3D1X<1D1W4o"). Qed.
#[local] Hint Rewrite find_containingB_eqf : bceq.



(* [comment removed for export] *)
Definition shadow_of (k : list kentry) (b n : expr) : expr * Z * expr :=
  let '(sb, sk) := split_lit (eadd (mkSrl k b 3) (ELit (shadow_off A))) in (sb, sk, mkSrl k n 3).

Definition shadow_ofB (bc : bctx) (b n : expr) : expr * Z * expr :=
  let '(sb, sk) := split_lit (eadd (mkSrlB bc b 3) (ELit (shadow_off A))) in (sb, sk, mkSrlB bc n 3).

Lemma shadow_ofB_eqf : forall fk, shadow_ofB (mkbc fk) = shadow_of fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01ah11eh22fkh31nh41sh51xi001xh62x0i012sbi022skp;1p;2p;4p;3p;6p;5g00@cj1GTg00aHR0j27Tg01\fj13Tg04Obj1:j2Ej3BTg04Pej1Fj2?j3=Tg04Qgj1>j31Tg03h\j1<Tg03T?j1;Tg04Rcj19Tg00PDj18Tg04Sfj22Tg01Bjj14Tg03d7j40Tg001hj36Tg00GAj2DTg04Tcj1CTg04Ubj1@Tg00>Fj6ATg02A3j55Tg012G#Gg00\8R1g00]5R2,71R3/71R4^31f0R5#3#:%F5P1P4f1R6#3/E51?65P1^42^01R7f2R8#>P0P1P2P4P5P8g03U:#<#;R9O2p,1A#9#8R:'2#4P3P1P1P2P6P5C0R;P8f3R<P9O2C0n2001100000120101102P0P1P2P4A1<89/2:#4P3P1P;f5?1<9C0n2001100000120101102564X17P0P1P2P4A1869/2:#4P3P1P;f4?189C0n2001100000120101102,D4%38R9#C%@8EAAB965A=865564eX61D5X51D5W2o"). Qed.
#[local] Hint Rewrite shadow_ofB_eqf : bceq.



(* [comment removed for export] *)
Definition lit_entry (ms : list amap) (kd : mkind) (b l : Z) : bool :=
  existsb (fun m => negb (is_fog m) && mkind_eqb (am_kind m) kd
                    && expr_eqb (am_base m) (ELit b) && expr_eqb (am_len m) (ELit l)) ms.
(* [comment removed for export] *)
Definition LS_LO : Z := MID_LO.
Definition LS_LEN : Z := 0x10000000.
Definition HS_LO : Z := 0x2008fff7000.
Definition TWO47 : Z := 0x800000000000.
(* [comment removed for export] *)
Definition end_hi2 (k : list kentry) (b n : expr) : option Z :=
  match xhi k b, xhi k n with
  | Some h, Some m =>
      Some (if Z.ltb (h + m) two64
            then match xhi k (eadd b n) with Some e => Z.min (h + m) e | None => h + m end
            else h + m)
  | _, _ => None
  end.
Definition end_hi2B (bc : bctx) (b n : expr) : option Z :=
  match xhiB bc b, xhiB bc n with
  | Some h, Some m =>
      Some (if Z.ltb (h + m) two64
            then match xhiB bc (eadd b n) with Some e => Z.min (h + m) e | None => h + m end
            else h + m)
  | _, _ => None
  end.
Lemma end_hi2B_eqf : forall fk, end_hi2B (mkbc fk) = end_hi2 fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01ei001eh12fkh21nh31oh41xi011xh52x0i021hi031mp;1p;2p;3p;6p;5g00@cj1FTg00F=R0j1ETg01\fj11Tg04Vej17j2<j3ATg04Wfj1Dj2;j3BTg03M]j1:j20Tg01K4j23Tg02>Bj29Tg04Sfj25Tg04:0j28Tg00F_j22Tg00lQj1CTg001hj36Tg00GAj2=Tg03L`j1>Tg03NWj1?Tg00>Fj6@Tg02A3j54Tg012G#Fg00\8R1g00]5R2#ER3^21f0R4#1#7%D4P1P3f1R5#1/<41;54P3^01R6f2R7#:P0P2P3P4P7O1P0P2P3P5P7O1g00NdR8P21354R9g02BS'9R:P0P2P2P7f4R;f3R<'5R=O11375/84R>P9n10110100021010000P9n0100000020000,22%C2R?n10110100021010300P?n10110100021010200P0P2P310<7P0P2P310;7P8P2P:P0P2P2f5/0=P>P9n10110100021010000P9n0100000020000,22P?n10110100021010300P?n10110100021010200563X36P0P2P31075P0P2P310<5P8P2P:P0P2P215<7,0;P>P9n10110100021010000P9n0100000020000,22P?n10110100021010300P?n10110100021010200,=3%17R?#>%?7E@AA?54AB754563eX51D4X41D4W1o"). Qed.
#[local] Hint Rewrite end_hi2B_eqf : bceq.

(* [comment removed for export] *)
Definition shadow_band_ok (k : list kentry) (ms : list amap) (b n : expr) : bool :=
  let '(bb, bk) := split_lit b in
  let '(sb, sk, sn) := shadow_of k b n in
  (flat_x k sb sk sn && ranges_apart_x k bb bk n (ELit MID_LO) 0 (ELit (KHI - MID_LO))
   && lit_entry ms KRWLAZY LS_LO LS_LEN && lit_entry ms KRWLAZY HS_LO (KHI - HS_LO)
   && Z.leb LS_LO (shadow_off A + 512) && Z.leb (shadow_off A + MID_LO / 8) (LS_LO + LS_LEN)
   && Z.leb HS_LO (shadow_off A + KHI / 8) && Z.leb (shadow_off A + TWO47 / 8) KHI
   && match xlo k b, end_hi2 k b n with                                  (* [comment removed for export] *)
      | Some lo, Some eh => Z.leb 4096 lo && Z.leb eh TWO47
      | _, _ => false
      end)%bool.

Definition shadow_band_okB (bc : bctx) (ms : list amap) (b n : expr) : bool :=
  let '(bb, bk) := split_lit b in
  let '(sb, sk, sn) := shadow_ofB bc b n in
  (flat_xB bc sb sk sn && ranges_apart_xB bc bb bk n (ELit MID_LO) 0 (ELit (KHI - MID_LO))
   && lit_entry ms KRWLAZY LS_LO LS_LEN && lit_entry ms KRWLAZY HS_LO (KHI - HS_LO)
   && Z.leb LS_LO (shadow_off A + 512) && Z.leb (shadow_off A + MID_LO / 8) (LS_LO + LS_LEN)
   && Z.leb HS_LO (shadow_off A + KHI / 8) && Z.leb (shadow_off A + TWO47 / 8) KHI
   && match xloB bc b, end_hi2B bc b n with
      | Some lo, Some eh => Z.leb 4096 lo && Z.leb eh TWO47
      | _, _ => false
      end)%bool.

Lemma shadow_band_okB_eqf : forall fk, shadow_band_okB (mkbc fk) = shadow_band_ok fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bh11nh21oh32b1h42b2h51eh62fkh72k1h82k2h92n1h:2n2h;3offh<1pi001ph=1xi011xh>2x0h?2x1i022bbi032bki042ehi052loi062sbi072ski082snp;1p;2p;3p;4p;7p;6p;5g00@cj1HTg01\fj13Tg04Xfj1Pj2gj3Uj4WTg04Ynj1Kj2Yj3Oj4`Tg00F=R0j1NTg04Wfj1Mj3FTg01Bjj1=Tg00aHR1j2BTg04Obj3Ij1\Tg03Yfj4fj1ZTg00PDj1ETg02=ej2DTg02>_j7Xj1bTg017?j20Tg04[5j4:Tg04Rcj1TTg03SZj18Tg03T?j1<Tg01K4j27Tg01KQj22Tg04\7j29Tg03D[j2Lj1dTg04Pej3@j1JTg03Zfj4>j1QTg02<`j7?j1RTg03FYj2Aj1STg00GAj2eTg03HQj1cTg00>Fj65Tg02?gj1aTg04\Tj1[Tg04]Xj1]Tg04Vej1^Tg04^_j1_Tg02A3j5;Tg001hj3VTf0R2g04_dR3g04`dR4g04abR5C:p=Gf2R6f1R7'0/02p=C%82#8p=6f4R8f3R9'0/06/07/02p=1g00NdR:?V72p=4g012G#Hg013F#HR;g00\8R<P:^1<R=]0%32#P%K2P<P=%37/g21Y72P<P:%36?U72AO672g00]5R>#NR?^1<^0<R@%M9P1P<P>P:%=6RAP11B<>RBP<P:f6RC#3?I89P1P<P>P:P7f:RD#3REP7P2P6CfPEf5RFP8f7RGg04baRH#ERIg02B5RJg04c`RK/DH#ERLFXRM'0f9RN#GROPNP3g04d\RP1DKPRQC:RR3Cp,1A#TRSg03U:#8#6RT#6#6#6RU#<'7,24RV%<TRT,9H,7S1745'2R519KT,7S,2PR4g04eZRH/9T,7S/2KRKD1RSP0P>P:f8RT,LEREP0P>P:PGPNPTO2%8U#6#</27122H'0RHg00OdRUn10110100021010400PUn10110100021010500'0n2001100000120106107n2001101000120100108n2001101000120102103P1P<P>P:PAP1PBP<P:A@C89RWP1P<P>P:P7PDP7P2P6C>RXPDPFP8PGPIPJPLF?'0?CORPVP5P4PKD1RYP0P>P:1ADTP0P>P:f;?FNTPHPUn10110100021010400RZPUn10110100021010500'0n2001100000120106107n2001101000120100108n2001101000120102103R['4X2@1BB<^1<^0<R@%J9P1P<P>P:PAP1PBP<P:P6P8P9O2P1P<P>P:P7P0P>P:PEPZPUn10110100021010500RE,0Sn2001100000120106107n2001101000120100108n2001101000120102103/4[X<@P=^;>^0<R=%Q9P1P<P>P:PAP1PBP<P:PWP1P<P>P:P7PCP7P2P6O3PMPOPRPVD1P5P4PKPED1n2001100000120106107n2001101000120100108n2001101000120102103/4[X0=P:^:<^8>^4<^9<^7>^3<R=%R9P1P<P>P:PAP1PBP<P:PWP1P<P>P:P7PXPCPFP8PGPIPJPLO6POPRPVD1P5P4PKPED1n2001100000120106107n2001101000120100108n2001101000120102103/4[X0=P?^5<R?%S9P1P<P>P:PAP1PBP<P:PWP1P<P>P:P7P0P>P:PCPTO1PZPUn10110100021010500,0Yn2001100000120106107n2001101000120100108n2001101000120102103/4[X2?P1P<P>P:%=7P1PBP<P:A@F96P1P<P>P:P7PNP7P2P6C>PNPFP8PCPIPJPLF?%GTPTP3PPPQC:PVD1P5P4PKP0P>P:1ANGP0P>P:AFDTGPHPUn10110100021010400PUn10110100021010500D1n2001100000120106107n2001101000120100108n2001101000120102103,e:%39R:#d%c9E5%b:%a9E5%Z:%[9E5%\:%]9E5%^:%_9E5P:P6P7P2CWP9P6P7P2C`'4eX?<D;X><D;X=;D;W6o"). Qed.
#[local] Hint Rewrite shadow_band_okB_eqf : bceq.

(* [comment removed for export] *)
Definition shadow_facts (k : list kentry) (ms : list amap) (b n : expr) : list kentry :=
  let '(sb, sk, sn) := shadow_of k b n in
  if (match find_containing k ms [KRWLAZY] sb sk sn with Some _ => true | None => false end
      || shadow_band_ok k ms b n)%bool
  then [KWr (SA sb sk) sn; KZero (SA sb sk) sn] else [].

Definition shadow_factsB (bc : bctx) (ms : list amap) (b n : expr) : list kentry :=
  let '(sb, sk, sn) := shadow_ofB bc b n in
  if (match find_containingB bc ms [KRWLAZY] sb sk sn with Some _ => true | None => false end
      || shadow_band_okB bc ms b n)%bool
  then [KWr (SA sb sk) sn; KZero (SA sb sk) sn] else [].

Lemma shadow_factsB_eqf : forall fk, shadow_factsB (mkbc fk) = shadow_facts fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bh11nh22msh32fkh45kindsh51oh63offh71pi001ph81xi011xh92x0h:2x1i021ai032sbi042ski052snp;1p;2p;3p;6p;4p;5g00@cj16Tg01\fj10Tg04fXj1Bj2Sj3Ij4MTg04g^j1>j2Pj3Aj4<Tg04Ynj1@j47Tg00aHR0j2:Tg04Obj3=j1?Tg00eAj1;Tg00LGj35Tg04I7j6Rj1GTg00G[j21Tg00n;j2QTg01RRj2OTg01LLj2NTg04Pej38j1CTg04J@j69j1ETg001hj32Tg00F=R1j1DTg00GAj2FTg04hcj1HTg00>Fj64Tg04]Xj1JTg04Xfj1KTg04j0j1LTg02A3j53Tg012GR2#6R3g013FR4#6R5g00\8R6P3^16R7]0f0R8#0#B%>8P6P7f1R7#0/S81P78P6P3f2R9#0?I78AA978g00NdR:^16^06^25R;f3R<#@P0g00]5R=,:6R>P6P3f4R?#0?=97P0P6P=P3P7P:P3P1P4P:f8R@#0f7RAg04NbRBg04_d%;B35RCP7P8P9ERg00ODRDg00OdREn10110100021010200RFP?PAf6RGf5RHO3'11Q78RI/O91NI9%;2RI552552R2PIn0100000020000n2001100000120103104n2001101000120100105P0P>P6P3A8?97RJP0P6P=P3P7P:P3P1P4P:P@PAPCP7P8P9E9PDPEn10110100021010200P@PAPGPHC7R@'1P2PIn0100000020000n2001100000120103104n2001101000120100105RK523X0;1:>6^16^06R;%C<P0P>P6P3P8P9P7O2P0P6P=P3P7P:P311F@P2PIn0100000020000n2001100000120103104n2001101000120100105=23KX7;%6B%D4^16^6=^06]4^25RB%E<P0P>P6P3PJP0P6P=P3P7P:P3P1P4P:P?PAPCP7P8P9O5PDPEn10110100021010200/1@P2PIn0100000020000n2001100000120103104n2001101000120100105=23KX5BP0P>P6P3A8<78P0P6P=P3P7P:P3P1P4P:PAPGPCP7P8P9E9PDPEn10110100021010200PAPGPHP?C7'1P2PIn0100000020000n2001100000120103104n2001101000120100105,F3%0<RI#G%H<E4%?I%J<E4%KI%L<E4PIP9P7P8CMP<P9P7P8C<523eX:6D3X96D3X85D3W3o"). Qed.
#[local] Hint Rewrite shadow_factsB_eqf : bceq.



(* [comment removed for export] *)
Definition vis_cost (nhi : Z) : Z := nhi + nhi / 8 + 16384.

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
                           flat_x k0 pb pk (snd p)
                           && ranges_apart_x k0 bb bk n pb pk (snd p) && ranges_apart_x k0 sb sk sn pb pk (snd p)) (a_vis cs)
      (* [comment removed for export] *)
      && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                           flat_x k0 pb pk (snd p) && ranges_apart_x k0 sb sk sn pb pk (snd p)) (a_ghost cs)
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
                           flat_xB bc pb pk (snd p)
                           && ranges_apart_xB bc bb bk n pb pk (snd p) && ranges_apart_xB bc sb sk sn pb pk (snd p)) (a_vis cs)
      (* [comment removed for export] *)
      && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                           flat_xB bc pb pk (snd p) && ranges_apart_xB bc sb sk sn pb pk (snd p)) (a_ghost cs)
      && Z.leb (a_eager cs + a_abytes cs + vis_cost nhi) LIMIT)%bool
  then Some (ACS (mk_ss (pc cs) (s_regs (a_ss cs)) (shadow_factsB bc (a_maps cs) b n ++ k) (nxt cs))
                (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                ((b, n) :: a_vis cs) (a_ghost cs) (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs))
  else None
  | None => None
  end.

Lemma vis_add_eq : forall cs b n k, vis_add cs b n k = vis_add_ref cs b n k.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01pi001ph11bh21nh31eh42b1h52b2h62csh71kh82k1h92k2h:1lh;2msh<2n1h=2n2h>1oh?3offh@1zi012bbi022bki033nhii042pbi052pki062sbi072ski082sni091xp;1p;2p;3p;4p;7p;;p;6g00@cj1WTg00g[j16Tg03g_j1gj2ATg00F=R0j1ITg01Bjj1ETg00aHR1j2DTg01\fj15Tg04Obj3]j1iTg03L`j2Nj1lTg03h\j1aTg03T?j1`Tg01KQj23Tg017?j20Tg03Yfj4Cj1eTg04k<j1\Tg04l8j2BTg000Nj3yTg00ahj3uTg02>_j7?j1oTg00iUj1UTg01;jj32Tg00jSj1PTg04m=j1QTg04n=j1OTg01K4j27Tg04o>j1bTg050?j1LTg00eaj1KTg00f^j1JTg00hVj1HTg04fXj4Mj1hTg051:j3<Tg01e[j49Tg051Wj1GTg052Wj1RTg03d7j4FTg00LGj3STg00_Mj1TTg00`Kj1_Tg053Uj1^Tg054Vl;:Tg00F_j2;Tg00lQj1zTg04Pej3[j1sTg03M]j2Zj1qTg03Zfj4@j1xTg02<`j7>j1wTg04g^j4Xj1tTg001hj34Tg00GAj2mTg03NWj1kTg00>Fj68Tg04]Xj1jTg055Tj1nTg02?gj1fTg04\Tj1pTg03iAj1dj2VTg03jAj1rTg056^j4cTg057^j4vTf2R2f1R3'0f0R4'0p=1f4R5f3R6'0/02/03/04p==A2234,06p=Yg014ER7g00\8R8g012GR9#WR:g00]5R;^38R<%66R=#g%I7R>P1P8P;P>%E6R?P11D8;R@P8P>f6RA#6RB#5f5RC;]5RDP1P8P;P>P3P0P;P>f:RE#6RF#5RGf8RH'NRIg00NdRJP>g03U:#a#`RKf7RLPEO1'3PLf9RMO1,3K'0f;RN#6RO#5RPPAPCPMCC%\NRQ/BERR311BQMRS1D88RTP1P8P;PJAy884#ERUf>#6RV#5RWP3P4Au882RXCCRYPWPMPHf<RZP3P4PXF?R[PWPCP5PAP3P4PXF?RW31n2001109000120104105X0T%UNR\32P1P8P;PJPU10YWn2001109000120104105X0T%PNRY52T%QNR]%ONR^'7%b4R_'7p,5LIMITR`'3RaD=%LNRb%KN#JRcPP%HNRPPEPMCM=<9HPQC9PP%GNRd%RNReP]P8P8PEPMCF=ST\RfPY17^_R^%TNRg%_NRh%^NRiM;:,;7Rj%z7Rkn0100000020000Pkn10110900021010300n2001100000121106107n2001109000121100108n2001109000121101102P1P8P;P>P?P1P@P8P>A[BC5RBP1P8P;P>P3P0P;P>1ZFHPJP>1AOE,3K1AOM,3K'0RlPOPAPCPMC@'0?1RSRmPTP1P8P;PJPUPVP3P4PXC@RnPVPMPHPZP3P4PXF>PVPCP5PAP3P4PXF>RV31n2001109000120104105X0TP\CYP1P8P;PJPU10nVn2001109000120104105X0T=2TY;1aRVPbPcPOPPPEPMCX=<9HPQC9PPPdPeP]PfPYP^PgPhPiM;:,;7Pkn0100000020000ROPkn10110900021010300n2001100000121106107n2001109000121100108n2001109000121101102Ro34X@<PJ^28^?;^18R<%x=P1P8P;P>P?P1P@P8P>PDP1P8P;P>P3P0P;P>PIPJP>PLPAPCPMO3=1lRPSP1P8P;PJPUPEP3P4PXO3RS?1[Wn2001109000120104105X0T=2T\P1P8P;PJPU10SWn2001109000120104105X0T=2TYPaD=PjPkn0100000020000Pkn10110900021010300n2001100000121106107n2001109000121100108n2001109000121101102=4>oX1<PJ^=8^9;^58^<8^8;^48R<%w=P1P8P;P>P?P1P@P8P>PDP1P8P;P>P3P0P;P>PIPJP>PmPTP1P8P;PJPUPEPMPHPZP3P4PXO6PEPCP5PAP3P4PXO6RZ51nn2001109000120104105X0TP\CYP1P8P;PJPU10nZn2001109000120104105X0T=2TY;1aPjPkn0100000020000Pkn10110900021010300n2001100000120106107n2001109000121100108n2001109000121101102=4>oX1<g013F#WP:^28^18];R:%t=P1P8P;P>P?P1P@P8P>PDP1P8P;P>P3P0P;P>PIPJP>PVPbPcPLPPPEPMO3=<9HPQC9PPPdPeP]PfPYP^PgPhPiM;:,;7Pkn0100000020000Pkn10110900021010300n2001100000120106107n2001109000121100108n2001109000121101102=4>oX::1D@8^28^18R:%s=P1P8P;P>P?P1P@P8P>P2PCP5O2P1P8P;P>P3P0P;P>PIPOPkn10110900021010300n2001100000121106107n2001109000121100108n2001109000121101102=4>oX0:%I;^38R:%q=P1P8P;P>P?P1P@P8P>PBP1P8P;P>P3P0P;P>PAPHO1POPkn10110900021010300n2001100000120106107n2001109000121100108n2001109000121101102=4>oX>:P1P8P;P>%E2R:P1P@P8P>%6CRo?[56P1P8P;P>P3P0P;P>%6MRO/ZLPJP>1AFM,3K1AFH,3K'0PFPAPCPHC@%\ERB/BMR?311BBHRIP1P8P;PJPUf=#6RiP3P4PXC@RhPiPMPHPNP3P4PXF>PiPCP5PAP3P4PXF>Rg31n2001109000120104105X0T%UER^52TP1P8P;PJPU10hgn2001109000120104105X0T%PERg52T%QERh%OERY'7/7_/3`R`D=%LERf%KE#JR]PF%HERFPMPHCX=<9LPBC9PF%GERe%RERdPhP8P8PMPHCF=ST^RPPg17Y_RY%TER_%_ERQ%^EREM;:,;7Pkn0100000020000Pkn10110900021010300n2001100000121106107n2001109000121100108n2001109000121101102Rc,m>%5=Rb#l%k=E8%ib%j=E8%hb%n=E8%ob%f=E8%eb%p=E8%db%r=E8P1P8P;P>P:P1P@P8P>%5o?]56P1P8P;P>P3P0P;P>%5O/NLPJP>1VGM,3K1VGH,3K'0PGPAPCPHCC;1?PIP1P8P;PJPU%5iRiP3P4PXCCRIPiPMPHPNP3P4PXF?PiPCP5PAP3P4PXF?RX31n2001109000120104105X0T=2T^P1P8P;PJPU10IXn2001109000120104105X0T=2TgP`D=PfP]PGPFPMPHCM=<9LPBC9PFPePdPhPPPgPYP_PQPEM;:,;7Pkn0100000020000Pkn10110900021110300n2001100000121106107n2001109000121100108n2001109000121101102=4>ceP6P2P3P4CcP6P2P3P4Cv54>eW7X28W1W6o"). Qed.


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
Definition node_casedisj (cs : acs) (b1 b2 : expr) : option (acs * acs) :=
  let k := kn cs in
  match find_disj k b1 b2 with
  | Some (c1, o1, n1, c2, o2, n2) =>
      match flat_x k c1 o1 n1, flat_x k c2 o2 n2, disj_side_fact k c1 o1 n1 c2 o2, disj_side_fact k c2 o2 n2 c1 o1 with
      | true, true, Some K1, Some K2 => Some (add_kn cs [K1], add_kn cs [K2])
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
      && match end_hi2 k b1 n1, end_hi2 k b2 n2 with                       (* [comment removed for export] *)
         | Some e1, Some e2 => Z.leb e1 (2 ^ 47) && Z.leb e2 (2 ^ 47)
         | _, _ => false end
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
      && match end_hi2B bc b1 n1, end_hi2B bc b2 n2 with
         | Some e1, Some e2 => Z.leb e1 (2 ^ 47) && Z.leb e2 (2 ^ 47)
         | _, _ => false end
      && ranges_apart_xB bc c1 o1 n1 c2 o2 n2)%bool
  then Some (add_kn cs [KDisj (SA sb1 sk1) sn1 (SA sb2 sk2) sn2])
  else None.

Lemma node_shdisj_eq : forall cs b1 n1 b2 n2, node_shdisj cs b1 n1 b2 n2 = node_shdisj_ref cs b1 n1 b2 n2.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bh11nh22b1h32b2h42n1h52n2h62csh71eh82k1h92k2h:1oh;3offh<1pi001ph=1zi012c1i022c2i032e1i042e2i052o1i062o2i073sb1i083sb2i093sk1i0:3sk2i0;3sn1i0<3sn2i0=1xp;1p;2p;3p;4p;7p;6p;5g00g[j14Tg03g_j1cj2CTg00F=R0j1GTg01Bjj1ETg00aHR1j2KTg01\fj12Tg04Obj3>j1bTg03h\j1:Tg03T?j1BTg01KQj21Tg03Yfj43j1]Tg04Vej3Aj1RTg03SZj1`Tg058bj2YTg02>_j7Jj1_Tg00n;j2ITg01SQj4VTg00eAj1UTg00LGj3TTg059?j2HTg00F_j2FTg00lQj1PTg04Pej3=j1MTg03Zfj46j1OTg04Wfj3<j1QTg02<`j7Dj1NTg001hj37Tg017?j20Tg00GAj2LTg04^_j1STg00>Fj6;Tg04]Xj1aTg02?gj1^Tg04\Tj1ZTg03iAj1[j2@Tg03jAj1\Tg05:>j5XTg05;Bj5WTf2R2f1R3f0R4'1'0p=9f4R5f3R6'0/02/03/04p=51C34,12p=81023/04p=?g014ER7g00\8R8g00]5R9^78R:%45R;#c%G7R<P1P8P9P<%E5R=P1P8P9P<P=P11K89R>P8P<f9R?#4R@#2f8RAf7RB3>RCP1P8P9P<P3P1P>P8P<f=RD#4RE#2f:RF;>?RGP1P8P9P<P3g00NdRHP<g03U:RI#:#BRJf<RKf@RLO1'1PKf?RMO179JPKf>RNO1,1JPKPDO1,1JfARO#4RP#2RQf;RRPFPMC3PQP?PAPDC3D5PQf5RSP5f6RTC3PQP3P4P2C3P0P9PHAAQLMP0P9PHfB#4RU#2?AMN%`IRI#B%:I#:#:#:#B'YRI,13?94IRIg00OdRVn10110=00021010400PVn10110=00021010300RWPQPRPFPMP?PAPDFJRXD5g012GRY1IS5PT1I34P2CV%UY3TRY,HO,F7RO%P7RZn0100000020000n200110000012010810:n200110=00012010010<n2001100000120107109n200110=00012010010;n200110=000120102106n200110=000120101105P1P8P9P<P=P1P8P9P<P=P1P>P8P<A=@ABR@P1P8P9P<P3P1P>P8P<A=EF?REP1P8P9P<P3PHP<A8JPL1CPM79JA8JPNA8JPD3?R[PPPRPFPMC6PPP?PAPDC6PPPSP5PTC6PPP3P4P2C6D5R\P0P9PHA<PLMP0P9PHA<UMNPIPVn10110=00021010400PVn10110=00021010300PPPRPFPMP?PAPDFDRU3?POPZn0100000020000n200110000012010810:n200110=00012010010<n2001100000120107109n200110=00012010010;n200110=000120102106n200110=000120101105R]37X=:PH^18^;9^08R:%O;P1P8P9P<P=P1P8P9P<P=P1P>P8P<PCP1P8P9P<P3P1P>P8P<PGP1P8P9P<P3PHP<PKPRPFPMO3PKP?PAPDO35?[PKPSP5PTO3PKP3P4P2O3PWPXD5POPZn0100000020000n200110000012010810:n200110=00012010010<n2001100000120107109n200110=00012010010;n200110=000120102106n200110=000120101105=7<]X0:PH^58^99^38^48^89^28R:%N;P1P8P9P<P=P1P8P9P<P=P1P>P8P<PCP1P8P9P<P3P1P>P8P<PGP1P8P9P<P3PHP<10\WRWPKPRPFPMP?PAPDO6'0POPZn0100000020000n200110000012010810:n200110=00012010010<n2001100000120107109n200110=00012010010;n200110=000120102106n200110=000120101105=7<]X0:1K>8^18^08R:%M;P1P8P9P<P=P1P8P9P<P=P1P>P8P<P5PAPBO2P1P8P9P<P3P1P>P8P<PAPFP?O2P1P8P9P<P3PHP<10WUPOPZn0100000020000n200110000012010810:n200110=00012010010<n2001100000120107109n200110=00012010010;n200110=000120102106n200110=000120101105=7<]X<:%G9^18^08R:%Q;P1P8P9P<P=P1P8P9P<P=P1P>P8P<P@P1P8P9P<P3P1P>P8P<PEP1P8P9P<P3PHP<P0P9PHPKPLPMO2P0P9PHPDPMPNO2PIPVn10110=00021010400PVn10110=00021010300=?\UPOPZn0100000020000n200110000012010810:n200110=00012010010<n2001100000120107109n200110=00012010010;n200110=000120102106n200110=000120101105=7<]X::P1P8P9P<%E6R:P1P8P9P<P:P1P>P8P<%4AR]?=BTP1P8P9P<P3P1P>P8P<%4KRO?=?AP1P8P9P<P3PHP<%4LRU=8JM1CUN79JA8JUDA8JUKPUPRPFPNC6PUP?PAPKC6D5PUPSP5PTC6PUP3P4P2C6P0P9PHA<UMNP0P9PHA<PNDPIPVn10110=00021010400PVn10110=00021010300PUPRPFPNP?PAPKFDD51HLY,F7R7PZn0100000020000n200110000012010810:n200110=00012010010<n2001100000120107109n200110=00012010010;n200110=000120102106n200110=000120101105RY,L<%2;RL#R%S;E;%bL%a;E;%_L%^;E;%]L%Z;E;%[L%\;E;P1P8P9P<P:P1P8P9P<P:P1P>P8P<%2]?>BTP1P8P9P<P3P1P>P8P<%2O?>?AP1P8P9P<P3PHP<%2URU/@M,1J1@UN79J1@UD,1J1@UK,1JPUPRPFPNC3PUP?PAPKC3D5PUPSP5PTC3PUP3P4P2C3P0P9PHAAUMNP0P9PHAAQNDPIPVn10110=00021010400PVn10110=00021010300PUPRPFPNP?PAPKFJD5P7PZn0100000020000n200110000012010810:n200110=00012010010<n2001100000120107109n200110=00012010010;n200110=000120102106n200110=000120101105=7<YeP5P6P2P3P4DXP5P6P2P3P4DW57<eX58X38X48W2W6o"). Qed.


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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01eh11oh22csh31zi002hii013leni022loi031xp;1p;2p;4p;3p;6g00g[j18Tg03g_j1Xj2?Tg00aHj2CTg00F=R0j1@Tg003hj1>Tg05<Jj2DTg02>Bj2BTg05=Jj1RTg00PDj1OTg03d7j47Tg00F_j2<Tg00lQj1WTg01\fj1=Tg01Anj25Tg03D[j2Gj1KTg03L`j2Fj1ITg03h\j16Tg03SZj14Tg03T?j1;Tg01KQj22Tg017?j20Tg058bj2STg03FYj2Ej1MTg03M]j2Aj1NTg001hj33Tg00GAj2LTg03HQj1JTg00>Fj69Tg03NWj1PTg03iAj1Qj2TTg03jAj1HTg05>Jj1UTg05?Kj1VTf0R1#>#>p=1g00\8R2g00]5R3f1R4P1C7p=:g014EP3^02R5%81R6#X1C23R7/C3R8#@R9P0P3P9g01YJ#>#1#1#1#1#1R:,D4R;g00NdR<P9g02B5R=/B1P7P3%R1R>#O/:>P>C7,<8%W8R>n0100000020000R?P0P3P9%84R@#=RA154:RB'GRCP0P3P9f2RD#8RE#=RF15D:RG'FP<P91B=4R=g03U:RH#6#4#4#;RIPDf3RD/5:RJO1'2'0%4HRH#;%6H#6#6#4#;'S,21RH'0P7P31:J4P1C7,<8RKP>n0100000020000P>n10110300021010000P>n10110300021010200n10110300021010100P0P3P9P;P?P0P3P91E@BP0P3P91AEGP<P9%8D/?J,2I,0=/0HPKP>n0100000020000RKP>n10110300021010000RJP>n10110300021010200n10110300021010100RD33X35%@3^02R2%N6P0P3P9P;P?P0P3P9PCP0P3P9P4PGO1PKP>n10110300021010000P>n10110300021010200n10110300021010100=39DX12P2%M6P0P3P9P;P?P0P3P9P1PBO1PJP>n10110300021010200n10110300021010100=39DX12P0P3P91D1:R2P?P0P3P9151:R:,E6P0P3P91A@BP<P91?EG,2I,0=/0HP7P31:G4P1C7,<8R8P>n0100000020000P>n10110300021010000P>n10110300021010200n10110300021010100R4,L9%=6R7#K%J6E9%I7%P6E9%Q7%H6E9P0P3P9P2P?P0P3P91G7:P0P3P91FABP<P91TFG,2I,0=/0HP8P>n0100000020000P>n10110300021010000P>n10110300021010200n10110300021010100=394e%U1%V1539eW2o"). Qed.


(* [comment removed for export] *)
Fixpoint inside_maps (k : list kentry) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  match ms with
  | [] => false
  | m :: rest => (negb (is_fog m) && xinside k b off len (am_base m) 0 (am_len m)) || inside_maps k rest b off len
  end.

Fixpoint inside_mapsB (bc : bctx) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  match ms with
  | [] => false
  | m :: rest => (negb (is_fog m) && xinsideB bc b off len (am_base m) 0 (am_len m)) || inside_mapsB bc rest b off len
  end.

Lemma inside_mapsB_eqf : forall fk, inside_mapsB (mkbc fk) = inside_maps fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01bh13lenh23offh32msh42IHh52b1h62b2h72fkh82k1h92k2h:1mh;2n1h<2n2h=4restp;1p;2p;3p;4p;5p;7p;6p;8g00@cj1>Tg01\fj10Tg05@Pj1Cj2Mj3Jj4Aj53Tg05AUj1?j2Kj3Bj4@j51Tg001hj32Tg00eAj1LTg00GAj2=Tg04KHj1<Tg01Knj1;Tg00bEj18Tg00cEj17Tg03EXj7Ij1ETg017?j24Tg00G[j26Tg03GSj79j1DTg03IRj1FTg00>Fj6:Tg00LGj3GTg00^kj8HTg02A3j55Tg012G#>g013FR0#>R1g00\8R2g00]5R3g00NdR4^12R5]2R6]0f0R7#0#C%?7P2P6f1R6#0/M71K67P3P5f2R5#0?J67AB567P2P4f3R8#0P5P6P7CAP8P5P6P7C@P0f8R9#0P8P5P6P7D3P9P8P5P6P7D1524^12^23^02X31f7%L0P5P6P7D1,=4X12X23X02f9R9#0P8P5P6P7D3P9P8P5P6P7D1524^12^23^02P4f:R9f4R:P5P6P7D1R;f6R<#<#;R=f;R>#0P8P5P6%8<R?g02B5R@%7<R<FI'4/67P>P8P5P6P?P@P<F9,4=P>f5R>P8P5P6D1RA'6RB524X04P4^<2^93^62^;2^83^52RC%D9P7P8P5P6P?P@P<O6,4=/6A=24BX0C%<>#;P9P5P6P7%8>P@%7>F9'4/6;,=4%09R;#E%F9E:P;P:P5P6P7D3P8P5P6P7O3E:P;AG0>:R>P5P6P7D3P9P>P5P6P7D1524eX12X23X02W4X=1X:0P8P5P6P7GHX12D5X23D5X02D5X31D5W7o"). Qed.
#[local] Hint Rewrite inside_mapsB_eqf : bceq.



(* [comment removed for export] *)
Definition lit_ivs (ms : list amap) : list (Z * Z) :=
  flat_map (fun m => if is_fog m then [] else
                     match am_base m, am_len m with
                     | ELit b, ELit l => [(zlit64 b, zlit64 b + zlit64 l)]
                     | _, _ => []
                     end) ms.
(* [comment removed for export] *)
Fixpoint band_covered_from (ivs : list (Z * Z)) (fuel : nat) (cur hi : Z) : bool :=
  if Z.leb hi cur then true else
  match fuel with
  | O => false
  | S f => match List.find (fun iv => (Z.leb (fst iv) cur && Z.ltb cur (snd iv))%bool) ivs with
           | Some iv => band_covered_from ivs f (snd iv) hi
           | None => false
           end
  end.
Definition band_covered (ms : list amap) (lo hi : Z) : bool :=
  let ivs := lit_ivs ms in band_covered_from ivs (length ivs) lo hi.

(* [comment removed for export] *)
Definition in_band (k : list kentry) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  (band_covered ms MID_LO KHI && xinside k b off len (ELit MID_LO) 0 (ELit (KHI - MID_LO)))%bool.
Definition in_bandB (bc : bctx) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  (band_covered ms MID_LO KHI && xinsideB bc b off len (ELit MID_LO) 0 (ELit (KHI - MID_LO)))%bool.
Lemma in_bandB_eqf : forall fk, in_bandB (mkbc fk) = in_band fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01bh12b1h22b2h32fkh42k1h52k2h63lenh72n1h82n2h93offh:1xh;2x0h<2x1h=2x2p;1p;2p;3p;4p;7p;6p;5g00@cj17Tg01\fj10Tg05BYj1=j2Gj3>j4;j5ATg05CZj19j2Ej3<j4:j5BTg03GSj18j76Tg05DZj33Tg00PDj14Tg02=ej2FTg017?j22Tg001hj35Tg00GAj2DTg03EXj1CTg03IRj1?Tg00>Fj6@Tg02A3j51Tg012G#7g013F#7R0g00\8R1g00]5R2g00NdR3^61R4]9R5]0f0R6#0#=%96P1P5f1R5#0/G61E56P2P4f2R4#0?>56A<456P1P3f3R7#0P4P5P6C;P7P4P5P6C:P3^81^52^21^71^42^11R8f4R9#8g04baR:g04c`R;539R<P6P7P4P5%4:R=g02B5R>1F;:#4R?O6'2f5P7P4P5P=P>P?F6,2<553X08A37:;P9P4P5P6P=P>P?F6'2,D3%09R?#C%?9E@P?P7P4P5P6DAP9P7P4P5P6DB553eX=1D1X<2D1X;1D1X:0D1W3o"). Qed.
#[local] Hint Rewrite in_bandB_eqf : bceq.

Definition safe_range (k : list kentry) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  ((match xhi k len, base_range k b with
    | Some lh, Some (lo, hi) =>
        (Z.leb (img_lo A) (lo + off) && Z.leb (hi + off + lh) (img_hi A))       (* [comment removed for export] *)
    | _, _ => false
    end)
   || xinside k b off len e_sp0 STK_OFF (ELit STK_LEN)                            (* [comment removed for export] *)
   || inside_maps k ms b off len
   || in_band k ms b off len)%bool.                                                (* [comment removed for export] *)

Definition safe_rangeB (bc : bctx) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  ((match xhiB bc len, base_rangeB bc b with
    | Some lh, Some (lo, hi) =>
        (Z.leb (img_lo A) (lo + off) && Z.leb (hi + off + lh) (img_hi A))       (* [comment removed for export] *)
    | _, _ => false
    end)
   || xinsideB bc b off len e_sp0 STK_OFF (ELit STK_LEN)                          (* [comment removed for export] *)
   || inside_mapsB bc ms b off len
   || in_bandB bc ms b off len)%bool.                                              (* [comment removed for export] *)

Lemma safe_rangeB_eqf : forall fk, safe_rangeB (mkbc fk) = safe_range fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bh11eh21oh32b1h42b2h52fkh62k1h72k2h83lenh92msh:2n1h;2n2h<3offh=1xi001xh>2x0h?2x1h@2x2i012hii022lhi032loi041pp;1p;2p;3p;4p;7p;5p;6g00@cj1?Tg01\fj12Tg05E_j1Hj2bj3Mj4Ej5ZTg05Fcj1Cj2Vj3Gj4Dj5[Tg05CZj1Bj5<Tg03L`j2Aj1STg00aHR0j2@Tg03[ej2aj1QTg03Whj1]Tg01K4j24Tg01KQj26Tg03Xgj1TTg017?j2=Tg00PDj1LTg03EXj7Ij1_Tg00G[j20Tg05@Pj5Fj1\Tg03M]j2:j1NTg03\ij2;j1OTg03GSj7>j1KTg05AUj58j1JTg00F=R1j19Tg00GAj2PTg03]jj1RTg00>Fj65Tg03NWj1`Tg03IRj1^Tg05Gfj1YTg05BYj1XTg05Hoj1WTg02A3j57Tg001hj3UTf2R2f1R3'0f0R4'0p=1g00NdR5?U34p=3g012G#?g013F#?R6g00\8R7g00]5R8P5^87R9]<R:]0R;%24#H%C4P7P:%23/b41V34P8P9%22?M34AG234P7P5f3R9#2P2P3P4CEP9P2P3P4CDP;^96R;f4R:#BP1P8P5f5R<#2R=/A3P11@88R>P5f6R?#2/a:P0P8P8P5P4p,1AR@#]RA143?'6144?/49%T@R@'6'=n2001104000120103101RBg00OdRCn10110000021010400RDPCn10110000021010200REP=P9P2P3g05J4RFg05K2RGg05L2#LRHFI'0RIP=P:P9P2P3DFP4P:P9P2P3O4R=31P1P8P51:<3RJP1P>P51;?:PBPCn10110000021010400PCn10110000021010200P<P9P2P3PFPGPHF>R?'0P<P:P9P2P3D8RKP<P:P9P2P3D<RL31RM'3X0;P;%J:A1I=L/3MX0;P5^;7^78^47^:7^68^37R;%K:P4P9P2P3PFPGPHO6,0E?1KL/3MX0;%98^17R;%N:P1P8P5P4P3O1PDPCn10110000021010200/0??1KL/3MX2;%9>^17R;%O:P1P8P5PJP1P>P5P3P:O1PBPCn10110000021010400PCn10110000021010200/0??1KL/3MX2;P1P8P51::4P1P>P51;<9P0P8P8P5P4143<,6A144</49/6@'=n2001104000120103101PCn10110000021010400PCn10110000021010200P:P2P3P4PFPGPHF>'0P:P9P2P3P4D8P:P9P2P3P4D<31,P5%2:R5#Q%R:E5%S5%`:E5%_5%^:E5%\5%Y:E5%X5%W:E5P5P9P2P3P4DZP:P9P2P3P4D['3eX@7D7X?8D7X>7D7X=6D7W5o"). Qed.
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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bi001bh11Ki011Kh22fkh33lenh42msh53offh61xh72x0i021ai032a1i042a2i051ci061ei072hii081ki092k0i0:1li0;2loi0<1mi0=1ni0>2n1i0?2n2i0@1oi0A1vi0B1wp;1p;2p;5p;3p;6g00@cj14Tg01\fj13Tg05M2j1;j2Dj3>Tg05N8j17j2Aj3?Tg05Fcj1<j51Tg003hj10Tg01>;j2:Tg01JTj19Tg00PDj18Tg017?j22Tg001hj36Tg00GAj2CTg05E_j1BTg05O=j1@Tg00>Fj6=Tg02A3j55Tg012GR0#4g013F#4R1g00NdR2^10f0R3#3#;%73P0P2f1R4#3/D31A43g00\8R5g00]5P2^35]5]0^41R5f2R6#<P0P2P4g016AR7P2P6f3R8g01YJ#0#0#0#0#0#0#0#0':R9f5R:f7R;P4P3%98#8R<O4'2n0110200012010010@P7P2P4f4f6R=P4P3P6O4n0110200012010010@R>P7P2P6P:P;P4P3P8O4n0110200012010010@R?g00ODR@P@P@P>P@P?P>n01101000:3010210B10A2010210:3010210:1082010;1072010610<3010610;1072010210=4010310>10410?3010210:1052010210:P0P2P4P7P2P6f8R>P;P4P3P<D1,29n0110200012010010@P7P2P4P;P=P4P3P6D1n0110200012010010@R?P7P2P6P>P;P4P3P8D1n0110200012010010@R>P@P@P@P?P@P>P?n01101000:3010210B10A2010210:3010210:1092010;1072010610<3010610;1072010210=4010310>10410?3010210:1052010210:562X05P0P2P3P7P2P6P;P=P4P3P<D1,29n0110200012010010@P7P2P4P=P:P4P3P6D1n0110200012010010@R:P7P2P6P;P=P4P3P8D1n0110200012010010@R8P@P@P@P:P@P8P:n01101000:3010210B10A2010210:3010210:1092010;1072010610<3010610;1072010210=4010310>10410?3010210:1052010210:,C2%36R:#B%@6E=A>:43A?643562eX70D5X61D5W2o"). Qed.
#[local] Hint Rewrite grant_keep_bB_eqf : bceq.



Definition kn_grant_filter (k : list kentry) (ms : list amap) : list kentry :=
  kimg_clip (List.filter (grant_keep_b k ms) k).

Definition kn_grant_filterB (bc : bctx) (ms : list amap) : list kentry :=
  kimg_clip (List.filter (grant_keep_bB bc ms) (bc_fk bc)).

Lemma kn_grant_filterB_eqf : forall fk, kn_grant_filterB (mkbc fk) = kn_grant_filter fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01Kh11bh22fkh31lh42msh51xp;1p;3p;2p;6p;5g00@cj17Tg01\fj13Tg05PEj1;j2>Tg05QNj1:j2<Tg05N8j1Aj24Tg02N=j16Tg01E0j31Tg05RVj10Tg001hj32Tg00GAj29Tg02P:j18Tg00>Fj65Tg05M2j1@Tg05SXj1?Tg02A3j5=Tg012GR0#7R1g013F#7R2P1f0R3#3#;%:3g00Nd^00^42R4f1R5#AP3P5O1f2R6#3#6510#01465R7=106#0R6521X14P1P5A1073#0=216X311453=105#0,91%35R0#6%85E5%@0%?5E51>031<53521eX52D=W2o"). Qed.
#[local] Hint Rewrite kn_grant_filterB_eqf : bceq.



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
Definition null_kend (base ne : expr) (lb nlo : Z) : list kentry :=
  match ne with
  | ELit _ => []
  | _ => [KRange (eadd base ne) (lb + nlo) TOPMAX]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition iv_meets (c n : Z) (iv : Z * Z) : bool := (Z.ltb (fst iv) (c + n) && Z.ltb c (snd iv) && Z.ltb (fst iv) (snd iv))%bool.
Fixpoint lowbound_from (ivs : list (Z * Z)) (fuel : nat) (n c : Z) : Z :=
  match fuel with
  | O => c
  | S f => match List.find (iv_meets c n) ivs with
           | Some iv => lowbound_from ivs f n (Z.max c (page_up (snd iv)))
           | None => c
           end
  end.
Definition lowbound (ms : list amap) (n : Z) : Z :=
  let ivs := (img_lo A, img_hi A) :: lit_ivs ms in lowbound_from ivs (S (length ivs)) n 4096.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pd_ok (k : list kentry) : bool :=
  (Z.leb 12 (ealign k e_pd) &&
   match erange k (esub e_sp0 e_pd) with
   | Some (lo, hi) => (Z.leb 0 lo && Z.leb hi 4095)%bool
   | None => false
   end)%bool.
Definition pd_okB (bc : bctx) : bool :=
  (Z.leb 12 (ealignB bc e_pd) &&
   match erangeB bc (esub e_sp0 e_pd) with
   | Some (lo, hi) => (Z.leb 0 lo && Z.leb hi 4095)%bool
   | None => false
   end)%bool.
Lemma pd_okB_eqf : forall fk, pd_okB (mkbc fk) = pd_ok fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01eh12fkh21oh31zi002hii012loi021pi031xp;1p;2p;3p;6g00@cj1HTg03g_j1Gj26Tg03h\j14Tg03SZj15Tg03T?j19Tg01KQj20Tg00aHR0j2?Tg01\fj18Tg05Tbj2<Tg03o>j2;j1BTg017?j22Tg041_j2:j1DTg001hj33Tg00F=R1j1FTg00GAj2CTg043]j1@Tg00>Fj67Tg03iAj1ATg03jAj1>Tg05U_j1=Tg05V^j1ETf0R2#4#4p=1g012G#Hg00\8R3g00]5R4]0R5%G2g00NdR6g03U:#4R7#5#5#9R8P2g05W\R9O1'0P11?44R:P6f1R;#8g05J4/<9R<';P0P4P4P6P2g02B5/0;%17#1#1#1#1#9,02'2n2001102000120101100R7g00OdR4n10110300021010200'216;9,08R0P1P:P61:;<P7P4n10110300021010200'2R;33X35%F:^03R3%D2P1P:P6P2P<O1P7P4n10110300021010200,20=36;X231629,08P1P:P61:2<P7P4n10110300021010200'2,C6%82R4#B%@2E7%A4%>2E7%=4%E2536eW1o"). Qed.
#[local] Hint Rewrite pd_okB_eqf : bceq.
Definition pd_disj (k : list kentry) (bb : expr) (bk : Z) (ne : expr) : list kentry :=
  if pd_ok k then [KDisj (SA bb bk) ne (SA e_pd STK_OFF) (ELit STK_WTOP)] else [].

Definition grant_facts (k : list kentry) (ms : list amap) (v : nat) (base ne : expr) (lb nlo : Z) : list kentry :=
  KDisj (SA base 0) ne (SA e_sp0 STK_OFF) (ELit STK_LEN)
  :: KRange (EVar v) (lb / 4096) ((TOPMAX - nlo) / 4096)
  :: pd_disj k base 0 ne ++
  (if Z.ltb lb (img_hi A) then [KDisj (SA base 0) ne (SA (ELit (img_lo A)) 0) (ELit (img_hi A - img_lo A))] else [])
  ++ (if band_covered ms MID_LO KHI then [KDisj (SA base 0) ne (SA (ELit MID_LO) 0) (ELit (KHI - MID_LO))] else [])
  ++ null_kend base ne lb nlo.

Definition mmap_null (cs : acs) (kind : mkind) (eager visible : bool) : option acs :=
  match mmap_len cs with
  | Some (ne, nlo, nhi) =>
      if (fresh_ok cs && expr_vars_lt (nxt cs) ne
          && gap_ok cs nhi && (negb eager || budget_ok cs nhi)
          && no_holes (a_maps cs))%bool then     (* [comment removed for export] *)
        let v := nxt cs in
        let base := escale 4096 (EVar v) in
        let lb := lowbound (a_maps cs) nlo in   (* [comment removed for export] *)
        let kfacts := grant_facts (kn cs) (a_maps cs) v base ne lb nlo ++ kdisj_new (a_maps cs) base ne in
        let kmem := [KWr (SA base 0) ne; KZero (SA base 0) ne] in
        let k' := kfacts ++ kn_grant_filter (kn cs) (a_maps cs) in
        let cs1 := add_entry cs (sr_upd (s_regs (a_ss cs)) 10 base) k' (S v) (AM base ne kind) nhi eager (a_ylo cs) in
        if visible then vis_add cs1 base ne (kmem ++ kn cs1) else Some cs1
      else None
  | None => None
  end.

(* [comment removed for export] *)
Definition fixed_args (cs : acs) (top : Z) : option (expr * Z * expr * Z * Z) :=
  let k := kn cs in let a := reg cs 10 in
  let '(b, off) := split_lit a in
  match mmap_len cs, xlo k a, xhi k a with
  | Some (ne, nlo, nhi), Some alo, Some ahi =>
      if (page_aligned k a && Z.ltb 0 alo && (Z.leb (img_hi A) alo || Z.leb TOPMAX top) && Z.leb (ahi + nhi) top && flat_x k b off ne)%bool then Some (b, off, ne, nlo, nhi) else None
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
  let k' := ksh ++ kn_grant_filter k ms0 in
  let cs1 := add_entry (with_maps0 cs ms0) (s_regs (a_ss cs)) k' (nxt cs) m nhi eager (a_ylo cs) in
  if visible then vis_add cs1 a ne (kmem ++ kn cs1) else Some cs1.

Definition mmap_fixed_free (cs : acs) (kind : mkind) (eager visible : bool) : option acs :=
  let k := kn cs in
  let a := reg cs 10 in
  match fixed_args cs CEIL with
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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01Ki001Kh12ukh22unh31bh42b1h52fkh62k1h71lh82n1i012n1h91sh:2sph;2ubh<1xh=2x0h>2x1i021ai032a1i042a2i051ci061ei072hii081ki092k0i0:2loi0;1mi0<1ni0=2n2i0>1vi0?1wp;1p;2p;3p;4p;6p;5g00@cj1ITg01\fj10Tg05XYj1<j2Hj3=j4CTg05Y\j18j2Fj3;j4DTg02DXj1:j65Tg02M;j49j1?Tg02N=j16Tg01E0j31Tg02O;j47j1GTg001hj32Tg00GAj2ETg02P:j1>Tg00>Fj63Tg02Q=j1@Tg02COj1ATg02RCj1BTg02A3j54Tg012GR0#IR1g00\8R2g00]5R3P1^22R4]1f0R5#0#<%85P3P4f1R4#0/H51F45P2P1f2R6#0?=45A;645g02I9R7g00NdR8^00^22^13^;2]:R9f3R:#:P0P8P5f4R;f8R<#0f7R=f6R>f5R?C9P=P>P?P:O5R@g00ODRAP@PAPAPAPAPAP@PAn01100000:3010210?10>2010210<3010210<1082010:1072010610;3010610:1072010210<4010310110410=3010210<1052010210<X00%0;#6R@510P0P8P5P<P<P=P>P?C7P=P>P?P:E5RBPAPBPAPAPAPAPAPBPAn01100000:3010210?10>2010210<3010210<1092010:1072010610;3010610:1072010210<4010310110410=3010210<1052010210<X00=10;RC521X39P7^82^63^42R7%G:P0P8P5P<P;P=P>P?O3P=P>P?P:E5R<PAP<PAPAPAPAPAP<PAn01100000:3010210?10>2010210<3010210<1082010:1072010610;3010610:1072010210<4010310110410=3010210<1052010210<X00=10@=21CX97P1P:P0P8P5PBPAPBPAPAPAPAPAPBPAn01100000:3010210?10>2010210<3010210<1082010:1072010610;3010610:1072010210<4010310110410=3010210<1052010210<X00=105=21CX71P0P8P5P=P=P>P?P;C7P>P?P;P:E5R;PAP;PAPAPAPAPAP;PAn01100000:3010210?10>2010210<3010210<1092010:1072010610;3010610:1072010210<4010310110410=3010210<1052010210<X00=10:,E1%0:R0#6%>:E3%?0%@:E3%A0%B:E3P0P6P4P5CCP:P6P4P5CD521eX>2D4X=3D4X<2D4W5o"). Qed.
#[local] Hint Rewrite kn_rezeroB_eqf : bceq.

Definition kn_rezeroM (k : list kentry) := kn_rezeroB (mkbc k).
Lemma kn_rezeroM_eq : kn_rezeroM = kn_rezero.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01kh12ubh22ukh32unp;1p;3p;5g00@cj15Tg05Z^j14Tg05[eR0j10Tg05Y\R1j11Tg001hj33Tg02A3j52Tg012G#5R2g00\8R3g00]5P2^33]2]1R3P0P1f0R1#4%01%11533eX02D2o"). Qed.



(* [comment removed for export] *)
Definition rekind (ms : list amap) (m : amap) : list amap :=
  map (fun m' => if amap_eqb m' m then AM (am_base m') (am_len m') KRW else m') ms.

(* [comment removed for export] *)
Inductive fixed_in_arm := ArmE | ArmF | ArmG.

(* [comment removed for export] *)
Definition fixed_in_args_ref (cs : acs) (arm : fixed_in_arm) : option (expr * Z * expr * Z * Z * amap) :=
  match fixed_args cs TOPMAX with
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
  match fixed_args cs TOPMAX with
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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h03armi003armh11bi011bh22csh35kindsh42msh51nh61oh73offi023offi031mi042nei053nhii063nloi071pi082p0i092p1i0:2p2i0;1xp;1p;2p;3p;4p;6g00@cj1<Tg00F=R0j1@Tg00g[j16Tg04J@j1Aj6>Tg00aHR1j22Tg05\hj2=Tg00hVj1;Tg00eAj1DTg00LGj33Tg04k<j18Tg04l8j24Tg01Anj27Tg017?j2?Tg03d7j40Tg00F_j2KTg00lQj1JTg001hj35Tg00GAj2ITg01\fj19Tg04I7j1Hj6FTg04hcj1CTg00>Fj6ETg05]kj2BTg05_1j2GTg003hj1:Tf0R2#:#:p=1g014Eg05`;R3g013FR4#<g04NbR5#<R6g00\8R7g00]5R8%@4^57]7]1]3]4R9f1R:#6R;#A1278R</27R=/28R>/28R?/24R@#@RAP0P?PAf2RBg05aBRC'=RDP1P>P8PAP2P1P=P8PAP:P1P<P7PAP:P1P7P8PAP:P0P4PAf9REf;RF#;RGP3P6f:RHg05bAg05cAg05dA%D5RI535535535RJg04_d=35IRIPJn011000003000000R5P:P2PBO5g00NdRKPAf<RL#8RMf3RN'4g01YJ#1#1#1#1#1RO,7L,4M'?P?P4P>P8P=P8P<P7P7P8PBP:C0PNC0f5C0f7C0P2C0,K@RM%J@R@n0100000020000RLP@n10110;00021010300n200110:000120101102n200110900012010:104n2001108000120109106n2001107000121108105P@n10110;00021110700P0P?PAPDP1P>P8PAP2P1P=P8PAP:P1P<P7PAP:P1P7P8PAP:P0P4PA%6FPGP5P:P2PBE>PLP@n10110;00021010300n200110:000120101102n200110900012010:104n2001108000120109106n2001107000121108105P@n10110;0002111070035X69P0P?PA1=:CRCP1P>P8PAP2P1P=P8PAP:P1P<P7PAP:P1P7P8PAP:P0P4PA%6HR9%;HRHP3P6PEPJPIPJn011000003000000RJP:P2PBE>PKPA%8FRK/4N17FO,4K'?PMP@n0100000020000RMP@n10110;00021010300n200110:000120101102n200110900012010:104n2001108000120109106n2001107000121108105P@n10110;00021110700RK,IA%9;#H%C;EEP0P?PAPCP1P>P8PAP2P1P=P8PAP:P1P<P7PAP:P1P7P8PAP:P0P4PA%99PHPJP:P2PBEFPMP@n10110;00021010300n200110:000120101102n200110900012010:104n2001108000120109106n2001107000121108105P@n10110;00021110700=5AKe1B:21G:255AeW0W2o"). Qed.


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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01lh13armi003armh22csh32ubh42ukh52uni011bi021mi032nei043nhii053nloi063offi071pi082p0i092p1i0:2p2i0;2p3i0<1xp;1p;2p;4p;;p;3p;6g00@cj1QTg00g[j12Tg035Wj1]j4NTg00F=R0j1[Tg00aHR1j28Tg05]kj2MTg05eAj2KTg050?j1CTg03SZj1ATg03T?j1\Tg01K4j2:Tg00eaj1>Tg00f^j1=Tg01\fj1;Tg02J7j4Rj1hTg05RVj10Tg05XYj4Pj1fTg01_]j1OTg01e[j43Tg00hVj1STg05fCj2LTg051Wj1JTg052Wj1BTg04m=j1DTg00iUj1ETg00jSj1FTg04n=j1GTg00_Mj1HTg00`Kj1@Tg053Uj1ITg054Vl;4Tg01Anj2?Tg00n;j2ZTg01RRj2YTg01LLj2XTg056^j45Tg00lQj1WTg02K:j4Vj1jTg05Y\j4Uj1kTg001hj39Tg00GAj2iTg02SPj1gTg00>Fj6<Tg05Z^j1eTg034Tj1cj4aTg037_j1bTg05gBj2`Tg05hHj2dTg003hj1TTg00LGj3_Tg00F_j2^Tf0R2#T#Tp=7g012GR3f1R4;_2p=1g014ER5/^2p=6g05`;R6g00\8R7g00]5R8%Q3R3^57]4]3R9%24R:#]%[5R;P01878R</87R=/88R>/88R?g013FR@'8RAP;f2RB/M4RCP1P?P@P;P2P1P>P8P;P4P1P=P8P;P4P1P<P7P;P4P1P7P8P;P4g00NdRDP;P6PDf<REf=RFf6RG'Kg00ODRHPHn011000003000000RIP6P;PE%CFg03U:#A#A#\RJ':RK%>FRL#=RMP6P3PE%2FRN#;ROP4P2PBCR#0RPPOP4P2PBCP#0f;ROP4P2PBO3#0RQn011000003000000%OLRLC3P6%Q@RRPE%SFRSf8RT'LRUPSPUn011000003000000RU%JFRS%BFRVP6P8PE%DFRW/:GPWPWn011000003000000RW%EFRX%FFRY%GFRZ%HFR[%@FR\%IFR]M;4R^g01YJ#7#7#7#7#7R_,?FRFPB1Z42R`/YBRa1X`BR`%2^'1'1C5%6^R^P^n011000003000000%W5R^n0100000020100n200110;000121101106n200110:00012110;103n200110900012110:105n2001108000121109104n2001107000121108102P^n10110<00021110700P0PAP;PCP1P?P@P;P2P1P>P8P;P4P1P=P8P;P4P1P<P7P;P4P1P7P8P;P4PDP;PIP6P;PEPKPMP6P3PEPNP4P2PBCV#0PNP4P2PBCU#0RbPNP4P2PBCN#0RNn011000003000000PLC3PUPSPVPWPXPYPZP[P\P]M;4RcPFPB%2c,1`,1aC5%6cRcPcn011000003000000P^n0100000020100n200110;000121101106n200110:00012110;103n200110900012110:105n2001108000121109104n2001107000121108102P^n10110<00021110700Rc39X09P9%k:P0PAP;PCP1P?P@P;P2P1P>P8P;P4P1P=P8P;P4P1P<P7P;P4P1P7P8P;P4PDP;PIP6P;PEPKPMP6P3PEPPPQPNn011000003000000PLC3PUPSPVPWPXPYPZP[P\P]M;4RPPFPB%2P,1`,1aC5%6PRPPPn011000003000000P^n0100000020100n200110;000121101106n200110:00012110;103n200110900012110:105n2001108000121109104n2001107000121108102P^n10110<00021110700=9;cX09P9%j:P0PAP;PCP1P?P@P;P2P1P>P8P;P4P1P=P8P;P4P1P<P7P;P4P1P7P8P;P4PDP;PIP6P;PEPKPMP6P3PEPQPbPNn011000003000000PLC3PUPSPVPWPXPYPZP[P\P]M;4R]PFPB%2],1`,1aC5%6]R]P]n011000003000000P^n0100000020100n200110;000121101106n200110:00012110;103n200110900012110:105n2001108000121109104n2001107000121108102P^n10110<00021110700=9;cX09P0PAP;1M42R9P1P?P@P;P2P1P>P8P;P4P1P=P8P;P4P1P<P7P;P4P1P7P8P;P4PDP;P6PDPO1KEGPHPHn011000003000000RHP6P;PO%CE/:JRJ%>ERc#=R]P6P3PO%2ERFP4P2PBCV#0PFP4P2PBCU#0PFP4P2PBCN#0n011000003000000%OcRcC3P6PRPO%SERR/LTRTPRPTn011000003000000RT%JERR%BER\P6P8PO%DER[/:GP[P[n011000003000000R[%EERG%FERZ%GERY%HERX%@ERW%IERVM;4RS1?E_R_PB%2S,1`,1aC5%6SRSPSn011000003000000P^n0100000020100n200110;000121101106n200110:00012110;103n200110900012110:105n2001108000121109104n2001107000121108102P^n10110<00021110700RS,i;%;:RE#h%g:E<%fE%e:E<%cE%b:E<P0PAP;P9P1P?P@P;P2P1P>P8P;P4P1P=P8P;P4P1P<P7P;P4P1P7P8P;P4PDP;PHP6P;POPJP]P6P3PO%;FRFP4P2PBCR#0PFP4P2PBCP#0PFP4P2PBCa#0n011000003000000PcC3PTPRP\P[PGPZPYPXPWPVM;4RVP_PB%2V,1`,1aC5%6VRVPVn011000003010000P^n0100000020100n200110;000121101106n200110:00012110;103n200110900012110:105n2001108000121109104n2001107000121108102P^n10110<00021110700=9;Se1`421d4259;eW1X25o"). Qed.


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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bh12csh24holei004holeh31lh43lnei013lneh51mh62neh73offh83rnei023rneh92ubh:2ukh;2unp;1p;2p;3p;5p;4p;;p;6p;8g00@cj1HTg00g[j1TTg035Wj1Zj4VTg050?j1>Tg03SZj1WTg03T?j1\Tg01K4j2FTg00eaj1BTg00f^j1@Tg00PDj1XTg05iRj3<Tg01Anj2;Tg00bEj1CTg05jOj3STg00cEj1KTg05kRj5ITg05RVj15Tg01_]j1ETg01e[j47Tg05lUj32Tg00eAj1YTg00hVj1DTg05Tbj26Tg04LGj1GTg04Sfj28Tg051:j34Tg05mTj3?Tg051Wj1JTg052Wj1=Tg04m=j1LTg00iUj1MTg00jSj1NTg04n=j1OTg00_Mj1PTg00`Kj1QTg053Uj1RTg054Vl;9Tg001hj3:Tg00GAj2cTg01\fj1bTg034Tj1aj4^Tg037_j1`Tg00>Fj6_Tg05nZj8]Tg05ofj8[Tg003hj1UTg00LGj3ATf0R0#U#Up=3g012GR1f1R2;A0p=0g013FR3?A20p=1g00NdR4g014ER5g00\8R6g00]5R7%H1^;6^:7^96R7f6R1#TR8#Zf7R9#>g03U:#W#W#\R:'FR;%B9R<#@g01YJ#3#3#3#3#3R=g0616#XR>3<R?1;9=R@f3RA#CRBf2RC3SRDP@f4REPB%KARFP2DIRGP0P1f5RHPEO3#5'0'0%E<R<C7P4%H3RIf8g0629RJ92@E%Y3RK'1PKn0110000020000%D9P4PIPC16@B%GARL52B/1KPKn0110100020000P4PIP218@ER@18BF/6@;2L/1KPKn01102000200005437?A543RL%J9R@%=9RF%L9RB%M9RM%N9RN%O9RO%P9RP%Q9RQ%R9RRM;9P;P?%T9P1PHPECV#5,0G,0DP<C7PLP@PFPBPMPNPOPPPQPRM;95:5X37%>1/F:R:%B1R7#@?<=>R>1;1=R=%CCRR;S2RQP=PAPR%KCRPP0DIROP8PHPEPACV#5'0'0%E7R7C7P4PIP9A2=AJ/1KPKn0110000020000%D1P4PIP216=R%GCRJ52R/1KPKn0110100020000P4PIP018=AR=18RP/6=;2J/1KPKn01102000200005437?C543RK%J1RJ%=1R=%L1RP%M1RR%N1RI%O1RN%P1RM%Q1RB%R1RFM;9R@,c5%b8RL#a%`8E_P:P>PLPHPEPAC^#5,0O,0QP7C7PKPJP=PPPRPIPNPMPBPFM;9=:5@eP9P1PHPEPAPCP2P0G]P9P1PHPEPAPCP2P0G[5:5eX84X44X53X66W7W0W1W2o"). Qed.


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
                 | 3, 0x22 => mmap_null cs KRW true true               (* [comment removed for export] *)
                 | 3, 0x4022 => mmap_null cs KRWLAZY false true        (* [comment removed for export] *)
                 | 0, 0x22 => mmap_null cs KNONE false false           (* [comment removed for export] *)
                 | 0, 0x4022 => mmap_null cs KNONELAZY false false     (* [comment removed for export] *)
                 | _, _ => None
                 end
               else
                 match prot, flags with
                 | 3, 0x4032 => mmap_fixed_free cs KRWLAZY false false  (* [comment removed for export] *)
                 | 3, 0x32 => mmap_fixed_free cs KRW true true          (* [comment removed for export] *)
                 | 0, 0x4032 => mmap_fixed_free cs KNONELAZY false false (* [comment removed for export] *)
                 | 0, 0x32 => mmap_fixed_free cs KNONE false false      (* [comment removed for export] *)
                 | 3, 0x104022 => mmap_fixed_free cs KRWLAZY false false   (* [comment removed for export] *)
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
  match reg_lit cs 17, reg_lit cs 12, fixed_args cs TOPMAX with
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
  match reg_lit cs 17, reg_lit cs 12, fixed_args cs TOPMAX with
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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bi001bh12csh25kindsh31lh42msh51nh61oh73offi013offh82ubh92ukh:2uni021mi032nei043nhii053nloi061pi072p0i082p1i093p10i0:3p11i0;3p12i0<2p2i0=2p3i0>2p4i0?2p5i0@2p6i0A2p7i0B2p8i0C2p9i0D1xi0E1zi0F2z0p;1p;2p;3p;4p;;p;6g00@cj1ATg00F=R0j1LTg00g[j11Tg04J@j1\j6VTg003hj1>Tg05<Jj2=Tg00lQj1^Tg00aHR1j2:Tg05\hj2FTg00hVj1?Tg00eAj1[Tg00LGj3@Tg05eAj2YTg04k<j1WTg04l8j2<Tg017?j29Tg01Anj2QTg050?j1NTg03SZj1UTg03T?j1_Tg01K4j27Tg00eaj1JTg00f^j1ITg00PDj1]Tg05iRj3GTg01\fj1;Tg02J7j4Hj1fTg05RVj16Tg01_]j1KTg01e[j44Tg05fCj2ETg051Wj1DTg052Wj1MTg04m=j1CTg00iUj1OTg00jSj1PTg04n=j1BTg00_Mj1RTg00`Kj1STg053Uj1ZTg054Vl;5Tg00n;j2kTg01RRj2jTg01LLj2iTg056^j43Tg02K:j4Xj1hTg001hj38Tg00GAj2gTg02SPj1eTg00>Fj6TTg04I7j1bj6dTg04hcj1cTg0639j1aTg064?j1`Tf0R2#>#>p=2g012GR3f1R4;@2p=0g014ER5g013FR6#Ag04NbR7#Ag00\8R8g00]5R9%L6^58]7]0]2]4R:%12R;#\%L5R<P0P9P<g01YJ#2#2#2#2#2R=#2R>#>#2#2R?,=4R@P9P<P2%^5R5g005kRAP<P2P5PAP<P2PAP<P2P5PAP<P2P5PAP<P2P5PAP<P2PAP<P2PAP<P2P5P5P0P9P<f:/=>RBP9P<P2P5PAP<P2PAP<P2P5P5P01:89RC/:8RD/:9RE/:9RFP<f=g05aBRG'FRHP1PEP9P<P2P1PDP9P<P4P1PCP8P<P4P1P8P9P<P4P0P6P<fERIfFRJ#?RKg05cAg05dA%[75@75@7R7P4P2f2RLO5g00NdRMP<fGRNf7RO'Y%WNRPf3RQ'<'91QN=RR,<P'9RP%NNg03U:#U#U#_RS'7RT%JNRU#Ig02B5#]RV7G=RW%1NRX#;PLP4PQCH#6%KURUC4%?N/E2RY%DNRZ%MNR[%CN/7OR\%ONR]%PNR^%BNR_%RNR`%SNRa%ZNRNM;5RbPRPQ1kL4Rc/jQRd1icQRc%1b'0'0C3P5n0100000020000P5n10110D00021010200n200110;000121100101n200110:00012110;103n200110900012110:105n200110C000121109104P5n10110D00021110C00n0110B00031010C1010C01P5P5n0110A00031110B1010B00P5n0110F0003001110A1010AP5n10110D00021110F00n0110@00031010A1010A01P5P5n0110?00031110@1010@00P5P5n0110>00031110?1010?00P5n0110=00031010>1110>00P5n0110<00031010=1110=00P5n0110800031010<1110<00P5P5n011070003111081010800P5n011060003101071110700P5n0110E0003001110610106P5n10110D00021110E00P0P9P<P@P9P<P2P5PAP<P2P5PAP<P2PAP<P2P5PAP<P2P5PAP<P2P5PAP<P2PAP<P2PAP<P2P5P5P0P9P<PBP9P<P2P5PAP<P2PAP<P2P5P5P0PFP<PHP1PEP9P<P2P1PDP9P<P4P1PCP8P<P4P1P8P9P<P4P0P6P<%1JRbPKP7P4P2PLEVRePMP<PPPTPWPXPLP4PQCX#6PUC4PYPZP[P\P]P^P_P`PaPNM;5RXPRPQ%1X,0c,0dC3P5n0100000020000P5n10110D00021010200n200110;000121100101n200110:00012110;103n200110900012110:105n200110C000121109104P5n10110D00021110C00n0110B00031010C1010C01P5P5n0110A00031110B1010B00P5n0110F0003001110A1010AP5n10110D00021110F00n0110@00031010A1010A01P5P5n0110?00031110@1010@00P5P5n0110>00031110?1010?00P5n0110=00031010>1110>00P5n0110<00031010=1110=00P5n0110800031010<1110<00P5P5n011070003111081010800P5n011060003101071110700P5n0110E0003001110610106P5n10110D00021110E00RX38X6:%A3^:8^99^88R3%h;P0P9P<P@P9P<P2P5PAP<P2P5PAP<P2PAP<P2P5PAP<P2P5PAP<P2P5PAP<P2PAP<P2PAP<P2P5P5P0P9P<PBP9P<P2P5PAP<P2PAP<P2P5P5P0PFP<PHP1PEP9P<P2P1PDP9P<P4P1PCP8P<P4P1P8P9P<P4P0P6P<PePMP<PPPTPWPJPLP4PQO3#6PUC4PYPZP[P\P]P^P_P`PaPNM;5RNPRPQ%1N,0c,0dC3P5n0100000020000P5n10110D00021010200n200110;000121100101n200110:00012110;103n200110900012110:105n200110C000121109104P5n10110D00021110C00n0110B00031010C1010C01P5P5n0110A00031110B1010B00P5n0110F0003001110A1010AP5n10110D00021110F00n0110@00031010A1010A01P5P5n0110?00031110@1010@00P5P5n0110>00031110?1010?00P5n0110=00031010>1110>00P5n0110<00031010=1110=00P5n0110800031010<1110<00P5P5n011070003111081010800P5n011060003101071110700P5n0110E0003001110610106P5n10110D00021110E00=8<XX33P0P9P<1=2?R?P9P<P2P5PAP<P2P5PAP<P2PAP<P2P5PAP<P2P5PAP<P2P5PAP<P2PAP<P2PAP<P2P5P5P0P9P<f9/=>R>P9P<P2P5PAP<P2PAP<P2P5P5P0PFP<f</FGRGP1PEP9P<P2P1PDP9P<P4P1PCP8P<P4P1P8P9P<P4P0P6P<%1IR3%?IRIP7P4P2PLEVPMP<1YJO%WJRX/<Q'91QJ=RN,<X'9RX%NJ/7SRS%JJRR#I?G=VRVPbPLP4PQCX#6%KRRRC41EK2RK%DJR=%MJRa%CJ/7ORO%OJR`%PJR_%BJR^%RJR]%SJR\%ZJRJM;5R[PNPQ%1[,0c,0dC3P5n0100000020000P5n10110D00021010200n200110;000121100101n200110:00012110;103n200110900012110:105n200110C000121109104P5n10110D00021110C00n0110B00031010C1010C01P5P5n0110A00031110B1010B00P5n0110F0003001110A1010AP5n10110D00021110F00n0110@00031010A1010A01P5P5n0110?00031110@1010@00P5P5n0110>00031110?1010?00P5n0110=00031010>1110>00P5n0110<00031010=1110=00P5n0110800031010<1110<00P5P5n011070003111081010800P5n011060003101071110700P5n0110E0003001110610106P5n10110D00021110E00R[,g<%;;RZ#f%e;ET%bZ%c;ETP0P9P<P?P9P<P2P5PAP<P2P5PAP<P2PAP<P2P5PAP<P2P5PAP<P2P5PAP<P2PAP<P2PAP<P2P5P5P0P9P<P>P9P<P2P5PAP<P2PAP<P2P5P5P0PFP<PGP1PEP9P<P2P1PDP9P<P4P1PCP8P<P4P1P8P9P<P4P0P6P<%;3PIP7P4P2PLEdPMP<PXPSPV%;bPLP4PQCH#6PRC4PKP=PaPOP`P_P^P]P\PJM;5RJPNPQ%1J,0c,0dC3P5n0100000020000P5n10110D00021010200n200110;000121100101n200110:00012110;103n200110900012110:105n200110C000121109104P5n10110D00021110C00n0110B00031010C1010C01P5P5n0110A00031110B1010B00P5n0110F0003001110A1010AP5n10110D00021110F00n0110@00031010A1010A01P5P5n0110?00031110@1010@00P5P5n0110>00031110?1010?00P5n0110=00031010>1110>00P5n0110<00031010=1110=00P5n0110800031010<1110<00P5P5n011070003111081010800P5n011060003101071110700P5n0110E0003001110610106P5n10110D00021110E00=8<[e%a2%`258<eW1o"). Qed.


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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01mh11nh21bh32fkh41xh52x0h62x1p;1p;2p;3p;6p;4p;5g00@cj1GTg01\fj11Tg065Ij1=j2Fj3>j4ATg066Mj1:j2Ej3<j4BTg03`3j1;j38Tg04KHj14Tg01Knj13Tg00bEj17Tg01IUj26Tg017?j20Tg00cEj19Tg001hj35Tg00GAj2DTg03_2j1CTg067Pj1?Tg00>Fj6@Tg02A3j52Tg012G#Gg00\8R0g013FR1g00NdR2]0R3^10f0R4#1#=%:4P0P3f1R3#1/F41E34P1P2f2R5#1?>34A<534P2^00^10R6f3R7#;%43#3%73,67'0R8P4P5%93R9O2'0f4?859,08552X26%44#3%74,65'0%949873'0,D2%17R6#C%?7E@P6P5P3P4CAP7P5P3P4CB552eX61D2X50D2X40D2W3o"). Qed.
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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01pi001ph11bh22kkh31mh41eh51nh61kh71lh82b1h92b2h:2csh;2k1h<2k2h=2n1h>2n2h?1oh@3offhA2ubhB2ukhC2unhD1zi011zi022bbi032bki042hii052nei063nhii073nloi082p0i092p1i0:2p2i0;2p3i0<2p4i0=2p5i0>2p6i0?2p7i0@2p8i0A2pbi0B2pki0C2sbi0D2ski0E2sni0F1xp%0p&0p;1p;2p;3p;4p;7p;5p;;p;6g00g[j1;Tg066Mk10Nj3\j4WTg00F=R0j1UTg003hj1LTg05<Jj2_Tg00lQk10KTg00aHR1j2CTg05>Jj1RTg01Anj2>Tg01Bjj1GTg00hVj1eTg008Fj3DTg01\fj1=Tg03eTj2mk105Tg03Yfj4jj1xTg03L`j2]k100Tg01K4j2JTg02>Bk20JTg04Obj3Bj1}Tg03h\k10FTg03T?j1TTg03iAj2Aj1vTg01KQj28Tg017?j21Tg03EXj7Pk102Tg03OXj5Qj1zTg02>_j7Vk104Tg01Knj19Tg00iUj1OTg01E0j32Tg01;jj3<Tg050?j1ZTg03SZj1nTg00eaj1MTg00f^j1STg00PDj1pTg05iRj3oTg00@ck10MTg02TWS00k40LTg02J7j4lk10;Tg01_]j1kTg051Wj1iTg052Wj1hTg04m=j1dTg00jSj1^Tg051:j3@Tg04n=j1`Tg00_Mj1aTg00`Kj1bTg053Uj1cTg054Vl;5Tg03fZj2[k10=Tg03Zfj4fk10DTg03M]j2gk108Tg04Pej3Fk109Tg03g_j2Ek10ETg03GSj7Yk107Tg03PYj5Xk10>Tg02<`j7Nk10<Tg02K:S01j4Hk10CTg001hj33Tg00GAk203Tg00>Fj64Tg03IRj1~Tg03NWk101Tg04]Xj1|Tg02?gj1{Tg068Uk106Tg069_k10:Tg02SPj1yTg04\Tj1wTg03jAk10?Tg065Ik10@k30Ak40BTg06:dj1uTg06;lj1tTg06=0j1sTg000Nk30GTg00ahj3rTg007Ik50HTg01e[k40ITg00F_j2qTf0R2#L#Lp=:f2R3f1R4'1/12p=0g00\8R5@0G52p=IAr552p=Kf7R6f6R7f5R8f4R9f3R:P3P4I0HP2H0Ip=7g014ER;/q2p=6A<342,1:p=?g013FR<g00NdR=]3^55^15R>%;2R?$0N%U;R@P0g00]5RAP@g01YJ#:#:#:#:#:RB#L#:#:#:S02,_4RCPAP@P2&0K;RDg005kREP@P2PEP@P2PEP@P2PEP@P2PDPEP@P2PEP@P2PDPEP@P2PEP@P2PDPDP01C5ARF/CARGP@f:RH#RRIP1PFPAP@P2P1P5PAP@P4P1P5PAP@f?/>B#GRJP=P@f@RKfARL/>BRMP:O2%eLRN5D<%;LRO#=RP/mMRQPPP4P2P:CjRR30P0PAP=1]PM1J28g02BS+0JRSg00OdRTn10110F00021010400RU1C55RVP1P5PAP=%I2RW#GRXP1PFP5P=fD#;RY#=RZ%I3R[%K3R\3BR]P1P5PAP=P4g03U:R^$0F#TR_fH#;R`#=Ra%I7Rb'A'8%K7Rc,Aa,8_'1PaP8P9Pcf8RdP6PHFPRePaP`P4P2P3DQRa30n200110800012010C10Dn200110F00012010810En200110F00012010A10BX0VP1P5PAP=PXPZP4P2P\P9P:P7FVRZ#9n200110F00012010A10BX0V%OLRf52VRg3<30%ZL%n^#n#TS03'JR^%MLRh#Sg02B5#pS047oBRig012G$0MRjPVP1PFP5PjfCS05#;Rk#=S06%K2Rl7BWP1P5PAPjP4P8P4P2P3H0Ln200110800012010C10DS07n200110F00012010810EX0VX2jRmPgPPP4P2P:Cl%khRhG7S08PLfBRn/>BS09P9P2O3#9X3<=2<N%iLRo%hLRp%dLRqP1P5PAP=PXPZn200110F00012010A10BX0V=2VfRZ%^LRr9@VgRs%`LRt%aLRu%bLRv%cLRLM;5#6PDn0100000020100n200110F000121102103n200110@000121105107n200110?00012110@106PDn10110F00021110?00n0110>00031010?1010?01PDPDn0110=00031110>1010>00PDn0110<00031010=1110=00PDPDn0110;00031110<1010<00PDn0110:00031010;1110;00PDPDn0110900031110:1010:00PDPDn011080003111091010900PDPDn011000003111081010800PDn011010003001110010100PDn10110F00021110100P0PAP@PCPAP@P2PDPEP@P2PEP@P2PEP@P2PEP@P2PDPEP@P2PEP@P2PDPEP@P2PEP@P2PDPDP0PGP@PIP1PFPAP@P2P1P5PAP@P4P1P5PAP@PJP=P@A\OM:=D<NRw1[OMPOP4P2P:CfRx30RyP0PAP=1gOMPSPTn10110F00021010400'1S0:PVP1P5PAP=PXP1PFP5P=AFY[\S0;P1P5PAP=P41E`b,8_1E`c,8_'1RzP`P8P9PcPdP6PHFYP`P`P4P2P3DXR{30n200110800012010C10Dn200110F00012010810En200110F00012010A10BX0VP1P5PAP=PXPYP4P2P\P9P:P7FNRY#9n200110F00012010A10BX0V=2VfR|C?S0<P^PiPjPVP1PFP5PjAFkWlS0=P1P5PAPjP4P8P4P2P3CHn200110800012010C10DS0>n200110F00012010810EX0VX2jP|POP4P2P:CHR}PhG7%;nR~Q09P9P2CW#9X3<=2<NRNPoPpPqP1P5PAP=PXPYn200110F00012010A10BX0V=2VfS09A@V|rS0?PtPuPvPLM;5#6PDn0100000020100n200110F000121102103n200110@000121105107n200110?00012110@106PDn10110F00021110?00n0110>00031010?1010?01PDPDn0110=00031110>1010>00PDn0110<00031010=1110=00PDPDn0110;00031110<1010<00PDn0110:00031010;1110;00PDPDn0110900031110:1010:00PDPDn011080003111091010900PDPDn011000003111081010800PDn011010003001110010100PDn10110F00021110100RY33X1>PA^45R>&0E?P0PAP@PCPAP@P2PDPEP@P2PEP@P2PEP@P2PEP@P2PDPEP@P2PEP@P2PDPEP@P2PEP@P2PDPDP0PGP@PIP1PFPAP@P2P1P5PAP@P4P1P5PAP@PJP=P@11wQRQ/1RP1P5PAP=PXP1PFP5P=P]P1P5PAP=P4fGRRPbO1,8_PRPcO1,8_'1?0ean200110800012010C10Dn200110F00012010810En200110F00012010A10BX0V=<Vg70UQ08PNPoPpPqPZPsPtPuPvPLM;5#6S08PDn0100000020100n200110F000121102103n200110@000121105107n200110?00012110@106PDn10110F00021110?00n0110>00031010?1010?01PDPDn0110=00031110>1010>00PDn0110<00031010=1110=00PDPDn0110;00031110<1010<00PDn0110:00031010;1110;00PDPDn0110900031110:1010:00PDPDn011080003111091010900PDPDn011000003111081010800PDn011010003001110010100PDn10110F00021110100=3@YXD>P=^55^@A^15R>&0D?P0PAP@PCPAP@P2PDPEP@P2PEP@P2PEP@P2PEP@P2PDPEP@P2PEP@P2PDPEP@P2PEP@P2PDPDP0PGP@PIP1PFPAP@P2P1P5PAP@P4P1P5PAP@PJP=P@PKP4P2P:O3S0@,1QP1P5PAP=PXP1PFP5P=P]P1P5PAP=P411zeRe/1an200110800012010C10Dn200110F00012010810En200110F00012010A10BX0V=<VgS0A70UQ08PDn0100000020100n200110F000121102103n200110@000121105107n200110?00012110@106PDn10110F00021110?00n0110>00031010?1010?01PDPDn0110=00031110>1010>00PDn0110<00031010=1110=00PDPDn0110;00031110<1010<00PDn0110:00031010;1110;00PDPDn0110900031110:1010:00PDPDn011080003111091010900PDPDn011000003111081010800PDn011010003001110010100PDn10110F00021110100=3@YX1>Pj^C5^BA^A5Ra&0C?P0PAP@PCPAP@P2PDPEP@P2PEP@P2PEP@P2PEP@P2PDPEP@P2PEP@P2PDPEP@P2PEP@P2PDPDP0PGP@PIP1PFPAP@P2P1P5PAP@P4P1P5PAP@PJP=P@A0QxURQQ0A'1P^PiPjPVPmPgQ0@PhG7PNPoPpPqPZPsPtPuPvPLM;5#6PDn0100000020100n200110F000121102103n200110@000121105107n200110?00012110@106PDn10110F00021110?00n0110>00031010?1010?01PDPDn0110=00031110>1010>00PDn0110<00031010=1110=00PDPDn0110;00031110<1010<00PDn0110:00031010;1110;00PDPDn0110900031110:1010:00PDPDn011080003111091010900PDPDn011000003111081010800PDn011010003001110010100PDn10110F00021110100=3@YX7aP>^6jR>&0>?P0PAP@PCPAP@P2PDPEP@P2PEP@P2PEP@P2PEP@P2PDPEP@P2PEP@P2PDPEP@P2PEP@P2PDPDP0PGP@PIP1PFPAP@P2P1P5PAP@P4P1P5PAP@PJP=P@PQPVP1P5PAP=PXP1PFP5P=P]P1P5PAP=P4PRP`P4P2P3O4,1en200110800012010C10Dn200110F00012010810En200110F00012010A10BX0VPgC?P^PiPjPVPmPgP}PhG7PNPoPpPqPZPsPtPuPvPLM;5#6RsPDn0100000020100n200110F000121102103n200110@000121105107n200110?00012110@106PDn10110F00021110?00n0110>00031010?1010?01PDPDn0110=00031110>1010>00PDn0110<00031010=1110=00PDPDn0110;00031110<1010<00PDn0110:00031010;1110;00PDPDn0110900031110:1010:00PDPDn011080003111091010900PDPDn011000003111081010800PDn011010003001110010100PDn10110F00021110100=3@YX1>P=^45R>&0=?P0PAP@PCPAP@P2PDPEP@P2PEP@P2PEP@P2PEP@P2PDPEP@P2PEP@P2PDPEP@P2PEP@P2PDPDP0PGP@PIP1PFPAP@P2P1P5PAP@P4P1P5PAP@PJP=P@PKPMO1RZ=0wxP1P5PAP=PXP1PFP5P=P]P1P5PAP=P411e{n200110800012010C10DRen200110F00012010810En200110F00012010A10BX0VR]=<Vg70UPsPDn0100000020100n200110F000121102103n200110@000121105107n200110?00012110@106PDn10110F00021110?00n0110>00031010?1010?01PDPDn0110=00031110>1010>00PDn0110<00031010=1110=00PDPDn0110;00031110<1010<00PDn0110:00031010;1110;00PDPDn0110900031110:1010:00PDPDn011080003111091010900PDPDn011000003111081010800PDn011010003001110010100PDn10110F00021110100=3@YX1>P=^>5^<A^95^=5^;A^85R>&0<?P0PAP@PCPAP@P2PDPEP@P2PEP@P2PEP@P2PEP@P2PDPEP@P2PEP@P2PDPEP@P2PEP@P2PDPDP0PGP@PIP1PFPAP@P2P1P5PAP@P4P1P5PAP@PJP=P@11yURUPVP]P1P5PAP=PXQ05P4P2P\P9P:P7O6R]#9n200110F00012010A10BX0V=2VfRsC?P^PiPjPVPmPsP}PhG7PNPoPpPqP1P5PAP=PXP]n200110F00012010A10BX0V=2VfA@VsrPtPuPvPLM;5#6PDn0100000020100n200110F000121102103n200110@000121105107n200110?00012110@106PDn10110F00021110?00n0110>00031010?1010?01PDPDn0110=00031110>1010>00PDn0110<00031010=1110=00PDPDn0110;00031110<1010<00PDn0110:00031010;1110;00PDPDn0110900031110:1010:00PDPDn011080003111091010900PDPDn011000003111081010800PDn011010003001110010100PDn10110F00021110100=3@YX1>1CF5^55^15Rs&09?P0PAP@PCPAP@P2PDPEP@P2PEP@P2PEP@P2PEP@P2PDPEP@P2PEP@P2PDPEP@P2PEP@P2PDPDP0PGP@PIP1PFPAP@P2P1P5PAP@P4P1P5PAP@PJP=P@PUPVP1P5PAP=PXP1PFP5P=Q05P[P\O2Pen200110F00012010810En200110F00012010A10BX0VP|C?P^PiPjPVP1PFP5PjPnPWPlO2Q07n200110F00012010810EX0VX2jP|P}PhG7PNPoPpPqQ09Q0?PtPuPvPLM;5#6PDn0100000020100n200110F000121102103n200110@000121105107n200110?00012110@106PDn10110F00021110?00n0110>00031010?1010?01PDPDn0110=00031110>1010>00PDn0110<00031010=1110=00PDPDn0110;00031110<1010<00PDn0110:00031010;1110;00PDPDn0110900031110:1010:00PDPDn011080003111091010900PDPDn011000003111081010800PDn011010003001110010100PDn10110F00021110100=3@YX0s%UA^45Rs&08?P0PAP@PCPAP@P2PDPEP@P2PEP@P2PEP@P2PEP@P2PDPEP@P2PEP@P2PDPEP@P2PEP@P2PDPDP0PGP@PIP1PFPAP@P2P1P5PAP@P4P1P5PAP@PJP=P@P0PAP=PZPSPTn10110F00021010400P1P5PAP=PXP1PFP5P=Q0;Pen200110F00012010810En200110F00012010A10BX0V=<V|50yP^PiPjPVP1PFP5PjQ0=Q07n200110F00012010810EX0VX2jP|P}PhG7PNPoPpPqQ09Q0?PtPuPvPLM;5#6RyPDn0100000020100n200110F000121102103n200110@000121105107n200110?00012110@106PDn10110F00021110?00n0110>00031010?1010?01PDPDn0110=00031110>1010>00PDn0110<00031010=1110=00PDPDn0110;00031110<1010<00PDn0110:00031010;1110;00PDPDn0110900031110:1010:00PDPDn011080003111091010900PDPDn011000003111081010800PDn011010003001110010100PDn10110F00021110100=3@YX?sP>&07?P0PAP@PCPAP@P2PDPEP@P2PEP@P2PEP@P2PEP@P2PDPEP@P2PEP@P2PDPEP@P2PEP@P2PDPDP0PGP@PIP1PFPAP@P2P1P5PAP@P4P1P5PAP@PJP=P@Q0:PVP1P5PAP=PXP1PFP5P=Q0;P1P5PAP=P4PRP8P9PcPdP6PHO6=0z{n200110800012010C10Dn200110F00012010810En200110F00012010A10BX0VP|C?PyPDn0100000020100n200110F000121102103n200110@000121105107n200110?00012110@106PDn10110F00021110?00n0110>00031010?1010?01PDPDn0110=00031110>1010>00PDn0110<00031010=1110=00PDPDn0110;00031110<1010<00PDn0110:00031010;1110;00PDPDn0110900031110:1010:00PDPDn011080003111091010900PDPDn011000003111081010800PDn011010003001110010100PDn10110F00021110100=3@YX1>Pa^6jRaQ01P0PAP@PCPAP@P2PDPEP@P2PEP@P2PEP@P2PEP@P2PDPEP@P2PEP@P2PDPEP@P2PEP@P2PDPDP0PGP@PIP1PFPAP@P2P1P5PAP@P4P1P5PAP@PJP=P@Q0<P^PiPjPVP1PFP5PjQ0=P1P5PAPjP4fFP8P4P2P3O4n200110800012010C10Dn200110F00012010810EX0VX2jP|P}PhG7PNPoPpPqQ09Q0?PtPuPvPLM;5#6PDn0100000020100n200110F000121102103n200110@000121105107n200110?00012110@106PDn10110F00021110?00n0110>00031010?1010?01PDPDn0110=00031110>1010>00PDn0110<00031010=1110=00PDPDn0110;00031110<1010<00PDn0110:00031010;1110;00PDPDn0110900031110:1010:00PDPDn011080003111091010900PDPDn011000003111081010800PDn011010003001110010100PDn10110F00021110100=3@YX7aP0PAP@Q02,_2RaPAP@P2PDPEP@P2PEP@P2PEP@P2PEP@P2PDPEP@P2PEP@P2PDPEP@P2PEP@P2PDPDP0PGP@f9#RRYP1PFPAP@P2P1P5PAP@P4P1P5PAP@f>/>B#GRLP=P@%;KRv1>KBRu;\:%eKRt5D<1[vuPvP4P2P:Cf30P0PAP=1gvuPSPTn10110F00021010400P1P5PAP=PXP1PFP5P=AFk[\P1P5PAP=P4%;RRR/Eb,8_1ERc,8_'1PRP8P9PcPdP6PHFYPRPRP4P2P3DX30n200110800012010C10Dn200110F00012010810En200110F00012010A10BX0VP1P5PAP=PXPkP4P2P\P9P:P7FNRk#9n200110F00012010A10BX0V%OKRq52VRp5<V30%ZKQ03'JRo%MKRN#SQ047oBRBPjPVP1PFP5PjAF~WlQ0>n200110F00012010810EX0VX2jPpPvP4P2P:CH%kNRNG7POPMP9P2CW#9X3<=2<t%iKRO%hKRh%dKR}P1P5PAP=PXPkn200110F00012010A10BX0V=2Vq%^KRk9@Vp%`KRp%aKR|%bKRi%cKRKM;5#6PDn0100000020100n200110F000121102103n200110@000121105107n200110?00012110@106PDn10110F00021110?00n0110>00031010?1010?01PDPDn0110=00031110>1010>00PDn0110<00031010=1110=00PDPDn0110;00031110<1010<00PDn0110:00031010;1110;00PDPDn0110900031110:1010:00PDPDn011080003111091010900PDPDn011000003111081010800PDn011010003001110010100PDn10110F00021110100R^-03@Q00g06>8E4%=?RJ$02%~?E4&00J&01?E4%}J%|?E4&04J%{?E4&05J&06?E4%zJ&0:?E4&0;J%y?E4%xJ%w?E4%vJ&0??E4&0@J%u?E4P0PAP@PaPAP@P2PDPEP@P2PEP@P2PEP@P2PEP@P2PDPEP@P2PEP@P2PDPEP@P2PEP@P2PDPDP0PGP@PYP1PFPAP@P2P1P5PAP@P4P1P5PAP@PLP=P@%=vRv@0Au:=D<t1mvuPvP4P2P:Cj30P0PAP=1]vuPSPTn10110F00021010400P1P5PAP=PXP1PFP5P=Q06?B[\P1P5PAP=P4%=RR[/Ab,8_1A[c,8_'1P[P8P9PcPdP6PHFPP[PRP4P2P3DQ30n200110800012010C10Dn200110F00012010810En200110F00012010A10BX0VP1P5PAP=PXQ06P4P2P\P9P:P7FVR7#9n200110F00012010A10BX0V=2VqR\5<V30PoPBPjPVP1PFP5Pj%=~?BWlQ07n200110F00012010810EX0VX2jP\PvP4P2P:ClPNG7PPPMP9P2H0B#9X3<=2<tPOPhP}P1P5PAP=PXP7n200110F00012010A10BX0V=2VqA@V\kPpP|PiPKM;5#6PDn0100000020100n200110F000121102103n200110@000121105107n200110?00012110@106PDn10110F00021110?00n0110>00031010?1010?01PDPDn0110=00031110>1010>00PDn0110<00031010=1110=00PDPDn0110;00031110<1010<00PDn0110:00031010;1110;00PDPDn0110900031110:1010:00PDPDn011080003111091010900PDPDn011000003111081010800PDn011010003001110010100PDn10110F00021110100=3@^e%t2%s253@eX:;o"). Qed.


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
      | Some lo, Some hi => Z.ltb 0 lo && Z.leb (img_hi A) lo && Z.leb (hi + d + 4096) (MID_LO + 2^32)
      | _, _ => false
      end)%bool.

(* [comment removed for export] *)
Definition brk_grow_facts (k : list kentry) (ms : list amap) (bb : expr) (bk d : Z) : list kentry :=
  KDisj (SA bb bk) (ELit (d + 4096)) (SA e_sp0 STK_OFF) (ELit STK_LEN)
  :: pd_disj k bb bk (ELit (d + 4096)) ++                                   (* [comment removed for export] *)
  (if band_covered ms MID_LO KHI then [KDisj (SA bb bk) (ELit (d + 4096)) (SA (ELit MID_LO) 0) (ELit (KHI - MID_LO))] else [])
  ++ flat_map (fun m => if is_fog m then [] else [KDisj (SA (am_base m) 0) (am_len m) (SA bb bk) (ELit (d + 4096))]) ms.

Definition brk_grow_possible (cs : acs) (d : Z) : bool :=
  (brk_base_ok cs d && budget_ok cs d && no_holes (a_maps cs))%bool.   (* [comment removed for export] *)

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
        let k' := brk_grow_facts k (a_maps cs) bb bk d ++ kn_grant_filter k (a_maps cs) in   (* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition stack_side (k : list kentry) (b : expr) : bool :=
  match erange k (esub b (eaddz e_sp0 STK_OFF)) with
  | Some (lo, hi) => (Z.leb 0 lo && Z.leb hi TWO47)%bool
  | None => false
  end.
Definition stack_sideB (bc : bctx) (b : expr) : bool :=
  match erangeB bc (esub b (eaddz e_sp0 STK_OFF)) with
  | Some (lo, hi) => (Z.leb 0 lo && Z.leb hi TWO47)%bool
  | None => false
  end.
Lemma stack_sideB_eqf : forall fk, stack_sideB (mkbc fk) = stack_side fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bh11eh22fkh31oi002hii012loi021pi031xp;1p;2p;3p;6g00@cj1@Tg00aHR0j2?Tg00F=R1j14Tg041_j13j20Tg06?>j2>Tg05Tbj26Tg01KQj21Tg017?j25Tg001hj32Tg00GAj27Tg01\fj18Tg03o>j19Tg043]j1=Tg00>Fj6:Tg06@<j1;Tg06A@j1<Tg012G#@g00\8R2g00]5R3/?3R4#4]1R5f0R6#3g00NdR7^02R8P1P4P7f1R9g05J4g05K2'>,66R:O1P0P3P3P7P6g02B5/19g04eZ,16'5n2001102000120101100R3g00OdR0n10110300021010200X02P1P4P7f2/0:P3P0n10110300021010200X0232X35P1P4P7109:P3P0n10110300021010200X02,78%86R2#9%=6E:%;2%<6528eW2o"). Qed.

Definition node_unvis_ref (cs : acs) (b n : expr) : option acs :=
  let k := kn cs in
  let '(bb, bk) := split_lit b in
  let '(sb, sk, sn) := shadow_of k b n in
  match xhi k b, xhi k n with
  | Some bh, Some nh =>
      if (existsb (vis_here b n) (a_vis cs)
          && Z.leb 3 (ealign k b) && Z.leb 3 (ealign k n) && flat_x k bb bk n   (* [comment removed for export] *)
          && flat_x k sb sk sn && kzero_x k k sb sk sn)%bool
      then
        let k1 := if stack_side k b then k else kn_unfill k bb bk n in   (* [comment removed for export] *)
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
          && Z.leb 3 (ealignB bc b) && Z.leb 3 (ealignB bc n) && flat_xB bc bb bk n   (* [comment removed for export] *)
          && flat_xB bc sb sk sn && kzero_xB bc k sb sk sn)%bool
      then
        let k1 := if stack_sideB bc b then k else kn_unfillB bc bb bk n in   (* [comment removed for export] *)
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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bi001bh11pi011ph21nh31eh41kh51lh62b0h72csh81oh93offh:2ubh;2ukh<2unh=1zi022bbi032bhi042bki052nhi062sbi072ski082sni091xp&0p;1p;2p;3p;4p;5p;;p;6g00g[j15Tg03g_k102j2;Tg00F=R0j1^Tg01Bjj1QTg00aHR1j2YTg01\fj19Tg04Obj3`j1pTg03L`j2?j1uTg06BCj2Oj3DTg00iUj1FTg008Fj3ETg03h\j1fTg03T?j1dTg01KQj2:Tg03Yfj4@j1jTg03OXj5cj1nTg00eaj1UTg01^bj1RTg00f^j1ITg00@cj1rTg06@<j2aj1sTg02J7j4]j1lTg02TWR2j4>Tg01_]j1HTg01e[j41Tg00hVj1GTg051Wj1JTg052Wj1KTg04m=j1LTg01Knj1MTg01E0j3NTg00jSj1CTg00eAj1eTg00LGj3BTg051:j3STg04n=j1TTg00_Mj1\Tg00`Kj1[Tg053Uj1ZTg054Vl;2Tg00lQk101Tg04Pej3Xj1yTg03M]j2=j1xTg03Zfj4<k100Tg03PYj5Wj1zTg017?j28Tg06A@j2Vj1~Tg02K:R3j47j1}Tg001hj33Tg00GAj2_Tg00>Fj66Tg03NWj1qTg04]Xj1oTg069_j1mTg02SPj1kTg06CDj1tTg04\Tj1vTg03iAj1wj2bTg03jAj1iTg06DLj3hTg06EOj3gTg03d7j4{Tg00F_j2|Tf2R4f1R5f0R6':'8p=A1845/86p=4g00\8R7P7P5P6C{p=Pg014ER8/|6p=0g00]5R9^37R:%54R;$02%^8R<P1P7P9P<%Q4R=P11Y79R>P7P<f5R?#5R@#9f4RAf3RB3`RCP1P7P9P<P5P0P9P<f9RD#5RE#9RFf8RG'?RHP0P9P<f:RI#5RJ#9RK/?GRLg00NdRMP<1Y77RN1OIDf;RO#FRP3ERQg03U:#f#dRRPGPIO1RS3APGPDO1,:R%5ORT#9RUf7RVf6RWPDC@34PUPBP4PAC@PUPTPBP4PADcRX34%UORY#RRZ%IYR[PMg012G#rR\1aUIPTPUPVPWPDC]RUn0100000020000PBP4PAC>%HYRYC1%GOR]%JOR^%KOR_%LOR`ADOI6#MX1N=NNPRP%CO1PID%eNRa5BN5SNRb%TORc%\ORd%[ORe%ZORfM;2#0Rg&018Rhn0100000020000Phn10110900021010500Phn10110900021010300n2001101000120106107n2001109000120101108n2001109000120102104P1P7P9P<P=P1P>P7P<AX@ABR@P1P7P9P<P5P0P9P<1=EGRiP0P9P<1=JGRjPMP<1;TI,:R1;TD,:R54QRQPTPVPWPDC<PTPBP4PAC<34RkPTPTPBP4PADW'8RlPZP[PMP\1VTIRmPTPTPVPWPDC7Rnn0100000020000RoPBP4PAC7PYC1P]P^P_P`PPPbPcPdPePfM;2#0Phn0100000020000Phn10110900021010500Phn10110900021010300n2001101000120106107n2001109000120101108n2001109000120102104Rp33X=:PM^27^99^07R:&00;P1P7P9P<P=P1P>P7P<PCP1P7P9P<P5P0P9P<PHP0P9P<PLPMP<PGPVPWPDO3Rq,8QPGPBP4PAO3;4XPgPhn0100000020000Phn10110900021010500Phn10110900021010300n2001101000120106107n2001109000120101108n2001109000120102104=3<pX0:PM^07Rg%~;P1P7P9P<P=P1P>P7P<PCP1P7P9P<P5P0P9P<PHP0P9P<PLPMP<18kXRXPZP[PMP\PSPTPUn0100000020000PBP4PAC>PYC1P]P^P_P`PPPbPcPdPePfM;2#0Phn0100000020000Phn10110900021010500Phn10110900021010300n2001101000120106107n2001109000120101108n2001109000120102104=3<pX0gP\^<7^;9^:7Rg%};P1P7P9P<P=P1P>P7P<PCP1P7P9P<P5P0P9P<PHP0P9P<PLPMP<PXPZP[PMP\PmPTPqn0100000020000PBP4PAC>PYC1P]P^P_P`PPPbPcPdPePfM;2#0Phn0100000020000Phn10110900021010500Phn10110900021010300n2001101000120106107n2001109000120101108n2001109000120102104=3<pX5gP:^4\R:%z;P1P7P9P<P=P1P>P7P<PCP1P7P9P<P5P0P9P<PHP0P9P<PLPMP<PGPTPBP4PAO4,8kPZP[PoPBP4PAC>PYC1P]P^P_P`PPPbPcPdPePfM;2#0RkPhn0100000020000Phn10110900021010500Phn10110900021010300n2001101000120106107n2001109000120101108n2001109000120102104=3<pX0:1Y>7^27^07R:%y;P1P7P9P<P=P1P>P7P<P4PAPBO2P1P7P9P<P5P0P9P<PHP0P9P<PLPMP<PlPkPhn0100000020000RkPhn10110900021010500Phn10110900021010300n2001101000120106107n2001109000120101108n2001109000120102104=3<pX1:%^9^37R:%x;P1P7P9P<P=P1P>P7P<P@P1P7P9P<P5P0P9P<PWPGO1P0P9P<PVPGO1PkPhn10110900021010500Phn10110900021010300n2001101000120106107n2001109000120101108n2001109000120102104=3<pX8:Pg^4\RgP3P1P7P9P<P=P1P>P7P<P@P1P7P9P<P5P0P9P<PiP0P9P<PjPMP<PlPZP[PGPoPBP4PAO4PYC1P]P^P_P`PPPbPcPdPePfM;2#0Phn0100000020000Phn10110900021010500Phn10110900021010300n2001101000120106107n2001109000120101108n2001109000120102104=3<pX5g1V;5PMPMP1P7P9P<%QBP1P>P7P<%5W?X?AP1P7P9P<P5P0P9P<1=JDP0P9P<1=TDPMP<1OOIf<R?#FRg5EN%5?Rp/;O7AR1;pI,:RPpPVPWPIC<34PpPBP4PAC<PpPpPBP4PADW34%U?Ro#R%IoPMP\PGPpPpPVPWPIC7n0100000020000PBP4PAC7%HoC1%G?%J?%K?%L?AD?O6#MX1N=NNg%C?1POI=BNa5SN%T?%\?%[?%Z?M;2#0Phn0100000020000Phn10110900021010500Phn10110900021010300n2001101000120106107n2001109000120101108n2001109000120102104R?=3<?P6P1P7P9P<P=P1P>P7P<P@P1P7P9P<P5P0P9P<PiP0P9P<PjPMP<PlPZP[PTPBP4PAC7PYC1P]P^P_P`PPPbPcPdPePfM;2#0Phn0100000020000Phn10110900021010500Phn10110900021010300n2001101000120106107n2001109000120101108n2001109000120102104,_<P1P7P9P<P=P1P>P7P<P@P1P7P9P<P5P0P9P<PiP0P9P<PjPMP<PlPZP[PnPBP4PAC7PYC1P]P^P_P`PPPbPcPdPePfM;2#0Phn0100000020000Phn10110900021010500Phn10110900021010300n2001101000120106107n2001109000120101108n2001109000120102104,_<n0110001020000b6P2g06>8E6%9;R2#u%q;E6%p2%o;E6%n2%m;E6%l2%k;E6%s2%t;E6%j2%v;E6%w2%i;E6P1P7P9P<%Q5R;P1P>P7P<%5AR2#9?`B4P1P7P9P<P5P0P9P<%5GRf#9/?VP0P9P<1?FVPMP<1ODG%FIRF5ENRe1bKD7AR1bKG,:RPKPVPWPGC@34PKPBP4PAC@PKPJPBP4PADc34%UIRd#RRc%IdRbPMP\1aKDPJPKPVPWPGC]n0100000020000PBP4PAC>%HdRdC1%GIRK%JIRP%KIR`%LIR_ADID6#MX1N=NNFRF%CI1PDG=BNa5SNRN%TIRa%\IR^%[IR]%ZIRIM;2#0Phn0100000020000Phn10110900021010500Phn10110900021010300n2001101000120106107n2001109000120101108n2001109000120102104P1P7P9P<P;P1P>P7P<AX2B4P1P7P9P<P5P0P9P<1=fVP0P9P<1=EVPMP<1;JD9AeR1;JG,:RPJPVPWPGC<34PJPBP4PAC<PJPJPBP4PADW34PcPbPMP\1VJDPJPJPVPWPGC7n0100000020000PBP4PAC7PdC1PKPPP`P_PFPNPaP^P]PIM;2#0Phn0100000020000Phn10110900021010500Phn10110900021010300n2001101000120106107n2001109000120101108n200110900012010210453<eAh456Ag45653<eX27X07X78o"). Qed.


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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bi001bh11kh21oh34cmaxh42csh51ei011eh65entryh71lh81ni021nh93offh:2ubh;2ukh<2uni031ai041ci051di062dbi073dhii082dki093dsti0:1ii0;2k0i0<2loi0=2nei0>3nhii0?3nloi0@2opi0A3reti0B2sxi0C1xp;1p;2p;4p;5p;3p;6g00@cj1nTg00g[j12Tg03K\j1[j5BTg00F=R0j1DTg050?j1UTg03T]j2:Tg01Knj1=Tg00lQj1MTg06FVj1LTg003hj1>Tg05<Jj2GTg02>Bj2@Tg01Anj20Tg01Bjj1TTg01\fj16Tg03D[j2Qj1gTg03L`j2?j1cTg01KQj2PTg03SZj19Tg03T?j1ETg03h\j1\Tg058bj2ZTg017?j21Tg01K4j2YTg00F_j24Tg06GVj45Tg03<jj2CTg03OXj5Jj1dTg03U_j4Kj1aTg06HYj3ITg00n;j2XTg01LLj2HTg01TPj3NTg02iMR1j4OTg00LGj3;Tg03FYj2Fj1jTg03M]j2Aj1kTg03PYj5Sj1mTg03Vdj4Wj1lTg02fAR2j4VTg001hj33Tg00GAj2hTg00>Fj67Tg03HQj1fTg03NWj1bTg06IZj1`Tg069_j1eTg03JWj1_j5RTg06Jcj1^Tg06Klj3]Tg06M1j3iTf0R3#>#>p=8%93#9p=<g014ER4g00]5R5g012GR6#nR7g00\8R8g00NdR9^88^95]0R:]1R;f2R<#2R=#[%D4R>P9P>f3R?#U/:<#=R@%M4R4P0P5P>%L?RAP0P5P>f4RBg01YJ#8#8#8#8#8RC#>RD'GREP9P>1@3?#=RFP4g00aHRGP8P5P>f5RH/0C#TRIP0P5P>f7RJ#2RK#6RL%>DRM,0JRN'QROP0P5P>f8RP#2RQ#6RR10PMRS'?RTP0P5P>f9RU#2RV#6RW10UCRX'?RYP9P>g02B5RZ/P<f1R[g03U:#9R\#E%\\#9#<#E'Z'P'11Y3[g02BSR]'@'1R^P9P>1:[ZR_f:R`f6Ra10`CRb,48Rc%2`RdC5ReP9P>%9\#<#<#<#ER\,CH/:ZRf%6dRgPdPBP?10`MRhDJ'1PJPdPBP?PhO4Ri'1PeP0P7P>P9%D7RjPgPBP?PhCK147dRkP8PjPbP8Pjf;Rb/0MRlf<#21C[]R];I3,47%M7RmPmPmPmPmPmPmn0110=000810102101023010@1031003010@1031003010@1031003010@1031004010B10<1021014010B10;10:102PmPmPmPmPmPmPmn01109000810105101023010@1031003010@1031003010@1031003010@1031004010B10<1021014010B10;10:102Rnn0100000020000RoP9P>PP%2bRpPHPBPlO4PbPJ10bC,48RqP9P71@Z?RrP9P61Ca\R\/:ZRZ1XHBRs/HlANsl\n0100000020000RtP3PHPBPlCORu5;6Pun0100000020000C5RuP4n0100000020000P4n10110C00021010;00n0100000020001n0100000020001P4n0100000020100P4n10110C00021110700P4n10110C00021110>00P4n10110C00021110?00n200110C000121106108n0100000020001P4n10110C00021110400P4n10110C00021110A00n0100000020001P9P>P@P4P0P5P>PAP0P5P>PEP9P>PFP4PGP8P5P>PIP0P5P>1FKNRvP0P5P>1AQSRwP0P5P>1AVXRxP9P>P^P9P>P_PeP9P>PdPdPBP?PhDS,1fPdPdPBP?PhDBRy'1RzPeP0P7P>P9PjPdPBP?PhCWPkPnn0100000020000R{P9P>PpPpPHPBPlDBR|PbPJPqP9P7PrP3PHPBPlCVR}9;6tP}n0100000020000C5P4n0100000020000P4n10110C00021010;00n0100000020001n0100000020001P4n0100000020100P4n10110C00021110700P4n10110C00021110>00P4n10110C00021110?00n200110C000121106108n0100000020001P4n10110C00021110400P4n10110C00021110A00n0100000020001R}33X0;P;%m=P9P>P@P4P0P5P>PAP0P5P>PEP9P>PFP4PGP8P5P>PIP0P5P>POP0P5P>PTP0P5P>PYP9P>P^P9P>P_PeP9P>11fi/1yPeP0P7P>PoP9P>P|PuP4n0100000020000RuP4n10110C00021010;00n0100000020001n0100000020001P4n0100000020100P4n10110C00021110700P4n10110C00021110>00P4n10110C00021110?00n200110C000121106108n0100000020001P4n10110C00021110400P4n10110C00021110A00n0100000020001=3>}X0;P:%l=P9P>P@P4P0P5P>PAP0P5P>PEP9P>PFP4PGP8P5P>PIP0P5P>POP0P5P>PTP0P5P>PYP9P>P^P9P>P_PeP9P>PzPeP0P7P>P9PjPJPBP?PhO3PkPnn0100000020000PuP4n10110C00021010;00n0100000020001n0100000020001P4n0100000020100P4n10110C00021110700P4n10110C00021110>00P4n10110C00021110?00n200110C000121106108n0100000020001P4n10110C00021110400P4n10110C00021110A00n0100000020001=3>}X0:%D5^58R:%k=P9P>P@P4P0P5P>PAP0P5P>PEP9P>PFP4PGP8P5P>PIP0P5P>POP0P5P>PHPSO1P0P5P>PaPXO1P9P>P^P9P>P_PeP9P>PzPeP0P7P>P{PuP4n10110C00021010;00n0100000020001n0100000020001P4n0100000020100RuP4n10110C00021110700P4n10110C00021110>00P4n10110C00021110?00n200110C000121106108n0100000020001P4n10110C00021110400P4n10110C00021110A00n0100000020001=3>}X2:P:%j=P9P>P@P4P0P5P>PAP0P5P>PEP9P>PFP4PGP8P5P>PIP0P5P>PBPNO1P0P5P>PwP0P5P>PxPuP4n10110C00021110700P4n10110C00021110>00P4n10110C00021110?00n200110C000121106108n0100000020001P4n10110C00021110400P4n10110C00021110A00n0100000020001=3>}X2:P7^<8^;5^:8^17R:P2P9P>P@P4P0P5P>PAP0P5P>PEP9P>PFP4PGP8P5P>PIP0P5P>PvP0P5P>PwP0P5P>PxP9P>P^P9P>P_PeP9P>PzPeP0P7P>P{P9P>P|PbPJPqP9P7PrPPP3PHPBPlO4Rl9;6tPln0100000020000C5P4n0100000020000P4n10110C00021010;00n0100000020001n0100000020001P4n0100000020100P4n10110C00021110700P4n10110C00021110>00P4n10110C00021110?00n200110C000121106108n0100000020001P4n10110C00021110400P4n10110C00021110A00n0100000020001=3>}X7:P9P>%U</:[#=R:P4P0P5P>%L<R}P0P5P>1G?DRDP9P>1@3<#=RlP4PGP8P5P>10BC#TRtP0P5P>%2aRq10aMRb'FP0P5P>1AKNP0P5P>10PCRP,AQP9P>P^P9P>P_PUPa148XPVC5RaP9P>PVPVPBP?10UMRUDS,1fPVPVPBP?PUDB'1PaP0P7P>P9PjPVPBP?PUCW147VRMP8PjPXP8PjPhAIp]3,47PmPmPmPmPmPmPmn0110=000810102101023010@1031003010@1031003010@1031003010@1031004010B10<1021014010B10;10:102PmPmPmPmPmPmPmn01109000810105101023010@1031003010@1031003010@1031003010@1031004010B10<1021014010B10;10:102Rmn0100000020000P9P>PdPdPHPBPhDBP`PJPcP9P7PrP9P6PZ1HshANsh\n0100000020000RsP3PHPBPhCVR\5;6P\n0100000020000C5P4n0100000020000P4n10110C00021010;00n0100000020001n0100000020001P4n0100000020100P4n10110C00021110700P4n10110C00021110>00P4n10110C00021110?00n200110C000121106108n0100000020001P4n10110C00021110400P4n10110C00021110A00n0100000020001R\,h>P1g06N:E7%6=R1#g%f=E7%c1%b=E7%a1%`=E7%d1%e=E7%_1%^=E7P9P>P:P4P0P5P>P}P0P5P>PDP9P>PlP4PGP8P5P>PtP0P5P>%6q/QbP0P5P>1?LNP0P5P>1?RPP9P>P^P9P>P_PaP9P>PWPVPBP?PUDJ,1fPWPVPBP?PUDR'1PaP0P7P>P9PjPWPBP?PUCKPMPmn0100000020000P9P>PgPdPHPBPhDRP`PJPcP9P7PrP3PHPBPhCORh9;6sPhn0100000020000C5P4n0100000020000P4n10110C00021010;00n0100000020001n0100000020001P4n0100000020100P4n10110C00021110700P4n10110C00021110>00P4n10110C00021110?00n200110C000121106108n0100000020001P4n10110C00021110400P4n10110C00021110A00n0100000020001=3>\eA]<[3Ai<[353>eX35W6W4o"). Qed.


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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h04fuelh11oh21bh31nh43offh51xi001xh62x0h72x1h82x2h92x3h:2IHh;3acch<2dbh=2dkh>1fh?2fkh@5hintsi015hintshA1li021lhB2rbhC2rkhD2sbhE2skhF2sxi032bsi041ei054resti061si073scsi081vp;1p;2p;3p;4p;5p;6p;7p;8g00@cR0j19Tg00F=R1j1DTg01\fj11Tg06O?j2Aj3Pj4Lj5Hj6Kj7ZTg06PCj2<j3Nj4Jj5Fj6Rj76Tg001hj34Tg00GAj2QTg02A3j58Tg003hj10Tg03SZj1CTg03T?j1OTg01KQj2?Tg03@Uj3Xj1^Tg04D?j4Wj1\Tg017?j27Tg00F_j23Tg06QFj1VTg00PDj1UTg00lQj1ITg01K4j22Tg02=ej2:Tg00n;j2;Tg01HVj3@Tg00LGj3=Tg00eAj1BTg03=Jj8Tj2`Tg03AVj3Gj1bTg04EDj4Ej2STg03;hj8Mj2aTg03>Oj2_Tg00>Fj6>Tg06RKj1]Tg06SPj1[Tg04GLj4YTg00]5R2f3R3f2R4f1R5f0R6D8p=5g012GR7#9R8g005LR9g00\8R:%D8R;^32R<^=2R=^<:R>^E2R?]DR@%14RA/A61<6434RBX09P:P?%15g01YJRC'A1<C5P>APAC6ANC46P:P=%13RAPCP5P6CLPCP3P5P6CJP<f4RD#1REPCP4P5P6DHPCPDP4P5P6DFP;f5RF#1RGPCP3P4P5P6EKPCPFP3P4P5P6ERPCf6RHPDP3P4P5P6F6,Q;X92C5X82C5X7:D8X62C5X5:D8P:P?%05R?,AA1<?3P>%04R>=PE6AN>D6P:P=PG%03RGP5P6CLPGPFP5P6CJP<%1H%0DR<P4P5P6DHP<PHP4P5P6DFP;f7R<#1%0FRGP3P4P5P6EKPGP<P3P4P5P6ERP@f8RG,<Hg00NdR=P;g03U:R>#C#C#C#ORE/?5R?P1P:P=f9RA#1RI?XFDRJg00ODRKP1%92RLP=PI%0CRC#0#0#0#0#0#0#0RMPFPDCWRNPKg00OdROn10110000021010200n10110000021010400'7P1P:P;P1P:%D:RPPJ13:6RQP1PLPPPN%V6#U,3:RN%I:RRn10110000021010300n10110000021010800P1P8P;P5PH12FERSPD123ERT1:4ERUO51;FD?@M5==76,38RV%I8RWn10110000021010500PWn10110000021010800P=P;%O>R>/?5RXg03?XRYP;p,4segsRZPIPFPDPCPO%B=RIg026PR[#BR\GTR]P0P[P;P5P1P8P;P3PG12<>R^PH12F>R_1:D>R`O51;<H?@C3==76,38RaPWn10110000021010500PWn10110700020020106102PWPWn011000003301081071012010710100%B7,38Rbn0100000020000n0100000020000P=P;P1P:P=AGAFDRcPKP1PLP=PMPAPFPDCERdPKPOn10110000021010200Ren10110000021010400,7?RfP1P:P;P1P:PPPcPQP1PLPPPdPNPRn10110000021010300Rdn10110000021010800P1P8P;PGf:RcPHPSPDPTPUF6PVPWn10110000021010500RVPWn10110000021010800RUP=P;PXPYP;PZPAPFPDPCPOPIP\GMP0P[P;P5P1P8P;Pcf<PGP^PHP_P`F6PaPWn10110000021010500PWn10110700020020106102RaPWPWn011000003301081071012010710100Pbn0100000020000n0100000020000R`54;X1@%DL^42^2:^09R@1S6AX09P=P;P1P:P=PJPKP1PLP=P6PMPFPDO3R_PKPOn10110000021010200n10110000021010400,7?P1P:P;P1P:PPPJPQP1PLPPP_PNPRn10110000021010300n10110000021010800PVPWn10110000021010800P=P;PXPYP;P]PaPWPWn011000003301081071012010710100Pbn0100000020000R]n0100000020000=4;`X1@PP^42^2:R@%bGP=P;P1P:P=P6PFPDO2R_PKPen10110000021010400,7?P1P:P;P1P:PPP_PQPdn10110000021010800PVPWn10110000021010800P]n0100000020000=4;`X1@%9=%9[PY];]@^F=^39^C2^B:R@1aZGP=P;PfPUP=P;PXPYP;P6PFPDPCPOPIP\O6PaPWPWn011000003301081071012010710100Pbn0100000020000n0100000020000=4;`XA@P=P;1?E6P1P:P=AGGD3R@PKP1PLP=PMPGPDP3CER`PKPOn10110000021010200n10110000021010400'7P1P:P;P1P:PPP@PQP1PLPPP`PNPRn10110000021010300n10110000021010800P1P8P;P<PAPF12DEP3124E1:5EF61;D3?@M5==76,38PWn10110000021010500PWn10110000021010800P=P;1?>6PYP;PZPGPDP3PCPOPIP\GMP0P[P;P5P1P8P;PAf;P<12H>PF12D>1:3>F61;HF?@C3==76,38PWn10110000021010500PWn10110700020020106102PWPWn011000003301081071012010710100Pbn0100000020000n0100000020000,Q;%1GRb,`Z1_GZE>%^b%]GE>%\b%[GE>1AbHPFE>Pb%0HRHPDP3P4P5P6FZPHPGPDP3P4P5P6F654;eX92C5X82C5X7:D8X62C5X5:D8X:BX>9P6CYW0W?o"). Qed.
Lemma copy_factsB_eqf : forall fk, copy_factsB (mkbc fk) = (fun fuel => copy_facts fuel fk).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h04fuelh12dbh22dkh32fkh41nh52sbh62skp;1p;2p;5g00@cj16Tg00F=j15Tg01\fj10Tg06O?j11Tg06PCj24Tg06TYj22Tg02A3j53Tg012G#6R0g005LR1g00\8R2g00]5R3%50^43^23^12]6]5f0R2#0#1f1R3,42X011232X01D3W3o"). Qed.
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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bi001bh11ii011ih21oh34fuelh41kh51ni021nh62b1h72b2h82csh92dbi032dbh:2dki042dkh;1ei051eh<5entryh=2k1h>2k2i062k2h?1lh@2n1hA2n2hB3offhC2sbi072sbhD2ski082skhE2ubhF2ukhG2uni091ai0:1di0;3dhii0<3dsti0=2k0i0>2kci0?2loi0@2nei0A3nhii0B3nloi0C2opi0D3reti0E3shii0F2sxi0G1xi0H1zp%0p&0p;1p;2p;4p;3p;5p;7p;6g00@ck10@Tg00F=R0j1\Tg00g[j14Tg06PCj2nj7cTg050?j1kTg03T]j2<Tg01Knj1eTg00lQj1aTg06FVj1`Tg01Anj21Tg01Bjj1UTg003hj1TTg01\fj16Tg03D[j2jj1yTg03L`j2Kj1wTg01KQj2JTg03SZj1FTg03T?j1PTg03h\k10=Tg058bk20<Tg017?j20Tg01K4j2MTg02>Bj2@Tg06GVj45Tg03U_j4ij1tTg00F_j2NTg03<jj2VTg06HYj3bTg03JWj5>k100Tg02>_j7_j1uTg03OXj5^j1|Tg00n;j2ATg01LLj2]Tg02iMS00j48Tg03Yfj4Dj1rTg06Ubj1XTg01JTk10?Tg06VBk20>Tg04k<j1RTg06V_j2:Tg00RHj1QTg01HVj3BTg04\7j2[Tg06W6j2ZTg06WRj6HTg01UOj2ITg03FYj2gj1~Tg03M]j2Gk102Tg03Vdj4fk104Tg03K\j5=k10:Tg02<`j7dk103Tg03PYj5hk109Tg02fAS01j49Tg03Zfj4Ck10;Tg001hj37Tg00GAj2}Tg00>Fj6;Tg03HQj1xTg03NWj1vTg02?gj1zTg06IZj1{Tg069_j1sTg06Jck101Tg04\Tj1qTg06O?k105k706Tg06XWj1pTg06Y_k207Tg06Zdj2oTg00LGk308Tg051:j3YTg006Pj4mTg06[mj5lTf0R1#T#Tp=O%F1#Fp=Lf2R2f1R3'0/01p=Wg00\8R4/N1p=?g012GR5@0831p=2AY531p=Sg005LR6P5P3P1Cmp=Ef6R7f5R8f4R9f3R:AY5235Y5P1Dlp=3g014ER;g00]5R<&0@5R5#\R=^5<^:<^94^D<^C4^36R>%42,n1X36%\;R?g00NdR@P?%k2/<3#eRA%a;R;P0P<P?%`2RBg00aHRCP4P<P?g01YJRD#O#O#O#ORE#ORF,1:#URGPCP4P<P?%TFRH,18#URIP0P<P?f7RJ#4S02#6S03%THRK,1JRL'jRMP0P<P?f8RN#4RO#6S0411NKS05'KRPP0P<P?f9RQ#4RR#6S0611QFS07'KRSP0P<P?f:RT#4RU#6S0811THS09'KRVP@P?g02B5RW/J:g03U:#FRX#P&0=X#F#L#P+0<,J2'01M32g02BSRY'@1M12/@Y3WRZP@P?1<2WR[f;R\PN11\FR]#?S0:%4\R^C5R_P0P5P?P@P=%6^S0;PJP711\KR`Ci1N5^S0<P4P=P]P4P=f<R]/1KRaf=Rb#4Rc1V3YS0=;b1,N5%a5RYPYPYPYPYPYPYn0110@000810102101023010C1091003010C1091003010C1091003010C1091004010F10?1021054010F10=101102PYPYPYPYPYPYPYn0110<00081010:101023010C1091003010C1091003010C1091003010C1091004010F10?1021054010F10=101102S0>n0100000020000S0?P@P?%4]Rd#6RePdPNPJPaD>PePNPJPaP7P8PaF_Rf'0RgP@P?1@W9RhPePdP7P8PaD^'0S0@P]PQ11]F#?S0A1ANJS0B/]aRiP1PNPJPaC8'2C5RjP4P?PaP@P?%LXRX#F#L#LRk#F#L#P,J9Rl%6cRmPJP711bKRnCDRo'0P0P5P?P\%X9S0CPJP7PQPNP9O6f>RpP\11pF#?S0DP2PTPQ11pKRqC8,S1C5S0EP@P?PmPcPJP7PnD>S0F/0oPbPT11bF#?S0G%PXRX&0?1+0>Ro,MQ,ATS0H%Rpg06]1Rm':/:1#Q7BEX16P@P61<891V9X/<W'0%PkRk,J9;Wh1[9X#XPDn0100000020000Rr,ZDS0I'ES0JPcPJP7PQPNP8EHS0KP@P51@W8S0L1AQNS0M/InRsP3PQPNPnC8Rt'2Ptn0100000020000PrF3S0NP;n0100000020100Rtn10110G00021010>01Ptn0100000020101PtP@P?f?Rt#4Ru#6S0OPuPQPN11tKRvD>S0PQ0OPQPNPvCD'0PtP]11tF#?S0Q1M\o,A]S0Rf@Rw#R/:m/:1#QS0S7BEX16P@P61<J71V7X/<W'01J7k1@W73W1[7X#XPDn0100000020000Rx,ZDS0T'ES0UPuPQPNP\PTPJEHS0VP@P51@WJRy1A\TS0W/IvRzP:P\PTPvC8R{'2P{n0100000020000PxF3S0XP;n0100000020100R{P{P{P{P@P?%4wR{#6R|P{PTPQ11wKR}D>S0YP|PTPQP}CD'0PwPb11wF#?S0Z1M]o,AbS0[fA#R/:m/:1#Q7BEX16P@P61<NJ1VJX/<W'01JJk;Wy1[JX#XPDn0100000020000RX,ZDS0\'ES0]P{PTPQP]P\PNEHS0^P@P51@WNS0_1A]\S0`/I}RWP9P]P\P}C8RD'2PDn0100000020000PXF3S0aP;n0100000020100RDPDn0110@00081110H111023110C1091003110C1091003110C1091003110C1091004110F10?1021054110F106101102n0100000020001P;n0100000020100P;n10110G00021110=00n0100000020001P;n0100000020100P;n10110G00021110E00P;n10110G00021110;00P;n10110G00021110A00P;n10110G00021110B00n200110G000121107108n200110G000121103104P;n10110G00021110D00n0100000020001P@P?PAP;P0P<P?PBPCP4P<P?PGPCP4P<P?PIP0P<P?Q02/gLS0bP0P<P?Q05,GOS0cP0P<P?Q07,GRS0dP0P<P?Q09,GUS0eP@P?PZP@P?P[P_P0P5P?P@P=P^PJP7P`CfQ0<Q0>n0100000020000S0fP@P?PdPdPNPJPaD=RDPdPNPJPaP7P8PaFd'0S0gP@P?PdPdP7P8PaDh,0hS0hP]PQQ0AP1PNPJPaC9,2iC5P4P?PaP@P?PcPJP7PnCCRk,0lS0iP0P5P?Q0CPcPJP7PQPNP9FcRoPpP\Q0DP2PTPQPqC9,S1C5P@P?PcPcPJP7PnD=/0kS0jPbPTQ0GQ0JQ0KP@P5Q0LP3PQPNPnC9R|,2sP|n0100000020000PrF3P;n0100000020100R|n10110G00021010>01P|n0100000020101P|P@P?PuPuPQPNPvD=PuPQPNPvCCS0k'0S0lPtP]Q0QQ0UQ0VP@P5PyP:P\PTPvC9R|,2zP|n0100000020000PxF3P;n0100000020100R|P|P|P|P@P?P{P{PTPQP}D=P{PTPQP}CCS0m'0S0nPwPbQ0ZQ0]Q0^P@P5Q0_P9P]P\P}C9R|,2WP|n0100000020000PXF3P;n0100000020100R|P|n0110@00081110H111023110C1091003110C1091003110C1091003110C1091004110F10?1021054110F106101102n0100000020001P;n0100000020100P;n10110G00021110=00n0100000020001P;n0100000020100P;n10110G00021110E00P;n10110G00021110;00P;n10110G00021110A00P;n10110G00021110B00n200110G000121107108n200110G000121103104P;n10110G00021110D00n0100000020001R|37X2>P@^54^B<^04R>%43R~$0;P@P?PAP;P0P<P?PBPCP4P<P?PGPCP4P<P?PIP0P<P?PMP0P<P?PPP0P<P?PSP0P<P?PVP@P?PZP@P?P[P_P0P5P?Q0?P@P?PgP@P?Q0@PjP4P?PaP@P?P\PJP7PnO3Rg,0lP0P5P?PoQ0EP@P?Q0F/0gQ0NP;n0100000020100Rgn10110G00021010>01Pgn0100000020101PgP@P?Q0PPbPQPNPvO3'0Q0XP;n0100000020100RgPgPgPgP@P?Q0YPpPTPQP}O3'0Q0aP;n0100000020100RgPgn0110@00081110H111023110C1091003110C1091003110C1091003110C1091004110F10?1021054110F106101102n0100000020001P;n0100000020100P;n10110G00021110=00n0100000020001P;n0100000020100P;n10110G00021110E00P;n10110G00021110;00P;n10110G00021110A00P;n10110G00021110B00n200110G000121107108n200110G000121103104P;n10110G00021110D00n0100000020001=7?|X0>P>^45Rg&0:~P@P?PAP;P0P<P?PBPCP4P<P?PGPCP4P<P?PIP0P<P?PMP0P<P?PPP0P<P?PSP0P<P?PVP@P?PZP@P?P[P_P0P5P?Q0?P@P?PTPdPNPJPaO4/0fP@P?Q0@PjP4P?PaP@P?Q0iP0P5P?PoQ0EP@P?P\PcPJP7PnO4/0kQ0NP;n0100000020100Rkn10110G00021010>01Pkn0100000020101PkP@P?PbPuPQPNPvO4Q0k'0Q0XP;n0100000020100RkPkPkPkP@P?PpP{PTPQP}O4Q0m'0Q0aP;n0100000020100R{P{n0110@00081110H111023110C1091003110C1091003110C1091003110C1091004110F10?1021054110F106101102n0100000020001P;n0100000020100P;n10110G00021110=00n0100000020001P;n0100000020100P;n10110G00021110E00P;n10110G00021110;00P;n10110G00021110A00P;n10110G00021110B00n200110G000121107108n200110G000121103104P;n10110G00021110D00n0100000020001=7?|X0gPg&09~P@P?PAP;P0P<P?PBPCP4P<P?PGPCP4P<P?PIP0P<P?PMP0P<P?PPP0P<P?PSP0P<P?PVP@P?PZP@P?P[P_P0P5P?Q0?P@P?10DfRfP@P?PTPdP7P8PaO4,0hPjP4P?PaP@P?Q0iP0P5P?PoQ0EP@P?Q0jQ0NP;n0100000020100R{n10110G00021010>01P{n0100000020101P{P@P?Q0lQ0XP;n0100000020100R{P{P{P{P@P?Q0nQ0aP;n0100000020100R{P{n0110@00081110H111023110C1091003110C1091003110C1091003110C1091004110F10?1021054110F106101102R{n0100000020001P;n0100000020100P;n10110G00021110=00n0100000020001P;n0100000020100P;n10110G00021110E00P;n10110G00021110;00P;n10110G00021110A00P;n10110G00021110B00n200110G000121107108n200110G000121103104P;n10110G00021110D00n0100000020001=7?|X0gP>&04~P@P?PAP;P0P<P?PBPCP4P<P?PGPCP4P<P?PIP0P<P?PMP0P<P?PPP0P<P?PSP0P<P?PVP@P?PZP@P?P[P_P0P5P?P@P=PQPJP7P`O3Q0<Q0>n0100000020000P@P?PfP@P?Q0hPjP{n0100000020001R{P;n0100000020100P;n10110G00021110=00n0100000020001P;n0100000020100P;n10110G00021110E00P;n10110G00021110;00P;n10110G00021110A00P;n10110G00021110B00n200110G000121107108n200110G000121103104P;n10110G00021110D00n0100000020001=7?|X0>P@^A4^><^74^@4^=<^64R>&03~P@P?PAP;P0P<P?PBPCP4P<P?PGPCP4P<P?PIP0P<P?PMP0P<P?PPP0P<P?PSP0P<P?PVP@P?PZP@P?P[P_P0P5P?Q0fP@P?PTPNPJPaP7P8PaO6,0DP{P;n0100000020100P;n10110G00021110=00n0100000020001P;n0100000020100P;n10110G00021110E00P;n10110G00021110;00P;n10110G00021110A00P;n10110G00021110B00n200110G000121107108n200110G000121103104P;n10110G00021110D00n0100000020001=7?|X0>%\<^;4R>&02~P@P?PAP;P0P<P?PBPCP4P<P?PGPCP4P<P?PIP0P<P?PMP0P<P?P7Q05O1P0P<P?PJQ07O1P0P<P?PNQ09O1P@P?PZP@P?P[P_P0P5P?Q0fP@P?Q0gP{P;n0100000020100P;n10110G00021110=00n0100000020001P;n0100000020100R{P;n10110G00021110E00P;n10110G00021110;00P;n10110G00021110A00P;n10110G00021110B00n200110G000121107108n200110G000121103104P;n10110G00021110D00n0100000020001=7?|X2>P>%~~P@P?PAP;P0P<P?PBPCP4P<P?PGPCP4P<P?PIP0P<P?P8PLO1P0P<P?Q0cP0P<P?Q0dP0P<P?Q0eP{P;n10110G00021110E00P;n10110G00021110;00P;n10110G00021110A00P;n10110G00021110B00n200110G000121107108n200110G000121103104P;n10110G00021110D00n0100000020001=7?|X2>P5^G4^F<^E4^45R>Q01P@P?PAP;P0P<P?PBPCP4P<P?PGPCP4P<P?PIP0P<P?Q0bP0P<P?Q0cP0P<P?Q0dP0P<P?Q0eP@P?PZP@P?P[P_P0P5P?Q0fP@P?Q0gP@P?Q0hP]PQQ0APTP1PNPJPaO4,2iC5P4P?PaP@P?Q0iP0P5P?PoPpP\Q0DP]P2PTPQPqO4,S1C5P@P?Q0jPbPTQ0GQ0JQ0KP@P5Q0LP\P3PQPNPnO4Ro,2sPon0100000020000PrF3P;n0100000020100Ron10110G00021010>01Pon0100000020101PoP@P?Q0lPtP]Q0QQ0UQ0VP@P5PyPbP:P\PTPvO4Ro,2zPon0100000020000PxF3P;n0100000020100RoPoPoPoP@P?Q0nPwPbQ0ZQ0]Q0^P@P5Q0_PpP9P]P\P}O4R},2WP}n0100000020000PXF3P;n0100000020100R}P}n0110@00081110H111023110C1091003110C1091003110C1091003110C1091004110F10?1021054110F106101102n0100000020001P;n0100000020100P;n10110G00021110=00n0100000020001P;n0100000020100P;n10110G00021110E00P;n10110G00021110;00P;n10110G00021110A00P;n10110G00021110B00n200110G000121107108n200110G000121103104P;n10110G00021110D00n0100000020001=7?|X?>P@P?%k3/<1#eR>P;P0P<P?%`3R|PCP4P<P?112F#UR}PCP4P<P?119H#URWP0P<P?%47Rw117KRo'gP0P<P?Q02/GLP0P<P?11NFRz,GOP0P<P?11QHRH,GRP@P?PZP@P?P[PTPN11TFRF#?PUC5RRP0P5P?P@P=PUPJP711TKRKCf1N5URUP4P=PFP4P=P`Q0==bd1,N5PYPYPYPYPYPYPYn0110@000810102101023010C1091003010C1091003010C1091003010C1091004010F10?1021054010F10=101102PYPYPYPYPYPYPYn0110<00081010:101023010C1091003010C1091003010C1091003010C1091004010F10?1021054010F10=101102RYn0100000020000P@P?P^P^PNPJP`D=P^PNPJP`P7P8P`Fd'0P@P?P^P^P7P8P`Dh,0hP\PQQ0:Q0B/]`RFP1PNPJP`C9'2C5P4P?P`P@P?PdPJP7PaCCRO,0lP0P5P?Q0CPdPJP7PQPNP9FcPbP\Q0GP2PTPQPnC9,S1C5P@P?PdPdPJP7PaD=/0OP]PTQ0AQ0H%Rb/:m/:1#Q7BEX16Q0I'EROPdPJP7PQPNP8EHRsP@P5Q0LQ0M/IaRiP3PQPNPaC9R_'2P_n0100000020000PrF3P;n0100000020100R_n10110G00021010>01P_n0100000020101P_P@P?%4pR_P_PQPNPqD=P_PQPNPqCC'0PpP]Q0DQ0R%Rt/:m/:1#Q7BEX16Q0T'ERmP_PQPNP\PTPJEHRIP@P5PyQ0W/IqRGP:P\PTPqC9RB'2PBn0100000020000PxF3P;n0100000020100RBPBPBPBP@P?PuPuPTPQPvD=PuPTPQPvCC'0PtPbQ0QQ0[Q0S7BEX16Q0\'ER6PuPTPQP]P\PNEHREP@P5Q0_Q0`/IvRBP9P]P\PvC9RA'2PAn0100000020000PXF3P;n0100000020100RAPAn0110@00081110H111023110C1091003110C1091003110C1091003110C1091004110F10?1021054110F106101102n0100000020001P;n0100000020100P;n10110G00021110=00n0100000020001P;n0100000020100P;n10110G00021110E00P;n10110G00021110;00P;n10110G00021110A00P;n10110G00021110B00n200110G000121107108n200110G000121103104P;n10110G00021110D00n0100000020001RA,}?Q00g06N:E;%6~R{#y%x~E;%w{%v~E;%u{%z~E;%t{%{~E;%|{%s~E;&00{&01~E;%r{%q~E;&05{%p~E;P@P?P>P;P0P<P?P|PCP4P<P?P}PCP4P<P?PWP0P<P?%6w/joP0P<P?Q03/KLP0P<P?Q04/KzP0P<P?Q06/KHP@P?PZP@P?P[PRP0P5P?P@P=Q08PJP7PKCiPUPYn0100000020000P@P?Q0;P^PNPJP`D>Q0;PNPJP`P7P8P`F_'0P@P?Q0;P^P7P8P`D^,0hP\PQQ0:P1PNPJP`C8,2FC5P4P?P`P@P?PePJP7PaCDR`,0lP0P5P?PeQ0CPJP7PQPNP9K06PbP\Q0GP2PTPQPnC8,S1C5P@P?PePdPJP7PaD>/0`P]PTQ0APOPsP@P5Q0LP3PQPNPaC8Ra,2iPan0100000020000PrF3P;n0100000020100Rrn10110G00021010>01Prn0100000020101PrP@P?%6_RrP_PQPNPqD>PrPQPNPqCD'0PpP]Q0DPmPIP@P5PyP:P\PTPqC8Rq,2GPqn0100000020000PxF3P;n0100000020100RxPxPxPxP@P?Q0OPuPTPQPvD>Q0OPTPQPvCD'0PtPbQ0QP6PEP@P5Q0_P9P]P\PvC8Rv,2BPvn0100000020000PXF3P;n0100000020100RXPXn0110@00081110H111023110C1091003110C1091003110C1091003110C1091004110F10?1021054110F106101102n0100000020001P;n0100000020100P;n10110G00021110=00n0100000020001P;n0100000020100P;n10110G00021110E00P;n10110G00021110;00P;n10110G00021110A00P;n10110G00021110B00n200110G000121107108n200110G000121103104P;n10110G00021110D00n0100000020001=7?Ae207311o3157?eW<W8o"). Qed.


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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bh11kh21nh31oh43offh52b1h62b2h72csh81eh92k1h:2k2h;1lh<2n1h=2n2h>2ubh?2ukh@2uni002bbi013bhii022bki033nhii043nloi052qbi062qki073reti084sphii094sploi0:1xp;1p;2p;5p;7p;4p;3p;6g00@cj1nTg00g[j14Tg02fAj1Vj4KTg00F=R0j1ETg050?j1PTg06]mj1]Tg03T]j2OTg01Knj1MTg00lQj1STg06FVj1FTg01Anj20Tg01Bjj1<Tg03SZj16Tg06_1j1kTg06?>j2NTg01\fj12Tg003hj1ATg03D[j2?j1bTg03L`j28j1\Tg01KQj2=Tg03T?j1:Tg03h\j1UTg058bj2TTg01K4j2HTg02>Bj2RTg03BVj5Gj1dTg017?j25Tg00PDj1ITg02>_j7Jj1[Tg03OXj5Dj1aTg00F_j2QTg06GVj4@Tg03FYj2>j1fTg03M]j27j1hTg03CYj5Cj1mTg02<`j7Bj1jTg03PYj5Lj1lTg001hj33Tg00GAj2cTg03HQj1_Tg00>Fj69Tg03NWj1^Tg02?gj1`Tg069_j1ZTg06_Oj1eTg02e?j1Yj4gTg02hGj1XTg06`Vj1WTg06aZj1iTf0R1#A#Ap=;f2R2f1R3'5/51p=1g014ER4g00\8R5g00]5R6g012G#nR7^@5]?]>R8%41R9#V%E4R:g00NdR;P:%P3p,1A#]R<'O#MR=%S4R4P0P6P:%F3R>g00aHR?P5P6P:g01YJ#;R@#;#;#;#;RA,02#<RBP?P5P6P:f4RC/0@g03U:RD#6RE#6#6RF#6RG#kRH'N#<RIP0P6P:f6RJ#4RK#2RL%AARM,0JRN'?ROP0P6P:f7RP#4RQ#2RR10PMRS'8RTP0P6P:f8RU#4RV#2RW10UARX'8RYP0P6P:f9RZ#4R[#2R\10Z@R]'?R^P0P6P:f:R_#4R`#2Ra10_@Rb'8RcP;P:g02B5/=Cf3RC%:E%UE#6#6#6#:'T'=1H2C%:F'Hg02BSRF'=31%:GRG/=31R1F31RFf;R2#4RE#2RdPEPJf5RePGDG'5PdPJPe%IGRfPUPP102MRgFJRhPdPEPUPPPgDDRd31P2PZ%:D#I,Q5RDP_PJPePfO3C@P4n0100000020000P4n10110:00021010800P4n10110:00021010900P4n10110:00021010100P4n10110:00021110300P4n10110:00021110400n200110:000121105106n200110:000121100102P4n10110:00021110700n0100000020001P;P:P=P4P0P6P:P>P?P5P6P:PBP?P5P6P:PIP0P6P:1>KNP0P6P:17QSRiP0P6P:17VXRjP0P6P:1>[]P0P6P:17`bP;P:PEPEPJPePGDC,5FRkPEPJPePfPUPPPgFBPEPEPUPPPgDLRl31P2PZPDPEPJPePfCKC@R2P4n0100000020000RmP4n10110:00021010800RnP4n10110:00021010900P4n10110:00021010100P4n10110:00021010300P4n10110:00021110400n200110:000121105106n200110:000121100102P4n10110:00021110700n0100000020001Ro33X;8P;^26^46^05^17R8%m9P;P:P=P4P0P6P:P>P?P5P6P:PBP?P5P6P:PIP0P6P:POP0P6P:PTP0P6P:PYP0P6P:P^P0P6P:PcP;P:P_PEPJPePGO4,5F?1hdP2P4n0100000020000P4n10110:00021010800P4n10110:00021010900P4n10110:00021010100P4n10110:00021110300P4n10110:00021110400n200110:000121105106n200110:000121100102P4n10110:00021110700n0100000020001=3:oX08P;^25^46^05^17R7%l9P;P:P=P4P0P6P:P>P?P5P6P:PBP?P5P6P:PIP0P6P:POP0P6P:PTP0P6P:PYP0P6P:P^P0P6P:PcP;P:P_PEPUPPPgO491khP2P4n0100000020000P4n10110:00021010800P4n10110:00021010900P4n10110:00021010100P4n10110:00021110300P4n10110:00021110400n200110:000121105106n200110:000121100102P4n10110:00021110700n0100000020001=3:oX07P;^=5^:6^65^<5^96^55R7%j9P;P:P=P4P0P6P:P>P?P5P6P:PBP?P5P6P:PIP0P6P:POP0P6P:PTP0P6P:PYP0P6P:P^P0P6P:PcP;P:P_PJPePfPUPPPgO6=1klP2P4n0100000020000P4n10110:00021010800P4n10110:00021010900P4n10110:00021010100P4n10110:00021110300P4n10110:00021110400n200110:000121105106n200110:000121100102P4n10110:00021110700n0100000020001=3:oX07%E6^85R7%h9P;P:P=P4P0P6P:P>P?P5P6P:PBP?P5P6P:PIP0P6P:POP0P6P:PJPSO1P0P6P:PPPXO1P0P6P:P^P0P6P:PZPbO1PmP4n10110:00021010800P4n10110:00021010900P4n10110:00021010100P4n10110:00021010300P4n10110:00021110400n200110:000121105106n200110:000121100102P4n10110:00021110700n0100000020001=3:oX37P7%f9P;P:P=P4P0P6P:P>P?P5P6P:PBP?P5P6P:PIP0P6P:PePNO1P0P6P:PiP0P6P:PjP0P6P:PUP]O1PnP4n10110:00021010900P4n10110:00021010100P4n10110:00021010300P4n10110:00021110400n200110:000121105106n200110:000121100102P4n10110:00021110700n0100000020001=3:oX37P;P:%P1/O<#MR<P4P0P6P:%F1R7P?P5P6P:103A#<R3P?P5P6P:10C@/NH#<RHP0P6P:%4eRC10eMRo'>P0P6P:17KNP0P6P:10PARA,7QP0P6P:10U@R@,>VP0P6P:17[]P;P:P`P`PJPePGDC,5FP`PJPePfPUPP10_MRMFBP`P`PUPPPMDL31P_PZPDP`PJPePfCKC@P4n0100000020000P4n10110:00021010800P4n10110:00021010900P4n10110:00021010100P4n10110:00021010300P4n10110:00021110400n200110:000121105106n200110:000121100102P4n10110:00021110700n0100000020001R[,c:%29RV#b%_9E9%\V%^9E9%[V%`9E9%aV%Z9E9%dV%e9E9%YV%X9E9P;P:P<P4P0P6P:P7P?P5P6P:P3P?P5P6P:PHP0P6P:%2C/?oP0P6P:18LNP0P6P:18RAP0P6P:1?W@P0P6P:18\]P;P:PaP`PJPePGDG,5FPaPJPePfPUPPPMFJPaP`PUPPPMDD31P_PZPDPaPJPePfCgC@P4n0100000020000P4n10110:00021010800P4n10110:00021010900P4n10110:00021010100P4n10110:00021110300P4n10110:00021110400n200110:000121105106n200110:000121100102P4n10110:00021110700n0100000020001=3:[e%W1%i153:eW7o"). Qed.


(* [comment removed for export] *)
Definition img_cov (k : list kentry) (a b : Z) : bool :=
  existsb (fun K => match K with KImg lo hi => Z.leb lo a && Z.leb b hi | _ => false end) k.

Definition img_covB (bc : bctx) (a b : Z) : bool :=
  existsb (fun K => match K with KImg lo hi => Z.leb lo a && Z.leb b hi | _ => false end) (bc_fk bc).
Lemma img_covB_eqf : forall fk, img_covB (mkbc fk) = img_cov fk.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01Ki001Kh11bh22fkh31lh41xh52x0i012a0i022a1i032a2i041ci051ei062hii071ki082k0i092loi0:1mi0;1ni0<2n1i0=2n2i0>1vi0?1wp;1p;2p;3p;6p;5g00@cj1@Tg01\fj12Tg06bbj17j2?j3=Tg06ccj16j2;j3<Tg01KQj20Tg017?j23Tg008Fj31Tg001hj34Tg00GAj28Tg02N=j19Tg02P:j1:Tg00>Fj6>Tg02A3j55Tg012GR0#@R1g00]5R2g00NdR3^12f0R4#2#7%64P2P3f1R5#2/?41;54P1f2R6P0P3P4g00OdR7P7P7f5,05f4R8/04'3R9P7P7P7P7P7P7n01100000:3010110?10>2010110;3010110;107201091062010510:301051091062010110;4010210<10310=3010110;1042010110;X00=104P0P3P4P7P7P7P9P7P7P7P7P7P7n01100000:3010110?10>2010110;3010110;108201091062010510:301051091062010110;4010210<10310=3010110;1042010110;X00f3R9510543X31P0P3P4P7P7P710581094'3P7P7P7P7P7P7n01100000:3010110?10>2010110;3010110;108201091062010510:301051091062010110;4010210<10310=3010110;1042010110;X00=106,83%26R0#9%:6E>A=054A<654543eX52D5X42D5W2o"). Qed.
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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01bi001bh11kh22b1h32b2h42csh51ei011eh62k1h72k2h81lh91ni021nh:2n1h;2n2h<1oh=3offh>2ubh?2ukh@2uni031ai041di052dbi063dhii072dki083dsti091ii0:2k0i0;2loi0<2n0i0=2opi0>3reti0?3srci0@2sxi0A1xp;1p;2p;4p;3p;7p;5p;6g00@cj1nTg00g[j18Tg03K\j1Zj5ITg00F=R0j1CTg050?j1STg06dcj1dTg03T]j2@Tg01Knj1ETg00lQj1LTg06FVj1JTg003hj1BTg05<Jj2>Tg06efj1mTg03h\j16Tg03T?j1ATg017?j20Tg01Anj25Tg01Bjj1OTg01\fj1:Tg03L`j2Nj1bTg00PDj19Tg03U_j4Mj1^Tg00F_j24Tg03<jj2YTg06HYj3KTg01K4j2DTg02>Bj2HTg01KQj2XTg03SZj1?Tg06ccj3WTg02>_j7Gj1`Tg00n;j2FTg01HVj3VTg01LLj2UTg02iMR1j4TTg06GVj4=Tg03M]j2Rj1hTg03Vdj4Qj1kTg02<`j7Pj1jTg02fAR2j4lTg001hj31Tg00GAj2cTg00>Fj67Tg03NWj1_Tg02?gj1aTg06IZj1eTg03JWj1fj5\Tg06Jcj1]Tg06fgj1gTg06h0j1[Tg00LGj3iTf0R3#B#Bp=;%63#6p=3f2R4f1R5'0/03p=<g012GR6?i53p=2g014ER7%n6R6g00\8R8g00]5R9g00NdR:^98]=]0R;]1R<%83R=#Z%C7R>P:P>%S5p,1AR?#dR@'@#ERA%L7R7P0P9P>%J5RBP0P9P>g01YJ#;#;#;#;RC#;RD#BRE,>4RFP0P9P>f3RG%BERH'>RIP:P>%m?R?,@5g03U:RJ#6#3#3#3RK#3#3#ARL,@3'0#ERMP7g00aHRNP8P9P>f4/5D#OROP0P9P>f6RP#8RQ#:RR15PDRS'NRTP0P6P>P:%C6RUf7RV#8RW#:RXP4P5%9LRYCM146WRZP8PU15VDR[f8R\#8R]g02BSR^,Y3R_;KL,46%L6R`P`P`P`P`P`P`n011080008101041010<3010=1031003010=1031003010=1031003010=1031004010@10;10<1014010@10:10910<Ran0100000020000P:P>1D5L/H^g02B5Rb/X?%?J#?RJ#6#ARc,D?Rd/H^3<R^PVP]PGP4PYO4'0AW3?dRd%:]PGP4PY%9bRbP?%9cRcFGRe3<P\PP15\D,48Rf1FG4g06i=#97VCRC%?J#A,D4,FG%?K#6#3#A#9'URKP3PGP4PYCT'2'2RJC=RgP7n0100000020000P7n10110A00021110:00P7n10110A00021110600n200110A000121105107n0100000020001P7n10110A00021110200P7n10110A00021110?00P7n10110A00021110>00n0100000020001P:P>PAP7P0P9P>PBP0P9P>PFP0P9P>PIP:P>PMP7PNP8P9P>POP0P9P>1RQSRhP0P6P>P:PUPWP4P5PYCQPZPan0100000020000RiP:P>P]P]PGP4PYDI=<^dRjP]PGP4PYPbP?PcFP'0R]P\PPPfP3PGP4PYCl,2K,2CRkC=P7n0100000020000P7n10110A00021110:00P7n10110A00021110600n200110A000121105107n0100000020001P7n10110A00021110200P7n10110A00021110?00P7n10110A00021110>00n0100000020001Rl31X0<P;%k=P:P>PAP7P0P9P>PBP0P9P>PFP0P9P>PIP:P>PMP7PNP8P9P>POP0P9P>PTP0P6P>P:PUPPP4P5PYO3PZPan0100000020000P:P>10jePgP7n0100000020000P7n10110A00021110:00P7n10110A00021110600n200110A000121105107n0100000020001P7n10110A00021110200P7n10110A00021110?00P7n10110A00021110>00n0100000020001=1>lX0;P:^;8^79^38^:8^69^28R;%j=P:P>PAP7P0P9P>PBP0P9P>PFP0P9P>PIP:P>PMP7PNP8P9P>POP0P9P>PTP0P6P>PiP:P>PVPGP4PYPbP?PcO6,0jPgP7n0100000020000P7n10110A00021110:00P7n10110A00021110600n200110A000121105107n0100000020001P7n10110A00021110200P7n10110A00021110?00P7n10110A00021110>00n0100000020001=1>lX0;%C9^58R;%h=P:P>PAP7P0P9P>PBP0P9P>PFP0P9P>PIP:P>PMP7PNP8P9P>POP0P9P>f5RjPSO1P0P6P>PiP:P>P]PgP7n0100000020000P7n10110A00021110:00P7n10110A00021110600n200110A000121105107n0100000020001P7n10110A00021110200P7n10110A00021110?00P7n10110A00021110>00n0100000020001=1>lX<;P6^@8^?9^>8^16R;P2P:P>PAP7P0P9P>PBP0P9P>PFP0P9P>PIP:P>PMP7PNP8P9P>POP0P9P>PhP0P6P>PiP:P>P]P\PPPfPVP3PGP4PYO4,2K,2CC=P7n0100000020000P7n10110A00021110:00P7n10110A00021110600n200110A000121105107n0100000020001P7n10110A00021110200P7n10110A00021110?00P7n10110A00021110>00n0100000020001=1>lX8;P:P>%S3/@@#ER@P7P0P9P>%J3R;P0P9P>1>5EREP0P9P>1>4HRHP:P>PMP7PNP8P9P>15GD#ORlP0P9P>%8jRC15jDRj'RP0P6P>P:PUPQP4P5PYCQ146QRQP8PUPSAKW_L,46P`P`P`P`P`P`P`n011080008101041010<3010=1031003010=1031003010=1031003010=1031004010@10;10<1014010@10:10910<R`n0100000020000P:P>PWPWPGP4PYDI,0^PWPGP4PYPbP?PcFP7<dPVPP148[R[PkC=P7n0100000020000P7n10110A00021110:00P7n10110A00021110600n200110A000121105107n0100000020001P7n10110A00021110200P7n10110A00021110?00P7n10110A00021110>00n0100000020001Rk,c>P1g06N:E7%:=R1#b%_=E7%`1%a=E7%^1%e=E7%f1%]=E7P:P>P@P7P0P9P>P;P0P9P>PEP0P9P>PHP:P>PMP7PNP8P9P>PlP0P9P>%:C/NjP0P6P>P:PUPRP4P5PYCMPQP`n0100000020000P:P>PXPWPGP4PYD\,0^PXPGP4PYPbP?PcFG7<dPVPPP[PJC=P7n0100000020000P7n10110A00021110:00P7n10110A00021110600n200110A000121105107n0100000020001P7n10110A00021110200P7n10110A00021110?00P7n10110A00021110>00n0100000020001=1>ke%g3%[351>eW4o"). Qed.


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
Definition MAXVA_LEN : Z := 180.
Definition MAXVA_POST : list (nat * Z) :=
  [(10%nat, 0x7fffffffffff); (11%nat, 0xffffffffffffffff); (12%nat, 0x3333333333333333);
   (13%nat, 0x0f0f0f0f0f0f0f0f); (14%nat, 0x0101010101010101); (15%nat, 0x7fffc00000000000)].
Definition TWO46 : Z := 0x400000000000.
Definition summary_maxva (cs : acs) : option acs :=
  if (Z.eqb (x_maxva A) 0 || negb (Z.eqb (pc cs) (x_maxva A)))%bool then None else
  let k := kn cs in
  match xlo k (reg cs 10), xhi k (reg cs 10) with
  | Some lo, Some hi =>
      if (Z.leb TWO46 lo && Z.ltb hi TWO47)%bool
      then Some (set_pc (fold_left (fun c rv => set_reg c (fst rv) (ELit (snd rv))) MAXVA_POST cs) (pc cs + MAXVA_LEN))
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition kn_readable_x (k : list kentry) (rb : expr) (rk : Z) (ne : expr) : bool :=
  existsb (fun K => match K with
                    | KUnk (SA kb kk) len | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
                        xinside k rb rk ne kb kk len
                    | _ => false
                    end) k.



(* [comment removed for export] *)
Definition e_envp : expr := eadd e_sp0 (eadd (escale 8 (EVar V_ARGC)) (ELit 16)).
Definition e_auxv : expr := eadd e_envp (eadd (escale 8 (EVar V_ENVC)) (ELit 8)).
Definition e_str0 : expr := eaddz e_auxv 160.
Definition e_str1 : expr := eadd e_str0 (eaddz (EVar V_L0) 1).
Definition e_atrandom : expr := eadd e_str0 (escale 8 (EVar V_W)).
(* [comment removed for export] *)
Definition e_atr8 : expr :=   (* [comment removed for export] *)
  eadd (eadd (escale 4096 (EVar V_S1)) (eadd (escale 2 (EVar V_S2)) (escale 512 (EVar V_SP)))) (eadd (EVar V_ARGC) (eadd (EVar V_ENVC) (EVar V_W))).

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
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "p'0h01jh11th21dh31ih44resth51xh62IHh71bi001bh81oi011oi021li031mi041np;1p;3p;2p;4p;6p;5g00F=j1BTg00@cR0j1ATg06j>j32Tg00lQj1<Tg00D`j20Tg06k=j44Tg00eAj1=Tg00GAj25Tg001hj33Tg003hj17Tg00LGj3:Tg00>Fj6@Tg04GLj5>Tg06kYj2;Tg00F_j2?Tg005LR1f0R2'?p=8f5R3f4R4f3R5f2R6f1R7C4;32p=1g01YJR8=272p=6P6P8P7P2C4p=9%B1R9#AR:P9P9P2A2657%<1R;g00NdR<P91025%87R=P9P2P6P;C4R>n0100000020000E1^01^21^1:R?X31P0P9P9P9P71626P;P<P91078%86R@P9P7P2P;C4RAn0100000020000E1P6P1P9P9P2%=9RB/66P;P<P91028RCP@P9P2PBP;C4RDn0100000020000E1P2159=16B7=99;P<P91088REP=A99B;RFn0100000020000539eP1P1P9P2P;P;n0110400020010103=39;P2159;RGPGX01P2O1RHn0110400020010104P9P9%72RI16B5P;P<P910I8RJ%85RKP9PIPBP;C4RLn0100000020000E1eX01P2O1n0110400020010104P1P9P9P2A:967RMf6RN'6P;P<P9PC%8NRCP9P2PMP;C4ROn0100000020000E1P4%83RP,59A:972RQ/63=99;P<P9PEPPA99Q;REn0100000020000539e159>P9P9PIA:956R>f7RR'6P;P<P9PJ%8RRJP9PIP>P;C4RSn0100000020000E1eX01P2O1n0110400020010104X4:X59P7P2O2n10110200020020101102X01X21X1:P0P9P9P9P7%73R0=226P;P<P91070P@PAn0100000020000E1P6P1P9P9P2A2B06P;P<P91020P@PDn0100000020000E1P2PG%74R@=2B7=99;P<P9108@P=PFn0100000020000539eP9P<P9102NRFPKPDn0100000020000P<P9107R%84R@P;n01000000200009392X89PFP<P<P<P9P2PPP9P6PBP;C4n0100000020000P<P9P2PPP;n0100000020000539P2P1A39PPP7159@159CX01P2O1n0110400020010104P1A39D;P7PGPHn0110400020010104n0110000020000b7P9P2A2BN5P;C4P3PBP5P2O3E@P9P9PI%7NRH=2B5P;P<P910IHPKPLn0100000020000E1eX01P2O1n0110400020010104P1P9P9P2f9RL#7RK=2MNP;P<P9102KPCPOn0100000020000E1P41597f8#7R4=2Q3=99;P<P91084PPPEn0100000020000539ePLP6PRP2O3P9P9PIf:#7RL=2>RP;P<P910ILPJPSn0100000020000E1eX01P2O1n0110400020010104X4:X59P7P2O2n10110200020120101102X01X21X1:X6?X31P2P7D>X31W1A2567/;2P<P91026P=1;52n0100000020000539^01^21^31^1:eo"). Qed.
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

(* [comment removed for export] *)
Definition K_RND : nat := 25.

(* [comment removed for export] *)
Definition e_auxb : expr * Z := split_lit e_auxv.
Definition e_atrb : expr * Z := split_lit e_atrandom.
Definition auxw (i : Z) (ty : Z) (v : expr) : list kentry :=
  [KWord (SA (fst e_auxb) (snd e_auxb + 16 * i)) 8 (ELit ty); KWord (SA (fst e_auxb) (snd e_auxb + 16 * i + 8)) 8 v].

(* [comment removed for export] *)
Definition init_kn_with (atr : kentry) (A : atable) : list kentry :=
  [KRange (EVar V_S1) 0xFFFF0000 0xFFFFFFFF; KRange (EVar V_S2) 0 255; KRange (EVar V_SP) 0 7;   (* [comment removed for export] *)
   KRange (eaddz e_atrandom 16) 0x7fff800000c0 0x800000000000; KRange e_atr8 0xFFFF0000001 0xFFFFFFFFFE7;   (* [comment removed for export] *)
   KRange e_sp0 0x7fff80000000 0x7fffffffff40; KRange e_pd 0x7fff80000000 0x7ffffffff000;                 (* [comment removed for export] *)
   KRange (eadd (escale 4096 (EVar V_S1)) (eadd (escale 2 (EVar V_S2)) (escale 512 (EVar V_SP)))) 0xFFFF0000000 0xFFFFFFFFFE8;
   KRange (EVar V_ARGC) 1 1024; KRange (EVar V_ENVC) 0 256; KRange (EVar V_L0) 0 131071; KRange (EVar V_L1) 0 131071;
   KRange (EVar V_UID) 0 0xFFFFFFFE; KRange (EVar V_HW) 0 0x3FFFFF;
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
Definition e_stkwlen : expr := esub (ELit STK_WTOP) e_pd.
Definition init_vis (A : atable) : list (expr * expr) :=
  [(ELit (img_lo A), ELit (img_hi A - img_lo A)); (eaddz e_pd STK_OFF, e_stkwlen)].

Definition init_acs_of_with (kn0 : list kentry) (A : atable) : acs :=
  ACS (mk_ss (a_entry A) init_regs kn0 NX0) [] (img_hi A - img_lo A) MBASE_MIN 0 (init_vis A) []
      (vis_cost (img_hi A - img_lo A) + vis_cost STK_WMAX) (escale 4096 (EVar V_BRK)) FdStd false.
Definition init_acs_of (A : atable) : acs := init_acs_of_with (init_kn A) A.        (* [comment removed for export] *)
Definition init_acs_of_zero (A : atable) : acs := init_acs_of_with (init_kn_zero A) A.  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ASAN : atable :=
  {| img_lo := 0x10000; img_hi := 0x60d000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x306ac; rw_lo := 0xaf000; rw_len := 0x55e000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x634a0; x_imemcpy := 0x63424; x_memset := 0xa8e5c; x_memcpy := 0xa8a58; x_memiszero := 0x639d0;
     x_istrncpy := 0x638cc; x_sealed := 0x1182b; x_popfree := 0x36a98;
     x_maxva := 0x64ae8;
     x_envscan := 0x9e860; x_envscan_k := 0x9e86c; x_pnscan := 0x9e924; x_pnscan_k := 0x9e930;
     stops_more := [0x3470c; 0x35d30; 0x5f51c; 0x6da24; 0x6dbb4; 0x59b64; 0x59b78; 0x59b8c]  (* [comment removed for export] *) |}.

(* [comment removed for export] *)
Definition ASAN_TEXT_LO : Z := 0x306ac.
Definition ASAN_TEXT_N : nat := 128697.
Definition asan_init : acs := init_acs_of ASAN.

(* [comment removed for export] *)
Definition BOTH : atable :=
  {| img_lo := 0x10000; img_hi := 0x60f000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x30670; rw_lo := 0xb1000; rw_len := 0x55e000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x63464; x_imemcpy := 0x633e8; x_memset := 0xab85c; x_memcpy := 0xab458; x_memiszero := 0x63994;
     x_istrncpy := 0x63890; x_sealed := 0x1182b; x_popfree := 0x36a5c;
     x_maxva := 0x64aac;
     x_envscan := 0xa1260; x_envscan_k := 0xa126c; x_pnscan := 0xa1324; x_pnscan_k := 0xa1330;
     stops_more := [0x346d0; 0x35cf4; 0x5f4e0; 0x6d9e8; 0x6db78; 0x59b28; 0x59b3c; 0x59b50]  (* [comment removed for export] *) |}.
Definition BOTH_TEXT_LO : Z := 0x30670.
Definition BOTH_TEXT_N : nat := 131400.
Definition both_init : acs := init_acs_of BOTH.

End APC.
