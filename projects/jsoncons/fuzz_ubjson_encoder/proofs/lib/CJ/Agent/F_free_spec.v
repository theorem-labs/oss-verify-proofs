(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free MallocTree MallocBlocks MallocHINV MallocFacts_B MallocFacts_B_reach Malloc_iface.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import MallocKit_B MallocKit_B2 MallocFacts_Bpres F_ntf F_free_K F_free.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require MallocFacts_inv.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require MallocFacts_inv3.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_F_free_spec () := "C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocBlocks5blockC13~~~C46Stdlib5Lists4List2InC47Corelib5Lists7ListDef3mapI46Stdlib7Sorting;Permutation;Permutation00C47Corelib4Init5Logic8eq_ind_rC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent6F_free@NoDup_map_inj_inC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent6F_free=filter_ext_inC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec4Prog4bptrC13~~~C47Corelib4Init9Datatypes3fstC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4cptrC13~~~I46Stdlib5Lists4List5NoDup00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocBlocks6blk_idC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<Malloc_iface8bptr_eqbC13~~~C47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool7Is_trueC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocBlocks8blk_slotC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8aptr_eqbC13~~~C35stdpp9decidable;Is_true_decC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5AgentAMallocFacts_Bpres>aptr_eqb_spec'C13~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4andbC47Corelib4Init5Logic9False_indK47Corelib4Init5Logic3and01C47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z8eqb_reflC47Corelib4Init5Logic3notC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<Malloc_iface9lb_removeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent6F_free4lbrmC13~~~K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3sndI47Corelib7Numbers7BinNums1Z00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aptrC13~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C46Stdlib7Sorting;Permutation?Permutation_mapC46Stdlib7Sorting;PermutationAPermutation_NoDupC45stdpp>list_relations4listBfilter_Permutationc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;F_free_spec9lbrm_permC13~~~C46Stdlib7Sorting;Permutation>Permutation_in".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
Lemma lb_remove_lbrm LB (p : bptr) A n : List.NoDup (map blk_slot LB) -> In (p, A, n) LB ->
  lb_remove p LB = lbrm LB (p, A, n).
Proof.
ltac2:(KReplay.run1_chk (kr_t_F_free_spec ()) ["CEIL_WRAP_1"] "p'0h01xh11Eh21Hh32Hxh41bi001bh51Ah62LBh71ni011nh81ph93Hinh:2NDh;2NEh<2b'h=1ri021ri031ep;1p;4p;2p;3p;:p;6p;8p;7g0000R0p4p70R1g001FR2p4p710R3p8P1g001]R4p4p710p8P1p10029p4p710p8P1g002dR5p4p710p8P1g003BR6p4p710p8P1g004]R1p4p710p8g0065R7p4p70R8P3p8P8g007AR8p4p710R3p8g007^R9p4p70R:P4p4p7210p8P:P6p4p7210p8P:P3p8P:g008lR:p4p710p8g009Hj1TTP4j4STP:j2PTg009hj2BTP2j3=Tg00:Hj1ETg00;_j2CTg00=8j1;Tg00=Vj16Tg00>1R2j1:Tg00?Jj29Tg00@\j1?Tg00A:j2RTg00B^j35Tg00C8R:j2QTg00C[j28Tg00D8j2<TP6l:OTg00DVj2NTg00E5j4ATg00EPj2@Tg00Eij1LTP5j6Ij8JTg00FKj1KTP1j7HTg00Fdj2GTg00H>j2MTg00IMj4DTP8j3>Tg00Imj3FTf3R8g00JJR1P7P1f2R5f1R6CDf0R4CDp=3A>6149>71p=4A>914p=0AF914p=1%;4#6p=7%;6#6/@4p=2%T0R3P0P9P2P8CS,P91B71R;/B1P;P8P5P6C3f4R<3=P0%E4f5R='C#;R>#6X40%:4P;P=P<P8C3#:'9#;R?#6X<0%?>X00%??X00P=f6R?9=0414;6R>#0R@%0?RA'Rg00JhRB?5@A19@ARA'Q14;5RC#0f7RD#0'9g00L6REP:14;8#0f8R:#055B14;=#1f:RF#1'8RG,<6%76'2P614;<#0f9RH#055BRIP0P9P2f;R2PDP=P;PFPHP:C3R:P<P?P4M:OA50=:P0P;P2PFPHC3RHf=R:9=04%0:95B@%1Cf>#1'8g00LVRC#6RD'2]1]3X00f<R99=0HP;P9P2PFC3,4;#0%0955BPEg00M6RBg00MVRF,24X4EPF\FREPE1NF4X2FREPECA%7BRE/@Fe%1:RF/8F%LFEIP;P:P9P2C3,4;#1/8F/2DeW1W3P?P4P=P6GJb21<BG/2EeW1P4O1%KI%6BRBPB[RIPIP4X2BRBPBCA1<CG%7C'2eW;P4O1n10210010200021110310101b4b=%1>%1?'8,<AP;P?P=P<C3RA,4;#0,9@#7'2e%E6/C?%:6%:A'9#7'2eW3X00FH1G<=P;P<P8P5C3,M=553eW9W:X71X51X87X63P8P5P6P4O4X71X51X87W6o"). Qed.

Lemma NoDup_map_perm {A B} (f : A -> B) (l l' : list A) : Permutation l l' -> List.NoDup (map f l) -> List.NoDup (map f l').
Proof.
ltac2:(KReplay.run1 (kr_t_F_free_spec ()) ["CEIL_WRAP_1"] "h01Ah11Bh21fh31lh42l'h52NDh61Pp;1p;3p;4p;2p;6p;5p200R0g001]R1p4p710p8P0g0029R2p4p710p8P0g00N3R3p4p710p8p201R4P1p4p7210p8P4g00N`R5p4p710p8P4P3p4p7210p8P4g008lR6p4p710p8g009Hj11TP2j35TP1j40TP6j22TP3j64TP5j53Tf1R5P5[R3f2R6#1R1f3R2#1R7f4R8f0R9755f5R:P8P2P6C0,28P:f6R;P:P8P2C0P;P:P8P6C0P;P:P8P2P6P5E4P9D3W5W6X47X31X23X14X00P8P2P6P5P9O5W4W3W2X14X00o"). Qed.

Lemma lbrm_perm LB LB' blk : Permutation LB LB' -> Permutation (lbrm LB blk) (lbrm LB' blk).
Proof.
ltac2:(KReplay.run1 (kr_t_F_free_spec ()) ["CEIL_WRAP_1"] "h02LBh13LB'h23blkh31Ph42b'h51xp;1p;3p;2p;6g009Hj18Tg0029j32Tg00>1j11Tg00?Jj23Tg00=8j17Tg00=Vj16Tg00@\j15Tg00OOj64Tg00H>j20Tg0000R0#8R1f2R2f1R3520P0f0R4#1%12'3#7R5#6X40%55X50f3R5P2P4E410531023520eW3X20X11X01P2P3P4O3X20X11W0o"). Qed.

Lemma In_lbrm_perm LB LB' blk b : Permutation LB LB' -> In b (lbrm LB blk) -> In b (lbrm LB' blk).
Proof.
ltac2:(KReplay.run1 (kr_t_F_free_spec ()) ["CEIL_WRAP_1"] "h02LBh13LB'h21bh33blkh41Hh51Pp;1p;3p;2p;4p;6g009Hj15Tg0029j34Tg00H>j20Tg001Fj31Tg00P>j43Tg00QWj62Tg0000R0#5R1f3R2f2R3540f1R4f4R5/03510P0f5R6/021052P3P6P5P2P4C3f0R5E2W4W5X20X30X11X01P2P3P4P5O4X20X30X11W0o"). Qed.
End CEIL_WRAP_1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
