(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import F_syscalls MallocRep F_malloc_free MallocTree MallocBlocks MallocHINV MallocFacts_B MallocFacts_B_reach Malloc_iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import MallocKit_B MallocKit_B2 MallocFacts_Bpres F_ntf F_free_K F_free.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require MallocFacts_inv.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require MallocFacts_inv3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_F_free_spec () := "C35stdpp4base6LookupC69OSSVerify5KrLib2CJ1A<MallocBlocks5blockC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC47Corelib5Lists7ListDef3mapI46Stdlib7Sorting;Permutation;Permutation00C47Corelib4Init5Logic8eq_ind_rC46Stdlib7Sorting;Permutation>Permutation_inC69OSSVerify5KrLib2CJ1A6F_free@NoDup_map_inj_inC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1A6F_free=filter_ext_inC1?~~~~~~~~~~~~~~~C45stdpp>list_relations4list9NoDup_nilC69OSSVerify5KrLib2CJ4Spec4Prog4bptrC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC69OSSVerify5KrLib2CJ4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List5NoDup00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib2CJ1A<MallocBlocks6blk_idC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1A<Malloc_iface8bptr_eqbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool7Is_trueC69OSSVerify5KrLib2CJ1A<MallocBlocks8blk_slotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc8aptr_eqbC1?~~~~~~~~~~~~~~~C35stdpp9decidable;Is_true_decC69OSSVerify5KrLib2CJ1AAMallocFacts_Bpres>aptr_eqb_spec'C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4andbC47Corelib4Init5Logic9False_indK47Corelib4Init5Logic3and01C47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z8eqb_reflC47Corelib4Init5Logic3notC69OSSVerify5KrLib2CJ1A<Malloc_iface9lb_removeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1A6F_free4lbrmC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3sndI47Corelib7Numbers7BinNums1Z00C69OSSVerify5KrLib2CJ4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C46Stdlib7Sorting;Permutation?Permutation_mapC46Stdlib7Sorting;PermutationAPermutation_NoDupC45stdpp>list_relations4listBfilter_Permutationc69OSSVerify5KrLib2CJ1A;F_free_spec9lbrm_permC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Lemma lb_remove_lbrm LB (p : bptr) A n : List.NoDup (map blk_slot LB) -> In (p, A, n) LB ->
  lb_remove p LB = lbrm LB (p, A, n).
Proof.
ltac2:(KReplay.run1 (kr_t_F_free_spec ()) ["AC_1"] "p'0h01xh11Eh21Hh32Hxh41bi001bh51Ah63Hinh72LBh82NDh92NEh:2b'h;1ni011nh<1ph=1ri021ri031ep;1p;4p;2p;3p;:p;6p;8p;7p-1R0p10000R1p4p710p8P0P1p4p7210p8g000DR1p4p70R0g001@R2p4p710R3p8P0g001WR4p4p710p8P0p10023p4p710p8P0g002^R5p4p710p8P0p1003<p4p710p8P0g003hR6p4p710p8P0g004iR7p4p710p8P0p1005gp4p710p8g006MR0p4p70R8P3p8P8g007CR8p4p710R3p8g007`R9p4p70R:P4p4p7210p8P:P3p8P:P6p4p7210p8P:g008XR:p4p710p8g0094j1TTP4j4STP:j2PTg009Tj2BTP2j3=Tg00:4j1ETg00;1j2CTg00<0j1;Tg00<Nj16Tg00<iR2j1:Tg00=hj29Tg00>dj1?Tg00?Bj2RTg00@Lj35Tg00@fR:j2QTg00AIj28Tg00Afj2<TP6l:OTg00BDj2NTg00Bcj4ATg00C>j2@Tg00CWj1LTP5j6Ij8JTg00D9j1KTP7j7HTg00DRj2GTg00ERj2MTg00FGj4DTP8j3>Tg00Fgj3FTf3R8g00GDR7P0P7f2R5f1R6CDf0R4CDp=3A>6749>07p=4A>974p=0AF974p=1%;4#6p=7%;6#6/@4p=2%T1R3P1P9P2P8CS,P91B07R;/B7P;P8P5P6C3f4R<3=P1%E4f5R='C#;R>#6X41%:4P;P=P<P8C3#:'9#;R?#6X:1%?>X01%??X01P=f6R?9=1414;6R>#0R@%0?RA'Rg00GbRB?5@A19@ARA'Q14;5RC#0f7RD#0'9g00HZREP:14;8#0f8R:#055B14;=#1f:RF#1'8RG,<6%76'2P614;<#0f9RH#055BRIP1P9P2f;R2PDP=P;PFPHP:C3R:P<P?P4M:OA51=:P1P;P2PFPHC3RHf=R:9=14%0:95B@%1Cf>#1'8g00I:RC#6RD'2]1]3X01f<R99=1HP;P9P2PFC3,4;#0%0955BPEg00IZRBg00J:RF,24X4EPF\FREPE1NF4X2FREPECA%7BRE/@Fe%1:RF/8F%LFEIP;P:P9P2C3,4;#1/8F/2DeW1W3P?P4P=P6GJb21<BG/2EeW1P4O1%KI%6BRBPB[RIPIP4X2BRBPBCA1<CG%7C'2eW9P4O1n10210010200021110310101b4b=%1>%1?'8,<AP;P?P=P<C3RA,4;#0,9@#7'2e%E6/C?%:6%:A'9#7'2eW3X01FH1G<=P;P<P8P5C3,M=553eW6W8X;7X57X<0W7o"). Qed.

Lemma NoDup_map_perm {A B} (f : A -> B) (l l' : list A) : Permutation l l' -> List.NoDup (map f l) -> List.NoDup (map f l').
Proof.
ltac2:(KReplay.run1 (kr_t_F_free_spec ()) ["AC_1"] "h01Ah11Bh22NDh31Ph41fh51lh62l'p;1p;3p;4p;2p;6p;5p200R0g001WR1p4p710p8P0g0023R2p4p710p8P0g00JWR3p4p710p8p201R4P1p4p7210p8P4g00KDR5p4p710p8P4P3p4p7210p8P4g008XR6p4p710p8g0094j11TP2j35TP1j40TP6j22TP3j64TP5j53Tf1R5P5[f2R3#1f3R6#1f4R1f0R2755f5R7P1P6P3C0,21P7f6R8P7P1P6C0P8P7P1P3C0P8P7P1P6P3P5E4P2D3W2W3W6W5W4X14X00o"). Qed.

Lemma lbrm_perm LB LB' blk : Permutation LB LB' -> Permutation (lbrm LB blk) (lbrm LB' blk).
Proof.
ltac2:(KReplay.run1 (kr_t_F_free_spec ()) ["AC_1"] "h02LBh13LB'h21Ph32b'h43blkh51xp;1p;3p;2p;6g0094j18Tg0023j32Tg00<ij11Tg00=hj23Tg00<0j17Tg00<Nj16Tg00>dj15Tg00L3j64Tg00ERj20Tg000DR0#8R1f2R2f1R3520P0f0R4#1%12'3#7R5#6X30%55X50f3R5P2P4E410531023520eW2X40X11W0o"). Qed.

Lemma In_lbrm_perm LB LB' blk b : Permutation LB LB' -> In b (lbrm LB blk) -> In b (lbrm LB' blk).
Proof.
ltac2:(KReplay.run1 (kr_t_F_free_spec ()) ["AC_1"] "h01Hh12LBh23LB'h31Ph41bh53blkp;1p;3p;2p;4p;6g0094j15Tg0023j34Tg00ERj20Tg001@j31Tg00Lbj43Tg003<j62Tg000DR0#5R1f3R2f2R3540f1R4f4R5/03510P0f5R6/021052P3P6P5P2P4C3f0E2W0W3X40X50X21W1o"). Qed.

Section FP.
Variables (st st' : mstate) (LB0 : list block) (blk : block) (lo sp : Z) (m m' : mem).
Hypothesis C : CINV st LB0.
Hypothesis MR : mrep st m.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LS : lo <= sp.
Hypothesis BLKR : forall blk', In blk' (lbrm LB0 blk) -> exists r', (s_regions st') !! fst (blk_slot blk') = Some r'.
Hypothesis SHR : forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r'.
Hypothesis PE : pres_except (fun a => free_fp st lo sp a \/ DROPPED st st' a \/ 107900 <= a < 107904) m m'.

Let FPT := fun a => free_fp st lo sp a \/ DROPPED st st' a \/ 107900 <= a < 107904.

End FP.

End AC_1.
