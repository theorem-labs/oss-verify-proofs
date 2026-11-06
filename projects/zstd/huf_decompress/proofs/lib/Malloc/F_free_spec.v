(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free MallocTree MallocBlocks MallocHINV MallocFacts_B MallocFacts_B_reach Malloc_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_B MallocKit_B2 MallocFacts_Bpres F_ntf F_free_K F_free.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require MallocFacts_inv.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require MallocFacts_inv3.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_free_spec () := "C35stdpp4base6LookupC59OSSVerify5KrLib6Malloc<MallocBlocks5blockC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC47Corelib5Lists7ListDef3mapI46Stdlib7Sorting;Permutation;Permutation00C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib6Malloc6F_free@NoDup_map_inj_inC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc6F_free=filter_ext_inC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation>Permutation_inC45stdpp>list_relations4list9NoDup_nilC59OSSVerify5KrLib6Malloc8ProgDeps4bptrC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List5NoDup00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib6Malloc<MallocBlocks6blk_idC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<Malloc_iface8bptr_eqbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool7Is_trueC59OSSVerify5KrLib6Malloc<MallocBlocks8blk_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8aptr_eqbC1?~~~~~~~~~~~~~~~C35stdpp9decidable;Is_true_decC59OSSVerify5KrLib6MallocAMallocFacts_Bpres>aptr_eqb_spec'C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4andbC47Corelib4Init5Logic9False_indK47Corelib4Init5Logic3and01C47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z8eqb_reflC47Corelib4Init5Logic3notC59OSSVerify5KrLib6Malloc<Malloc_iface9lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc6F_free4lbrmC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3sndI47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C46Stdlib7Sorting;Permutation?Permutation_mapC46Stdlib7Sorting;PermutationAPermutation_NoDupC45stdpp>list_relations4listBfilter_Permutationc59OSSVerify5KrLib6Malloc;F_free_spec9lbrm_permC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma lb_remove_lbrm LB (p : bptr) A n : List.NoDup (map blk_slot LB) -> In (p, A, n) LB ->
  lb_remove p LB = lbrm LB (p, A, n).
Proof.
ltac2:(KReplay.run1 (kr_t_F_free_spec ()) ["CANSEC1"] "p'0h01xh11Eh21Hh32Hxh41bi001bh51Ah62LBh71ni011nh81ph93Hinh:2NDh;2NEh<2b'h=1ri021ri031ep;1p;4p;2p;3p;:p;6p;8p;7p-1R0p10000R1p4p710p8P0P1p4p7210p8g000DR1p4p70R0g001BR2p4p710R3p8P0g001YR4p4p710p8P0p10025p4p710p8P0g002`R5p4p710p8P0g003>R6p4p710p8P0g004AR7p4p710p8P0p1005Ap4p710p8P0p1005mp4p710p8g006SR0p4p70R8P3p8P8g007LR8p4p710R3p8g007iR9p4p70R:P4p4p7210p8P:P6p4p7210p8P:P3p8P:g008^R:p4p710p8g009:j1TTP4j4STP:j2PTg009Zj2BTP2j3=Tg00::j1ETg00;9j2CTg00<:j1;Tg00<Xj16Tg00=3R2j1:Tg00>4j29Tg00>mj1?Tg00?Kj2RTg00@Wj35Tg00A1R:j2QTg00ATj28Tg00B1j2<TP6l:OTg00BOj2NTg00Bnj4ATg00CIj2@Tg00Cbj1LTP5j6Ij8JTg00DDj1KTP7j7HTg00D]j2GTg00E_j2MTg00FVj4DTP8j3>Tg00G6j3FTf3R8g00GSR7P0P7f2R5f1R6CDf0R4CDp=3A>6749>07p=4A>974p=0AF974p=1%;4#6p=7%;6#6/@4p=2%T1R3P1P9P2P8CS,P91B07R;/B7P;P8P5P6C3f4R<3=P1%E4f5R='C#;R>#6X41%:4P;P=P<P8C3#:'9#;R?#6X<1%?>X01%??X01P=f6R?9=1414;6R>#0R@%0?RA'Rg00H1RB?5@A19@ARA'Q14;5RC#0f7RD#0'9g00HfREP:14;8#0f8R:#055B14;=#1f:RF#1'8RG,<6%76'2P614;<#0f9RH#055BRIP1P9P2f;R2PDP=P;PFPHP:C3R:P<P?P4M:OA51=:P1P;P2PFPHC3RHf=R:9=14%0:95B@%1Cf>#1'8g00IFRC#6RD'2]1]3X01f<R99=1HP;P9P2PFC3,4;#0%0955BPEg00IfRBg00JFRF,24X4EPF\FREPE1NF4X2FREPECA%7BRE/@Fe%1:RF/8F%LFEIP;P:P9P2C3,4;#1/8F/2DeW1W3P?P4P=P6GJb21<BG/2EeW1P4O1%KI%6BRBPB[RIPIP4X2BRBPBCA1<CG%7C'2eW;P4O1n10210010200021110310101b4b=%1>%1?'8,<AP;P?P=P<C3RA,4;#0,9@#7'2e%E6/C?%:6%:A'9#7'2eW3X01FH1G<=P;P<P8P5C3,M=553eW9W:X77X57X80X63P8P5P6P4O4X77X57X80W6o"). Qed.

Lemma NoDup_map_perm {A B} (f : A -> B) (l l' : list A) : Permutation l l' -> List.NoDup (map f l) -> List.NoDup (map f l').
Proof.
ltac2:(KReplay.run1 (kr_t_F_free_spec ()) ["CANSEC1"] "h01Ah11Bh21fh31lh42l'h52NDh61Pp;1p;3p;4p;2p;6p;5p200R0g001YR1p4p710p8P0g0025R2p4p710p8P0g00JcR3p4p710p8p201R4P1p4p7210p8P4g00KPR5p4p710p8P4P3p4p7210p8P4g008^R6p4p710p8g009:j11TP2j35TP1j40TP6j22TP3j64TP5j53Tf1R5P5[R3f2R6#1R1f3R2#1R7f4R8f0R9755f5R:P8P2P6C0,28P:f6R;P:P8P2C0P;P:P8P6C0P;P:P8P2P6P5E4P9D3W5W6X47X31X23X14X00P8P2P6P5P9O5W4W3W2X14X00o"). Qed.

Lemma lbrm_perm LB LB' blk : Permutation LB LB' -> Permutation (lbrm LB blk) (lbrm LB' blk).
Proof.
ltac2:(KReplay.run1 (kr_t_F_free_spec ()) ["CANSEC1"] "h02LBh13LB'h23blkh31Ph42b'h51xp;1p;3p;2p;6g009:j18Tg0025j32Tg00=3j11Tg00>4j23Tg00<:j17Tg00<Xj16Tg00>mj15Tg00L?j64Tg00E_j20Tg000DR0#8R1f2R2f1R3520P0f0R4#1%12'3#7R5#6X40%55X50f3R5P2P4E410531023520eW3X20X11X01P2P3P4O3X20X11W0o"). Qed.

Lemma In_lbrm_perm LB LB' blk b : Permutation LB LB' -> In b (lbrm LB blk) -> In b (lbrm LB' blk).
Proof.
ltac2:(KReplay.run1 (kr_t_F_free_spec ()) ["CANSEC1"] "h02LBh13LB'h21bh33blkh41Hh51Pp;1p;3p;2p;4p;6g009:j15Tg0025j34Tg00E_j20Tg001Bj31Tg00Lnj43Tg005Aj62Tg000DR0#5R1f3R2f2R3540f1R4f4R5/03510P0f5R6/021052P3P6P5P2P4C3f0R5E2W4W5X20X30X11X01P2P3P4P5O4X20X30X11W0o"). Qed.

(* [comment removed for export] *)
Section FP.
Variables (st st' : mstate) (LB0 : list block) (blk : block) (lo sp : Z) (m m' : mem).
Hypothesis C : CINV st LB0.
Hypothesis LO : ATOP <= lo.
Hypothesis LS : lo <= sp.
Hypothesis BLKR : forall blk', In blk' (lbrm LB0 blk) -> exists r', (s_regions st') !! fst (blk_slot blk') = Some r'.
Hypothesis SHR : forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r'.

Let FPT := fun a => free_fp st lo sp a \/ DROPPED st st' a \/ 107900 <= a < 107904.
End FP.

End CANSEC1.
