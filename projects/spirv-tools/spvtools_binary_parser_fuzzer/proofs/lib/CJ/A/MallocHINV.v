(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import STree Malloc MallocCtrl Prog.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import MallocRep MallocTree.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Export MallocBlocks.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_MallocHINV () := "I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C49OSSVerify5KrLib9RunRandom9rr_secretC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc5minitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1A<MallocBlocks8brk_linkC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01I69OSSVerify5KrLib2CJ1A<MallocBlocks;AREACH_from00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2CJ1A<MallocBlocks;AREACH_from01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01I47Corelib7Numbers7BinNums1Z00C69OSSVerify5KrLib2CJ1A<MallocBlocks5blockC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C69OSSVerify5KrLib2CJ4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec4Prog6ps_brkC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib2CJ4Spec6Malloc4concC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic3iffC69OSSVerify5KrLib2CJ1A:MallocTree;brk_link_psC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2CJ4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2CJ4Spec4Prog6PState00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2CJ4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib7Numbers7BinNums1N00".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Definition HINV_from (resv : list (Z * Z)) (st : mstate) (pbrk : Z) (LB : list block) : Prop :=
  brk_link st pbrk /\ AREACH_from resv st LB.
End AC_1.

Notation HINV := (HINV_from agent_reserved).
Section AC_2. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Lemma HINV_from_init : forall resv pbrk, HINV_from resv (minit rr_secret resv) pbrk [].
Proof.
ltac2:(KReplay.run1 (kr_t_MallocHINV ()) ["AC_2"] "h04pbrkh14resvp;2p;1p;5p;3p;4g0000j28Tg000Pj17Tg0010j10Tg001hj21Tg002aj26Tg003`j12Tg004@j53Tg005Dj34Tg006Hj45Tg006cR0/80#7p,4RRNDR1#0f1R2'1R3f0'6p,5ACEILR4P1P2P3g007A#2D3g008=A4412C5X00W1o"). Qed.

Lemma brk_link_ps_iff : forall st s, brk_link_ps st s <-> brk_link st (ps_brk s).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocHINV ()) ["AC_2"] "p'0h01Hh11bi001bh23offi013offh33ridi023ridh41sh52sti031xp;1p;4p;2p;3g008Yj19Tg009Pj18Tg00:Ij10Tg00;Aj43Tg00;aj22Tg00<Yj31Tg00=3j25Tg006Hj44Tg00=Lj26Tg002aj27Tg00>Lg00?Hf1R0#9#8g00@BR1P1P1p-0f0R1g00A@R2P2g006cR3f4#0f5R4g00A\R5P3P0P1C3R6'231n011030003000020102101R7/57P1P2\2R7P7g008=X02R2P2C4R2P2%04f6R4/26513R6%04f7P5P3f2P0C3'2513[R4P4P1X06R6P6C4X23X35P0P1O2n011000003000020102101b11601%01,70'5eW4W5o"). Qed.

End AC_2.
