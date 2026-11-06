(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import MallocRep MallocTree.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Export MallocBlocks.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_MallocHINV () := "I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP:secret_valC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5minitC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocBlocks8brk_linkC13~~~K47Corelib4Init9Datatypes4list01I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocBlocks;AREACH_from00C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocBlocks;AREACH_from01C13~~~K47Corelib4Init5Logic3and01I47Corelib7Numbers7BinNums1Z00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocBlocks5blockC13~~~K47Corelib4Init5Logic4True01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc3ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5c_brkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec4Prog6ps_brkC13~~~K47Corelib4Init9Datatypes4prod01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4concC13~~~I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic3iffC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree;brk_link_psC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec4Prog6PState00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8brkstate00C13~~~I47Corelib4Init5Logic4True00I47Corelib7Numbers7BinNums1N00".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
Definition HINV_from (resv : list (Z * Z)) (st : mstate) (pbrk : Z) (LB : list block) : Prop :=
  brk_link st pbrk /\ AREACH_from resv st LB.
(* [comment removed for export] *)

Lemma HINV_from_init : forall resv pbrk, HINV_from resv (minit secret_val resv) pbrk [].
Proof.
ltac2:(KReplay.run1 (kr_t_MallocHINV ()) ["CEIL_WRAP_1"] "h04pbrkh14resvp;2p;1p;4g0000j28Tg000Pj17Tg0010j10Tg002Aj21Tg003Pj26Tg004ij12Tg005Ij43Tg006gj24Tg008Ej45Tg008`R0/80#7p,4RUNpR1#0f1R2'1R3f0'6P1P2P3g009>#2C3g00:T1412C5X00W1o"). Qed.
(* [comment removed for export] *)

Lemma brk_link_ps_iff : forall st s, brk_link_ps st s <-> brk_link st (ps_brk s).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocHINV ()) ["CEIL_WRAP_1"] "p'0h01Hh11bi001bh23offi013offh33ridi023ridh41sh52sti031xp;1p;4p;2p;3g00;0j19Tg00<=j18Tg00=Lj10Tg00>Zj43Tg00?:j22Tg00@Hj31Tg00@bj25Tg008Ej44Tg00A;j26Tg003Pj27Tg00BUg00Cgf1R0#9#8g00E7R1P1P1p-0f0R1g00FKR2P2g008`R3f4#0f5R4g00FgR5P3P0P1C3R6'231n011030003000020102101R7/57P1P2\2R7P7g00:TX02R2P2C4R2P2%04f6R4/26513R6%04f7P5P3f2P0C3'2513[R4P4P1X06R6P6C4X23X35P0P1O2n011000003000020102101b11601%01,70'5eW4W5o"). Qed.
End CEIL_WRAP_1.

