(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RtCells () := "K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula06I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib5AsanW4AImgEref_find_segment_noneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow8no_imageC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib5AsanW4AImg5asegsC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma no_image_asan : forall s1 s2, 0x60d000 <= s1 -> no_image asegs s1 s2.
Proof.
ltac2:(KReplay.run1 (kr_t_RtCells ()) ["CANSEC1"] "h07__arithh14__ffh24__p1h34__p2h48__varmaph55__with64__x1h74__x2h81Hh92Hzh:2s1h;2s2h<1zp;1p;2p;3p;4p;7p;6p;8g0000j15Tg000Uj10Tg001:j16Tg001Xj22Tg0024j2?Tg002Pj2<Tg002kj1JTg003Kj1ETg003kj1DTg004Ij1CTg004gj1ATg005Rj29Tg0065j2WTg006Wj2VTg0071j2UTg007]j3TTg0087j3NTg008Vj4MTg009Hj1:Tg009gj27Tg00:Pj3;Tg00;9j2ITg00;ej3FTg00<Ej2GTg00<cj4HTg00=Aj2=Tg00=dj7KTg00>Hj1BTg00>jj7LTg00?Nj2OTg00?hj2PTg00@Ej4@Tg00AJj3RTg00BCj4STg00Bnj7ZTg00CRj6YTg00D6j8XTf0R0#0#0#0#0p=1g00DZR1f1R2g00E8P0CSp=4P2g00E_R3g00F>R4P4g00F^R5P0g00G>FZp=3P2P3P4P4P5P0EYp=8f3R6P3P4P4P5f2R7P2P0GXp=>%00#0p=Qg00G^R8#5#0#1#5#5#0#5#1#1#1#6R9/2212601?07'<P2%68R:g00HCR;#JR<%E;R=%D1R>%C1R?%A1R@191:RA/4A'31W@5RAP0P7g00HoRBg00IORC'V1U07=TBCdg00Io=N12CMRCb1b4b512::P0b0p-0RBg00JMRD#:RE#:,71171E171D5;15;1g00Jl'I=F;<P=P11G17P2P>CHP?P@P@P3P4P4P5%08R?,=1R>1=18R8'4,3@f4R=,8@FK%B4R<P@1919R;/4>,3@P<P@P3P4P4P5f5R5,8@14;8,3@FLC>C>PAPCb1b4b5X61X71X2BW31220/<71297R91O59[[^61^71^2B^3BP01P7:%0?#Q#1#1#1#6'21?7=P5P7P2P6O6b0C@W9X<1g00KX?R72eW8X;1X:1o"). Qed.

(* [comment removed for export] *)
End CANSEC1.
Notation rt_got m :=
  (rw_cells asegs m 0xaf718 [C8 (Z_to_bv 64 0x1494a8); C8 (Z_to_bv 64 0xb5178); C8 (Z_to_bv 64 0xb7978);
                              C8 (Z_to_bv 64 0xb8668); C8 (Z_to_bv 64 0xb8670); C8 (Z_to_bv 64 0xb8660)]).
(* [comment removed for export] *)
Notation rt_got_ric m := (rw_cells asegs m 0xb0290 [C8 (Z_to_bv 64 0xb8659)]).
(* [comment removed for export] *)
Notation rt_shbase m := (rw_cells asegs m 0xb7978 [C8 (Z_to_bv 64 0x7fff8000)]).
(* [comment removed for export] *)
Notation rt_inited m := (rw_cells asegs m 0xb8658 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]).
(* [comment removed for export] *)
Notation rt_layout m := (rw_cells asegs m 0xb8660 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
(* [comment removed for export] *)
Notation rt_real_mem m := (rw_cells asegs m 0xb15a0 [C8 (Z_to_bv 64 0xa8a58); C8 (Z_to_bv 64 0xa8e5c)]).
Notation rt_real_wcslen m := (rw_cells asegs m 0xb1550 [C8 (Z_to_bv 64 0xa92e4)]).
Notation rt_real_read m := (rw_cells asegs m 0xb1478 [C8 (Z_to_bv 64 0xae15c)]).
Notation rt_real_printf m := (rw_cells asegs m 0xb1498 [C8 (Z_to_bv 64 0xa83a8); C8 (Z_to_bv 64 0xa5298)]).
