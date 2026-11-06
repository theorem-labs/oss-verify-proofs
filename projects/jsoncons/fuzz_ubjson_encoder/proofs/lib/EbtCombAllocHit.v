(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac
     As0StepLib As0Tables ArtMem ArtAtomics ArtTac EbtClassId EbtCachePop EbtCombAlloc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_EbtCombAllocHit () := "K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic6eq_symI47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init5Logic6eq_indC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9As0Tables7AsanTab8class_idC13~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01". Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Definition art_ca_hit_mem (M : word -> option byte) (sp ra s0 s1 s2 s3 s4 ca c cnt st csz : Z) : word -> option byte :=
  Wn 8 (Wn 4 (art_ca_frame M sp ra s0 s1 s2 s3 s4) (ca + 80 * c) (cnt - 1)) (ca + 2576) (st + csz).

(* [comment removed for export] *)
Definition art_ca_kept (r : reg) : Prop :=
  r <> 5%bv /\ r <> 6%bv /\ r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv /\ r <> 15%bv /\ r <> 16%bv /\ r <> 17%bv.

Lemma class_id_small : forall s, 1 <= s <= 512 -> AsanTab.class_id s = (s + 31) / 32.
Proof.
ltac2:(KReplay.run1 (kr_t_EbtCombAllocHit ()) [] "h01Hh14__p1h24__x1h31mh41nh52Hsh67__arithh74__ffh88__varmaph95__with:1bh;1sp;1p;2p;6p;4p;7p;8p;3g0000j13Tg000Nj21Tg000jj10Tg001OR0j29Tg001jj24Tg002Gj2JTg002gj1DTg003Gj1BTg003gj2ATg004Ej1@Tg004cj1>Tg005Nj6=Tg0062j2VTg006Uj2UTg0078j4TTg007cj7OTg008Gj7NTg008kj1LTg009Mj8ITg00:1j2HTg00:Sj2:Tg00:mj2CTg00;Yj3ETg00<8j4FTg00<jj4GTg00=Fj35Tg00=`j16Tg00>Ej22Tg00>bj28Tg00??j1KTg00?]j2?Tg00@:j2;Tg00@Wj2MTg00A7j2<Tg00AWj2PTg00B4j2QTg00BQj6RTg00Bmj1STg00DBR1f0R2g00DbR335p=7g00EBR4g00E`R5#3R6/12%05R7#0#0#0#0R8#0#0#0#0#3R9,12R:'9P1f1R;/49R<P3P014;2#7f2R0/1;R=[11;2140;#7[R>f3R?/40#7\=1J;2P2n2001000000120000000X34X44P>^34^44P2P0P9p-0R>g00FER=#D%B=1A4;%@4%>4R=g00G1R@g00GPRAPAg00H0RBP=P@PAPAPBP=P@PAPAPBP?E=P=P@PAPAPBP41V45g00HP1U49CTg00I7FOR@FN%LAP@GI1H=BP2P01:131C20#7dg00IWRB=E4;CFb7b8b9X24W119;:11;9[^24^1>P2116?P?P0O3b6O3b0CGA513<P1P3P1P4P2%65#6#6#6#3R5,2?%38R8'8R3%37R7%K?R<'?/;71;<6R<,M?/<7'2P1P41P7<,<?/QBPBP6n0100000020000'2n0100000020000=543X:11205/88,:41409P2ERb0%S;12;5/88554eW5W;o"). Qed.

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
End FPX.
