(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac.AsCodeM0.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= hs_am_lia.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation LE2 z := (word_to_le_bytes 2 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition al2_words : list (option (bv 32)) :=
  [Some W_4bdbc; Some W_4bdc0; Some W_4bdc4; Some W_4bdc8; Some W_4bdcc; Some W_4bdd0; Some W_4bdd4; Some W_4bdd8;
   Some W_4bddc; Some W_4bde0; Some W_4bde4; Some W_4bde8; Some W_4bdec; Some W_4bdf0; Some W_4bdf4; Some W_4bdf8;
   Some W_4bdfc; Some W_4be00; Some W_4be04; Some W_4be08; Some W_4be0c; Some W_4be10; Some W_4be14; Some W_4be18;
   Some W_4be1c; Some W_4be20; Some W_4be24; Some W_4be28; Some W_4be2c; Some W_4be30; Some W_4be34; Some W_4be38;
   Some W_4be3c; Some W_4be40; Some W_4be44; Some W_4be48; Some W_4be4c; Some W_4be50; Some W_4be54; Some W_4be58;
   Some W_4be5c; Some W_4be60; Some W_4be64; Some W_4be68; Some W_4be6c; Some W_4be70; Some W_4be74; Some W_4be78;
   Some W_4be7c; Some W_4be80; Some W_4be84; Some W_4be88; Some W_4be8c; Some W_4be90; Some W_4be94; Some W_4be98;
   Some W_4be9c; Some W_4bea0; Some W_4bea4; Some W_4bea8; Some W_4beac; Some W_4beb0; Some W_4beb4; Some W_4beb8;
   Some W_4bebc; Some W_4bec0; Some W_4bec4; Some W_4bec8; Some W_4becc; Some W_4bed0; Some W_4bed4; Some W_4bed8;
   None; None; Some W_4bee4; Some W_4bee8; Some W_4beec; Some W_4bef0; Some W_4bef4; Some W_4bef8; Some W_4befc;
   Some W_4bf00; Some W_4bf04; Some W_4bf08; Some W_4bf0c; Some W_4bf10; Some W_4bf14; Some W_4bf18; Some W_4bf1c;
   Some W_4bf20; Some W_4bf24; Some W_4bf28; Some W_4bf2c; Some W_4bf30; Some W_4bf34; Some W_4bf38; Some W_4bf3c;
   Some W_4bf40; Some W_4bf44; Some W_4bf48; Some W_4bf4c; Some W_4bf50; Some W_4bf54; Some W_4bf58; Some W_4bf5c;
   Some W_4bf60; Some W_4bf64; Some W_4bf68; Some W_4bf6c; Some W_4bf70; Some W_4bf74; Some W_4bf78; Some W_4bf7c;
   Some W_4bf80; Some W_4bf84; Some W_4bf88; Some W_4bf8c; Some W_4bf90; Some W_4bf94; Some W_4bf98; Some W_4bf9c;
   Some W_4bfa0; Some W_4bfa4; Some W_4bfa8; Some W_4bfac; Some W_4bfb0; Some W_4bfb4; Some W_4bfb8; Some W_4bfbc;
   Some W_4bfc0; Some W_4bfc4; Some W_4bfc8; Some W_4bfcc; Some W_4bfd0; Some W_4bfd4; Some W_4bfd8; Some W_4bfdc;
   None; None; Some W_4bfe8; Some W_4bfec; Some W_4bff0; Some W_4bff4; Some W_4bff8; Some W_4bffc; Some W_4c000;
   None; None; None; None; Some W_4c014; Some W_4c018; Some W_4c01c; Some W_4c020; Some W_4c024; None; None;
   Some W_4c030; Some W_4c034; Some W_4c038; Some W_4c03c; Some W_4c040; None; None; Some W_4c04c; Some W_4c050;
   Some W_4c054; Some W_4c058; Some W_4c05c; Some W_4c060; Some W_4c064; Some W_4c068; Some W_4c06c; Some W_4c070;
   Some W_4c074; Some W_4c078; Some W_4c07c; Some W_4c080; Some W_4c084; Some W_4c088; Some W_4c08c; Some W_4c090;
   Some W_4c094; Some W_4c098; Some W_4c09c; Some W_4c0a0; Some W_4c0a4; Some W_4c0a8; Some W_4c0ac; Some W_4c0b0;
   Some W_4c0b4; Some W_4c0b8; Some W_4c0bc; Some W_4c0c0; Some W_4c0c4; Some W_4c0c8; Some W_4c0cc; Some W_4c0d0;
   Some W_4c0d4; Some W_4c0d8; Some W_4c0dc; Some W_4c0e0; Some W_4c0e4; Some W_4c0e8; Some W_4c0ec; Some W_4c0f0;
   Some W_4c0f4; Some W_4c0f8; Some W_4c0fc; Some W_4c100; Some W_4c104; Some W_4c108; Some W_4c10c; Some W_4c110;
   Some W_4c114; Some W_4c118; Some W_4c11c; Some W_4c120; Some W_4c124; Some W_4c128; Some W_4c12c; Some W_4c130;
   Some W_4c134; Some W_4c138; Some W_4c13c; Some W_4c140; Some W_4c144; Some W_4c148; Some W_4c14c; Some W_4c150;
   Some W_4c154; Some W_4c158; Some W_4c15c; Some W_4c160; Some W_4c164; Some W_4c168; Some W_4c16c; Some W_4c170;
   Some W_4c174; Some W_4c178; Some W_4c17c; Some W_4c180; Some W_4c184; Some W_4c188; Some W_4c18c; Some W_4c190;
   Some W_4c194; Some W_4c198; Some W_4c19c; Some W_4c1a0; Some W_4c1a4; Some W_4c1a8; Some W_4c1ac; Some W_4c1b0;
   Some W_4c1b4; Some W_4c1b8; Some W_4c1bc; Some W_4c1c0; Some W_4c1c4; None; None; Some W_4c1d0; Some W_4c1d4;
   Some W_4c1d8; Some W_4c1dc; Some W_4c1e0; None; None; Some W_4c1ec; Some W_4c1f0; Some W_4c1f4; Some W_4c1f8;
   Some W_4c1fc; Some W_4c200; Some W_4c204; Some W_4c208; Some W_4c20c; Some W_4c210; Some W_4c214; Some W_4c218;
   Some W_4c21c; Some W_4c220; Some W_4c224; Some W_4c228; Some W_4c22c; None; None; Some W_4c238; Some W_4c23c;
   Some W_4c240; Some W_4c244; Some W_4c248; Some W_4c24c; Some W_4c250; Some W_4c254; Some W_4c258; Some W_4c25c;
   Some W_4c260; Some W_4c264; Some W_4c268; Some W_4c26c; Some W_4c270; Some W_4c274; Some W_4c278; Some W_4c27c;
   Some W_4c280; Some W_4c284; Some W_4c288; Some W_4c28c]%list.

(* [comment removed for export] *)
Definition hb0w (b : word) : word := v_or (v_andi b (-4)) (Z_to_bv 64 1).
Definition hb1w (b : word) : word := v_or (v_andi (hb0w b) 143) (Z_to_bv 64 16).


Local Set Warnings "-abstract-large-number".


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma mod16_sum8 : forall a b, (a mod 16 = 0)%Z -> (b mod 16 = 0)%Z -> ((a + b) mod 8 = 0)%Z.
Proof using. intros a b Ha Hb. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section AMC.
  Variable segs : list Segment.
  Variable rb : word.
  Hypothesis HAL2 : code_ato segs rb 0x4bdc4 al2_words.
  Hypothesis RB : (U rb mod 2 = 0)%Z /\ (U rb + 2 ^ 24 < 2 ^ 64)%Z.

  Lemma K66cf8 : fetch_word segs (at_ rb 0x4bdc4) = Some W_4bdbc.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 0 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66cfc : fetch_word segs (at_ rb 0x4bdc8) = Some W_4bdc0.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 1 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66d00 : fetch_word segs (at_ rb 0x4bdcc) = Some W_4bdc4.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 2 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66d04 : fetch_word segs (at_ rb 0x4bdd0) = Some W_4bdc8.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 3 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66d08 : fetch_word segs (at_ rb 0x4bdd4) = Some W_4bdcc.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 4 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66d0c : fetch_word segs (at_ rb 0x4bdd8) = Some W_4bdd0.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 5 _ HAL2 eq_refl). Qed.

   (* [comment removed for export] *)
  Lemma K66d18 : fetch_word segs (at_ rb 0x4bde4) = Some W_4bddc.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 8 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66d1c : fetch_word segs (at_ rb 0x4bde8) = Some W_4bde0.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 9 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66d20 : fetch_word segs (at_ rb 0x4bdec) = Some W_4bde4.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 10 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66d24 : fetch_word segs (at_ rb 0x4bdf0) = Some W_4bde8.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 11 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66d28 : fetch_word segs (at_ rb 0x4bdf4) = Some W_4bdec.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 12 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66d2c : fetch_word segs (at_ rb 0x4bdf8) = Some W_4bdf0.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 13 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66d30 : fetch_word segs (at_ rb 0x4bdfc) = Some W_4bdf4.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 14 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66d34 : fetch_word segs (at_ rb 0x4be00) = Some W_4bdf8.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 15 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66d38 : fetch_word segs (at_ rb 0x4be04) = Some W_4bdfc.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 16 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66d3c : fetch_word segs (at_ rb 0x4be08) = Some W_4be00.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 17 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66d40 : fetch_word segs (at_ rb 0x4be0c) = Some W_4be04.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 18 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66d44 : fetch_word segs (at_ rb 0x4be10) = Some W_4be08.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 19 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66d48 : fetch_word segs (at_ rb 0x4be14) = Some W_4be0c.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 20 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66d4c : fetch_word segs (at_ rb 0x4be18) = Some W_4be10.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 21 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66d50 : fetch_word segs (at_ rb 0x4be1c) = Some W_4be14.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 22 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66d54 : fetch_word segs (at_ rb 0x4be20) = Some W_4be18.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 23 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66d58 : fetch_word segs (at_ rb 0x4be24) = Some W_4be1c.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 24 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66d5c : fetch_word segs (at_ rb 0x4be28) = Some W_4be20.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 25 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66d60 : fetch_word segs (at_ rb 0x4be2c) = Some W_4be24.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 26 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66d64 : fetch_word segs (at_ rb 0x4be30) = Some W_4be28.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 27 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66d68 : fetch_word segs (at_ rb 0x4be34) = Some W_4be2c.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 28 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66d6c : fetch_word segs (at_ rb 0x4be38) = Some W_4be30.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 29 _ HAL2 eq_refl). Qed.

































   (* [comment removed for export] *)
  Lemma K66df8 : fetch_word segs (at_ rb 0x4bec4) = Some W_4bebc.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 64 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66dfc : fetch_word segs (at_ rb 0x4bec8) = Some W_4bec0.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 65 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66e00 : fetch_word segs (at_ rb 0x4becc) = Some W_4bec4.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 66 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66e04 : fetch_word segs (at_ rb 0x4bed0) = Some W_4bec8.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 67 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66e08 : fetch_word segs (at_ rb 0x4bed4) = Some W_4becc.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 68 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66e0c : fetch_word segs (at_ rb 0x4bed8) = Some W_4bed0.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 69 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66e10 : fetch_word segs (at_ rb 0x4bedc) = Some W_4bed4.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 70 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66e14 : fetch_word segs (at_ rb 0x4bee0) = Some W_4bed8.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 71 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66e20 : fetch_word segs (at_ rb 0x4beec) = Some W_4bee4.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 74 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66e24 : fetch_word segs (at_ rb 0x4bef0) = Some W_4bee8.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 75 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66e28 : fetch_word segs (at_ rb 0x4bef4) = Some W_4beec.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 76 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66e2c : fetch_word segs (at_ rb 0x4bef8) = Some W_4bef0.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 77 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66e30 : fetch_word segs (at_ rb 0x4befc) = Some W_4bef4.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 78 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66e34 : fetch_word segs (at_ rb 0x4bf00) = Some W_4bef8.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 79 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66e38 : fetch_word segs (at_ rb 0x4bf04) = Some W_4befc.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 80 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66e3c : fetch_word segs (at_ rb 0x4bf08) = Some W_4bf00.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 81 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66e40 : fetch_word segs (at_ rb 0x4bf0c) = Some W_4bf04.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 82 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66e44 : fetch_word segs (at_ rb 0x4bf10) = Some W_4bf08.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 83 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66e48 : fetch_word segs (at_ rb 0x4bf14) = Some W_4bf0c.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 84 _ HAL2 eq_refl). Qed.








   (* [comment removed for export] *)
  Lemma K66e70 : fetch_word segs (at_ rb 0x4bf3c) = Some W_4bf34.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 94 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66e74 : fetch_word segs (at_ rb 0x4bf40) = Some W_4bf38.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 95 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66e78 : fetch_word segs (at_ rb 0x4bf44) = Some W_4bf3c.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 96 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66e7c : fetch_word segs (at_ rb 0x4bf48) = Some W_4bf40.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 97 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66e80 : fetch_word segs (at_ rb 0x4bf4c) = Some W_4bf44.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 98 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66e84 : fetch_word segs (at_ rb 0x4bf50) = Some W_4bf48.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 99 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66e88 : fetch_word segs (at_ rb 0x4bf54) = Some W_4bf4c.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 100 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66e8c : fetch_word segs (at_ rb 0x4bf58) = Some W_4bf50.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 101 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66e90 : fetch_word segs (at_ rb 0x4bf5c) = Some W_4bf54.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 102 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66e94 : fetch_word segs (at_ rb 0x4bf60) = Some W_4bf58.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 103 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66e98 : fetch_word segs (at_ rb 0x4bf64) = Some W_4bf5c.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 104 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66e9c : fetch_word segs (at_ rb 0x4bf68) = Some W_4bf60.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 105 _ HAL2 eq_refl). Qed.








   (* [comment removed for export] *)
  Lemma K66ec4 : fetch_word segs (at_ rb 0x4bf90) = Some W_4bf88.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 115 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66ec8 : fetch_word segs (at_ rb 0x4bf94) = Some W_4bf8c.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 116 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66ecc : fetch_word segs (at_ rb 0x4bf98) = Some W_4bf90.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 117 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66ed0 : fetch_word segs (at_ rb 0x4bf9c) = Some W_4bf94.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 118 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66ed4 : fetch_word segs (at_ rb 0x4bfa0) = Some W_4bf98.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 119 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66ed8 : fetch_word segs (at_ rb 0x4bfa4) = Some W_4bf9c.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 120 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66edc : fetch_word segs (at_ rb 0x4bfa8) = Some W_4bfa0.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 121 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66ee0 : fetch_word segs (at_ rb 0x4bfac) = Some W_4bfa4.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 122 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66ee4 : fetch_word segs (at_ rb 0x4bfb0) = Some W_4bfa8.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 123 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66ee8 : fetch_word segs (at_ rb 0x4bfb4) = Some W_4bfac.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 124 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66eec : fetch_word segs (at_ rb 0x4bfb8) = Some W_4bfb0.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 125 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66ef0 : fetch_word segs (at_ rb 0x4bfbc) = Some W_4bfb4.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 126 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66ef4 : fetch_word segs (at_ rb 0x4bfc0) = Some W_4bfb8.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 127 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66ef8 : fetch_word segs (at_ rb 0x4bfc4) = Some W_4bfbc.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 128 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66efc : fetch_word segs (at_ rb 0x4bfc8) = Some W_4bfc0.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 129 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66f00 : fetch_word segs (at_ rb 0x4bfcc) = Some W_4bfc4.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 130 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66f04 : fetch_word segs (at_ rb 0x4bfd0) = Some W_4bfc8.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 131 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66f08 : fetch_word segs (at_ rb 0x4bfd4) = Some W_4bfcc.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 132 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66f0c : fetch_word segs (at_ rb 0x4bfd8) = Some W_4bfd0.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 133 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66f10 : fetch_word segs (at_ rb 0x4bfdc) = Some W_4bfd4.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 134 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66f14 : fetch_word segs (at_ rb 0x4bfe0) = Some W_4bfd8.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 135 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66f18 : fetch_word segs (at_ rb 0x4bfe4) = Some W_4bfdc.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 136 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66f24 : fetch_word segs (at_ rb 0x4bff0) = Some W_4bfe8.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 139 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66f28 : fetch_word segs (at_ rb 0x4bff4) = Some W_4bfec.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 140 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66f2c : fetch_word segs (at_ rb 0x4bff8) = Some W_4bff0.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 141 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66f30 : fetch_word segs (at_ rb 0x4bffc) = Some W_4bff4.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 142 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66f34 : fetch_word segs (at_ rb 0x4c000) = Some W_4bff8.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 143 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66f38 : fetch_word segs (at_ rb 0x4c004) = Some W_4bffc.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 144 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66f3c : fetch_word segs (at_ rb 0x4c008) = Some W_4c000.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 145 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66f50 : fetch_word segs (at_ rb 0x4c01c) = Some W_4c014.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 150 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66f54 : fetch_word segs (at_ rb 0x4c020) = Some W_4c018.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 151 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66f58 : fetch_word segs (at_ rb 0x4c024) = Some W_4c01c.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 152 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66f5c : fetch_word segs (at_ rb 0x4c028) = Some W_4c020.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 153 _ HAL2 eq_refl). Qed.
   (* [comment removed for export] *)
  Lemma K66f6c : fetch_word segs (at_ rb 0x4c038) = Some W_4c030.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 157 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66f70 : fetch_word segs (at_ rb 0x4c03c) = Some W_4c034.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 158 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66f74 : fetch_word segs (at_ rb 0x4c040) = Some W_4c038.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 159 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66f78 : fetch_word segs (at_ rb 0x4c044) = Some W_4c03c.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 160 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66f7c : fetch_word segs (at_ rb 0x4c048) = Some W_4c040.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 161 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66f88 : fetch_word segs (at_ rb 0x4c054) = Some W_4c04c.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 164 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66f8c : fetch_word segs (at_ rb 0x4c058) = Some W_4c050.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 165 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66f90 : fetch_word segs (at_ rb 0x4c05c) = Some W_4c054.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 166 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66f94 : fetch_word segs (at_ rb 0x4c060) = Some W_4c058.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 167 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66f98 : fetch_word segs (at_ rb 0x4c064) = Some W_4c05c.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 168 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66f9c : fetch_word segs (at_ rb 0x4c068) = Some W_4c060.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 169 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66fa0 : fetch_word segs (at_ rb 0x4c06c) = Some W_4c064.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 170 _ HAL2 eq_refl). Qed.
   (* [comment removed for export] *)
  Lemma K66fa8 : fetch_word segs (at_ rb 0x4c074) = Some W_4c06c.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 172 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66fac : fetch_word segs (at_ rb 0x4c078) = Some W_4c070.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 173 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66fb0 : fetch_word segs (at_ rb 0x4c07c) = Some W_4c074.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 174 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66fb4 : fetch_word segs (at_ rb 0x4c080) = Some W_4c078.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 175 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66fb8 : fetch_word segs (at_ rb 0x4c084) = Some W_4c07c.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 176 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66fbc : fetch_word segs (at_ rb 0x4c088) = Some W_4c080.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 177 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66fc0 : fetch_word segs (at_ rb 0x4c08c) = Some W_4c084.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 178 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66fc4 : fetch_word segs (at_ rb 0x4c090) = Some W_4c088.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 179 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66fc8 : fetch_word segs (at_ rb 0x4c094) = Some W_4c08c.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 180 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66fcc : fetch_word segs (at_ rb 0x4c098) = Some W_4c090.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 181 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66fd0 : fetch_word segs (at_ rb 0x4c09c) = Some W_4c094.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 182 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66fd4 : fetch_word segs (at_ rb 0x4c0a0) = Some W_4c098.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 183 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66fd8 : fetch_word segs (at_ rb 0x4c0a4) = Some W_4c09c.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 184 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66fdc : fetch_word segs (at_ rb 0x4c0a8) = Some W_4c0a0.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 185 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66fe0 : fetch_word segs (at_ rb 0x4c0ac) = Some W_4c0a4.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 186 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66fe4 : fetch_word segs (at_ rb 0x4c0b0) = Some W_4c0a8.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 187 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66fe8 : fetch_word segs (at_ rb 0x4c0b4) = Some W_4c0ac.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 188 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66fec : fetch_word segs (at_ rb 0x4c0b8) = Some W_4c0b0.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 189 _ HAL2 eq_refl). Qed.
   (* [comment removed for export] *)
  Lemma K66ff4 : fetch_word segs (at_ rb 0x4c0c0) = Some W_4c0b8.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 191 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66ff8 : fetch_word segs (at_ rb 0x4c0c4) = Some W_4c0bc.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 192 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K66ffc : fetch_word segs (at_ rb 0x4c0c8) = Some W_4c0c0.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 193 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67000 : fetch_word segs (at_ rb 0x4c0cc) = Some W_4c0c4.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 194 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67004 : fetch_word segs (at_ rb 0x4c0d0) = Some W_4c0c8.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 195 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67008 : fetch_word segs (at_ rb 0x4c0d4) = Some W_4c0cc.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 196 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K6700c : fetch_word segs (at_ rb 0x4c0d8) = Some W_4c0d0.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 197 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67010 : fetch_word segs (at_ rb 0x4c0dc) = Some W_4c0d4.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 198 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67014 : fetch_word segs (at_ rb 0x4c0e0) = Some W_4c0d8.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 199 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67018 : fetch_word segs (at_ rb 0x4c0e4) = Some W_4c0dc.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 200 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K6701c : fetch_word segs (at_ rb 0x4c0e8) = Some W_4c0e0.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 201 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67020 : fetch_word segs (at_ rb 0x4c0ec) = Some W_4c0e4.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 202 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67024 : fetch_word segs (at_ rb 0x4c0f0) = Some W_4c0e8.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 203 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67028 : fetch_word segs (at_ rb 0x4c0f4) = Some W_4c0ec.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 204 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K6702c : fetch_word segs (at_ rb 0x4c0f8) = Some W_4c0f0.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 205 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67030 : fetch_word segs (at_ rb 0x4c0fc) = Some W_4c0f4.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 206 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67034 : fetch_word segs (at_ rb 0x4c100) = Some W_4c0f8.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 207 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67038 : fetch_word segs (at_ rb 0x4c104) = Some W_4c0fc.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 208 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K6703c : fetch_word segs (at_ rb 0x4c108) = Some W_4c100.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 209 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67040 : fetch_word segs (at_ rb 0x4c10c) = Some W_4c104.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 210 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67044 : fetch_word segs (at_ rb 0x4c110) = Some W_4c108.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 211 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67048 : fetch_word segs (at_ rb 0x4c114) = Some W_4c10c.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 212 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K6704c : fetch_word segs (at_ rb 0x4c118) = Some W_4c110.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 213 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67050 : fetch_word segs (at_ rb 0x4c11c) = Some W_4c114.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 214 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67054 : fetch_word segs (at_ rb 0x4c120) = Some W_4c118.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 215 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67058 : fetch_word segs (at_ rb 0x4c124) = Some W_4c11c.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 216 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K6705c : fetch_word segs (at_ rb 0x4c128) = Some W_4c120.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 217 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67060 : fetch_word segs (at_ rb 0x4c12c) = Some W_4c124.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 218 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67064 : fetch_word segs (at_ rb 0x4c130) = Some W_4c128.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 219 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67068 : fetch_word segs (at_ rb 0x4c134) = Some W_4c12c.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 220 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K6706c : fetch_word segs (at_ rb 0x4c138) = Some W_4c130.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 221 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67070 : fetch_word segs (at_ rb 0x4c13c) = Some W_4c134.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 222 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67074 : fetch_word segs (at_ rb 0x4c140) = Some W_4c138.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 223 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67078 : fetch_word segs (at_ rb 0x4c144) = Some W_4c13c.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 224 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K6707c : fetch_word segs (at_ rb 0x4c148) = Some W_4c140.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 225 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67080 : fetch_word segs (at_ rb 0x4c14c) = Some W_4c144.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 226 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67084 : fetch_word segs (at_ rb 0x4c150) = Some W_4c148.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 227 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67088 : fetch_word segs (at_ rb 0x4c154) = Some W_4c14c.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 228 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K6708c : fetch_word segs (at_ rb 0x4c158) = Some W_4c150.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 229 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67090 : fetch_word segs (at_ rb 0x4c15c) = Some W_4c154.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 230 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67094 : fetch_word segs (at_ rb 0x4c160) = Some W_4c158.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 231 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67098 : fetch_word segs (at_ rb 0x4c164) = Some W_4c15c.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 232 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K6709c : fetch_word segs (at_ rb 0x4c168) = Some W_4c160.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 233 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K670a0 : fetch_word segs (at_ rb 0x4c16c) = Some W_4c164.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 234 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K670a4 : fetch_word segs (at_ rb 0x4c170) = Some W_4c168.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 235 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K670a8 : fetch_word segs (at_ rb 0x4c174) = Some W_4c16c.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 236 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K670ac : fetch_word segs (at_ rb 0x4c178) = Some W_4c170.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 237 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K670b0 : fetch_word segs (at_ rb 0x4c17c) = Some W_4c174.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 238 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K670b4 : fetch_word segs (at_ rb 0x4c180) = Some W_4c178.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 239 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K670b8 : fetch_word segs (at_ rb 0x4c184) = Some W_4c17c.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 240 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K670bc : fetch_word segs (at_ rb 0x4c188) = Some W_4c180.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 241 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K670c0 : fetch_word segs (at_ rb 0x4c18c) = Some W_4c184.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 242 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K670c4 : fetch_word segs (at_ rb 0x4c190) = Some W_4c188.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 243 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K670c8 : fetch_word segs (at_ rb 0x4c194) = Some W_4c18c.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 244 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K670cc : fetch_word segs (at_ rb 0x4c198) = Some W_4c190.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 245 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K670d0 : fetch_word segs (at_ rb 0x4c19c) = Some W_4c194.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 246 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K670d4 : fetch_word segs (at_ rb 0x4c1a0) = Some W_4c198.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 247 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K670d8 : fetch_word segs (at_ rb 0x4c1a4) = Some W_4c19c.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 248 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K670dc : fetch_word segs (at_ rb 0x4c1a8) = Some W_4c1a0.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 249 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K670e0 : fetch_word segs (at_ rb 0x4c1ac) = Some W_4c1a4.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 250 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K670e4 : fetch_word segs (at_ rb 0x4c1b0) = Some W_4c1a8.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 251 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K670e8 : fetch_word segs (at_ rb 0x4c1b4) = Some W_4c1ac.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 252 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K670ec : fetch_word segs (at_ rb 0x4c1b8) = Some W_4c1b0.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 253 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K670f0 : fetch_word segs (at_ rb 0x4c1bc) = Some W_4c1b4.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 254 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K670f4 : fetch_word segs (at_ rb 0x4c1c0) = Some W_4c1b8.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 255 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K670f8 : fetch_word segs (at_ rb 0x4c1c4) = Some W_4c1bc.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 256 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K670fc : fetch_word segs (at_ rb 0x4c1c8) = Some W_4c1c0.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 257 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67100 : fetch_word segs (at_ rb 0x4c1cc) = Some W_4c1c4.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 258 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K6710c : fetch_word segs (at_ rb 0x4c1d8) = Some W_4c1d0.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 261 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67110 : fetch_word segs (at_ rb 0x4c1dc) = Some W_4c1d4.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 262 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67114 : fetch_word segs (at_ rb 0x4c1e0) = Some W_4c1d8.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 263 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67118 : fetch_word segs (at_ rb 0x4c1e4) = Some W_4c1dc.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 264 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K6711c : fetch_word segs (at_ rb 0x4c1e8) = Some W_4c1e0.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 265 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67128 : fetch_word segs (at_ rb 0x4c1f4) = Some W_4c1ec.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 268 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K6712c : fetch_word segs (at_ rb 0x4c1f8) = Some W_4c1f0.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 269 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67130 : fetch_word segs (at_ rb 0x4c1fc) = Some W_4c1f4.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 270 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67134 : fetch_word segs (at_ rb 0x4c200) = Some W_4c1f8.  Proof using HAL2. exact (code_ato_get segs rb 0x4bdc4 al2_words 271 _ HAL2 eq_refl). Qed.


































   (* [comment removed for export] *)


  Variables (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (sp m stk thr ctx tr szw : word) (bsz : list byte) (b1 : byte) (n tid : Z).
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H8 : getr regs 8 = Z_to_bv 64 1.
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 n.
  Hypothesis H10 : getr regs 10 = m.
  Hypothesis H19 : getr regs 19 = Z_to_bv 64 (needed n).
  Hypothesis H20 : getr regs 20 = Z_to_bv 64 (rz n).
  Hypothesis H21 : getr regs 21 = Z_to_bv 64 n.
  Hypothesis H23 : getr regs 23 = stk.
  Hypothesis H25 : getr regs 25 = Z_to_bv 64 7.
  Hypothesis H26 : getr regs 26 = thr.
  Hypothesis H27 : getr regs 27 = Z_to_bv 64 1.
  Hypothesis Hn : (1 <= n <= 64512)%Z.
  Hypothesis Htid : (0 <= tid < 2 ^ 31)%Z.
  Hypothesis Gm : (U m mod 16 = 0)%Z /\ (0x10007fff8000 <= U m)%Z /\ (U m + 2 ^ 17 <= 2 ^ 47)%Z.   (* [comment removed for export] *)
  Hypothesis Gsp : (2 ^ 32 <= U sp)%Z /\ (U sp + 144 <= 2 ^ 47)%Z.
  (* [comment removed for export] *)
  Hypothesis Gthr : (4096 <= U thr /\ hideW (U thr + 4096 <= AIMGLO \/ AIMGHI <= U thr))%Z /\ (U thr + 4096 <= 2 ^ 64)%Z.   (* [comment removed for export] *)
  Hypothesis Gctx : (U ctx + 16 <= 2 ^ 64)%Z.
  Hypothesis Gstk : (U stk + 16 <= 2 ^ 64)%Z.
  (* [comment removed for export] *)
  Hypothesis Rb1 : rdn segs mem (at_ m (rz n - 15)) 1 = Some [b1].
  Hypothesis SOKh : store_ok segs mem (at_ m (rz n - 16)) 16 = true.
  Hypothesis R16 : rdn segs mem (at_ sp 16) 8 = Some (LE8 (Z_to_bv 64 16)).
  Hypothesis Rctx : rdn segs mem thr 8 = Some (LE8 ctx).
  Hypothesis Rtid : rdn segs mem (at_ ctx 8) 4 = Some (LE4 tid).
  Hypothesis Rtr : rdn segs mem stk 8 = Some (LE8 tr).
  Hypothesis Rsz : rdn segs mem (at_ stk 8) 8 = Some bsz.
  Hypothesis Hbsz : bytes_le_to_Z bsz = U szw /\ length bsz = 8%nat.
  Hypothesis Dsp : (U m + rz n <= U sp + 16 \/ U sp + 24 <= U m + rz n - 16)%Z.
  Hypothesis Dthr : (U m + rz n <= U thr \/ U thr + 8 <= U m + rz n - 16)%Z.
  Hypothesis Dctx : (U m + rz n <= U ctx + 8 \/ U ctx + 12 <= U m + rz n - 16)%Z.
  Hypothesis Dstk : (U m + rz n <= U stk \/ U stk + 16 <= U m + rz n - 16)%Z.

  #[local] Abbreviation CLC := (fun r => In r (18 :: 20 :: 21 :: 24 :: 25 :: 1 :: 5 :: 6 :: 10 :: 11 :: 12 :: 13 :: 14 :: 15 :: 16 :: 17 :: nil)).

  Definition amC_mem : word -> option byte :=
    let w1 := hb0w (Z_to_bv 64 (U b1)) in
    wbytes (wbytes (wbytes (wbytes mem (at_ m (rz n - 15)) [Z_to_bv 8 (U w1)]) (at_ m (rz n - 14)) (LE2 0)) (at_ m (rz n - 12)) (LE4 n))
           (at_ m (rz n - 15)) [Z_to_bv 8 (U (hb1w (Z_to_bv 64 (U b1))))].
  Lemma amC_mem_outside : forall x : word, (U x < U m + rz n - 16 \/ U m + rz n <= U x)%Z -> amC_mem x = mem x.
  Proof using Hbsz Gm Hn bsz szw rb.
    intros x Hx. pose proof (u64_range m). destruct Gm as (Gm1 & Gm2 & Gm3). pose proof (rz_log_range n).
    assert (Hrz2 : (16 <= rz n <= 1024)%Z).
    { (lazymatch goal with |- ?G => let G' := eval unfold rz in G in change_no_check G' end). destruct (rz_log_cases n ltac:(lia)) as [[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[C E]]]]]]]]; rewrite E; lia. }
    (lazymatch goal with |- ?G => let G' := eval unfold amC_mem in G in change_no_check G' end). rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite ?at_u; try lia. reflexivity.
  Qed.

  Theorem amC_run :
    exists r,
      msteps segs (mkst regs (at_ rb 0x4bdc4) mem rom) (mkst r (at_ rb 0x8ea80) amC_mem rom)
      /\ getr r 1 = at_ rb 0x4bed0 /\ getr r 10 = tr /\ getr r 11 = szw
      /\ getr r 18 = m /\ getr r 20 = at_ m (rz n) /\ getr r 21 = at_ m (rz n - 16) /\ getr r 24 = Z_to_bv 64 (tid * 2 ^ 32) /\ getr r 25 = at_ m (rz n + n)
      /\ regs_agree CLC regs r.
  Proof using Dstk Dctx Dthr Dsp Hbsz Rsz Rtr Rtid Rctx R16 SOKh Rb1 Gstk Gctx Gthr Gsp Gm Htid Hn H27 H26 H25 H23 H21 H20 H19 H10 H9 H2 bsz ctx thr stk sp HAL2.
    pose proof (u64_range m) as Hmr. pose proof (u64_range sp) as Hspr. pose proof (u64_range thr) as Hthr. pose proof (u64_range ctx) as Hctx.
    pose proof (u64_range stk) as Hstk. pose proof (u8_range b1) as Hb1.
    destruct Gm as (Gm1 & Gm2 & Gm3). destruct Gsp as [Gs1 Gs2]. destruct Gthr as [Gt1 Gt2]. pose proof (rz_log_range n) as HRL.
    assert (Hrz2 : (16 <= rz n <= 1024)%Z).
    { (lazymatch goal with |- ?G => let G' := eval unfold rz in G in change_no_check G' end). destruct (rz_log_cases n ltac:(lia)) as [[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[C E]]]]]]]]; rewrite E; lia. }
    assert (Hrz16 : (rz n mod 16 = 0)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold rz in G in change_no_check G' end); rewrite Z.mul_comm; apply Z_mod_mult).
    destruct (needed_facts n Hn) as [NF1 NF2].
    assert (Hnd : (needed n = rounded n + rz n)%Z) by reflexivity.
    assert (Hrd2 : (Z.max n 8 <= rounded n <= Z.max n 8 + 7)%Z).
    { (lazymatch goal with |- ?G => let G' := eval unfold rounded, RoundUp in G in change_no_check G' end). pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)). lia. }
    set (M1 := wbytes mem (at_ m (rz n - 15)) [Z_to_bv 8 (U (hb0w (Z_to_bv 64 (U b1))))]).
    set (M2 := wbytes M1 (at_ m (rz n - 14)) (LE2 0)).
    set (M3 := wbytes M2 (at_ m (rz n - 12)) (LE4 n)).
    assert (M3_out : forall x : word, (U x < U m + rz n - 16 \/ U m + rz n <= U x)%Z -> M3 x = mem x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M3, M2, M1 in G in change_no_check G' end). rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite ?at_u; try lia. reflexivity. }
    assert (AM_out : forall x : word, (U x < U m + rz n - 16 \/ U m + rz n <= U x)%Z -> amC_mem x = mem x) by exact amC_mem_outside.
    Ltac cellC R OUT := rewrite <- R; apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply OUT; rewrite ?at_u in Hx by lia; cbn in Hx; lia].
    assert (R16' : rdn segs M3 (at_ sp 16) 8 = Some (LE8 (Z_to_bv 64 16))) by cellC R16 M3_out.
    assert (Rctx' : rdn segs amC_mem thr 8 = Some (LE8 ctx)) by cellC Rctx AM_out.
    assert (Rtid' : rdn segs amC_mem (at_ ctx 8) 4 = Some (LE4 tid)) by cellC Rtid AM_out.
    assert (Rtr' : rdn segs amC_mem stk 8 = Some (LE8 tr)) by cellC Rtr AM_out.
    assert (Rsz' : rdn segs amC_mem (at_ stk 8) 8 = Some bsz) by cellC Rsz AM_out.
    Ltac sok SOKh k N := repeat (eapply store_ok_mono; [apply wbytes_grows|]);
      eapply (store_ok_sub segs mem (at_ m (rz n - 16)) _ 16); [rewrite at_u; lia | exact SOKh | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia].
    assert (Hp8 : ((U m + rz n) mod 8 = 0)%Z) by (apply mod16_sum8; [exact Gm1 | exact Hrz16]).
    assert (SOK1 : store_ok segs M1 (at_ m (rz n - 16)) 16 = true) by ((lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); eapply store_ok_mono; [apply wbytes_grows | exact SOKh]).
    assert (SOK2 : store_ok segs M2 (at_ m (rz n - 16)) 16 = true) by ((lazymatch goal with |- ?G => let G' := eval unfold M2 in G in change_no_check G' end); eapply store_ok_mono; [apply wbytes_grows | exact SOK1]).
    assert (SOK3 : store_ok segs M3 (at_ m (rz n - 16)) 16 = true) by ((lazymatch goal with |- ?G => let G' := eval unfold M3 in G in change_no_check G' end); eapply store_ok_mono; [apply wbytes_grows | exact SOK2]).
    Ltac sok16 SOK := eapply (store_ok_sub segs _ (at_ m (rz n - 16)) _ 16); [rewrite at_u; lia | exact SOK | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia].
    Ltac vz := cbv delta [v_add v_addi v_mul v_slli v_srli v_sub] beta; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia; unorm;
               first [reflexivity | f_equal; lia | apply bv_eq; wd_ulia].
    wd_eexists. split.
    - an K66cf8 D_4bdbc.                                   (* [comment removed for export] *)
      ab_ft K66cfc D_4bdc0 ltac:(condz).                  (* [comment removed for export] *)
      av K66d00 D_4bdc4 (at_ m (rz n)) ltac:(rewrite v_add_at by lia; reflexivity).   (* [comment removed for export] *)
      an K66d04 D_4bdc8.                                   (* [comment removed for export] *)
      replace (v_and (at_ m (rz n)) (Z_to_bv 64 7)) with (Z_to_bv 64 0)
        by (symmetry; (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end); unorm; rewrite at_u by lia; f_equal; change 7%Z with (Z.ones 3); rewrite Z.land_ones by lia; exact Hp8).
      av K66d08 D_4bdcc (Z_to_bv 64 (needed n + U m)) ltac:(vz).   (* [comment removed for export] *)
      ab_tk K66d0c D_4bdd0 ltac:(condz).                  (* [comment removed for export] *)
      av K66d18 D_4bddc (at_ m (rz n + n)) ltac:(rewrite v_add_at by lia; rewrite at_at; reflexivity).   (* [comment removed for export] *)
      ab_ft K66d1c D_4bde0 ltac:(condz).                  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lbu with (b := b1); [exact K66d20 | reflexivity | exact D_4bde4
          | gres; rwH; imm_norm; rewrite ?at_addi; rewrite <- Rb1; f_equal; f_equal; lia]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      an K66d24 D_4bde8.                                   (* [comment removed for export] *)
      an K66d28 D_4bdec.                                   (* [comment removed for export] *)
      an K66d2c D_4bdf0.                                   (* [comment removed for export] *)
      change (v_or (v_andi (Z_to_bv 64 (U b1)) (-4)) (Z_to_bv 64 1)) with (hb0w (Z_to_bv 64 (U b1))).
      av K66d30 D_4bdf4 (Z_to_bv 64 0) ltac:(cbv delta [v_srli] beta; rewrite Z.shiftr_div_pow2 by lia; unorm; f_equal; apply Z.div_small; lia).  (* [comment removed for export] *)
      av K66d34 D_4bdf8 (Z_to_bv 64 0) ltac:(cbv delta [v_srli] beta; rewrite Z.shiftr_div_pow2 by lia; unorm; f_equal; apply Z.div_small; lia).  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sb_at with (a := at_ m (rz n - 15)) (b := Z_to_bv 8 (U (hb0w (Z_to_bv 64 (U b1)))));
          [exact K66d38 | reflexivity | exact D_4bdfc | gres; rwH; imm_norm; rewrite ?at_addi; f_equal; lia | gres; rwH; reflexivity | reflexivity | sok16 SOKh]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      change (wbytes mem _ _) with M1.
      chain_step; [reflexivity
        | eapply step_sh_at with (a := at_ m (rz n - 14)) (v := Z_to_bv 64 0);
          [exact K66d3c | reflexivity | exact D_4be00 | gres; rwH; imm_norm; rewrite ?at_addi; f_equal; lia | gres; rwH; reflexivity | sok16 SOK1]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      change (wbytes M1 _ _) with M2.
      chain_step; [reflexivity
        | eapply step_sw_at with (a := at_ m (rz n - 12)) (v := Z_to_bv 64 n);
          [exact K66d40 | reflexivity | exact D_4be04 | gres; rwH; imm_norm; rewrite ?at_addi; f_equal; lia | gres; rwH; reflexivity | sok16 SOK2]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      change (wbytes M2 _ _) with M3.
      ab_ft K66d44 D_4be08 ltac:(condz).                  (* [comment removed for export] *)
      av K66d48 D_4be0c (at_ m (rz n - 16)) ltac:(rewrite at_addi; f_equal; lia).   (* [comment removed for export] *)
      an K66d4c D_4be10.                                   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 (Z_to_bv 64 16)) (v := Z_to_bv 64 16);
          [exact K66d50 | reflexivity | exact D_4be14 | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi; fold_at_vars; exact R16' | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      an K66d54 D_4be18.                                   (* [comment removed for export] *)
      change (v_or (v_andi (hb0w (Z_to_bv 64 (U b1))) 143) (Z_to_bv 64 16)) with (hb1w (Z_to_bv 64 (U b1))).
      chain_step; [reflexivity
        | eapply step_sb_at with (a := at_ m (rz n - 15)) (b := Z_to_bv 8 (U (hb1w (Z_to_bv 64 (U b1)))));
          [exact K66d58 | reflexivity | exact D_4be1c | gres; rwH; imm_norm; rewrite ?at_addi; f_equal; lia | gres; rwH; reflexivity | reflexivity | sok16 SOK3]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      change (wbytes M3 _ _) with amC_mem.
      ab_ft K66d5c D_4be20 ltac:(condz).                  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 ctx) (v := ctx);
          [exact K66d60 | reflexivity | exact D_4be24 | gres; rwH; imm_norm; rewrite ?v_addi_0; exact Rctx' | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 tid)) (v := Z_to_bv 64 tid);
          [exact K66d64 | reflexivity | exact D_4be28 | gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; exact Rtid' | apply bytes4_small; lia]
        | step_simpl]; rewrite (v_lw_small tid) by lia; vn.    (* [comment removed for export] *)
      av K66d68 D_4be2c (Z_to_bv 64 (tid * 2 ^ 32)) ltac:(vz).   (* [comment removed for export] *)
      an K66d6c D_4be30.                                   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 tr) (v := tr);
          [exact K66df8 | reflexivity | exact D_4bebc | gres; rwH; imm_norm; rewrite ?v_addi_0; exact Rtr' | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := bsz) (v := szw);
          [exact K66dfc | reflexivity | exact D_4bec0 | gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; exact Rsz' | exact (proj1 Hbsz)]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      an K66e00 D_4bec4.                                   (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
  (* [comment removed for export] *)
  Lemma land_48m8 : forall x, (0 <= x < 2 ^ 48)%Z -> Z.land x (2 ^ 48 - 8) = (x - x mod 8)%Z.
  Proof using Hbsz Gm bsz szw m rb.
    intros x Hx. apply Z.bits_inj'. intros k Hk.
    rewrite Z.land_spec.
    assert (Em : (2 ^ 48 - 8)%Z = Z.shiftl (2 ^ 45 - 1) 3) by reflexivity. rewrite Em.
    assert (Ex : (x - x mod 8)%Z = Z.shiftl (x / 2 ^ 3) 3).
    { rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z. pose proof (Z.div_mod x 8). lia. }
    rewrite Ex.
    destruct (Z.lt_ge_cases k 3) as [Hl|Hg].
    - rewrite !Z.shiftl_spec_low by lia. apply andb_false_r.
    - rewrite !Z.shiftl_spec_high by lia.
      destruct (Z.lt_ge_cases k 48) as [Hl2|Hg2].
      + assert (Ht : Z.testbit (2 ^ 45 - 1) (k - 3) = true).
        { replace (2 ^ 45 - 1)%Z with (Z.ones 45) by reflexivity. apply Z.ones_spec_low. lia. }
        rewrite Ht, andb_true_r. rewrite Z.div_pow2_bits by lia. f_equal. lia.
      + rewrite (testbit_high 48 x k) by lia.
        rewrite (testbit_high 45 (x / 2 ^ 3) (k - 3)); [reflexivity | lia | | lia].
        change (2 ^ 3)%Z with 8%Z. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
  Qed.

  Variable gSB : Z.                     (* [comment removed for export] *)
  Hypothesis GLSB : gload segs rb 0x4bee4 10 gSB.
  Variables (psb : word) (SB : Z) (sb0 : byte).
  Hypothesis GgSB : (AIMGLO <= gSB /\ gSB + 8 <= AIMGHI)%Z.
  Hypothesis Gpsb : (AIMGLO <= U psb /\ U psb + 8 <= AIMGHI)%Z.
  Hypothesis GSB : (0 < SB <= 0x7fff8000)%Z /\ (SB + U m / 8 + 1 <= 2 ^ 62)%Z.   (* [comment removed for export] *)

  Definition amD_mem (M : word -> option byte) (id : Z) : word -> option byte :=
    wbytes M (at_ m (rz n - 8)) (LE8 (Z_to_bv 64 (tid * 2 ^ 32 + id))).

  Lemma amD1 : forall (M : word -> option byte) r0 (id : Z),
    (0 <= id < 2 ^ 32)%Z ->   (* [comment removed for export] *)
    getr r0 10 = Z_to_bv 64 id -> getr r0 8 = Z_to_bv 64 1 -> getr r0 9 = Z_to_bv 64 n -> getr r0 18 = m -> getr r0 20 = at_ m (rz n) ->
    getr r0 21 = at_ m (rz n - 16) -> getr r0 24 = Z_to_bv 64 (tid * 2 ^ 32) ->
    store_ok segs M (at_ m (rz n - 16)) 16 = true ->
    rdn segs M (Z_to_bv 64 gSB) 8 = Some (LE8 psb) ->
    rdn segs M psb 8 = Some (LE8 (Z_to_bv 64 SB)) ->
    rdn segs M (Z_to_bv 64 (SB + U m / 8)) 1 = Some [sb0] -> U sb0 <> 0%Z ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4bed0) M rom) (mkst r (at_ rb 0x4bfc8) (amD_mem M id) rom)
      /\ getr r 22 = Z_to_bv 64 (n - n mod 8)
      /\ (forall i : reg, In i [2; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27; 4; 3] -> getr r i = getr r0 i)
      /\ regs_agree (fun x => In x [10; 11; 22]) r0 r.
  Proof using GSB Gpsb GgSB GLSB Hbsz Gm Htid Hn bsz szw HAL2.
    intros M r0 id Hid R10 R8 R9 R18 R20 R21 R24 SOK Rg Rp Rs NZ.
    pose proof (u64_range m) as Hmr. destruct Gm as (Gm1 & Gm2 & Gm3). pose proof (rz_log_range n) as HRL. destruct GSB as [GS1 GS2].
    assert (Hrz2 : (16 <= rz n <= 1024)%Z).
    { (lazymatch goal with |- ?G => let G' := eval unfold rz in G in change_no_check G' end). destruct (rz_log_cases n ltac:(lia)) as [[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[C E]]]]]]]]; rewrite E; lia. }
    set (M' := amD_mem M id).
    assert (M'_out : forall x : word, (U x < U m + rz n - 8 \/ U m + rz n <= U x)%Z -> M' x = M x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M', amD_mem in G in change_no_check G' end). rewrite wbytes_outside; [reflexivity | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    Ltac cellD R OUT := rewrite <- R; apply rdn_ext; [rewrite ?at_u by lia; wd_ulia_c | intros x Hx; apply OUT; rewrite ?at_u in Hx by lia; unorm; cbn in Hx; lia].
    assert (Rg' : rdn segs M' (Z_to_bv 64 gSB) 8 = Some (LE8 psb)).
    { rewrite <- Rg. apply rdn_ext; [wd_ulia_c | intros x Hx; apply M'_out; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia]. }
    assert (Rp' : rdn segs M' psb 8 = Some (LE8 (Z_to_bv 64 SB))).
    { rewrite <- Rp. apply rdn_ext; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros x Hx; apply M'_out; cbn in Hx; lia]. }
    assert (Hd8 : (0 <= U m / 8)%Z /\ (SB + U m / 8 < U m)%Z).
    { split; [apply Z.div_pos; lia|]. pose proof (Z.div_mod (U m) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (U m) 8 ltac:(lia)). lia. }
    assert (Rs' : rdn segs M' (Z_to_bv 64 (SB + U m / 8)) 1 = Some [sb0]).
    { rewrite <- Rs. apply rdn_ext; [wd_ulia_c | intros x Hx; apply M'_out; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia]. }
    pose proof (u8_range sb0) as Hsb0.
    wd_eexists. split.
    - av K66e04 D_4bec8 (Z_to_bv 64 (id * 2 ^ 32)) ltac:(vz).            (* [comment removed for export] *)
      av K66e08 D_4becc (Z_to_bv 64 id) ltac:(cbv delta [v_srli] beta; rewrite Z.shiftr_div_pow2 by lia; unorm; f_equal; apply Z.div_mul; lia).  (* [comment removed for export] *)
      an K66e0c D_4bed0.                                                   (* [comment removed for export] *)
      rewrite (v_or_shl (Z_to_bv 64 id) tid 32) by (wd_ulia).
      replace (tid * 2 ^ 32 + U (Z_to_bv 64 id))%Z with (tid * 2 ^ 32 + id)%Z by (unorm; reflexivity).
      chain_step; [reflexivity
        | eapply step_sd_at with (a := at_ m (rz n - 8));
          [exact K66e10 | reflexivity | exact D_4bed4 | gres; rwH; imm_norm; rewrite ?at_addi; f_equal; lia | gres; rwH; reflexivity
          | eapply (store_ok_sub segs _ (at_ m (rz n - 16)) _ 16); [rewrite at_u; lia | exact SOK | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia] ]
        | step_simpl]; vn.                                                 (* [comment removed for export] *)
      change (wbytes M _ _) with M'.
      ab_ft K66e14 D_4bed8 ltac:(condz).                                  (* [comment removed for export] *)
      eapply msteps_trans; [apply (GLSB _ M' rom psb Rg')|]. zlit_at.      (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 (Z_to_bv 64 SB)) (v := Z_to_bv 64 SB);
          [exact K66e20 | reflexivity | exact D_4bee4 | gres; rwH; imm_norm; rewrite ?v_addi_0; exact Rp' | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                                 (* [comment removed for export] *)
      av K66e24 D_4bee8 (Z_to_bv 64 (U m / 8)) ltac:(cbv delta [v_srli] beta; rewrite Z.shiftr_div_pow2 by lia; reflexivity).   (* [comment removed for export] *)
      av K66e28 D_4beec (Z_to_bv 64 (SB + U m / 8)) ltac:(vz).            (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lbu with (b := sb0); [exact K66e2c | reflexivity | exact D_4bef0
          | gres; rwH; imm_norm; rewrite ?v_addi_0; exact Rs']
        | step_simpl]; vn.                                                 (* [comment removed for export] *)
      ab_tk K66e30 D_4bef4 ltac:(condz).                                  (* [comment removed for export] *)
      an K66ef0 D_4bfb4.                                                   (* [comment removed for export] *)
      an K66ef4 D_4bfb8.                                                   (* [comment removed for export] *)
      an K66ef8 D_4bfbc.                                                   (* [comment removed for export] *)
      match goal with |- context [v_and (Z_to_bv 64 n) ?msk] =>
        replace (v_and (Z_to_bv 64 n) msk) with (Z_to_bv 64 (n - n mod 8))
          by (symmetry; (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end); unorm; f_equal; imm_norm; apply land_48m8; lia) end.
      wd_refl.
    - post.
      + intros i Hi; cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [gres; reflexivity|]); destruct Hi.
      + ra_solve.
  Qed.
  (* [comment removed for export] *)
  Lemma amD2z : forall (M : word -> option byte) r0,
    (n < 8)%Z -> getr r0 22 = Z_to_bv 64 (n - n mod 8) ->
    msteps segs (mkst r0 (at_ rb 0x4bfc8) M rom) (mkst r0 (at_ rb 0x4bfdc) M rom).
  Proof using Hbsz Hn bsz szw m HAL2.
    intros M r0 Hn8 R22. assert (E : (n - n mod 8 = 0)%Z) by (rewrite (Z.mod_small n 8) by lia; lia).
    ab_tk K66efc D_4bfc0 ltac:(rewrite E; condz). wd_refl.
  Qed.
  Lemma amD2 : forall (M : word -> option byte) r0,
    (8 <= n)%Z -> getr r0 22 = Z_to_bv 64 (n - n mod 8) -> getr r0 20 = at_ m (rz n) ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4bfc8) M rom) (mkst r (at_ rb 0x6f610) M rom)
      /\ getr r 1 = at_ rb 0x4bfdc /\ getr r 10 = at_ m (rz n) /\ getr r 11 = Z_to_bv 64 (n - n mod 8) /\ getr r 12 = Z_to_bv 64 0
      /\ regs_agree (fun x => In x [1; 10; 11; 12]) r0 r.
  Proof using Hbsz Gm Hn bsz szw HAL2.
    intros M r0 Hn8 R22 R20. pose proof (Z.mod_pos_bound n 8 ltac:(lia)).
    wd_eexists. split.
    - ab_ft K66efc D_4bfc0 ltac:(condz).                  (* [comment removed for export] *)
      an K66f00 D_4bfc4. an K66f04 D_4bfc8. an K66f08 D_4bfcc.   (* [comment removed for export] *)
      an K66f0c D_4bfd0.                                   (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.

  (* [comment removed for export] *)
  Variables (g_cpm gMB gME gHE gFL : Z) (pmb pme phe pfl : word) (midend : word) (pp : byte).
  Hypothesis CPM : code_ato segs rb 0x6f5fc cpm_words.
  Hypothesis GCPM : gloadb segs rb 0x6f5fc 10 g_cpm.
  Hypothesis GLSB2 : gload segs rb 0x4bfe8 10 gSB.
  Hypothesis GLMB : gload segs rb 0x4c00c 12 gMB.
  Hypothesis GLME : gload segs rb 0x4c014 13 gME.
  Hypothesis GLHE : gload segs rb 0x4c030 13 gHE.
  Hypothesis GLFL : gload segs rb 0x4c04c 11 gFL.
  (* [comment removed for export] *)
  Hypothesis Gcells : Forall (fun c => AIMGLO <= c /\ c + 8 <= AIMGHI)%Z [g_cpm; gMB; gME; gHE; gFL] /\ (AIMGLO <= U pmb /\ U pmb + 8 <= AIMGHI)%Z /\ (AIMGLO <= U pme /\ U pme + 8 <= AIMGHI)%Z
                      /\ (AIMGLO <= U phe /\ U phe + 8 <= AIMGHI)%Z /\ (AIMGLO <= U pfl /\ U pfl + 128 <= AIMGHI)%Z.
  Hypothesis Ghi : (0x10007fff8000 <= U m)%Z.          (* [comment removed for export] *)

  Lemma amE1z : forall (M : word -> option byte) r0,
    (n mod 8 = 0)%Z -> getr r0 9 = Z_to_bv 64 n -> getr r0 22 = Z_to_bv 64 (n - n mod 8) ->
    msteps segs (mkst r0 (at_ rb 0x4bfdc) M rom) (mkst r0 (at_ rb 0x4c070) M rom).
  Proof using Hbsz Hn bsz szw m HAL2.
    intros M r0 Hm R9 R22. ab_tk K66f10 D_4bfd4 ltac:(rewrite Hm, Z.sub_0_r; condz). wd_refl.
  Qed.

  Definition amE1_mem (M : word -> option byte) : word -> option byte :=
    wbytes M (Z_to_bv 64 (SB + (U m + rz n + (n - n mod 8)) / 8)) [Z_to_bv 8 (n mod 8)].

  Lemma amE1 : forall (M : word -> option byte) r0,
    (n mod 8 <> 0)%Z -> getr r0 9 = Z_to_bv 64 n -> getr r0 22 = Z_to_bv 64 (n - n mod 8) -> getr r0 20 = at_ m (rz n) ->
    rdn segs M (Z_to_bv 64 g_cpm) 1 = Some [Z_to_bv 8 1] ->
    rdn segs M (Z_to_bv 64 gSB) 8 = Some (LE8 psb) -> rdn segs M psb 8 = Some (LE8 (Z_to_bv 64 SB)) ->
    rdn segs M (Z_to_bv 64 gMB) 8 = Some (LE8 pmb) -> rdn segs M pmb 8 = Some (LE8 (Z_to_bv 64 0)) ->
    rdn segs M (Z_to_bv 64 gME) 8 = Some (LE8 pme) -> rdn segs M pme 8 = Some (LE8 midend) ->
    rdn segs M (Z_to_bv 64 gHE) 8 = Some (LE8 phe) -> rdn segs M phe 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff)) ->
    rdn segs M (Z_to_bv 64 gFL) 8 = Some (LE8 pfl) -> rdn segs M (at_ pfl 85) 1 = Some [Z_to_bv 8 1] ->
    store_ok segs M (Z_to_bv 64 (SB + (U m + rz n + (n - n mod 8)) / 8)) 1 = true ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4bfdc) M rom) (mkst r (at_ rb 0x4c070) (amE1_mem M) rom)
      /\ regs_agree (fun x => In x [22; 1; 10; 11; 12; 13; 14; 15; 16; 17]) r0 r.
  Proof using Gcells GLFL GLHE GLME GLMB GLSB2 GCPM CPM GSB Hbsz Gm Hn bsz szw RB HAL2.
    intros M r0 Hm R9 R22 R20 Rcpm RgSB RSB RgMB RMB RgME RME RgHE RHE RgFL Rpp SOK.
    pose proof (u64_range m) as Hmr. destruct Gm as (Gm1 & Gm2 & Gm3). pose proof (rz_log_range n) as HRL. destruct GSB as [GS1 GS2].
    destruct Gcells as (GC & Gpmb & Gpme & Gphe & Gpfl).
    pose proof (u64_range pmb). pose proof (u64_range pme). pose proof (u64_range phe). pose proof (u64_range pfl). pose proof (u64_range psb).
    assert (Hrz2 : (16 <= rz n <= 1024)%Z).
    { (lazymatch goal with |- ?G => let G' := eval unfold rz in G in change_no_check G' end). destruct (rz_log_cases n ltac:(lia)) as [[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[C E]]]]]]]]; rewrite E; lia. }
    pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Hm8. pose proof (Z.mod_le n 8 ltac:(lia) ltac:(lia)) as Hm9.
    set (e := (U m + rz n + (n - n mod 8))%Z).
    assert (He : (0x10007fff8000 <= e)%Z /\ (e + 8 <= 2 ^ 47)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold e in G in change_no_check G' end); lia).
    assert (Hd : (0 <= e / 8)%Z /\ (SB + e / 8 < 2 ^ 47)%Z /\ (0x10007fff7fff < e)%Z).
    { split; [apply Z.div_pos; lia|]. pose proof (Z.div_mod e 8 ltac:(lia)). pose proof (Z.mod_pos_bound e 8 ltac:(lia)). lia. }
    destruct (cpm_run segs rb g_cpm CPM GCPM M rom (regupd r0 1 (at_ rb 0x4bfe4)) (at_ rb 0x4bfe4) Rcpm) as (r1 & RUN1 & A10 & AG1).
    { apply ret_ok_at; [exact (proj1 RB) | reflexivity | pose proof (u64_range rb); pose proof (proj2 RB); lia]. }
    { gres. reflexivity. }
    assert (B20 : getr r1 20 = at_ m (rz n)) by (rewrite (AG1 20) by notin_list; gres; exact R20).
    assert (B22 : getr r1 22 = Z_to_bv 64 (n - n mod 8)) by (rewrite (AG1 22) by notin_list; gres; exact R22).
    assert (B9 : getr r1 9 = Z_to_bv 64 n) by (rewrite (AG1 9) by notin_list; gres; exact R9).
    wd_eexists. split.
    - ab_ft K66f10 D_4bfd4 ltac:(condz).                  (* [comment removed for export] *)
      an K66f14 D_4bfd8.                                   (* [comment removed for export] *)
      eapply msteps_trans; [exact RUN1|].
      ab_ft K66f18 D_4bfdc ltac:(condz).                  (* [comment removed for export] *)
      eapply msteps_trans; [apply (GLSB2 _ M rom psb RgSB)|]. zlit_at.   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 (Z_to_bv 64 SB)) (v := Z_to_bv 64 SB);
          [exact K66f24 | reflexivity | exact D_4bfe8 | gres; rwH; imm_norm; rewrite ?v_addi_0; exact RSB | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      av K66f28 D_4bfec (Z_to_bv 64 e) ltac:((lazymatch goal with |- ?G => let G' := eval unfold e in G in change_no_check G' end); cbv delta [v_add] beta; rewrite at_u by lia; unorm; f_equal; lia).  (* [comment removed for export] *)
      av K66f2c D_4bff0 (Z_to_bv 64 (SB - 1)) ltac:(vz).  (* [comment removed for export] *)
      an K66f30 D_4bff4.                                   (* [comment removed for export] *)
      replace (v_sltu (Z_to_bv 64 SB) (Z_to_bv 64 (SB - 1))) with (Z_to_bv 64 0)
        by ((lazymatch goal with |- ?G => let G' := eval unfold v_sltu, c_ltu, bv_ltu in G in change_no_check G' end); unorm; replace (SB <? SB - 1)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
      an K66f34 D_4bff8.                                   (* [comment removed for export] *)
      an K66f38 D_4bffc.                                   (* [comment removed for export] *)
      replace (v_and (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 (SB - 1))) with (Z_to_bv 64 (SB - 1))
        by (symmetry; (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end); unorm; f_equal; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_comm, Z.land_ones by lia; apply Z.mod_small; lia).
      ab_ft K66f3c D_4c000 ltac:(condz).                  (* [comment removed for export] *)
      eapply msteps_trans; [apply (GLMB _ M rom pmb RgMB)|]. zlit_at.   (* [comment removed for export] *)
      eapply msteps_trans; [apply (GLME _ M rom pme RgME)|]. zlit_at.   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
          [exact K66f50 | reflexivity | exact D_4c014 | gres; rwH; imm_norm; rewrite ?v_addi_0; exact RMB | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 midend) (v := midend);
          [exact K66f54 | reflexivity | exact D_4c018 | gres; rwH; imm_norm; rewrite ?v_addi_0; exact RME | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      an K66f58 D_4c01c.                                   (* [comment removed for export] *)
      ab_tk K66f5c D_4c020 ltac:(condz).                  (* [comment removed for export] *)
      eapply msteps_trans; [apply (GLHE _ M rom phe RgHE)|]. zlit_at.   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 (Z_to_bv 64 0x7fffffffffff)) (v := Z_to_bv 64 0x7fffffffffff);
          [exact K66f6c | reflexivity | exact D_4c030 | gres; rwH; imm_norm; rewrite ?v_addi_0; exact RHE | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      an K66f70 D_4c034.                                   (* [comment removed for export] *)
      av K66f74 D_4c038 (Z_to_bv 64 (0xfffffffffff + SB)) ltac:(vz).   (* [comment removed for export] *)
      ab_ft K66f78 D_4c03c ltac:(condz).                  (* [comment removed for export] *)
      ab_ft K66f7c D_4c040 ltac:(condz).                  (* [comment removed for export] *)
      eapply msteps_trans; [apply (GLFL _ M rom pfl RgFL)|]. zlit_at.   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lbu with (b := Z_to_bv 8 1); [exact K66f88 | reflexivity | exact D_4c04c
          | gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; exact Rpp]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      av K66f8c D_4c050 (Z_to_bv 64 (e / 8)) ltac:(cbv delta [v_srli] beta; rewrite Z.shiftr_div_pow2 by lia; unorm; reflexivity).  (* [comment removed for export] *)
      av K66f90 D_4c054 (Z_to_bv 64 (SB + e / 8)) ltac:(vz).   (* [comment removed for export] *)
      an K66f94 D_4c058.                                   (* [comment removed for export] *)
      an K66f98 D_4c05c.                                   (* [comment removed for export] *)
      replace (v_and (Z_to_bv 64 n) (Z_to_bv 64 18446744073709551615)) with (Z_to_bv 64 n)
        by (symmetry; (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end); unorm; f_equal; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
      av K66f9c D_4c060 (Z_to_bv 64 (n mod 8)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end); unorm; f_equal; change (bv_wrap 64 7) with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sb_at with (a := Z_to_bv 64 (SB + e / 8)) (b := Z_to_bv 8 (n mod 8));
          [exact K66fa0 | reflexivity | exact D_4c064 | gres; rwH; imm_norm; rewrite ?v_addi_0; reflexivity | gres; rwH; reflexivity | unorm; reflexivity | exact SOK]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      change (wbytes M _ _) with (amE1_mem M).
      wd_refl.
    - ra_chain.
  Qed.
  (* [comment removed for export] *)
  Ltac setlast :=
    lazymatch goal with
    | |- msteps _ (mkst (regupd _ _ ?v) _ _ _) _ => first [is_var v | let t := fresh "w" in set (t := v)]
    | |- _ => idtac
    end.
  Ltac anl F D := stepi F D; gres; rwH; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold btgt in G in change_no_check G' end); rewrite ?at_addi; zlit_at; setlast.
  (* [comment removed for export] *)
  Ltac wc_foldlast c :=
    lazymatch goal with
    | |- msteps ?sg (mkst (regupd ?r ?rd ?v) ?pc ?mm ?rm) ?X =>
        change (msteps sg (mkst (regupd r rd v) pc mm rm) X) with (msteps sg (mkst (regupd r rd c) pc mm rm) X)
    end.
  Ltac anlc F D c := stepi F D; gres; rwH; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold btgt in G in change_no_check G' end); rewrite ?at_addi; zlit_at; first [wc_foldlast c | setlast].

  Variables (gFL3 gRMS : Z) (prms msetw : word) (fillw : Z).
  Hypothesis GLFL3 : gload segs rb 0x4c1d0 10 gFL3.
  Hypothesis GLRMS : gload segs rb 0x4c1ec 11 gRMS.
  Hypothesis Gcells2 : (AIMGLO <= gFL3 /\ gFL3 + 8 <= AIMGHI)%Z /\ (AIMGLO <= gRMS /\ gRMS + 8 <= AIMGHI)%Z /\ (AIMGLO <= U prms /\ U prms + 8 <= AIMGHI)%Z /\ (0 <= fillw < 2 ^ 31)%Z.
  Hypothesis Gthr2 : (U thr + 4096 <= U sp)%Z.
  Hypothesis MSOK : ret_ok msetw.

  Definition amE2a_mem (M : word -> option byte) (w0 w8 w16 : word) : word -> option byte :=
    wbytes (wbytes (wbytes M (at_ thr 2800) (LE8 w0)) (at_ thr 2808) (LE8 w8)) (at_ thr 2816) (LE8 w16).

  Lemma amE2a : forall (M : word -> option byte) r0 (v0 v8 v16 : word),
    getr r0 10 = at_ thr 2800 -> getr r0 9 = Z_to_bv 64 n -> getr r0 19 = Z_to_bv 64 (needed n) ->
    rdn segs M (at_ thr 2800) 8 = Some (LE8 v0) -> rdn segs M (at_ thr 2808) 8 = Some (LE8 v8) -> rdn segs M (at_ thr 2816) 8 = Some (LE8 v16) ->
    store_ok segs M (at_ thr 2800) 24 = true ->
    exists r w0 w8 w16, msteps segs (mkst r0 (at_ rb 0x4c074) M rom) (mkst r (at_ rb 0x4c0c8) (amE2a_mem M w0 w8 w16) rom)
      /\ getr r 10 = at_ thr 2912 /\ getr r 11 = Z_to_bv 64 512
      /\ regs_agree (fun x => In x [10; 11; 12; 13; 14]) r0 r.
  Proof using Hbsz Gthr Hn bsz szw m HAL2.
    intros M r0 v0 v8 v16 R10 R9 R19 Rv0 Rv8 Rv16 SOK.
    pose proof (u64_range thr) as Hthr. destruct Gthr as [Gt1 Gt2]. destruct (needed_facts n Hn) as [NF1 NF2].
    Ltac sok24 SOK := repeat (eapply store_ok_mono; [apply wbytes_grows|]);
      eapply (store_ok_sub segs _ (at_ thr 2800) _ 24); [rewrite at_u; lia | exact SOK | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia].
    eexists _, _, _, _. split.
    - chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 v16) (v := v16);
          [exact K66fa8 | reflexivity | exact D_4c06c | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi; zlit_at; exact Rv16 | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 v0) (v := v0);
          [exact K66fac | reflexivity | exact D_4c070 | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi, ?at_add_0_r; zlit_at; exact Rv0 | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 v8) (v := v8);
          [exact K66fb0 | reflexivity | exact D_4c074 | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi; zlit_at; exact Rv8 | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      av K66fb4 D_4c078 (Z_to_bv 64 (needed n - n)) ltac:(vz).   (* [comment removed for export] *)
      an K66fb8 D_4c07c. setlast.                          (* [comment removed for export] *)
      an K66fbc D_4c080. an K66fc0 D_4c084.               (* [comment removed for export] *)
      an K66fc4 D_4c088. setlast.                          (* [comment removed for export] *)
      an K66fc8 D_4c08c. setlast.                          (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sd_at with (a := at_ thr 2800);
          [exact K66fcc | reflexivity | exact D_4c090 | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi, ?at_add_0_r; reflexivity | gres; rwH; reflexivity | sok24 SOK]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sd_at with (a := at_ thr 2808);
          [exact K66fd0 | reflexivity | exact D_4c094 | gres; rwH; imm_norm; rewrite ?at_addi; reflexivity | gres; rwH; reflexivity | sok24 SOK]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sd_at with (a := at_ thr 2816);
          [exact K66fd4 | reflexivity | exact D_4c098 | gres; rwH; imm_norm; rewrite ?at_addi; reflexivity | gres; rwH; reflexivity | sok24 SOK]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      lazymatch goal with |- msteps _ (mkst _ _ (wbytes (wbytes (wbytes M _ (word_to_le_bytes 8 ?a)) _ (word_to_le_bytes 8 ?b)) _ (word_to_le_bytes 8 ?c)) _) _ =>
        change (wbytes (wbytes (wbytes M _ _) _ _) _ _) with (amE2a_mem M a b c) end.
      ab_tk K66fd8 D_4c09c ltac:(condz).                  (* [comment removed for export] *)
      an K66ff4 D_4c0b8.                                   (* [comment removed for export] *)
      an K66ff8 D_4c0bc.                                   (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.

  Lemma amE2lo : forall (M : word -> option byte) r0,
    (needed n <= 512)%Z -> getr r0 11 = Z_to_bv 64 512 -> getr r0 19 = Z_to_bv 64 (needed n) ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4c0c8) M rom) (mkst r (at_ rb 0x4c1b4) M rom)
      /\ getr r 11 = Z_to_bv 64 (class_of (needed n))
      /\ regs_agree (fun x => In x [11; 12; 13; 14; 15; 16]) r0 r.
  Proof using Hbsz Hn bsz szw m HAL2.
    intros M r0 Hle R11 R19. destruct (needed_facts n Hn) as [NF1 NF2].
    wd_eexists. split.
    - ab_ft K66ffc D_4c0c0 ltac:(condz).                  (* [comment removed for export] *)
      av K67000 D_4c0c4 (Z_to_bv 64 (needed n + 31)) ltac:(vz).        (* [comment removed for export] *)
      av K67004 D_4c0c8 (Z_to_bv 64 ((needed n + 31) / 32)) ltac:(vz). (* [comment removed for export] *)
      an K67008 D_4c0cc.                                   (* [comment removed for export] *)
      wd_refl.
    - post; [|ra_solve]. (lazymatch goal with |- ?G => let G' := eval unfold class_of in G in change_no_check G' end). replace (needed n <=? 512)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
  Qed.

  Lemma amE2hi : forall (M : word -> option byte) r0,
    (512 < needed n)%Z -> getr r0 11 = Z_to_bv 64 512 -> getr r0 19 = Z_to_bv 64 (needed n) ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4c0c8) M rom) (mkst r (at_ rb 0x4c1b4) M rom)
      /\ getr r 11 = Z_to_bv 64 (class_of (needed n))
      /\ regs_agree (fun x => In x [11; 12; 13; 14; 15; 16]) r0 r.
  Proof using Hbsz Hn bsz szw m HAL2.
    intros M r0 Hgt R11 R19. destruct (needed_facts n Hn) as [NF1 NF2].
    wd_eexists. split.
    - ab_tk K66ffc D_4c0c0 ltac:(condz).                  (* [comment removed for export] *)
      anlc K6700c D_4c0d0 (cidv_a2_1 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67010 D_4c0d4 (cidv_a5_1 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67014 D_4c0d8 (cidv_a6_1 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67018 D_4c0dc (cidv_a7_1 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K6701c D_4c0e0 (cidv_t0_1 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67020 D_4c0e4 (cidv_a2_2 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67024 D_4c0e8 (cidv_a5_2 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67028 D_4c0ec (cidv_a6_2 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K6702c D_4c0f0 (cidv_a7_2 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67030 D_4c0f4 (cidv_t0_2 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67034 D_4c0f8 (cidv_t1_1 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67038 D_4c0fc (cidv_a2_3 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K6703c D_4c100 (cidv_t1_2 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67040 D_4c104 (cidv_a5_3 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67044 D_4c108 (cidv_t1_3 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67048 D_4c10c (cidv_a6_3 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K6704c D_4c110 (cidv_t1_4 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67050 D_4c114 (cidv_a7_3 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67054 D_4c118 (cidv_t1_5 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67058 D_4c11c (cidv_t0_3 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K6705c D_4c120 (cidv_t1_6 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67060 D_4c124 (cidv_a2_4 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67064 D_4c128 (cidv_t1_7 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67068 D_4c12c (cidv_a2_5 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K6706c D_4c130 (cidv_t1_8 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67070 D_4c134 (cidv_a2_6 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67074 D_4c138 (cidv_t1_9 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67078 D_4c13c (cidv_a2_7 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K6707c D_4c140 (cidv_a2_8 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67080 D_4c144 (cidv_t1_10 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67084 D_4c148 (cidv_a5_4 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67088 D_4c14c (cidv_a2_9 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K6708c D_4c150 (cidv_a5_5 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67090 D_4c154 (cidv_a2_10 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67094 D_4c158 (cidv_a2_11 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67098 D_4c15c (cidv_a2_12 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K6709c D_4c160 (cidv_a5_6 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K670a0 D_4c164 (cidv_a2_13 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K670a4 D_4c168 (cidv_a5_7 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K670a8 D_4c16c (cidv_a2_14 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K670ac D_4c170 (cidv_a6_4 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K670b0 D_4c174 (cidv_a2_15 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K670b4 D_4c178 (cidv_a2_16 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K670b8 D_4c17c (cidv_a5_8 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K670bc D_4c180 (cidv_a2_17 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K670c0 D_4c184 (cidv_a7_4 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K670c4 D_4c188 (cidv_a5_9 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K670c8 D_4c18c (cidv_a2_18 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K670cc D_4c190 (cidv_a6_5 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K670d0 D_4c194 (cidv_a5_10 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K670d4 D_4c198 (cidv_a4_1 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K670d8 D_4c19c (cidv_a2_19 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K670dc D_4c1a0 (cidv_a4_2 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K670e0 D_4c1a4 (cidv_a2_20 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K670e4 D_4c1a8 (cidv_s0_1 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      wd_refl.
    - split; [|ra_chain].
      gres. rewrite <- (cid_hi_ok (needed n)) by lia. symmetry. apply cid_hi_cidv.
  Qed.
  (* [comment removed for export] *)
  Lemma amE2c : forall (M : word -> option byte) r0 (vbs : word),
    let c := class_of (needed n) in
    getr r0 10 = at_ thr 2912 -> getr r0 11 = Z_to_bv 64 c -> getr r0 9 = Z_to_bv 64 n -> getr r0 20 = at_ m (rz n) -> getr r0 2 = sp ->
    rdn segs M (at_ thr (2912 + 8 * c)) 8 = Some (LE8 vbs) -> store_ok segs M (at_ thr (2912 + 8 * c)) 8 = true ->
    rdn segs M (at_ sp 8) 8 = Some (LE8 (Z_to_bv 64 1)) ->
    rdn segs M (Z_to_bv 64 gFL3) 8 = Some (LE8 pfl) -> rdn segs M (at_ pfl 44) 4 = Some (LE4 4096) -> rdn segs M (at_ pfl 52) 4 = Some (LE4 fillw) ->
    rdn segs M (Z_to_bv 64 gRMS) 8 = Some (LE8 prms) -> rdn segs M prms 8 = Some (LE8 msetw) ->
    exists r wc, msteps segs (mkst r0 (at_ rb 0x4c1b4) M rom) (mkst r msetw (wbytes M (at_ thr (2912 + 8 * c)) (LE8 wc)) rom)
      /\ getr r 1 = at_ rb 0x4c204 /\ getr r 10 = at_ m (rz n) /\ getr r 11 = Z_to_bv 64 fillw /\ getr r 12 = Z_to_bv 64 (Z.min n 4096)
      /\ getr r 13 = msetw
      /\ regs_agree (fun x => In x [1; 10; 11; 12; 13]) r0 r.
  Proof using Dctx Dsp Dstk Dthr GLFL3 GLRMS GSB Gcells Gcells2 GgSB Gm Gpsb Gsp Gthr Gthr2 HAL2 Hbsz Hn Htid MSOK RB.
    intros M r0 vbs c R10 R11 R9 R20 R2 Rbs SOKbs Rfill RgFL Rmmf Rfb RgRMS Rrms.
    pose proof (u64_range thr) as Hthr. pose proof (u64_range sp) as Hspr. pose proof (u64_range pfl). pose proof (u64_range prms).
    destruct Gthr as [[Gt1 GtI] Gt2]. unfold hideW in GtI. destruct Gsp as [Gs1 Gs2]. destruct Gcells as (GC & Gpmb & Gpme & Gphe & Gpfl). destruct Gcells2 as (Gf3 & Grms & Gprms & Gfw).
    destruct (needed_facts n Hn) as [NF1 NF2]. pose proof (AsArith3.class_of_range (needed n) ltac:(lia)) as Hc. fold c in Hc.
    set (M' := fun wc : word => wbytes M (at_ thr (2912 + 8 * c)) (LE8 wc)).
    assert (M'_out : forall wc (x : word), (U x < U thr + 2912 + 8 * c \/ U thr + 2912 + 8 * c + 8 <= U x)%Z -> M' wc x = M x).
    { intros wc x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). rewrite wbytes_outside; [reflexivity | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    Ltac cellE R OUT := rewrite <- R; apply rdn_ext; [rewrite ?at_u by lia; wd_ulia_c | intros x Hx; apply OUT; rewrite ?at_u in Hx by lia; unorm; cbn in Hx; lia].
    assert (Rfill' : forall wc, rdn segs (M' wc) (at_ sp 8) 8 = Some (LE8 (Z_to_bv 64 1))) by (intros wc; cellE Rfill (M'_out wc)).
    assert (RgFL' : forall wc, rdn segs (M' wc) (Z_to_bv 64 gFL3) 8 = Some (LE8 pfl)).
    { intros wc. rewrite <- RgFL. apply rdn_ext; [wd_ulia_c | intros x Hx; apply M'_out; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia]. }
    assert (Rmmf' : forall wc, rdn segs (M' wc) (at_ pfl 44) 4 = Some (LE4 4096)) by (intros wc; cellE Rmmf (M'_out wc)).
    assert (Rfb' : forall wc, rdn segs (M' wc) (at_ pfl 52) 4 = Some (LE4 fillw)) by (intros wc; cellE Rfb (M'_out wc)).
    assert (RgRMS' : forall wc, rdn segs (M' wc) (Z_to_bv 64 gRMS) 8 = Some (LE8 prms)).
    { intros wc. rewrite <- RgRMS. apply rdn_ext; [wd_ulia_c | intros x Hx; apply M'_out; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia]. }
    assert (Rrms' : forall wc, rdn segs (M' wc) prms 8 = Some (LE8 msetw)) by (intros wc; cellE Rrms (M'_out wc)).
    (* [comment removed for export] *)
    assert (W1 : exists r1 wc, msteps segs (mkst r0 (at_ rb 0x4c1b4) M rom) (mkst r1 (at_ rb 0x4c1e4) (M' wc) rom)
               /\ getr r1 10 = pfl /\ getr r1 11 = Z_to_bv 64 4096 /\ getr r1 12 = Z_to_bv 64 n /\ getr r1 9 = Z_to_bv 64 n
               /\ getr r1 20 = at_ m (rz n) /\ getr r1 2 = sp
               /\ regs_agree (fun x => In x [1; 10; 11; 12; 13]) r0 r1).
    { eexists _, _. split.
      - av K670e8 D_4c1ac (Z_to_bv 64 (8 * c)) ltac:(vz).                   (* [comment removed for export] *)
        av K670ec D_4c1b0 (at_ thr (2912 + 8 * c)) ltac:(rewrite v_add_at by lia; rewrite at_at; reflexivity).   (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_ld with (bs := LE8 vbs) (v := vbs);
            [exact K670f0 | reflexivity | exact D_4c1b4 | gres; rwH; imm_norm; rewrite ?v_addi_0; exact Rbs | apply bytes_le_to_Z_8]
          | step_simpl]; vn.                                                (* [comment removed for export] *)
        an K670f4 D_4c1b8. setlast.                                         (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sd_at with (a := at_ thr (2912 + 8 * c));
            [exact K670f8 | reflexivity | exact D_4c1bc | gres; rwH; imm_norm; rewrite ?v_addi_0; reflexivity | gres; rwH; reflexivity | exact SOKbs]
          | step_simpl]; vn.                                                (* [comment removed for export] *)
        lazymatch goal with |- msteps _ (mkst _ _ (wbytes M _ (word_to_le_bytes 8 ?a)) _) _ => change (wbytes M _ _) with (M' a) end.
        chain_step; [reflexivity
          | eapply step_ld with (bs := LE8 (Z_to_bv 64 1)) (v := Z_to_bv 64 1);
            [exact K670fc | reflexivity | exact D_4c1c0 | gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; apply Rfill' | apply bytes_le_to_Z_8]
          | step_simpl]; vn.                                                (* [comment removed for export] *)
        ab_ft K67100 D_4c1c4 ltac:(condz).                                 (* [comment removed for export] *)
        eapply msteps_trans; [apply (GLFL3 _ _ rom pfl); apply RgFL'|]. zlit_at.   (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 4096)) (v := Z_to_bv 64 4096);
            [exact K6710c | reflexivity | exact D_4c1d0 | gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; apply Rmmf' | apply bytes4_small; lia]
          | step_simpl]; rewrite (v_lw_small 4096) by lia; vn.              (* [comment removed for export] *)
        ab_ft K67110 D_4c1d4 ltac:(condz).                                 (* [comment removed for export] *)
        an K67114 D_4c1d8.                                                  (* [comment removed for export] *)
        wd_refl.
      - post. ra_solve. }
    destruct W1 as (r1 & wc & RUN1 & A10 & A11 & A12 & A9 & A20 & A2 & AG1).
    (* [comment removed for export] *)
    assert (W2 : exists r2, msteps segs (mkst r1 (at_ rb 0x4c1e4) (M' wc) rom) (mkst r2 (at_ rb 0x4c1ec) (M' wc) rom)
               /\ getr r2 12 = Z_to_bv 64 (Z.min n 4096) /\ (forall i : reg, i <> 12 -> getr r2 i = getr r1 i)).
    { destruct (Z.lt_ge_cases n 4096) as [Hlt|Hge].
      - wd_eexists. split; [ab_tk K67118 D_4c1dc ltac:(condz); wd_refl|].
        split; [rewrite Z.min_l by lia; exact A12 | intros i Hi; reflexivity].
      - wd_eexists. split; [ab_ft K67118 D_4c1dc ltac:(condz); an K6711c D_4c1e0; wd_refl|].
        split; [gres; rewrite Z.min_r by lia; rewrite ?v_addi_0; reflexivity | intros i Hi; rewrite getr_other by (intros E; apply Hi; exact E); reflexivity]. }
    destruct W2 as (r2 & RUN2 & B12 & BK).
    eexists _, wc. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
      eapply msteps_trans; [apply (GLRMS _ _ rom prms); apply RgRMS'|]. zlit_at.   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 msetw) (v := msetw);
          [exact K67128 | reflexivity | exact D_4c1ec | gres; rwH; imm_norm; rewrite ?v_addi_0; apply Rrms' | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                                  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 fillw)) (v := Z_to_bv 64 fillw);
          [exact K6712c | reflexivity | exact D_4c1f0 | gres; rewrite (BK 10) by (intros E; discriminate E); rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; apply Rfb' | apply bytes4_small; lia]
        | step_simpl]; rewrite (v_lw_small fillw) by lia; vn.                (* [comment removed for export] *)
      an K67130 D_4c1f4.                                                    (* [comment removed for export] *)
      aret K67134 D_4c1f8 msetw.                                            (* [comment removed for export] *)
      rewrite at_addi; zlit_at. wd_refl.
    - post.
      + rewrite (BK 20) by (intros E; discriminate E). rewrite A20, ?at_add_0_r. reflexivity.
      + apply (regs_agree_strengthen [1; 10; 11; 12; 13] [1; 10; 11; 12; 13; 20] r0).
        * repeat (first [ apply regs_agree_upd; [solve [in_list] |] ]).
          intros i Hni. rewrite (BK i) by (intros ->; apply Hni; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]). apply AG1. intros Hx; apply Hni. cbn [In] in Hx |- *. clear - Hx. am_tauto.
        * intros i Hi Hni. cbn [In] in Hi.
          repeat (destruct Hi as [<-|Hi]; [first [exfalso; apply Hni; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])] | gres; rewrite (BK 20) by (intros E; discriminate E); apply AG1; notin_list] |]).
          destruct Hi.
  Qed.
End AMC.
End FPGen1.
