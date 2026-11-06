(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0.
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
  [Some W_4c834; Some W_4c838; Some W_4c83c; Some W_4c840; Some W_4c844; Some W_4c848; Some W_4c84c; Some W_4c850;
   Some W_4c854; Some W_4c858; Some W_4c85c; Some W_4c860; Some W_4c864; Some W_4c868; Some W_4c86c; Some W_4c870;
   Some W_4c874; Some W_4c878; Some W_4c87c; Some W_4c880; Some W_4c884; Some W_4c888; Some W_4c88c; Some W_4c890;
   Some W_4c894; Some W_4c898; Some W_4c89c; Some W_4c8a0; Some W_4c8a4; Some W_4c8a8; Some W_4c8ac; Some W_4c8b0;
   Some W_4c8b4; Some W_4c8b8; Some W_4c8bc; Some W_4c8c0; Some W_4c8c4; Some W_4c8c8; Some W_4c8cc; Some W_4c8d0;
   Some W_4c8d4; Some W_4c8d8; Some W_4c8dc; Some W_4c8e0; Some W_4c8e4; Some W_4c8e8; Some W_4c8ec; Some W_4c8f0;
   Some W_4c8f4; Some W_4c8f8; Some W_4c8fc; Some W_4c900; Some W_4c904; Some W_4c908; Some W_4c90c; Some W_4c910;
   Some W_4c914; Some W_4c918; Some W_4c91c; Some W_4c920; Some W_4c924; Some W_4c928; Some W_4c92c; Some W_4c930;
   Some W_4c934; Some W_4c938; Some W_4c93c; Some W_4c940; Some W_4c944; Some W_4c948; Some W_4c94c; Some W_4c950;
   None; None; Some W_4c95c; Some W_4c960; Some W_4c964; Some W_4c968; Some W_4c96c; Some W_4c970; Some W_4c974;
   Some W_4c978; Some W_4c97c; Some W_4c980; Some W_4c984; Some W_4c988; Some W_4c98c; Some W_4c990; Some W_4c994;
   Some W_4c998; Some W_4c99c; Some W_4c9a0; Some W_4c9a4; Some W_4c9a8; Some W_4c9ac; Some W_4c9b0; Some W_4c9b4;
   Some W_4c9b8; Some W_4c9bc; Some W_4c9c0; Some W_4c9c4; Some W_4c9c8; Some W_4c9cc; Some W_4c9d0; Some W_4c9d4;
   Some W_4c9d8; Some W_4c9dc; Some W_4c9e0; Some W_4c9e4; Some W_4c9e8; Some W_4c9ec; Some W_4c9f0; Some W_4c9f4;
   Some W_4c9f8; Some W_4c9fc; Some W_4ca00; Some W_4ca04; Some W_4ca08; Some W_4ca0c; Some W_4ca10; Some W_4ca14;
   Some W_4ca18; Some W_4ca1c; Some W_4ca20; Some W_4ca24; Some W_4ca28; Some W_4ca2c; Some W_4ca30; Some W_4ca34;
   Some W_4ca38; Some W_4ca3c; Some W_4ca40; Some W_4ca44; Some W_4ca48; Some W_4ca4c; Some W_4ca50; Some W_4ca54;
   None; None; Some W_4ca60; Some W_4ca64; Some W_4ca68; Some W_4ca6c; Some W_4ca70; Some W_4ca74; Some W_4ca78;
   None; None; None; None; Some W_4ca8c; Some W_4ca90; Some W_4ca94; Some W_4ca98; Some W_4ca9c; None; None;
   Some W_4caa8; Some W_4caac; Some W_4cab0; Some W_4cab4; Some W_4cab8; None; None; Some W_4cac4; Some W_4cac8;
   Some W_4cacc; Some W_4cad0; Some W_4cad4; Some W_4cad8; Some W_4cadc; Some W_4cae0; Some W_4cae4; Some W_4cae8;
   Some W_4caec; Some W_4caf0; Some W_4caf4; Some W_4caf8; Some W_4cafc; Some W_4cb00; Some W_4cb04; Some W_4cb08;
   Some W_4cb0c; Some W_4cb10; Some W_4cb14; Some W_4cb18; Some W_4cb1c; Some W_4cb20; Some W_4cb24; Some W_4cb28;
   Some W_4cb2c; Some W_4cb30; Some W_4cb34; Some W_4cb38; Some W_4cb3c; Some W_4cb40; Some W_4cb44; Some W_4cb48;
   Some W_4cb4c; Some W_4cb50; Some W_4cb54; Some W_4cb58; Some W_4cb5c; Some W_4cb60; Some W_4cb64; Some W_4cb68;
   Some W_4cb6c; Some W_4cb70; Some W_4cb74; Some W_4cb78; Some W_4cb7c; Some W_4cb80; Some W_4cb84; Some W_4cb88;
   Some W_4cb8c; Some W_4cb90; Some W_4cb94; Some W_4cb98; Some W_4cb9c; Some W_4cba0; Some W_4cba4; Some W_4cba8;
   Some W_4cbac; Some W_4cbb0; Some W_4cbb4; Some W_4cbb8; Some W_4cbbc; Some W_4cbc0; Some W_4cbc4; Some W_4cbc8;
   Some W_4cbcc; Some W_4cbd0; Some W_4cbd4; Some W_4cbd8; Some W_4cbdc; Some W_4cbe0; Some W_4cbe4; Some W_4cbe8;
   Some W_4cbec; Some W_4cbf0; Some W_4cbf4; Some W_4cbf8; Some W_4cbfc; Some W_4cc00; Some W_4cc04; Some W_4cc08;
   Some W_4cc0c; Some W_4cc10; Some W_4cc14; Some W_4cc18; Some W_4cc1c; Some W_4cc20; Some W_4cc24; Some W_4cc28;
   Some W_4cc2c; Some W_4cc30; Some W_4cc34; Some W_4cc38; Some W_4cc3c; None; None; Some W_4cc48; Some W_4cc4c;
   Some W_4cc50; Some W_4cc54; Some W_4cc58; None; None; Some W_4cc64; Some W_4cc68; Some W_4cc6c; Some W_4cc70;
   Some W_4cc74; Some W_4cc78; Some W_4cc7c; Some W_4cc80; Some W_4cc84; Some W_4cc88; Some W_4cc8c; Some W_4cc90;
   Some W_4cc94; Some W_4cc98; Some W_4cc9c; Some W_4cca0; Some W_4cca4; None; None; Some W_4ccb0; Some W_4ccb4;
   Some W_4ccb8; Some W_4ccbc; Some W_4ccc0; Some W_4ccc4; Some W_4ccc8; Some W_4cccc; Some W_4ccd0; Some W_4ccd4;
   Some W_4ccd8; Some W_4ccdc; Some W_4cce0; Some W_4cce4; Some W_4cce8; Some W_4ccec; Some W_4ccf0; Some W_4ccf4;
   Some W_4ccf8; Some W_4ccfc; Some W_4cd00; Some W_4cd04]%list.

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
  Hypothesis HAL2 : code_ato segs rb 0x4c834 al2_words.
  Hypothesis RB : (U rb mod 2 = 0)%Z /\ (U rb + 2 ^ 24 < 2 ^ 64)%Z.

  Lemma K67770 : fetch_word segs (at_ rb 0x4c834) = Some W_4c834.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 0 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67774 : fetch_word segs (at_ rb 0x4c838) = Some W_4c838.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 1 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67778 : fetch_word segs (at_ rb 0x4c83c) = Some W_4c83c.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 2 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K6777c : fetch_word segs (at_ rb 0x4c840) = Some W_4c840.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 3 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67780 : fetch_word segs (at_ rb 0x4c844) = Some W_4c844.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 4 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67784 : fetch_word segs (at_ rb 0x4c848) = Some W_4c848.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 5 _ HAL2 eq_refl). Qed.

   (* [comment removed for export] *)
  Lemma K67790 : fetch_word segs (at_ rb 0x4c854) = Some W_4c854.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 8 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67794 : fetch_word segs (at_ rb 0x4c858) = Some W_4c858.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 9 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67798 : fetch_word segs (at_ rb 0x4c85c) = Some W_4c85c.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 10 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K6779c : fetch_word segs (at_ rb 0x4c860) = Some W_4c860.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 11 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K677a0 : fetch_word segs (at_ rb 0x4c864) = Some W_4c864.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 12 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K677a4 : fetch_word segs (at_ rb 0x4c868) = Some W_4c868.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 13 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K677a8 : fetch_word segs (at_ rb 0x4c86c) = Some W_4c86c.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 14 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K677ac : fetch_word segs (at_ rb 0x4c870) = Some W_4c870.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 15 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K677b0 : fetch_word segs (at_ rb 0x4c874) = Some W_4c874.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 16 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K677b4 : fetch_word segs (at_ rb 0x4c878) = Some W_4c878.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 17 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K677b8 : fetch_word segs (at_ rb 0x4c87c) = Some W_4c87c.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 18 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K677bc : fetch_word segs (at_ rb 0x4c880) = Some W_4c880.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 19 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K677c0 : fetch_word segs (at_ rb 0x4c884) = Some W_4c884.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 20 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K677c4 : fetch_word segs (at_ rb 0x4c888) = Some W_4c888.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 21 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K677c8 : fetch_word segs (at_ rb 0x4c88c) = Some W_4c88c.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 22 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K677cc : fetch_word segs (at_ rb 0x4c890) = Some W_4c890.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 23 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K677d0 : fetch_word segs (at_ rb 0x4c894) = Some W_4c894.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 24 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K677d4 : fetch_word segs (at_ rb 0x4c898) = Some W_4c898.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 25 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K677d8 : fetch_word segs (at_ rb 0x4c89c) = Some W_4c89c.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 26 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K677dc : fetch_word segs (at_ rb 0x4c8a0) = Some W_4c8a0.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 27 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K677e0 : fetch_word segs (at_ rb 0x4c8a4) = Some W_4c8a4.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 28 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K677e4 : fetch_word segs (at_ rb 0x4c8a8) = Some W_4c8a8.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 29 _ HAL2 eq_refl). Qed.

































   (* [comment removed for export] *)
  Lemma K67870 : fetch_word segs (at_ rb 0x4c934) = Some W_4c934.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 64 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67874 : fetch_word segs (at_ rb 0x4c938) = Some W_4c938.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 65 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67878 : fetch_word segs (at_ rb 0x4c93c) = Some W_4c93c.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 66 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K6787c : fetch_word segs (at_ rb 0x4c940) = Some W_4c940.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 67 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67880 : fetch_word segs (at_ rb 0x4c944) = Some W_4c944.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 68 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67884 : fetch_word segs (at_ rb 0x4c948) = Some W_4c948.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 69 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67888 : fetch_word segs (at_ rb 0x4c94c) = Some W_4c94c.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 70 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K6788c : fetch_word segs (at_ rb 0x4c950) = Some W_4c950.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 71 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67898 : fetch_word segs (at_ rb 0x4c95c) = Some W_4c95c.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 74 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K6789c : fetch_word segs (at_ rb 0x4c960) = Some W_4c960.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 75 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K678a0 : fetch_word segs (at_ rb 0x4c964) = Some W_4c964.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 76 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K678a4 : fetch_word segs (at_ rb 0x4c968) = Some W_4c968.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 77 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K678a8 : fetch_word segs (at_ rb 0x4c96c) = Some W_4c96c.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 78 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K678ac : fetch_word segs (at_ rb 0x4c970) = Some W_4c970.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 79 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K678b0 : fetch_word segs (at_ rb 0x4c974) = Some W_4c974.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 80 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K678b4 : fetch_word segs (at_ rb 0x4c978) = Some W_4c978.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 81 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K678b8 : fetch_word segs (at_ rb 0x4c97c) = Some W_4c97c.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 82 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K678bc : fetch_word segs (at_ rb 0x4c980) = Some W_4c980.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 83 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K678c0 : fetch_word segs (at_ rb 0x4c984) = Some W_4c984.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 84 _ HAL2 eq_refl). Qed.








   (* [comment removed for export] *)
  Lemma K678e8 : fetch_word segs (at_ rb 0x4c9ac) = Some W_4c9ac.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 94 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K678ec : fetch_word segs (at_ rb 0x4c9b0) = Some W_4c9b0.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 95 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K678f0 : fetch_word segs (at_ rb 0x4c9b4) = Some W_4c9b4.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 96 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K678f4 : fetch_word segs (at_ rb 0x4c9b8) = Some W_4c9b8.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 97 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K678f8 : fetch_word segs (at_ rb 0x4c9bc) = Some W_4c9bc.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 98 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K678fc : fetch_word segs (at_ rb 0x4c9c0) = Some W_4c9c0.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 99 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67900 : fetch_word segs (at_ rb 0x4c9c4) = Some W_4c9c4.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 100 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67904 : fetch_word segs (at_ rb 0x4c9c8) = Some W_4c9c8.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 101 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67908 : fetch_word segs (at_ rb 0x4c9cc) = Some W_4c9cc.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 102 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K6790c : fetch_word segs (at_ rb 0x4c9d0) = Some W_4c9d0.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 103 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67910 : fetch_word segs (at_ rb 0x4c9d4) = Some W_4c9d4.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 104 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67914 : fetch_word segs (at_ rb 0x4c9d8) = Some W_4c9d8.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 105 _ HAL2 eq_refl). Qed.








   (* [comment removed for export] *)
  Lemma K6793c : fetch_word segs (at_ rb 0x4ca00) = Some W_4ca00.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 115 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67940 : fetch_word segs (at_ rb 0x4ca04) = Some W_4ca04.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 116 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67944 : fetch_word segs (at_ rb 0x4ca08) = Some W_4ca08.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 117 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67948 : fetch_word segs (at_ rb 0x4ca0c) = Some W_4ca0c.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 118 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K6794c : fetch_word segs (at_ rb 0x4ca10) = Some W_4ca10.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 119 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67950 : fetch_word segs (at_ rb 0x4ca14) = Some W_4ca14.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 120 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67954 : fetch_word segs (at_ rb 0x4ca18) = Some W_4ca18.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 121 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67958 : fetch_word segs (at_ rb 0x4ca1c) = Some W_4ca1c.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 122 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K6795c : fetch_word segs (at_ rb 0x4ca20) = Some W_4ca20.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 123 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67960 : fetch_word segs (at_ rb 0x4ca24) = Some W_4ca24.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 124 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67964 : fetch_word segs (at_ rb 0x4ca28) = Some W_4ca28.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 125 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67968 : fetch_word segs (at_ rb 0x4ca2c) = Some W_4ca2c.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 126 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K6796c : fetch_word segs (at_ rb 0x4ca30) = Some W_4ca30.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 127 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67970 : fetch_word segs (at_ rb 0x4ca34) = Some W_4ca34.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 128 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67974 : fetch_word segs (at_ rb 0x4ca38) = Some W_4ca38.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 129 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67978 : fetch_word segs (at_ rb 0x4ca3c) = Some W_4ca3c.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 130 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K6797c : fetch_word segs (at_ rb 0x4ca40) = Some W_4ca40.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 131 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67980 : fetch_word segs (at_ rb 0x4ca44) = Some W_4ca44.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 132 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67984 : fetch_word segs (at_ rb 0x4ca48) = Some W_4ca48.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 133 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67988 : fetch_word segs (at_ rb 0x4ca4c) = Some W_4ca4c.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 134 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K6798c : fetch_word segs (at_ rb 0x4ca50) = Some W_4ca50.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 135 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67990 : fetch_word segs (at_ rb 0x4ca54) = Some W_4ca54.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 136 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K6799c : fetch_word segs (at_ rb 0x4ca60) = Some W_4ca60.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 139 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K679a0 : fetch_word segs (at_ rb 0x4ca64) = Some W_4ca64.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 140 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K679a4 : fetch_word segs (at_ rb 0x4ca68) = Some W_4ca68.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 141 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K679a8 : fetch_word segs (at_ rb 0x4ca6c) = Some W_4ca6c.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 142 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K679ac : fetch_word segs (at_ rb 0x4ca70) = Some W_4ca70.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 143 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K679b0 : fetch_word segs (at_ rb 0x4ca74) = Some W_4ca74.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 144 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K679b4 : fetch_word segs (at_ rb 0x4ca78) = Some W_4ca78.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 145 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K679c8 : fetch_word segs (at_ rb 0x4ca8c) = Some W_4ca8c.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 150 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K679cc : fetch_word segs (at_ rb 0x4ca90) = Some W_4ca90.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 151 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K679d0 : fetch_word segs (at_ rb 0x4ca94) = Some W_4ca94.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 152 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K679d4 : fetch_word segs (at_ rb 0x4ca98) = Some W_4ca98.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 153 _ HAL2 eq_refl). Qed.
   (* [comment removed for export] *)
  Lemma K679e4 : fetch_word segs (at_ rb 0x4caa8) = Some W_4caa8.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 157 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K679e8 : fetch_word segs (at_ rb 0x4caac) = Some W_4caac.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 158 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K679ec : fetch_word segs (at_ rb 0x4cab0) = Some W_4cab0.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 159 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K679f0 : fetch_word segs (at_ rb 0x4cab4) = Some W_4cab4.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 160 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K679f4 : fetch_word segs (at_ rb 0x4cab8) = Some W_4cab8.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 161 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a00 : fetch_word segs (at_ rb 0x4cac4) = Some W_4cac4.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 164 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a04 : fetch_word segs (at_ rb 0x4cac8) = Some W_4cac8.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 165 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a08 : fetch_word segs (at_ rb 0x4cacc) = Some W_4cacc.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 166 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a0c : fetch_word segs (at_ rb 0x4cad0) = Some W_4cad0.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 167 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a10 : fetch_word segs (at_ rb 0x4cad4) = Some W_4cad4.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 168 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a14 : fetch_word segs (at_ rb 0x4cad8) = Some W_4cad8.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 169 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a18 : fetch_word segs (at_ rb 0x4cadc) = Some W_4cadc.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 170 _ HAL2 eq_refl). Qed.
   (* [comment removed for export] *)
  Lemma K67a20 : fetch_word segs (at_ rb 0x4cae4) = Some W_4cae4.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 172 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a24 : fetch_word segs (at_ rb 0x4cae8) = Some W_4cae8.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 173 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a28 : fetch_word segs (at_ rb 0x4caec) = Some W_4caec.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 174 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a2c : fetch_word segs (at_ rb 0x4caf0) = Some W_4caf0.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 175 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a30 : fetch_word segs (at_ rb 0x4caf4) = Some W_4caf4.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 176 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a34 : fetch_word segs (at_ rb 0x4caf8) = Some W_4caf8.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 177 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a38 : fetch_word segs (at_ rb 0x4cafc) = Some W_4cafc.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 178 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a3c : fetch_word segs (at_ rb 0x4cb00) = Some W_4cb00.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 179 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a40 : fetch_word segs (at_ rb 0x4cb04) = Some W_4cb04.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 180 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a44 : fetch_word segs (at_ rb 0x4cb08) = Some W_4cb08.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 181 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a48 : fetch_word segs (at_ rb 0x4cb0c) = Some W_4cb0c.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 182 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a4c : fetch_word segs (at_ rb 0x4cb10) = Some W_4cb10.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 183 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a50 : fetch_word segs (at_ rb 0x4cb14) = Some W_4cb14.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 184 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a54 : fetch_word segs (at_ rb 0x4cb18) = Some W_4cb18.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 185 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a58 : fetch_word segs (at_ rb 0x4cb1c) = Some W_4cb1c.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 186 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a5c : fetch_word segs (at_ rb 0x4cb20) = Some W_4cb20.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 187 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a60 : fetch_word segs (at_ rb 0x4cb24) = Some W_4cb24.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 188 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a64 : fetch_word segs (at_ rb 0x4cb28) = Some W_4cb28.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 189 _ HAL2 eq_refl). Qed.
   (* [comment removed for export] *)
  Lemma K67a6c : fetch_word segs (at_ rb 0x4cb30) = Some W_4cb30.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 191 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a70 : fetch_word segs (at_ rb 0x4cb34) = Some W_4cb34.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 192 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a74 : fetch_word segs (at_ rb 0x4cb38) = Some W_4cb38.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 193 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a78 : fetch_word segs (at_ rb 0x4cb3c) = Some W_4cb3c.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 194 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a7c : fetch_word segs (at_ rb 0x4cb40) = Some W_4cb40.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 195 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a80 : fetch_word segs (at_ rb 0x4cb44) = Some W_4cb44.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 196 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a84 : fetch_word segs (at_ rb 0x4cb48) = Some W_4cb48.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 197 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a88 : fetch_word segs (at_ rb 0x4cb4c) = Some W_4cb4c.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 198 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a8c : fetch_word segs (at_ rb 0x4cb50) = Some W_4cb50.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 199 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a90 : fetch_word segs (at_ rb 0x4cb54) = Some W_4cb54.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 200 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a94 : fetch_word segs (at_ rb 0x4cb58) = Some W_4cb58.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 201 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a98 : fetch_word segs (at_ rb 0x4cb5c) = Some W_4cb5c.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 202 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67a9c : fetch_word segs (at_ rb 0x4cb60) = Some W_4cb60.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 203 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67aa0 : fetch_word segs (at_ rb 0x4cb64) = Some W_4cb64.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 204 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67aa4 : fetch_word segs (at_ rb 0x4cb68) = Some W_4cb68.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 205 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67aa8 : fetch_word segs (at_ rb 0x4cb6c) = Some W_4cb6c.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 206 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67aac : fetch_word segs (at_ rb 0x4cb70) = Some W_4cb70.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 207 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67ab0 : fetch_word segs (at_ rb 0x4cb74) = Some W_4cb74.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 208 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67ab4 : fetch_word segs (at_ rb 0x4cb78) = Some W_4cb78.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 209 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67ab8 : fetch_word segs (at_ rb 0x4cb7c) = Some W_4cb7c.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 210 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67abc : fetch_word segs (at_ rb 0x4cb80) = Some W_4cb80.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 211 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67ac0 : fetch_word segs (at_ rb 0x4cb84) = Some W_4cb84.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 212 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67ac4 : fetch_word segs (at_ rb 0x4cb88) = Some W_4cb88.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 213 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67ac8 : fetch_word segs (at_ rb 0x4cb8c) = Some W_4cb8c.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 214 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67acc : fetch_word segs (at_ rb 0x4cb90) = Some W_4cb90.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 215 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67ad0 : fetch_word segs (at_ rb 0x4cb94) = Some W_4cb94.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 216 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67ad4 : fetch_word segs (at_ rb 0x4cb98) = Some W_4cb98.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 217 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67ad8 : fetch_word segs (at_ rb 0x4cb9c) = Some W_4cb9c.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 218 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67adc : fetch_word segs (at_ rb 0x4cba0) = Some W_4cba0.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 219 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67ae0 : fetch_word segs (at_ rb 0x4cba4) = Some W_4cba4.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 220 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67ae4 : fetch_word segs (at_ rb 0x4cba8) = Some W_4cba8.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 221 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67ae8 : fetch_word segs (at_ rb 0x4cbac) = Some W_4cbac.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 222 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67aec : fetch_word segs (at_ rb 0x4cbb0) = Some W_4cbb0.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 223 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67af0 : fetch_word segs (at_ rb 0x4cbb4) = Some W_4cbb4.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 224 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67af4 : fetch_word segs (at_ rb 0x4cbb8) = Some W_4cbb8.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 225 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67af8 : fetch_word segs (at_ rb 0x4cbbc) = Some W_4cbbc.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 226 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67afc : fetch_word segs (at_ rb 0x4cbc0) = Some W_4cbc0.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 227 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b00 : fetch_word segs (at_ rb 0x4cbc4) = Some W_4cbc4.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 228 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b04 : fetch_word segs (at_ rb 0x4cbc8) = Some W_4cbc8.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 229 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b08 : fetch_word segs (at_ rb 0x4cbcc) = Some W_4cbcc.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 230 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b0c : fetch_word segs (at_ rb 0x4cbd0) = Some W_4cbd0.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 231 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b10 : fetch_word segs (at_ rb 0x4cbd4) = Some W_4cbd4.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 232 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b14 : fetch_word segs (at_ rb 0x4cbd8) = Some W_4cbd8.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 233 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b18 : fetch_word segs (at_ rb 0x4cbdc) = Some W_4cbdc.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 234 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b1c : fetch_word segs (at_ rb 0x4cbe0) = Some W_4cbe0.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 235 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b20 : fetch_word segs (at_ rb 0x4cbe4) = Some W_4cbe4.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 236 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b24 : fetch_word segs (at_ rb 0x4cbe8) = Some W_4cbe8.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 237 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b28 : fetch_word segs (at_ rb 0x4cbec) = Some W_4cbec.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 238 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b2c : fetch_word segs (at_ rb 0x4cbf0) = Some W_4cbf0.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 239 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b30 : fetch_word segs (at_ rb 0x4cbf4) = Some W_4cbf4.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 240 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b34 : fetch_word segs (at_ rb 0x4cbf8) = Some W_4cbf8.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 241 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b38 : fetch_word segs (at_ rb 0x4cbfc) = Some W_4cbfc.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 242 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b3c : fetch_word segs (at_ rb 0x4cc00) = Some W_4cc00.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 243 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b40 : fetch_word segs (at_ rb 0x4cc04) = Some W_4cc04.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 244 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b44 : fetch_word segs (at_ rb 0x4cc08) = Some W_4cc08.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 245 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b48 : fetch_word segs (at_ rb 0x4cc0c) = Some W_4cc0c.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 246 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b4c : fetch_word segs (at_ rb 0x4cc10) = Some W_4cc10.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 247 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b50 : fetch_word segs (at_ rb 0x4cc14) = Some W_4cc14.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 248 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b54 : fetch_word segs (at_ rb 0x4cc18) = Some W_4cc18.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 249 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b58 : fetch_word segs (at_ rb 0x4cc1c) = Some W_4cc1c.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 250 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b5c : fetch_word segs (at_ rb 0x4cc20) = Some W_4cc20.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 251 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b60 : fetch_word segs (at_ rb 0x4cc24) = Some W_4cc24.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 252 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b64 : fetch_word segs (at_ rb 0x4cc28) = Some W_4cc28.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 253 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b68 : fetch_word segs (at_ rb 0x4cc2c) = Some W_4cc2c.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 254 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b6c : fetch_word segs (at_ rb 0x4cc30) = Some W_4cc30.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 255 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b70 : fetch_word segs (at_ rb 0x4cc34) = Some W_4cc34.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 256 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b74 : fetch_word segs (at_ rb 0x4cc38) = Some W_4cc38.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 257 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b78 : fetch_word segs (at_ rb 0x4cc3c) = Some W_4cc3c.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 258 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b84 : fetch_word segs (at_ rb 0x4cc48) = Some W_4cc48.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 261 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b88 : fetch_word segs (at_ rb 0x4cc4c) = Some W_4cc4c.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 262 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b8c : fetch_word segs (at_ rb 0x4cc50) = Some W_4cc50.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 263 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b90 : fetch_word segs (at_ rb 0x4cc54) = Some W_4cc54.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 264 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67b94 : fetch_word segs (at_ rb 0x4cc58) = Some W_4cc58.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 265 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67ba0 : fetch_word segs (at_ rb 0x4cc64) = Some W_4cc64.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 268 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67ba4 : fetch_word segs (at_ rb 0x4cc68) = Some W_4cc68.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 269 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67ba8 : fetch_word segs (at_ rb 0x4cc6c) = Some W_4cc6c.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 270 _ HAL2 eq_refl). Qed.   (* [comment removed for export] *)
  Lemma K67bac : fetch_word segs (at_ rb 0x4cc70) = Some W_4cc70.  Proof using HAL2. exact (code_ato_get segs rb 0x4c834 al2_words 271 _ HAL2 eq_refl). Qed.


































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
      msteps segs (mkst regs (at_ rb 0x4c834) mem rom) (mkst r (at_ rb 0x8f4f0) amC_mem rom)
      /\ getr r 1 = at_ rb 0x4c940 /\ getr r 10 = tr /\ getr r 11 = szw
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
    - an K67770 D_4c834.                                   (* [comment removed for export] *)
      ab_ft K67774 D_4c838 ltac:(condz).                  (* [comment removed for export] *)
      av K67778 D_4c83c (at_ m (rz n)) ltac:(rewrite v_add_at by lia; reflexivity).   (* [comment removed for export] *)
      an K6777c D_4c840.                                   (* [comment removed for export] *)
      replace (v_and (at_ m (rz n)) (Z_to_bv 64 7)) with (Z_to_bv 64 0)
        by (symmetry; (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end); unorm; rewrite at_u by lia; f_equal; change 7%Z with (Z.ones 3); rewrite Z.land_ones by lia; exact Hp8).
      av K67780 D_4c844 (Z_to_bv 64 (needed n + U m)) ltac:(vz).   (* [comment removed for export] *)
      ab_tk K67784 D_4c848 ltac:(condz).                  (* [comment removed for export] *)
      av K67790 D_4c854 (at_ m (rz n + n)) ltac:(rewrite v_add_at by lia; rewrite at_at; reflexivity).   (* [comment removed for export] *)
      ab_ft K67794 D_4c858 ltac:(condz).                  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lbu with (b := b1); [exact K67798 | reflexivity | exact D_4c85c
          | gres; rwH; imm_norm; rewrite ?at_addi; rewrite <- Rb1; f_equal; f_equal; lia]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      an K6779c D_4c860.                                   (* [comment removed for export] *)
      an K677a0 D_4c864.                                   (* [comment removed for export] *)
      an K677a4 D_4c868.                                   (* [comment removed for export] *)
      change (v_or (v_andi (Z_to_bv 64 (U b1)) (-4)) (Z_to_bv 64 1)) with (hb0w (Z_to_bv 64 (U b1))).
      av K677a8 D_4c86c (Z_to_bv 64 0) ltac:(cbv delta [v_srli] beta; rewrite Z.shiftr_div_pow2 by lia; unorm; f_equal; apply Z.div_small; lia).  (* [comment removed for export] *)
      av K677ac D_4c870 (Z_to_bv 64 0) ltac:(cbv delta [v_srli] beta; rewrite Z.shiftr_div_pow2 by lia; unorm; f_equal; apply Z.div_small; lia).  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sb_at with (a := at_ m (rz n - 15)) (b := Z_to_bv 8 (U (hb0w (Z_to_bv 64 (U b1)))));
          [exact K677b0 | reflexivity | exact D_4c874 | gres; rwH; imm_norm; rewrite ?at_addi; f_equal; lia | gres; rwH; reflexivity | reflexivity | sok16 SOKh]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      change (wbytes mem _ _) with M1.
      chain_step; [reflexivity
        | eapply step_sh_at with (a := at_ m (rz n - 14)) (v := Z_to_bv 64 0);
          [exact K677b4 | reflexivity | exact D_4c878 | gres; rwH; imm_norm; rewrite ?at_addi; f_equal; lia | gres; rwH; reflexivity | sok16 SOK1]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      change (wbytes M1 _ _) with M2.
      chain_step; [reflexivity
        | eapply step_sw_at with (a := at_ m (rz n - 12)) (v := Z_to_bv 64 n);
          [exact K677b8 | reflexivity | exact D_4c87c | gres; rwH; imm_norm; rewrite ?at_addi; f_equal; lia | gres; rwH; reflexivity | sok16 SOK2]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      change (wbytes M2 _ _) with M3.
      ab_ft K677bc D_4c880 ltac:(condz).                  (* [comment removed for export] *)
      av K677c0 D_4c884 (at_ m (rz n - 16)) ltac:(rewrite at_addi; f_equal; lia).   (* [comment removed for export] *)
      an K677c4 D_4c888.                                   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 (Z_to_bv 64 16)) (v := Z_to_bv 64 16);
          [exact K677c8 | reflexivity | exact D_4c88c | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi; fold_at_vars; exact R16' | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      an K677cc D_4c890.                                   (* [comment removed for export] *)
      change (v_or (v_andi (hb0w (Z_to_bv 64 (U b1))) 143) (Z_to_bv 64 16)) with (hb1w (Z_to_bv 64 (U b1))).
      chain_step; [reflexivity
        | eapply step_sb_at with (a := at_ m (rz n - 15)) (b := Z_to_bv 8 (U (hb1w (Z_to_bv 64 (U b1)))));
          [exact K677d0 | reflexivity | exact D_4c894 | gres; rwH; imm_norm; rewrite ?at_addi; f_equal; lia | gres; rwH; reflexivity | reflexivity | sok16 SOK3]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      change (wbytes M3 _ _) with amC_mem.
      ab_ft K677d4 D_4c898 ltac:(condz).                  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 ctx) (v := ctx);
          [exact K677d8 | reflexivity | exact D_4c89c | gres; rwH; imm_norm; rewrite ?v_addi_0; exact Rctx' | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 tid)) (v := Z_to_bv 64 tid);
          [exact K677dc | reflexivity | exact D_4c8a0 | gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; exact Rtid' | apply bytes4_small; lia]
        | step_simpl]; rewrite (v_lw_small tid) by lia; vn.    (* [comment removed for export] *)
      av K677e0 D_4c8a4 (Z_to_bv 64 (tid * 2 ^ 32)) ltac:(vz).   (* [comment removed for export] *)
      an K677e4 D_4c8a8.                                   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 tr) (v := tr);
          [exact K67870 | reflexivity | exact D_4c934 | gres; rwH; imm_norm; rewrite ?v_addi_0; exact Rtr' | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := bsz) (v := szw);
          [exact K67874 | reflexivity | exact D_4c938 | gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; exact Rsz' | exact (proj1 Hbsz)]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      an K67878 D_4c93c.                                   (* [comment removed for export] *)
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
  Hypothesis GLSB : gload segs rb 0x4c954 10 gSB.
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
    exists r, msteps segs (mkst r0 (at_ rb 0x4c940) M rom) (mkst r (at_ rb 0x4ca38) (amD_mem M id) rom)
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
    - av K6787c D_4c940 (Z_to_bv 64 (id * 2 ^ 32)) ltac:(vz).            (* [comment removed for export] *)
      av K67880 D_4c944 (Z_to_bv 64 id) ltac:(cbv delta [v_srli] beta; rewrite Z.shiftr_div_pow2 by lia; unorm; f_equal; apply Z.div_mul; lia).  (* [comment removed for export] *)
      an K67884 D_4c948.                                                   (* [comment removed for export] *)
      rewrite (v_or_shl (Z_to_bv 64 id) tid 32) by (wd_ulia).
      replace (tid * 2 ^ 32 + U (Z_to_bv 64 id))%Z with (tid * 2 ^ 32 + id)%Z by (unorm; reflexivity).
      chain_step; [reflexivity
        | eapply step_sd_at with (a := at_ m (rz n - 8));
          [exact K67888 | reflexivity | exact D_4c94c | gres; rwH; imm_norm; rewrite ?at_addi; f_equal; lia | gres; rwH; reflexivity
          | eapply (store_ok_sub segs _ (at_ m (rz n - 16)) _ 16); [rewrite at_u; lia | exact SOK | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia] ]
        | step_simpl]; vn.                                                 (* [comment removed for export] *)
      change (wbytes M _ _) with M'.
      ab_ft K6788c D_4c950 ltac:(condz).                                  (* [comment removed for export] *)
      eapply msteps_trans; [apply (GLSB _ M' rom psb Rg')|]. zlit_at.      (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 (Z_to_bv 64 SB)) (v := Z_to_bv 64 SB);
          [exact K67898 | reflexivity | exact D_4c95c | gres; rwH; imm_norm; rewrite ?v_addi_0; exact Rp' | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                                 (* [comment removed for export] *)
      av K6789c D_4c960 (Z_to_bv 64 (U m / 8)) ltac:(cbv delta [v_srli] beta; rewrite Z.shiftr_div_pow2 by lia; reflexivity).   (* [comment removed for export] *)
      av K678a0 D_4c964 (Z_to_bv 64 (SB + U m / 8)) ltac:(vz).            (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lbu with (b := sb0); [exact K678a4 | reflexivity | exact D_4c968
          | gres; rwH; imm_norm; rewrite ?v_addi_0; exact Rs']
        | step_simpl]; vn.                                                 (* [comment removed for export] *)
      ab_tk K678a8 D_4c96c ltac:(condz).                                  (* [comment removed for export] *)
      an K67968 D_4ca2c.                                                   (* [comment removed for export] *)
      an K6796c D_4ca30.                                                   (* [comment removed for export] *)
      an K67970 D_4ca34.                                                   (* [comment removed for export] *)
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
    msteps segs (mkst r0 (at_ rb 0x4ca38) M rom) (mkst r0 (at_ rb 0x4ca4c) M rom).
  Proof using Hbsz Hn bsz szw m HAL2.
    intros M r0 Hn8 R22. assert (E : (n - n mod 8 = 0)%Z) by (rewrite (Z.mod_small n 8) by lia; lia).
    ab_tk K67974 D_4ca38 ltac:(rewrite E; condz). wd_refl.
  Qed.
  Lemma amD2 : forall (M : word -> option byte) r0,
    (8 <= n)%Z -> getr r0 22 = Z_to_bv 64 (n - n mod 8) -> getr r0 20 = at_ m (rz n) ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4ca38) M rom) (mkst r (at_ rb 0x70080) M rom)
      /\ getr r 1 = at_ rb 0x4ca4c /\ getr r 10 = at_ m (rz n) /\ getr r 11 = Z_to_bv 64 (n - n mod 8) /\ getr r 12 = Z_to_bv 64 0
      /\ regs_agree (fun x => In x [1; 10; 11; 12]) r0 r.
  Proof using Hbsz Gm Hn bsz szw HAL2.
    intros M r0 Hn8 R22 R20. pose proof (Z.mod_pos_bound n 8 ltac:(lia)).
    wd_eexists. split.
    - ab_ft K67974 D_4ca38 ltac:(condz).                  (* [comment removed for export] *)
      an K67978 D_4ca3c. an K6797c D_4ca40. an K67980 D_4ca44.   (* [comment removed for export] *)
      an K67984 D_4ca48.                                   (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.

  (* [comment removed for export] *)
  Variables (g_cpm gMB gME gHE gFL : Z) (pmb pme phe pfl : word) (midend : word) (pp : byte).
  Hypothesis CPM : code_ato segs rb 0x7006c cpm_words.
  Hypothesis GCPM : gloadb segs rb 0x7006c 10 g_cpm.
  Hypothesis GLSB2 : gload segs rb 0x4ca58 10 gSB.
  Hypothesis GLMB : gload segs rb 0x4ca7c 12 gMB.
  Hypothesis GLME : gload segs rb 0x4ca84 13 gME.
  Hypothesis GLHE : gload segs rb 0x4caa0 13 gHE.
  Hypothesis GLFL : gload segs rb 0x4cabc 11 gFL.
  (* [comment removed for export] *)
  Hypothesis Gcells : Forall (fun c => AIMGLO <= c /\ c + 8 <= AIMGHI)%Z [g_cpm; gMB; gME; gHE; gFL] /\ (AIMGLO <= U pmb /\ U pmb + 8 <= AIMGHI)%Z /\ (AIMGLO <= U pme /\ U pme + 8 <= AIMGHI)%Z
                      /\ (AIMGLO <= U phe /\ U phe + 8 <= AIMGHI)%Z /\ (AIMGLO <= U pfl /\ U pfl + 128 <= AIMGHI)%Z.
  Hypothesis Ghi : (0x10007fff8000 <= U m)%Z.          (* [comment removed for export] *)

  Lemma amE1z : forall (M : word -> option byte) r0,
    (n mod 8 = 0)%Z -> getr r0 9 = Z_to_bv 64 n -> getr r0 22 = Z_to_bv 64 (n - n mod 8) ->
    msteps segs (mkst r0 (at_ rb 0x4ca4c) M rom) (mkst r0 (at_ rb 0x4cae0) M rom).
  Proof using Hbsz Hn bsz szw m HAL2.
    intros M r0 Hm R9 R22. ab_tk K67988 D_4ca4c ltac:(rewrite Hm, Z.sub_0_r; condz). wd_refl.
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
    exists r, msteps segs (mkst r0 (at_ rb 0x4ca4c) M rom) (mkst r (at_ rb 0x4cae0) (amE1_mem M) rom)
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
    destruct (cpm_run segs rb g_cpm CPM GCPM M rom (regupd r0 1 (at_ rb 0x4ca54)) (at_ rb 0x4ca54) Rcpm) as (r1 & RUN1 & A10 & AG1).
    { apply ret_ok_at; [exact (proj1 RB) | reflexivity | pose proof (u64_range rb); pose proof (proj2 RB); lia]. }
    { gres. reflexivity. }
    assert (B20 : getr r1 20 = at_ m (rz n)) by (rewrite (AG1 20) by notin_list; gres; exact R20).
    assert (B22 : getr r1 22 = Z_to_bv 64 (n - n mod 8)) by (rewrite (AG1 22) by notin_list; gres; exact R22).
    assert (B9 : getr r1 9 = Z_to_bv 64 n) by (rewrite (AG1 9) by notin_list; gres; exact R9).
    wd_eexists. split.
    - ab_ft K67988 D_4ca4c ltac:(condz).                  (* [comment removed for export] *)
      an K6798c D_4ca50.                                   (* [comment removed for export] *)
      eapply msteps_trans; [exact RUN1|].
      ab_ft K67990 D_4ca54 ltac:(condz).                  (* [comment removed for export] *)
      eapply msteps_trans; [apply (GLSB2 _ M rom psb RgSB)|]. zlit_at.   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 (Z_to_bv 64 SB)) (v := Z_to_bv 64 SB);
          [exact K6799c | reflexivity | exact D_4ca60 | gres; rwH; imm_norm; rewrite ?v_addi_0; exact RSB | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      av K679a0 D_4ca64 (Z_to_bv 64 e) ltac:((lazymatch goal with |- ?G => let G' := eval unfold e in G in change_no_check G' end); cbv delta [v_add] beta; rewrite at_u by lia; unorm; f_equal; lia).  (* [comment removed for export] *)
      av K679a4 D_4ca68 (Z_to_bv 64 (SB - 1)) ltac:(vz).  (* [comment removed for export] *)
      an K679a8 D_4ca6c.                                   (* [comment removed for export] *)
      replace (v_sltu (Z_to_bv 64 SB) (Z_to_bv 64 (SB - 1))) with (Z_to_bv 64 0)
        by ((lazymatch goal with |- ?G => let G' := eval unfold v_sltu, c_ltu, bv_ltu in G in change_no_check G' end); unorm; replace (SB <? SB - 1)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
      an K679ac D_4ca70.                                   (* [comment removed for export] *)
      an K679b0 D_4ca74.                                   (* [comment removed for export] *)
      replace (v_and (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 (SB - 1))) with (Z_to_bv 64 (SB - 1))
        by (symmetry; (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end); unorm; f_equal; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_comm, Z.land_ones by lia; apply Z.mod_small; lia).
      ab_ft K679b4 D_4ca78 ltac:(condz).                  (* [comment removed for export] *)
      eapply msteps_trans; [apply (GLMB _ M rom pmb RgMB)|]. zlit_at.   (* [comment removed for export] *)
      eapply msteps_trans; [apply (GLME _ M rom pme RgME)|]. zlit_at.   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
          [exact K679c8 | reflexivity | exact D_4ca8c | gres; rwH; imm_norm; rewrite ?v_addi_0; exact RMB | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 midend) (v := midend);
          [exact K679cc | reflexivity | exact D_4ca90 | gres; rwH; imm_norm; rewrite ?v_addi_0; exact RME | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      an K679d0 D_4ca94.                                   (* [comment removed for export] *)
      ab_tk K679d4 D_4ca98 ltac:(condz).                  (* [comment removed for export] *)
      eapply msteps_trans; [apply (GLHE _ M rom phe RgHE)|]. zlit_at.   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 (Z_to_bv 64 0x7fffffffffff)) (v := Z_to_bv 64 0x7fffffffffff);
          [exact K679e4 | reflexivity | exact D_4caa8 | gres; rwH; imm_norm; rewrite ?v_addi_0; exact RHE | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      an K679e8 D_4caac.                                   (* [comment removed for export] *)
      av K679ec D_4cab0 (Z_to_bv 64 (0xfffffffffff + SB)) ltac:(vz).   (* [comment removed for export] *)
      ab_ft K679f0 D_4cab4 ltac:(condz).                  (* [comment removed for export] *)
      ab_ft K679f4 D_4cab8 ltac:(condz).                  (* [comment removed for export] *)
      eapply msteps_trans; [apply (GLFL _ M rom pfl RgFL)|]. zlit_at.   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lbu with (b := Z_to_bv 8 1); [exact K67a00 | reflexivity | exact D_4cac4
          | gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; exact Rpp]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      av K67a04 D_4cac8 (Z_to_bv 64 (e / 8)) ltac:(cbv delta [v_srli] beta; rewrite Z.shiftr_div_pow2 by lia; unorm; reflexivity).  (* [comment removed for export] *)
      av K67a08 D_4cacc (Z_to_bv 64 (SB + e / 8)) ltac:(vz).   (* [comment removed for export] *)
      an K67a0c D_4cad0.                                   (* [comment removed for export] *)
      an K67a10 D_4cad4.                                   (* [comment removed for export] *)
      replace (v_and (Z_to_bv 64 n) (Z_to_bv 64 18446744073709551615)) with (Z_to_bv 64 n)
        by (symmetry; (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end); unorm; f_equal; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
      av K67a14 D_4cad8 (Z_to_bv 64 (n mod 8)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end); unorm; f_equal; change (bv_wrap 64 7) with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sb_at with (a := Z_to_bv 64 (SB + e / 8)) (b := Z_to_bv 8 (n mod 8));
          [exact K67a18 | reflexivity | exact D_4cadc | gres; rwH; imm_norm; rewrite ?v_addi_0; reflexivity | gres; rwH; reflexivity | unorm; reflexivity | exact SOK]
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
  Hypothesis GLFL3 : gload segs rb 0x4cc40 10 gFL3.
  Hypothesis GLRMS : gload segs rb 0x4cc5c 11 gRMS.
  Hypothesis Gcells2 : (AIMGLO <= gFL3 /\ gFL3 + 8 <= AIMGHI)%Z /\ (AIMGLO <= gRMS /\ gRMS + 8 <= AIMGHI)%Z /\ (AIMGLO <= U prms /\ U prms + 8 <= AIMGHI)%Z /\ (0 <= fillw < 2 ^ 31)%Z.
  Hypothesis Gthr2 : (U thr + 4096 <= U sp)%Z.
  Hypothesis MSOK : ret_ok msetw.

  Definition amE2a_mem (M : word -> option byte) (w0 w8 w16 : word) : word -> option byte :=
    wbytes (wbytes (wbytes M (at_ thr 2800) (LE8 w0)) (at_ thr 2808) (LE8 w8)) (at_ thr 2816) (LE8 w16).

  Lemma amE2a : forall (M : word -> option byte) r0 (v0 v8 v16 : word),
    getr r0 10 = at_ thr 2800 -> getr r0 9 = Z_to_bv 64 n -> getr r0 19 = Z_to_bv 64 (needed n) ->
    rdn segs M (at_ thr 2800) 8 = Some (LE8 v0) -> rdn segs M (at_ thr 2808) 8 = Some (LE8 v8) -> rdn segs M (at_ thr 2816) 8 = Some (LE8 v16) ->
    store_ok segs M (at_ thr 2800) 24 = true ->
    exists r w0 w8 w16, msteps segs (mkst r0 (at_ rb 0x4cae4) M rom) (mkst r (at_ rb 0x4cb38) (amE2a_mem M w0 w8 w16) rom)
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
          [exact K67a20 | reflexivity | exact D_4cae4 | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi; zlit_at; exact Rv16 | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 v0) (v := v0);
          [exact K67a24 | reflexivity | exact D_4cae8 | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi, ?at_add_0_r; zlit_at; exact Rv0 | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 v8) (v := v8);
          [exact K67a28 | reflexivity | exact D_4caec | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi; zlit_at; exact Rv8 | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      av K67a2c D_4caf0 (Z_to_bv 64 (needed n - n)) ltac:(vz).   (* [comment removed for export] *)
      an K67a30 D_4caf4. setlast.                          (* [comment removed for export] *)
      an K67a34 D_4caf8. an K67a38 D_4cafc.               (* [comment removed for export] *)
      an K67a3c D_4cb00. setlast.                          (* [comment removed for export] *)
      an K67a40 D_4cb04. setlast.                          (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sd_at with (a := at_ thr 2800);
          [exact K67a44 | reflexivity | exact D_4cb08 | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi, ?at_add_0_r; reflexivity | gres; rwH; reflexivity | sok24 SOK]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sd_at with (a := at_ thr 2808);
          [exact K67a48 | reflexivity | exact D_4cb0c | gres; rwH; imm_norm; rewrite ?at_addi; reflexivity | gres; rwH; reflexivity | sok24 SOK]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sd_at with (a := at_ thr 2816);
          [exact K67a4c | reflexivity | exact D_4cb10 | gres; rwH; imm_norm; rewrite ?at_addi; reflexivity | gres; rwH; reflexivity | sok24 SOK]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      lazymatch goal with |- msteps _ (mkst _ _ (wbytes (wbytes (wbytes M _ (word_to_le_bytes 8 ?a)) _ (word_to_le_bytes 8 ?b)) _ (word_to_le_bytes 8 ?c)) _) _ =>
        change (wbytes (wbytes (wbytes M _ _) _ _) _ _) with (amE2a_mem M a b c) end.
      ab_tk K67a50 D_4cb14 ltac:(condz).                  (* [comment removed for export] *)
      an K67a6c D_4cb30.                                   (* [comment removed for export] *)
      an K67a70 D_4cb34.                                   (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.

  Lemma amE2lo : forall (M : word -> option byte) r0,
    (needed n <= 512)%Z -> getr r0 11 = Z_to_bv 64 512 -> getr r0 19 = Z_to_bv 64 (needed n) ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4cb38) M rom) (mkst r (at_ rb 0x4cc24) M rom)
      /\ getr r 11 = Z_to_bv 64 (class_of (needed n))
      /\ regs_agree (fun x => In x [11; 12; 13; 14; 15; 16]) r0 r.
  Proof using Hbsz Hn bsz szw m HAL2.
    intros M r0 Hle R11 R19. destruct (needed_facts n Hn) as [NF1 NF2].
    wd_eexists. split.
    - ab_ft K67a74 D_4cb38 ltac:(condz).                  (* [comment removed for export] *)
      av K67a78 D_4cb3c (Z_to_bv 64 (needed n + 31)) ltac:(vz).        (* [comment removed for export] *)
      av K67a7c D_4cb40 (Z_to_bv 64 ((needed n + 31) / 32)) ltac:(vz). (* [comment removed for export] *)
      an K67a80 D_4cb44.                                   (* [comment removed for export] *)
      wd_refl.
    - post; [|ra_solve]. (lazymatch goal with |- ?G => let G' := eval unfold class_of in G in change_no_check G' end). replace (needed n <=? 512)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
  Qed.

  Lemma amE2hi : forall (M : word -> option byte) r0,
    (512 < needed n)%Z -> getr r0 11 = Z_to_bv 64 512 -> getr r0 19 = Z_to_bv 64 (needed n) ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4cb38) M rom) (mkst r (at_ rb 0x4cc24) M rom)
      /\ getr r 11 = Z_to_bv 64 (class_of (needed n))
      /\ regs_agree (fun x => In x [11; 12; 13; 14; 15; 16]) r0 r.
  Proof using Hbsz Hn bsz szw m HAL2.
    intros M r0 Hgt R11 R19. destruct (needed_facts n Hn) as [NF1 NF2].
    wd_eexists. split.
    - ab_tk K67a74 D_4cb38 ltac:(condz).                  (* [comment removed for export] *)
      anlc K67a84 D_4cb48 (cidv_a2_1 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67a88 D_4cb4c (cidv_a5_1 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67a8c D_4cb50 (cidv_a6_1 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67a90 D_4cb54 (cidv_a7_1 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67a94 D_4cb58 (cidv_t0_1 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67a98 D_4cb5c (cidv_a2_2 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67a9c D_4cb60 (cidv_a5_2 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67aa0 D_4cb64 (cidv_a6_2 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67aa4 D_4cb68 (cidv_a7_2 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67aa8 D_4cb6c (cidv_t0_2 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67aac D_4cb70 (cidv_t1_1 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67ab0 D_4cb74 (cidv_a2_3 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67ab4 D_4cb78 (cidv_t1_2 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67ab8 D_4cb7c (cidv_a5_3 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67abc D_4cb80 (cidv_t1_3 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67ac0 D_4cb84 (cidv_a6_3 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67ac4 D_4cb88 (cidv_t1_4 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67ac8 D_4cb8c (cidv_a7_3 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67acc D_4cb90 (cidv_t1_5 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67ad0 D_4cb94 (cidv_t0_3 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67ad4 D_4cb98 (cidv_t1_6 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67ad8 D_4cb9c (cidv_a2_4 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67adc D_4cba0 (cidv_t1_7 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67ae0 D_4cba4 (cidv_a2_5 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67ae4 D_4cba8 (cidv_t1_8 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67ae8 D_4cbac (cidv_a2_6 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67aec D_4cbb0 (cidv_t1_9 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67af0 D_4cbb4 (cidv_a2_7 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67af4 D_4cbb8 (cidv_a2_8 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67af8 D_4cbbc (cidv_t1_10 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67afc D_4cbc0 (cidv_a5_4 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67b00 D_4cbc4 (cidv_a2_9 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67b04 D_4cbc8 (cidv_a5_5 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67b08 D_4cbcc (cidv_a2_10 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67b0c D_4cbd0 (cidv_a2_11 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67b10 D_4cbd4 (cidv_a2_12 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67b14 D_4cbd8 (cidv_a5_6 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67b18 D_4cbdc (cidv_a2_13 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67b1c D_4cbe0 (cidv_a5_7 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67b20 D_4cbe4 (cidv_a2_14 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67b24 D_4cbe8 (cidv_a6_4 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67b28 D_4cbec (cidv_a2_15 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67b2c D_4cbf0 (cidv_a2_16 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67b30 D_4cbf4 (cidv_a5_8 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67b34 D_4cbf8 (cidv_a2_17 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67b38 D_4cbfc (cidv_a7_4 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67b3c D_4cc00 (cidv_a5_9 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67b40 D_4cc04 (cidv_a2_18 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67b44 D_4cc08 (cidv_a6_5 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67b48 D_4cc0c (cidv_a5_10 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67b4c D_4cc10 (cidv_a4_1 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67b50 D_4cc14 (cidv_a2_19 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67b54 D_4cc18 (cidv_a4_2 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67b58 D_4cc1c (cidv_a2_20 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
      anlc K67b5c D_4cc20 (cidv_s0_1 (Z_to_bv 64 (needed n))).   (* [comment removed for export] *)
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
    exists r wc, msteps segs (mkst r0 (at_ rb 0x4cc24) M rom) (mkst r msetw (wbytes M (at_ thr (2912 + 8 * c)) (LE8 wc)) rom)
      /\ getr r 1 = at_ rb 0x4cc74 /\ getr r 10 = at_ m (rz n) /\ getr r 11 = Z_to_bv 64 fillw /\ getr r 12 = Z_to_bv 64 (Z.min n 4096)
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
    assert (W1 : exists r1 wc, msteps segs (mkst r0 (at_ rb 0x4cc24) M rom) (mkst r1 (at_ rb 0x4cc54) (M' wc) rom)
               /\ getr r1 10 = pfl /\ getr r1 11 = Z_to_bv 64 4096 /\ getr r1 12 = Z_to_bv 64 n /\ getr r1 9 = Z_to_bv 64 n
               /\ getr r1 20 = at_ m (rz n) /\ getr r1 2 = sp
               /\ regs_agree (fun x => In x [1; 10; 11; 12; 13]) r0 r1).
    { eexists _, _. split.
      - av K67b60 D_4cc24 (Z_to_bv 64 (8 * c)) ltac:(vz).                   (* [comment removed for export] *)
        av K67b64 D_4cc28 (at_ thr (2912 + 8 * c)) ltac:(rewrite v_add_at by lia; rewrite at_at; reflexivity).   (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_ld with (bs := LE8 vbs) (v := vbs);
            [exact K67b68 | reflexivity | exact D_4cc2c | gres; rwH; imm_norm; rewrite ?v_addi_0; exact Rbs | apply bytes_le_to_Z_8]
          | step_simpl]; vn.                                                (* [comment removed for export] *)
        an K67b6c D_4cc30. setlast.                                         (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sd_at with (a := at_ thr (2912 + 8 * c));
            [exact K67b70 | reflexivity | exact D_4cc34 | gres; rwH; imm_norm; rewrite ?v_addi_0; reflexivity | gres; rwH; reflexivity | exact SOKbs]
          | step_simpl]; vn.                                                (* [comment removed for export] *)
        lazymatch goal with |- msteps _ (mkst _ _ (wbytes M _ (word_to_le_bytes 8 ?a)) _) _ => change (wbytes M _ _) with (M' a) end.
        chain_step; [reflexivity
          | eapply step_ld with (bs := LE8 (Z_to_bv 64 1)) (v := Z_to_bv 64 1);
            [exact K67b74 | reflexivity | exact D_4cc38 | gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; apply Rfill' | apply bytes_le_to_Z_8]
          | step_simpl]; vn.                                                (* [comment removed for export] *)
        ab_ft K67b78 D_4cc3c ltac:(condz).                                 (* [comment removed for export] *)
        eapply msteps_trans; [apply (GLFL3 _ _ rom pfl); apply RgFL'|]. zlit_at.   (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 4096)) (v := Z_to_bv 64 4096);
            [exact K67b84 | reflexivity | exact D_4cc48 | gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; apply Rmmf' | apply bytes4_small; lia]
          | step_simpl]; rewrite (v_lw_small 4096) by lia; vn.              (* [comment removed for export] *)
        ab_ft K67b88 D_4cc4c ltac:(condz).                                 (* [comment removed for export] *)
        an K67b8c D_4cc50.                                                  (* [comment removed for export] *)
        wd_refl.
      - post. ra_solve. }
    destruct W1 as (r1 & wc & RUN1 & A10 & A11 & A12 & A9 & A20 & A2 & AG1).
    (* [comment removed for export] *)
    assert (W2 : exists r2, msteps segs (mkst r1 (at_ rb 0x4cc54) (M' wc) rom) (mkst r2 (at_ rb 0x4cc5c) (M' wc) rom)
               /\ getr r2 12 = Z_to_bv 64 (Z.min n 4096) /\ (forall i : reg, i <> 12 -> getr r2 i = getr r1 i)).
    { destruct (Z.lt_ge_cases n 4096) as [Hlt|Hge].
      - wd_eexists. split; [ab_tk K67b90 D_4cc54 ltac:(condz); wd_refl|].
        split; [rewrite Z.min_l by lia; exact A12 | intros i Hi; reflexivity].
      - wd_eexists. split; [ab_ft K67b90 D_4cc54 ltac:(condz); an K67b94 D_4cc58; wd_refl|].
        split; [gres; rewrite Z.min_r by lia; rewrite ?v_addi_0; reflexivity | intros i Hi; rewrite getr_other by (intros E; apply Hi; exact E); reflexivity]. }
    destruct W2 as (r2 & RUN2 & B12 & BK).
    eexists _, wc. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
      eapply msteps_trans; [apply (GLRMS _ _ rom prms); apply RgRMS'|]. zlit_at.   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 msetw) (v := msetw);
          [exact K67ba0 | reflexivity | exact D_4cc64 | gres; rwH; imm_norm; rewrite ?v_addi_0; apply Rrms' | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                                  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 fillw)) (v := Z_to_bv 64 fillw);
          [exact K67ba4 | reflexivity | exact D_4cc68 | gres; rewrite (BK 10) by (intros E; discriminate E); rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; apply Rfb' | apply bytes4_small; lia]
        | step_simpl]; rewrite (v_lw_small fillw) by lia; vn.                (* [comment removed for export] *)
      an K67ba8 D_4cc6c.                                                    (* [comment removed for export] *)
      aret K67bac D_4cc70 msetw.                                            (* [comment removed for export] *)
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
