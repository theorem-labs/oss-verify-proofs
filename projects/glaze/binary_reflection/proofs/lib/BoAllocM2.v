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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia HsLia.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | hs_am_lia ].   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation LE2 z := (word_to_le_bytes 2 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1.
Context {fx : FPState}.

Definition am_words : list (option (bv 32)) :=
  [Some W_4c538; Some W_4c53c; Some W_4c540; Some W_4c544; Some W_4c548; None; Some W_4c550; Some W_4c554; None;
   Some W_4c55c; Some W_4c560; Some W_4c564; Some W_4c568; Some W_4c56c; Some W_4c570; Some W_4c574; Some W_4c578;
   Some W_4c57c; Some W_4c580; Some W_4c584; Some W_4c588; Some W_4c58c; Some W_4c590]%list.
Definition al_words : list (option (bv 32)) :=
  [Some W_4c594; Some W_4c598; Some W_4c59c; Some W_4c5a0; Some W_4c5a4; Some W_4c5a8; Some W_4c5ac; Some W_4c5b0;
   Some W_4c5b4; Some W_4c5b8; Some W_4c5bc; Some W_4c5c0; Some W_4c5c4; Some W_4c5c8; Some W_4c5cc; Some W_4c5d0;
   Some W_4c5d4; Some W_4c5d8; Some W_4c5dc; Some W_4c5e0; Some W_4c5e4; Some W_4c5e8; Some W_4c5ec; Some W_4c5f0;
   Some W_4c5f4; Some W_4c5f8; Some W_4c5fc; Some W_4c600; Some W_4c604; Some W_4c608; Some W_4c60c; Some W_4c610;
   Some W_4c614; Some W_4c618; Some W_4c61c; Some W_4c620; Some W_4c624; Some W_4c628; Some W_4c62c; Some W_4c630;
   Some W_4c634; Some W_4c638; Some W_4c63c; Some W_4c640; Some W_4c644; Some W_4c648; Some W_4c64c; Some W_4c650;
   None; None; Some W_4c65c; Some W_4c660; Some W_4c664; None; Some W_4c66c; None; Some W_4c674; Some W_4c678;
   Some W_4c67c; Some W_4c680; Some W_4c684; Some W_4c688; Some W_4c68c; Some W_4c690; Some W_4c694; Some W_4c698;
   Some W_4c69c; Some W_4c6a0; Some W_4c6a4; Some W_4c6a8; Some W_4c6ac; Some W_4c6b0; Some W_4c6b4; Some W_4c6b8;
   Some W_4c6bc; Some W_4c6c0; Some W_4c6c4; Some W_4c6c8; Some W_4c6cc; Some W_4c6d0; Some W_4c6d4; Some W_4c6d8;
   Some W_4c6dc; Some W_4c6e0; Some W_4c6e4; Some W_4c6e8; Some W_4c6ec; Some W_4c6f0; Some W_4c6f4; Some W_4c6f8;
   Some W_4c6fc; Some W_4c700; Some W_4c704; Some W_4c708; Some W_4c70c; Some W_4c710; Some W_4c714; Some W_4c718;
   Some W_4c71c; Some W_4c720; Some W_4c724; Some W_4c728; Some W_4c72c; Some W_4c730; Some W_4c734; Some W_4c738;
   Some W_4c73c; Some W_4c740; Some W_4c744; Some W_4c748; Some W_4c74c; Some W_4c750; Some W_4c754; Some W_4c758;
   Some W_4c75c; Some W_4c760; Some W_4c764; Some W_4c768; Some W_4c76c; Some W_4c770; Some W_4c774; Some W_4c778;
   Some W_4c77c; Some W_4c780; Some W_4c784; Some W_4c788; Some W_4c78c; Some W_4c790; Some W_4c794; Some W_4c798;
   Some W_4c79c; Some W_4c7a0; Some W_4c7a4; Some W_4c7a8; Some W_4c7ac; Some W_4c7b0; Some W_4c7b4; Some W_4c7b8;
   Some W_4c7bc; Some W_4c7c0; Some W_4c7c4; Some W_4c7c8; Some W_4c7cc; Some W_4c7d0; Some W_4c7d4; Some W_4c7d8;
   Some W_4c7dc; Some W_4c7e0; Some W_4c7e4; Some W_4c7e8; Some W_4c7ec; Some W_4c7f0; Some W_4c7f4; Some W_4c7f8;
   Some W_4c7fc; Some W_4c800; Some W_4c804; Some W_4c808; Some W_4c80c; Some W_4c810; Some W_4c814; Some W_4c818;
   Some W_4c81c; Some W_4c820; Some W_4c824; Some W_4c828; Some W_4c82c; Some W_4c830]%list.

(* [comment removed for export] *)
Lemma rz_log_cases : forall n, (1 <= n)%Z ->
  (n <= 48 /\ rz_log n = 0 \/ 49 <= n <= 96 /\ rz_log n = 1 \/ 97 <= n <= 448 /\ rz_log n = 2 \/ 449 <= n <= 3968 /\ rz_log n = 3
   \/ 3969 <= n <= 16128 /\ rz_log n = 4 \/ 16129 <= n <= 32256 /\ rz_log n = 5 \/ 32257 <= n <= 64512 /\ rz_log n = 6 \/ 64513 <= n /\ rz_log n = 7)%Z.
Proof using.
  intros n Hn. (lazymatch goal with |- ?G => let G' := eval unfold rz_log in G in change_no_check G' end).
  repeat match goal with |- context [Z.leb n ?k] => destruct (Z.leb_spec n k) end; lia.
Qed.
Lemma rz_log_range : forall n, (0 <= rz_log n <= 7)%Z.
Proof using. intros n. (lazymatch goal with |- ?G => let G' := eval unfold rz_log in G in change_no_check G' end). repeat match goal with |- context [Z.leb n ?k] => destruct (Z.leb n k) end; lia. Qed.


(* [comment removed for export] *)
Record am_tab := AMT { am_rb : word; am_inst : word; am_g_magic : Z; am_tbl2 : word; am_tbl : word; am_g_inited : Z; am_g_rss : Z }.
Record am_tab_ok (segs : list Segment) (t : am_tab) : Prop := AMTOK {
  ato_am : code_ato segs (am_rb t) 0x4c538 am_words;
  ato_al : code_ato segs (am_rb t) 0x4c594 al_words;
  ato_inst : gauipc_addi segs (am_rb t) 0x4c54c 0x4c558 10 10 (am_inst t);
  ato_mag : gload segs (am_rb t) 0x4c654 12 (am_g_magic t);
  ato_tbl2 : gauipc_addi segs (am_rb t) 0x4c668 0x4c670 12 12 (am_tbl2 t);
  ato_ain : code_ato segs (am_rb t) 0x7571c ain_words;
  ato_ainb : gloadb segs (am_rb t) 0x7571c 10 (am_g_inited t);
  ato_rss : code_ato segs (am_rb t) 0x7b3e4 rss_words;
  ato_rssb : gloadb segs (am_rb t) 0x7b3e4 10 (am_g_rss t);
  ato_rzl : code_ato segs (am_rb t) 0x51bb4 rzl_words;
  ato_rzm : gload segs (am_rb t) 0x51be8 12 (am_g_magic t);
  ato_rzt : gauipc_addi segs (am_rb t) 0x51bf0 0x51bf8 14 14 (am_tbl t);
  ato_rb : (U (am_rb t) mod 2 = 0)%Z /\ (U (am_rb t) + 2 ^ 24 < 2 ^ 64)%Z }.

(* [comment removed for export] *)
Definition am_clobx : list reg := [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31].

Section AM.
  Variable segs : list Segment.
  Variable t : am_tab.
  Hypothesis TOK : am_tab_ok segs t.
  #[local] Abbreviation rb := (am_rb t).
  #[local] Abbreviation INST := (am_inst t).
  Let HAM : code_ato segs rb 0x4c538 am_words := ato_am _ _ TOK.
  Let HAL : code_ato segs rb 0x4c594 al_words := ato_al _ _ TOK.

  Lemma I67474 : fetch_word segs (at_ rb 0x4c538) = Some W_4c538.  Proof using HAM TOK fx. exact (code_ato_get segs rb 0x4c538 am_words 0 _ HAM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67478 : fetch_word segs (at_ rb 0x4c53c) = Some W_4c53c.  Proof using HAM TOK fx. exact (code_ato_get segs rb 0x4c538 am_words 1 _ HAM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6747c : fetch_word segs (at_ rb 0x4c540) = Some W_4c540.  Proof using HAM TOK fx. exact (code_ato_get segs rb 0x4c538 am_words 2 _ HAM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67480 : fetch_word segs (at_ rb 0x4c544) = Some W_4c544.  Proof using HAM TOK fx. exact (code_ato_get segs rb 0x4c538 am_words 3 _ HAM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67484 : fetch_word segs (at_ rb 0x4c548) = Some W_4c548.  Proof using HAM TOK fx. exact (code_ato_get segs rb 0x4c538 am_words 4 _ HAM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6748c : fetch_word segs (at_ rb 0x4c550) = Some W_4c550.  Proof using HAM TOK fx. exact (code_ato_get segs rb 0x4c538 am_words 6 _ HAM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67490 : fetch_word segs (at_ rb 0x4c554) = Some W_4c554.  Proof using HAM TOK fx. exact (code_ato_get segs rb 0x4c538 am_words 7 _ HAM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67498 : fetch_word segs (at_ rb 0x4c55c) = Some W_4c55c.  Proof using HAM TOK fx. exact (code_ato_get segs rb 0x4c538 am_words 9 _ HAM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6749c : fetch_word segs (at_ rb 0x4c560) = Some W_4c560.  Proof using HAM TOK fx. exact (code_ato_get segs rb 0x4c538 am_words 10 _ HAM eq_refl). Qed.











   (* [comment removed for export] *)

  Lemma I674d0 : fetch_word segs (at_ rb 0x4c594) = Some W_4c594.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 0 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I674d4 : fetch_word segs (at_ rb 0x4c598) = Some W_4c598.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 1 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I674d8 : fetch_word segs (at_ rb 0x4c59c) = Some W_4c59c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 2 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I674dc : fetch_word segs (at_ rb 0x4c5a0) = Some W_4c5a0.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 3 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I674e0 : fetch_word segs (at_ rb 0x4c5a4) = Some W_4c5a4.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 4 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I674e4 : fetch_word segs (at_ rb 0x4c5a8) = Some W_4c5a8.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 5 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I674e8 : fetch_word segs (at_ rb 0x4c5ac) = Some W_4c5ac.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 6 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I674ec : fetch_word segs (at_ rb 0x4c5b0) = Some W_4c5b0.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 7 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I674f0 : fetch_word segs (at_ rb 0x4c5b4) = Some W_4c5b4.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 8 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I674f4 : fetch_word segs (at_ rb 0x4c5b8) = Some W_4c5b8.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 9 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I674f8 : fetch_word segs (at_ rb 0x4c5bc) = Some W_4c5bc.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 10 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I674fc : fetch_word segs (at_ rb 0x4c5c0) = Some W_4c5c0.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 11 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67500 : fetch_word segs (at_ rb 0x4c5c4) = Some W_4c5c4.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 12 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67504 : fetch_word segs (at_ rb 0x4c5c8) = Some W_4c5c8.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 13 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67508 : fetch_word segs (at_ rb 0x4c5cc) = Some W_4c5cc.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 14 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6750c : fetch_word segs (at_ rb 0x4c5d0) = Some W_4c5d0.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 15 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67510 : fetch_word segs (at_ rb 0x4c5d4) = Some W_4c5d4.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 16 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67514 : fetch_word segs (at_ rb 0x4c5d8) = Some W_4c5d8.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 17 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67518 : fetch_word segs (at_ rb 0x4c5dc) = Some W_4c5dc.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 18 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6751c : fetch_word segs (at_ rb 0x4c5e0) = Some W_4c5e0.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 19 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67520 : fetch_word segs (at_ rb 0x4c5e4) = Some W_4c5e4.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 20 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67524 : fetch_word segs (at_ rb 0x4c5e8) = Some W_4c5e8.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 21 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67528 : fetch_word segs (at_ rb 0x4c5ec) = Some W_4c5ec.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 22 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6752c : fetch_word segs (at_ rb 0x4c5f0) = Some W_4c5f0.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 23 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67530 : fetch_word segs (at_ rb 0x4c5f4) = Some W_4c5f4.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 24 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67534 : fetch_word segs (at_ rb 0x4c5f8) = Some W_4c5f8.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 25 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67538 : fetch_word segs (at_ rb 0x4c5fc) = Some W_4c5fc.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 26 _ HAL eq_refl). Qed.


   (* [comment removed for export] *)
  Lemma I67548 : fetch_word segs (at_ rb 0x4c60c) = Some W_4c60c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 30 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6754c : fetch_word segs (at_ rb 0x4c610) = Some W_4c610.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 31 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67550 : fetch_word segs (at_ rb 0x4c614) = Some W_4c614.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 32 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67554 : fetch_word segs (at_ rb 0x4c618) = Some W_4c618.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 33 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67558 : fetch_word segs (at_ rb 0x4c61c) = Some W_4c61c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 34 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6755c : fetch_word segs (at_ rb 0x4c620) = Some W_4c620.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 35 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67560 : fetch_word segs (at_ rb 0x4c624) = Some W_4c624.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 36 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67564 : fetch_word segs (at_ rb 0x4c628) = Some W_4c628.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 37 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67568 : fetch_word segs (at_ rb 0x4c62c) = Some W_4c62c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 38 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6756c : fetch_word segs (at_ rb 0x4c630) = Some W_4c630.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 39 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67570 : fetch_word segs (at_ rb 0x4c634) = Some W_4c634.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 40 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67574 : fetch_word segs (at_ rb 0x4c638) = Some W_4c638.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 41 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67578 : fetch_word segs (at_ rb 0x4c63c) = Some W_4c63c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 42 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6757c : fetch_word segs (at_ rb 0x4c640) = Some W_4c640.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 43 _ HAL eq_refl). Qed.
   (* [comment removed for export] *)
  Lemma I67584 : fetch_word segs (at_ rb 0x4c648) = Some W_4c648.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 45 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67588 : fetch_word segs (at_ rb 0x4c64c) = Some W_4c64c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 46 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6758c : fetch_word segs (at_ rb 0x4c650) = Some W_4c650.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 47 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67598 : fetch_word segs (at_ rb 0x4c65c) = Some W_4c65c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 50 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6759c : fetch_word segs (at_ rb 0x4c660) = Some W_4c660.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 51 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I675a0 : fetch_word segs (at_ rb 0x4c664) = Some W_4c664.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 52 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I675a8 : fetch_word segs (at_ rb 0x4c66c) = Some W_4c66c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 54 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I675b0 : fetch_word segs (at_ rb 0x4c674) = Some W_4c674.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 56 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I675b4 : fetch_word segs (at_ rb 0x4c678) = Some W_4c678.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 57 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I675b8 : fetch_word segs (at_ rb 0x4c67c) = Some W_4c67c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 58 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I675bc : fetch_word segs (at_ rb 0x4c680) = Some W_4c680.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 59 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I675c0 : fetch_word segs (at_ rb 0x4c684) = Some W_4c684.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 60 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I675c4 : fetch_word segs (at_ rb 0x4c688) = Some W_4c688.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 61 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I675c8 : fetch_word segs (at_ rb 0x4c68c) = Some W_4c68c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 62 _ HAL eq_refl). Qed.
   (* [comment removed for export] *)
  Lemma I675d0 : fetch_word segs (at_ rb 0x4c694) = Some W_4c694.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 64 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I675d4 : fetch_word segs (at_ rb 0x4c698) = Some W_4c698.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 65 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I675d8 : fetch_word segs (at_ rb 0x4c69c) = Some W_4c69c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 66 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I675dc : fetch_word segs (at_ rb 0x4c6a0) = Some W_4c6a0.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 67 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I675e0 : fetch_word segs (at_ rb 0x4c6a4) = Some W_4c6a4.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 68 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I675e4 : fetch_word segs (at_ rb 0x4c6a8) = Some W_4c6a8.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 69 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I675e8 : fetch_word segs (at_ rb 0x4c6ac) = Some W_4c6ac.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 70 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I675ec : fetch_word segs (at_ rb 0x4c6b0) = Some W_4c6b0.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 71 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I675f0 : fetch_word segs (at_ rb 0x4c6b4) = Some W_4c6b4.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 72 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I675f4 : fetch_word segs (at_ rb 0x4c6b8) = Some W_4c6b8.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 73 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I675f8 : fetch_word segs (at_ rb 0x4c6bc) = Some W_4c6bc.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 74 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I675fc : fetch_word segs (at_ rb 0x4c6c0) = Some W_4c6c0.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 75 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67600 : fetch_word segs (at_ rb 0x4c6c4) = Some W_4c6c4.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 76 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67604 : fetch_word segs (at_ rb 0x4c6c8) = Some W_4c6c8.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 77 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67608 : fetch_word segs (at_ rb 0x4c6cc) = Some W_4c6cc.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 78 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6760c : fetch_word segs (at_ rb 0x4c6d0) = Some W_4c6d0.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 79 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67610 : fetch_word segs (at_ rb 0x4c6d4) = Some W_4c6d4.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 80 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67614 : fetch_word segs (at_ rb 0x4c6d8) = Some W_4c6d8.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 81 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67618 : fetch_word segs (at_ rb 0x4c6dc) = Some W_4c6dc.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 82 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6761c : fetch_word segs (at_ rb 0x4c6e0) = Some W_4c6e0.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 83 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67620 : fetch_word segs (at_ rb 0x4c6e4) = Some W_4c6e4.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 84 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67624 : fetch_word segs (at_ rb 0x4c6e8) = Some W_4c6e8.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 85 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67628 : fetch_word segs (at_ rb 0x4c6ec) = Some W_4c6ec.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 86 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6762c : fetch_word segs (at_ rb 0x4c6f0) = Some W_4c6f0.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 87 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67630 : fetch_word segs (at_ rb 0x4c6f4) = Some W_4c6f4.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 88 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67634 : fetch_word segs (at_ rb 0x4c6f8) = Some W_4c6f8.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 89 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67638 : fetch_word segs (at_ rb 0x4c6fc) = Some W_4c6fc.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 90 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6763c : fetch_word segs (at_ rb 0x4c700) = Some W_4c700.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 91 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67640 : fetch_word segs (at_ rb 0x4c704) = Some W_4c704.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 92 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67644 : fetch_word segs (at_ rb 0x4c708) = Some W_4c708.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 93 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67648 : fetch_word segs (at_ rb 0x4c70c) = Some W_4c70c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 94 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6764c : fetch_word segs (at_ rb 0x4c710) = Some W_4c710.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 95 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67650 : fetch_word segs (at_ rb 0x4c714) = Some W_4c714.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 96 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67654 : fetch_word segs (at_ rb 0x4c718) = Some W_4c718.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 97 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67658 : fetch_word segs (at_ rb 0x4c71c) = Some W_4c71c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 98 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6765c : fetch_word segs (at_ rb 0x4c720) = Some W_4c720.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 99 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67660 : fetch_word segs (at_ rb 0x4c724) = Some W_4c724.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 100 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67664 : fetch_word segs (at_ rb 0x4c728) = Some W_4c728.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 101 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67668 : fetch_word segs (at_ rb 0x4c72c) = Some W_4c72c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 102 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6766c : fetch_word segs (at_ rb 0x4c730) = Some W_4c730.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 103 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67670 : fetch_word segs (at_ rb 0x4c734) = Some W_4c734.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 104 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67674 : fetch_word segs (at_ rb 0x4c738) = Some W_4c738.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 105 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67678 : fetch_word segs (at_ rb 0x4c73c) = Some W_4c73c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 106 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6767c : fetch_word segs (at_ rb 0x4c740) = Some W_4c740.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 107 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67680 : fetch_word segs (at_ rb 0x4c744) = Some W_4c744.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 108 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67684 : fetch_word segs (at_ rb 0x4c748) = Some W_4c748.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 109 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67688 : fetch_word segs (at_ rb 0x4c74c) = Some W_4c74c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 110 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6768c : fetch_word segs (at_ rb 0x4c750) = Some W_4c750.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 111 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67690 : fetch_word segs (at_ rb 0x4c754) = Some W_4c754.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 112 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67694 : fetch_word segs (at_ rb 0x4c758) = Some W_4c758.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 113 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67698 : fetch_word segs (at_ rb 0x4c75c) = Some W_4c75c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 114 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6769c : fetch_word segs (at_ rb 0x4c760) = Some W_4c760.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 115 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I676a0 : fetch_word segs (at_ rb 0x4c764) = Some W_4c764.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 116 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I676a4 : fetch_word segs (at_ rb 0x4c768) = Some W_4c768.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 117 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I676a8 : fetch_word segs (at_ rb 0x4c76c) = Some W_4c76c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 118 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I676ac : fetch_word segs (at_ rb 0x4c770) = Some W_4c770.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 119 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I676b0 : fetch_word segs (at_ rb 0x4c774) = Some W_4c774.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 120 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I676b4 : fetch_word segs (at_ rb 0x4c778) = Some W_4c778.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 121 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I676b8 : fetch_word segs (at_ rb 0x4c77c) = Some W_4c77c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 122 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I676bc : fetch_word segs (at_ rb 0x4c780) = Some W_4c780.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 123 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I676c0 : fetch_word segs (at_ rb 0x4c784) = Some W_4c784.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 124 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I676c4 : fetch_word segs (at_ rb 0x4c788) = Some W_4c788.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 125 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I676c8 : fetch_word segs (at_ rb 0x4c78c) = Some W_4c78c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 126 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I676cc : fetch_word segs (at_ rb 0x4c790) = Some W_4c790.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 127 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I676d0 : fetch_word segs (at_ rb 0x4c794) = Some W_4c794.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 128 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I676d4 : fetch_word segs (at_ rb 0x4c798) = Some W_4c798.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 129 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I676d8 : fetch_word segs (at_ rb 0x4c79c) = Some W_4c79c.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 130 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I676dc : fetch_word segs (at_ rb 0x4c7a0) = Some W_4c7a0.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 131 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I676e0 : fetch_word segs (at_ rb 0x4c7a4) = Some W_4c7a4.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 132 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I676e4 : fetch_word segs (at_ rb 0x4c7a8) = Some W_4c7a8.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 133 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I676e8 : fetch_word segs (at_ rb 0x4c7ac) = Some W_4c7ac.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 134 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I676ec : fetch_word segs (at_ rb 0x4c7b0) = Some W_4c7b0.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 135 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I676f0 : fetch_word segs (at_ rb 0x4c7b4) = Some W_4c7b4.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 136 _ HAL eq_refl). Qed.







   (* [comment removed for export] *)
  Lemma I67714 : fetch_word segs (at_ rb 0x4c7d8) = Some W_4c7d8.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 145 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67718 : fetch_word segs (at_ rb 0x4c7dc) = Some W_4c7dc.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 146 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I6771c : fetch_word segs (at_ rb 0x4c7e0) = Some W_4c7e0.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 147 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67720 : fetch_word segs (at_ rb 0x4c7e4) = Some W_4c7e4.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 148 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67724 : fetch_word segs (at_ rb 0x4c7e8) = Some W_4c7e8.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 149 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma I67728 : fetch_word segs (at_ rb 0x4c7ec) = Some W_4c7ec.  Proof using HAL TOK fx. exact (code_ato_get segs rb 0x4c594 al_words 150 _ HAL eq_refl). Qed.
















   (* [comment removed for export] *)


  Variables (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ra sp stk : word) (n : Z).
  Hypothesis Hret : ret_ok ra.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 n.
  Hypothesis H11 : getr regs 11 = stk.
  Hypothesis Hn : (1 <= n <= 64512)%Z.
  (* [comment removed for export] *)
  Variable MAG : word.
  Hypothesis Rinited : rdn segs mem (Z_to_bv 64 (am_g_inited t)) 1 = Some [Z_to_bv 8 1].
  Hypothesis Rrss : rdn segs mem (Z_to_bv 64 (am_g_rss t)) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rmag : rdn segs mem (Z_to_bv 64 (am_g_magic t)) 8 = Some (LE8 MAGICw).
  Hypothesis Rtbl2 : rdn segs mem (at_ (am_tbl2 t) 4) 1 = Some [Z_to_bv 8 3].     (* [comment removed for export] *)
  Hypothesis Rt16 : rdn segs mem (at_ (am_tbl t) 8) 1 = Some [Z_to_bv 8 4].
  Hypothesis Rt2048 : rdn segs mem (at_ (am_tbl t) 49) 1 = Some [Z_to_bv 8 11].
  Hypothesis Rminrz : rdn segs mem (at_ INST 3624) 2 = Some (LE2 16).
  Hypothesis Rmaxrz : rdn segs mem (at_ INST 3626) 2 = Some (LE2 2048).
  Hypothesis Rmaxsz : rdn segs mem (at_ INST 3616) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 40))).
  Hypothesis Hstk : store_ok segs mem (at_ sp (-160)) 160 = true.
  (* [comment removed for export] *)
  Hypothesis G0 : (0 <= am_g_inited t < 2 ^ 32)%Z /\ (0 <= am_g_rss t < 2 ^ 32)%Z /\ (0 <= am_g_magic t /\ am_g_magic t + 8 <= 2 ^ 32)%Z
            /\ (U (am_tbl2 t) + 64 <= 2 ^ 32)%Z /\ (U (am_tbl t) + 64 <= 2 ^ 32)%Z /\ (U INST + 4096 <= 2 ^ 32)%Z /\ (U stk <> 0)%Z.
  Hypothesis G1 : (2 ^ 32 + 160 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z.

  #[local] Abbreviation CLX := (fun r => In r am_clobx).

  Lemma RETa : forall d, (d mod 2 = 0)%Z -> (0 <= d < 2 ^ 24)%Z -> ret_ok (at_ rb d).
  Proof using TOK segs fx. intros d Hd Hdr. pose proof (ato_rb _ _ TOK) as [E1 E2]. pose proof (u64_range rb). apply ret_ok_at; [exact E1 | exact Hd | lia]. Qed.

  (* [comment removed for export] *)
  Definition am_m1 : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
      (at_ sp (-8)) (LE8 ra)) (at_ sp (-16)) (LE8 (getr regs 8)))
      (at_ sp (-24)) (LE8 (at_ rb 0x4c564))) (at_ sp (-32)) (LE8 (getr regs 8))) (at_ sp (-40)) (LE8 (getr regs 9)))
      (at_ sp (-48)) (LE8 (getr regs 18))) (at_ sp (-56)) (LE8 (getr regs 19))) (at_ sp (-64)) (LE8 (getr regs 20)))
      (at_ sp (-72)) (LE8 (getr regs 21))) (at_ sp (-80)) (LE8 (getr regs 22))) (at_ sp (-88)) (LE8 (getr regs 23)))
      (at_ sp (-96)) (LE8 (getr regs 24))) (at_ sp (-104)) (LE8 (getr regs 25))) (at_ sp (-112)) (LE8 (getr regs 26)))
      (at_ sp (-120)) (LE8 (getr regs 27)).
  Lemma am_m1_outside : forall x : word, (U x < U sp - 120 \/ U sp <= U x)%Z -> am_m1 x = mem x.
  Proof using G1.
    intros x Hx. pose proof (u64_range sp). destruct G1 as [G1a G1b]. (lazymatch goal with |- ?G => let G' := eval unfold am_m1 in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. reflexivity.
  Qed.

  Ltac sokS Hs lo N :=
    repeat (eapply store_ok_mono; [apply wbytes_grows|]);
    eapply (store_ok_sub segs mem lo _ N); [rewrite at_u; lia | exact Hs | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia].
  Ltac fsd8 F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | sokS Hstk (at_ sp (-160)) 160%nat ]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  Lemma amA1a :
    exists r,
      msteps segs (mkst regs (at_ rb 0x4c538) mem rom) (mkst r (at_ rb 0x7571c) am_m1 rom)
      /\ getr r 1 = at_ rb 0x4c5e8 /\ getr r 2 = at_ sp (-144) /\ getr r 9 = Z_to_bv 64 1 /\ getr r 27 = Z_to_bv 64 1 /\ getr r 23 = stk
      /\ getr r 18 = Z_to_bv 64 8 /\ getr r 21 = Z_to_bv 64 n /\ getr r 22 = INST
      /\ regs_agree CLX regs r.
  Proof using G1 G0 Hstk H11 H10 H2 H1 HAL HAM TOK.
    destruct G0 as (Ga & Gb & Gc & Gd & Ge & Gf & Gg). destruct G1 as [G1a G1b].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range stk) as Hstk'. pose proof (u64_range INST) as HI.
    destruct (ato_inst _ _ TOK) as [ix [IA IB]].
    wd_eexists. split.
    - an I67474 D_4c538.                                   (* [comment removed for export] *)
      fsd8 I67478 D_4c53c (at_ sp (-8)).                   (* [comment removed for export] *)
      fsd8 I6747c D_4c540 (at_ sp (-16)).                  (* [comment removed for export] *)
      an I67480 D_4c544. an I67484 D_4c548.               (* [comment removed for export] *)
      eapply msteps_trans; [apply IA|]. zlit_at.            (* [comment removed for export] *)
      an I6748c D_4c550. an I67490 D_4c554.               (* [comment removed for export] *)
      eapply msteps_trans; [apply IB; gres; reflexivity|]. zlit_at. rewrite ?regupd_regupd_same.   (* [comment removed for export] *)
      an I67498 D_4c55c.                                   (* [comment removed for export] *)
      an I6749c D_4c560.                                   (* [comment removed for export] *)
      an I674d0 D_4c594.                                   (* [comment removed for export] *)
      fsd8 I674d4 D_4c598 (at_ sp (-24)). fsd8 I674d8 D_4c59c (at_ sp (-32)). fsd8 I674dc D_4c5a0 (at_ sp (-40)). fsd8 I674e0 D_4c5a4 (at_ sp (-48)).
      fsd8 I674e4 D_4c5a8 (at_ sp (-56)). fsd8 I674e8 D_4c5ac (at_ sp (-64)). fsd8 I674ec D_4c5b0 (at_ sp (-72)). fsd8 I674f0 D_4c5b4 (at_ sp (-80)).
      fsd8 I674f4 D_4c5b8 (at_ sp (-88)). fsd8 I674f8 D_4c5bc (at_ sp (-96)). fsd8 I674fc D_4c5c0 (at_ sp (-104)). fsd8 I67500 D_4c5c4 (at_ sp (-112)).
      fsd8 I67504 D_4c5c8 (at_ sp (-120)).
      change (wbytes _ _ _) with am_m1.
      an I67508 D_4c5cc. an I6750c D_4c5d0. an I67510 D_4c5d4. an I67514 D_4c5d8. an I67518 D_4c5dc. an I6751c D_4c5e0.   (* [comment removed for export] *)
      an I67520 D_4c5e4.                                   (* [comment removed for export] *)
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end). ra_solve.
  Qed.

  Lemma v_sltu_lit : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
    v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (if (a <? b)%Z then 1 else 0).
  Proof using. intros a b Ha Hb. (lazymatch goal with |- ?G => let G' := eval unfold v_sltu, c_ltu, bv_ltu in G in change_no_check G' end). unorm. destruct (a <? b)%Z; reflexivity. Qed.

  (* [comment removed for export] *)
  Definition am_m2 : word -> option byte := wbytes (wbytes am_m1 (at_ sp (-136)) (LE8 (Z_to_bv 64 1))) (at_ sp (-128)) (LE8 (Z_to_bv 64 16)).
  Definition am_m3 : word -> option byte := wbytes (wbytes am_m2 (at_ sp (-152)) (LE8 (at_ rb 0x4c718))) (at_ sp (-152)) (LE8 (at_ rb 0x4c72c)).
  #[local] Hint Unfold am_m1 am_m2 am_m3 : asfr.
  Lemma am_m2_outside : forall x : word, (U x < U sp - 136 \/ U sp <= U x)%Z -> am_m2 x = mem x.
  Proof using G1.
    intros x Hx. pose proof (u64_range sp). destruct G1 as [G1a G1b]. (lazymatch goal with |- ?G => let G' := eval unfold am_m2 in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. apply am_m1_outside. lia.
  Qed.
  Lemma am_m3_outside : forall x : word, (U x < U sp - 152 \/ U sp <= U x)%Z -> am_m3 x = mem x.
  Proof using G1.
    intros x Hx. pose proof (u64_range sp). destruct G1 as [G1a G1b]. (lazymatch goal with |- ?G => let G' := eval unfold am_m3 in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. apply am_m2_outside. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma amA1b : forall (M : word -> option byte) r0,
    getr r0 10 = Z_to_bv 64 1 -> regs_agree CLX regs r0 ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4c5e8) M rom) (mkst r (at_ rb 0x7b3e4) M rom)
      /\ getr r 1 = at_ rb 0x4c5f0 /\ (forall i : reg, In i [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr r i = getr r0 i)
      /\ regs_agree CLX regs r.
  Proof using HAL TOK.
    intros M r0 R10 AG0. wd_eexists. split.
    - ab_ft I67524 D_4c5e8 ltac:(condz).                  (* [comment removed for export] *)
      an I67528 D_4c5ec.                                   (* [comment removed for export] *)
      wd_refl.
    - post. 2: ((lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); ra_chain).
      intros i Hi; cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [gres; reflexivity|]); destruct Hi.
  Qed.

  (* [comment removed for export] *)
  Lemma amA1c : forall r0,
    getr r0 10 = Z_to_bv 64 0 -> getr r0 2 = at_ sp (-144) -> getr r0 23 = stk -> getr r0 18 = Z_to_bv 64 8 -> getr r0 22 = INST -> getr r0 9 = Z_to_bv 64 1 ->
    regs_agree CLX regs r0 ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4c5f0) am_m1 rom) (mkst r (at_ rb 0x4c62c) am_m2 rom)
      /\ getr r 10 = Z_to_bv 64 49 /\ getr r 8 = Z_to_bv 64 8 /\ getr r 25 = Z_to_bv 64 7 /\ getr r 26 = at_ INST 2047
      /\ (forall i : reg, In i [2; 9; 18; 19; 20; 21; 22; 23; 24; 27] -> getr r i = getr r0 i)
      /\ regs_agree CLX regs r.
  Proof using G1 G0 Hstk Rtbl2 Rmag HAL TOK.
    intros r0 R10 R2 R23 R18 R22 R9 AG0.
    destruct G0 as (Ga & Gb & Gc & Gd & Ge & Gf & Gg). destruct G1 as [G1a G1b].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range stk) as Hstk'. pose proof (u64_range INST) as HI. pose proof (u64_range (am_tbl2 t)) as HT2.
    pose proof (ato_mag _ _ TOK) as GM. destruct (ato_tbl2 _ _ TOK) as [tx [TA TB]].
    assert (Rmag1 : rdn segs am_m1 (Z_to_bv 64 (am_g_magic t)) 8 = Some (LE8 MAGICw)).
    { rewrite <- Rmag. apply rdn_ext; [wd_ulia_c | intros x Hx; apply am_m1_outside; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia]. }
    assert (Rtb1 : rdn segs am_m1 (at_ (am_tbl2 t) 4) 1 = Some [Z_to_bv 8 3]).
    { rewrite <- Rtbl2. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply am_m1_outside; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    wd_eexists. split.
    - ab_ft I6752c D_4c5f0 ltac:(condz).                  (* [comment removed for export] *)
      ab_ft I67530 D_4c5f4 ltac:(condz).                  (* [comment removed for export] *)
      an I67534 D_4c5f8.                                   (* [comment removed for export] *)
      ab_tk I67538 D_4c5fc ltac:(condz).                  (* [comment removed for export] *)
      an I67574 D_4c638. an I67578 D_4c63c.               (* [comment removed for export] *)
      ab_tk I6757c D_4c640 ltac:(condz).                  (* [comment removed for export] *)
      an I67584 D_4c648. an I67588 D_4c64c.               (* [comment removed for export] *)
      ab_ft I6758c D_4c650 ltac:(condz).                  (* [comment removed for export] *)
      eapply msteps_trans; [eapply GM; exact Rmag1|]. zlit_at.   (* [comment removed for export] *)
      an I67598 D_4c65c. an I6759c D_4c660.               (* [comment removed for export] *)
      an I675a0 D_4c664.                                   (* [comment removed for export] *)
      eapply msteps_trans; [apply TA|]. zlit_at.            (* [comment removed for export] *)
      an I675a8 D_4c66c.                                   (* [comment removed for export] *)
      eapply msteps_trans; [apply TB; gres; reflexivity|]. zlit_at. rewrite ?regupd_regupd_same.   (* [comment removed for export] *)
      av I675b0 D_4c674 (at_ (am_tbl2 t) 4) ltac:(apply v_add_at; lia).   (* [comment removed for export] *)
      clbu I675b4 D_4c678 (Z_to_bv 8 3) Rtbl2.            (* [comment removed for export] *)
      an I675b8 D_4c67c. an I675bc D_4c680. an I675c0 D_4c684.   (* [comment removed for export] *)
      an I675c4 D_4c688.                                   (* [comment removed for export] *)
      ab_tk I675c8 D_4c68c ltac:(condz).                  (* [comment removed for export] *)
      an I67548 D_4c60c. an I6754c D_4c610. an I67550 D_4c614.   (* [comment removed for export] *)
      ab_ft I67554 D_4c618 ltac:(condz).                  (* [comment removed for export] *)
      an I67558 D_4c61c.                                   (* [comment removed for export] *)
      an I6755c D_4c620.                                   (* [comment removed for export] *)
      fsd I67560 D_4c624 (at_ sp (-136)).                  (* [comment removed for export] *)
      fsd I67564 D_4c628 (at_ sp (-128)).                  (* [comment removed for export] *)
      wd_refl.
    - post.
      all: lazymatch goal with
           | |- regs_agree _ _ _ => (lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); ra_chain
           | |- forall x : reg, In x _ -> _ => intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]); destruct Hx
           | |- _ => idtac
           end.
  Qed.

  (* [comment removed for export] *)
  Lemma amA2 : forall (M : word -> option byte) r0,
    getr r0 10 = Z_to_bv 64 49 -> getr r0 21 = Z_to_bv 64 n -> regs_agree CLX regs r0 ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4c62c) M rom) (mkst r (at_ rb 0x4c700) M rom)
      /\ getr r 19 = Z_to_bv 64 (rz_log n)
      /\ (forall i : reg, In i [2; 8; 9; 18; 20; 21; 22; 23; 24; 25; 26; 27] -> getr r i = getr r0 i)
      /\ regs_agree CLX regs r.
  Proof using Hn HAL TOK.
    intros M r0 R10 R21 AG0.
    Ltac fin := post; first [ (lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); ra_chain
                            | intros i Hi; cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [gres; reflexivity|]); destruct Hi
                            | idtac ].
    destruct (rz_log_cases n ltac:(lia)) as [[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[C E]]]]]]]]; rewrite E.
    - wd_eexists. split.
      { ab_ft I67568 D_4c62c ltac:(condz). an I6756c D_4c630. an I67570 D_4c634. wd_refl. }
      fin.
    - wd_eexists. split.
      { ab_tk I67568 D_4c62c ltac:(condz). an I675d0 D_4c694. ab_ft I675d4 D_4c698 ltac:(condz). an I675d8 D_4c69c. an I675dc D_4c6a0. wd_refl. }
      fin.
    - wd_eexists. split.
      { ab_tk I67568 D_4c62c ltac:(condz). an I675d0 D_4c694. ab_tk I675d4 D_4c698 ltac:(condz).
      an I675e0 D_4c6a4. ab_ft I675e4 D_4c6a8 ltac:(condz). an I675e8 D_4c6ac. an I675ec D_4c6b0. wd_refl. }
      fin.
    - wd_eexists. split.
      { ab_tk I67568 D_4c62c ltac:(condz). an I675d0 D_4c694. ab_tk I675d4 D_4c698 ltac:(condz).
      an I675e0 D_4c6a4. ab_tk I675e4 D_4c6a8 ltac:(condz).
      an I675f0 D_4c6b4. an I675f4 D_4c6b8. ab_ft I675f8 D_4c6bc ltac:(condz). an I675fc D_4c6c0. an I67600 D_4c6c4. wd_refl. }
      fin.
    - wd_eexists. split.
      { ab_tk I67568 D_4c62c ltac:(condz). an I675d0 D_4c694. ab_tk I675d4 D_4c698 ltac:(condz).
      an I675e0 D_4c6a4. ab_tk I675e4 D_4c6a8 ltac:(condz).
      an I675f0 D_4c6b4. an I675f4 D_4c6b8. ab_tk I675f8 D_4c6bc ltac:(condz).
      an I67604 D_4c6c8. an I67608 D_4c6cc. ab_ft I6760c D_4c6d0 ltac:(condz). an I67610 D_4c6d4. an I67614 D_4c6d8. wd_refl. }
      fin.
    - wd_eexists. split.
      { ab_tk I67568 D_4c62c ltac:(condz). an I675d0 D_4c694. ab_tk I675d4 D_4c698 ltac:(condz).
      an I675e0 D_4c6a4. ab_tk I675e4 D_4c6a8 ltac:(condz).
      an I675f0 D_4c6b4. an I675f4 D_4c6b8. ab_tk I675f8 D_4c6bc ltac:(condz).
      an I67604 D_4c6c8. an I67608 D_4c6cc. ab_tk I6760c D_4c6d0 ltac:(condz).
      an I67618 D_4c6dc. an I6761c D_4c6e0. ab_ft I67620 D_4c6e4 ltac:(condz). an I67624 D_4c6e8. an I67628 D_4c6ec. wd_refl. }
      fin.
    - wd_eexists. split.
      { ab_tk I67568 D_4c62c ltac:(condz). an I675d0 D_4c694. ab_tk I675d4 D_4c698 ltac:(condz).
      an I675e0 D_4c6a4. ab_tk I675e4 D_4c6a8 ltac:(condz).
      an I675f0 D_4c6b4. an I675f4 D_4c6b8. ab_tk I675f8 D_4c6bc ltac:(condz).
      an I67604 D_4c6c8. an I67608 D_4c6cc. ab_tk I6760c D_4c6d0 ltac:(condz).
      an I67618 D_4c6dc. an I6761c D_4c6e0. ab_tk I67620 D_4c6e4 ltac:(condz).
      an I6762c D_4c6f0. an I67630 D_4c6f4. an I67634 D_4c6f8. rewrite v_sltu_lit by lia. replace (n <? 64513)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      an I67638 D_4c6fc. wd_refl. }
      fin.
    - wd_eexists. split.
      { ab_tk I67568 D_4c62c ltac:(condz). an I675d0 D_4c694. ab_tk I675d4 D_4c698 ltac:(condz).
      an I675e0 D_4c6a4. ab_tk I675e4 D_4c6a8 ltac:(condz).
      an I675f0 D_4c6b4. an I675f4 D_4c6b8. ab_tk I675f8 D_4c6bc ltac:(condz).
      an I67604 D_4c6c8. an I67608 D_4c6cc. ab_tk I6760c D_4c6d0 ltac:(condz).
      an I67618 D_4c6dc. an I6761c D_4c6e0. ab_tk I67620 D_4c6e4 ltac:(condz).
      an I6762c D_4c6f0. an I67630 D_4c6f4. an I67634 D_4c6f8. rewrite v_sltu_lit by lia. replace (n <? 64513)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      an I67638 D_4c6fc. wd_refl. }
      fin.
  Qed.

  (* [comment removed for export] *)
  Lemma v_sllw_16 : forall k, (0 <= k <= 7)%Z -> v_sllw (Z_to_bv 64 16) (Z_to_bv 64 k) = Z_to_bv 64 (16 * 2 ^ k).
  Proof using.
    intros k Hk. (lazymatch goal with |- ?G => let G' := eval unfold v_sllw in G in change_no_check G' end). f_equal. unorm. rewrite (Z.mod_small k 32) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    assert (2 ^ k <= 2 ^ 7)%Z by (apply Z.pow_le_mono_r; lia). assert (0 < 2 ^ k)%Z by (apply Z.pow_pos_nonneg; lia).
    apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31)%Z. cbn in H. lia.
  Qed.
  Lemma land_m8 : forall x, (0 <= x < 2 ^ 64)%Z -> Z.land x (2 ^ 64 - 8) = (x - x mod 8)%Z.
  Proof using.
    intros x Hx. apply Z.bits_inj'. intros k Hk.
    rewrite Z.land_spec.
    assert (Em : (2 ^ 64 - 8)%Z = Z.shiftl (2 ^ 61 - 1) 3) by reflexivity. rewrite Em.
    assert (Ex : (x - x mod 8)%Z = Z.shiftl (x / 2 ^ 3) 3).
    { rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z. pose proof (Z.div_mod x 8). lia. }
    rewrite Ex.
    destruct (Z.lt_ge_cases k 3) as [Hl|Hg].
    - rewrite !Z.shiftl_spec_low by lia. apply andb_false_r.
    - rewrite !Z.shiftl_spec_high by lia.
      destruct (Z.lt_ge_cases k 64) as [Hl2|Hg2].
      + assert (Ht : Z.testbit (2 ^ 61 - 1) (k - 3) = true).
        { replace (2 ^ 61 - 1)%Z with (Z.ones 61) by reflexivity. apply Z.ones_spec_low. lia. }
        rewrite Ht, andb_true_r. rewrite Z.div_pow2_bits by lia. f_equal. lia.
      + rewrite (testbit_high 64 x k) by lia.
        rewrite (testbit_high 61 (x / 2 ^ 3) (k - 3)); [reflexivity | lia | | lia].
        change (2 ^ 3)%Z with 8%Z. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
  Qed.
  Lemma rounded_val : forall m, (8 <= m < 2 ^ 62)%Z -> Z.land (m + 7) (2 ^ 64 - 8) = RoundUp m 8.
  Proof using.
    intros m Hm. rewrite land_m8 by lia. (lazymatch goal with |- ?G => let G' := eval unfold RoundUp in G in change_no_check G' end). pose proof (Z.div_mod (m + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (m + 8 - 1) 8 ltac:(lia)).
    replace (m + 7)%Z with (m + 8 - 1)%Z by lia. lia.
  Qed.

  Ltac clh F D z Hr :=
    chain_step; [reflexivity
      | eapply step_lh with (bs := LE2 z) (v := Z_to_bv 64 z);
        [exact F | reflexivity | exact D | rd_addr Hr | vm_compute; reflexivity]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  Lemma amA3a : forall r0,
    getr r0 26 = at_ INST 2047 -> getr r0 2 = at_ sp (-144) -> regs_agree CLX regs r0 ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4c700) am_m2 rom) (mkst r (at_ rb 0x51bb4) am_m2 rom)
      /\ getr r 1 = at_ rb 0x4c718 /\ getr r 10 = Z_to_bv 64 16 /\ getr r 20 = Z_to_bv 64 65536 /\ getr r 24 = Z_to_bv 64 65535
      /\ (forall i : reg, In i [2; 8; 9; 18; 19; 21; 22; 23; 25; 26; 27] -> getr r i = getr r0 i)
      /\ regs_agree CLX regs r.
  Proof using G1 G0 Rminrz stk HAL TOK.
    intros r0 R26 R2 AG0. destruct G0 as (Ga & Gb & Gc & Gd & Ge & Gf & Gg). destruct G1 as [G1a G1b].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range INST) as HI.
    wd_eexists. split.
    { clh I6763c D_4c700 16%Z Rminrz.                      (* [comment removed for export] *)
      afence I67640 D_4c704.
      an I67644 D_4c708. an I67648 D_4c70c.               (* [comment removed for export] *)
      an I6764c D_4c710.                                   (* [comment removed for export] *)
      an I67650 D_4c714.                                   (* [comment removed for export] *)
      wd_refl. }
    post.
    all: lazymatch goal with
         | |- regs_agree _ _ _ => (lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); ra_chain
         | |- forall x : reg, In x _ -> _ => intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]); destruct Hx
         | |- _ => idtac
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma amA3b : forall r0,
    getr r0 10 = Z_to_bv 64 0 -> getr r0 26 = at_ INST 2047 -> getr r0 2 = at_ sp (-144) -> getr r0 24 = Z_to_bv 64 65535 -> regs_agree CLX regs r0 ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4c718) (wbytes am_m2 (at_ sp (-152)) (LE8 (at_ rb 0x4c718))) rom)
                         (mkst r (at_ rb 0x51bb4) (wbytes am_m2 (at_ sp (-152)) (LE8 (at_ rb 0x4c718))) rom)
      /\ getr r 1 = at_ rb 0x4c72c /\ getr r 10 = Z_to_bv 64 2048 /\ getr r 9 = Z_to_bv 64 0
      /\ (forall i : reg, In i [2; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr r i = getr r0 i)
      /\ regs_agree CLX regs r.
  Proof using G1 G0 Rmaxrz stk HAL TOK.
    intros r0 R10 R26 R2 R24 AG0. destruct G0 as (Ga & Gb & Gc & Gd & Ge & Gf & Gg). destruct G1 as [G1a G1b].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range INST) as HI.
    wd_eexists. split.
    { an I67654 D_4c718.                                     (* [comment removed for export] *)
      clh I67658 D_4c71c 2048%Z Rmaxrz.                     (* [comment removed for export] *)
      afence I6765c D_4c720.
      an I67660 D_4c724.                                     (* [comment removed for export] *)
      an I67664 D_4c728.                                     (* [comment removed for export] *)
      wd_refl. }
    post.
    all: lazymatch goal with
         | |- regs_agree _ _ _ => (lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); ra_chain
         | |- forall x : reg, In x _ -> _ => intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]); destruct Hx
         | |- _ => idtac
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma amA3c : forall (M : word -> option byte) r0,
    getr r0 10 = Z_to_bv 64 7 -> getr r0 9 = Z_to_bv 64 0 -> getr r0 19 = Z_to_bv 64 (rz_log n) -> regs_agree CLX regs r0 ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4c72c) M rom) (mkst r (at_ rb 0x4c738) M rom)
      /\ getr r 19 = Z_to_bv 64 (rz_log n) /\ getr r 10 = Z_to_bv 64 7 /\ getr r 9 = Z_to_bv 64 0
      /\ (forall i : reg, In i [2; 8; 18; 20; 21; 22; 23; 24; 25; 26; 27] -> getr r i = getr r0 i)
      /\ regs_agree CLX regs r.
  Proof using Hn HAL TOK.
    intros M r0 R10 R9 R19 AG0.
    destruct (rz_log_cases n ltac:(lia)) as [[C E]|REST].
    - rewrite E in *. wd_eexists. split.
      { ab_ft I67668 D_4c72c ltac:(condz).                 (* [comment removed for export] *)
        an I6766c D_4c730.                                  (* [comment removed for export] *)
        ab_ft I67670 D_4c734 ltac:(condz).                 (* [comment removed for export] *)
        wd_refl. }
      post.
      all: lazymatch goal with
           | |- regs_agree _ _ _ => (lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); ra_chain
           | |- forall x : reg, In x _ -> _ => intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]); destruct Hx
           | |- _ => idtac
           end.
    - assert (HR : (1 <= rz_log n <= 6)%Z) by lia.
      wd_eexists. split.
      { ab_tk I67668 D_4c72c ltac:(condz).                 (* [comment removed for export] *)
        ab_tk I67714 D_4c7d8 ltac:(condz).                 (* [comment removed for export] *)
        wd_refl. }
      post.
      all: lazymatch goal with
           | |- regs_agree _ _ _ => (lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); ra_chain
           | |- forall x : reg, In x _ -> _ => intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]); destruct Hx
           | |- _ => idtac
           end.
  Qed.

  (* [comment removed for export] *)
  Lemma amA4 : forall r0,
    getr r0 19 = Z_to_bv 64 (rz_log n) -> getr r0 21 = Z_to_bv 64 n -> getr r0 8 = Z_to_bv 64 8 -> getr r0 18 = Z_to_bv 64 8 ->
    getr r0 20 = Z_to_bv 64 65536 -> getr r0 26 = at_ INST 2047 -> getr r0 2 = at_ sp (-144) -> regs_agree CLX regs r0 ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4c738) am_m3 rom) (mkst r (at_ rb 0x4c814) am_m3 rom)
      /\ getr r 8 = Z_to_bv 64 1 /\ getr r 9 = Z_to_bv 64 n /\ getr r 19 = Z_to_bv 64 (needed n) /\ getr r 20 = Z_to_bv 64 (rz n)
      /\ getr r 24 = Z_to_bv 64 18446744073709551608
      /\ (forall i : reg, In i [2; 18; 21; 22; 23; 25; 26; 27] -> getr r i = getr r0 i)
      /\ regs_agree CLX regs r.
  Proof using G1 G0 Rmaxsz Hn stk HAL TOK.
    intros r0 R19 R21 R8 R18 R20 R26 R2 AG0. destruct G0 as (Ga & Gb & Gc & Gd & Ge & Gf & Gg). destruct G1 as [G1a G1b].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range INST) as HI. pose proof (rz_log_range n) as HRL.
    assert (HP : (1 <= rz_log n <= 7 \/ rz_log n = 0)%Z) by lia.
    assert (Hrz : (rz n = 16 * 2 ^ rz_log n)%Z) by reflexivity.
    assert (Hrz2 : (16 <= rz n <= 1024)%Z).
    { rewrite Hrz. destruct (rz_log_cases n ltac:(lia)) as [[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[C E]]]]]]]]; rewrite E; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia. }
    assert (Hrd : (rounded n = RoundUp (Z.max n 8) 8)%Z) by reflexivity.
    assert (Hrd2 : (Z.max n 8 <= rounded n <= Z.max n 8 + 7 /\ rounded n mod 8 = 0)%Z).
    { rewrite Hrd. (lazymatch goal with |- ?G => let G' := eval unfold RoundUp in G in change_no_check G' end). pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)).
      split; [lia|]. apply Z_mod_mult. }
    assert (Hnd : (needed n = rounded n + rz n)%Z) by reflexivity.
    assert (Hprim : (needed n <= 65536)%Z).
    { pose proof (AsArith3.is_primary_iff n ltac:(lia)) as X. destruct X as [_ X]. specialize (X ltac:(lia)). unfold is_primary in X. apply Z.leb_le. exact X. }
    (* [comment removed for export] *)
    assert (W1 : exists r1, msteps segs (mkst r0 (at_ rb 0x4c738) am_m3 rom) (mkst r1 (at_ rb 0x4c748) am_m3 rom)
                 /\ getr r1 10 = Z_to_bv 64 (Z.max n 8) /\ (forall i : reg, In i [2; 8; 18; 19; 20; 21; 22; 23; 25; 26; 27] -> getr r1 i = getr r0 i)
                 /\ regs_agree CLX regs r1).
    { destruct (Z.lt_ge_cases 8 n) as [Hn8|Hn8].
      - rewrite Z.max_l by lia. wd_eexists. split.
        { an I67674 D_4c738. an I67678 D_4c73c. ab_tk I6767c D_4c740 ltac:(condz). wd_refl. }
        post. all: lazymatch goal with
           | |- regs_agree _ _ _ => (lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); ra_chain
           | |- forall x : reg, In x _ -> _ => intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]); destruct Hx
           | |- _ => idtac end.
      - rewrite Z.max_r by lia. wd_eexists. split.
        { an I67674 D_4c738. an I67678 D_4c73c. ab_ft I6767c D_4c740 ltac:(condz). an I67680 D_4c744. wd_refl. }
        post. all: lazymatch goal with
           | |- regs_agree _ _ _ => (lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); ra_chain
           | |- forall x : reg, In x _ -> _ => intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]); destruct Hx
           | |- _ => idtac end. }
    destruct W1 as (r1 & RUN1 & A10 & AK & AG1).
    assert (A8 : getr r1 8 = Z_to_bv 64 8) by (rewrite (AK 8) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact R8).
    assert (A18 : getr r1 18 = Z_to_bv 64 8) by (rewrite (AK 18) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact R18).
    assert (A19 : getr r1 19 = Z_to_bv 64 (rz_log n)) by (rewrite (AK 19) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact R19).
    assert (A20 : getr r1 20 = Z_to_bv 64 65536) by (rewrite (AK 20) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact R20).
    assert (A21 : getr r1 21 = Z_to_bv 64 n) by (rewrite (AK 21) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact R21).
    assert (A26 : getr r1 26 = at_ INST 2047) by (rewrite (AK 26) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact R26).
    set (m := Z.max n 8) in *.
    eapply (runs_trans segs _ (fun r => mkst r (at_ rb 0x4c748) am_m3 rom) (fun r => r = r1)); [exists r1; split; [exact RUN1 | reflexivity] |].
    intros r1' ->.
    wd_eexists. split.
    { av I67684 D_4c748 (Z_to_bv 64 (m + 8)) ltac:(valz).   (* [comment removed for export] *)
      an I67688 D_4c74c.                                      (* [comment removed for export] *)
      an I6768c D_4c750.                                      (* [comment removed for export] *)
      av I67690 D_4c754 (Z_to_bv 64 (m + 7)) ltac:(valz).    (* [comment removed for export] *)
      an I67694 D_4c758.                                      (* [comment removed for export] *)
      an I67698 D_4c75c.                                      (* [comment removed for export] *)
      match goal with |- context [v_and ?x ?y] => replace (v_and x y) with (Z_to_bv 64 (rounded n)) by ((lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end); unorm; f_equal; rewrite Hrd; symmetry; apply rounded_val; lia) end.
      an I6769c D_4c760.                                      (* [comment removed for export] *)
      av I676a0 D_4c764 (Z_to_bv 64 (rounded n)) ltac:(valz).   (* [comment removed for export] *)
      av I676a4 D_4c768 (Z_to_bv 64 0) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end); change (bv_wrap 64 7) with 7%Z; unorm; rewrite land_7 by lia; replace (rounded n mod 8)%Z with 0%Z by lia; reflexivity).   (* [comment removed for export] *)
      ab_ft I676a8 D_4c76c ltac:(condz).                    (* [comment removed for export] *)
      an I676ac D_4c770.                                      (* [comment removed for export] *)
      av I676b0 D_4c774 (Z_to_bv 64 0) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sltiu in G in change_no_check G' end); unorm; change (bv_wrap 64 1) with 1%Z; replace (n <? 1)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).   (* [comment removed for export] *)
      an I676b4 D_4c778.                                      (* [comment removed for export] *)
      an I676b8 D_4c77c. rewrite (v_sllw_16 (rz_log n)) by lia. rewrite <- Hrz.   (* [comment removed for export] *)
      an I676bc D_4c780.                                      (* [comment removed for export] *)
      av I676c0 D_4c784 (Z_to_bv 64 n) ltac:(valz).           (* [comment removed for export] *)
      an I676c4 D_4c788.                                      (* [comment removed for export] *)
      av I676c8 D_4c78c (Z_to_bv 64 (needed n)) ltac:(rewrite Hnd; valz).   (* [comment removed for export] *)
      an I676cc D_4c790. rewrite (v_sltu_lit (needed n) 65537) by lia. replace (needed n <? 65537)%Z with true by (symmetry; apply Z.ltb_lt; lia).   (* [comment removed for export] *)
      an I676d0 D_4c794.                                      (* [comment removed for export] *)
      an I676d4 D_4c798.                                      (* [comment removed for export] *)
      an I676d8 D_4c79c.                                      (* [comment removed for export] *)
      all: try (match goal with |- context [v_and (Z_to_bv 64 0) ?y] => replace (v_and (Z_to_bv 64 0) y) with (Z_to_bv 64 0) by ((lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end); unorm; rewrite Z.land_0_l; reflexivity) end).
      an I676dc D_4c7a0.                                      (* [comment removed for export] *)
      av I676e0 D_4c7a4 (Z_to_bv 64 (needed n)) ltac:(valz).   (* [comment removed for export] *)
      ab_ft I676e4 D_4c7a8 ltac:(condz).                    (* [comment removed for export] *)
      ab_ft I676e8 D_4c7ac ltac:(condz).                    (* [comment removed for export] *)
      cld8 I676ec D_4c7b0 (Z_to_bv 64 (2 ^ 40)) Rmaxsz.      (* [comment removed for export] *)
      ab_tk I676f0 D_4c7b4 ltac:(condz).                    (* [comment removed for export] *)
      wd_refl. }
    post.
    all: lazymatch goal with
         | |- regs_agree _ _ _ => (lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); ra_chain
         | |- forall x : reg, In x _ -> _ => intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [gres; apply AK; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto|]); destruct Hx
         | |- _ => idtac
         end.
  Qed.

  (* [comment removed for export] *)
  Theorem amA_run :
    exists r,
      msteps segs (mkst regs (at_ rb 0x4c538) mem rom) (mkst r (at_ rb 0x4c814) am_m3 rom)
      /\ getr r 2 = at_ sp (-144) /\ getr r 8 = Z_to_bv 64 1 /\ getr r 9 = Z_to_bv 64 n /\ getr r 18 = Z_to_bv 64 8
      /\ getr r 19 = Z_to_bv 64 (needed n) /\ getr r 20 = Z_to_bv 64 (rz n) /\ getr r 21 = Z_to_bv 64 n /\ getr r 22 = INST
      /\ getr r 23 = stk /\ getr r 24 = Z_to_bv 64 18446744073709551608 /\ getr r 25 = Z_to_bv 64 7 /\ getr r 26 = at_ INST 2047
      /\ getr r 27 = Z_to_bv 64 1
      /\ regs_agree CLX regs r.
  Proof using G1 G0 Hstk Rmaxsz Rmaxrz Rminrz Rt2048 Rt16 Rtbl2 Rmag Rrss Rinited Hn H11 H10 H2 H1 HAL HAM TOK.
    pose proof G0 as (Ga & Gb & Gc & Gd & Ge & Gf & Gg). pose proof G1 as [G1a G1b].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range INST) as HI. pose proof (u64_range (am_tbl t)) as HT.
    pose proof TOK as TOK'. destruct TOK' as [_ _ _ _ _ AIN AINB RSS RSSB RZL RZM RZT RB].
    Ltac via AG r H := let T := fresh in pose proof (AG r ltac:(notin_list)) as T; rewrite H in T; exact T.
    Ltac viaK K AG r H := rewrite (K r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); via AG r H.
    (* [comment removed for export] *)
    destruct amA1a as (r1 & RUN1 & A1 & A2 & A9 & A27 & A23 & A18 & A21 & A22 & AG1).
    (* [comment removed for export] *)
    destruct (ain_run segs rb (am_g_inited t) AIN AINB am_m1 rom r1 (at_ rb 0x4c5e8)) as (r2 & RUN2 & B10 & AG2).
    { rewrite <- Rinited. apply rdn_ext; [wd_ulia_c | intros x Hx; apply am_m1_outside; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia]. }
    { apply RETa; [reflexivity | lia]. }
    { exact A1. }
    (* [comment removed for export] *)
    destruct (amA1b am_m1 r2 B10 ltac:(eapply regs_agree_trans; [exact AG1 | regs_agree_weaken AG2])) as (r3 & RUN3 & C1 & CK & AG3).
    (* [comment removed for export] *)
    destruct (rss_run segs rb (am_g_rss t) RSS RSSB am_m1 rom r3 (at_ rb 0x4c5f0)) as (r4 & RUN4 & D10 & AG4).
    { rewrite <- Rrss. apply rdn_ext; [wd_ulia_c | intros x Hx; apply am_m1_outside; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia]. }
    { apply RETa; [reflexivity | lia]. }
    { exact C1. }
    (* [comment removed for export] *)
    destruct (amA1c r4 D10) as (r5 & RUN5 & E10 & E8 & E25 & E26 & EK & AG5).
    { rewrite (AG4 2) by notin_list. viaK CK AG2 (2:reg) A2. }
    { rewrite (AG4 23) by notin_list. viaK CK AG2 (23:reg) A23. }
    { rewrite (AG4 18) by notin_list. viaK CK AG2 (18:reg) A18. }
    { rewrite (AG4 22) by notin_list. viaK CK AG2 (22:reg) A22. }
    { rewrite (AG4 9) by notin_list. viaK CK AG2 (9:reg) A9. }
    { eapply regs_agree_trans; [exact AG3 | regs_agree_weaken AG4]. }
    assert (E21 : getr r5 21 = Z_to_bv 64 n). { rewrite (EK 21) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG4 21) by notin_list. viaK CK AG2 (21:reg) A21. }
    Ltac thr5 EK AG4 CK AG2 r A := rewrite (EK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (AG4 r) by notin_list; rewrite (CK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); let T := fresh in pose proof (AG2 r ltac:(notin_list)) as T; rewrite A in T; exact T.
    assert (E2 : getr r5 2 = at_ sp (-144)) by (thr5 EK AG4 CK AG2 (2:reg) A2).
    assert (E9 : getr r5 9 = Z_to_bv 64 1) by (thr5 EK AG4 CK AG2 (9:reg) A9).
    assert (E18 : getr r5 18 = Z_to_bv 64 8) by (thr5 EK AG4 CK AG2 (18:reg) A18).
    assert (E22 : getr r5 22 = INST) by (thr5 EK AG4 CK AG2 (22:reg) A22).
    assert (E23 : getr r5 23 = stk) by (thr5 EK AG4 CK AG2 (23:reg) A23).
    assert (E27 : getr r5 27 = Z_to_bv 64 1) by (thr5 EK AG4 CK AG2 (27:reg) A27).
    (* [comment removed for export] *)
    destruct (amA2 am_m2 r5 E10 E21 AG5) as (r6 & RUN6 & F19 & FK & AG6).
    (* [comment removed for export] *)
    destruct (amA3a r6 ltac:(rewrite (FK 26) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact E26) ltac:(rewrite (FK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact E2) AG6) as (r7 & RUN7 & G1' & G10 & G20 & G24 & GK & AG7).
    (* [comment removed for export] *)
    assert (Rm2 : rdn segs am_m2 (Z_to_bv 64 (am_g_magic t)) 8 = Some (LE8 MAGICw)).
    { rewrite <- Rmag. apply rdn_ext; [wd_ulia_c | intros x Hx; apply am_m2_outside; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia]. }
    assert (Rt2 : rdn segs am_m2 (at_ (am_tbl t) 8) 1 = Some [Z_to_bv 8 4]).
    { rewrite <- Rt16. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply am_m2_outside; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    assert (SOK2 : store_ok segs am_m2 (at_ (at_ sp (-144)) (-8)) 8 = true).
    { rewrite at_at. (lazymatch goal with |- ?G => let G' := eval unfold am_m2, am_m1 in G in change_no_check G' end). repeat (eapply store_ok_mono; [apply wbytes_grows|]).
      eapply (store_ok_sub segs mem (at_ sp (-160)) _ 160); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    destruct (rzl16_run segs rb RB (am_g_magic t) (am_tbl t) RZL RZM RZT am_m2 rom r7 (at_ rb 0x4c718) (at_ sp (-144)) Rm2 ltac:(lia) SOK2
                ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(right; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ])
                (RETa 0x4c718 eq_refl ltac:(lia)) G1' ltac:(rewrite (GK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (FK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact E2) Rt2 G10)
      as (r8 & RUN8 & H10' & AG8).
    unfold rzM1 in RUN8. rewrite at_at in RUN8. cbn [Z.add] in RUN8.
    (* [comment removed for export] *)
    destruct (amA3b r8 H10') as (r9 & RUN9 & I1 & I10 & I9 & IK & AG9).
    { rewrite (AG8 26) by notin_list. rewrite (GK 26) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (FK 26) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). exact E26. }
    { rewrite (AG8 2) by notin_list. rewrite (GK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (FK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). exact E2. }
    { rewrite (AG8 24) by notin_list. exact G24. }
    { eapply regs_agree_trans; [exact AG7 | regs_agree_weaken AG8]. }
    (* [comment removed for export] *)
    set (M3a := wbytes am_m2 (at_ sp (-152)) (LE8 (at_ rb 0x4c718))) in *.
    assert (HM3a : forall x : word, (U x < U sp - 152 \/ U sp <= U x)%Z -> M3a x = mem x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M3a in G in change_no_check G' end). rewrite wbytes_outside; [apply am_m2_outside; lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    assert (Rm3 : rdn segs M3a (Z_to_bv 64 (am_g_magic t)) 8 = Some (LE8 MAGICw)).
    { rewrite <- Rmag. apply rdn_ext; [wd_ulia_c | intros x Hx; apply HM3a; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia]. }
    assert (Rt3 : rdn segs M3a (at_ (am_tbl t) 49) 1 = Some [Z_to_bv 8 11]).
    { rewrite <- Rt2048. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply HM3a; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    assert (SOK3 : store_ok segs M3a (at_ (at_ sp (-144)) (-8)) 8 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold M3a in G in change_no_check G' end). eapply store_ok_mono; [apply wbytes_grows | exact SOK2]. }
    destruct (rzl2048_run segs rb RB (am_g_magic t) (am_tbl t) RZL RZM RZT M3a rom r9 (at_ rb 0x4c72c) (at_ sp (-144)) Rm3 ltac:(lia) SOK3
                ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(right; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ])
                (RETa 0x4c72c eq_refl ltac:(lia)) I1 ltac:(rewrite (IK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (AG8 2) by notin_list; rewrite (GK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (FK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact E2) Rt3 I10)
      as (r10 & RUN10 & J10 & AG10).
    unfold rzM1 in RUN10. rewrite at_at in RUN10. cbn [Z.add] in RUN10.
    change (wbytes M3a (at_ sp (-152)) (LE8 (at_ rb 0x4c72c))) with am_m3 in RUN10.
    (* [comment removed for export] *)
    destruct (amA3c am_m3 r10 J10) as (r11 & RUN11 & K19 & K10 & K9 & KK & AG11).
    { rewrite (AG10 9) by notin_list. exact I9. }
    { rewrite (AG10 19) by notin_list. rewrite (IK 19) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG8 19) by notin_list. rewrite (GK 19) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). exact F19. }
    { eapply regs_agree_trans; [exact AG9 | regs_agree_weaken AG10]. }
    (* [comment removed for export] *)
    Ltac thrB KK AG10 IK AG8 GK FK r H := rewrite (KK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (AG10 r) by notin_list; rewrite (IK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]);
                                        rewrite (AG8 r) by notin_list; rewrite (GK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (FK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact H.
    destruct (amA4 r11 K19) as (r12 & RUN12 & L8 & L9 & L19 & L20 & L24 & LK & AG12).
    { thrB KK AG10 IK AG8 GK FK (21:reg) E21. }
    { rewrite (KK 8) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG10 8) by notin_list. rewrite (IK 8) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG8 8) by notin_list. rewrite (GK 8) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (FK 8) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). exact E8. }
    { thrB KK AG10 IK AG8 GK FK (18:reg) E18. }
    { rewrite (KK 20) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG10 20) by notin_list. rewrite (IK 20) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG8 20) by notin_list. exact G20. }
    { rewrite (KK 26) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG10 26) by notin_list. rewrite (IK 26) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG8 26) by notin_list. rewrite (GK 26) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (FK 26) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). exact E26. }
    { thrB KK AG10 IK AG8 GK FK (2:reg) E2. }
    { eapply regs_agree_trans; [exact AG11 | idtac]. apply regs_agree_refl. }
    exists r12. split.
    { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|].
      eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|]. eapply msteps_trans; [exact RUN7|]. eapply msteps_trans; [exact RUN8|].
      eapply msteps_trans; [exact RUN9|]. eapply msteps_trans; [exact RUN10|]. eapply msteps_trans; [exact RUN11 | exact RUN12]. }
    Ltac thrC LK KK AG10 IK AG8 GK FK r H := rewrite (LK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (KK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (AG10 r) by notin_list; rewrite (IK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]);
                                        rewrite (AG8 r) by notin_list; rewrite (GK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (FK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact H.
    split; [thrC LK KK AG10 IK AG8 GK FK (2:reg) E2|]. split; [exact L8|]. split; [exact L9|]. split; [thrC LK KK AG10 IK AG8 GK FK (18:reg) E18|].
    split; [exact L19|]. split; [exact L20|]. split; [thrC LK KK AG10 IK AG8 GK FK (21:reg) E21|]. split; [thrC LK KK AG10 IK AG8 GK FK (22:reg) E22|].
    split; [thrC LK KK AG10 IK AG8 GK FK (23:reg) E23|]. split; [exact L24|].
    split; [rewrite (LK 25) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (KK 25) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (AG10 25) by notin_list; rewrite (IK 25) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (AG8 25) by notin_list; rewrite (GK 25) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (FK 25) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact E25|].
    split; [thrC LK KK AG10 IK AG8 GK FK (26:reg) E26|].
    split; [thrC LK KK AG10 IK AG8 GK FK (27:reg) E27|].
    exact AG12.
  Qed.
End AM.
End FPGen1.
