(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= am_lia.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
Lemma Z_to_bv8_mod : forall a b, (a mod 256 = b mod 256)%Z -> Z_to_bv 8 a = Z_to_bv 8 b.
Proof. intros a b E. apply bv_eq. rewrite !Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 8) with 256%Z. exact E. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma LE4_lw : forall z, (0 <= z < 2 ^ 32)%Z -> word_to_le_bytes 4 (v_lw (Z_to_bv 64 z)) = word_to_le_bytes 4 (Z_to_bv 64 z).
Proof.
  intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold word_to_le_bytes, v_lw in G in change_no_check G' end). rewrite (u_Z2bv z) by lia. rewrite Z_to_bv_unsigned.
  set (w := bv_wrap 64 (bv_swrap 32 z)).
  assert (Hw : w = z \/ w = (z + 2 ^ 64 - 2 ^ 32)%Z).
  { (lazymatch goal with |- ?G => let G' := eval unfold w, bv_swrap, bv_wrap in G in change_no_check G' end). change (bv_modulus 32) with 4294967296%Z. change (bv_half_modulus 32) with 2147483648%Z.
    change (bv_modulus 64) with 18446744073709551616%Z.
    destruct (Z_lt_le_dec z (2 ^ 31)) as [L|G].
    - left. rewrite (Z.mod_small (z + 2147483648)) by lia. rewrite Z.mod_small by lia. lia.
    - right. Z.div_mod_to_equations. nia. }
  (lazymatch goal with |- ?G => let G' := eval cbn [Z_to_le_bytes] in G in change_no_check G' end). rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 8)%Z with 256%Z.
  destruct Hw as [-> | ->]; [reflexivity|].
  f_equal; [apply Z_to_bv8_mod; Z.div_mod_to_equations; lia|].
  f_equal; [apply Z_to_bv8_mod; Z.div_mod_to_equations; lia|].
  f_equal; [apply Z_to_bv8_mod; Z.div_mod_to_equations; lia|].
  f_equal. apply Z_to_bv8_mod; Z.div_mod_to_equations; lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPGen1.
Context {fx : FPState}.

Definition gf_words : list (option (bv 32)) :=
  [Some W_5153c; Some W_51540; Some W_51544; Some W_51548; Some W_5154c; Some W_51550; Some W_51554; Some W_51558;
   Some W_5155c; Some W_51560; Some W_51564; Some W_51568; Some W_5156c; Some W_51570; Some W_51574; Some W_51578;
   Some W_5157c; Some W_51580; Some W_51584; Some W_51588; Some W_5158c; Some W_51590; Some W_51594; Some W_51598;
   Some W_5159c; Some W_515a0; Some W_515a4; Some W_515a8; Some W_515ac; Some W_515b0; Some W_515b4; Some W_515b8;
   Some W_515bc; Some W_515c0; Some W_515c4; Some W_515c8; Some W_515cc; Some W_515d0; Some W_515d4; Some W_515d8;
   Some W_515dc; Some W_515e0; Some W_515e4; Some W_515e8; Some W_515ec; Some W_515f0; Some W_515f4; Some W_515f8;
   Some W_515fc; Some W_51600; Some W_51604; Some W_51608; Some W_5160c; Some W_51610; Some W_51614; Some W_51618;
   Some W_5161c; Some W_51620; Some W_51624; Some W_51628; Some W_5162c; Some W_51630; Some W_51634; Some W_51638;
   Some W_5163c; Some W_51640; Some W_51644; Some W_51648; Some W_5164c; Some W_51650; Some W_51654; Some W_51658;
   Some W_5165c; Some W_51660; Some W_51664; Some W_51668; Some W_5166c; Some W_51670; Some W_51674; Some W_51678;
   Some W_5167c; Some W_51680; Some W_51684; Some W_51688; Some W_5168c; Some W_51690; Some W_51694; Some W_51698;
   Some W_5169c; Some W_516a0; Some W_516a4; Some W_516a8; Some W_516ac; Some W_516b0; Some W_516b4; Some W_516b8;
   Some W_516bc; Some W_516c0; Some W_516c4; Some W_516c8; Some W_516cc; Some W_516d0; Some W_516d4; Some W_516d8;
   Some W_516dc; Some W_516e0; None; Some W_516e8; Some W_516ec; Some W_516f0; Some W_516f4; Some W_516f8;
   Some W_516fc; Some W_51700; Some W_51704; Some W_51708; Some W_5170c; Some W_51710; Some W_51714; Some W_51718;
   Some W_5171c; Some W_51720; Some W_51724; Some W_51728; Some W_5172c; Some W_51730; Some W_51734; Some W_51738;
   Some W_5173c; Some W_51740; Some W_51744; Some W_51748; Some W_5174c; Some W_51750; Some W_51754; Some W_51758;
   Some W_5175c; Some W_51760; Some W_51764; Some W_51768; Some W_5176c; Some W_51770; Some W_51774; Some W_51778;
   Some W_5177c; Some W_51780; Some W_51784; Some W_51788; Some W_5178c; Some W_51790; Some W_51794; Some W_51798;
   Some W_5179c; Some W_517a0; Some W_517a4; Some W_517a8; Some W_517ac; Some W_517b0; Some W_517b4; Some W_517b8;
   Some W_517bc; Some W_517c0; Some W_517c4; Some W_517c8; Some W_517cc; Some W_517d0; Some W_517d4; Some W_517d8]%list.

(* [comment removed for export] *)
Definition rf_clob : list reg := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30].
(* [comment removed for export] *)
Definition gf_mid : list reg := [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section GF.
  Variable segs : list Segment.
  Variable rb : word.
  Hypothesis HGF : code_ato segs rb 0x5153c gf_words.
  Hypothesis RB : (U rb mod 2 = 0)%Z /\ (U rb + 2 ^ 24 < 2 ^ 64)%Z.
  (* [comment removed for export] *)
  Variable gmsk : Z.
  Hypothesis GMSK : gauipc_ld segs rb 0x516e4 0x516f4 14 14 gmsk.
  Hypothesis Ggm : (AIMGLO <= gmsk /\ gmsk + 8 <= AIMGHI)%Z.

  Lemma G5153c : fetch_word segs (at_ rb 0x5153c) = Some W_5153c.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 0 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51540 : fetch_word segs (at_ rb 0x51540) = Some W_51540.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 1 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51544 : fetch_word segs (at_ rb 0x51544) = Some W_51544.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 2 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51548 : fetch_word segs (at_ rb 0x51548) = Some W_51548.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 3 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G5154c : fetch_word segs (at_ rb 0x5154c) = Some W_5154c.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 4 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51550 : fetch_word segs (at_ rb 0x51550) = Some W_51550.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 5 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51554 : fetch_word segs (at_ rb 0x51554) = Some W_51554.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 6 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51558 : fetch_word segs (at_ rb 0x51558) = Some W_51558.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 7 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G5155c : fetch_word segs (at_ rb 0x5155c) = Some W_5155c.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 8 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51560 : fetch_word segs (at_ rb 0x51560) = Some W_51560.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 9 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51564 : fetch_word segs (at_ rb 0x51564) = Some W_51564.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 10 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51568 : fetch_word segs (at_ rb 0x51568) = Some W_51568.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 11 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G5156c : fetch_word segs (at_ rb 0x5156c) = Some W_5156c.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 12 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51570 : fetch_word segs (at_ rb 0x51570) = Some W_51570.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 13 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51574 : fetch_word segs (at_ rb 0x51574) = Some W_51574.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 14 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51578 : fetch_word segs (at_ rb 0x51578) = Some W_51578.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 15 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G5157c : fetch_word segs (at_ rb 0x5157c) = Some W_5157c.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 16 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51580 : fetch_word segs (at_ rb 0x51580) = Some W_51580.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 17 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51584 : fetch_word segs (at_ rb 0x51584) = Some W_51584.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 18 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51588 : fetch_word segs (at_ rb 0x51588) = Some W_51588.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 19 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G5158c : fetch_word segs (at_ rb 0x5158c) = Some W_5158c.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 20 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51590 : fetch_word segs (at_ rb 0x51590) = Some W_51590.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 21 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51594 : fetch_word segs (at_ rb 0x51594) = Some W_51594.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 22 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51598 : fetch_word segs (at_ rb 0x51598) = Some W_51598.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 23 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G5159c : fetch_word segs (at_ rb 0x5159c) = Some W_5159c.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 24 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G515a0 : fetch_word segs (at_ rb 0x515a0) = Some W_515a0.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 25 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G515a4 : fetch_word segs (at_ rb 0x515a4) = Some W_515a4.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 26 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G515a8 : fetch_word segs (at_ rb 0x515a8) = Some W_515a8.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 27 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G515ac : fetch_word segs (at_ rb 0x515ac) = Some W_515ac.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 28 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G515b0 : fetch_word segs (at_ rb 0x515b0) = Some W_515b0.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 29 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G515b4 : fetch_word segs (at_ rb 0x515b4) = Some W_515b4.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 30 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G515b8 : fetch_word segs (at_ rb 0x515b8) = Some W_515b8.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 31 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G515bc : fetch_word segs (at_ rb 0x515bc) = Some W_515bc.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 32 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G515c0 : fetch_word segs (at_ rb 0x515c0) = Some W_515c0.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 33 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G515c4 : fetch_word segs (at_ rb 0x515c4) = Some W_515c4.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 34 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G515c8 : fetch_word segs (at_ rb 0x515c8) = Some W_515c8.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 35 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G515cc : fetch_word segs (at_ rb 0x515cc) = Some W_515cc.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 36 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G515d0 : fetch_word segs (at_ rb 0x515d0) = Some W_515d0.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 37 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G515d4 : fetch_word segs (at_ rb 0x515d4) = Some W_515d4.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 38 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G515d8 : fetch_word segs (at_ rb 0x515d8) = Some W_515d8.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 39 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G515dc : fetch_word segs (at_ rb 0x515dc) = Some W_515dc.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 40 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G515e0 : fetch_word segs (at_ rb 0x515e0) = Some W_515e0.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 41 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G515e4 : fetch_word segs (at_ rb 0x515e4) = Some W_515e4.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 42 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G515e8 : fetch_word segs (at_ rb 0x515e8) = Some W_515e8.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 43 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G515ec : fetch_word segs (at_ rb 0x515ec) = Some W_515ec.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 44 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G515f0 : fetch_word segs (at_ rb 0x515f0) = Some W_515f0.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 45 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G515f4 : fetch_word segs (at_ rb 0x515f4) = Some W_515f4.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 46 _ HGF eq_refl). Qed.




































   (* [comment removed for export] *)
  Lemma G5168c : fetch_word segs (at_ rb 0x5168c) = Some W_5168c.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 84 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51690 : fetch_word segs (at_ rb 0x51690) = Some W_51690.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 85 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51694 : fetch_word segs (at_ rb 0x51694) = Some W_51694.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 86 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51698 : fetch_word segs (at_ rb 0x51698) = Some W_51698.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 87 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G5169c : fetch_word segs (at_ rb 0x5169c) = Some W_5169c.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 88 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G516a0 : fetch_word segs (at_ rb 0x516a0) = Some W_516a0.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 89 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G516a4 : fetch_word segs (at_ rb 0x516a4) = Some W_516a4.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 90 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G516a8 : fetch_word segs (at_ rb 0x516a8) = Some W_516a8.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 91 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G516ac : fetch_word segs (at_ rb 0x516ac) = Some W_516ac.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 92 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G516b0 : fetch_word segs (at_ rb 0x516b0) = Some W_516b0.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 93 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G516b4 : fetch_word segs (at_ rb 0x516b4) = Some W_516b4.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 94 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G516b8 : fetch_word segs (at_ rb 0x516b8) = Some W_516b8.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 95 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G516bc : fetch_word segs (at_ rb 0x516bc) = Some W_516bc.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 96 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G516c0 : fetch_word segs (at_ rb 0x516c0) = Some W_516c0.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 97 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G516c4 : fetch_word segs (at_ rb 0x516c4) = Some W_516c4.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 98 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G516c8 : fetch_word segs (at_ rb 0x516c8) = Some W_516c8.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 99 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G516cc : fetch_word segs (at_ rb 0x516cc) = Some W_516cc.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 100 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G516d0 : fetch_word segs (at_ rb 0x516d0) = Some W_516d0.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 101 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G516d4 : fetch_word segs (at_ rb 0x516d4) = Some W_516d4.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 102 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G516d8 : fetch_word segs (at_ rb 0x516d8) = Some W_516d8.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 103 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G516dc : fetch_word segs (at_ rb 0x516dc) = Some W_516dc.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 104 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G516e0 : fetch_word segs (at_ rb 0x516e0) = Some W_516e0.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 105 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G516e8 : fetch_word segs (at_ rb 0x516e8) = Some W_516e8.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 107 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G516ec : fetch_word segs (at_ rb 0x516ec) = Some W_516ec.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 108 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G516f0 : fetch_word segs (at_ rb 0x516f0) = Some W_516f0.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 109 _ HGF eq_refl). Qed.
   (* [comment removed for export] *)
  Lemma G516f8 : fetch_word segs (at_ rb 0x516f8) = Some W_516f8.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 111 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G516fc : fetch_word segs (at_ rb 0x516fc) = Some W_516fc.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 112 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51700 : fetch_word segs (at_ rb 0x51700) = Some W_51700.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 113 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51704 : fetch_word segs (at_ rb 0x51704) = Some W_51704.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 114 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51708 : fetch_word segs (at_ rb 0x51708) = Some W_51708.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 115 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G5170c : fetch_word segs (at_ rb 0x5170c) = Some W_5170c.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 116 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51710 : fetch_word segs (at_ rb 0x51710) = Some W_51710.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 117 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51714 : fetch_word segs (at_ rb 0x51714) = Some W_51714.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 118 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51718 : fetch_word segs (at_ rb 0x51718) = Some W_51718.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 119 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G5171c : fetch_word segs (at_ rb 0x5171c) = Some W_5171c.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 120 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51720 : fetch_word segs (at_ rb 0x51720) = Some W_51720.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 121 _ HGF eq_refl). Qed.
   (* [comment removed for export] *)
  Lemma G51728 : fetch_word segs (at_ rb 0x51728) = Some W_51728.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 123 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G5172c : fetch_word segs (at_ rb 0x5172c) = Some W_5172c.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 124 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51730 : fetch_word segs (at_ rb 0x51730) = Some W_51730.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 125 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51734 : fetch_word segs (at_ rb 0x51734) = Some W_51734.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 126 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51738 : fetch_word segs (at_ rb 0x51738) = Some W_51738.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 127 _ HGF eq_refl). Qed.







   (* [comment removed for export] *)
  Lemma G5175c : fetch_word segs (at_ rb 0x5175c) = Some W_5175c.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 136 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51760 : fetch_word segs (at_ rb 0x51760) = Some W_51760.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 137 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51764 : fetch_word segs (at_ rb 0x51764) = Some W_51764.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 138 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51768 : fetch_word segs (at_ rb 0x51768) = Some W_51768.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 139 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G5176c : fetch_word segs (at_ rb 0x5176c) = Some W_5176c.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 140 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51770 : fetch_word segs (at_ rb 0x51770) = Some W_51770.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 141 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51774 : fetch_word segs (at_ rb 0x51774) = Some W_51774.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 142 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G51778 : fetch_word segs (at_ rb 0x51778) = Some W_51778.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 143 _ HGF eq_refl). Qed.


   (* [comment removed for export] *)
  Lemma G51788 : fetch_word segs (at_ rb 0x51788) = Some W_51788.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 147 _ HGF eq_refl). Qed.



   (* [comment removed for export] *)
  Lemma G5179c : fetch_word segs (at_ rb 0x5179c) = Some W_5179c.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 152 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G517a0 : fetch_word segs (at_ rb 0x517a0) = Some W_517a0.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 153 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G517a4 : fetch_word segs (at_ rb 0x517a4) = Some W_517a4.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 154 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G517a8 : fetch_word segs (at_ rb 0x517a8) = Some W_517a8.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 155 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G517ac : fetch_word segs (at_ rb 0x517ac) = Some W_517ac.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 156 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G517b0 : fetch_word segs (at_ rb 0x517b0) = Some W_517b0.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 157 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G517b4 : fetch_word segs (at_ rb 0x517b4) = Some W_517b4.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 158 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G517b8 : fetch_word segs (at_ rb 0x517b8) = Some W_517b8.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 159 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G517bc : fetch_word segs (at_ rb 0x517bc) = Some W_517bc.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 160 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G517c0 : fetch_word segs (at_ rb 0x517c0) = Some W_517c0.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 161 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G517c4 : fetch_word segs (at_ rb 0x517c4) = Some W_517c4.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 162 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G517c8 : fetch_word segs (at_ rb 0x517c8) = Some W_517c8.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 163 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G517cc : fetch_word segs (at_ rb 0x517cc) = Some W_517cc.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 164 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G517d0 : fetch_word segs (at_ rb 0x517d0) = Some W_517d0.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 165 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G517d4 : fetch_word segs (at_ rb 0x517d4) = Some W_517d4.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 166 _ HGF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma G517d8 : fetch_word segs (at_ rb 0x517d8) = Some W_517d8.  Proof using HGF. exact (code_ato_get segs rb 0x5153c gf_words 167 _ HGF eq_refl). Qed.   (* [comment removed for export] *)

  Variables (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ra sp alloc chp : word) (c m SPB nf : Z) (msk stv : word).
  #[local] Abbreviation RIz := (SPB + 2 ^ 37 + 128 * c)%Z.
  #[local] Abbreviation RI := (Z_to_bv 64 (SPB + 2 ^ 37 + 128 * c)).
  #[local] Abbreviation FABz := (SPB + c * 2 ^ 32 + 3758096384)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = alloc.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 c.
  Hypothesis H13 : getr regs 13 = chp.
  Hypothesis H14 : getr regs 14 = Z_to_bv 64 m.
  Hypothesis Hc : (1 <= c <= 30)%Z.
  Hypothesis Hm : (1 <= m <= 8)%Z /\ (m <= nf)%Z /\ (nf <= 2 ^ 27)%Z.
  Hypothesis GSPB : (0 <= SPB)%Z /\ (SPB + 2 ^ 37 + 4096 < 2 ^ 47)%Z /\ (SPB mod 2 ^ 16 = 0)%Z /\ (0x10007fff8000 <= SPB)%Z.
  Hypothesis G1 : (SPB + 2 ^ 37 + 4096 + 128 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Galloc : (AIMGLO <= U alloc /\ U alloc + 56 <= AIMGHI)%Z.
  (* [comment removed for export] *)
  Hypothesis Gchp : (U chp mod 4 = 0)%Z /\ (U chp + 64 <= U sp - 128)%Z
                    /\ (U chp + 64 <= SPB \/ SPB + 2 ^ 37 + 4096 <= U chp)%Z /\ (AIMGHI <= U chp \/ U chp + 64 <= AIMGLO)%Z.
  Hypothesis Hstk : store_ok segs mem (at_ sp (-128)) 128 = true.
  (* [comment removed for export] *)
  Hypothesis Rspb : rdn segs mem (at_ alloc 32) 8 = Some (LE8 (Z_to_bv 64 SPB)).
  Hypothesis Rrib : rdn segs mem (at_ alloc 48) 8 = Some (LE8 (Z_to_bv 64 (SPB + 2 ^ 37))).
  Hypothesis Rmu : rdn segs mem RI 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis SOKmu : store_ok segs mem RI 8 = true.
  Hypothesis Rnf : rdn segs mem (at_ RI 16) 8 = Some (LE8 (Z_to_bv 64 nf)).
  Hypothesis SOKnf : store_ok segs mem (at_ RI 16) 8 = true.
  Hypothesis Rst : rdn segs mem (at_ RI 72) 8 = Some (LE8 stv).
  Hypothesis SOKst : store_ok segs mem (at_ RI 72) 8 = true.
  Hypothesis Rmsk : rdn segs mem (Z_to_bv 64 gmsk) 8 = Some (LE8 msk).
  Hypothesis SOKch : store_ok segs mem chp (Z.to_nat (4 * m)) = true.
  (* [comment removed for export] *)
  Variable faf : Z -> Z.
  Hypothesis Hfaf : forall j, (nf - m <= j < nf)%Z -> rdn segs mem (Z_to_bv 64 (FABz + 4 * j)) 4 = Some (LE4 (faf j)) /\ (0 <= faf j < 2 ^ 32)%Z.

  #[local] Abbreviation CLX := (fun r : reg => In r rf_clob).
  #[local] Abbreviation CLM := (fun r : reg => In r gf_mid).

  (* [comment removed for export] *)
  Definition gf_frame : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
      (at_ sp (-8)) (LE8 ra)) (at_ sp (-16)) (LE8 (getr regs 8))) (at_ sp (-24)) (LE8 (getr regs 9)))
      (at_ sp (-32)) (LE8 (getr regs 18))) (at_ sp (-40)) (LE8 (getr regs 19))) (at_ sp (-48)) (LE8 (getr regs 20)))
      (at_ sp (-56)) (LE8 (getr regs 21))) (at_ sp (-64)) (LE8 (getr regs 22))) (at_ sp (-72)) (LE8 (getr regs 23)))
      (at_ sp (-80)) (LE8 (getr regs 24))) (at_ sp (-88)) (LE8 (getr regs 25))) (at_ sp (-96)) (LE8 (getr regs 26)))
      (at_ sp (-104)) (LE8 (getr regs 27)).
  Lemma gf_frame_outside : forall x : word, (U x < U sp - 128 \/ U sp <= U x)%Z -> gf_frame x = mem x.
  Proof using G1 GSPB SPB chp rb.
    intros x Hx. pose proof (u64_range sp). destruct G1 as [G1a G1b]. (lazymatch goal with |- ?G => let G' := eval unfold gf_frame in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. reflexivity.
  Qed.
  Lemma gf_frame_grows : mem_grows mem gf_frame.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold gf_frame in G in change_no_check G' end). do 13 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Lemma gf_frame_slots : forall (k : Z) (v : word),
    In (k, v) [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19); (-48, getr regs 20);
               (-56, getr regs 21); (-64, getr regs 22); (-72, getr regs 23); (-80, getr regs 24); (-88, getr regs 25);
               (-96, getr regs 26); (-104, getr regs 27)]%Z ->
    rdn segs gf_frame (at_ sp k) 8 = Some (LE8 v).
  Proof using G1 GSPB SPB chp rb.
    intros k v Hin. pose proof (u64_range sp). destruct G1 as [G1a G1b]. (lazymatch goal with |- ?G => let G' := eval unfold gf_frame in G in change_no_check G' end). cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin.
  Qed.

  (* [comment removed for export] *)
  Definition gf_m2 : word -> option byte :=
    wbytes (wbytes gf_frame RI (LE8 (Z_to_bv 64 (2 ^ 60)))) (at_ RI 16) (LE8 (Z_to_bv 64 (nf - m))).
  Lemma gf_m2_outside : forall x : word,
    (U x < U sp - 128 \/ U sp <= U x)%Z -> (U x < RIz \/ RIz + 8 <= U x)%Z -> (U x < RIz + 16 \/ RIz + 24 <= U x)%Z -> gf_m2 x = mem x.
  Proof using Gchp G1 GSPB Hc chp rb.
    intros x Hx Hy Hz. pose proof (u64_range sp). destruct G1 as [G1a G1b]. destruct GSPB as (S1 & S2 & S3 & S4). (lazymatch goal with |- ?G => let G' := eval unfold gf_m2 in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia.
    apply gf_frame_outside. exact Hx.
  Qed.

  Ltac sokS Hs0 lo N :=
    repeat (eapply store_ok_mono; [apply wbytes_grows|]);
    eapply (store_ok_sub segs mem lo _ N); [rewrite ?at_u; lia | exact Hs0 | rewrite ?at_u; lia | rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia].
  Ltac fsd8 F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | sokS Hstk (at_ sp (-128)) 128%nat ]
      | step_simpl]; vn.
  Ltac vz := cbv delta [v_add v_addi v_mul v_slli v_srli v_sub v_and v_or] beta; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia; unorm;
             first [reflexivity | f_equal; lia | apply bv_eq; wd_ulia].
  (* [comment removed for export] *)
  Ltac vaddi_at := repeat match goal with |- context [v_addi ?a ?k] => change (v_addi a k) with (at_ a k) end.
  (* [comment removed for export] *)
  Ltac fld8 F D vv R := chain_step; [reflexivity
      | eapply step_ld with (bs := LE8 vv) (v := vv);
        [exact F | reflexivity | exact D | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi, ?at_at; vaddi_at; zlit_at; R | apply bytes_le_to_Z_8]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  Lemma gfA :
    exists r,
      msteps segs (mkst regs (at_ rb 0x5153c) mem rom) (mkst r (at_ rb 0x516b0) gf_m2 rom)
      /\ getr r 2 = at_ sp (-128) /\ getr r 8 = RI /\ getr r 19 = Z_to_bv 64 (2 ^ 61) /\ getr r 20 = Z_to_bv 64 (FABz + 4 * (nf - m))
      /\ getr r 11 = at_ chp (4 * m) /\ getr r 13 = chp /\ getr r 14 = Z_to_bv 64 m
      /\ regs_agree CLM regs r.
  Proof using SOKnf Rnf SOKmu Rmu Rrib Rspb Hstk Gchp Galloc G1 GSPB Hm Hc H14 H13 H12 H10 H2 H1 alloc HGF.
    destruct G1 as [G1a G1b]. destruct Hm as (Hm1 & Hm2 & Hm3). destruct GSPB as (S1 & S2 & S3 & S4). destruct Gchp as (C1 & C2 & C3 & C4). destruct Galloc as [A1 A2].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range alloc). pose proof (u64_range chp).
    assert (RI8 : (RIz mod 8 = 0)%Z) by (clear - S3 Hc; Z.div_mod_to_equations; lia).
    wd_eexists. split.
    - an G5153c D_5153c.                                   (* [comment removed for export] *)
      fsd8 G51540 D_51540 (at_ sp (-8)).                   (* [comment removed for export] *)
      fsd8 G51544 D_51544 (at_ sp (-16)).                  (* [comment removed for export] *)
      fsd8 G51548 D_51548 (at_ sp (-24)).                  (* [comment removed for export] *)
      fsd8 G5154c D_5154c (at_ sp (-32)).                  (* [comment removed for export] *)
      fsd8 G51550 D_51550 (at_ sp (-40)).                  (* [comment removed for export] *)
      fsd8 G51554 D_51554 (at_ sp (-48)).                  (* [comment removed for export] *)
      fsd8 G51558 D_51558 (at_ sp (-56)).                  (* [comment removed for export] *)
      fsd8 G5155c D_5155c (at_ sp (-64)).                  (* [comment removed for export] *)
      fsd8 G51560 D_51560 (at_ sp (-72)).                  (* [comment removed for export] *)
      fsd8 G51564 D_51564 (at_ sp (-80)).                  (* [comment removed for export] *)
      fsd8 G51568 D_51568 (at_ sp (-88)).                  (* [comment removed for export] *)
      fsd8 G5156c D_5156c (at_ sp (-96)).                  (* [comment removed for export] *)
      fsd8 G51570 D_51570 (at_ sp (-104)).                 (* [comment removed for export] *)
      change (wbytes _ _ _) with gf_frame.
      an G51574 D_51574.                                   (* [comment removed for export] *)
      an G51578 D_51578.                                   (* [comment removed for export] *)
      an G5157c D_5157c.                                   (* [comment removed for export] *)
      fld8 G51580 D_51580 (Z_to_bv 64 SPB) ltac:(rewrite <- Rspb; apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply gf_frame_outside; rewrite at_u in Hx by lia; cbn in Hx; lia]).   (* [comment removed for export] *)
      fld8 G51584 D_51584 (Z_to_bv 64 (SPB + 2 ^ 37)) ltac:(rewrite <- Rrib; apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply gf_frame_outside; rewrite at_u in Hx by lia; cbn in Hx; lia]).   (* [comment removed for export] *)
      av G51588 D_51588 (Z_to_bv 64 (128 * c)) ltac:(vz).          (* [comment removed for export] *)
      av G5158c D_5158c (Z_to_bv 64 (c * 2 ^ 32)) ltac:(vz).       (* [comment removed for export] *)
      an G51590 D_51590.                                   (* [comment removed for export] *)
      an G51594 D_51594.                                   (* [comment removed for export] *)
      av G51598 D_51598 (Z_to_bv 64 (2 ^ 61)) ltac:(vz).           (* [comment removed for export] *)
      av G5159c D_5159c (Z_to_bv 64 3758096384) ltac:(vz).         (* [comment removed for export] *)
      av G515a0 D_515a0 (Z_to_bv 64 (2 ^ 40)) ltac:(vz).           (* [comment removed for export] *)
      av G515a4 D_515a4 (Z_to_bv 64 (c * 2 ^ 32 + 3758096384)) ltac:(vz).   (* [comment removed for export] *)
      av G515a8 D_515a8 (Z_to_bv 64 (2 ^ 40 + 1)) ltac:(vz).       (* [comment removed for export] *)
      av G515ac D_515ac (Z_to_bv 64 (2 ^ 60 + 2 ^ 20)) ltac:(vz).  (* [comment removed for export] *)
      av G515b0 D_515b0 constr:(RI) ltac:(vz).                      (* [comment removed for export] *)
      av G515b4 D_515b4 (Z_to_bv 64 FABz) ltac:(vz).       (* [comment removed for export] *)
      av G515b8 D_515b8 (Z_to_bv 64 (2 ^ 60 + 2 ^ 20 - 1)) ltac:(vz).   (* [comment removed for export] *)
      fld8 G515bc D_515bc (Z_to_bv 64 0) ltac:(rewrite <- Rmu; apply rdn_ext; [wd_ulia_c | intros x Hx; apply gf_frame_outside; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia]).   (* [comment removed for export] *)
      av G515c0 D_515c0 (Z_to_bv 64 (RIz + 8)) ltac:(vz).  (* [comment removed for export] *)
      av G515c4 D_515c4 (Z_to_bv 64 (2 ^ 60)) ltac:(vz).    (* [comment removed for export] *)
      an G515c8 D_515c8.                                     (* [comment removed for export] *)
      an G515cc D_515cc.   (* [comment removed for export] *)
      an G515d0 D_515d0.   (* [comment removed for export] *)
      an G515d4 D_515d4.           (* [comment removed for export] *)
      ab_ft G515d8 D_515d8 ltac:(condz).                    (* [comment removed for export] *)
      an G515dc D_515dc.    (* [comment removed for export] *)
      an G515e0 D_515e0.    (* [comment removed for export] *)
      (* [comment removed for export] *)
      eapply msteps_trans.
      { eapply (cas_d_run segs _ (at_ rb 0x515e4) (at_ rb 0x515e8) (at_ rb 0x515ec) (at_ rb 0x515f0) (at_ rb 0x515f4) gf_frame rom
                  _ _ _ _ _ _ _ _ 5 8 7 6 5 17 BC_NE _ _ (LE8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
                  G515e4 eq_refl D_515e4 G515e8 eq_refl D_515e8 G515ec eq_refl D_515ec G515f0 eq_refl D_515f0);
          rewrite ?at_addi; try reflexivity.
        all: lazymatch goal with
             | |- _ <> _ => intros X; discriminate X
             | |- (_ mod 8 = 0)%Z => gres; unorm; exact RI8
             | |- rdn _ _ _ _ = _ => gres; rewrite <- Rmu; apply rdn_ext; [wd_ulia_c | intros x Hx; apply gf_frame_outside; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia]
             | |- store_ok _ _ _ _ = true => gres; eapply store_ok_mono; [apply gf_frame_grows | exact SOKmu]
             | |- branch_taken _ _ _ = false => (lazymatch goal with |- ?G => let G' := eval cbn [branch_taken] in G in change_no_check G' end); gres; rewrite bv_eqb_refl; reflexivity
             | |- _ => apply bytes_le_to_Z_8
             end. }
      gres.
      ab_tk G515f4 D_515f4 ltac:(condz).                    (* [comment removed for export] *)
      fld8 G5168c D_5168c (Z_to_bv 64 nf) ltac:(rewrite wc_rdn_wbytes_out3; [ | rd8_side ];
                 rewrite <- Rnf; apply rdn_ext; [rewrite at_u by (wd_ulia); wd_ulia_c | intros x Hx; apply gf_frame_outside; rewrite at_u in Hx by (wd_ulia); revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia]).   (* [comment removed for export] *)
      ab_ft G51690 D_51690 ltac:(condz).                    (* [comment removed for export] *)
      av G51694 D_51694 (Z_to_bv 64 (nf - m)) ltac:(vz).    (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sd_at with (a := at_ RI 16);
          [exact G51698 | reflexivity | exact D_51698
          | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
          | gres; rwH; reflexivity
          | eapply store_ok_mono; [eapply mem_grows_trans; [apply gf_frame_grows | apply wbytes_grows] | exact SOKnf] ]
        | step_simpl]; vn.                                   (* [comment removed for export] *)
      change (wbytes (wbytes gf_frame _ _) _ _) with gf_m2.
      ab_ft G5169c D_5169c ltac:(condz).                    (* [comment removed for export] *)
      av G516a0 D_516a0 (Z_to_bv 64 (4 * (nf - m))) ltac:(vz).   (* [comment removed for export] *)
      av G516a4 D_516a4 (Z_to_bv 64 (FABz + 4 * (nf - m))) ltac:(vz).   (* [comment removed for export] *)
      av G516a8 D_516a8 (Z_to_bv 64 (4 * m)) ltac:(vz).      (* [comment removed for export] *)
      av G516ac D_516ac (at_ chp (4 * m)) ltac:(rewrite v_add_at by lia; reflexivity).   (* [comment removed for export] *)
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold gf_mid in G in change_no_check G' end). ra_solve.
  Qed.

  (* [comment removed for export] *)
  Fixpoint gf_cp (i : nat) : word -> option byte :=
    match i with
    | O => gf_m2
    | S i' => wbytes (gf_cp i') (at_ chp (4 * Z.of_nat i')) (LE4 (faf (nf - m + Z.of_nat i')%Z))
    end.
  Lemma gf_cp_grows : forall i, mem_grows gf_m2 (gf_cp i).
  Proof using. induction i as [|i IH]; [apply mem_grows_refl|]. (lazymatch goal with |- ?G => let G' := eval cbn [gf_cp] in G in change_no_check G' end). eapply mem_grows_trans; [exact IH | apply wbytes_grows]. Qed.
  Lemma gf_m2_grows : mem_grows mem gf_m2.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold gf_m2 in G in change_no_check G' end). eapply mem_grows_trans; [apply gf_frame_grows|]. eapply mem_grows_trans; apply wbytes_grows. Qed.
  Lemma gf_cp_outside : forall i (x : word), (Z.of_nat i <= m)%Z -> (U x < U chp \/ U chp + 4 * Z.of_nat i <= U x)%Z -> gf_cp i x = gf_m2 x.
  Proof using Gchp G1 GSPB Hm rb.
    induction i as [|i IH]; intros x Hi Hx; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [gf_cp] in G in change_no_check G' end). pose proof (u64_range chp). destruct Gchp as (C1 & C2 & C3 & C4). pose proof (u64_range sp).
    rewrite wbytes_outside; [apply IH; lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
  Qed.

  Lemma gfL : forall (j i : nat) r,
      (Z.of_nat i + Z.of_nat j = m)%Z -> (1 <= Z.of_nat j)%Z ->
      getr r 13 = at_ chp (4 * Z.of_nat i) -> getr r 20 = Z_to_bv 64 (FABz + 4 * (nf - m) + 4 * Z.of_nat i) -> getr r 11 = at_ chp (4 * m) ->
      exists r',
        msteps segs (mkst r (at_ rb 0x516b0) (gf_cp i) rom) (mkst r' (at_ rb 0x516c4) (gf_cp (Z.to_nat m)) rom)
        /\ (forall x : reg, ~ In x [12; 13; 20] -> getr r' x = getr r x).
  Proof using G1 GSPB Galloc Gchp Ggm HGF Hc Hfaf Hm RB SOKch.
    induction j as [|j IH]; intros i r Hij Hj R13 R20 R11; [lia|].
    destruct G1 as [G1a G1b]. destruct Hm as (Hm1 & Hm2 & Hm3). destruct GSPB as (S1 & S2 & S3 & S4). destruct Gchp as (C1 & C2 & C3 & C4).
    pose proof (u64_range sp) as Hspr. pose proof (u64_range chp).
    destruct (Hfaf (nf - m + Z.of_nat i)%Z ltac:(lia)) as [Rf Bf].
    assert (RD : rdn segs (gf_cp i) (Z_to_bv 64 (FABz + 4 * (nf - m) + 4 * Z.of_nat i)) 4 = Some (LE4 (faf (nf - m + Z.of_nat i)%Z))).
    { rewrite <- Rf. replace (FABz + 4 * (nf - m + Z.of_nat i))%Z with (FABz + 4 * (nf - m) + 4 * Z.of_nat i)%Z by lia.
      apply rdn_ext; [wd_ulia_c|]. intros x Hx. revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx.
      rewrite gf_cp_outside by lia. apply gf_m2_outside; lia. }
    assert (SOK : store_ok segs (gf_cp i) (at_ chp (4 * Z.of_nat i)) 4 = true).
    { eapply store_ok_mono; [eapply mem_grows_trans; [apply gf_m2_grows | apply gf_cp_grows]|].
      eapply (store_ok_sub segs mem chp _ (Z.to_nat (4 * m))); [lia | exact SOKch | rewrite at_u; lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia]. }
    (* [comment removed for export] *)
    assert (BODY : exists r1, msteps segs (mkst r (at_ rb 0x516b0) (gf_cp i) rom) (mkst r1 (at_ rb 0x516c0) (gf_cp (S i)) rom)
              /\ getr r1 13 = at_ chp (4 * Z.of_nat (S i)) /\ getr r1 20 = Z_to_bv 64 (FABz + 4 * (nf - m) + 4 * Z.of_nat (S i)) /\ getr r1 11 = at_ chp (4 * m)
              /\ (forall x : reg, ~ In x [12; 13; 20] -> getr r1 x = getr r x)).
    { wd_eexists. split.
      - chain_step; [reflexivity
          | eapply step_lw with (bs := LE4 (faf (nf - m + Z.of_nat i)%Z)) (v := Z_to_bv 64 (faf (nf - m + Z.of_nat i)%Z));
            [exact G516b0 | reflexivity | exact D_516b0 | gres; rewrite R20; imm_norm; rewrite ?v_addi_0; exact RD | apply bytes4_small; lia]
          | step_simpl]; vn.                               (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sw_at with (a := at_ chp (4 * Z.of_nat i));
            [exact G516b4 | reflexivity | exact D_516b4
            | gres; rewrite R13; imm_norm; rewrite ?v_addi_0, ?at_addi, ?at_add_0_r; reflexivity
            | gres; reflexivity
            | exact SOK ]
          | step_simpl]; vn.                               (* [comment removed for export] *)
        rewrite (LE4_lw (faf (nf - m + Z.of_nat i)%Z)) by lia. change (wbytes (gf_cp i) _ _) with (gf_cp (S i)).
        an G516b8 D_516b8.                                 (* [comment removed for export] *)
        an G516bc D_516bc.                                 (* [comment removed for export] *)
        wd_refl.
      - split; [gres; rewrite ?at_at; f_equal; lia|]. split; [gres; vaddi_at; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia|].
        split; [gres; first [exact R11 | rewrite R11; reflexivity]|].
        intros x Hx. gres. rewrite !getr_other; [reflexivity| | |]; intros E; apply Hx; rewrite <- E; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]. }
    destruct BODY as (r1 & RUN1 & Q13 & Q20 & Q11 & QK).
    destruct (Z.eq_dec (Z.of_nat j) 0) as [Zj|NZj].
    - (* [comment removed for export] *)
      exists r1. split.
      + eapply msteps_trans; [exact RUN1|].
        ab_ft G516c0 D_516c0 ltac:(condz).
        replace (Z.to_nat m) with (S i) by lia. wd_refl.
      + exact QK.
    - destruct (IH (S i) r1 ltac:(lia) ltac:(lia) Q13 Q20 Q11) as (r' & RUN' & QK').
      exists r'. split.
      + eapply msteps_trans; [exact RUN1|].
        ab_tk G516c0 D_516c0 ltac:(condz).
        exact RUN'.
      + intros x Hx. rewrite (QK' x Hx). exact (QK x Hx).
  Qed.

  (* [comment removed for export] *)
  Definition gf_m4 : word -> option byte := wbytes (gf_cp (Z.to_nat m)) (at_ RI 72) (LE8 (v_add stv (Z_to_bv 64 m))).
  Definition gf_m5 : word -> option byte := wbytes gf_m4 RI (LE8 (Z_to_bv 64 0)).

  Lemma gf_m4_low : forall x : word, (U x < RIz \/ RIz + 80 <= U x)%Z -> (U x < U chp \/ U chp + 4 * m <= U x)%Z -> (U x < U sp - 128 \/ U sp <= U x)%Z -> gf_m4 x = mem x.
  Proof using Gchp G1 GSPB Hm Hc rb.
    intros x H1x H2x H3x. destruct G1 as [G1a G1b]. destruct Hm as (Hm1 & Hm2 & Hm3). destruct GSPB as (S1 & S2 & S3 & S4). destruct Gchp as (C1 & C2 & C3 & C4).
    pose proof (u64_range sp). pose proof (u64_range chp). (lazymatch goal with |- ?G => let G' := eval unfold gf_m4 in G in change_no_check G' end).
    rewrite wbytes_outside; [| rewrite length_N_to_le_bytes, at_u by (wd_ulia); wd_ulia_c | rewrite length_N_to_le_bytes, at_u by (wd_ulia); wd_ulia_c].
    rewrite gf_cp_outside by lia. apply gf_m2_outside; lia.
  Qed.
  Lemma gf_m5_frame : forall x : word, (U sp - 128 <= U x < U sp)%Z -> gf_m5 x = gf_frame x.
  Proof using Gchp G1 GSPB Hm Hc rb.
    intros x Hx. destruct G1 as [G1a G1b]. destruct Hm as (Hm1 & Hm2 & Hm3). destruct GSPB as (S1 & S2 & S3 & S4). destruct Gchp as (C1 & C2 & C3 & C4).
    pose proof (u64_range sp). pose proof (u64_range chp). (lazymatch goal with |- ?G => let G' := eval unfold gf_m5, gf_m4 in G in change_no_check G' end).
    rewrite wbytes_outside; [| rewrite length_N_to_le_bytes; wd_ulia_c | rewrite length_N_to_le_bytes; wd_ulia_c].
    rewrite wbytes_outside; [| rewrite length_N_to_le_bytes, at_u by (wd_ulia); wd_ulia_c | rewrite length_N_to_le_bytes, at_u by (wd_ulia); wd_ulia_c].
    rewrite gf_cp_outside by lia. (lazymatch goal with |- ?G => let G' := eval unfold gf_m2 in G in change_no_check G' end).
    rewrite wbytes_outside; [| rewrite length_N_to_le_bytes, at_u by (wd_ulia); wd_ulia_c | rewrite length_N_to_le_bytes, at_u by (wd_ulia); wd_ulia_c].
    rewrite wbytes_outside; [reflexivity | rewrite length_N_to_le_bytes; wd_ulia_c | rewrite length_N_to_le_bytes; wd_ulia_c].
  Qed.
  Lemma gf_mu4 : rdn segs gf_m4 RI 8 = Some (LE8 (Z_to_bv 64 (2 ^ 60))).
  Proof using Gchp G1 GSPB Hm Hc rb.
    destruct G1 as [G1a G1b]. destruct Hm as (Hm1 & Hm2 & Hm3). destruct GSPB as (S1 & S2 & S3 & S4). destruct Gchp as (C1 & C2 & C3 & C4).
    pose proof (u64_range sp). pose proof (u64_range chp). (lazymatch goal with |- ?G => let G' := eval unfold gf_m4 in G in change_no_check G' end).
    rewrite wc_rdn_wbytes_out3; [ | rd8_side ].
    transitivity (rdn segs gf_m2 RI 8).
    { apply rdn_ext; [wd_ulia_c|]. intros x Hx. revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx. apply gf_cp_outside; lia. }
    (lazymatch goal with |- ?G => let G' := eval unfold gf_m2 in G in change_no_check G' end). rewrite wc_rdn_wbytes_out3; [ | rd8_side ]. apply rdn_wbytes_hit8. unorm. lia.
  Qed.

  Lemma gfB : forall r0,
      getr r0 2 = at_ sp (-128) -> getr r0 8 = RI -> getr r0 19 = Z_to_bv 64 (2 ^ 61) -> getr r0 14 = Z_to_bv 64 m ->
      regs_agree CLM regs r0 ->
      exists r',
        msteps segs (mkst r0 (at_ rb 0x516c4) (gf_cp (Z.to_nat m)) rom) (mkst r' ra gf_m5 rom)
        /\ getr r' 10 = Z_to_bv 64 1 /\ getr r' 2 = sp /\ regs_agree CLX regs r'.
  Proof using G1 GMSK GSPB Galloc Gchp Ggm H1 H10 H12 H13 H14 H2 HGF Hc Hm Hret RB Rmsk Rst SOKmu SOKst.
    intros r0 R2 R8 R19 R14 AG0.
    destruct G1 as [G1a G1b]. destruct Hm as (Hm1 & Hm2 & Hm3). destruct GSPB as (S1 & S2 & S3 & S4). destruct Gchp as (C1 & C2 & C3 & C4). destruct Galloc as [A1 A2]. destruct Ggm as [Gg1 Gg2].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range chp). pose proof (u64_range stv).
    assert (RI8 : (RIz mod 8 = 0)%Z) by (clear - S3 Hc; Z.div_mod_to_equations; lia).
    destruct GMSK as (xm & GMa & GMb).
    assert (Rst3 : rdn segs (gf_cp (Z.to_nat m)) (at_ RI 72) 8 = Some (LE8 stv)).
    { rewrite <- Rst. apply rdn_ext; [rewrite at_u by (wd_ulia); wd_ulia_c|]. intros x Hx. rewrite at_u in Hx by (wd_ulia). revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx.
      rewrite gf_cp_outside by lia. apply gf_m2_outside; lia. }
    assert (Rmsk4 : rdn segs gf_m4 (Z_to_bv 64 gmsk) 8 = Some (LE8 msk)).
    { rewrite <- Rmsk. apply rdn_ext; [wd_ulia_c|]. intros x Hx. revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx. apply gf_m4_low; lia. }
    assert (FR5 : forall (k : Z) (v : word),
      In (k, v) [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19); (-48, getr regs 20);
                 (-56, getr regs 21); (-64, getr regs 22); (-72, getr regs 23); (-80, getr regs 24); (-88, getr regs 25);
                 (-96, getr regs 26); (-104, getr regs 27)]%Z ->
      rdn segs gf_m5 (at_ sp k) 8 = Some (LE8 v)).
    { intros k v Hin. rewrite <- (gf_frame_slots k v Hin).
      assert (Hk : (-128 <= k <= -8)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply gf_m5_frame. lia. }
    wd_eexists. split; [|split; [|split]].
    - fld8 G516c4 D_516c4 stv ltac:(exact Rst3).        (* [comment removed for export] *)
      an G516c8 D_516c8.                                   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sd_at with (a := at_ RI 72);
          [exact G516cc | reflexivity | exact D_516cc
          | gres; rwH; imm_norm; vaddi_at; rewrite ?at_addi; first [reflexivity | f_equal; lia]
          | gres; rwH; reflexivity
          | eapply store_ok_mono; [eapply mem_grows_trans; [apply gf_m2_grows | apply gf_cp_grows] | exact SOKst] ]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      change (wbytes (gf_cp _) _ _) with gf_m4.
      an G516d0 D_516d0.                                   (* [comment removed for export] *)
      fld8 G516d4 D_516d4 (Z_to_bv 64 (2 ^ 60)) ltac:(rewrite <- (at_0 RI) at 1; rewrite ?at_0; exact gf_mu4).   (* [comment removed for export] *)
      an G516d8 D_516d8.                                   (* [comment removed for export] *)
      an G516dc D_516dc.                                   (* [comment removed for export] *)
      an G516e0 D_516e0.                                   (* [comment removed for export] *)
      eapply msteps_trans; [apply GMa|]. zlit_at.          (* [comment removed for export] *)
      an G516e8 D_516e8.                                   (* [comment removed for export] *)
      an G516ec D_516ec.                                   (* [comment removed for export] *)
      an G516f0 D_516f0.                                   (* [comment removed for export] *)
      eapply msteps_trans; [eapply GMb; [gres; reflexivity | exact Rmsk4]|]. zlit_at.   (* [comment removed for export] *)
      an G516f8 D_516f8.                                   (* [comment removed for export] *)
      an G516fc D_516fc.                                   (* [comment removed for export] *)
      an G51700 D_51700.                                   (* [comment removed for export] *)
      an G51704 D_51704.                                   (* [comment removed for export] *)
      an G51708 D_51708.                                   (* [comment removed for export] *)
      an G5170c D_5170c.                                   (* [comment removed for export] *)
      an G51728 D_51728.                                   (* [comment removed for export] *)
      an G5172c D_5172c.                                   (* [comment removed for export] *)
      ab_ft G51730 D_51730 ltac:(condz).                  (* [comment removed for export] *)
      an G51734 D_51734.                                   (* [comment removed for export] *)
      ab_tk G51738 D_51738 ltac:(condz).                  (* [comment removed for export] *)
      an G5175c D_5175c.                                   (* [comment removed for export] *)
      an G51760 D_51760.                                   (* [comment removed for export] *)
      an G51764 D_51764.                                   (* [comment removed for export] *)
      an G51768 D_51768.                                   (* [comment removed for export] *)
      an G5176c D_5176c.                                   (* [comment removed for export] *)
      an G51770 D_51770.                                   (* [comment removed for export] *)
      an G51774 D_51774.                                   (* [comment removed for export] *)
      ab_tk G51778 D_51778 ltac:(condz).                  (* [comment removed for export] *)
      eapply msteps_trans.
      { eapply (cas_d_run segs _ (at_ rb 0x51710) (at_ rb 0x51714) (at_ rb 0x51718) (at_ rb 0x5171c) (at_ rb 0x51720) gf_m4 rom
                  _ _ _ _ _ _ _ _ 7 8 28 6 7 12 BC_NE _ _ (LE8 (Z_to_bv 64 (2 ^ 60))) (Z_to_bv 64 (2 ^ 60))
                  G51710 eq_refl D_51710 G51714 eq_refl D_51714 G51718 eq_refl D_51718 G5171c eq_refl D_5171c);
          rewrite ?at_addi; try reflexivity.
        all: lazymatch goal with
             | |- _ <> _ => intros X; discriminate X
             | |- (_ mod 8 = 0)%Z => gres; rwH; unorm; exact RI8
             | |- rdn _ _ _ _ = _ => gres; rwH; exact gf_mu4
             | |- store_ok _ _ _ _ = true => gres; rwH; (lazymatch goal with |- ?G => let G' := eval unfold gf_m4 in G in change_no_check G' end); eapply store_ok_mono; [|exact SOKmu];
                                              eapply mem_grows_trans; [apply gf_m2_grows|]; eapply mem_grows_trans; [apply gf_cp_grows | apply wbytes_grows]
             | |- branch_taken _ _ _ = false => (lazymatch goal with |- ?G => let G' := eval cbn [branch_taken] in G in change_no_check G' end); gres; rewrite bv_eqb_refl; reflexivity
             | |- _ => apply bytes_le_to_Z_8
             end. }
      gres. rwH. change (wbytes gf_m4 _ _) with gf_m5.
      ab_tk G51720 D_51720 ltac:(condz).                  (* [comment removed for export] *)
      ab_tk G51788 D_51788 ltac:(condz).                  (* [comment removed for export] *)
      an G5179c D_5179c.                                   (* [comment removed for export] *)
      Ltac cldF F D vv H := chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 vv) (v := vv);
          [exact F | reflexivity | exact D | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi, ?at_at; zlit_at; apply H; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])] | apply bytes_le_to_Z_8]
        | step_simpl]; vn.
      cldF G517a0 D_517a0 ra (FR5 (-8)%Z).                          (* [comment removed for export] *)
      cldF G517a4 D_517a4 (getr regs 8) (FR5 (-16)%Z).              (* [comment removed for export] *)
      cldF G517a8 D_517a8 (getr regs 9) (FR5 (-24)%Z).              (* [comment removed for export] *)
      cldF G517ac D_517ac (getr regs 18) (FR5 (-32)%Z).             (* [comment removed for export] *)
      cldF G517b0 D_517b0 (getr regs 19) (FR5 (-40)%Z).             (* [comment removed for export] *)
      cldF G517b4 D_517b4 (getr regs 20) (FR5 (-48)%Z).             (* [comment removed for export] *)
      cldF G517b8 D_517b8 (getr regs 21) (FR5 (-56)%Z).             (* [comment removed for export] *)
      cldF G517bc D_517bc (getr regs 22) (FR5 (-64)%Z).             (* [comment removed for export] *)
      cldF G517c0 D_517c0 (getr regs 23) (FR5 (-72)%Z).             (* [comment removed for export] *)
      cldF G517c4 D_517c4 (getr regs 24) (FR5 (-80)%Z).             (* [comment removed for export] *)
      cldF G517c8 D_517c8 (getr regs 25) (FR5 (-88)%Z).             (* [comment removed for export] *)
      cldF G517cc D_517cc (getr regs 26) (FR5 (-96)%Z).             (* [comment removed for export] *)
      cldF G517d0 D_517d0 (getr regs 27) (FR5 (-104)%Z).            (* [comment removed for export] *)
      an G517d4 D_517d4.                                   (* [comment removed for export] *)
      aret G517d8 D_517d8 ra.                              (* [comment removed for export] *)
      wd_refl.
    - gres. reflexivity.
    - gres. rewrite ?at_at. first [reflexivity | apply bv_eq; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]].
    - apply (regs_agree_strengthen rf_clob gf_mid regs).
      + (lazymatch goal with |- ?G => let G' := eval unfold gf_mid in G in change_no_check G' end).
        repeat (first [ apply regs_agree_upd; [solve [in_list] |]
                      | apply regs_agree_upd_keep; [ | first [reflexivity | rwH; rewrite ?at_0; reflexivity | symmetry; assumption] | let X := fresh in intros X; discriminate X ] ]).
        exact AG0.
      + intros i Hi Hni. cbn [gf_mid In] in Hi.
        repeat (destruct Hi as [<-|Hi]; [gres; rwH; rewrite ?at_at, ?at_addi, ?at_0; first [reflexivity | symmetry; assumption | apply bv_eq; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | f_equal; lia | exfalso; apply Hni; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]] |]).
        destruct Hi.
  Qed.

  (* [comment removed for export] *)
  Theorem gf_run :
    exists r', msteps segs (mkst regs (at_ rb 0x5153c) mem rom) (mkst r' ra gf_m5 rom)
      /\ getr r' 10 = Z_to_bv 64 1 /\ getr r' 2 = sp /\ regs_agree CLX regs r'.
  Proof using G1 GMSK GSPB Galloc Gchp Ggm H1 H10 H12 H13 H14 H2 HGF Hc Hfaf Hm Hret Hstk RB Rmsk Rmu Rnf Rrib Rspb Rst SOKch SOKmu SOKnf SOKst.
    destruct Hm as (Hm1 & Hm2 & Hm3).
    destruct gfA as (r1 & RUN1 & P2 & P8 & P19 & P20 & P11 & P13 & P14 & AG1).
    destruct (gfL (Z.to_nat m) 0 r1 ltac:(lia) ltac:(lia) ltac:(rewrite P13; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat] in G in change_no_check G' end); rewrite Z.mul_0_r, at_0; reflexivity)
                ltac:(rewrite P20; f_equal; lia) P11) as (r2 & RUN2 & QK).
    assert (AG2 : regs_agree CLM regs r2).
    { intros x Hx. rewrite QK; [exact (AG1 x Hx)|]. intros Hin. apply Hx. (lazymatch goal with |- ?G => let G' := eval unfold gf_mid in G in change_no_check G' end). cbn [In] in Hin |- *. clear - Hin. am_tauto. }
    destruct (gfB r2 ltac:(rewrite QK by notin; exact P2) ltac:(rewrite QK by notin; exact P8) ltac:(rewrite QK by notin; exact P19)
                ltac:(rewrite QK by notin; exact P14) AG2) as (r3 & RUN3 & Q10 & Q2 & AG3).
    exists r3. split; [|exact (conj Q10 (conj Q2 AG3))].
    eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
  Qed.

  (* [comment removed for export] *)
  Lemma gf_m5_grows : mem_grows mem gf_m5.
  Proof using.
    (lazymatch goal with |- ?G => let G' := eval unfold gf_m5, gf_m4 in G in change_no_check G' end). eapply mem_grows_trans; [apply gf_m2_grows|]. eapply mem_grows_trans; [apply gf_cp_grows|].
    eapply mem_grows_trans; apply wbytes_grows.
  Qed.
  Lemma gf_m5_outside : forall x : word,
    (U x < U sp - 128 \/ U sp <= U x)%Z -> (U x < RIz \/ RIz + 8 <= U x)%Z -> (U x < RIz + 16 \/ RIz + 24 <= U x)%Z ->
    (U x < RIz + 72 \/ RIz + 80 <= U x)%Z -> (U x < U chp \/ U chp + 4 * m <= U x)%Z -> gf_m5 x = mem x.
  Proof using Gchp G1 GSPB Hm Hc rb.
    intros x F1 F2 F3 F4 F5. destruct G1 as [G1a G1b]. destruct Hm as (Hm1 & Hm2 & Hm3). destruct GSPB as (S1 & S2 & S3 & S4). destruct Gchp as (C1 & C2 & C3 & C4).
    pose proof (u64_range sp). pose proof (u64_range chp). (lazymatch goal with |- ?G => let G' := eval unfold gf_m5, gf_m4 in G in change_no_check G' end).
    rewrite wbytes_outside; [| rewrite length_N_to_le_bytes; wd_ulia_c | rewrite length_N_to_le_bytes; wd_ulia_c].
    rewrite wbytes_outside; [| rewrite length_N_to_le_bytes, at_u by (wd_ulia); wd_ulia_c | rewrite length_N_to_le_bytes, at_u by (wd_ulia); wd_ulia_c].
    rewrite gf_cp_outside by lia. apply gf_m2_outside; lia.
  Qed.





End GF.
End FPGen1.
