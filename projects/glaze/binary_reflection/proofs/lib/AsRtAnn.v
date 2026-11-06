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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsAtom.
#[local] Unset Lia Cache. #[local] Unset Nia Cache. #[local] Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= ha_first_lia.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPGen1.
Context {fx : FPState}.
#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ann_andi_m8 : forall x : word, v_andi x (-8) = Z_to_bv 64 (U x / 8 * 8)%Z.
Proof using.
  intros x. pose proof (u64_range x). (lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end). change (bv_wrap 64 (-8)) with (2 ^ 64 - 2 ^ 3)%Z.
  rewrite land_m8 by lia. f_equal. pose proof (Z.div_mod (U x) 8 ltac:(lia)). lia.
Qed.
Lemma ann_andi_7 : forall x : word, v_andi x 7 = Z_to_bv 64 (U x mod 8)%Z.
Proof using. intros x. pose proof (u64_range x). (lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end). change (bv_wrap 64 7) with 7%Z. rewrite land_7 by lia. reflexivity. Qed.
Lemma sbyte_range : forall b : byte, (-128 <= bv_signed b <= 127)%Z.
Proof using.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *.
  change (2 ^ Z.of_N 8)%Z with 256%Z in *. change (256 `div` 2)%Z with 128%Z.
  pose proof (Z.mod_pos_bound (U b + 128) 256 ltac:(lia)). lia.
Qed.
Lemma signed_v_lb : forall b : byte, bv_signed (v_lb b) = bv_signed b.
Proof using.
  intros b. pose proof (sbyte_range b). (lazymatch goal with |- ?G => let G' := eval unfold v_lb in G in change_no_check G' end). unfold bv_signed at 1. rewrite Z_to_bv_unsigned.
  (lazymatch goal with |- ?G => let G' := eval unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in G in change_no_check G' end). change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z. change (2 ^ 64 `div` 2)%Z with (2 ^ 63)%Z.
  destruct (Z_lt_le_dec (bv_signed b) 0).
  - replace (bv_signed b mod 2 ^ 64)%Z with (bv_signed b + 2 ^ 64)%Z.
    2:{ symmetry. rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small; lia. }
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small; lia.
  - rewrite (Z.mod_small (bv_signed b)) by lia. rewrite Z.mod_small; lia.
Qed.
Lemma u_v_lb_signed_nz : forall b : byte, bv_signed b <> 0%Z -> U (v_lb b) <> 0%Z.
Proof using.
  intros b Hb. pose proof (sbyte_range b). (lazymatch goal with |- ?G => let G' := eval unfold v_lb in G in change_no_check G' end). rewrite Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap, bv_modulus in G in change_no_check G' end).
  change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z.
  destruct (Z_lt_le_dec (bv_signed b) 0).
  - replace (bv_signed b mod 2 ^ 64)%Z with (bv_signed b + 2 ^ 64)%Z; [lia|].
    symmetry. rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small; lia.
  - rewrite Z.mod_small; lia.
Qed.
(* [comment removed for export] *)
Lemma c_lts_small_lb : forall (x : Z) (b : byte), (0 <= x < 2 ^ 63)%Z ->
  c_lts (Z_to_bv 64 x) (v_lb b) = Z.ltb x (bv_signed b).
Proof using. intros x b Hx. (lazymatch goal with |- ?G => let G' := eval unfold c_lts, bv_lts in G in change_no_check G' end). rewrite bv_signed_small64 by lia. rewrite signed_v_lb. reflexivity. Qed.

(* [comment removed for export] *)
Definition dn8 (x : Z) : Z := (x / 8 * 8)%Z.
Lemma dn8_le : forall x, (dn8 x <= x < dn8 x + 8)%Z.
Proof using. intros x. (lazymatch goal with |- ?G => let G' := eval unfold dn8 in G in change_no_check G' end). pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia. Qed.
Lemma dn8_nonneg : forall x, (0 <= x)%Z -> (0 <= dn8 x)%Z.
Proof using. intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold dn8 in G in change_no_check G' end). pose proof (Z.div_pos x 8 Hx ltac:(lia)). lia. Qed.
Lemma dn8_mod : forall x, (dn8 x mod 8 = 0)%Z.
Proof using. intros x. (lazymatch goal with |- ?G => let G' := eval unfold dn8 in G in change_no_check G' end). apply Z_mod_mult. Qed.
Lemma dn8_mono : forall x y, (x <= y)%Z -> (dn8 x <= dn8 y)%Z.
Proof using. intros x y H. (lazymatch goal with |- ?G => let G' := eval unfold dn8 in G in change_no_check G' end). pose proof (Z.div_le_mono x y 8 ltac:(lia) H). lia. Qed.
Lemma dn8_id : forall x, (x mod 8 = 0)%Z -> dn8 x = x.
Proof using. intros x H. (lazymatch goal with |- ?G => let G' := eval unfold dn8 in G in change_no_check G' end). pose proof (Z.div_mod x 8 ltac:(lia)). lia. Qed.
Lemma dn8_up7 : forall x, (dn8 (x + 7) = dn8 x /\ x mod 8 = 0)%Z \/ (dn8 (x + 7) = dn8 x + 8 /\ x mod 8 <> 0)%Z.
Proof using.
  intros x. (lazymatch goal with |- ?G => let G' := eval unfold dn8 in G in change_no_check G' end). pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
  destruct (Z.eq_dec (x mod 8) 0) as [E|NE].
  - left. split; [|exact E]. replace (x + 7)%Z with (x / 8 * 8 + 7)%Z by lia.
    rewrite Z.div_add_l by lia. change (7 / 8)%Z with 0%Z. lia.
  - right. split; [|exact NE]. replace (x + 7)%Z with ((x / 8 + 1) * 8 + (x mod 8 - 1))%Z by lia.
    rewrite Z.div_add_l by lia. rewrite (Z.div_small (x mod 8 - 1) 8) by lia. lia.
Qed.

(* [comment removed for export] *)
Definition anncc_clob : list reg := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28].
(* [comment removed for export] *)
Definition anncc_clobx : list reg := [1; 2; 8; 9; 18; 19; 20; 21; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28].

(* [comment removed for export] *)
Definition anncc_words : list (option (bv 32)) :=
  [
   Some W_7054c; Some W_70550; Some W_70554; Some W_70558; Some W_7055c; Some W_70560; Some W_70564; Some W_70568;
   Some W_7056c; Some W_70570; Some W_70574; None; None; Some W_70580; Some W_70584; Some W_70588; Some W_7058c;
   Some W_70590; None; None; Some W_7059c; Some W_705a0; Some W_705a4; Some W_705a8; Some W_705ac; Some W_705b0;
   Some W_705b4; Some W_705b8; Some W_705bc; Some W_705c0; Some W_705c4; Some W_705c8; Some W_705cc; Some W_705d0;
   Some W_705d4; Some W_705d8; None; None; Some W_705e4; Some W_705e8; Some W_705ec; Some W_705f0; Some W_705f4;
   Some W_705f8; Some W_705fc; Some W_70600; Some W_70604; Some W_70608; Some W_7060c; Some W_70610; Some W_70614;
   Some W_70618; Some W_7061c; Some W_70620; None; None; Some W_7062c; Some W_70630; Some W_70634; Some W_70638;
   Some W_7063c; Some W_70640; Some W_70644; Some W_70648; Some W_7064c; Some W_70650; Some W_70654; Some W_70658;
   Some W_7065c; Some W_70660; Some W_70664; Some W_70668; Some W_7066c; Some W_70670; Some W_70674; Some W_70678;
   Some W_7067c; Some W_70680; Some W_70684; Some W_70688; Some W_7068c; Some W_70690; Some W_70694; Some W_70698;
   Some W_7069c; Some W_706a0; Some W_706a4; Some W_706a8; Some W_706ac; Some W_706b0; Some W_706b4; None; None;
   None; Some W_706c4; Some W_706c8; Some W_706cc; Some W_706d0; Some W_706d4; Some W_706d8; Some W_706dc; None;
   None; Some W_706e8; Some W_706ec; Some W_706f0; Some W_706f4; Some W_706f8; Some W_706fc; Some W_70700;
   Some W_70704; Some W_70708; Some W_7070c; Some W_70710; Some W_70714; Some W_70718; Some W_7071c; Some W_70720;
   Some W_70724; Some W_70728; Some W_7072c; Some W_70730; Some W_70734; Some W_70738; Some W_7073c; Some W_70740;
   Some W_70744; Some W_70748; Some W_7074c; Some W_70750; Some W_70754; Some W_70758; Some W_7075c; Some W_70760;
   Some W_70764; Some W_70768; Some W_7076c; Some W_70770; Some W_70774; Some W_70778; Some W_7077c; Some W_70780;
   Some W_70784; Some W_70788; Some W_7078c; Some W_70790; Some W_70794; Some W_70798; Some W_7079c; Some W_707a0;
   Some W_707a4; Some W_707a8; Some W_707ac; Some W_707b0; Some W_707b4; Some W_707b8; Some W_707bc; Some W_707c0;
   Some W_707c4; Some W_707c8; Some W_707cc; Some W_707d0; Some W_707d4; Some W_707d8
  ]%list.

Section ANNCC.
  Variable segs : list Segment.
  Variable base : word.
  Variable pt : poison_tab.           (* [comment removed for export] *)
  Variable mt : m2s_tab.              (* [comment removed for export] *)
  Variables g_flags p_flags g_verb p_verb g_shoff p_shoff : Z.
  Hypothesis HCODE : code_ato segs base 0 anncc_words.
  Hypothesis PTOK : poison_tab_ok segs pt.
  Hypothesis PTB : pt_base pt = at_ base (-3908).
  Hypothesis MTOK : m2s_tab_ok segs mt.
  Hypothesis MTB : mt_base mt = at_ base (-2632).
  Hypothesis G44 : gload segs base 44 11 g_flags.
  Hypothesis G72 : gload segs base 72 10 g_verb.
  Hypothesis G404 : gload segs base 404 11 g_shoff.
  Hypothesis Hbase : (U base mod 2 = 0)%Z /\ (4096 <= U base)%Z /\ (U base + 4096 < 2 ^ 64)%Z.

  Lemma Fo0 : fetch_word segs (at_ base 0) = Some W_7054c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 0 _ HCODE eq_refl). Qed.
  Lemma Fo4 : fetch_word segs (at_ base 4) = Some W_70550.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 1 _ HCODE eq_refl). Qed.
  Lemma Fo8 : fetch_word segs (at_ base 8) = Some W_70554.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 2 _ HCODE eq_refl). Qed.
  Lemma Fo12 : fetch_word segs (at_ base 12) = Some W_70558.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 3 _ HCODE eq_refl). Qed.
  Lemma Fo16 : fetch_word segs (at_ base 16) = Some W_7055c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 4 _ HCODE eq_refl). Qed.
  Lemma Fo20 : fetch_word segs (at_ base 20) = Some W_70560.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 5 _ HCODE eq_refl). Qed.
  Lemma Fo24 : fetch_word segs (at_ base 24) = Some W_70564.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 6 _ HCODE eq_refl). Qed.
  Lemma Fo28 : fetch_word segs (at_ base 28) = Some W_70568.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 7 _ HCODE eq_refl). Qed.
  Lemma Fo32 : fetch_word segs (at_ base 32) = Some W_7056c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 8 _ HCODE eq_refl). Qed.
  Lemma Fo36 : fetch_word segs (at_ base 36) = Some W_70570.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 9 _ HCODE eq_refl). Qed.
  Lemma Fo40 : fetch_word segs (at_ base 40) = Some W_70574.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 10 _ HCODE eq_refl). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma Fo52 : fetch_word segs (at_ base 52) = Some W_70580.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 13 _ HCODE eq_refl). Qed.
  Lemma Fo56 : fetch_word segs (at_ base 56) = Some W_70584.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 14 _ HCODE eq_refl). Qed.
  Lemma Fo60 : fetch_word segs (at_ base 60) = Some W_70588.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 15 _ HCODE eq_refl). Qed.
  Lemma Fo64 : fetch_word segs (at_ base 64) = Some W_7058c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 16 _ HCODE eq_refl). Qed.
  Lemma Fo68 : fetch_word segs (at_ base 68) = Some W_70590.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 17 _ HCODE eq_refl). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma Fo80 : fetch_word segs (at_ base 80) = Some W_7059c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 20 _ HCODE eq_refl). Qed.
  Lemma Fo84 : fetch_word segs (at_ base 84) = Some W_705a0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 21 _ HCODE eq_refl). Qed.
  Lemma Fo88 : fetch_word segs (at_ base 88) = Some W_705a4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 22 _ HCODE eq_refl). Qed.
  Lemma Fo92 : fetch_word segs (at_ base 92) = Some W_705a8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 23 _ HCODE eq_refl). Qed.


































  Lemma Fo248 : fetch_word segs (at_ base 248) = Some W_70644.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 62 _ HCODE eq_refl). Qed.
  Lemma Fo252 : fetch_word segs (at_ base 252) = Some W_70648.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 63 _ HCODE eq_refl). Qed.
  Lemma Fo256 : fetch_word segs (at_ base 256) = Some W_7064c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 64 _ HCODE eq_refl). Qed.
  Lemma Fo260 : fetch_word segs (at_ base 260) = Some W_70650.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 65 _ HCODE eq_refl). Qed.
  Lemma Fo264 : fetch_word segs (at_ base 264) = Some W_70654.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 66 _ HCODE eq_refl). Qed.
  Lemma Fo268 : fetch_word segs (at_ base 268) = Some W_70658.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 67 _ HCODE eq_refl). Qed.
  Lemma Fo272 : fetch_word segs (at_ base 272) = Some W_7065c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 68 _ HCODE eq_refl). Qed.
  Lemma Fo276 : fetch_word segs (at_ base 276) = Some W_70660.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 69 _ HCODE eq_refl). Qed.
  Lemma Fo280 : fetch_word segs (at_ base 280) = Some W_70664.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 70 _ HCODE eq_refl). Qed.
  Lemma Fo284 : fetch_word segs (at_ base 284) = Some W_70668.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 71 _ HCODE eq_refl). Qed.
  Lemma Fo288 : fetch_word segs (at_ base 288) = Some W_7066c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 72 _ HCODE eq_refl). Qed.
  Lemma Fo292 : fetch_word segs (at_ base 292) = Some W_70670.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 73 _ HCODE eq_refl). Qed.
  Lemma Fo296 : fetch_word segs (at_ base 296) = Some W_70674.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 74 _ HCODE eq_refl). Qed.
  Lemma Fo300 : fetch_word segs (at_ base 300) = Some W_70678.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 75 _ HCODE eq_refl). Qed.
  Lemma Fo304 : fetch_word segs (at_ base 304) = Some W_7067c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 76 _ HCODE eq_refl). Qed.
  Lemma Fo308 : fetch_word segs (at_ base 308) = Some W_70680.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 77 _ HCODE eq_refl). Qed.
  Lemma Fo312 : fetch_word segs (at_ base 312) = Some W_70684.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 78 _ HCODE eq_refl). Qed.
  Lemma Fo316 : fetch_word segs (at_ base 316) = Some W_70688.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 79 _ HCODE eq_refl). Qed.
  Lemma Fo320 : fetch_word segs (at_ base 320) = Some W_7068c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 80 _ HCODE eq_refl). Qed.
  Lemma Fo324 : fetch_word segs (at_ base 324) = Some W_70690.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 81 _ HCODE eq_refl). Qed.
  Lemma Fo328 : fetch_word segs (at_ base 328) = Some W_70694.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 82 _ HCODE eq_refl). Qed.
  Lemma Fo332 : fetch_word segs (at_ base 332) = Some W_70698.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 83 _ HCODE eq_refl). Qed.
  Lemma Fo336 : fetch_word segs (at_ base 336) = Some W_7069c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 84 _ HCODE eq_refl). Qed.
  Lemma Fo340 : fetch_word segs (at_ base 340) = Some W_706a0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 85 _ HCODE eq_refl). Qed.
  Lemma Fo344 : fetch_word segs (at_ base 344) = Some W_706a4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 86 _ HCODE eq_refl). Qed.
  Lemma Fo348 : fetch_word segs (at_ base 348) = Some W_706a8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 87 _ HCODE eq_refl). Qed.
  Lemma Fo352 : fetch_word segs (at_ base 352) = Some W_706ac.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 88 _ HCODE eq_refl). Qed.
  Lemma Fo356 : fetch_word segs (at_ base 356) = Some W_706b0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 89 _ HCODE eq_refl). Qed.



  Lemma Fo384 : fetch_word segs (at_ base 384) = Some W_706cc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 96 _ HCODE eq_refl). Qed.
  Lemma Fo388 : fetch_word segs (at_ base 388) = Some W_706d0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 97 _ HCODE eq_refl). Qed.
  Lemma Fo392 : fetch_word segs (at_ base 392) = Some W_706d4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 98 _ HCODE eq_refl). Qed.
  Lemma Fo396 : fetch_word segs (at_ base 396) = Some W_706d8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 99 _ HCODE eq_refl). Qed.
  Lemma Fo400 : fetch_word segs (at_ base 400) = Some W_706dc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 100 _ HCODE eq_refl). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma Fo412 : fetch_word segs (at_ base 412) = Some W_706e8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 103 _ HCODE eq_refl). Qed.
  Lemma Fo416 : fetch_word segs (at_ base 416) = Some W_706ec.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 104 _ HCODE eq_refl). Qed.
  Lemma Fo420 : fetch_word segs (at_ base 420) = Some W_706f0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 105 _ HCODE eq_refl). Qed.
  Lemma Fo424 : fetch_word segs (at_ base 424) = Some W_706f4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 106 _ HCODE eq_refl). Qed.
  Lemma Fo428 : fetch_word segs (at_ base 428) = Some W_706f8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 107 _ HCODE eq_refl). Qed.
  Lemma Fo432 : fetch_word segs (at_ base 432) = Some W_706fc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 108 _ HCODE eq_refl). Qed.























  Lemma Fo528 : fetch_word segs (at_ base 528) = Some W_7075c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 132 _ HCODE eq_refl). Qed.
  Lemma Fo532 : fetch_word segs (at_ base 532) = Some W_70760.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 133 _ HCODE eq_refl). Qed.
  Lemma Fo536 : fetch_word segs (at_ base 536) = Some W_70764.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 134 _ HCODE eq_refl). Qed.
  Lemma Fo540 : fetch_word segs (at_ base 540) = Some W_70768.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 135 _ HCODE eq_refl). Qed.
  Lemma Fo544 : fetch_word segs (at_ base 544) = Some W_7076c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 136 _ HCODE eq_refl). Qed.
  Lemma Fo548 : fetch_word segs (at_ base 548) = Some W_70770.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 137 _ HCODE eq_refl). Qed.
  Lemma Fo552 : fetch_word segs (at_ base 552) = Some W_70774.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 138 _ HCODE eq_refl). Qed.
  Lemma Fo556 : fetch_word segs (at_ base 556) = Some W_70778.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 139 _ HCODE eq_refl). Qed.
  Lemma Fo560 : fetch_word segs (at_ base 560) = Some W_7077c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 140 _ HCODE eq_refl). Qed.
  Lemma Fo564 : fetch_word segs (at_ base 564) = Some W_70780.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 141 _ HCODE eq_refl). Qed.
  Lemma Fo568 : fetch_word segs (at_ base 568) = Some W_70784.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 142 _ HCODE eq_refl). Qed.
  Lemma Fo572 : fetch_word segs (at_ base 572) = Some W_70788.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 143 _ HCODE eq_refl). Qed.
  Lemma Fo576 : fetch_word segs (at_ base 576) = Some W_7078c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 144 _ HCODE eq_refl). Qed.
  Lemma Fo580 : fetch_word segs (at_ base 580) = Some W_70790.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 145 _ HCODE eq_refl). Qed.
  Lemma Fo584 : fetch_word segs (at_ base 584) = Some W_70794.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 146 _ HCODE eq_refl). Qed.
  Lemma Fo588 : fetch_word segs (at_ base 588) = Some W_70798.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 147 _ HCODE eq_refl). Qed.
  Lemma Fo592 : fetch_word segs (at_ base 592) = Some W_7079c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 148 _ HCODE eq_refl). Qed.
  Lemma Fo596 : fetch_word segs (at_ base 596) = Some W_707a0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 149 _ HCODE eq_refl). Qed.
  Lemma Fo600 : fetch_word segs (at_ base 600) = Some W_707a4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 150 _ HCODE eq_refl). Qed.
  Lemma Fo604 : fetch_word segs (at_ base 604) = Some W_707a8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 151 _ HCODE eq_refl). Qed.
  Lemma Fo608 : fetch_word segs (at_ base 608) = Some W_707ac.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 152 _ HCODE eq_refl). Qed.
  Lemma Fo612 : fetch_word segs (at_ base 612) = Some W_707b0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 153 _ HCODE eq_refl). Qed.
  Lemma Fo616 : fetch_word segs (at_ base 616) = Some W_707b4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 154 _ HCODE eq_refl). Qed.
  Lemma Fo620 : fetch_word segs (at_ base 620) = Some W_707b8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 155 _ HCODE eq_refl). Qed.
  Lemma Fo624 : fetch_word segs (at_ base 624) = Some W_707bc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 156 _ HCODE eq_refl). Qed.
  Lemma Fo628 : fetch_word segs (at_ base 628) = Some W_707c0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 157 _ HCODE eq_refl). Qed.
  Lemma Fo632 : fetch_word segs (at_ base 632) = Some W_707c4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 158 _ HCODE eq_refl). Qed.
  Lemma Fo636 : fetch_word segs (at_ base 636) = Some W_707c8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 159 _ HCODE eq_refl). Qed.
  Lemma Fo640 : fetch_word segs (at_ base 640) = Some W_707cc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 160 _ HCODE eq_refl). Qed.
  Lemma Fo644 : fetch_word segs (at_ base 644) = Some W_707d0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 161 _ HCODE eq_refl). Qed.
  Lemma Fo648 : fetch_word segs (at_ base 648) = Some W_707d4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 162 _ HCODE eq_refl). Qed.
  Lemma Fo652 : fetch_word segs (at_ base 652) = Some W_707d8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 anncc_words 163 _ HCODE eq_refl). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable mem : word -> option byte.
  Variable rom : word -> option byte.
  Variables beg endw old new ra sp : word.
  Variable dco : byte.          (* [comment removed for export] *)
  Variable eb : byte.           (* [comment removed for export] *)
  Variable cpm : byte.          (* [comment removed for export] *)
  Variables midend midend2 : word.   (* [comment removed for export] *)
  Variable thr : Z.             (* [comment removed for export] *)

  #[local] Abbreviation LE8 z := (word_to_le_bytes 8 (Z_to_bv 64 z)).
  (* [comment removed for export] *)
  Definition Ab : Z := U beg.  Definition Ae : Z := U endw.  Definition Ao : Z := U old.  Definition An : Z := U new.
  Definition ga : Z := dn8 Ao.              (* [comment removed for export] *)
  Definition gc : Z := dn8 (Ao + 7).        (* [comment removed for export] *)
  Definition gb1 : Z := dn8 An.             (* [comment removed for export] *)
  Definition gb2 : Z := dn8 (An + 7).



  Definition sp2 : word := at_ sp (-2128).

  (* [comment removed for export] *)
  Hypothesis Rg_flags : rdn segs mem (Z_to_bv 64 g_flags) 8 = Some (LE8 p_flags).
  Hypothesis Rdco : rdn segs mem (Z_to_bv 64 (p_flags + 96)) 1 = Some [dco].
  Hypothesis Hdco : U dco <> 0%Z.
  Hypothesis Rg_verb : rdn segs mem (Z_to_bv 64 g_verb) 8 = Some (LE8 p_verb).
  Hypothesis Rverb : rdn segs mem (Z_to_bv 64 p_verb) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).
  (* [comment removed for export] *)
  Definition RebH : Prop := (Ae mod 8 <> 0)%Z ->
    rdn segs mem (Z_to_bv 64 g_shoff) 8 = Some (LE8 p_shoff) /\ rdn segs mem (Z_to_bv 64 p_shoff) 8 = Some (LE8 0x7fff8000)
    /\ rdn segs mem (Z_to_bv 64 (0x7fff8000 + Ae / 8)) 1 = Some [eb] /\ bv_signed eb <> 0%Z /\ (bv_signed eb <= Ae mod 8)%Z.
  Hypothesis Reb : RebH.
  (* [comment removed for export] *)
  Hypothesis Pg_shoff : rdn segs mem (Z_to_bv 64 (pt_g_shoff pt)) 8 = Some (LE8 (pt_p_shoff pt)).
  Hypothesis Pshoff : rdn segs mem (Z_to_bv 64 (pt_p_shoff pt)) 8 = Some (LE8 0x7fff8000).
  Hypothesis Pg_midbeg : rdn segs mem (Z_to_bv 64 (pt_g_midbeg pt)) 8 = Some (LE8 (pt_p_midbeg pt)).
  Hypothesis Pmidbeg : rdn segs mem (Z_to_bv 64 (pt_p_midbeg pt)) 8 = Some (LE8 0).
  Hypothesis Pg_midend : rdn segs mem (Z_to_bv 64 (pt_g_midend pt)) 8 = Some (LE8 (pt_p_midend pt)).
  Hypothesis Pmidend : rdn segs mem (Z_to_bv 64 (pt_p_midend pt)) 8 = Some (word_to_le_bytes 8 midend).
  Hypothesis Pg_hiend : rdn segs mem (Z_to_bv 64 (pt_g_hiend pt)) 8 = Some (LE8 (pt_p_hiend pt)).
  Hypothesis Phiend : rdn segs mem (Z_to_bv 64 (pt_p_hiend pt)) 8 = Some (LE8 0x7fffffffffff).
  Hypothesis Pg_rms : rdn segs mem (Z_to_bv 64 (pt_g_rms pt)) 8 = Some (LE8 (pt_p_rms pt)).
  Hypothesis Prms : rdn segs mem (Z_to_bv 64 (pt_p_rms pt)) 8 = Some (word_to_le_bytes 8 (pt_mset pt)).
  Hypothesis Pmset : U (pt_mset pt) <> 0%Z.
  Hypothesis Pmset_ok : ret_ok (pt_mset pt).
  Definition PcpmH : Prop := (An < Ao)%Z -> rdn segs mem (Z_to_bv 64 (pt_c_cpm pt)) 1 = Some [cpm] /\ U cpm <> 0%Z.
  Hypothesis Pcpm : PcpmH.
  Definition PcflH : Prop := (Ao < An)%Z -> (ga < gb1)%Z ->
    rdn segs mem (Z_to_bv 64 (pt_g_cfl pt)) 8 = Some (LE8 (pt_p_cfl pt))
    /\ rdn segs mem (Z_to_bv 64 (pt_p_cfl pt + 120)) 8 = Some (LE8 thr)
    /\ ((gb1 - ga) / 8 < thr)%Z /\ (0 <= thr < 18446744073709551616)%Z.
  Hypothesis Pcfl : PcflH.
  (* [comment removed for export] *)
  Hypothesis Mg_shoff : rdn segs mem (Z_to_bv 64 (mt_g_shoff mt)) 8 = Some (LE8 (mt_p_shoff mt)).
  Hypothesis Mshoff : rdn segs mem (Z_to_bv 64 (mt_p_shoff mt)) 8 = Some (LE8 0x7fff8000).
  Hypothesis Mg_midbeg : rdn segs mem (Z_to_bv 64 (mt_g_midbeg mt)) 8 = Some (LE8 (mt_p_midbeg mt)).
  Hypothesis Mmidbeg : rdn segs mem (Z_to_bv 64 (mt_p_midbeg mt)) 8 = Some (LE8 0).
  Hypothesis Mg_midend : rdn segs mem (Z_to_bv 64 (mt_g_midend mt)) 8 = Some (LE8 (mt_p_midend mt)).
  Hypothesis Mmidend : rdn segs mem (Z_to_bv 64 (mt_p_midend mt)) 8 = Some (word_to_le_bytes 8 midend2).
  Hypothesis Mg_hiend : rdn segs mem (Z_to_bv 64 (mt_g_hiend mt)) 8 = Some (LE8 (mt_p_hiend mt)).
  Hypothesis Mhiend : rdn segs mem (Z_to_bv 64 (mt_p_hiend mt)) 8 = Some (LE8 0x7fffffffffff).
  (* [comment removed for export] *)
  Definition ann_cells : list Z :=
    ([g_flags; p_flags; p_flags + 96; g_verb; p_verb; g_shoff; p_shoff] ++ poison_cells pt
     ++ [pt_c_cpm pt; pt_g_cfl pt; pt_p_cfl pt; pt_p_cfl pt + 120] ++ m2s_cells mt)%Z.
  Hypothesis Hcells : Forall (fun c => 0 <= c /\ c + 8 <= U sp - 2192 /\ c + 8 <= 0x7fff8000)%Z ann_cells.
  (* [comment removed for export] *)
  Hypothesis Hbeg8 : (Ab mod 8 = 0)%Z.
  Hypothesis HO1 : (Ab <= Ao)%Z.  Hypothesis HO2 : (Ao <= Ae)%Z.
  Hypothesis HN1 : (Ab <= An)%Z.  Hypothesis HN2 : (An <= Ae)%Z.
  Hypothesis Hn40 : (Ae - Ab <= 1099511627776)%Z.      (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition rngH : Prop := (0x10007fff8000 <= Ab /\ Ae < 0x800000000000)%Z \/ (Ae <= 0x7fff7fff)%Z.
  Hypothesis Hrng : rngH.
  (* [comment removed for export] *)
  Hypothesis Hsp : (0x10007fff8000 + 2192 <= U sp)%Z.
  Hypothesis Hstk : store_ok segs mem (at_ sp (-2192)) 2192 = true.
  (* [comment removed for export] *)
  Hypothesis Hshw : forall a : word, (0x7fff8000 + Ab / 8 <= U a < 0x7fff8000 + (Ae + 7) / 8)%Z -> store_ok segs mem a 1 = true.
  Hypothesis Hret : ret_ok ra.

  #[local] Abbreviation CL := (fun r => In r anncc_clob).
  #[local] Abbreviation CLX := (fun r => In r anncc_clobx).

  Lemma cell_bound : forall c, In c ann_cells -> (0 <= c /\ c + 8 <= U sp - 2192 /\ c + 8 <= 0x7fff8000)%Z.
  Proof using Hcells. intros c Hc. exact (proj1 (Forall_forall _ _) Hcells c Hc). Qed.
  Ltac cellb c := pose proof (cell_bound c ltac:((lazymatch goal with |- ?G => let G' := eval unfold ann_cells, poison_cells, m2s_cells in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In app] in G in change_no_check G' end); am_tauto)).

  (* [comment removed for export] *)
  Lemma gran_facts :
    (ga <= Ao < ga + 8)%Z /\ (Ao <= gc < Ao + 8)%Z /\ (gb1 <= An < gb1 + 8)%Z /\ (An <= gb2 < An + 8)%Z
    /\ (Ab <= ga)%Z /\ (gc <= dn8 (Ae + 7) <= Ae + 7)%Z /\ (Ab <= gb1)%Z /\ (gb2 <= dn8 (Ae + 7))%Z.
  Proof using HN2 HN1 HO2 HO1 Hbeg8 base.
    (lazymatch goal with |- ?G => let G' := eval unfold ga, gc, gb1, gb2 in G in change_no_check G' end).
    pose proof (dn8_le Ao). pose proof (dn8_le (Ao + 7)). pose proof (dn8_le An). pose proof (dn8_le (An + 7)). pose proof (dn8_le (Ae + 7)).
    pose proof (dn8_mono Ab Ao HO1) as M1. rewrite (dn8_id Ab Hbeg8) in M1.
    pose proof (dn8_mono Ab An HN1) as M2. rewrite (dn8_id Ab Hbeg8) in M2.
    pose proof (dn8_mono (Ao + 7) (Ae + 7) ltac:(lia)). pose proof (dn8_mono (An + 7) (Ae + 7) ltac:(lia)).
    repeat split; lia.
  Qed.

  Section WithRegs.
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = beg.
  Hypothesis H11 : getr regs 11 = endw.
  Hypothesis H12 : getr regs 12 = old.
  Hypothesis H13 : getr regs 13 = new.

  (* [comment removed for export] *)
  Definition M1 : word -> option byte :=
    ps_frame mem sp ra (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21).

  Lemma rdM1 : forall c n bs, (0 <= c)%Z -> (c + Z.of_nat n <= U sp - 56)%Z ->
    rdn segs mem (Z_to_bv 64 c) n = Some bs -> rdn segs M1 (Z_to_bv 64 c) n = Some bs.
  Proof using Hsp beg Hbase base.
    intros c n bs Hc0 Hc Hr. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold M1, ps_frame in G in change_no_check G' end).
    rewrite !rdn_wbytes_out; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); unorm; try lia.
    exact Hr.
  Qed.
  Lemma M1_ok : forall (a : word) n, store_ok segs mem a n = true -> store_ok segs M1 a n = true.
  Proof using. intros a n H. (lazymatch goal with |- ?G => let G' := eval unfold M1, ps_frame in G in change_no_check G' end). repeat (eapply store_ok_mono; [apply wbytes_grows|]). exact H. Qed.
  Lemma M1_grows : mem_grows mem M1.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold M1, ps_frame in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Lemma M1_out : forall a : word, (U a < U sp - 56 \/ U sp <= U a)%Z -> M1 a = mem a.
  Proof using Hsp beg base.
    intros a Ha. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold M1, ps_frame in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; try reflexivity; (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia.
  Qed.

  (* [comment removed for export] *)
  Ltac fsd F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | repeat (eapply store_ok_mono; [apply wbytes_grows|]);
          eapply (store_ok_sub segs mem (at_ sp (-2192)) _ 2192);
          [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia] ]
      | step_simpl]; vn.
  (* [comment removed for export] *)
  Ltac cld F D vv Hr :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?v_addi_0;
          first [ apply rdM1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Hr]
                | (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; apply rdM1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Hr] ]
        | apply bytes_le_to_Z_8]
      | step_simpl]; vn.
  (* [comment removed for export] *)
  Ltac gl G Hr :=
    eapply msteps_trans; [ eapply G; apply rdM1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Hr] | ]; zlit_at.
  Ltac cells_split :=
    let HC := fresh "HC" in
    pose proof Hcells as HC; unfold ann_cells, poison_cells, m2s_cells in HC; cbn [app] in HC;
    repeat match type of HC with Forall _ (_ :: _) => apply Forall_cons_iff in HC; destruct HC as [? HC] end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma blkA :
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r (at_ base 248) M1 rom)
      /\ getr r 1 = ra /\ getr r 2 = sp2 /\ getr r 8 = sp /\ getr r 9 = beg /\ getr r 18 = new
      /\ getr r 19 = old /\ getr r 20 = endw
      /\ regs_agree CLX regs r.
  Proof using H13 H12 H11 H10 H2 H1 Hstk Hsp HO1 Hcells Rverb Rg_verb Hdco Rdco Rg_flags dco Hbase G72 G44 HCODE p_shoff g_shoff p_verb g_verb p_flags g_flags mt pt.
    pose proof (u64_range sp) as Hspr. cells_split. pose proof (u8_range dco) as Hdr.
    wd_eexists. split.
    - an Fo0 D_7054c.                                    (* [comment removed for export] *)
      fsd Fo4 D_70550 (at_ sp (-8)).                     (* [comment removed for export] *)
      fsd Fo8 D_70554 (at_ sp (-16)).                    (* [comment removed for export] *)
      fsd Fo12 D_70558 (at_ sp (-24)).                   (* [comment removed for export] *)
      fsd Fo16 D_7055c (at_ sp (-32)).                   (* [comment removed for export] *)
      fsd Fo20 D_70560 (at_ sp (-40)).                   (* [comment removed for export] *)
      fsd Fo24 D_70564 (at_ sp (-48)).                   (* [comment removed for export] *)
      fsd Fo28 D_70568 (at_ sp (-56)).                   (* [comment removed for export] *)
      change (wbytes _ _ _) with M1.
      an Fo32 D_7056c.                                   (* [comment removed for export] *)
      an Fo36 D_70570.                                   (* [comment removed for export] *)
      an Fo40 D_70574.                                   (* [comment removed for export] *)
      gl G44 Rg_flags.                                   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lbu with (b := dco);
          [exact Fo52 | reflexivity | exact D_70580
          | gres; rwH; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; apply rdM1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rdco] ]
        | step_simpl]; vn.                                (* [comment removed for export] *)
      ab_ft Fo56 D_70584 ltac:(condz).                 (* [comment removed for export] *)
      an Fo60 D_70588.                                   (* [comment removed for export] *)
      an Fo64 D_7058c.                                   (* [comment removed for export] *)
      an Fo68 D_70590.                                   (* [comment removed for export] *)
      gl G72 Rg_verb.                                    (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
          [exact Fo80 | reflexivity | exact D_7059c
          | gres; rwH; imm_norm; rewrite ?v_addi_0; apply rdM1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rverb]
          | apply bytes4_small; lia ]
        | step_simpl]; vn.                                (* [comment removed for export] *)
      try rewrite (v_lw_small 0) by lia.
      an Fo84 D_705a0.                                   (* [comment removed for export] *)
      ab_ft Fo88 D_705a4 ltac:(condz).                 (* [comment removed for export] *)
      ab_tk Fo92 D_705a8 ltac:(unfold Ab, Ao in *; condz).   (* [comment removed for export] *)
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold anncc_clobx in G in change_no_check G' end). ra_solve.
  Qed.

  (* [comment removed for export] *)
  Definition ann_slots : list (Z * word) :=
    [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19); (-48, getr regs 20); (-56, getr regs 21)]%Z.
  Lemma slots_M1 : forall (k : Z) (v : word), In (k, v) ann_slots -> rdn segs M1 (at_ sp k) 8 = Some (word_to_le_bytes 8 v).
  Proof using Hsp beg base.
    intros k v Hin. pose proof (u64_range sp). unfold ann_slots in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (lazymatch goal with |- ?G => let G' := eval unfold M1, ps_frame in G in change_no_check G' end); rd8_chain|]). destruct Hin.
  Qed.
  Lemma slots_keep : forall (m : word -> option byte) (k : Z) (v : word),
    (forall a : word, (U sp - 56 <= U a < U sp)%Z -> m a = M1 a) ->
    In (k, v) ann_slots -> rdn segs m (at_ sp k) 8 = Some (word_to_le_bytes 8 v).
  Proof using Hsp beg Hbase base.
    intros m k v HM Hin. pose proof (u64_range sp).
    assert (Hk : (-56 <= k /\ k + 8 <= 0)%Z).
    { unfold ann_slots in Hin. cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin. }
    rewrite <- (slots_M1 k v Hin). apply rdn_ext; [rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
    intros x Hx. rewrite at_u in Hx by lia. apply HM. cbn in Hx. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac fld F D vv SL :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; apply SL; clear; (lazymatch goal with |- ?G => let G' := eval cbn [ann_slots In] in G in change_no_check G' end); am_tauto
        | apply bytes_le_to_Z_8]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma blkZ : forall (m : word -> option byte) r0,
    (forall k v, In (k, v) ann_slots -> rdn segs m (at_ sp k) 8 = Some (word_to_le_bytes 8 v)) ->
    getr r0 2 = sp2 ->
    exists r,
      msteps segs (mkst r0 (at_ base 616) m rom) (mkst r ra m rom)
      /\ getr r 1 = ra /\ getr r 2 = sp /\ getr r 8 = getr regs 8 /\ getr r 9 = getr regs 9 /\ getr r 18 = getr regs 18
      /\ getr r 19 = getr regs 19 /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21
      /\ regs_agree (fun x => In x [1; 2; 8; 9; 18; 19; 20; 21]) r0 r.
  Proof using Hret HCODE.
    intros m r0 SL R2. pose proof (u64_range sp) as Hspr.
    wd_eexists. split.
    - unfold sp2 in R2.
      an Fo616 D_707b4.                                  (* [comment removed for export] *)
      fld Fo620 D_707b8 ra SL.                           (* [comment removed for export] *)
      fld Fo624 D_707bc (getr regs 8) SL.                (* [comment removed for export] *)
      fld Fo628 D_707c0 (getr regs 9) SL.                (* [comment removed for export] *)
      fld Fo632 D_707c4 (getr regs 18) SL.               (* [comment removed for export] *)
      fld Fo636 D_707c8 (getr regs 19) SL.               (* [comment removed for export] *)
      fld Fo640 D_707cc (getr regs 20) SL.               (* [comment removed for export] *)
      fld Fo644 D_707d0 (getr regs 21) SL.               (* [comment removed for export] *)
      an Fo648 D_707d4.                                  (* [comment removed for export] *)
      aret Fo652 D_707d8 ra.                             (* [comment removed for export] *)
      try rewrite at_0. wd_refl.
    - post. all: try (rewrite at_0; reflexivity). all: try ra_solve. all: match goal with |- ?G => fail 100 G end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma blkB_eq : forall r0,
    Ao = An ->
    getr r0 1 = ra -> getr r0 2 = sp2 -> getr r0 8 = sp -> getr r0 9 = beg -> getr r0 18 = new ->
    getr r0 19 = old -> getr r0 20 = endw -> regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 248) M1 rom) (mkst r (at_ base 616) M1 rom)
      /\ getr r 2 = sp2 /\ regs_agree CLX regs r.
  Proof using Hn40 HN2 HN1 HO2 Hbase HCODE.
    intros r0 EQ R1 R2 R8 R9 R18 R19 R20 AG0.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range beg). pose proof (u64_range endw). pose proof (u64_range old). pose proof (u64_range new).
    unfold Ab, Ae, Ao, An in *.
    assert (EQW : old = new) by (apply bv_eq; exact EQ).
    wd_eexists. split.
    - unfold sp2 in R2.
      ab_ft Fo248 D_70644 ltac:(condz).                (* [comment removed for export] *)
      ab_ft Fo252 D_70648 ltac:(condz).                (* [comment removed for export] *)
      ab_ft Fo256 D_7064c ltac:(condz).                (* [comment removed for export] *)
      av Fo260 D_70650 (Z_to_bv 64 (U endw - U beg)) ltac:(apply bv_eq; rewrite v_sub_small by lia; unorm; reflexivity).  (* [comment removed for export] *)
      an Fo264 D_70654.                                  (* [comment removed for export] *)
      av Fo268 D_70658 (Z_to_bv 64 1099511627776) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      an Fo272 D_7065c.                                  (* [comment removed for export] *)
      ab_ft Fo276 D_70660 ltac:(condz).                (* [comment removed for export] *)
      ab_tk Fo280 D_70664 ltac:(rewrite EQW; condz).   (* [comment removed for export] *)
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold anncc_clobx in G in change_no_check G' end). ra_solve.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma blkB_ne : forall r0,
    Ao <> An ->
    getr r0 1 = ra -> getr r0 2 = sp2 -> getr r0 8 = sp -> getr r0 9 = beg -> getr r0 18 = new ->
    getr r0 19 = old -> getr r0 20 = endw -> regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 248) M1 rom) (mkst r (at_ base 292) M1 rom)
      /\ getr r 1 = ra /\ getr r 2 = sp2 /\ getr r 8 = sp /\ getr r 9 = beg /\ getr r 18 = new
      /\ getr r 19 = old /\ getr r 20 = endw
      /\ regs_agree CLX regs r.
  Proof using Hsp Hrng Hn40 HN2 HN1 HO2 HO1 Hcells Reb eb Hbase G404 HCODE p_shoff g_shoff p_verb g_verb p_flags g_flags mt pt.
    intros r0 NE R1 R2 R8 R9 R18 R19 R20 AG0.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range beg). pose proof (u64_range endw). pose proof (u64_range old). pose proof (u64_range new).
    cells_split. pose proof (dn8_le (U endw)) as DN. pose proof (dn8_nonneg (U endw) ltac:(lia)) as DN0.
    pose proof Reb as RB. unfold RebH in RB.
    unfold Ab, Ae, Ao, An in *.
    assert (NEW : old <> new) by (intros E; apply NE; rewrite E; reflexivity).
    (* [comment removed for export] *)
    Ltac pre R2 NEW :=
      unfold sp2 in R2;
      ab_ft Fo248 D_70644 ltac:(condz);                (* [comment removed for export] *)
      ab_ft Fo252 D_70648 ltac:(condz);                (* [comment removed for export] *)
      ab_ft Fo256 D_7064c ltac:(condz);                (* [comment removed for export] *)
      av Fo260 D_70650 (Z_to_bv 64 (U endw - U beg)) ltac:(apply bv_eq; rewrite v_sub_small by lia; unorm; reflexivity);  (* [comment removed for export] *)
      an Fo264 D_70654;                                  (* [comment removed for export] *)
      av Fo268 D_70658 (Z_to_bv 64 1099511627776) ltac:(apply bv_eq; vm_compute; reflexivity);   (* [comment removed for export] *)
      an Fo272 D_7065c;                                  (* [comment removed for export] *)
      ab_ft Fo276 D_70660 ltac:(condz);                (* [comment removed for export] *)
      ab_ft Fo280 D_70664 ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq in G in change_no_check G' end); apply bv_eqb_neq; exact NEW);   (* [comment removed for export] *)
      av Fo284 D_70668 (Z_to_bv 64 (U endw mod 8)) ltac:(apply ann_andi_7).   (* [comment removed for export] *)
    destruct (Z.eq_dec (U endw mod 8) 0) as [E0 | NE0].
    { (* [comment removed for export] *)
      wd_eexists. split.
      - pre R2 NEW.
        ab_ft Fo288 D_7066c ltac:(condz).              (* [comment removed for export] *)
        wd_refl.
      - post. (lazymatch goal with |- ?G => let G' := eval unfold anncc_clobx in G in change_no_check G' end). ra_solve. }
    (* [comment removed for export] *)
    destruct (RB NE0) as (Rg & Rs & Re & Enz & Ele).
    pose proof (u_v_lb_signed_nz eb Enz) as Unz.
    pose proof (Z.mod_pos_bound (U endw) 8 ltac:(lia)) as M8.
    assert (E47 : (U endw < 0x800000000000)%Z) by (pose proof Hrng as RG; unfold rngH, Ab, Ae in RG; destruct RG; lia).
    assert (D8 : (0 <= U endw / 8 < 17592186044416)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    (* [comment removed for export] *)
    assert (MX : exists mx : word, (U mx = Z.max (U old) (U new))%Z /\ (mx = old \/ mx = new)).
    { destruct (Z_lt_le_dec (U new) (U old)); [exists old | exists new]; split; try lia; am_tauto. }
    destruct MX as (mx & UMX & MXC).
    Ltac fixpre R2 NEW :=
      pre R2 NEW;
      ab_tk Fo288 D_7066c ltac:(condz);                (* [comment removed for export] *)
      av Fo384 D_706cc (Z_to_bv 64 (dn8 (U endw))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold dn8 in G in change_no_check G' end); apply ann_andi_m8);   (* [comment removed for export] *)
      an Fo388 D_706d0.                                  (* [comment removed for export] *)
    destruct (Z_le_gt_dec (Z.max (U old) (U new)) (dn8 (U endw))) as [LE | GT].
    { (* [comment removed for export] *)
      destruct MXC as [-> | ->].
      + wd_eexists. split.
        * fixpre R2 NEW.
          ab_tk Fo392 D_706d4 ltac:(condz).            (* [comment removed for export] *)
          ab_tk Fo400 D_706dc ltac:(condz).            (* [comment removed for export] *)
          wd_refl.
        * post. (lazymatch goal with |- ?G => let G' := eval unfold anncc_clobx in G in change_no_check G' end). ra_solve.
      + wd_eexists. split.
        * fixpre R2 NEW.
          ab_ft Fo392 D_706d4 ltac:(condz).            (* [comment removed for export] *)
          an Fo396 D_706d8.                              (* [comment removed for export] *)
          ab_tk Fo400 D_706dc ltac:(condz).            (* [comment removed for export] *)
          wd_refl.
        * post. (lazymatch goal with |- ?G => let G' := eval unfold anncc_clobx in G in change_no_check G' end). ra_solve. }
    (* [comment removed for export] *)
    Ltac shread Rg Rs Re :=
      gl G404 Rg;                                        (* [comment removed for export] *)
      cld Fo412 D_706e8 (Z_to_bv 64 0x7fff8000) Rs;      (* [comment removed for export] *)
      av Fo416 D_706ec (Z_to_bv 64 (U endw / 8)) ltac:(apply v_srli_3);   (* [comment removed for export] *)
      av Fo420 D_706f0 (Z_to_bv 64 (0x7fff8000 + U endw / 8)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia);  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lb with (b := eb);
          [exact Fo424 | reflexivity | exact D_706f4
          | gres; rwH; imm_norm; rewrite ?v_addi_0; apply rdM1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Re] ]
        | step_simpl]; vn;                                (* [comment removed for export] *)
      ab_ft Fo428 D_706f8 ltac:(condz);                (* [comment removed for export] *)
      ab_tk Fo432 D_706fc ltac:(rwH; rewrite c_lts_small_lb by lia; apply Z.ltb_ge; lia).   (* [comment removed for export] *)
    destruct MXC as [-> | ->].
    + wd_eexists. split.
      * fixpre R2 NEW.
        ab_tk Fo392 D_706d4 ltac:(condz).              (* [comment removed for export] *)
        ab_ft Fo400 D_706dc ltac:(condz).              (* [comment removed for export] *)
        shread Rg Rs Re. wd_refl.
      * post. (lazymatch goal with |- ?G => let G' := eval unfold anncc_clobx in G in change_no_check G' end). ra_solve.
    + wd_eexists. split.
      * fixpre R2 NEW.
        ab_ft Fo392 D_706d4 ltac:(condz).              (* [comment removed for export] *)
        an Fo396 D_706d8.                                (* [comment removed for export] *)
        ab_ft Fo400 D_706dc ltac:(condz).              (* [comment removed for export] *)
        shread Rg Rs Re. wd_refl.
      * post. (lazymatch goal with |- ?G => let G' := eval unfold anncc_clobx in G in change_no_check G' end). ra_solve.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac dpre Hbeg8 :=
    an Fo292 D_70670;                                    (* [comment removed for export] *)
    an Fo296 D_70674;                                    (* [comment removed for export] *)
    an Fo300 D_70678;                                    (* [comment removed for export] *)
    av Fo304 D_7067c (Z_to_bv 64 0) ltac:(rewrite ann_andi_7; f_equal; exact Hbeg8);   (* [comment removed for export] *)
    ab_ft Fo308 D_70680 ltac:(condz);                  (* [comment removed for export] *)
    an Fo312 D_70684;                                    (* [comment removed for export] *)
    an Fo316 D_70688.                                    (* [comment removed for export] *)

  Lemma blkD_G1 : forall r0,
    (Ao < An)%Z -> (ga < gb1)%Z ->
    getr r0 1 = ra -> getr r0 2 = sp2 -> getr r0 8 = sp -> getr r0 9 = beg -> getr r0 18 = new ->
    getr r0 19 = old -> getr r0 20 = endw -> regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 292) M1 rom) (mkst r (pt_base pt) M1 rom)
      /\ getr r 1 = at_ base 584 /\ getr r 2 = sp2 /\ getr r 8 = sp /\ getr r 9 = Z_to_bv 64 gb1 /\ getr r 18 = Z_to_bv 64 gb2
      /\ getr r 19 = Z_to_bv 64 0 /\ getr r 20 = old /\ getr r 21 = new
      /\ getr r 10 = Z_to_bv 64 ga /\ getr r 11 = Z_to_bv 64 (gb1 - ga) /\ getr r 12 = Z_to_bv 64 0
      /\ regs_agree CLX regs r.
  Proof using Hrng Hn40 HN2 HN1 HO2 HO1 Hbeg8 Hbase PTB HCODE.
    intros r0 LT CALL R1 R2 R8 R9 R18 R19 R20 AG0.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range beg). pose proof (u64_range endw). pose proof (u64_range old). pose proof (u64_range new).
    pose proof gran_facts as GF. pose proof Hbeg8 as B8.
    assert (E47 : (Ae < 0x800000000000)%Z) by (pose proof Hrng as RG; unfold rngH in RG; destruct RG; lia).
    unfold ga, gc, gb1, gb2, dn8, Ab, Ae, Ao, An in *. rewrite PTB.
    wd_eexists. split.
    - unfold sp2 in R2. dpre B8.
      ab_tk Fo320 D_7068c ltac:(condz).                (* [comment removed for export] *)
      av Fo528 D_7075c (Z_to_bv 64 (U old / 8 * 8)) ltac:(apply ann_andi_m8).   (* [comment removed for export] *)
      ab_ft Fo532 D_70760 ltac:(condz).                (* [comment removed for export] *)
      an Fo536 D_70764.                                  (* [comment removed for export] *)
      av Fo540 D_70768 (Z_to_bv 64 (U new / 8 * 8)) ltac:(apply ann_andi_m8).   (* [comment removed for export] *)
      an Fo544 D_7076c.                                  (* [comment removed for export] *)
      av Fo548 D_70770 (Z_to_bv 64 ((U new + 7) / 8 * 8)) ltac:(rewrite ann_andi_m8; rewrite at_u by lia; reflexivity).   (* [comment removed for export] *)
      ab_tk Fo552 D_70774 ltac:(condz).                (* [comment removed for export] *)
      av Fo348 D_706a8 (Z_to_bv 64 (U new / 8 * 8 - U old / 8 * 8)) ltac:(apply bv_eq; rewrite v_sub_small by (wd_ulia); unorm; reflexivity).   (* [comment removed for export] *)
      an Fo352 D_706ac.                                  (* [comment removed for export] *)
      an Fo356 D_706b0.                                  (* [comment removed for export] *)
      an Fo580 D_70790.                                  (* [comment removed for export] *)
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold anncc_clobx in G in change_no_check G' end). ra_solve.
  Qed.

  Lemma blkD_G0 : forall r0,
    (Ao < An)%Z -> (gb1 <= ga)%Z ->
    getr r0 1 = ra -> getr r0 2 = sp2 -> getr r0 8 = sp -> getr r0 9 = beg -> getr r0 18 = new ->
    getr r0 19 = old -> getr r0 20 = endw -> regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 292) M1 rom) (mkst r (at_ base 584) M1 rom)
      /\ getr r 1 = ra /\ getr r 2 = sp2 /\ getr r 8 = sp /\ getr r 9 = Z_to_bv 64 gb1 /\ getr r 18 = Z_to_bv 64 gb2
      /\ getr r 19 = Z_to_bv 64 0 /\ getr r 20 = old /\ getr r 21 = new
      /\ regs_agree CLX regs r.
  Proof using Hrng HN2 HN1 HO2 HO1 Hbeg8 Hbase HCODE.
    intros r0 LT NOCALL R1 R2 R8 R9 R18 R19 R20 AG0.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range beg). pose proof (u64_range endw). pose proof (u64_range old). pose proof (u64_range new).
    pose proof gran_facts as GF. pose proof Hbeg8 as B8.
    assert (E47 : (Ae < 0x800000000000)%Z) by (pose proof Hrng as RG; unfold rngH in RG; destruct RG; lia).
    unfold ga, gc, gb1, gb2, dn8, Ab, Ae, Ao, An in *.
    wd_eexists. split.
    - unfold sp2 in R2. dpre B8.
      ab_tk Fo320 D_7068c ltac:(condz).                (* [comment removed for export] *)
      av Fo528 D_7075c (Z_to_bv 64 (U old / 8 * 8)) ltac:(apply ann_andi_m8).   (* [comment removed for export] *)
      ab_ft Fo532 D_70760 ltac:(condz).                (* [comment removed for export] *)
      an Fo536 D_70764.                                  (* [comment removed for export] *)
      av Fo540 D_70768 (Z_to_bv 64 (U new / 8 * 8)) ltac:(apply ann_andi_m8).   (* [comment removed for export] *)
      an Fo544 D_7076c.                                  (* [comment removed for export] *)
      av Fo548 D_70770 (Z_to_bv 64 ((U new + 7) / 8 * 8)) ltac:(rewrite ann_andi_m8; rewrite at_u by lia; reflexivity).   (* [comment removed for export] *)
      ab_ft Fo552 D_70774 ltac:(condz).                (* [comment removed for export] *)
      an Fo556 D_70778.                                  (* [comment removed for export] *)
      av Fo560 D_7077c (Z_to_bv 64 ((U new + 7) / 8 * 8)) ltac:(rewrite ann_andi_m8; rewrite at_u by lia; reflexivity).   (* [comment removed for export] *)
      ab_tk Fo564 D_70780 ltac:(condz).                (* [comment removed for export] *)
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold anncc_clobx in G in change_no_check G' end). ra_solve.
  Qed.

  Lemma blkD_S1 : forall r0,
    (An < Ao)%Z -> (gb2 < gc)%Z ->
    getr r0 1 = ra -> getr r0 2 = sp2 -> getr r0 8 = sp -> getr r0 9 = beg -> getr r0 18 = new ->
    getr r0 19 = old -> getr r0 20 = endw -> regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 292) M1 rom) (mkst r (pt_base pt) M1 rom)
      /\ getr r 1 = at_ base 584 /\ getr r 2 = sp2 /\ getr r 8 = sp /\ getr r 9 = Z_to_bv 64 gb1 /\ getr r 18 = Z_to_bv 64 gb2
      /\ getr r 19 = Z_to_bv 64 0 /\ getr r 20 = old /\ getr r 21 = new
      /\ getr r 10 = Z_to_bv 64 gb2 /\ getr r 11 = Z_to_bv 64 (gc - gb2) /\ getr r 12 = Z_to_bv 64 252
      /\ regs_agree CLX regs r.
  Proof using Hrng Hn40 HN2 HN1 HO2 HO1 Hbeg8 Hbase PTB HCODE.
    intros r0 LT CALL R1 R2 R8 R9 R18 R19 R20 AG0.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range beg). pose proof (u64_range endw). pose proof (u64_range old). pose proof (u64_range new).
    pose proof gran_facts as GF. pose proof Hbeg8 as B8.
    assert (E47 : (Ae < 0x800000000000)%Z) by (pose proof Hrng as RG; unfold rngH in RG; destruct RG; lia).
    unfold ga, gc, gb1, gb2, dn8, Ab, Ae, Ao, An in *. rewrite PTB.
    wd_eexists. split.
    - unfold sp2 in R2. dpre B8.
      ab_ft Fo320 D_7068c ltac:(condz).                (* [comment removed for export] *)
      av Fo324 D_70690 (Z_to_bv 64 (U new / 8 * 8)) ltac:(apply ann_andi_m8).   (* [comment removed for export] *)
      ab_ft Fo328 D_70694 ltac:(condz).                (* [comment removed for export] *)
      av Fo332 D_70698 (Z_to_bv 64 (U new / 8 * 8)) ltac:(apply ann_andi_m8).   (* [comment removed for export] *)
      an Fo336 D_7069c.                                  (* [comment removed for export] *)
      av Fo340 D_706a0 (Z_to_bv 64 ((U new + 7) / 8 * 8)) ltac:(rewrite ann_andi_m8; rewrite at_u by lia; reflexivity).   (* [comment removed for export] *)
      ab_tk Fo344 D_706a4 ltac:(condz).                (* [comment removed for export] *)
      an Fo556 D_70778.                                  (* [comment removed for export] *)
      av Fo560 D_7077c (Z_to_bv 64 ((U old + 7) / 8 * 8)) ltac:(rewrite ann_andi_m8; rewrite at_u by lia; reflexivity).   (* [comment removed for export] *)
      ab_ft Fo564 D_70780 ltac:(condz).                (* [comment removed for export] *)
      av Fo568 D_70784 (Z_to_bv 64 ((U old + 7) / 8 * 8 - (U new + 7) / 8 * 8)) ltac:(apply bv_eq; rewrite v_sub_small by (wd_ulia); unorm; reflexivity).   (* [comment removed for export] *)
      an Fo572 D_70788.                                  (* [comment removed for export] *)
      an Fo576 D_7078c.                                  (* [comment removed for export] *)
      an Fo580 D_70790.                                  (* [comment removed for export] *)
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold anncc_clobx in G in change_no_check G' end). ra_solve.
  Qed.

  Lemma blkD_S0 : forall r0,
    (An < Ao)%Z -> (gc <= gb2)%Z ->
    getr r0 1 = ra -> getr r0 2 = sp2 -> getr r0 8 = sp -> getr r0 9 = beg -> getr r0 18 = new ->
    getr r0 19 = old -> getr r0 20 = endw -> regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 292) M1 rom) (mkst r (at_ base 584) M1 rom)
      /\ getr r 1 = ra /\ getr r 2 = sp2 /\ getr r 8 = sp /\ getr r 9 = Z_to_bv 64 gb1 /\ getr r 18 = Z_to_bv 64 gb2
      /\ getr r 19 = Z_to_bv 64 0 /\ getr r 20 = old /\ getr r 21 = new
      /\ regs_agree CLX regs r.
  Proof using Hrng HN2 HN1 HO2 HO1 Hbeg8 Hbase HCODE.
    intros r0 LT NOCALL R1 R2 R8 R9 R18 R19 R20 AG0.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range beg). pose proof (u64_range endw). pose proof (u64_range old). pose proof (u64_range new).
    pose proof gran_facts as GF. pose proof Hbeg8 as B8.
    assert (E47 : (Ae < 0x800000000000)%Z) by (pose proof Hrng as RG; unfold rngH in RG; destruct RG; lia).
    unfold ga, gc, gb1, gb2, dn8, Ab, Ae, Ao, An in *.
    wd_eexists. split.
    - unfold sp2 in R2. dpre B8.
      ab_ft Fo320 D_7068c ltac:(condz).                (* [comment removed for export] *)
      av Fo324 D_70690 (Z_to_bv 64 (U new / 8 * 8)) ltac:(apply ann_andi_m8).   (* [comment removed for export] *)
      ab_ft Fo328 D_70694 ltac:(condz).                (* [comment removed for export] *)
      av Fo332 D_70698 (Z_to_bv 64 (U new / 8 * 8)) ltac:(apply ann_andi_m8).   (* [comment removed for export] *)
      an Fo336 D_7069c.                                  (* [comment removed for export] *)
      av Fo340 D_706a0 (Z_to_bv 64 ((U new + 7) / 8 * 8)) ltac:(rewrite ann_andi_m8; rewrite at_u by lia; reflexivity).   (* [comment removed for export] *)
      ab_tk Fo344 D_706a4 ltac:(condz).                (* [comment removed for export] *)
      an Fo556 D_70778.                                  (* [comment removed for export] *)
      av Fo560 D_7077c (Z_to_bv 64 ((U old + 7) / 8 * 8)) ltac:(rewrite ann_andi_m8; rewrite at_u by lia; reflexivity).   (* [comment removed for export] *)
      ab_tk Fo564 D_70780 ltac:(condz).                (* [comment removed for export] *)
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold anncc_clobx in G in change_no_check G' end). ra_solve.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma blkT0 : forall (m : word -> option byte) r0,
    (An mod 8 = 0)%Z ->
    getr r0 2 = sp2 -> getr r0 9 = Z_to_bv 64 gb1 -> getr r0 18 = Z_to_bv 64 gb2 -> regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 584) m rom) (mkst r (at_ base 616) m rom)
      /\ getr r 2 = sp2 /\ regs_agree CLX regs r.
  Proof using Hrng Hn40 HN2 endw beg Hbase HCODE.
    intros m r0 A0 R2 R9 R18 AG0.
    pose proof (u64_range new). pose proof (dn8_up7 (U new)) as UP. pose proof (dn8_nonneg (U new) ltac:(lia)).
    pose proof (dn8_le (U new)).
    assert (E47 : (Ae < 0x800000000000)%Z) by (pose proof Hrng as RG; unfold rngH in RG; destruct RG; lia).
    unfold ga, gc, gb1, gb2, dn8, Ab, Ae, Ao, An in *.
    assert (EQ : ((U new + 7) / 8 * 8 = U new / 8 * 8)%Z) by (destruct UP; lia). rewrite EQ in R18.
    wd_eexists. split.
    - ab_tk Fo584 D_70794 ltac:(condz).                (* [comment removed for export] *)
      wd_refl.
    - post. exact AG0.
  Qed.

  Lemma blkT1a : forall (m : word -> option byte) r0,
    (An mod 8 <> 0)%Z ->
    getr r0 2 = sp2 -> getr r0 8 = sp -> getr r0 9 = Z_to_bv 64 gb1 -> getr r0 18 = Z_to_bv 64 gb2 -> getr r0 21 = new ->
    regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 584) m rom) (mkst r (mt_base mt) m rom)
      /\ getr r 1 = at_ base 612 /\ getr r 2 = sp2 /\ getr r 8 = sp /\ getr r 10 = Z_to_bv 64 gb1
      /\ getr r 18 = Z_to_bv 64 (An mod 8) /\ regs_agree CLX regs r.
  Proof using Hrng Hn40 HN2 endw beg Hbase MTB HCODE.
    intros m r0 A0 R2 R8 R9 R18 R21 AG0.
    pose proof (u64_range new). pose proof (dn8_up7 (U new)) as UP. pose proof (dn8_nonneg (U new) ltac:(lia)).
    pose proof (dn8_le (U new)). pose proof (Z.mod_pos_bound (U new) 8 ltac:(lia)).
    assert (E47 : (Ae < 0x800000000000)%Z) by (pose proof Hrng as RG; unfold rngH in RG; destruct RG; lia).
    unfold ga, gc, gb1, gb2, dn8, Ab, Ae, Ao, An in *.
    assert (EQ : ((U new + 7) / 8 * 8 = U new / 8 * 8 + 8)%Z) by (destruct UP; lia). rewrite EQ in R18.
    rewrite MTB.
    wd_eexists. split.
    - ab_ft Fo584 D_70794 ltac:(condz).                (* [comment removed for export] *)
      av Fo588 D_70798 (Z_to_bv 64 8) ltac:(apply bv_eq; rewrite v_sub_small by (wd_ulia); wd_ulia).   (* [comment removed for export] *)
      an Fo592 D_7079c.                                  (* [comment removed for export] *)
      ab_ft Fo596 D_707a0 ltac:(condz).                (* [comment removed for export] *)
      av Fo600 D_707a4 (Z_to_bv 64 (U new mod 8)) ltac:(apply ann_andi_7).   (* [comment removed for export] *)
      an Fo604 D_707a8.                                  (* [comment removed for export] *)
      an Fo608 D_707ac.                                  (* [comment removed for export] *)
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold anncc_clobx in G in change_no_check G' end). ra_solve.
  Qed.

  (* [comment removed for export] *)
  Lemma blkT1b : forall (m : word -> option byte) r0 (a0 : word),
    getr r0 10 = a0 -> getr r0 18 = Z_to_bv 64 (An mod 8) ->
    store_ok segs m a0 1 = true ->
    msteps segs (mkst r0 (at_ base 612) m rom) (mkst r0 (at_ base 616) (wbytes m a0 [Z_to_bv 8 (An mod 8)]) rom).
  Proof using beg HCODE.
    intros m r0 a0 R10 R18 OK. pose proof (u64_range new). pose proof (Z.mod_pos_bound (U new) 8 ltac:(lia)).
    unfold An in *.
    chain_step; [reflexivity
      | eapply step_sb_at with (a := a0);
        [exact Fo612 | reflexivity | exact D_707b0
        | gres; rwH; imm_norm; rewrite ?v_addi_0; reflexivity
        | gres; rwH; reflexivity
        | unorm; reflexivity
        | exact OK ]
      | step_simpl]; vn.                                  (* [comment removed for export] *)
    wd_refl.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition PZ (m : word -> option byte) (lo hi v : Z) : word -> option byte :=
    wbytes (ps_frame m sp2 (at_ base 584) sp (Z_to_bv 64 gb1) (Z_to_bv 64 gb2) (Z_to_bv 64 0) old new)
           (Z_to_bv 64 (shad (Z_to_bv 64 lo))) (repeat (cbyte (Z_to_bv 64 v)) (Z.to_nat (shlen (Z_to_bv 64 (hi - lo))))).
  Definition ann_M2 : word -> option byte :=
    if (Ao <? An)%Z then (if (ga <? gb1)%Z then PZ M1 ga gb1 0 else M1)
    else (if (gb2 <? gc)%Z then PZ M1 gb2 gc 252 else M1).
  (* [comment removed for export] *)
  Definition SBADDR : word := Z_to_bv 64 (gb1 / 8 + 0x7fff8000).
  Definition ann_M3 : word -> option byte :=
    if (An mod 8 =? 0)%Z then ann_M2 else wbytes ann_M2 SBADDR [Z_to_bv 8 (An mod 8)].
  Definition ann_mem : word -> option byte := if (Ao =? An)%Z then M1 else ann_M3.

  Lemma WV : forall (m : word -> option byte) (x : word), store_ok segs m x 1 = true -> wview segs m x <> None.
  Proof using. intros m x Hx. cbn [store_ok] in Hx. destruct (wview segs m x); [discriminate | discriminate Hx]. Qed.

  (* [comment removed for export] *)
  Lemma nums :
    (0 <= Ab)%Z /\ (Ae < 0x800000000000)%Z /\ (0 <= ga)%Z /\ (0 <= gb1)%Z /\ (0 <= gc)%Z /\ (0 <= gb2)%Z
    /\ (Ab / 8 <= ga / 8)%Z /\ (Ab / 8 <= gb1 / 8)%Z /\ (Ab / 8 <= gb2 / 8)%Z
    /\ ((gb1 - ga) / 8 = gb1 / 8 - ga / 8)%Z /\ ((gc - gb2) / 8 = gc / 8 - gb2 / 8)%Z
    /\ (gb1 / 8 <= (Ae + 7) / 8)%Z /\ (gc / 8 <= (Ae + 7) / 8)%Z /\ ((Ae + 7) / 8 <= 17592186044416)%Z
    /\ (ga = ga / 8 * 8)%Z /\ (gb1 = gb1 / 8 * 8)%Z /\ (gb2 = gb2 / 8 * 8)%Z /\ (gc = gc / 8 * 8)%Z
    /\ ((An mod 8 <> 0)%Z -> (gb1 / 8 + 1 <= (Ae + 7) / 8)%Z).
  Proof using Hrng HN2 HN1 HO2 HO1 Hbeg8 Hbase base.
    pose proof (u64_range beg). pose proof (u64_range endw). pose proof gran_facts as GF.
    assert (E47 : (Ae < 0x800000000000)%Z) by (pose proof Hrng as RG; unfold rngH in RG; destruct RG; lia).
    unfold ga, gc, gb1, gb2, dn8, Ab, Ae, Ao, An in *.
    pose proof (Z.div_pos (U old) 8 ltac:(pose proof (u64_range old); lia) ltac:(lia)).
    pose proof (Z.div_pos (U new) 8 ltac:(pose proof (u64_range new); lia) ltac:(lia)).
    rewrite !Z.div_mul by lia. rewrite <- !Z.mul_sub_distr_r. rewrite !Z.div_mul by lia.
    assert (U beg / 8 <= U old / 8)%Z by (apply Z.div_le_mono; lia).
    assert (U beg / 8 <= U new / 8)%Z by (apply Z.div_le_mono; lia).
    assert (U new / 8 <= (U new + 7) / 8)%Z by (apply Z.div_le_mono; lia).
    assert ((U new + 7) / 8 <= (U endw + 7) / 8)%Z by (apply Z.div_le_mono; lia).
    assert ((U old + 7) / 8 <= (U endw + 7) / 8)%Z by (apply Z.div_le_mono; lia).
    assert ((U endw + 7) / 8 <= 17592186044416)%Z.
    { pose proof (Z.div_le_mono (U endw + 7) 140737488355334 8 ltac:(lia) ltac:(lia)) as DM.
      change (140737488355334 / 8)%Z with 17592186044416%Z in DM. exact DM. }
    repeat split; try lia.
    intros NZ. pose proof (dn8_le (U new)) as DL. unfold dn8 in DL. pose proof (Z.div_mod (U new) 8 ltac:(lia)).
    assert (U new / 8 * 8 + 8 <= U endw + 7)%Z by lia.
    pose proof (Z.div_le_mono (U new / 8 * 8 + 8) (U endw + 7) 8 ltac:(lia) ltac:(lia)) as DM.
    rewrite Z.div_add_l in DM by lia. change (8 / 8)%Z with 1%Z in DM. lia.
  Qed.

  Lemma psf_out : forall (m : word -> option byte) (a : word),
    (U a < U sp - 2192 \/ U sp - 2128 <= U a)%Z ->
    ps_frame m sp2 (at_ base 584) sp (Z_to_bv 64 gb1) (Z_to_bv 64 gb2) (Z_to_bv 64 0) old new a = m a.
  Proof using Hsp beg.
    intros m a Ha. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold ps_frame, sp2 in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; try reflexivity; (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite ?at_at, ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia.
  Qed.

  Lemma PZ_same : forall m lo hi v (a : word),
    (0 <= lo)%Z -> (lo <= hi)%Z -> (hi <= 0x800000000000)%Z ->
    (U a < U sp - 2192 \/ U sp - 2128 <= U a)%Z ->
    (U a < 0x7fff8000 + lo / 8 \/ 0x7fff8000 + lo / 8 + (hi - lo) / 8 <= U a)%Z ->
    PZ m lo hi v a = m a.
  Proof using Hsp beg Hbase.
    intros m lo hi v a Q0 Q1 Q2 Hf Hs. (lazymatch goal with |- ?G => let G' := eval unfold PZ, shad, shlen in G in change_no_check G' end).
    pose proof (Z.div_pos lo 8 Q0 ltac:(lia)). pose proof (Z.div_pos (hi - lo) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound lo 8 17592186044416 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound (hi - lo) 8 17592186044416 ltac:(lia) ltac:(lia)).
    rewrite wbytes_outside; [apply psf_out; exact Hf | |];
      rewrite repeat_length, Z2Nat.id by (wd_ulia); (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); wd_ulia.
  Qed.

  Lemma PZ_grows : forall m lo hi v, mem_grows m (PZ m lo hi v).
  Proof using.
    intros m lo hi v. (lazymatch goal with |- ?G => let G' := eval unfold PZ, ps_frame in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma M2_low : forall a : word, (U a < U sp - 2192)%Z -> (U a < 0x7fff8000)%Z -> ann_M2 a = mem a.
  Proof using Hsp Hrng HN2 HN1 HO2 HO1 Hbeg8 endw beg Hbase.
    intros a Q1 Q2. pose proof nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & _).
    pose proof gran_facts as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
    pose proof (Z.div_pos ga 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_pos gb2 8 ltac:(lia) ltac:(lia)).
    assert (M1a : M1 a = mem a) by (apply M1_out; lia).
    (lazymatch goal with |- ?G => let G' := eval unfold ann_M2 in G in change_no_check G' end). destruct (Z.ltb_spec Ao An) as [LT|GE]; [destruct (Z.ltb_spec ga gb1) as [C|C] | destruct (Z.ltb_spec gb2 gc) as [C|C]]; try exact M1a.
    - assert (P1 : (0 <= ga)%Z) by lia. assert (P2 : (ga <= gb1)%Z) by lia.
      assert (P3 : (gb1 <= 0x800000000000)%Z) by (clear - G3 HN2 N2; lia).
      assert (P4 : (U a < U sp - 2192 \/ U sp - 2128 <= U a)%Z) by (left; lia).
      assert (P5 : (U a < 0x7fff8000 + ga / 8 \/ 0x7fff8000 + ga / 8 + (gb1 - ga) / 8 <= U a)%Z) by (left; lia).
      rewrite (PZ_same M1 ga gb1 0 a P1 P2 P3 P4 P5). exact M1a.
    - assert (P1 : (0 <= gb2)%Z) by lia. assert (P2 : (gb2 <= gc)%Z) by lia.
      assert (P3 : (gc <= 0x800000000000)%Z) by (clear - G6 N14; unfold dn8 in *; lia).
      assert (P4 : (U a < U sp - 2192 \/ U sp - 2128 <= U a)%Z) by (left; lia).
      assert (P5 : (U a < 0x7fff8000 + gb2 / 8 \/ 0x7fff8000 + gb2 / 8 + (gc - gb2) / 8 <= U a)%Z) by (left; lia).
      rewrite (PZ_same M1 gb2 gc 252 a P1 P2 P3 P4 P5). exact M1a.
  Qed.
  Lemma M2_grows : mem_grows mem ann_M2.
  Proof using.
    (lazymatch goal with |- ?G => let G' := eval unfold ann_M2 in G in change_no_check G' end). destruct (Z.ltb_spec Ao An); [destruct (Z.ltb_spec ga gb1) | destruct (Z.ltb_spec gb2 gc)];
      first [exact M1_grows | eapply mem_grows_trans; [exact M1_grows | apply PZ_grows]].
  Qed.
  (* [comment removed for export] *)
  Lemma M2_slots : forall a : word, (U sp - 56 <= U a < U sp)%Z -> ann_M2 a = M1 a.
  Proof using Hsp Hrng HN2 HN1 HO2 HO1 Hbeg8 endw beg Hbase.
    intros a Ha. pose proof nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & _).
    pose proof gran_facts as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). pose proof Hsp.
    pose proof (Z.div_pos ga 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_pos gb2 8 ltac:(lia) ltac:(lia)).
    (lazymatch goal with |- ?G => let G' := eval unfold ann_M2 in G in change_no_check G' end). destruct (Z.ltb_spec Ao An) as [LT|GE]; [destruct (Z.ltb_spec ga gb1) as [C|C] | destruct (Z.ltb_spec gb2 gc) as [C|C]]; try reflexivity.
    - assert (P3 : (gb1 <= 0x800000000000)%Z) by (clear - G3 HN2 N2; lia).
      exact (PZ_same M1 ga gb1 0 a ltac:(lia) ltac:(lia) P3 ltac:(right; lia) ltac:(right; rewrite N10; lia)).
    - assert (P3 : (gc <= 0x800000000000)%Z) by (clear - G6 N14; unfold dn8 in *; lia).
      exact (PZ_same M1 gb2 gc 252 a ltac:(lia) ltac:(lia) P3 ltac:(right; lia) ltac:(right; rewrite N11; lia)).
  Qed.
  Lemma slots_of : forall (m : word -> option byte),
    (forall a : word, (U sp - 56 <= U a < U sp)%Z -> m a = M1 a) ->
    forall k v, In (k, v) ann_slots -> rdn segs m (at_ sp k) 8 = Some (word_to_le_bytes 8 v).
  Proof using Hsp beg Hbase base. intros m HM k v Hin. exact (slots_keep m k v HM Hin). Qed.

  (* [comment removed for export] *)
  Lemma m2sH_of_low : forall m : word -> option byte,
    (forall a : word, (U a < U sp - 2192)%Z -> (U a < 0x7fff8000)%Z -> m a = mem a) ->
    m2sH segs mt m (Z_to_bv 64 gb1) midend2.
  Proof using Hsp Hrng HN2 HN1 HO2 HO1 Hbeg8 Hcells Mhiend Mg_hiend Mmidend Mg_midend Mmidbeg Mg_midbeg Mshoff Mg_shoff old endw beg Hbase p_shoff g_shoff p_verb g_verb p_flags g_flags pt base.
    intros m LOW. cells_split. pose proof nums as (N1 & N2 & N3 & N4 & _). pose proof gran_facts as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
    pose proof Hrng as RG. unfold rngH in RG.
    assert (RD : forall c bs, (0 <= c)%Z -> (c + 8 <= U sp - 2192)%Z -> (c + 8 <= 0x7fff8000)%Z ->
              rdn segs mem (Z_to_bv 64 c) 8 = Some bs -> rdn segs m (Z_to_bv 64 c) 8 = Some bs).
    { intros c bs A B C R. rewrite <- R. apply rdn_ext; [wd_ulia_c|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. apply LOW; lia. }
    split; try (apply RD; [lia | lia | lia | assumption]).
    - (lazymatch goal with |- ?G => let G' := eval unfold m2s_cells in G in change_no_check G' end). repeat apply Forall_cons; try apply Forall_nil; lia.
    - unorm. destruct RG; lia.
    - unorm. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma Hcells_poison : Forall (fun c => 0 <= c /\ c + 8 <= U sp - 2192 /\ c + 8 <= 0x7fff8000)%Z (poison_cells pt).
  Proof using Hcells p_shoff g_shoff p_verb g_verb p_flags g_flags mt.
    rewrite Forall_forall. intros c Hc. apply cell_bound. (lazymatch goal with |- ?G => let G' := eval unfold ann_cells in G in change_no_check G' end).
    apply in_app_iff. right. apply in_app_iff. left. exact Hc.
  Qed.

  Ltac ph_common :=
    pose proof (u64_range sp) as Hspr; pose proof (u64_range base) as Hbr; pose proof Hbase as (HB1 & HB2 & HB3);
    cells_split; pose proof nums as NU; pose proof gran_facts as GF; pose proof Hcells_poison as HCP;
    pose proof Hrng as RG; unfold rngH in RG.
  Ltac rdM1c H := apply rdM1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact H].

  Lemma PH_G1 : (Ao < An)%Z -> (ga < gb1)%Z ->
    poisonH segs pt M1 (Z_to_bv 64 ga) (Z_to_bv 64 (gb1 - ga)) (Z_to_bv 64 0) (at_ base 584) sp2 cpm midend thr.
  Proof using Hshw Hstk Hsp Hrng Hn40 HN2 HN1 HO2 HO1 Hbeg8 Hcells Pcfl Pmset_ok Pmset Prms Pg_rms Phiend Pg_hiend Pmidend Pg_midend Pmidbeg Pg_midbeg Pshoff Pg_shoff endw beg Hbase p_shoff g_shoff p_verb g_verb p_flags g_flags mt.
    intros LT CALL. ph_common. destruct (Pcfl LT CALL) as (C1 & C2 & C3 & C4).
    destruct NU as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15 & N16 & N17 & N18 & N19).
    split.
    - rdM1c Pg_shoff. - rdM1c Pshoff. - rdM1c Pg_midbeg. - rdM1c Pmidbeg. - rdM1c Pg_midend. - rdM1c Pmidend.
    - rdM1c Pg_hiend. - rdM1c Phiend. - rdM1c Pg_rms. - rdM1c Prms. - exact Pmset. - exact Pmset_ok.
    - intros NZ. exfalso. apply NZ. unorm. reflexivity.
    - intros _. split; [rdM1c C1 | split; [rdM1c C2 | split; [| exact C4]]]. (lazymatch goal with |- ?G => let G' := eval unfold shlen in G in change_no_check G' end). unorm. exact C3.
    - eapply Forall_impl; [|exact HCP]. intros c Hc. cbn beta in Hc. (lazymatch goal with |- ?G => let G' := eval unfold sp2 in G in change_no_check G' end). rewrite at_u by lia. lia.
    - unorm. rewrite N15. apply Z_mod_mult.
    - unorm. rewrite N15, N16, <- Z.mul_sub_distr_r. apply Z_mod_mult.
    - unorm. destruct RG as [[R1 R2] | R3]; [left | right]; (nodisj; lia).
    - (lazymatch goal with |- ?G => let G' := eval unfold sp2 in G in change_no_check G' end). rewrite at_u by lia. lia.
    - (lazymatch goal with |- ?G => let G' := eval unfold sp2 in G in change_no_check G' end). rewrite at_at. apply M1_ok.
      eapply (store_ok_sub segs mem (at_ sp (-2192)) _ 2192); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    - apply M1_ok. (lazymatch goal with |- ?G => let G' := eval unfold shad, shlen in G in change_no_check G' end). unorm. rewrite N10.
      apply store_ok_of_all; [unorm; rewrite Z2Nat.id by (nodisj; lia); (nodisj; lia)|]. intros x Hx. rewrite u_Z2bv in Hx by lia. rewrite Z2Nat.id in Hx by lia.
      apply WV. apply Hshw. lia.
    - apply ret_ok_at; [exact HB1 | reflexivity | lia].
  Qed.

  Lemma PH_S1 : (An < Ao)%Z -> (gb2 < gc)%Z ->
    poisonH segs pt M1 (Z_to_bv 64 gb2) (Z_to_bv 64 (gc - gb2)) (Z_to_bv 64 252) (at_ base 584) sp2 cpm midend thr.
  Proof using Hshw Hstk Hsp Hrng Hn40 HN2 HN1 HO2 HO1 Hbeg8 Hcells Pcpm Pmset_ok Pmset Prms Pg_rms Phiend Pg_hiend Pmidend Pg_midend Pmidbeg Pg_midbeg Pshoff Pg_shoff endw beg Hbase p_shoff g_shoff p_verb g_verb p_flags g_flags mt.
    intros LT CALL. ph_common. destruct (Pcpm LT) as (C1 & C2).
    destruct NU as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15 & N16 & N17 & N18 & N19).
    split.
    - rdM1c Pg_shoff. - rdM1c Pshoff. - rdM1c Pg_midbeg. - rdM1c Pmidbeg. - rdM1c Pg_midend. - rdM1c Pmidend.
    - rdM1c Pg_hiend. - rdM1c Phiend. - rdM1c Pg_rms. - rdM1c Prms. - exact Pmset. - exact Pmset_ok.
    - intros _. split; [rdM1c C1 | exact C2].
    - intros Z0. exfalso. revert Z0. unorm. lia.
    - eapply Forall_impl; [|exact HCP]. intros c Hc. cbn beta in Hc. (lazymatch goal with |- ?G => let G' := eval unfold sp2 in G in change_no_check G' end). rewrite at_u by lia. lia.
    - unorm. rewrite N17. apply Z_mod_mult.
    - unorm. rewrite N17, N18, <- Z.mul_sub_distr_r. apply Z_mod_mult.
    - unorm. destruct RG as [[R1 R2] | R3]; [left | right]; (nodisj; lia).
    - (lazymatch goal with |- ?G => let G' := eval unfold sp2 in G in change_no_check G' end). rewrite at_u by lia. lia.
    - (lazymatch goal with |- ?G => let G' := eval unfold sp2 in G in change_no_check G' end). rewrite at_at. apply M1_ok.
      eapply (store_ok_sub segs mem (at_ sp (-2192)) _ 2192); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    - apply M1_ok. (lazymatch goal with |- ?G => let G' := eval unfold shad, shlen in G in change_no_check G' end). unorm. rewrite N11.
      apply store_ok_of_all; [unorm; rewrite Z2Nat.id by (nodisj; lia); (nodisj; lia)|]. intros x Hx. rewrite u_Z2bv in Hx by (nodisj; lia). rewrite Z2Nat.id in Hx by (nodisj; lia).
      apply WV. apply Hshw. (nodisj; lia).
    - apply ret_ok_at; [exact HB1 | reflexivity | lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma incl_saved_clx : forall x, In x [1; 2; 8; 9; 18; 19; 20; 21] -> In x anncc_clobx.
  Proof using rom Hbase base. intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold anncc_clobx in G in change_no_check G' end). cbn [In] in Hx |- *. am_tauto. Qed.
  Lemma incl_poison_clx : forall x, In x poison_clob -> In x anncc_clobx.
  Proof using rom Hbase base. intros x Hx. unfold poison_clob, anncc_clobx in *. cbn [In] in Hx |- *. am_tauto. Qed.
  Lemma incl_m2s_clx : forall x, In x m2s_clob -> In x anncc_clobx.
  Proof using rom Hbase base. intros x Hx. unfold m2s_clob, anncc_clobx in *. cbn [In] in Hx |- *. am_tauto. Qed.

  Lemma SBADDR_lo : (0x7fff8000 <= U SBADDR < 0x10007fff8000)%Z /\ (U SBADDR = gb1 / 8 + 0x7fff8000)%Z.
  Proof using Hrng HN2 HN1 HO2 HO1 Hbeg8 old endw beg Hbase base.
    pose proof nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & _).
    pose proof gran_facts as (G1 & G2 & G3 & _).
    pose proof (Z.div_pos gb1 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_lt_upper_bound gb1 8 17592186044416 ltac:(lia) ltac:(clear -G3 HN2 N2; lia)).
    (lazymatch goal with |- ?G => let G' := eval unfold SBADDR in G in change_no_check G' end). unorm. lia.
  Qed.

  Lemma tail_run : forall (m : word -> option byte) r0,
    (forall a : word, (U sp - 56 <= U a < U sp)%Z -> m a = M1 a) ->
    (forall a : word, (U a < U sp - 2192)%Z -> (U a < 0x7fff8000)%Z -> m a = mem a) ->
    mem_grows mem m ->
    getr r0 2 = sp2 -> getr r0 8 = sp -> getr r0 9 = Z_to_bv 64 gb1 -> getr r0 18 = Z_to_bv 64 gb2 -> getr r0 21 = new ->
    regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 584) m rom)
                  (mkst r ra (if (An mod 8 =? 0)%Z then m else wbytes m SBADDR [Z_to_bv 8 (An mod 8)]) rom)
      /\ getr r 1 = ra /\ getr r 2 = sp /\ getr r 8 = getr regs 8 /\ getr r 9 = getr regs 9 /\ getr r 18 = getr regs 18
      /\ getr r 19 = getr regs 19 /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21
      /\ regs_agree CLX regs r.
  Proof using Hret Hshw Hsp Hrng Hn40 HN2 HN1 HO2 HO1 Hbeg8 Hcells Mhiend Mg_hiend Mmidend Mg_midend Mmidbeg Mg_midbeg Mshoff Mg_shoff midend2 old endw beg Hbase MTB MTOK HCODE p_shoff g_shoff p_verb g_verb p_flags g_flags mt pt.
    intros m r0 SLm LOWm GRm R2 R8 R9 R18 R21 AG0.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range base) as Hbr. pose proof Hbase as (HB1 & HB2 & HB3). pose proof Hsp as SP.
    pose proof (slots_of m SLm) as SL.
    destruct (Z.eqb_spec (An mod 8) 0) as [A0 | A1].
    - destruct (blkT0 m r0 A0 R2 R9 R18 AG0) as (r1 & RUN1 & Q2 & AG1).
      destruct (blkZ m r1 SL Q2) as (r2 & RUN2 & Z1 & Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & AGZ).
      exists r2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|].
      repeat (split; [assumption|]).
      eapply regs_agree_trans; [exact AG1 | eapply regs_agree_mono; [| exact AGZ]; exact incl_saved_clx].
    - destruct (blkT1a m r0 A1 R2 R8 R9 R18 R21 AG0) as (r1 & RUN1 & Q1 & Q2 & Q8 & Q10 & Q18 & AG1).
      assert (RA : ret_ok (at_ base 612)) by (apply ret_ok_at; [exact HB1 | reflexivity | lia]).
      destruct (m2s_run segs mt MTOK m rom (Z_to_bv 64 gb1) midend2 (at_ base 612) r1 (m2sH_of_low m LOWm) Q10 Q1 RA)
        as (r2 & RUN2 & P10 & AG2).
      pose proof SBADDR_lo as ((SB1 & SB2) & SB3).
      assert (P10' : getr r2 10 = SBADDR).
      { rewrite P10. (lazymatch goal with |- ?G => let G' := eval unfold SBADDR in G in change_no_check G' end). apply bv_eq. pose proof nums as (_ & N2 & _ & N4 & _). pose proof gran_facts as (_ & _ & G3 & _).
        assert (gb1 < 0x800000000000)%Z by (clear -G3 HN2 N2; lia). unorm. reflexivity. }
      assert (P18 : getr r2 18 = Z_to_bv 64 (An mod 8)) by (rewrite (AG2 18) by notin; exact Q18).
      assert (OKb : store_ok segs m SBADDR 1 = true).
      { eapply store_ok_mono; [exact GRm|]. apply Hshw. rewrite SB3.
        pose proof nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15 & N16 & N17 & N18 & N19).
        pose proof (N19 A1). lia. }
      pose proof (blkT1b m r2 SBADDR P10' P18 OKb) as RUN3.
      assert (SL' : forall k v, In (k, v) ann_slots -> rdn segs (wbytes m SBADDR [Z_to_bv 8 (An mod 8)]) (at_ sp k) 8 = Some (word_to_le_bytes 8 v)).
      { apply slots_of. intros a Ha. rewrite wbytes_outside; [apply SLm; exact Ha | (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
      assert (Q2' : getr r2 2 = sp2) by (rewrite (AG2 2) by notin; exact Q2).
      destruct (blkZ _ r2 SL' Q2') as (r3 & RUN4 & Z1 & Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & AGZ).
      exists r3. split.
      + eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3 | exact RUN4].
      + repeat (split; [assumption|]).
        eapply regs_agree_trans; [exact AG1|]. eapply regs_agree_trans.
        * eapply regs_agree_mono; [| exact AG2]. exact incl_m2s_clx.
        * eapply regs_agree_mono; [| exact AGZ]. exact incl_saved_clx.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem anncc_run0 :
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r ra ann_mem rom)
      /\ getr r 2 = sp /\ regs_agree CL regs r.
  Proof using H13 H12 H11 H10 H2 H1 Hret Hshw Hstk Hsp Hrng Hn40 HN2 HN1 HO2 HO1 Hbeg8 Hcells Mhiend Mg_hiend Mmidend Mg_midend Mmidbeg Mg_midbeg Mshoff Mg_shoff Pcfl Pcpm Pmset_ok Pmset Prms Pg_rms Phiend Pg_hiend Pmidend Pg_midend Pmidbeg Pg_midbeg Pshoff Pg_shoff Reb Rverb Rg_verb Hdco Rdco Rg_flags thr midend2 midend cpm eb dco endw beg Hbase G404 G72 G44 MTB MTOK PTB PTOK HCODE p_shoff g_shoff p_verb g_verb p_flags g_flags mt pt.
    pose proof (u64_range sp) as Hspr. pose proof Hsp as SP.
    assert (FINAL : forall r, getr r 1 = ra -> getr r 2 = sp -> getr r 8 = getr regs 8 -> getr r 9 = getr regs 9 ->
              getr r 18 = getr regs 18 -> getr r 19 = getr regs 19 -> getr r 20 = getr regs 20 -> getr r 21 = getr regs 21 ->
              regs_agree CLX regs r -> regs_agree CL regs r).
    { intros r Z1 Z2 Z8 Z9 Z18 Z19 Z20 Z21 AG x Hx.
      destruct (In_dec (fun a b : reg => decide (a = b)) x [1; 2; 8; 9; 18; 19; 20; 21]) as [Hin | Hnin].
      - cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [first [rewrite Z1; symmetry; exact H1 | rewrite Z2; symmetry; exact H2 | assumption] |]). destruct Hin.
      - apply AG. intros Hc. unfold anncc_clobx in Hc. cbn [In] in Hc, Hnin. apply Hx. (lazymatch goal with |- ?G => let G' := eval unfold anncc_clob in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end). clear - Hc Hnin. am_tauto. }
    destruct blkA as (rA & RUNA & A1 & A2 & A8 & A9 & A18 & A19 & A20 & AGA).
    (lazymatch goal with |- ?G => let G' := eval unfold ann_mem in G in change_no_check G' end). destruct (Z.eqb_spec Ao An) as [EQ | NE].
    { destruct (blkB_eq rA EQ A1 A2 A8 A9 A18 A19 A20 AGA) as (rB & RUNB & B2 & AGB).
      destruct (blkZ M1 rB slots_M1 B2) as (rZ & RUNZ & Z1 & Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & AGZ).
      exists rZ. split; [eapply msteps_trans; [exact RUNA|]; eapply msteps_trans; [exact RUNB | exact RUNZ] |].
      split; [exact Z2|]. apply (FINAL rZ Z1 Z2 Z8 Z9 Z18 Z19 Z20 Z21).
      eapply regs_agree_trans; [exact AGB | eapply regs_agree_mono; [| exact AGZ]; exact incl_saved_clx]. }
    destruct (blkB_ne rA NE A1 A2 A8 A9 A18 A19 A20 AGA) as (rB & RUNB & B1 & B2 & B8 & B9 & B18 & B19 & B20 & AGB).
    (* [comment removed for export] *)
    assert (MID : exists r, msteps segs (mkst rB (at_ base 292) M1 rom) (mkst r (at_ base 584) ann_M2 rom)
              /\ getr r 2 = sp2 /\ getr r 8 = sp /\ getr r 9 = Z_to_bv 64 gb1 /\ getr r 18 = Z_to_bv 64 gb2 /\ getr r 21 = new
              /\ regs_agree CLX regs r).
    { (lazymatch goal with |- ?G => let G' := eval unfold ann_M2 in G in change_no_check G' end). destruct (Z.ltb_spec Ao An) as [LT | GE].
      - destruct (Z.ltb_spec ga gb1) as [CALL | NOCALL].
        + destruct (blkD_G1 rB LT CALL B1 B2 B8 B9 B18 B19 B20 AGB) as (rD & RUND & D1 & D2 & D8 & D9 & D18 & D19 & D20 & D21 & D10 & D11 & D12 & AGD).
          destruct (poison_shadow segs pt PTOK M1 rom (Z_to_bv 64 ga) (Z_to_bv 64 (gb1 - ga)) (Z_to_bv 64 0) (at_ base 584) sp2 cpm midend thr rD
                      (PH_G1 LT CALL) D1 D2 D10 D11 D12) as (rP & RUNP & AGP).
          rewrite D8, D9, D18, D19, D20, D21 in RUNP. change (wbytes _ _ _) with (PZ M1 ga gb1 0) in RUNP.
          exists rP. split; [eapply msteps_trans; [exact RUND | exact RUNP]|].
          repeat split; try (rewrite (AGP _) by notin; assumption).
          eapply regs_agree_trans; [exact AGD | eapply regs_agree_mono; [| exact AGP]; exact incl_poison_clx].
        + destruct (blkD_G0 rB LT ltac:(lia) B1 B2 B8 B9 B18 B19 B20 AGB) as (rD & RUND & D1 & D2 & D8 & D9 & D18 & D19 & D20 & D21 & AGD).
          exists rD. repeat (split; [assumption|]). exact AGD.
      - assert (LT : (An < Ao)%Z) by lia.
        destruct (Z.ltb_spec gb2 gc) as [CALL | NOCALL].
        + destruct (blkD_S1 rB LT CALL B1 B2 B8 B9 B18 B19 B20 AGB) as (rD & RUND & D1 & D2 & D8 & D9 & D18 & D19 & D20 & D21 & D10 & D11 & D12 & AGD).
          destruct (poison_shadow segs pt PTOK M1 rom (Z_to_bv 64 gb2) (Z_to_bv 64 (gc - gb2)) (Z_to_bv 64 252) (at_ base 584) sp2 cpm midend thr rD
                      (PH_S1 LT CALL) D1 D2 D10 D11 D12) as (rP & RUNP & AGP).
          rewrite D8, D9, D18, D19, D20, D21 in RUNP. change (wbytes _ _ _) with (PZ M1 gb2 gc 252) in RUNP.
          exists rP. split; [eapply msteps_trans; [exact RUND | exact RUNP]|].
          repeat split; try (rewrite (AGP _) by notin; assumption).
          eapply regs_agree_trans; [exact AGD | eapply regs_agree_mono; [| exact AGP]; exact incl_poison_clx].
        + destruct (blkD_S0 rB LT ltac:(lia) B1 B2 B8 B9 B18 B19 B20 AGB) as (rD & RUND & D1 & D2 & D8 & D9 & D18 & D19 & D20 & D21 & AGD).
          exists rD. repeat (split; [assumption|]). exact AGD. }
    destruct MID as (rM & RUNM & Q2 & Q8 & Q9 & Q18 & Q21 & AGM).
    destruct (tail_run ann_M2 rM M2_slots M2_low M2_grows Q2 Q8 Q9 Q18 Q21 AGM) as (rT & RUNT & Z1 & Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & AGT).
    exists rT. split.
    - eapply msteps_trans; [exact RUNA|]. eapply msteps_trans; [exact RUNB|]. eapply msteps_trans; [exact RUNM|].
      (lazymatch goal with |- ?G => let G' := eval unfold ann_M3 in G in change_no_check G' end). exact RUNT.
    - split; [exact Z2|]. exact (FINAL rT Z1 Z2 Z8 Z9 Z18 Z19 Z20 Z21 AGT).
  Qed.
  End WithRegs.

End ANNCC. End FPGen1.
