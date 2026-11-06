(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM2. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA.AsRtXStrlen OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM2.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= am_lia.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPGen1.
Context {fx : FPState}.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation W8 w := (word_to_le_bytes 8 w).
#[local] Abbreviation LE8 z := (word_to_le_bytes 8 (Z_to_bv 64 z)).

(* [comment removed for export] *)
Definition sk_pos (hint i : Z) : Z := ((hint + i) mod 16384)%Z.
Definition sk0_flag (fs : word) (hint i : Z) : Z := (U fs + 4096 + sk_pos hint i)%Z.
Definition sk0_frame (fs : word) (hint i : Z) : Z := (U fs + 36864 + sk_pos hint i * 64)%Z.
Definition sk0_sh (fs : word) (hint i : Z) : Z := (sk0_frame fs hint i / 8 + 0x7fff8000)%Z.

(* [comment removed for export] *)
Definition sk0_mem4 (m : word -> option byte) (fs : word) (hint i0 : Z) (S : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (U fs)) (LE8 (hint + i0 + 1)))
    (Z_to_bv 64 (sk0_flag fs hint i0)) [Z_to_bv 8 1])
    (Z_to_bv 64 (sk0_frame fs hint i0 + 24)) (W8 S))
    (Z_to_bv 64 (sk0_frame fs hint i0 + 56)) (LE8 (sk0_flag fs hint i0)).
(* [comment removed for export] *)
Definition sk0_mem (m : word -> option byte) (fs : word) (hint i0 : Z) (S : word) : word -> option byte :=
  wbytes (sk0_mem4 m fs hint i0 S) (Z_to_bv 64 (sk0_sh fs hint i0)) (LE8 0).

Lemma sk_pos_rng : forall hint i, (0 <= sk_pos hint i < 16384)%Z.
Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold sk_pos in G in change_no_check G' end). apply Z.mod_pos_bound. lia. Qed.

(* [comment removed for export] *)
Lemma v_and_maskN : forall (j : Z) z, (0 <= j <= 62)%Z -> v_and (Z_to_bv 64 z) (Z_to_bv 64 (2 ^ j - 1)) = Z_to_bv 64 (z mod 2 ^ j).
Proof using.
  intros j z Hj. (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end). assert (P : (0 < 2 ^ j)%Z) by (apply Z.pow_pos_nonneg; lia).
  assert (P64 : (2 ^ j < 2 ^ 64)%Z) by (apply Z.pow_lt_mono_r; lia).
  rewrite (u_Z2bv (2 ^ j - 1)) by lia. rewrite Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 64) with (2 ^ 64)%Z.
  replace (2 ^ j - 1)%Z with (Z.ones j) by (rewrite Z.ones_equiv; lia). rewrite Z.land_ones by lia.
  rewrite Z.mod_mod_divide; [reflexivity|].
  exists (2 ^ (64 - j))%Z. rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.
Lemma v_and_16332 : forall z, v_and (Z_to_bv 64 z) (Z_to_bv 64 16383) = Z_to_bv 64 (z mod 16384).
Proof using. intros z. exact (v_and_maskN 14 z ltac:(lia)). Qed.
Lemma v_addi_Z : forall z i, v_addi (Z_to_bv 64 z) i = Z_to_bv 64 (z + i).
Proof using.
  intros z i. (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end). apply bv_eq. rewrite !Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma v_add_ZZ : forall a b, v_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof using.
  intros a b. (lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end). apply bv_eq. rewrite !Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite <- Zplus_mod. reflexivity.
Qed.
Lemma v_addiw_m1 : forall z, (1 <= z < 2 ^ 31)%Z -> v_addiw (Z_to_bv 64 z) (-1) = Z_to_bv 64 (z - 1).
Proof using.
  intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold v_addiw in G in change_no_check G' end). rewrite u_Z2bv by lia.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31)%Z; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sk0_sh_rng : forall (fs : word) hint i, (U fs + 1085440 <= 2 ^ 47)%Z ->
  (0x7fff8000 <= sk0_sh fs hint i /\ sk0_sh fs hint i + 8 <= 0x10007fff8000)%Z.
Proof using.
  intros fs hint i H64. pose proof (u64_range fs) as Hfr. (lazymatch goal with |- ?G => let G' := eval unfold sk0_sh, sk0_frame in G in change_no_check G' end). pose proof (sk_pos_rng hint i) as Hp.
  pose proof (Z.div_pos (U fs + 36864 + sk_pos hint i * 64) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_upper_bound (U fs + 36864 + sk_pos hint i * 64) 8 (2 ^ 44 - 8) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma v_slli_6 : forall z, (0 <= z < 2 ^ 32)%Z -> v_slli (Z_to_bv 64 z) 6 = Z_to_bv 64 (z * 64).
Proof using. intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end). rewrite u_Z2bv by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.

Ltac av_and F D vv tac :=
  chain_step;
  [ reflexivity
  | eapply AsRtFlush.step_and_at with (v := vv); [ exact F | reflexivity | exact D | reflexivity | gres; rwH; imm_norm; tac ]
  | step_simpl ]; vn.

(* [comment removed for export] *)
Definition stk0_words : list (option (bv 32)) :=
  [
   Some W_57164; Some W_57168; Some W_5716c; Some W_57170; Some W_57174; Some W_57178; None; None; Some W_57184;
   Some W_57188; Some W_5718c; Some W_57190; Some W_57194; Some W_57198; Some W_5719c; Some W_571a0; Some W_571a4;
   Some W_571a8; Some W_571ac; Some W_571b0; Some W_571b4; Some W_571b8; Some W_571bc; Some W_571c0; Some W_571c4;
   Some W_571c8; Some W_571cc; Some W_571d0; Some W_571d4; Some W_571d8; Some W_571dc; Some W_571e0; Some W_571e4;
   Some W_571e8; Some W_571ec; Some W_571f0; Some W_571f4; Some W_571f8; Some W_571fc; Some W_57200; Some W_57204;
   Some W_57208; None; None; Some W_57214; Some W_57218; Some W_5721c; Some W_57220; Some W_57224; Some W_57228;
   Some W_5722c; Some W_57230; Some W_57234; Some W_57238; Some W_5723c; Some W_57240; Some W_57244; Some W_57248;
   Some W_5724c; Some W_57250; Some W_57254; Some W_57258; Some W_5725c; Some W_57260; Some W_57264; Some W_57268;
   Some W_5726c; Some W_57270; Some W_57274; Some W_57278; Some W_5727c; Some W_57280; Some W_57284; Some W_57288;
   Some W_5728c; Some W_57290; Some W_57294; Some W_57298; Some W_5729c; Some W_572a0; Some W_572a4; Some W_572a8;
   Some W_572ac; Some W_572b0; Some W_572b4; Some W_572b8; Some W_572bc; Some W_572c0; Some W_572c4; Some W_572c8;
   Some W_572cc; Some W_572d0; Some W_572d4
  ]%list.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section STK0B.
  Variables (segs : list Segment) (sb : word).
  Variable mt : m2s_tab.
  Hypothesis HC_S0 : code_ato segs sb 0 stk0_words.
  Hypothesis MTOK : m2s_tab_ok segs mt.
  Hypothesis MTB : mt_base mt = at_ sb 1612.
  Hypothesis Hsb : (U sb mod 2 = 0)%Z /\ (U sb + 30000 < 2 ^ 64)%Z.


  Lemma F_57164 : fetch_word segs (at_ sb 0) = Some W_57164.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 0 _ HC_S0 eq_refl). Qed.
  Lemma F_57168 : fetch_word segs (at_ sb 4) = Some W_57168.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 1 _ HC_S0 eq_refl). Qed.
  Lemma F_5716c : fetch_word segs (at_ sb 8) = Some W_5716c.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 2 _ HC_S0 eq_refl). Qed.
  Lemma F_57170 : fetch_word segs (at_ sb 12) = Some W_57170.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 3 _ HC_S0 eq_refl). Qed.
  Lemma F_57174 : fetch_word segs (at_ sb 16) = Some W_57174.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 4 _ HC_S0 eq_refl). Qed.
  Lemma F_57178 : fetch_word segs (at_ sb 20) = Some W_57178.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 5 _ HC_S0 eq_refl). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma F_57184 : fetch_word segs (at_ sb 32) = Some W_57184.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 8 _ HC_S0 eq_refl). Qed.
  Lemma F_57188 : fetch_word segs (at_ sb 36) = Some W_57188.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 9 _ HC_S0 eq_refl). Qed.
  Lemma F_5718c : fetch_word segs (at_ sb 40) = Some W_5718c.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 10 _ HC_S0 eq_refl). Qed.
  Lemma F_57190 : fetch_word segs (at_ sb 44) = Some W_57190.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 11 _ HC_S0 eq_refl). Qed.
  Lemma F_57194 : fetch_word segs (at_ sb 48) = Some W_57194.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 12 _ HC_S0 eq_refl). Qed.
  Lemma F_57198 : fetch_word segs (at_ sb 52) = Some W_57198.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 13 _ HC_S0 eq_refl). Qed.



  Lemma F_571a8 : fetch_word segs (at_ sb 68) = Some W_571a8.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 17 _ HC_S0 eq_refl). Qed.
  Lemma F_571ac : fetch_word segs (at_ sb 72) = Some W_571ac.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 18 _ HC_S0 eq_refl). Qed.
  Lemma F_571b0 : fetch_word segs (at_ sb 76) = Some W_571b0.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 19 _ HC_S0 eq_refl). Qed.
  Lemma F_571b4 : fetch_word segs (at_ sb 80) = Some W_571b4.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 20 _ HC_S0 eq_refl). Qed.
  Lemma F_571b8 : fetch_word segs (at_ sb 84) = Some W_571b8.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 21 _ HC_S0 eq_refl). Qed.
  Lemma F_571bc : fetch_word segs (at_ sb 88) = Some W_571bc.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 22 _ HC_S0 eq_refl). Qed.
  Lemma F_571c0 : fetch_word segs (at_ sb 92) = Some W_571c0.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 23 _ HC_S0 eq_refl). Qed.
  Lemma F_571c4 : fetch_word segs (at_ sb 96) = Some W_571c4.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 24 _ HC_S0 eq_refl). Qed.
  Lemma F_571c8 : fetch_word segs (at_ sb 100) = Some W_571c8.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 25 _ HC_S0 eq_refl). Qed.
  Lemma F_571cc : fetch_word segs (at_ sb 104) = Some W_571cc.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 26 _ HC_S0 eq_refl). Qed.
  Lemma F_571d0 : fetch_word segs (at_ sb 108) = Some W_571d0.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 27 _ HC_S0 eq_refl). Qed.
  Lemma F_571d4 : fetch_word segs (at_ sb 112) = Some W_571d4.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 28 _ HC_S0 eq_refl). Qed.
  Lemma F_571d8 : fetch_word segs (at_ sb 116) = Some W_571d8.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 29 _ HC_S0 eq_refl). Qed.
  Lemma F_571dc : fetch_word segs (at_ sb 120) = Some W_571dc.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 30 _ HC_S0 eq_refl). Qed.
  Lemma F_571e0 : fetch_word segs (at_ sb 124) = Some W_571e0.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 31 _ HC_S0 eq_refl). Qed.
  Lemma F_571e4 : fetch_word segs (at_ sb 128) = Some W_571e4.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 32 _ HC_S0 eq_refl). Qed.
  Lemma F_571e8 : fetch_word segs (at_ sb 132) = Some W_571e8.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 33 _ HC_S0 eq_refl). Qed.
  Lemma F_571ec : fetch_word segs (at_ sb 136) = Some W_571ec.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 34 _ HC_S0 eq_refl). Qed.
  Lemma F_571f0 : fetch_word segs (at_ sb 140) = Some W_571f0.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 35 _ HC_S0 eq_refl). Qed.
  Lemma F_571f4 : fetch_word segs (at_ sb 144) = Some W_571f4.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 36 _ HC_S0 eq_refl). Qed.
  Lemma F_571f8 : fetch_word segs (at_ sb 148) = Some W_571f8.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 37 _ HC_S0 eq_refl). Qed.
  Lemma F_571fc : fetch_word segs (at_ sb 152) = Some W_571fc.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 38 _ HC_S0 eq_refl). Qed.
  Lemma F_57200 : fetch_word segs (at_ sb 156) = Some W_57200.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 39 _ HC_S0 eq_refl). Qed.





















  Lemma F_57260 : fetch_word segs (at_ sb 252) = Some W_57260.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 63 _ HC_S0 eq_refl). Qed.
  Lemma F_57264 : fetch_word segs (at_ sb 256) = Some W_57264.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 64 _ HC_S0 eq_refl). Qed.
  Lemma F_57268 : fetch_word segs (at_ sb 260) = Some W_57268.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 65 _ HC_S0 eq_refl). Qed.
  Lemma F_5726c : fetch_word segs (at_ sb 264) = Some W_5726c.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 66 _ HC_S0 eq_refl). Qed.
  Lemma F_57270 : fetch_word segs (at_ sb 268) = Some W_57270.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 67 _ HC_S0 eq_refl). Qed.
  Lemma F_57274 : fetch_word segs (at_ sb 272) = Some W_57274.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 68 _ HC_S0 eq_refl). Qed.
  Lemma F_57278 : fetch_word segs (at_ sb 276) = Some W_57278.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 69 _ HC_S0 eq_refl). Qed.
  Lemma F_5727c : fetch_word segs (at_ sb 280) = Some W_5727c.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 70 _ HC_S0 eq_refl). Qed.
  Lemma F_57280 : fetch_word segs (at_ sb 284) = Some W_57280.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 71 _ HC_S0 eq_refl). Qed.
  Lemma F_57284 : fetch_word segs (at_ sb 288) = Some W_57284.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 72 _ HC_S0 eq_refl). Qed.
  Lemma F_57288 : fetch_word segs (at_ sb 292) = Some W_57288.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 73 _ HC_S0 eq_refl). Qed.
  Lemma F_5728c : fetch_word segs (at_ sb 296) = Some W_5728c.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 74 _ HC_S0 eq_refl). Qed.
  Lemma F_57290 : fetch_word segs (at_ sb 300) = Some W_57290.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 75 _ HC_S0 eq_refl). Qed.
  Lemma F_57294 : fetch_word segs (at_ sb 304) = Some W_57294.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 76 _ HC_S0 eq_refl). Qed.
  Lemma F_57298 : fetch_word segs (at_ sb 308) = Some W_57298.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 77 _ HC_S0 eq_refl). Qed.
  Lemma F_5729c : fetch_word segs (at_ sb 312) = Some W_5729c.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 78 _ HC_S0 eq_refl). Qed.
  Lemma F_572a0 : fetch_word segs (at_ sb 316) = Some W_572a0.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 79 _ HC_S0 eq_refl). Qed.
  Lemma F_572a4 : fetch_word segs (at_ sb 320) = Some W_572a4.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 80 _ HC_S0 eq_refl). Qed.
  Lemma F_572a8 : fetch_word segs (at_ sb 324) = Some W_572a8.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 81 _ HC_S0 eq_refl). Qed.
  Lemma F_572ac : fetch_word segs (at_ sb 328) = Some W_572ac.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 82 _ HC_S0 eq_refl). Qed.
  Lemma F_572b0 : fetch_word segs (at_ sb 332) = Some W_572b0.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 83 _ HC_S0 eq_refl). Qed.
  Lemma F_572b4 : fetch_word segs (at_ sb 336) = Some W_572b4.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 84 _ HC_S0 eq_refl). Qed.
  Lemma F_572b8 : fetch_word segs (at_ sb 340) = Some W_572b8.   (* [comment removed for export] *)
  Proof using HC_S0. exact (code_ato_get segs sb 0 stk0_words 85 _ HC_S0 eq_refl). Qed.








  Variable m : word -> option byte.
  Variable rom : word -> option byte.
  Variables (ra S resw fs midend s0v s1v s2v : word).
  Variables (hint i0 : Z).
  (* [comment removed for export] *)
  #[local] Abbreviation FLG := (sk0_flag fs hint i0).
  #[local] Abbreviation FRM := (sk0_frame fs hint i0).
  #[local] Abbreviation SHW := (sk0_sh fs hint i0).
  Hypothesis Rfs : rdn segs m (Z_to_bv 64 (U resw)) 8 = Some (W8 fs).
  Hypothesis Rgc : rdn segs m (Z_to_bv 64 (U fs + 96)) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rlog : rdn segs m (Z_to_bv 64 (U fs + 88)) 8 = Some (LE8 20).
  Hypothesis Rhint : rdn segs m (Z_to_bv 64 (U fs)) 8 = Some (LE8 hint).
  Hypothesis Hnz : forall j, (0 <= j < i0)%Z -> exists b : byte, rdn segs m (Z_to_bv 64 (sk0_flag fs hint j)) 1 = Some [b] /\ U b <> 0%Z.
  Hypothesis Hz : rdn segs m (Z_to_bv 64 FLG) 1 = Some [Z_to_bv 8 0].
  Hypothesis OKh : store_ok segs m (Z_to_bv 64 (U fs)) 8 = true.
  Hypothesis OKf : store_ok segs m (Z_to_bv 64 FLG) 1 = true.
  Hypothesis OK24 : store_ok segs m (Z_to_bv 64 (FRM + 24)) 8 = true.
  Hypothesis OK56 : store_ok segs m (Z_to_bv 64 (FRM + 56)) 8 = true.
  Hypothesis OKsh : store_ok segs m (Z_to_bv 64 SHW) 8 = true.
  Hypothesis PHm : m2sH segs mt m (Z_to_bv 64 FRM) midend.
  Hypothesis Hmcells : Forall (fun c => 0 <= c /\ c + 8 <= U fs)%Z (m2s_cells mt).
  (* [comment removed for export] *)
  Hypothesis FR1 : rdn segs m (at_ S (-8)) 8 = Some (W8 ra).
  Hypothesis FR2 : rdn segs m (at_ S (-16)) 8 = Some (W8 s0v).
  Hypothesis FR3 : rdn segs m (at_ S (-24)) 8 = Some (W8 s1v).
  Hypothesis FR4 : rdn segs m (at_ S (-32)) 8 = Some (W8 s2v).
  (* [comment removed for export] *)
  Hypothesis Hfs : (0 < U fs /\ U fs + 1085440 <= 2 ^ 47 /\ 0x10007fff8000 + 208 <= U S)%Z /\ (U fs + 1085440 <= U S - 32)%Z.
  Hypothesis Hres : (U resw <> 0)%Z.
  Hypothesis Hfsnz : (U fs <> 0)%Z.
  Hypothesis Hhint : (0 <= hint)%Z.
  Hypothesis Hi0 : (0 <= i0 < 16384)%Z.
  Hypothesis HS : (32 <= U S)%Z.
  Hypothesis Hret : ret_ok ra.

  Ltac addr_eq :=
    apply bv_eq; rewrite ?v_addi_0;
    repeat match goal with |- context [v_addi ?b ?e] => change (v_addi b e) with (at_ b e) end;
    (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia.
  Ltac rdm Hr :=
    repeat (rewrite wd_rdn_wbytes_out3; [ | rd8_side ]);
    lazymatch goal with |- rdn _ m _ _ = _ => exact Hr end.
  Ltac cldz F D cc vv Hr :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm;
          lazymatch goal with |- rdn _ _ ?a _ = _ => replace a with (Z_to_bv 64 cc : word) by addr_eq end;
          rdm Hr
        | apply bytes_le_to_Z_8]
      | step_simpl]; vn.
  Ltac clbu F D cc Hr :=
    chain_step; [reflexivity
      | eapply step_lbu; [exact F | reflexivity | exact D | ];
        gres; rwH; imm_norm;
        lazymatch goal with |- rdn _ _ ?a _ = _ => replace a with (Z_to_bv 64 cc : word) by addr_eq end;
        rdm Hr
      | step_simpl]; vn.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition LCLOB : list reg := [10; 12; 15; 16; 17]%list.

  Lemma sk0_iter : forall (i : Z) r,
    (0 <= i < i0)%Z ->
    getr r 10 = Z_to_bv 64 (16384 - i) -> getr r 12 = Z_to_bv 64 (hint + i) ->
    getr r 11 = Z_to_bv 64 (U fs + 4096) -> getr r 13 = Z_to_bv 64 16383 ->
    exists r',
      msteps segs (mkst r (at_ sb 132) m rom) (mkst r' (at_ sb 132) m rom)
      /\ getr r' 10 = Z_to_bv 64 (16384 - (i + 1)) /\ getr r' 12 = Z_to_bv 64 (hint + (i + 1))
      /\ regs_agree (fun x => In x LCLOB) r r'.
  Proof using Hi0 Hhint Hfsnz Hfs Hnz S HC_S0.
    intros i r Hi Q10 Q12 Q11 Q13. pose proof Hhint as Hh0. destruct Hfs as [Hf0 Hf1].
    pose proof (u64_range fs) as Hfr. pose proof (u64_range S) as HSr. pose proof (sk_pos_rng hint i) as Hp.
    destruct (Hnz i Hi) as (b & Rb & Nb). pose proof (u8_range b) as Hb8.
    wd_eexists. split.
    - av_and F_571e8 D_571e8 (Z_to_bv 64 (sk_pos hint i)) ltac:(rewrite v_and_16332; reflexivity).      (* [comment removed for export] *)
      av F_571ec D_571ec (Z_to_bv 64 (sk0_flag fs hint i)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add, sk0_flag in G in change_no_check G' end); unorm; f_equal; lia). (* [comment removed for export] *)
      clbu F_571f0 D_571f0 (sk0_flag fs hint i) Rb.            (* [comment removed for export] *)
      ab_ft F_571f4 D_571f4 ltac:(condz).                      (* [comment removed for export] *)
      av F_571f8 D_571f8 (Z_to_bv 64 (16384 - (i + 1))) ltac:(rewrite v_addiw_m1 by lia; f_equal; lia).    (* [comment removed for export] *)
      av F_571fc D_571fc (Z_to_bv 64 (hint + (i + 1))) ltac:(rewrite v_addi_Z; f_equal; lia).           (* [comment removed for export] *)
      ab_tk F_57200 D_57200 ltac:(condz).                      (* [comment removed for export] *)
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold LCLOB in G in change_no_check G' end). ra_solve.
  Qed.

  Lemma sk0_loop : forall (n : nat) (i : Z) r,
    (0 <= i)%Z -> (i + Z.of_nat n = i0)%Z ->
    getr r 10 = Z_to_bv 64 (16384 - i) -> getr r 12 = Z_to_bv 64 (hint + i) ->
    getr r 11 = Z_to_bv 64 (U fs + 4096) -> getr r 13 = Z_to_bv 64 16383 ->
    exists r',
      msteps segs (mkst r (at_ sb 132) m rom) (mkst r' (at_ sb 252) m rom)
      /\ getr r' 12 = Z_to_bv 64 (hint + i0) /\ getr r' 15 = Z_to_bv 64 FLG /\ getr r' 16 = Z_to_bv 64 (sk_pos hint i0)
      /\ regs_agree (fun x => In x LCLOB) r r'.
  Proof using Hi0 Hhint Hfsnz Hfs Hz Hnz S HC_S0.
    induction n as [|n IH]; intros i r Hi0' Hin Q10 Q12 Q11 Q13.
    - assert (i = i0) by lia. subst i. pose proof Hhint as Hh0. destruct Hfs as [Hf0 Hf1].
      pose proof (u64_range fs) as Hfr. pose proof (u64_range S) as HSr. pose proof (sk_pos_rng hint i0) as Hp.
      wd_eexists. split.
      + av_and F_571e8 D_571e8 (Z_to_bv 64 (sk_pos hint i0)) ltac:(rewrite v_and_16332; reflexivity).   (* [comment removed for export] *)
        av F_571ec D_571ec (Z_to_bv 64 FLG) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add, sk0_flag in G in change_no_check G' end); unorm; f_equal; lia).              (* [comment removed for export] *)
        clbu F_571f0 D_571f0 (sk0_flag fs hint i0) Hz.                           (* [comment removed for export] *)
        ab_tk F_571f4 D_571f4 ltac:(vals_lit; condz).          (* [comment removed for export] *)
        wd_refl.
      + post. (lazymatch goal with |- ?G => let G' := eval unfold LCLOB in G in change_no_check G' end). ra_solve.
    - destruct (sk0_iter i r ltac:(lia) Q10 Q12 Q11 Q13) as (r1 & RUN1 & A10 & A12 & AG1).
      assert (A11 : getr r1 11 = Z_to_bv 64 (U fs + 4096)) by (rewrite (AG1 11 ltac:((lazymatch goal with |- ?G => let G' := eval unfold LCLOB in G in change_no_check G' end); notin)); exact Q11).
      assert (A13 : getr r1 13 = Z_to_bv 64 16383) by (rewrite (AG1 13 ltac:((lazymatch goal with |- ?G => let G' := eval unfold LCLOB in G in change_no_check G' end); notin)); exact Q13).
      destruct (IH (i + 1)%Z r1 ltac:(lia) ltac:(lia) A10 A12 A11 A13) as (r' & RUN2 & B12 & B15 & B16 & AG2).
      exists r'. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|]. repeat (split; [assumption|]).
      eapply regs_agree_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac wsd F D cc OK :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := Z_to_bv 64 cc);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; addr_eq
        | gres; rwH; reflexivity
        | (lazymatch goal with |- ?G => let G' := eval unfold sk0_mem4 in G in change_no_check G' end); repeat (eapply store_ok_mono; [apply wbytes_grows|]); exact OK ]
      | step_simpl]; vn.
  Ltac fldm F D vv FR :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold sk0_mem, sk0_mem4 in G in change_no_check G' end);
          repeat (rewrite wd_rdn_wbytes_out3; [ | rd8_side ]); exact FR
        | apply bytes_le_to_Z_8]
      | step_simpl]; vn.

  Definition S2CLOB : list reg := [9; 18; 10; 11; 12; 13; 14; 15]%list.

  (* [comment removed for export] *)
  Lemma blkS2 : forall r2,
    getr r2 10 = resw -> getr r2 2 = at_ S (-32) -> getr r2 8 = S ->
    exists r,
      msteps segs (mkst r2 (at_ sb 36) m rom) (mkst r (at_ sb 132) m rom)
      /\ getr r 10 = Z_to_bv 64 (16384 - 0) /\ getr r 12 = Z_to_bv 64 (hint + 0)
      /\ getr r 11 = Z_to_bv 64 (U fs + 4096) /\ getr r 13 = Z_to_bv 64 16383
      /\ getr r 9 = fs /\ getr r 18 = Z_to_bv 64 20 /\ getr r 2 = at_ S (-32) /\ getr r 8 = S
      /\ regs_agree (fun x => In x S2CLOB) r2 r.
  Proof using Hhint Hfsnz Hres Hfs Rhint Rlog Rgc Rfs HC_S0.
    intros r2 Q10 Q2 Q8. pose proof Hhint as Hh0. destruct Hfs as [Hf0 Hf1].
    pose proof (u64_range fs) as Hfr. pose proof (u64_range S) as HSr. pose proof (u64_range resw) as Hrr.
    wd_eexists. split.
    - cldz F_57188 D_57188 (U resw) fs Rfs.                    (* [comment removed for export] *)
      ab_ft F_5718c D_5718c ltac:(condz).                      (* [comment removed for export] *)
      clbu F_57190 D_57190 (U fs + 96)%Z Rgc.                  (* [comment removed for export] *)
      cldz F_57194 D_57194 (U fs + 88)%Z (Z_to_bv 64 20) Rlog. (* [comment removed for export] *)
      ab_tk F_57198 D_57198 ltac:(vals_lit; condz).            (* [comment removed for export] *)
      an F_571a8 D_571a8.                                      (* [comment removed for export] *)
      an F_571ac D_571ac.                                      (* [comment removed for export] *)
      an F_571b0 D_571b0.                                      (* [comment removed for export] *)
      an F_571b4 D_571b4.                                      (* [comment removed for export] *)
      ab_ft F_571b8 D_571b8 ltac:(vm_compute; reflexivity).    (* [comment removed for export] *)
      an F_571bc D_571bc.                                      (* [comment removed for export] *)
      an F_571c0 D_571c0.                                      (* [comment removed for export] *)
      cldz F_571c4 D_571c4 (U fs) (Z_to_bv 64 hint) Rhint.     (* [comment removed for export] *)
      an F_571c8 D_571c8.                                      (* [comment removed for export] *)
      an F_571cc D_571cc.                                      (* [comment removed for export] *)
      av F_571d0 D_571d0 (Z_to_bv 64 (U fs + 4096)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      an F_571d4 D_571d4.                                      (* [comment removed for export] *)
      an F_571d8 D_571d8.                                      (* [comment removed for export] *)
      an F_571dc D_571dc.                                      (* [comment removed for export] *)
      av F_571e0 D_571e0 (Z_to_bv 64 (hint + 16383)) ltac:(rewrite v_add_ZZ; reflexivity).  (* [comment removed for export] *)
      av F_571e4 D_571e4 (Z_to_bv 64 (hint + 16384)) ltac:(rewrite v_addi_Z; f_equal; lia). (* [comment removed for export] *)
      wd_refl.
    - post; try (apply bv_eq; vm_compute; reflexivity). (lazymatch goal with |- ?G => let G' := eval unfold S2CLOB in G in change_no_check G' end). ra_solve.
  Qed.

  Definition S3CLOB : list reg := [1; 9; 10; 12; 16; 18]%list.

  (* [comment removed for export] *)
  Lemma blkS3 : forall r4,
    getr r4 12 = Z_to_bv 64 (hint + i0) -> getr r4 15 = Z_to_bv 64 FLG -> getr r4 16 = Z_to_bv 64 (sk_pos hint i0) ->
    getr r4 11 = Z_to_bv 64 (U fs + 4096) -> getr r4 9 = fs -> getr r4 18 = Z_to_bv 64 20 -> getr r4 8 = S -> getr r4 2 = at_ S (-32) ->
    exists r,
      msteps segs (mkst r4 (at_ sb 252) m rom) (mkst r (at_ sb 1612) (sk0_mem4 m fs hint i0 S) rom)
      /\ getr r 10 = Z_to_bv 64 FRM /\ getr r 1 = at_ sb 304 /\ getr r 9 = Z_to_bv 64 FRM /\ getr r 2 = at_ S (-32)
      /\ regs_agree (fun x => In x S3CLOB) r4 r.
  Proof using Hhint Hfsnz Hfs OK56 OK24 OKf OKh HC_S0.
    intros r4 Q12 Q15 Q16 Q11 Q9 Q18 Q8 Q2. pose proof Hhint as Hh0. destruct Hfs as [Hf0 Hf1].
    pose proof (u64_range fs) as Hfr. pose proof (u64_range S) as HSr. pose proof (sk_pos_rng hint i0) as Hp.
    assert (HFL : (U fs + 4096 <= FLG < U fs + 20480)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold sk0_flag in G in change_no_check G' end); lia).
    assert (HFR : (U fs + 36864 <= FRM /\ FRM + 64 <= U fs + 1085440)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold sk0_frame in G in change_no_check G' end); lia).
    wd_eexists. split.
    - av F_57260 D_57260 (Z_to_bv 64 (hint + i0 + 1)) ltac:(rewrite v_addi_Z; reflexivity).   (* [comment removed for export] *)
      an F_57264 D_57264.                                      (* [comment removed for export] *)
      an F_57268 D_57268.                                      (* [comment removed for export] *)
      av F_5726c D_5726c (Z_to_bv 64 (sk_pos hint i0 * 64)) ltac:(rewrite v_slli_6 by lia; reflexivity).   (* [comment removed for export] *)
      wsd F_57270 D_57270 (U fs) OKh.                          (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sb_at with (a := Z_to_bv 64 FLG) (v := Z_to_bv 64 1) (b := Z_to_bv 8 1);
          [exact F_57274 | reflexivity | exact D_57274
          | gres; rwH; imm_norm; addr_eq
          | gres; rwH; reflexivity
          | apply bv_eq; vm_compute; reflexivity
          | repeat (eapply store_ok_mono; [apply wbytes_grows|]); exact OKf ]
        | step_simpl]; vn.                                       (* [comment removed for export] *)
      an F_57278 D_57278.                                      (* [comment removed for export] *)
      av F_5727c D_5727c (Z_to_bv 64 (U fs + 36864)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).    (* [comment removed for export] *)
      av F_57280 D_57280 (Z_to_bv 64 FRM) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add, sk0_frame in G in change_no_check G' end); unorm; f_equal; lia).     (* [comment removed for export] *)
      wsd F_57284 D_57284 (FRM + 24)%Z OK24.                   (* [comment removed for export] *)
      wsd F_57288 D_57288 (FRM + 56)%Z OK56.                   (* [comment removed for export] *)
      change (wbytes (wbytes (wbytes (wbytes m _ _) _ _) _ _) _ _) with (sk0_mem4 m fs hint i0 S).
      an F_5728c D_5728c.                                      (* [comment removed for export] *)
      an F_57290 D_57290.                                      (* [comment removed for export] *)
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold S3CLOB in G in change_no_check G' end). ra_solve.
  Qed.

  Definition S4CLOB : list reg := [1; 2; 8; 9; 18; 10; 11; 12]%list.

  (* [comment removed for export] *)
  Lemma blkS4 : forall r6,
    getr r6 10 = Z_to_bv 64 SHW -> getr r6 9 = Z_to_bv 64 FRM -> getr r6 2 = at_ S (-32) ->
    exists r,
      msteps segs (mkst r6 (at_ sb 304) (sk0_mem4 m fs hint i0 S) rom) (mkst r ra (sk0_mem m fs hint i0 S) rom)
      /\ getr r 10 = Z_to_bv 64 FRM /\ getr r 1 = ra /\ getr r 2 = S /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v
      /\ regs_agree (fun x => In x S4CLOB) r6 r.
  Proof using Hret Hhint Hfsnz Hfs FR4 FR3 FR2 FR1 OKsh HC_S0.
    intros r6 Q10 Q9 Q2. pose proof Hhint as Hh0. destruct Hfs as [Hf0 Hf1].
    pose proof (u64_range fs) as Hfr. pose proof (u64_range S) as HSr. pose proof (sk_pos_rng hint i0) as Hp.
    assert (HFL : (U fs + 4096 <= FLG < U fs + 20480)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold sk0_flag in G in change_no_check G' end); lia).
    assert (HFR : (U fs + 36864 <= FRM /\ FRM + 64 <= U fs + 1085440)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold sk0_frame in G in change_no_check G' end); lia).
    pose proof (sk0_sh_rng fs hint i0 ltac:(lia)) as HSH.
    wd_eexists. split.
    - an F_57294 D_57294.                                      (* [comment removed for export] *)
      an F_57298 D_57298.                                      (* [comment removed for export] *)
      an F_5729c D_5729c.                                      (* [comment removed for export] *)
      wsd F_572a0 D_572a0 (sk0_sh fs hint i0) OKsh.                            (* [comment removed for export] *)
      change (wbytes (sk0_mem4 m fs hint i0 S) _ _) with (sk0_mem m fs hint i0 S).
      fldm F_572a4 D_572a4 ra FR1.                             (* [comment removed for export] *)
      fldm F_572a8 D_572a8 s0v FR2.                            (* [comment removed for export] *)
      fldm F_572ac D_572ac s1v FR3.                            (* [comment removed for export] *)
      fldm F_572b0 D_572b0 s2v FR4.                            (* [comment removed for export] *)
      an F_572b4 D_572b4.                                      (* [comment removed for export] *)
      aret F_572b8 D_572b8 ra.                                 (* [comment removed for export] *)
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold S4CLOB in G in change_no_check G' end). ra_solve.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma PH4 : m2sH segs mt (sk0_mem4 m fs hint i0 S) (Z_to_bv 64 FRM) midend.
  Proof using Hfsnz Hfs Hmcells PHm sb.
    destruct Hfs as [Hf0 Hf1]. pose proof (u64_range fs) as Hfr. pose proof (u64_range S) as HSr. pose proof (sk_pos_rng hint i0) as Hp.
    assert (HFL : (U fs + 4096 <= FLG < U fs + 20480)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold sk0_flag in G in change_no_check G' end); lia).
    assert (HFR : (U fs + 36864 <= FRM /\ FRM + 64 <= U fs + 1085440)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold sk0_frame in G in change_no_check G' end); lia).
    pose proof Hmcells as HC. unfold m2s_cells in HC.
    repeat match type of HC with Forall _ (_ :: _) => apply Forall_cons_iff in HC; destruct HC as [? HC] end.
    destruct PHm as [R1 R2 R3 R4 R5 R6 R7 R8 HCx Hlo Hhi].
    constructor; try assumption; (lazymatch goal with |- ?G => let G' := eval unfold sk0_mem4 in G in change_no_check G' end);
      (repeat (rewrite wd_rdn_wbytes_out3; [ | rd8_side ])); assumption.
  Qed.

  Definition SBCLOB : list reg := [1; 2; 5; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18]%list.
  Lemma SB_sub2 : forall x : reg, In x S2CLOB -> In x SBCLOB. Proof using. (lazymatch goal with |- ?G => let G' := eval unfold S2CLOB, SBCLOB in G in change_no_check G' end). incl_lists. Qed.
  Lemma SB_subL : forall x : reg, In x LCLOB -> In x SBCLOB. Proof using. (lazymatch goal with |- ?G => let G' := eval unfold LCLOB, SBCLOB in G in change_no_check G' end). incl_lists. Qed.
  Lemma SB_sub3 : forall x : reg, In x S3CLOB -> In x SBCLOB. Proof using. (lazymatch goal with |- ?G => let G' := eval unfold S3CLOB, SBCLOB in G in change_no_check G' end). incl_lists. Qed.
  Lemma SB_subM : forall x : reg, In x m2s_clob -> In x SBCLOB. Proof using. (lazymatch goal with |- ?G => let G' := eval unfold m2s_clob, SBCLOB in G in change_no_check G' end). incl_lists. Qed.
  Lemma SB_sub4 : forall x : reg, In x S4CLOB -> In x SBCLOB. Proof using. (lazymatch goal with |- ?G => let G' := eval unfold S4CLOB, SBCLOB in G in change_no_check G' end). incl_lists. Qed.

  Theorem stk0B_run : forall r2,
    getr r2 10 = resw -> getr r2 2 = at_ S (-32) -> getr r2 8 = S ->
    exists r,
      msteps segs (mkst r2 (at_ sb 36) m rom) (mkst r ra (sk0_mem m fs hint i0 S) rom)
      /\ getr r 10 = Z_to_bv 64 FRM /\ getr r 1 = ra /\ getr r 2 = S /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v
      /\ regs_agree (fun x => In x SBCLOB) r2 r.
  Proof using Hret Hi0 Hhint Hfsnz Hres Hfs FR4 FR3 FR2 FR1 Hmcells PHm OKsh OK56 OK24 OKf OKh Hz Hnz Rhint Rlog Rgc Rfs midend Hsb MTB MTOK HC_S0 mt.
    intros r2 Q10 Q2 Q8. destruct Hsb as [Hb2 Hb64]. pose proof (u64_range sb) as Hsbr.
    assert (RT304 : ret_ok (at_ sb 304)) by (apply ret_ok_at; [exact Hb2 | reflexivity | lia]).
    destruct (blkS2 r2 Q10 Q2 Q8) as (r3 & RUN3 & A10 & A12 & A11 & A13 & A9 & A18 & A2 & A8 & AG3).
    destruct (sk0_loop (Z.to_nat i0) 0%Z r3 ltac:(lia) ltac:(lia) A10 A12 A11 A13) as (r4 & RUN4 & B12 & B15 & B16 & AG4).
    assert (B11 : getr r4 11 = Z_to_bv 64 (U fs + 4096)) by (rewrite (AG4 11 ltac:((lazymatch goal with |- ?G => let G' := eval unfold LCLOB in G in change_no_check G' end); notin)); exact A11).
    assert (B9 : getr r4 9 = fs) by (rewrite (AG4 9 ltac:((lazymatch goal with |- ?G => let G' := eval unfold LCLOB in G in change_no_check G' end); notin)); exact A9).
    assert (B18 : getr r4 18 = Z_to_bv 64 20) by (rewrite (AG4 18 ltac:((lazymatch goal with |- ?G => let G' := eval unfold LCLOB in G in change_no_check G' end); notin)); exact A18).
    assert (B8 : getr r4 8 = S) by (rewrite (AG4 8 ltac:((lazymatch goal with |- ?G => let G' := eval unfold LCLOB in G in change_no_check G' end); notin)); exact A8).
    assert (B2 : getr r4 2 = at_ S (-32)) by (rewrite (AG4 2 ltac:((lazymatch goal with |- ?G => let G' := eval unfold LCLOB in G in change_no_check G' end); notin)); exact A2).
    destruct (blkS3 r4 B12 B15 B16 B11 B9 B18 B8 B2) as (r5 & RUN5 & C10 & C1 & C9 & C2 & AG5).
    destruct (m2s_run segs mt MTOK (sk0_mem4 m fs hint i0 S) rom (Z_to_bv 64 FRM) midend (at_ sb 304) r5 PH4 C10 C1 RT304)
      as (r6 & RUN6 & D10 & AG6).
    assert (UF : U (Z_to_bv 64 FRM) = FRM).
    { destruct Hfs as [Hf0 Hf1]. pose proof (u64_range fs). pose proof (u64_range S). pose proof (sk_pos_rng hint i0). (lazymatch goal with |- ?G => let G' := eval unfold sk0_frame in G in change_no_check G' end). rewrite u_Z2bv; lia. }
    rewrite UF in D10. change (Z_to_bv 64 (FRM / 8 + 2147450880)) with (Z_to_bv 64 SHW) in D10.
    assert (D9 : getr r6 9 = Z_to_bv 64 FRM) by (rewrite (AG6 9 ltac:((lazymatch goal with |- ?G => let G' := eval unfold m2s_clob in G in change_no_check G' end); notin)); exact C9).
    assert (D2 : getr r6 2 = at_ S (-32)) by (rewrite (AG6 2 ltac:((lazymatch goal with |- ?G => let G' := eval unfold m2s_clob in G in change_no_check G' end); notin)); exact C2).
    destruct (blkS4 r6 D10 D9 D2) as (r7 & RUN7 & E10 & E1 & E2 & E8 & E9 & E18 & AG7).
    exists r7. split.
    - rewrite MTB in RUN6.
      eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|].
      eapply msteps_trans; [exact RUN6 | exact RUN7].
    - repeat (split; [assumption|]).
      eapply regs_agree_trans; [eapply regs_agree_trans; [eapply regs_agree_trans; [eapply regs_agree_trans|]|]|].
      + exact (regs_agree_mono _ _ _ _ SB_sub2 AG3).
      + exact (regs_agree_mono _ _ _ _ SB_subL AG4).
      + exact (regs_agree_mono _ _ _ _ SB_sub3 AG5).
      + exact (regs_agree_mono _ _ _ _ SB_subM AG6).
      + exact (regs_agree_mono _ _ _ _ SB_sub4 AG7).
  Qed.
End STK0B.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section STK0.
  Variables (segs : list Segment) (sb : word).
  Variable tg : tlsga_tab.
  Variable mt : m2s_tab.
  Variable c_arg : word.
  Hypothesis HC_S0 : code_ato segs sb 0 stk0_words.
  Hypothesis TGOK : tlsga_tab_ok segs tg.
  Hypothesis TGHB : tg_hb tg = at_ sb 21448.
  Hypothesis MTOK : m2s_tab_ok segs mt.
  Hypothesis MTB : mt_base mt = at_ sb 1612.
  Hypothesis A24 : gaddr2 segs sb 24 10 10 c_arg.              (* [comment removed for export] *)
  Hypothesis Hsb : (U sb mod 2 = 0)%Z /\ (U sb + 30000 < 2 ^ 64)%Z.

  Variable mem : word -> option byte.
  Variable rom : word -> option byte.
  Variables (ra S fs midend : word).
  Variable v : tlsga_vals.
  Variables (hint i0 : Z).
  #[local] Abbreviation FLG := (sk0_flag fs hint i0).
  #[local] Abbreviation FRM := (sk0_frame fs hint i0).
  #[local] Abbreviation SHW := (sk0_sh fs hint i0).
  Hypothesis TGH : tlsgaH segs tg mem (at_ S (-32)) v.
  Hypothesis Harg : tv_arg v = c_arg.
  Hypothesis Rfs : rdn segs mem (Z_to_bv 64 (U (tg_res v))) 8 = Some (W8 fs).
  Hypothesis Hres : (U (tg_res v) <> 0)%Z /\ (U (tg_res v) + 8 <= U S - 208)%Z.
  Hypothesis Rgc : rdn segs mem (Z_to_bv 64 (U fs + 96)) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rlog : rdn segs mem (Z_to_bv 64 (U fs + 88)) 8 = Some (LE8 20).
  Hypothesis Rhint : rdn segs mem (Z_to_bv 64 (U fs)) 8 = Some (LE8 hint).
  Hypothesis Hnz : forall j, (0 <= j < i0)%Z -> exists b : byte, rdn segs mem (Z_to_bv 64 (sk0_flag fs hint j)) 1 = Some [b] /\ U b <> 0%Z.
  Hypothesis Hz : rdn segs mem (Z_to_bv 64 FLG) 1 = Some [Z_to_bv 8 0].
  Hypothesis OKh : store_ok segs mem (Z_to_bv 64 (U fs)) 8 = true.
  Hypothesis OKf : store_ok segs mem (Z_to_bv 64 FLG) 1 = true.
  Hypothesis OK24 : store_ok segs mem (Z_to_bv 64 (FRM + 24)) 8 = true.
  Hypothesis OK56 : store_ok segs mem (Z_to_bv 64 (FRM + 56)) 8 = true.
  Hypothesis OKsh : store_ok segs mem (Z_to_bv 64 SHW) 8 = true.
  Hypothesis PH : m2sH segs mt mem (Z_to_bv 64 FRM) midend.
  Hypothesis Hmcells : Forall (fun c => 0 <= c /\ c + 8 <= U fs)%Z (m2s_cells mt).
  (* [comment removed for export] *)
  Hypothesis Hfs : (0 < U fs /\ U fs + 1085440 <= 2 ^ 47 /\ 0x10007fff8000 + 208 <= U S)%Z /\ (U fs + 1085440 <= U S - 208)%Z.
  Hypothesis Hhint : (0 <= hint)%Z.
  Hypothesis Hi0 : (0 <= i0 < 16384)%Z.
  Hypothesis HS : (208 <= U S)%Z.
  Hypothesis Hstk : store_ok segs mem (at_ S (-32)) 32 = true.
  Hypothesis Hret : ret_ok ra.

  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = S.
  Hypothesis H4 : getr regs 4 = tv_tp v.

  #[local] Abbreviation M1 := (fl_frame mem S ra (getr regs 8) (getr regs 9) (getr regs 18)).

  Ltac fsd F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | repeat (eapply store_ok_mono; [apply wbytes_grows|]);
          eapply (store_ok_sub segs mem (at_ S (-32)) _ 32);
          [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia] ]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  Lemma blkS1 :
    exists r,
      msteps segs (mkst regs (at_ sb 0) mem rom) (mkst r (at_ sb 21448) M1 rom)
      /\ getr r 10 = c_arg /\ getr r 1 = at_ sb 36 /\ getr r 2 = at_ S (-32) /\ getr r 8 = S /\ getr r 4 = tv_tp v
      /\ regs_agree (fun x => In x [1; 2; 8; 10]%list) regs r.
  Proof using H4 H2 H1 Hstk Hfs fs Hsb A24 HC_S0.
    pose proof (u64_range S) as HSr. destruct Hsb as [Hb2 Hb64]. destruct A24 as [x24 AX].
    wd_eexists. split.
    - an (F_57164 segs sb HC_S0) D_57164.                      (* [comment removed for export] *)
      fsd (F_57168 segs sb HC_S0) D_57168 (at_ S (-8)).       (* [comment removed for export] *)
      fsd (F_5716c segs sb HC_S0) D_5716c (at_ S (-16)).      (* [comment removed for export] *)
      fsd (F_57170 segs sb HC_S0) D_57170 (at_ S (-24)).      (* [comment removed for export] *)
      fsd (F_57174 segs sb HC_S0) D_57174 (at_ S (-32)).      (* [comment removed for export] *)
      change (wbytes _ _ _) with M1.
      an (F_57178 segs sb HC_S0) D_57178.                      (* [comment removed for export] *)
      eapply msteps_trans; [eapply AX|]; zlit_at.              (* [comment removed for export] *)
      an (F_57184 segs sb HC_S0) D_57184.                      (* [comment removed for export] *)
      wd_refl.
    - post; rewrite ?at_0; try reflexivity. ra_solve.
  Qed.

  Theorem stk0_run :
    exists r Mj,
      msteps segs (mkst regs (at_ sb 0) mem rom) (mkst r ra (sk0_mem Mj fs hint i0 S) rom)
      /\ scr_rel mem Mj (U S - 208) (U S)
      /\ getr r 10 = Z_to_bv 64 FRM /\ getr r 1 = ra /\ getr r 2 = S
      /\ regs_agree (fun x => In x m2s_clob) regs r.
  Proof using H4 H2 H1 Hret Hstk Hi0 Hhint Hfs Hmcells PH OKsh OK56 OK24 OKf OKh Hz Hnz Rhint Rlog Rgc Hres Rfs Harg TGH v midend Hsb A24 MTB MTOK TGHB TGOK HC_S0 c_arg mt tg.
    pose proof (u64_range S) as HSr. destruct Hsb as [Hb2 Hb64]. pose proof (u64_range sb) as Hsbr.
    destruct Hfs as [Hf0 Hf1]. destruct Hres as [Hr0 Hr1]. pose proof (u64_range fs) as Hfr. pose proof (u64_range (tg_res v)) as Hrr.
    pose proof (sk_pos_rng hint i0) as Hp.
    assert (RT36 : ret_ok (at_ sb 36)) by (apply ret_ok_at; [exact Hb2 | reflexivity | lia]).
    assert (US32 : U (at_ S (-32)) = (U S - 32)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    destruct blkS1 as (r1 & RUN1 & A10 & A1 & A2 & A8 & A4 & AG1).
    (* [comment removed for export] *)
    assert (TGH1 : tlsgaH segs tg M1 (at_ S (-32)) v).
    { apply (tlsgaH_above segs tg mem M1 (at_ S (-32)) v TGH); [apply fl_frame_grows|].
      intros a Ha. apply fl_frame_out; [lia | rewrite US32 in Ha; lia]. }
    rewrite <- Harg in A10.
    destruct (tlsga_run_t segs tg TGOK M1 rom (at_ sb 36) (at_ S (-32)) v r1 TGH1 RT36 A1 A2 A4 A10)
      as (r2 & Mj & RUN2 & SR & B10 & B1 & B2 & AG2).
    rewrite US32 in SR.
    assert (B8 : getr r2 8 = S) by (rewrite (AG2 8 ltac:(notin)); exact A8).
    (* [comment removed for export] *)
    assert (RDJ : forall c n bs, (0 <= c)%Z -> (c + Z.of_nat n <= U S - 208)%Z ->
                  rdn segs mem (Z_to_bv 64 c) n = Some bs -> rdn segs Mj (Z_to_bv 64 c) n = Some bs).
    { intros c n bs Hc0 Hc Hr.
      apply (scr_rel_rdn segs M1 Mj (U S - 32 - 176) (U S - 32) c n bs SR); [lia | lia | left; lia|].
      apply rd_fl_frame; [lia | lia | lia | exact Hr]. }
    assert (OKJ : forall (a : word) n, store_ok segs mem a n = true -> store_ok segs Mj a n = true).
    { intros a n OK. apply (scr_rel_ok segs M1 Mj _ _ a n SR). apply fl_frame_ok. exact OK. }
    assert (HFL : forall j, (U fs + 4096 <= sk0_flag fs hint j < U fs + 20480)%Z) by (intros j; pose proof (sk_pos_rng hint j); (lazymatch goal with |- ?G => let G' := eval unfold sk0_flag in G in change_no_check G' end); lia).
    assert (HFR : (U fs + 36864 <= FRM /\ FRM + 64 <= U fs + 1085440)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold sk0_frame in G in change_no_check G' end); lia).
    assert (SLOT : forall k vv, (k = 8 \/ k = 16 \/ k = 24 \/ k = 32)%Z ->
                   rdn segs M1 (at_ S (- k)) 8 = Some (W8 vv) -> rdn segs Mj (at_ S (- k)) 8 = Some (W8 vv)).
    { intros k vv Hk Hr. destruct SR as (O & _ & _).
      rewrite (rdn_ext segs 8 Mj M1 (at_ S (- k))); [exact Hr | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | rewrite at_u by lia; intros x Hx; apply O; lia]. }
    assert (PHJ : m2sH segs mt Mj (Z_to_bv 64 FRM) midend).
    { pose proof Hmcells as HC. unfold m2s_cells in HC.
      repeat match type of HC with Forall _ (_ :: _) => apply Forall_cons_iff in HC; destruct HC as [? HC] end.
      destruct PH as [R1 R2 R3 R4 R5 R6 R7 R8 HCx Hlo Hhi].
      constructor; try assumption; apply RDJ; try assumption; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia. }
    destruct (stk0B_run segs sb mt HC_S0 MTOK MTB (conj Hb2 Hb64) Mj rom ra S (tg_res v) fs midend (getr regs 8) (getr regs 9) (getr regs 18) hint i0)
      with (r2 := r2) as (r & RUN3 & E10 & E1 & E2 & E8 & E9 & E18 & AG3).
    { apply RDJ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Rfs]. }
    { apply RDJ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Rgc]. }
    { apply RDJ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Rlog]. }
    { apply RDJ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Rhint]. }
    { intros j Hj. destruct (Hnz j Hj) as (b & Rb & Nb). exists b. split; [|exact Nb].
      pose proof (HFL j). apply RDJ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Rb]. }
    { pose proof (HFL i0). apply RDJ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Hz]. }
    { apply OKJ; exact OKh. } { apply OKJ; exact OKf. } { apply OKJ; exact OK24. } { apply OKJ; exact OK56. } { apply OKJ; exact OKsh. }
    { exact PHJ. }
    { exact Hmcells. }
    { apply (SLOT 8%Z ra); [lia|]. (lazymatch goal with |- ?G => let G' := eval unfold fl_frame in G in change_no_check G' end). rd8_chain. }
    { apply (SLOT 16%Z (getr regs 8)); [lia|]. (lazymatch goal with |- ?G => let G' := eval unfold fl_frame in G in change_no_check G' end). rd8_chain. }
    { apply (SLOT 24%Z (getr regs 9)); [lia|]. (lazymatch goal with |- ?G => let G' := eval unfold fl_frame in G in change_no_check G' end). rd8_chain. }
    { apply (SLOT 32%Z (getr regs 18)); [lia|]. (lazymatch goal with |- ?G => let G' := eval unfold fl_frame in G in change_no_check G' end). rd8_chain. }
    { split; lia. }
    { exact Hr0. }
    { lia. }
    { exact Hhint. }
    { exact Hi0. }
    { exact Hret. }
    { exact B10. }
    { exact B2. }
    { exact B8. }
    exists r, Mj. split; [|split; [|split; [exact E10 | split; [exact E1 | split; [exact E2|]]]]].
    - rewrite TGHB in RUN2. eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2 | exact RUN3].
    - (* [comment removed for export] *)
      apply (scr_rel_trans mem M1 Mj).
      + (lazymatch goal with |- ?G => let G' := eval unfold fl_frame in G in change_no_check G' end).
        repeat (apply scr_rel_wb; [ | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ] | wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); lia | lia ]).
        apply scr_rel_refl.
      + apply (scr_rel_mono M1 Mj _ _ _ _ SR); lia.
    - intros x Hx.
      destruct (In_dec (fun a b : reg => decide (a = b)) x [1; 2; 8; 9; 18]%list) as [I|NI].
      + cbn [In] in I.
        repeat (destruct I as [<-|I]; [first [rewrite E1; symmetry; exact H1 | rewrite E2; symmetry; exact H2 | exact E8 | exact E9 | exact E18] |]).
        destruct I.
      + assert (NB : ~ In x SBCLOB).
        { intros I. unfold SBCLOB in I. unfold m2s_clob in Hx. cbn [In] in I, NI, Hx. am_tauto. }
        rewrite (AG3 x NB). rewrite (AG2 x). 2:{ intros I. unfold m2s_clob in Hx. cbn [In] in I, Hx. am_tauto. }
        apply AG1. intros I. unfold m2s_clob in Hx. cbn [In] in I, NI, Hx. am_tauto.
  Qed.
End STK0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record stk_tab := SKT { sk_base : word; sk_tg : tlsga_tab; sk_mt : m2s_tab; sk_arg : word }.

Definition stk0_tab_ok (segs : list Segment) (t : stk_tab) : Prop :=
  code_ato segs (sk_base t) 0 stk0_words
  /\ tlsga_tab_ok segs (sk_tg t) /\ tg_hb (sk_tg t) = at_ (sk_base t) 21448
  /\ m2s_tab_ok segs (sk_mt t) /\ mt_base (sk_mt t) = at_ (sk_base t) 1612
  /\ gaddr2 segs (sk_base t) 24 10 10 (sk_arg t)
  /\ ((U (sk_base t) mod 2 = 0)%Z /\ (U (sk_base t) + 30000 < 2 ^ 64)%Z).

(* [comment removed for export] *)
Record stk0H (segs : list Segment) (t : stk_tab) (mem : word -> option byte) (S fs midend : word) (v : tlsga_vals) (hint i0 : Z) : Prop := SK0H {
  s0h_tls : tlsgaH segs (sk_tg t) mem (at_ S (-32)) v;
  s0h_arg : tv_arg v = sk_arg t;
  s0h_fs : rdn segs mem (Z_to_bv 64 (U (tg_res v))) 8 = Some (W8 fs);
  s0h_res : (U (tg_res v) <> 0)%Z /\ (U (tg_res v) + 8 <= U S - 208)%Z;
  s0h_gc : rdn segs mem (Z_to_bv 64 (U fs + 96)) 1 = Some [Z_to_bv 8 0];
  s0h_log : rdn segs mem (Z_to_bv 64 (U fs + 88)) 8 = Some (LE8 20);
  s0h_hint : rdn segs mem (Z_to_bv 64 (U fs)) 8 = Some (LE8 hint);
  s0h_busy : forall j, (0 <= j < i0)%Z -> exists b : byte, rdn segs mem (Z_to_bv 64 (sk0_flag fs hint j)) 1 = Some [b] /\ U b <> 0%Z;
  s0h_free : rdn segs mem (Z_to_bv 64 (sk0_flag fs hint i0)) 1 = Some [Z_to_bv 8 0];
  s0h_ok_hint : store_ok segs mem (Z_to_bv 64 (U fs)) 8 = true;
  s0h_ok_flag : store_ok segs mem (Z_to_bv 64 (sk0_flag fs hint i0)) 1 = true;
  s0h_ok_24 : store_ok segs mem (Z_to_bv 64 (sk0_frame fs hint i0 + 24)) 8 = true;
  s0h_ok_56 : store_ok segs mem (Z_to_bv 64 (sk0_frame fs hint i0 + 56)) 8 = true;
  s0h_ok_sh : store_ok segs mem (Z_to_bv 64 (sk0_sh fs hint i0)) 8 = true;
  s0h_m2s : m2sH segs (sk_mt t) mem (Z_to_bv 64 (sk0_frame fs hint i0)) midend;
  s0h_mcells : Forall (fun c => 0 <= c /\ c + 8 <= U fs)%Z (m2s_cells (sk_mt t));
  s0h_geom : (0 < U fs /\ U fs + 1085440 <= 2 ^ 47 /\ 0x10007fff8000 + 208 <= U S)%Z /\ (U fs + 1085440 <= U S - 208)%Z;
  s0h_hintr : (0 <= hint)%Z;
  s0h_i0 : (0 <= i0 < 16384)%Z;
  s0h_S : (208 <= U S)%Z;
  s0h_stk : store_ok segs mem (at_ S (-32)) 32 = true }.

Theorem stk0_run_t : forall segs t, stk0_tab_ok segs t ->
  forall mem rom (ra S fs midend : word) v hint i0 regs,
  stk0H segs t mem S fs midend v hint i0 -> ret_ok ra ->
  getr regs 1 = ra -> getr regs 2 = S -> getr regs 4 = tv_tp v ->
  exists r Mj,
    msteps segs (mkst regs (sk_base t) mem rom) (mkst r ra (sk0_mem Mj fs hint i0 S) rom)
    /\ scr_rel mem Mj (U S - 208) (U S)
    /\ getr r 10 = Z_to_bv 64 (sk0_frame fs hint i0) /\ getr r 1 = ra /\ getr r 2 = S
    /\ regs_agree (fun x => In x m2s_clob) regs r.
Proof using.
  intros segs t (C1 & TG & TGB & MT & MTB & A24 & HB) mem rom ra S fs midend v hint i0 regs
         [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20 P21] Hret H1 H2 H4.
  replace (mkst regs (sk_base t) mem rom) with (mkst regs (at_ (sk_base t) 0) mem rom) by (rewrite at_0; reflexivity).
  first [ exact (stk0_run segs (sk_base t) (sk_tg t) (sk_mt t) (sk_arg t) C1 TG TGB MT MTB A24 HB mem rom ra S fs midend v hint i0
           P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20 P21 Hret regs H1 H2 H4)
        | exact (stk0_run segs (sk_base t) (sk_tg t) (sk_mt t) (sk_arg t) C1 TG TGB MT MTB A24 HB mem rom ra S fs midend v hint i0
           P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P21 Hret regs H1 H2 H4) ].
Qed.
End FPGen1.
