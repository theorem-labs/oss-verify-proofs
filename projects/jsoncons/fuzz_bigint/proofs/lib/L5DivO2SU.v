(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface
     BigModel BigFactsBase BigFactsOps L5Defs L5Core L5CoreSpecsU L5Words L5WordsB L5ShlU L5MulMU L5NormU L5DivSpecsU.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nra Cache. Unset Nia Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5DO2SU.
Import L5CSU. Import L5DSU. Import L5W.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
Definition DIVO2_SCR : Z := 352 + UNNORM_SCR.
(* [comment removed for export] *)
Definition DIVO2_K : Z := 11.
Definition divO2_bytes (capy : Z) : Z := 24 * capy + 768.

(* [comment removed for export] *)
Definition q_after (L : heap_layout) (LBy : list (Z * Z)) (M' : word -> option byte) (Q : Z) (LB' : list (Z * Z)) : Prop :=
  exists fbq nq stq, L5.big_at RSEGS M' Q (L5.BO fbq nq stq) /\
    match stq with
    | L5.BInl _ _ => LB' = LBy
    | L5.BDyn cap q => LB' = (q, 8 * cap) :: LBy /\ L5C.fresh_block L LBy M' q (8 * cap) /\ cap <= 300
    end.

Section DivO2.
Variable L : heap_layout.
Variable HI : heap_iface.

Definition divO2_post (LB : list (Z * Z)) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (Y Q A fba sp : Z) (by_ : L5.bigobj) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  regs_preserved R R'
  /\ (exists LBy, y_after L LB M M' Y by_ LBy /\ q_after L LBy M' Q LB')
  /\ a_ok M' A fba
  /\ credit_after L cr DIVO2_K (divO2_bytes (L5.bo_cap by_)) cr'
  /\ L5C.hpres L LB sp DIVO2_SCR [(Y, 32); (L5.bo_data Y by_, 8 * L5.bo_cap by_); (Q, 32)] M M'.

(* [comment removed for export] *)
Definition divO2_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (Y Q A fba sp r : Z) (by_ : L5.bigobj) (wy : list Z),
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 Y -> getr R 11%bv = Z_to_bv 64 A -> getr R 12%bv = Z_to_bv 64 Q -> getr R 13%bv = Z_to_bv 64 Y ->
    getr R 14%bv = Z_to_bv 64 1 ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 3%bv = Z_to_bv 64 GP -> getr R 4%bv = Z_to_bv 64 TP -> L5C.stk (hl_sptop L) M sp DIVO2_SCR ->
    L5.img_clear M 0x10000 0x20000 ->
    (* [comment removed for export] *)
    y_ok LB M Y by_ wy -> (1 <= L5.bo_len by_)%nat -> L5.bo_cap by_ <= 268 ->
    Y mod 8 = 0 -> sp + 48 <= Y -> Y + 32 <= hl_sptop L -> L5.writable RSEGS M Y 32 ->
    (forall cap q, L5.bo_st by_ = L5.BDyn cap q -> L5.writable RSEGS M q (8 * cap)) ->
    (* [comment removed for export] *)
    a_ok M A fba -> A mod 8 = 0 -> sp + 48 <= A -> A + 32 <= hl_sptop L ->
    zero_obj M Q -> Q mod 8 = 0 -> sp <= Q -> Q + 32 <= hl_sptop L -> L5.writable RSEGS M Q 32 ->
    (Y + 32 <= A \/ A + 32 <= Y) -> Q + 32 <= Y -> Q + 32 <= A ->
    credit_for L cr DIVO2_K (divO2_bytes (L5.bo_cap by_)) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
        divO2_post LB cr M M' R R' Y Q A fba sp by_ LB' cr' ->
        model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R DIVIDE M model) K.
End DivO2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition WA : list Z := [A0; A1].
(* [comment removed for export] *)
Definition D0 : Z := 0x5abe7036bc514e54.
Definition D1 : Z := 0xaa7cd8d89cf2abc8.
Definition DA : list Z := [D0; D1; 0].

Lemma log2_A1 : Z.log2 A1 = 61. Proof. vm_compute. reflexivity. Qed.
Lemma clz_A1 : L5NORMU.clz_of (nth_w WA 1) = 2. Proof. unfold L5NORMU.clz_of. cbn [nth_w WA nth]. rewrite log2_A1. reflexivity. Qed.
Lemma A1_top : nth_w WA 1 <> 0 /\ nth_w WA 1 < 2 ^ 63. Proof. cbn [nth_w WA nth]. unfold A1. lia. Qed.
Lemma WA_ok : words_ok WA. Proof. unfold words_ok, WA, A0, A1. repeat constructor; lia. Qed.
Lemma shl_WA : L5SHLU.shl_result WA 2 = DA. Proof. vm_compute. reflexivity. Qed.
Lemma rlen_DA : rlen DA = 2%nat. Proof. vm_compute. reflexivity. Qed.
Lemma length_DA : length DA = 3%nat. Proof. reflexivity. Qed.
Lemma second_DA : L5NORMU.second 2 DA = false. Proof. vm_compute. reflexivity. Qed.
Lemma second_WA : L5NORMU.second 2 (L5SHLU.shl_result WA (L5NORMU.clz_of (nth_w WA 1))) = false.
Proof. rewrite clz_A1, shl_WA. apply second_DA. Qed.
Lemma norm_words_WA : L5NORMU.norm_words WA 2 false = DA. Proof. unfold L5NORMU.norm_words. rewrite shl_WA. reflexivity. Qed.
Lemma D1_range : 2 ^ 63 <= D1 < 2 ^ 64 /\ 4 <= D1. Proof. unfold D1. lia. Qed.
Lemma DA_1 : nth_w DA 1 = D1. Proof. reflexivity. Qed.
Lemma DA_0 : nth_w DA 0 = D0. Proof. reflexivity. Qed.
Lemma D0_range : 0 <= D0 < 2 ^ 64. Proof. unfold D0. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma shl_top_small ws k : words_ok ws -> (1 <= length ws)%nat -> 0 < k < 64 ->
  0 <= nth_w (shl_words ws k) (length ws) < 2 ^ k.
Proof.
  intros W L Hk. rewrite shl_words_nth by lia.
  assert (WO: BigFactsBase.words_ok (ws ++ [0])). { apply (proj1 (words_ok_BF _)). apply words_ok_app. exact W. constructor. lia. constructor. }
  destruct (BigFactsOps.shlG_val k Hk (ws ++ [0]) (length ws) WO) as [E _]. rewrite E.
  assert (NL: BigModel.nth_w (ws ++ [0]) (length ws) = 0).
  { unfold BigModel.nth_w. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. }
  rewrite NL. unfold BigModel.W.shl, BigModel.W.wrap. rewrite Z.mul_0_l, Z.mod_0_l by (pose proof BigFactsBase.M_pos; lia).
  destruct (Nat.ltb_spec 0 (length ws)). 2: lia.
  assert (WL: 0 <= BigModel.nth_w (ws ++ [0]) (length ws - 1) < 2 ^ 64).
  { unfold BigModel.nth_w. rewrite app_nth1 by lia. apply (words_ok_nth ws). exact W. }
  split. apply Z.add_nonneg_nonneg. lia. apply Z.div_pos. lia. apply Z.pow_pos_nonneg; lia.
  rewrite Z.add_0_l. apply Z.div_lt_upper_bound. apply Z.pow_pos_nonneg; lia.
  rewrite <- Z.pow_add_r by lia. replace (64 - k + k) with 64 by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma rlen_shl_bounds ws k : words_ok ws -> (1 <= length ws)%nat -> nth_w ws (length ws - 1) <> 0 -> 0 < k < 64 ->
  (length ws <= rlen (shl_words ws k) <= S (length ws))%nat.
Proof.
  intros W L T Hk. split.
  - assert (RL: rlen ws = length ws). { apply rlen_charact. lia. intros i Hi. lia. right. exact T. }
    rewrite <- RL at 1. apply L5WB.rlen_mono. exact W. apply shl_words_ok. exact Hk. exact W.
    rewrite shl_words_val by assumption. pose proof (BigFactsBase.val_nonneg ws (proj1 (words_ok_BF _) W)).
    assert (1 <= 2 ^ k). { change 1 with (2 ^ 0). apply Z.pow_le_mono_r; lia. } nia.
  - rewrite <- (shl_words_length ws k). apply rlen_le.
Qed.

(* [comment removed for export] *)
Lemma shl_grown_top ws k : words_ok ws -> (1 <= length ws)%nat -> 0 < k < 64 ->
  rlen (shl_words ws k) = S (length ws) -> nth_w (shl_words ws k) (rlen (shl_words ws k) - 1) < 2 ^ k.
Proof. intros W L Hk E. rewrite E. replace (S (length ws) - 1)%nat with (length ws) by lia. apply shl_top_small; assumption. Qed.

End SCFG_1.
End L5DO2SU.
