(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac Arr ZBridge WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzLemmasHb. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Ltac flagsb := zb_masks; decide_tests; cbn [Z.b2z]; zb_fold_lits.
(* [comment removed for export] *)
Ltac zify_cond_z K := zify_cond K; bz32_in K.

(* [comment removed for export] *)
Ltac u32_store_done ARR i :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?mm _ (le4 ?v)) _) =>
      lazymatch type of ARR with u32arr _ _ ?A ?ws =>
        let H := fresh "ARR" in
        pose proof (u32arr_write segs mm A ws i v ARR ltac:(lia)) as H; clear ARR; store_done; rename H into ARR
      end
  end.
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Lemma u8arr_write_le1 : forall segs m A bs (i : Z) (x : word),
  u8arr segs m A bs -> (0 <= i < Z.of_nat (length bs))%Z ->
  u8arr segs (write_to_mem m (wa (A + i)) (le1 x)) A (upd bs (Z.to_nat i) (Z_to_bv 8 (bv_unsigned x mod 256))).
Proof.
  intros segs m A bs i x ARR Hi.
  replace (le1 x) with [Z_to_bv 8 (bv_unsigned x mod 256)%Z].
  - apply u8arr_write; assumption.
  - unfold le1. cbn. f_equal. apply Z_to_bv8_mod. rewrite Z.mod_mod by lia. reflexivity.
Qed.
End ACeilS1.


Ltac u8_store_done ARR i :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?mm _ (le1 ?x)) _) =>
      lazymatch type of ARR with u8arr _ _ ?A ?bs =>
        let H := fresh "ARR" in
        pose proof (u8arr_write_le1 segs mm A bs i x ARR ltac:(lia)) as H; clear ARR; store_done; rename H into ARR
      end
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?mm _ [?b]) _) =>
      lazymatch type of ARR with u8arr _ _ ?A ?bs =>
        let H := fresh "ARR" in
        pose proof (u8arr_write segs mm A bs i b ARR ltac:(lia)) as H; clear ARR; store_done; rename H into ARR
      end
  end.

(* [comment removed for export] *)
Ltac u32_read ARR LEN i w NTH RD :=
  lazymatch type of ARR with u32arr ?segs ?m ?A ?ws =>
    destruct (nth_error_ok ws i _ LEN ltac:(lia)) as [w NTH];
    pose proof (u32arr_read segs m A ws i w _ ARR NTH ltac:(lia) eq_refl) as RD
  end.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section ACeilS2. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End ACeilS2.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Musl Require Import MuslStr.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes.
Section ACeilS3. Context {ACEIL__ : ACeil}.


Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes, le_bytes_to_word.
  rewrite Z_to_bv_unsigned.
  assert (R : (0 <= bytes_le_to_Z bs < 2^64)%Z).
  { rewrite bytes_le_to_Z_le_val. pose proof (le_val_range _ (bytes_ok_map bs)) as X.
    rewrite length_map, L in X. change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in X. lia. }
  unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z. rewrite Z.mod_small by lia.
  rewrite <- L. apply Z_to_le_bytes_to_Z.
Qed.

Fixpoint c8cells (k : nat) (bs : list byte) : list cell :=
  match k with
  | O => []
  | S k' => C8 (le_bytes_to_word (List.firstn 8 bs)) :: c8cells k' (List.skipn 8 bs)
  end.

Lemma c8cells_size : forall k bs, cells_size (c8cells k bs) = (8 * k)%nat.
Proof. induction k; intros; cbn [c8cells cells_size csize]; [reflexivity|]. rewrite IHk. lia. Qed.

Lemma c8cells_bytes : forall k bs, length bs = (8 * k)%nat -> cells_bytes (c8cells k bs) = bs.
Proof.
  induction k as [|k IH]; intros bs L; cbn [c8cells cells_bytes cbytes].
  - destruct bs; [reflexivity| cbn in L; lia].
  - rewrite le8_of_bytes by (rewrite List.firstn_length_le; lia). rewrite IH by (rewrite List.length_skipn; lia). apply List.firstn_skipn.
Qed.

Lemma c8cells_wf : forall k bs, cells_wf (c8cells k bs).
Proof. induction k; intros; cbn; [exact I|]. split; [exact I| exact (IHk _)]. Qed.

(* [comment removed for export] *)
Lemma rw_cells_CB_c8 : forall segs m A pre (k : nat) bs post,
  rw_cells segs m A (pre ++ CB (8 * k) bs :: post) -> rw_cells segs m A (pre ++ c8cells k bs ++ post).
Proof.
  intros segs m A pre k bs post [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 [W2 W3]]. cbn in W2.
  split; [split|].
  - apply cells_wf_app. split; [exact W1|]. apply cells_wf_app. split; [apply c8cells_wf| exact W3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb. rewrite c8cells_bytes by lia. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in Hw. rewrite c8cells_size. exact Hw.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma le4_mod32 : forall x, le4 (Z_to_bv 64 x) = le4 (Z_to_bv 64 (x mod 2^32)).
Proof.
  intros x. unfold le4. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^32 * 2^32)%Z.
  rewrite <- (Z_to_le_bytes_mod 4 (x mod (2^32 * 2^32)) 32) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_mod 4 ((x mod 2^32) mod (2^32 * 2^32)) 32) by (cbn; lia).
  f_equal. rewrite Zaux.Zmod_mod_mult by lia. rewrite (Z.mod_small (x mod 2^32) (2^32 * 2^32)).
  - rewrite Z.mod_mod by lia. reflexivity.
  - pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)). lia.
Qed.

Lemma le4_word_mod32 : forall w : word, le4 w = le4 (Z_to_bv 64 (bv_unsigned w mod 2^32)).
Proof.
  intros w. rewrite <- (le4_mod32 (bv_unsigned w)). unfold le4. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma rw_cells_recell : forall segs m A cs k c c',
  rw_cells segs m A cs -> cell_at cs k = Some c -> cbytes c = cbytes c' -> csize c = csize c' -> cell_wf c' ->
  rw_cells segs m A (cell_upd cs k c').
Proof.
  intros segs m A cs k c c' [[Hwf Hb] Hw] Hk Hby Hsz Hwf'.
  cps_destruct (cell_at_split cs k c c' Hk) as (pre & post & E & Hpre & Eupd). rewrite Eupd. rewrite E in Hwf, Hb, Hw.
  apply cells_wf_app in Hwf. destruct Hwf as [W1 [W2 W3]].
  split; [split|].
  - apply cells_wf_app. split; [exact W1|]. split; [exact Hwf'| exact W3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes] in *. rewrite <- Hby. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size] in *. rewrite <- Hsz. exact Hw.
Qed.
End ACeilS3.


(* [comment removed for export] *)
Ltac cell_mod32 H k :=
  lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
    let c := eval cbv beta iota zeta delta [cell_at csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add] in (cell_at cs k) in
    lazymatch c with
    | Some (C4 (Z_to_bv 64 ?x)) =>
      let H' := fresh "RC" in
      pose proof (rw_cells_recell segs m A cs k (C4 (Z_to_bv 64 x)) (C4 (Z_to_bv 64 (x mod 2^32)%Z)) H
               ltac:(cbv beta iota zeta delta [cell_at csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add]; reflexivity)
               (le4_mod32 x) eq_refl I) as H';
      clear H; cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H'; rename H' into H
    | Some (C4 ?w) =>
      let H' := fresh "RC" in
      pose proof (rw_cells_recell segs m A cs k (C4 w) (C4 (Z_to_bv 64 (bv_unsigned w mod 2^32)%Z)) H
               ltac:(cbv beta iota zeta delta [cell_at csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add]; reflexivity)
               (le4_word_mod32 w) eq_refl I) as H';
      clear H; cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H'; rename H' into H
    end
  end.
Section ACeilS4. Context {ACEIL__ : ACeil}.


Lemma land255_range : forall x, (0 <= Z.land x 255 < 256)%Z.
Proof.
  intros x. change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.
Lemma land_mask_range : forall x k, (0 <= k)%Z -> (0 <= Z.land x (2^k - 1) < 2^k)%Z.
Proof.
  intros x k Hk. rewrite zb_land_mask by lia. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.
End ACeilS4.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac forget_reg n w :=
  let v := reg_val n in
  first [ is_var v
        | let E := fresh "E" w in remember v as w eqn:E in |- *; clear E ].

(* [comment removed for export] *)
Ltac bz32l :=
  strip_mod64_in_swrap;
  repeat match goal with
  | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
  | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
  | |- context [bv_wrap 32 ?e] => change (bv_wrap 32 e) with (Z.modulo e 4294967296)
  | |- context [Z.modulo ?e 4294967296] => rewrite (Z.mod_small e 4294967296) by lia
  | |- context [bv_swrap 32 ?e] => rewrite (swrap32_small e) by lia
  | |- context [Z.modulo ?e 18446744073709551616] => rewrite (Z.mod_small e 18446744073709551616) by lia
  | |- context [Z.lxor ?e 9223372036854775808] => rewrite (lxor_sign_small e) by lia
  | |- context [Z.lxor ?e 18446744073709551615] => rewrite (zb_lxor_ones e) by lia
  | |- context [bv_signed (Z_to_bv 64 ?e)] => rewrite (signed_lit_small e) by lia
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia
  | |- context [sx32 (Z_to_bv 64 ?e)] => rewrite (sx32_of_Z e) by lia
  | |- context [zx32 (Z_to_bv 64 ?e)] => rewrite (zx32_of_Z e) by lia
  end; zb_fold_lits.
Ltac wstepl := zstep; bz32l.
(* [comment removed for export] *)
