(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk MpiCoreAux CellsX.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mod64_eq_cancel : forall a b, 0 < a <= 18446744073709551616 -> 0 < b <= 18446744073709551616 ->
  a mod 18446744073709551616 = b mod 18446744073709551616 -> a = b.
Proof.
  intros a b Ha Hb E.
  destruct (Z.eq_dec a 18446744073709551616) as [Ea|Na]; destruct (Z.eq_dec b 18446744073709551616) as [Eb|Nb].
  - lia.
  - rewrite Ea, Z.mod_same, Z.mod_small in E by lia. lia.
  - rewrite Eb, Z.mod_same, Z.mod_small in E by lia. lia.
  - rewrite !Z.mod_small in E by lia. exact E.
Qed.
Lemma bveqb_lit_ne : forall a b, negb (bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b)) = true -> a <> b.
Proof. intros a b H E. subst. unfold bv_eqb in H. rewrite Z.eqb_refl in H. discriminate. Qed.
Lemma bveqb_lit_eq : forall a b, negb (bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b)) = false ->
  0 < a <= 18446744073709551616 -> 0 < b <= 18446744073709551616 -> a = b.
Proof.
  intros a b H Ha Hb. unfold bv_eqb in H. rewrite !Z_to_bv_unsigned in H. unfold bv_wrap in H.
  change (bv_modulus 64) with 18446744073709551616 in H.
  apply mod64_eq_cancel; [lia|lia|]. destruct (Z.eqb_spec (a mod 18446744073709551616) (b mod 18446744073709551616)); [assumption| discriminate].
Qed.
Ltac ptr_cases K := if_cases K; [ apply bveqb_lit_ne in K | apply bveqb_lit_eq in K; [|lia|lia] ].

(* [comment removed for export] *)
Lemma mod64_zero_small : forall a, -18446744073709551616 < a < 18446744073709551616 ->
  a mod 18446744073709551616 = 0 -> a = 0.
Proof. intros a Ha Hm. pose proof (Z.div_mod a 18446744073709551616 ltac:(lia)). lia. Qed.

Lemma Z_to_bv_mod64_sub : forall a b, Z_to_bv 64 (a mod 18446744073709551616 - b) = Z_to_bv 64 (a - b).
Proof.
  intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
  rewrite Zminus_mod_idemp_l. reflexivity.
Qed.

Lemma lxor_allones64 : forall x, 0 <= x < 2^64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
  intros x Hx. change 18446744073709551615 with (Z.ones 64).
  rewrite <- Z.ldiff_ones_l_low; [| lia | ].
  2:{ destruct (Z.eq_dec x 0) as [->|]. cbn; lia. apply Z.log2_lt_pow2; lia. }
  rewrite Z.ldiff_land, Z.land_comm, Z.land_ones by lia. unfold Z.lnot.
  rewrite <- (Z.mod_add _ 1) by lia. change (Z.ones 64) with (2^64 - 1). rewrite Z.mod_small; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac ubk K := exfalso; ub_decide K; rewrite ?Z.lor_0_l, ?Z.lor_0_r in K; try (rewrite Z.div_small in K by lia); first [ lia | discriminate K | congruence ].
Ltac gkill K := if_cases K; zify_cond K; [ ubk K | clear K ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma same_from_upd_lt : forall {T} k (l l0 : list T) i v, same_from k l l0 -> (i < k)%nat -> same_from k (upd l i v) l0.
Proof. intros T k l l0 i v H Hi q Hq. rewrite nth_error_upd_other by lia. apply H. exact Hq. Qed.

(* [comment removed for export] *)
Ltac rd H i :=
  let w := fresh "w" in let N := fresh "N" in let RD := fresh "RD" in
  lazymatch type of H with
  | u32arr ?sg ?mm ?A ?l =>
      destruct (nth_error l (Z.to_nat i)) as [w|] eqn:N; [| exfalso; apply nth_error_None in N; lia];
      pose proof (u32arr_read sg mm A l i w _ H N ltac:(lia) ltac:(f_equal; lia)) as RD
  | bytes_at ?sg ?mm ?A (u32s ?l) =>
      destruct (nth_error l (Z.to_nat i)) as [w|] eqn:N; [| exfalso; apply nth_error_None in N; lia];
      pose proof (u32ro_read sg mm A l i w _ H N ltac:(lia) ltac:(f_equal; lia)) as RD
  end;
  zstep; clear RD N; try clear w.

(* [comment removed for export] *)
Ltac wr H L FS i :=
  let SOK := fresh "SOK" in let H' := fresh "HX'" in
  lazymatch type of H with
  | u32arr ?sg ?mm ?A ?l =>
      pose proof (u32arr_store_ok sg mm A l i _ H ltac:(lia) ltac:(f_equal; lia)) as SOK;
      zstep;
      lazymatch goal with |- context [write_to_mem _ _ (le4 ?v)] =>
        pose proof (u32arr_write sg mm A l i v H ltac:(lia)) as H';
        apply (same_from_upd_lt _ _ _ (Z.to_nat i) v) in FS; [| lia];
        store_done; try clear H; rename H' into H;
        let l1 := fresh "ws" in let E := fresh "E" in let L1 := fresh "L" in
        remember (upd l (Z.to_nat i) v) as l1 eqn:E;
        lazymatch type of L with _ = ?r =>
          assert (L1 : Z.of_nat (length l1) = r) by (rewrite E, upd_length; exact L) end;
        clear L E; rename L1 into L; try clear l
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac getx R n :=
  lazymatch n with
  | 1%positive => lazymatch R with (TNode (TNode _ (Some ?v) _) None _) => v end
  | 2%positive => lazymatch R with (TNode _ None (TNode _ (Some ?v) _)) => v end
  | 3%positive => lazymatch R with (TNode (TNode (TNode _ (Some ?v) _) _ _) None _) => v end
  | 4%positive => lazymatch R with (TNode _ None (TNode (TNode _ (Some ?v) _) _ _)) => v end
  | 5%positive => lazymatch R with (TNode (TNode _ _ (TNode _ (Some ?v) _)) None _) => v end
  | 6%positive => lazymatch R with (TNode _ None (TNode _ _ (TNode _ (Some ?v) _))) => v end
  | 7%positive => lazymatch R with (TNode (TNode (TNode (TNode _ (Some ?v) _) _ _) _ _) None _) => v end
  | 8%positive => lazymatch R with (TNode _ None (TNode (TNode (TNode _ (Some ?v) _) _ _) _ _)) => v end
  | 9%positive => lazymatch R with (TNode (TNode _ _ (TNode (TNode _ (Some ?v) _) _ _)) None _) => v end
  | 10%positive => lazymatch R with (TNode _ None (TNode _ _ (TNode (TNode _ (Some ?v) _) _ _))) => v end
  | 11%positive => lazymatch R with (TNode (TNode (TNode _ _ (TNode _ (Some ?v) _)) _ _) None _) => v end
  | 12%positive => lazymatch R with (TNode _ None (TNode (TNode _ _ (TNode _ (Some ?v) _)) _ _)) => v end
  | 13%positive => lazymatch R with (TNode (TNode _ _ (TNode _ _ (TNode _ (Some ?v) _))) None _) => v end
  | 14%positive => lazymatch R with (TNode _ None (TNode _ _ (TNode _ _ (TNode _ (Some ?v) _)))) => v end
  | 15%positive => lazymatch R with (TNode (TNode (TNode (TNode (TNode _ (Some ?v) _) _ _) _ _) _ _) None _) => v end
  | 16%positive => lazymatch R with (TNode _ None (TNode (TNode (TNode (TNode _ (Some ?v) _) _ _) _ _) _ _)) => v end
  | 17%positive => lazymatch R with (TNode (TNode _ _ (TNode (TNode (TNode _ (Some ?v) _) _ _) _ _)) None _) => v end
  | 18%positive => lazymatch R with (TNode _ None (TNode _ _ (TNode (TNode (TNode _ (Some ?v) _) _ _) _ _))) => v end
  | 19%positive => lazymatch R with (TNode (TNode (TNode _ _ (TNode (TNode _ (Some ?v) _) _ _)) _ _) None _) => v end
  | 20%positive => lazymatch R with (TNode _ None (TNode (TNode _ _ (TNode (TNode _ (Some ?v) _) _ _)) _ _)) => v end
  | 21%positive => lazymatch R with (TNode (TNode _ _ (TNode _ _ (TNode (TNode _ (Some ?v) _) _ _))) None _) => v end
  | 22%positive => lazymatch R with (TNode _ None (TNode _ _ (TNode _ _ (TNode (TNode _ (Some ?v) _) _ _)))) => v end
  | 23%positive => lazymatch R with (TNode (TNode (TNode (TNode _ _ (TNode _ (Some ?v) _)) _ _) _ _) None _) => v end
  | 24%positive => lazymatch R with (TNode _ None (TNode (TNode (TNode _ _ (TNode _ (Some ?v) _)) _ _) _ _)) => v end
  | 25%positive => lazymatch R with (TNode (TNode _ _ (TNode (TNode _ _ (TNode _ (Some ?v) _)) _ _)) None _) => v end
  | 26%positive => lazymatch R with (TNode _ None (TNode _ _ (TNode (TNode _ _ (TNode _ (Some ?v) _)) _ _))) => v end
  | 27%positive => lazymatch R with (TNode (TNode (TNode _ _ (TNode _ _ (TNode _ (Some ?v) _))) _ _) None _) => v end
  | 28%positive => lazymatch R with (TNode _ None (TNode (TNode _ _ (TNode _ _ (TNode _ (Some ?v) _))) _ _)) => v end
  | 29%positive => lazymatch R with (TNode (TNode _ _ (TNode _ _ (TNode _ _ (TNode _ (Some ?v) _)))) None _) => v end
  | 30%positive => lazymatch R with (TNode _ None (TNode _ _ (TNode _ _ (TNode _ _ (TNode _ (Some ?v) _))))) => v end
  | 31%positive => lazymatch R with (TNode (TNode (TNode (TNode (TNode (TNode _ (Some ?v) _) _ _) _ _) _ _) _ _) None _) => v end
  end.

(* [comment removed for export] *)
Ltac fgt n :=
  lazymatch goal with |- _ (MS ?R _ _ _ _ _ _) =>
    let v := getx R n in
    first [ is_var v
          | let c := fresh "v" in set (c := v) in |- *; clearbody c ]
  end.
(* [comment removed for export] *)
Ltac vstep n := step; fgt n.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mw_lor_shl8_low : forall b r, 0 <= b < 256 -> 0 <= r -> Z_to_bv 8 (Z.lor b (Z.shiftl r 8)) = Z_to_bv 8 b.
Proof.
  intros b r Hb Hr. apply bv_eq. rewrite !Z_to_bv_unsigned. change (bv_wrap 8 ?x) with (x mod 2^8). cbv beta.
  change (bv_wrap 8 b) with (b mod 2^8).
  apply Z.bits_inj'. intros i Hi.
  destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite Z.lor_spec, Z.shiftl_spec by lia.
    rewrite (Z.testbit_neg_r r (i - 8)) by lia. apply orb_false_r.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma mw_lor_shl8_high : forall b r, 0 <= b < 256 -> 0 <= r -> Z.shiftr (Z.lor b (Z.shiftl r 8)) 8 = r.
Proof.
  intros b r Hb Hr. rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
  rewrite Z.shiftr_div_pow2, Z.div_small by lia. reflexivity.
Qed.
Lemma mw_bytes_le_to_Z_nonneg : forall bs, 0 <= bytes_le_to_Z bs.
Proof.
  induction bs as [|b bs IH]; cbn; [lia|]. apply Z.lor_nonneg. split; [apply bv_unsigned_in_range|].
  apply Z.shiftl_nonneg. exact IH.
Qed.
Lemma mw_Z_to_le_bytes_to_Z : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. pose proof (mw_bytes_le_to_Z_nonneg bs).
  f_equal.
  - rewrite mw_lor_shl8_low by (cbn in Hb; lia). apply definitions.Z_to_bv_bv_unsigned.
  - rewrite mw_lor_shl8_high by (cbn in Hb; lia). exact IH.
Qed.

Lemma le4_le_bytes_to_word : forall bs, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs Hl. unfold le4, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 ?x) with (x mod 2^64).
  rewrite <- (Z_to_le_bytes_mod 4 (_ mod 2^64)). change (2 ^ (8 * Z.of_nat 4)) with (2^32).
  rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists (2^32); reflexivity).
  rewrite (Z_to_le_bytes_mod 4). rewrite <- Hl. apply mw_Z_to_le_bytes_to_Z.
Qed.

(* [comment removed for export] *)
Lemma bytes_as_u32s : forall (k : nat) (bs : list byte), length bs = (4 * k)%nat ->
  exists ws, bs = u32s ws /\ length ws = k.
Proof.
  induction k as [|k IH]; intros bs Hl.
  - exists []. destruct bs; [split; reflexivity| cbn in Hl; lia].
  - destruct (IH (skipn 4 bs)) as (ws & E & L). { rewrite skipn_length. lia. }
    exists (le_bytes_to_word (firstn 4 bs) :: ws). split; [| cbn; lia].
    cbn [u32s flat_map]. change (flat_map le4 ws) with (u32s ws). rewrite <- E.
    rewrite le4_le_bytes_to_word by (rewrite firstn_length; lia). symmetry. apply firstn_skipn.
Qed.

Lemma u8arr_of_u32arr : forall segs m A ws, u32arr segs m A ws -> u8arr segs m A (u32s ws).
Proof. intros segs m A ws [Hb Hw]. split; [exact Hb|]. rewrite u32s_length. replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws)) by lia. exact Hw. Qed.

Lemma u32arr_of_u8arr : forall segs m A bs (k : nat), u8arr segs m A bs -> length bs = (4 * k)%nat ->
  exists ws, u32arr segs m A ws /\ length ws = k.
Proof.
  intros segs m A bs k [Hb Hw] Hl. destruct (bytes_as_u32s k bs Hl) as (ws & -> & L).
  exists ws. split; [|exact L]. split; [exact Hb|]. rewrite u32s_length in Hw.
  replace (4 * Z.of_nat (length ws)) with (Z.of_nat (4 * length ws)) by lia. exact Hw.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac rd8 H i :=
  let w := fresh "b" in let N := fresh "N" in let RD := fresh "RD" in
  lazymatch type of H with
  | u8arr ?sg ?mm ?A ?l =>
      destruct (nth_error l (Z.to_nat i)) as [w|] eqn:N; [| exfalso; apply nth_error_None in N; lia];
      pose proof (u8arr_read sg mm A l i w _ H N ltac:(lia) ltac:(f_equal; lia)) as RD
  | bytes_at ?sg ?mm ?A ?l =>
      destruct (nth_error l (Z.to_nat i)) as [w|] eqn:N; [| exfalso; apply nth_error_None in N; lia];
      pose proof (u8ro_read sg mm A l i w _ H N ltac:(lia) ltac:(f_equal; lia)) as RD
  end;
  zstep; clear RD N; try clear w.

Ltac wr8 H L FS i :=
  let SOK := fresh "SOK" in let H' := fresh "HX'" in
  lazymatch type of H with
  | u8arr ?sg ?mm ?A ?l =>
      pose proof (u8arr_store_ok sg mm A l i _ H ltac:(lia) ltac:(f_equal; lia)) as SOK;
      zstep;
      lazymatch goal with |- context [write_to_mem _ _ (le1 ?v0) ] =>
        change (le1 v0) with [Z_to_bv 8 (bv_unsigned v0)] end;
      lazymatch goal with |- context [write_to_mem _ _ [?v] ] =>
        pose proof (u8arr_write sg mm A l i v H ltac:(lia)) as H';
        apply (same_from_upd_lt _ _ _ (Z.to_nat i) v) in FS; [| lia];
        store_done; try clear H; rename H' into H;
        let l1 := fresh "bs" in let E := fresh "E" in let L1 := fresh "L" in
        remember (upd l (Z.to_nat i) v) as l1 eqn:E;
        lazymatch type of L with _ = ?r =>
          assert (L1 : Z.of_nat (length l1) = r) by (rewrite E, upd_length; exact L) end;
        clear L E; rename L1 into L; try clear l
      end
  end.
