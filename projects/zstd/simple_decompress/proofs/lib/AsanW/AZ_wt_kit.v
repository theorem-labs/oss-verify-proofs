(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem ZdSeqBuildW ZdHufWM ZdHufWX SepHide.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA.
Import ListNotations. Import KXS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma Zupd_comm : forall i j x y (l : list Z), i <> j -> 0 <= i -> 0 <= j -> Zupd i x (Zupd j y l) = Zupd j y (Zupd i x l).
Proof.
  intros i j x y l NE Hi Hj. unfold Zupd.
  assert (NE' : Z.to_nat i <> Z.to_nat j) by lia. revert NE'.
  generalize (Z.to_nat i) (Z.to_nat j). clear. intros a b. revert a b.
  induction l as [|h t IH]; intros [|a] [|b] NE; cbn; try reflexivity; [congruence|]. rewrite IH by congruence. reflexivity.
Qed.
Lemma Zupd_length2 : forall i x (l : list Z), Z.of_nat (length (Zupd i x l)) = Z.of_nat (length l).
Proof. intros. rewrite Zupd_length. reflexivity. Qed.

Lemma Forall_Zupd : forall (P : Z -> Prop) i v (l : list Z), Forall P l -> P v -> Forall P (Zupd i v l).
Proof.
  intros P i v l F Hv. unfold Zupd. generalize (Z.to_nat i). intros n. revert n.
  induction F as [|x t Hx Ht IH]; intros [|n]; cbn [upd_nat]; constructor; auto.
Qed.

Lemma upd_bytes_map4 : forall (f : Z -> byte) (l : list Z) (i : nat) a b c d, (i + 4 <= length l)%nat ->
  upd_bytes (map f l) i [f a; f b; f c; f d] = map f (upd_nat (i + 3) d (upd_nat (i + 2) c (upd_nat (i + 1) b (upd_nat i a l)))).
Proof.
  intros f l i. revert l. induction i as [|i IH]; intros l a b c d H.
  - destruct l as [|x [|y [|z [|u t]]]]; cbn [length] in H; try lia. reflexivity.
  - destruct l as [|x t]; cbn [length] in H; [lia|].
    change (upd_bytes (map f (x :: t)) (S i) [f a; f b; f c; f d]) with (f x :: upd_bytes (map f t) i [f a; f b; f c; f d]).
    rewrite IH by lia. reflexivity.
Qed.

Lemma log_flat_head : forall E a w v rest, log_flat E (SE a w v :: rest) ->
  log_flat E rest /\ 0 <= estart E a /\ estart E a + Z.of_nat w <= 2^64.
Proof.
  intros E a w v rest H. change (log_flat E ([SE a w v] ++ rest)) in H. apply log_flat_app in H as [H1 H2].
  cbn [log_flat] in H1. destruct H1 as (_ & (F1 & F2 & F3 & F4) & _). split; [exact H2| lia].
Qed.

Section KXK.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma kxk_nil : forall E (m : word -> option byte) A bs, u8arr segs m A bs -> u8arr segs (mem_denot E m []) A bs.
Proof. intros. exact H. Qed.

Lemma kxk_apart : forall E m rest a w v A bs az,
  u8arr segs (mem_denot E m rest) A bs -> log_flat E (SE a w v :: rest) -> estart E a = az ->
  A + Z.of_nat (length bs) <= az \/ az + Z.of_nat w <= A ->
  u8arr segs (mem_denot E m (SE a w v :: rest)) A bs.
Proof.
  intros E m rest a w v A bs az H LF Ha Hd. rewrite mem_denot_cons.
  destruct (log_flat_head E a w v rest LF) as (_ & F1 & F2).
  apply u8arr_frame; [exact H| lia | rewrite kx_sbytes_length; lia | rewrite kx_sbytes_length; lia].
Qed.

(* [comment removed for export] *)
Lemma kxk_apartK : forall E m0 kn, know_ok segs E m0 kn ->
  forall m rest a w v A bs ca cn,
  u8arr segs (mem_denot E m rest) A bs -> log_flat E (SE a w v :: rest) ->
  log_apart_b kn [SE a w v] ca cn = true -> estart E ca = A -> elenZ E cn = Z.of_nat (length bs) ->
  u8arr segs (mem_denot E m (SE a w v :: rest)) A bs.
Proof.
  intros E m0 kn HK m rest a w v A bs ca cn H LF Hb EA EN.
  change (SE a w v :: rest) with ([SE a w v] ++ rest). rewrite mem_denot_app.
  change (SE a w v :: rest) with ([SE a w v] ++ rest) in LF. apply log_flat_app in LF as [LF1 _].
  apply kx_u8arr_apartP; [exact LF1| | exact H].
  rewrite <- EA, <- EN. exact (log_apart_b_sound segs E m0 kn HK [SE a w v] ca cn LF1 Hb).
Qed.

(* [comment removed for export] *)
Lemma kxk_in1 : forall E m rest a v A (buf : list Z) az x,
  u8arr segs (mem_denot E m rest) A (map (Z_to_bv 8) buf) -> estart E a = az -> edenot E v = Z_to_bv 64 x ->
  A <= az -> az + 1 <= A + Z.of_nat (length buf) ->
  u8arr segs (mem_denot E m (SE a 1%nat v :: rest)) A (map (Z_to_bv 8) (Zupd (az - A) (x mod 256) buf)).
Proof.
  intros E m rest a v A buf az x H Ha Hv H1 H2. rewrite mem_denot_cons, Ha.
  unfold kx_sbytes. rewrite Hv. change (word_to_le_bytes 1 (Z_to_bv 64 x)) with (le1 (Z_to_bv 64 x)).
  replace az with (A + (az - A)) at 1 by lia.
  apply u8arr_sb; [exact H| lia| rewrite Z.mod_mod by lia; reflexivity].
Qed.
(* [comment removed for export] *)
Lemma kxk_in1w : forall E m rest a v A (buf : list Z) az (W : word),
  u8arr segs (mem_denot E m rest) A (map (Z_to_bv 8) buf) -> estart E a = az -> edenot E v = W ->
  A <= az -> az + 1 <= A + Z.of_nat (length buf) ->
  u8arr segs (mem_denot E m (SE a 1%nat v :: rest)) A (map (Z_to_bv 8) (Zupd (az - A) (bv_unsigned W mod 256) buf)).
Proof.
  intros E m rest a v A buf az W H Ha Hv H1 H2.
  apply kxk_in1; [exact H| exact Ha| | exact H1| exact H2]. rewrite Hv. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* [comment removed for export] *)
Lemma kxk_in2 : forall E m rest a v A (buf : list Z) az x,
  u8arr segs (mem_denot E m rest) A (map (Z_to_bv 8) buf) -> estart E a = az -> edenot E v = Z_to_bv 64 x ->
  A <= az -> az + 2 <= A + Z.of_nat (length buf) ->
  u8arr segs (mem_denot E m (SE a 2%nat v :: rest)) A
        (map (Z_to_bv 8) (Zupd (az - A + 1) ((x / 256) mod 256) (Zupd (az - A) (x mod 256) buf))).
Proof.
  intros E m rest a v A buf az x H Ha Hv H1 H2. rewrite mem_denot_cons, Ha.
  unfold kx_sbytes. rewrite Hv. change (word_to_le_bytes 2 (Z_to_bv 64 x)) with (le2 (Z_to_bv 64 x)).
  replace az with (A + (az - A)) at 1 by lia.
  apply u8arr_sh; [exact H| lia| lia| reflexivity].
Qed.
Lemma kxk_in2w : forall E m rest a v A (buf : list Z) az (W : word),
  u8arr segs (mem_denot E m rest) A (map (Z_to_bv 8) buf) -> estart E a = az -> edenot E v = W ->
  A <= az -> az + 2 <= A + Z.of_nat (length buf) ->
  u8arr segs (mem_denot E m (SE a 2%nat v :: rest)) A
        (map (Z_to_bv 8) (Zupd (az - A + 1) ((bv_unsigned W / 256) mod 256) (Zupd (az - A) (bv_unsigned W mod 256) buf))).
Proof.
  intros E m rest a v A buf az W H Ha Hv H1 H2.
  apply kxk_in2; [exact H| exact Ha| | exact H1| exact H2]. rewrite Hv. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* [comment removed for export] *)
Lemma kxk_in4 : forall E m rest a v A (buf : list Z) az x,
  u8arr segs (mem_denot E m rest) A (map (Z_to_bv 8) buf) -> estart E a = az -> edenot E v = Z_to_bv 64 x ->
  A <= az -> az + 4 <= A + Z.of_nat (length buf) ->
  u8arr segs (mem_denot E m (SE a 4%nat v :: rest)) A
        (map (Z_to_bv 8) (Zupd (az - A + 3) ((x / 16777216) mod 256) (Zupd (az - A + 2) ((x / 65536) mod 256)
                            (Zupd (az - A + 1) ((x / 256) mod 256) (Zupd (az - A) (x mod 256) buf))))).
Proof.
  intros E m rest a v A buf az x H Ha Hv H1 H2. rewrite mem_denot_cons, Ha.
  unfold kx_sbytes. rewrite Hv. change (word_to_le_bytes 4 (Z_to_bv 64 x)) with (le4 (Z_to_bv 64 x)).
  rewrite (le4_Z x x eq_refl). unfold zle4.
  replace az with (A + (az - A)) at 1 by lia.
  pose proof (u8arr_writen segs (mem_denot E m rest) A _ (az - A) [Z_to_bv 8 (x mod 256); Z_to_bv 8 ((x / 256) mod 256); Z_to_bv 8 ((x / 65536) mod 256); Z_to_bv 8 ((x / 16777216) mod 256)]
                H ltac:(lia) ltac:(rewrite length_map; cbn [length]; lia)) as K.
  rewrite upd_bytes_map4 in K by lia. unfold Zupd.
  replace (Z.to_nat (az - A + 3)) with (Z.to_nat (az - A) + 3)%nat by lia. replace (Z.to_nat (az - A + 2)) with (Z.to_nat (az - A) + 2)%nat by lia.
  replace (Z.to_nat (az - A + 1)) with (Z.to_nat (az - A) + 1)%nat by lia. exact K.
Qed.
Lemma kxk_in4w : forall E m rest a v A (buf : list Z) az (W : word),
  u8arr segs (mem_denot E m rest) A (map (Z_to_bv 8) buf) -> estart E a = az -> edenot E v = W ->
  A <= az -> az + 4 <= A + Z.of_nat (length buf) ->
  u8arr segs (mem_denot E m (SE a 4%nat v :: rest)) A
        (map (Z_to_bv 8) (Zupd (az - A + 3) ((bv_unsigned W / 16777216) mod 256) (Zupd (az - A + 2) ((bv_unsigned W / 65536) mod 256)
                            (Zupd (az - A + 1) ((bv_unsigned W / 256) mod 256) (Zupd (az - A) (bv_unsigned W mod 256) buf))))).
Proof.
  intros E m rest a v A buf az W H Ha Hv H1 H2.
  apply kxk_in4; [exact H| exact Ha| | exact H1| exact H2]. rewrite Hv. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* [comment removed for export] *)
Lemma kxk_in16 : forall E m rest a v A (l : list Z) az x s,
  u8arr segs (mem_denot E m rest) A (u16s (map (Z_to_bv 64) l)) -> estart E a = az -> edenot E v = Z_to_bv 64 x ->
  az = A + 2 * s -> 0 <= s -> s < Z.of_nat (length l) ->
  u8arr segs (mem_denot E m (SE a 2%nat v :: rest)) A (u16s (map (Z_to_bv 64) (Zupd s (x mod 65536) l))).
Proof.
  intros E m rest a v A l az x s H Ha Hv Hs H1 H2. rewrite mem_denot_cons, Ha, Hs.
  unfold kx_sbytes. rewrite Hv. change (word_to_le_bytes 2 (Z_to_bv 64 x)) with (le2 (Z_to_bv 64 x)).
  unfold Zupd. rewrite <- (u16s_upd_Z l (Z.to_nat s) x (x mod 65536)) by (rewrite Z.mod_mod by lia; reflexivity).
  apply u16arr_write; [exact H| rewrite length_map; lia].
Qed.
Lemma kxk_in16w : forall E m rest a v A (l : list Z) az (W : word) s,
  u8arr segs (mem_denot E m rest) A (u16s (map (Z_to_bv 64) l)) -> estart E a = az -> edenot E v = W ->
  az = A + 2 * s -> 0 <= s -> s < Z.of_nat (length l) ->
  u8arr segs (mem_denot E m (SE a 2%nat v :: rest)) A (u16s (map (Z_to_bv 64) (Zupd s (bv_unsigned W mod 65536) l))).
Proof.
  intros E m rest a v A l az W s H Ha Hv Hs H1 H2.
  apply (kxk_in16 E m rest a v A l az (bv_unsigned W) s); [exact H| exact Ha| | exact Hs| exact H1| exact H2].
  rewrite Hv. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rdval_u8Z : forall m A (buf : list Z) i az,
  u8arr segs m A (map (Z_to_bv 8) buf) -> az = A + i -> 0 <= i < Z.of_nat (length buf) ->
  rdval segs m (wa az) 1 false = Z_to_bv 64 (Znth i buf mod 256).
Proof.
  intros m A buf i az [HB _] -> Hi.
  rewrite (rdval_bytes_at segs m A _ i 1 false HB) by (rewrite ?length_map; lia).
  f_equal.
  rewrite (firstn1_skipn (Z.to_nat i) (map (Z_to_bv 8) buf) (Z_to_bv 8 (Znth i buf))) by (apply nth_error_map_Znth; lia).
  unfold extz. cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. reflexivity.
Qed.
Lemma rdval_u8Zb : forall m A (buf : list Z) i az,
  u8arr segs m A (map (Z_to_bv 8) buf) -> az = A + i -> 0 <= i < Z.of_nat (length buf) ->
  Forall (fun v : Z => 0 <= v < 256) buf ->
  rdval segs m (wa az) 1 false = Z_to_bv 64 (Znth i buf).
Proof.
  intros m A buf i az H Ha Hi HF. rewrite (rdval_u8Z m A buf i az H Ha Hi). f_equal. apply Z.mod_small.
  exact (Forall_Znth _ buf i HF Hi).
Qed.

(* [comment removed for export] *)
Lemma rdval_u32Zb : forall m A (buf : list Z) i az,
  u8arr segs m A (map (Z_to_bv 8) buf) -> az = A + i -> 0 <= i -> i + 4 <= Z.of_nat (length buf) ->
  Forall (fun v : Z => 0 <= v < 256) buf ->
  rdval segs m (wa az) 4 false = Z_to_bv 64 (Znth i buf + 256 * Znth (i + 1) buf + 65536 * Znth (i + 2) buf + 16777216 * Znth (i + 3) buf).
Proof.
  intros m A buf i az [HB _] -> Hi Hl HF.
  rewrite (rdval_bytes_at segs m A _ i 4 false HB); [| lia| rewrite length_map; lia].
  f_equal. rewrite (firstn4_skipn (Z_to_bv 8 0)) by (rewrite length_map; lia).
  pose proof (Forall_Znth _ buf i HF ltac:(lia)) as B0. pose proof (Forall_Znth _ buf (i + 1) HF ltac:(lia)) as B1.
  pose proof (Forall_Znth _ buf (i + 2) HF ltac:(lia)) as B2. pose proof (Forall_Znth _ buf (i + 3) HF ltac:(lia)) as B3. cbv beta in *.
  assert (N : forall k, 0 <= k -> k < Z.of_nat (length buf) -> nth (Z.to_nat k) (map (Z_to_bv 8) buf) (Z_to_bv 8 0) = Z_to_bv 8 (Znth k buf)).
  { intros k Hk Hk2. unfold Znth. change (Z_to_bv 8 0) with ((Z_to_bv 8) 0). rewrite map_nth. reflexivity. }
  replace (Z.to_nat i + 1)%nat with (Z.to_nat (i + 1)) by lia. replace (Z.to_nat i + 2)%nat with (Z.to_nat (i + 2)) by lia.
  replace (Z.to_nat i + 3)%nat with (Z.to_nat (i + 3)) by lia.
  rewrite !N by lia.
  unfold extz. rewrite bytes_le_to_Z_le_val. cbn [map le_val]. rewrite !byte_lit by lia.
  lia.
Qed.

Lemma bytes_le_to_Z_le2 : forall x, bytes_le_to_Z (le2 (Z_to_bv 64 x)) = x mod 65536.
Proof.
  intros x. unfold le2. rewrite bytes_le_to_Z_to_le_bytes by (apply bv_unsigned_in_range).
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (65536 * 281474976710656).
  change (2 ^ (8 * Z.of_nat 2)) with 65536. rewrite Z.rem_mul_r by lia. Z.div_mod_to_equations. lia.
Qed.

Lemma rdval_u16_raw : forall m A (l : list Z) i az sx,
  bytes_at segs m A (u16s (map (Z_to_bv 64) l)) -> az = A + 2 * i -> 0 <= i < Z.of_nat (length l) ->
  rdval segs m (wa az) 2 sx = Z_to_bv 64 (extz sx 2 (Znth i l mod 65536)).
Proof.
  intros m A l i az sx HB -> Hi.
  rewrite (rdval_bytes_at segs m A _ (2 * i) 2 sx HB); [| lia| rewrite u16s_length, length_map; lia].
  f_equal. f_equal.
  destruct (nth_error_split (map (Z_to_bv 64) l) (Z.to_nat i) _ (nth_error_map_Znth (Z_to_bv 64) l i Hi)) as (pre & post & E & Hlen).
  rewrite E. rewrite u16s_app. cbn [u16s].
  replace (Z.to_nat (2 * i)) with (length (u16s pre)) by (rewrite u16s_length; lia).
  rewrite skipn_app, skipn_all, Nat.sub_diag. cbn [app]. rewrite skipn_O.
  rewrite firstn_app, length_le2. replace (2 - 2)%nat with 0%nat by reflexivity. rewrite firstn_O, app_nil_r.
  rewrite firstn_all2 by (rewrite length_le2; lia).
  apply bytes_le_to_Z_le2.
Qed.
Lemma rdval_u16Z : forall m A (l : list Z) i az,
  bytes_at segs m A (u16s (map (Z_to_bv 64) l)) -> az = A + 2 * i -> 0 <= i < Z.of_nat (length l) ->
  rdval segs m (wa az) 2 false = Z_to_bv 64 (Znth i l mod 65536).
Proof. intros. rewrite (rdval_u16_raw m A l i az false) by assumption. reflexivity. Qed.
Lemma rdval_s16Z : forall m A (l : list Z) i az,
  bytes_at segs m A (u16s (map (Z_to_bv 64) l)) -> az = A + 2 * i -> 0 <= i < Z.of_nat (length l) ->
  -32768 <= Znth i l < 32768 ->
  rdval segs m (wa az) 2 true = Z_to_bv 64 (Znth i l).
Proof.
  intros m A l i az HB Ha Hi Hr. rewrite (rdval_u16_raw m A l i az true HB Ha Hi).
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  unfold extz, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N (8 * N.of_nat 2)) with 65536.
  change (2^64) with 18446744073709551616. Z.div_mod_to_equations. lia.
Qed.
End KXK.

(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac kxk_sizes := rewrite ?length_map, ?Zupd_length, ?upd_length in *.

(* [comment removed for export] *)
Ltac kxk_apart_b kn zs a w v K :=
  lazymatch type of K with
  | u8arr _ _ ?A ?bs =>
      let ln := kx_len_term bs in
      lazymatch ln with (?N, _) =>
        let eA := kx_rz_old zs A in let eN := kx_rz_old zs N in
        eval vm_compute in (log_apart_b kn [SE a w v] (zsa eA) (zx eN))
      end
  end.

(* [comment removed for export] *)
Ltac kxk_step GEN segs E zs nz kn KXA LF a w v rest K IDX :=
  let ab := eval cbv in (a_base a) in
  let zb := kx_ez E zs nz ab in
  let off := eval cbv in (a_off a) in
  let HEQ := fresh "KXEQ" in
  assert (HEQ : estart E a = zb + off)
    by (apply (estart_ez zs E a KXA); change (0 <= zb < 2^64); kx_lia);
  let K' := fresh "KXK" in
  let apart := kxk_apart_b kn zs a w v K in
  lazymatch apart with
  | true =>
      lazymatch goal with
      | KXK : know_ok _ E _ kn |- _ =>
          lazymatch type of K with
          | u8arr _ _ ?A ?bs =>
              let ln := kx_len_term bs in
              lazymatch ln with (?N, ?HL) =>
                let eA := kx_rz_old zs A in let eN := kx_rz_old zs N in
                let PA := kx_estart_prf zs E KXA eA A in let PN := kx_elen_prf zs E KXA eN N in
                pose proof (kxk_apartK segs E _ kn KXK _ rest a w v A bs (zsa eA) (zx eN) K LF
                              ltac:(vm_cast_no_check (@eq_refl bool true)) PA (eq_trans PN (eq_sym HL))) as K'
              end
          end
      end
  | false =>
      let W := kx_word E zs nz v in
      let HV := fresh "KXV" in
      assert (HV : edenot E v = W) by kx_word_prf E zs KXA v;
      lazymatch type of K with
      | u8arr _ _ ?A (map (Z_to_bv 8) ?buf) =>
          lazymatch w with
          | 1%nat =>
              lazymatch W with
              | Z_to_bv 64 ?x => pose proof (kxk_in1 segs E _ rest a v A buf (zb + off) x K HEQ HV ltac:(kx_lia) ltac:(kxk_sizes; kx_lia)) as K'
              | _ => pose proof (kxk_in1w segs E _ rest a v A buf (zb + off) W K HEQ HV ltac:(kx_lia) ltac:(kxk_sizes; kx_lia)) as K'
              end
          | 2%nat =>
              lazymatch W with
              | Z_to_bv 64 ?x => pose proof (kxk_in2 segs E _ rest a v A buf (zb + off) x K HEQ HV ltac:(kx_lia) ltac:(kxk_sizes; kx_lia)) as K'
              | _ => pose proof (kxk_in2w segs E _ rest a v A buf (zb + off) W K HEQ HV ltac:(kx_lia) ltac:(kxk_sizes; kx_lia)) as K'
              end
          | 4%nat =>
              lazymatch W with
              | Z_to_bv 64 ?x => pose proof (kxk_in4 segs E _ rest a v A buf (zb + off) x K HEQ HV ltac:(kx_lia) ltac:(kxk_sizes; kx_lia)) as K'
              | _ => pose proof (kxk_in4w segs E _ rest a v A buf (zb + off) W K HEQ HV ltac:(kx_lia) ltac:(kxk_sizes; kx_lia)) as K'
              end
          end
      | u8arr _ _ ?A (u16s (map (Z_to_bv 64) ?l)) =>
          lazymatch w with
          | 2%nat =>
              let rec try_idx li :=
                lazymatch li with
                | @cons _ ?s ?t =>
                    first
                      [ lazymatch W with
                        | Z_to_bv 64 ?x =>
                            pose proof (kxk_in16 segs E _ rest a v A l (zb + off) x s K HEQ HV ltac:(kx_lia) ltac:(kx_lia) ltac:(kxk_sizes; kx_lia)) as K'
                        | _ => pose proof (kxk_in16w segs E _ rest a v A l (zb + off) W s K HEQ HV ltac:(kx_lia) ltac:(kx_lia) ltac:(kxk_sizes; kx_lia)) as K'
                        end
                      | try_idx t ]
                | _ => fail 1 "kxk_step: no index of the list matches the short store at" zb off
                end in
              try_idx IDX
          end
      end;
      clear HV;
      (* [comment removed for export] *)
      lazymatch GEN with
      | true =>
          let gv v := let x := fresh "kxv" in let EQ := fresh "KXVE" in
                      remember v as x eqn:EQ in K'; change (hidden (x = v)) in EQ in
          let gtop _ := lazymatch type of K' with
                        | u8arr _ _ _ (map _ (Zupd _ ?v _)) => gv v | u8arr _ _ _ (u16s (map _ (Zupd _ ?v _))) => gv v end in
          let g2 _ := lazymatch type of K' with u8arr _ _ _ (map _ (Zupd _ _ (Zupd _ ?v _))) => gv v end in
          let g3 _ := lazymatch type of K' with u8arr _ _ _ (map _ (Zupd _ _ (Zupd _ _ (Zupd _ ?v _)))) => gv v end in
          let g4 _ := lazymatch type of K' with u8arr _ _ _ (map _ (Zupd _ _ (Zupd _ _ (Zupd _ _ (Zupd _ ?v _))))) => gv v end in
          lazymatch w with
          | 1%nat => gtop tt
          | 2%nat => lazymatch type of K' with u8arr _ _ _ (u16s _) => gtop tt | _ => g2 tt; gtop tt end
          | 4%nat => g4 tt; g3 tt; g2 tt; gtop tt
          end
      | false => idtac
      end;
      (* [comment removed for export] *)
      lazymatch type of K with
      | u8arr _ _ _ ?bs =>
          let ln := kx_len_term bs in
          lazymatch ln with (?N, ?HL) =>
            lazymatch type of K' with
            | u8arr _ _ _ ?bs' =>
                let HLn := fresh "KXUL" in
                assert (HLn : Z.of_nat (length bs') = N)
                  by (rewrite ?length_map, ?u16s_length, ?length_map, ?Zupd_length; generalize HL; rewrite ?length_map, ?u16s_length, ?length_map, ?Zupd_length;
                      let t := fresh in intros t; first [exact t | lia]);
                try (lazymatch HL with @eq_refl _ _ => idtac | _ => clear HL end)
            end
          end
      end
  end;
  clear HEQ; clear K; rename K' into K.

(* [comment removed for export] *)
Ltac kxk_build GEN segs E zs nz kn KXA LF log K IDX :=
  lazymatch log with
  | @nil _ => idtac
  | @cons _ (SE ?a ?w ?v) ?rest =>
      let LF' := fresh "KXKF" in
      pose proof (proj1 (log_flat_head E a w v rest LF)) as LF';
      kxk_build GEN segs E zs nz kn KXA LF' rest K IDX;
      kxk_step GEN segs E zs nz kn KXA LF a w v rest K IDX;
      clear LF'
  end.

(* [comment removed for export] *)
Ltac kxk_keep_gix GEN H IDX :=
  lazymatch goal with
  | |- context [mem_denot ?E ?m ?log] =>
      lazymatch goal with
      | KXA : atoms_ok ?zs E, KXLF : log_flat E log, KXK : know_ok ?sg E m ?kn |- _ =>
          let segs := lazymatch type of H with u8arr ?sg' _ _ _ => sg' end in
          let nz := kx_len zs in
          let LF0 := fresh "KXKF" in
          pose proof KXLF as LF0;
          apply (kxk_nil segs E) in H;
          kxk_build GEN segs E zs nz kn KXA LF0 log H IDX;
          clear LF0
      end
  end.
Ltac kxk_keep_ix H IDX := kxk_keep_gix false H IDX.
Ltac kxk_keep H := kxk_keep_gix false H (@nil Z).
(* [comment removed for export] *)
Ltac kxk_keepg_ix H IDX := kxk_keep_gix true H IDX.
Ltac kxk_keepg H := kxk_keep_gix true H (@nil Z).

(* [comment removed for export] *)
Ltac kxk_sbase5 B1 B2 B3 B4 B5 t :=
  lazymatch t with
  | context [B1] => B1 | context [B2] => B2 | context [B3] => B3 | context [B4] => B4 | context [B5] => B5 | _ => t
  end.
Ltac kx_sep_unhide5 B1 B2 B3 B4 B5 :=
  match goal with
  | |- context [?a + _ <= ?b \/ _] =>
      let X := kxk_sbase5 B1 B2 B3 B4 B5 a in let Y := kxk_sbase5 B1 B2 B3 B4 B5 b in unhide_related X Y
  end.
(* [comment removed for export] *)
Ltac kx_lia_sep5 B1 B2 B3 B4 B5 :=
  first [ lia | kx_sep_unhide5 B1 B2 B3 B4 B5; lia | kx_bv_ranges; lia ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac kxk_ix H i' :=
  lazymatch type of H with
  | u8arr _ _ _ (map _ (Zupd ?i _ _)) => replace i with i' in * by lia
  | u8arr _ _ _ (u16s (map _ (Zupd ?i _ _))) => replace i with i' in * by lia
  end.
Ltac kxk_ix2 H i' :=
  lazymatch type of H with
  | u8arr _ _ _ (map _ (Zupd _ _ (Zupd ?i _ _))) => replace i with i' in * by lia
  | u8arr _ _ _ (u16s (map _ (Zupd _ _ (Zupd ?i _ _)))) => replace i with i' in * by lia
  end.
Ltac kxk_ix3 H i' :=
  lazymatch type of H with
  | u8arr _ _ _ (map _ (Zupd _ _ (Zupd _ _ (Zupd ?i _ _)))) => replace i with i' in * by lia
  end.

(* [comment removed for export] *)
Ltac kx_autoFAc AKS STOPS FUEL KZS REGIONS WINDOWS :=
  let ks := eval cbv beta iota delta [app] in KZS in
  kx_autoFA AKS STOPS FUEL ks REGIONS WINDOWS.
Ltac kx_autoFLAc CH AKS STOPS FUEL KZS REGIONS WINDOWS :=
  let ks := eval cbv beta iota delta [app] in KZS in
  kx_autoFLA CH AKS STOPS FUEL ks REGIONS WINDOWS.

(* [comment removed for export] *)
Ltac kx_the_read RD := match goal with |- context [ev ?E ?j] => kx_read_eq j RD end.

(* [comment removed for export] *)
Ltac kx_tidy_run :=
  kx_abs;
  repeat match goal with |- context [ev ?E ?j] => generalize (ev E j); intro end;
  match goal with
  | KXA : atoms_ok _ ?E |- _ => repeat match goal with K : context [E] |- _ => clear K end; try clear E
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac kx_read_reg r RD :=
  let v := StepF.reg_val r in
  lazymatch v with ev ?E ?j => kx_read_eq j RD end.

(* [comment removed for export] *)
Ltac kxk_vl H v' :=
  lazymatch type of H with
  | u8arr _ _ _ (map _ (Zupd _ ?v _)) => replace v with v' in * by (Z.div_mod_to_equations; lia)
  | u8arr _ _ _ (u16s (map _ (Zupd _ ?v _))) => replace v with v' in * by (Z.div_mod_to_equations; lia)
  end.
Ltac kxk_vl2 H v' :=
  lazymatch type of H with
  | u8arr _ _ _ (map _ (Zupd _ _ (Zupd _ ?v _))) => replace v with v' in * by (Z.div_mod_to_equations; lia)
  | u8arr _ _ _ (u16s (map _ (Zupd _ _ (Zupd _ ?v _)))) => replace v with v' in * by (Z.div_mod_to_equations; lia)
  end.

(* [comment removed for export] *)
Ltac kx_setreg r z' :=
  let v := StepF.reg_val r in
  lazymatch v with
  | Z_to_bv 64 z' => idtac
  | Z_to_bv 64 ?z => replace (Z_to_bv 64 z) with (Z_to_bv 64 z') by (f_equal; lia)
  end.
