(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgU.   (* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import StartupTac ArgvEnv RefLayout.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Abbreviation RPH := ImgU.M.phdrs.

(* [comment removed for export] *)
Fixpoint after_last_slash (s : list byte) (i acc : nat) : nat :=
  match s with
  | [] => acc
  | b :: s' => after_last_slash s' (S i) (if bv_eqb b (Z_to_bv 8 47) then S i else acc)
  end.
Definition progname_off (s : list byte) : nat := after_last_slash s 0 0.

Lemma after_last_slash_le : forall s i acc, (acc <= i)%nat ->
  (after_last_slash s i acc <= i + length s)%nat.
Proof.
  induction s as [|c s IH]; intros i acc H; cbn [after_last_slash length]; [lia|].
  etransitivity; [apply IH; destruct (bv_eqb _ _); lia | lia].
Qed.

Lemma progname_off_le : forall s, (progname_off s <= length s)%nat.
Proof. intro s. unfold progname_off. pose proof (after_last_slash_le s 0 0). lia. Qed.

(* [comment removed for export] *)
Lemma sd_bytes_le_cons : forall (b : byte) bs,
  bytes_le_to_Z (b :: bs) = (bv_unsigned b + bytes_le_to_Z bs * 256)%Z.
Proof.
  intros b bs. cbn [bytes_le_to_Z]. pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8)%Z with 256%Z.
  rewrite <- Z.lxor_lor.
  - rewrite Z.add_nocarry_lxor; [reflexivity|].
    apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256%Z with (2 ^ 8)%Z. rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
  - apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256%Z with (2 ^ 8)%Z. rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
Qed.

Lemma sd_le_bytes_roundtrip : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes]. rewrite sd_bytes_le_cons.
  pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8)%Z with 256%Z.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8)%Z with 256%Z.
    replace ((bv_unsigned b + bytes_le_to_Z bs * 256) / 256)%Z with (bytes_le_to_Z bs).
    + exact IH.
    + rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma rdn_of_nth : forall segs m bs (za : Z),
  (0 <= za)%Z -> (za + Z.of_nat (length bs) <= 2^64)%Z ->
  (forall i, (i < length bs)%nat -> m (Z_to_bv 64 (za + Z.of_nat i)) = Some (nth i bs (Z_to_bv 8 0))) ->
  rdn segs m (Z_to_bv 64 za) (length bs) = Some bs.
Proof.
  intros segs m bs. induction bs as [|b bs IH]; intros za Hz Hnw Hpw; [reflexivity|].
  cbn [length] in Hnw, Hpw. cbn [length rdn].
  pose proof (Hpw 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0. cbn [nth] in H0. rewrite H0.
  destruct bs as [|b2 bs2]; [reflexivity|]. cbn [length] in Hnw, Hpw, IH.
  replace (Z_to_bv 64 za + 1)%bv with (Z_to_bv 64 (za + 1)).
  2:{ apply bv_eq. rewrite u_add1 by (rewrite u_Z2bv by lia; lia). rewrite !u_Z2bv by lia. reflexivity. }
  rewrite IH; [reflexivity | lia | cbn [length]; lia |].
  intros i Hi. pose proof (Hpw (S i) ltac:(lia)) as H. cbn [nth] in H.
  replace (za + 1 + Z.of_nat i)%Z with (za + Z.of_nat (S i))%Z by lia. exact H.
Qed.

Section Defs.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable uid : word.   (* [comment removed for export] *)
  Variable hw : word.    (* [comment removed for export] *)
  Variable rdraw : EntryDraw.  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition aux_base : word := Z_to_bv 64 (bv_unsigned sp0 - 368).
  (* [comment removed for export] *)
  Definition argv_w : word := Z_to_bv 64 (bv_unsigned sp0 + 8).
  Definition envp_w : word := Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)).
  Definition auxv_w : word :=
    Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev)).
  Definition argc_w : word := argcN av.
  (* [comment removed for export] *)
  Definition pn_w : word := cat_argv_ptr sp0 av ev 0.
  Definition progname_w : word :=
    Z_to_bv 64 (bv_unsigned pn_w + Z.of_nat (progname_off (nth 0 av []))).
  (* [comment removed for export] *)
  Definition rnd_w : word := at_random_ptr sp0 av ev.
  (* [comment removed for export] *)
  Definition rnd_bytes : list byte := at_random_bytes (ed_random rdraw).
  Definition rnd_lo4 : list byte := firstn 4 rnd_bytes.
  Definition rnd_hi4 : list byte := firstn 4 (skipn 4 rnd_bytes).
  (* [comment removed for export] *)
  Definition ssp_lo : word := Z_to_bv 64 (bytes_le_to_Z rnd_lo4).
  Definition ssp_hi : word := Z_to_bv 64 (bytes_le_to_Z rnd_hi4).
  (* [comment removed for export] *)
  Definition glo : list byte := word_to_le_bytes 4 (v_lw ssp_lo).
  Definition ghi : list byte := word_to_le_bytes 4 (v_lw ssp_hi).
  (* [comment removed for export] *)
  Definition guard_bytes : list byte := nth 0 glo (Z_to_bv 8 0) :: Z_to_bv 8 0 :: skipn 2 glo ++ ghi.
  Definition canary_w : word := Z_to_bv 64 (bytes_le_to_Z guard_bytes).

  (* [comment removed for export] *)
  Definition D_libc : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (fun _ => None)
      (Z_to_bv 64 0xc4f48) (word_to_le_bytes 8 envp_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0xe52b0) (word_to_le_bytes 8 auxv_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0xe5310) (word_to_le_bytes 8 hw))             (* [comment removed for export] *)
      (Z_to_bv 64 0xe52d8) (word_to_le_bytes 8 (Z_to_bv 64 4096))) (* [comment removed for export] *)
      (Z_to_bv 64 0xe52a0) (word_to_le_bytes 8 pn_w))            (* [comment removed for export] *)
      (Z_to_bv 64 0xe5298) (word_to_le_bytes 8 progname_w).      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition J_lsm (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x960d0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argv_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x32634)).

  (* [comment removed for export] *)
  Definition J_aux (Jf : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
      (wbytes Jf aux_base (zeros 304))
      (Z_to_bv 64 (bv_unsigned sp0 - 344)) (word_to_le_bytes 8 (Z_to_bv 64 0x10040)))  (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 336)) (word_to_le_bytes 8 (Z_to_bv 64 56)))       (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 328)) (word_to_le_bytes 8 (Z_to_bv 64 10)))       (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 240)) (word_to_le_bytes 8 hw))                    (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 320)) (word_to_le_bytes 8 (Z_to_bv 64 4096)))     (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 280)) (word_to_le_bytes 8 uid))        (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 272)) (word_to_le_bytes 8 uid))        (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 184)) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 168)) (word_to_le_bytes 8 rnd_w).                  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_tlsA (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0xe5040) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0xe5050) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0xe5048) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0xe52c0) (word_to_le_bytes 8 (Z_to_bv 64 0xe0)))     (* [comment removed for export] *)
      (Z_to_bv 64 0xe52c8) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0xc5028) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0xc5010) (word_to_le_bytes 8 (Z_to_bv 64 0xc5028)))  (* [comment removed for export] *)
      (Z_to_bv 64 0xc4f50) (word_to_le_bytes 8 (Z_to_bv 64 0xc4f50)))  (* [comment removed for export] *)
      (Z_to_bv 64 0xe52a8) [Z_to_bv 8 1])                              (* [comment removed for export] *)
      (Z_to_bv 64 0xc4f78) (word_to_le_bytes 4 (Z_to_bv 64 2)).        (* [comment removed for export] *)

  Definition D_tlsB (tid : word) (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0xc4f70) (word_to_le_bytes 4 tid))                   (* [comment removed for export] *)
      (Z_to_bv 64 0xc4fe8) (word_to_le_bytes 8 (Z_to_bv 64 0xe52e0)))  (* [comment removed for export] *)
      (Z_to_bv 64 0xc4fc8) (word_to_le_bytes 8 (Z_to_bv 64 0xc4fc8)))  (* [comment removed for export] *)
      (Z_to_bv 64 0xc4f58) (word_to_le_bytes 8 (Z_to_bv 64 0xc4f50)))  (* [comment removed for export] *)
      (Z_to_bv 64 0xc4f60) (word_to_le_bytes 8 (Z_to_bv 64 0xc4f50)))  (* [comment removed for export] *)
      (Z_to_bv 64 0xc4f68) (word_to_le_bytes 8 (Z_to_bv 64 0)).        (* [comment removed for export] *)

  Definition D_tls (tid : word) (D : word -> option byte) : word -> option byte :=
    D_tlsB tid (D_tlsA D).

  (* [comment removed for export] *)
  Definition J_tls (J : word -> option byte) (ra s0 s1 s2 s3 s4 s5 : word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 ra))
      (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 s0))
      (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1))
      (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 s2))
      (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 s3))
      (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 s4))
      (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 s5).

  (* [comment removed for export] *)
  Definition D_ssp (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0xe5288) (word_to_le_bytes 4 (v_lw ssp_lo)))   (* [comment removed for export] *)
      (Z_to_bv 64 0xe528c) (word_to_le_bytes 4 (v_lw ssp_hi)))   (* [comment removed for export] *)
      (Z_to_bv 64 0xe5289) [Z_to_bv 8 0])                        (* [comment removed for export] *)
      (Z_to_bv 64 0xc5008) (word_to_le_bytes 8 canary_w).        (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_fd (D : word -> option byte) : word -> option byte :=
    wbytes D (Z_to_bv 64 0xb35a0) [Z_to_bv 8 1].

  (* [comment removed for export] *)
  Definition D_main (tid : word) : word -> option byte := D_fd (D_ssp (D_tls tid D_libc)).


  (* [comment removed for export] *)
  Lemma length_rnd_bytes : length rnd_bytes = 16%nat.
  Proof. unfold rnd_bytes. apply length_at_random_bytes. Qed.

  Lemma ssp_lo_val : bytes_le_to_Z rnd_lo4 = bv_unsigned ssp_lo.
  Proof.
    unfold ssp_lo. pose proof (bytes_le_to_Z_bound rnd_lo4) as Hb. pose proof (bytes_le_to_Z_nonneg rnd_lo4) as H0.
    assert (HL : length rnd_lo4 = 4%nat) by (unfold rnd_lo4; rewrite firstn_length_le; [reflexivity | rewrite length_rnd_bytes; lia]).
    rewrite HL in Hb. change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z in Hb.
    symmetry. apply u_Z2bv; lia.
  Qed.

  Lemma ssp_hi_val : bytes_le_to_Z rnd_hi4 = bv_unsigned ssp_hi.
  Proof.
    unfold ssp_hi. pose proof (bytes_le_to_Z_bound rnd_hi4) as Hb. pose proof (bytes_le_to_Z_nonneg rnd_hi4) as H0.
    assert (HL : length rnd_hi4 = 4%nat) by (unfold rnd_hi4; rewrite firstn_length_le; [reflexivity | rewrite length_skipn, length_rnd_bytes; lia]).
    rewrite HL in Hb. change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z in Hb.
    symmetry. apply u_Z2bv; lia.
  Qed.

  Lemma length_guard_bytes : length guard_bytes = 8%nat.
  Proof. unfold guard_bytes, glo, ghi, word_to_le_bytes. cbn [length app skipn Z_to_le_bytes]. reflexivity. Qed.

  Lemma canary_val : bytes_le_to_Z guard_bytes = bv_unsigned canary_w.
  Proof.
    unfold canary_w. pose proof (bytes_le_to_Z_bound guard_bytes) as Hb. pose proof (bytes_le_to_Z_nonneg guard_bytes) as H0.
    rewrite length_guard_bytes in Hb. change (2 ^ (8 * Z.of_nat 8))%Z with 18446744073709551616%Z in Hb.
    symmetry. apply u_Z2bv; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_guard_raw : forall segs DD,
    rdn segs (wbytes (wbytes (wbytes DD (Z_to_bv 64 0xe5288) glo) (Z_to_bv 64 0xe528c) ghi)
                     (Z_to_bv 64 0xe5289) [Z_to_bv 8 0]) (Z_to_bv 64 0xe5288) 8 = Some guard_bytes.
  Proof.
    intros segs DD.
    pose proof (rdn_of_nth segs (wbytes (wbytes (wbytes DD (Z_to_bv 64 0xe5288) glo) (Z_to_bv 64 0xe528c) ghi)
                     (Z_to_bv 64 0xe5289) [Z_to_bv 8 0]) guard_bytes 0xe5288) as H.
    rewrite length_guard_bytes in H. apply H; [lia | cbn; lia |].
    assert (Lg : length glo = 4%nat) by (unfold glo; apply length_N_to_le_bytes).
    assert (Lh : length ghi = 4%nat) by (unfold ghi; apply length_N_to_le_bytes).
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; [ | | | | | | | | cbn in Hi; lia];
      cbn [Z.of_nat Pos.of_succ_nat Pos.succ];
      match goal with |- _ (Z_to_bv 64 ?e) = _ => let v := eval vm_compute in e in change e with v end;
      repeat first [ rewrite wbytes_inside by (rewrite ?Lg, ?Lh; cbn [length]; rewrite !u_Z2bv by lia; lia)
                   | rewrite wbytes_outside by (rewrite ?Lg, ?Lh; cbn [length]; rewrite !u_Z2bv by lia; lia) ];
      rewrite ?u_Z2bv by lia;
      match goal with |- context [Z.to_nat ?e] => let v := eval vm_compute in (Z.to_nat e) in change (Z.to_nat e) with v end;
      unfold guard_bytes, glo, ghi, word_to_le_bytes; cbn [Z_to_le_bytes nth skipn app]; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma guard_bytes_canary : guard_bytes = word_to_le_bytes 8 canary_w.
  Proof.
    unfold canary_w at 1. unfold word_to_le_bytes. rewrite u_Z2bv.
    - rewrite <- length_guard_bytes. symmetry. apply sd_le_bytes_roundtrip.
    - apply bytes_le_to_Z_nonneg.
    - pose proof (bytes_le_to_Z_bound guard_bytes) as Hb.
      rewrite length_guard_bytes in Hb. change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in Hb. exact Hb.
  Qed.
End Defs.
