(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/FP.v; 365 of its 401 lines of code are new or changed and 355 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import check_braid FloatExact.
Import ListNotations.
Open Scope Z_scope.

Definition CRT_LOOP : Z := 0x13378.
Definition CRT_LOOP_END : Z := 0x13428.

Definition s24 (b0 b1 b2 : byte) : Z :=
  bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2
  - (if 128 <=? bv_unsigned b2 then 16777216 else 0).

Definition cv (pb : Z -> byte) (j : Z) : Z :=
  f32 (s24 (pb (3 * j)) (pb (3 * j + 1)) (pb (3 * j + 2))) (-23).

Lemma unbox_nan_box : forall v : bv 32, unbox_s (nan_box v) = v.
Proof.
  intros v. unfold unbox_s, nan_box, low32.
  pose proof (bv_unsigned_in_range 32 v) as Hv. unfold bv_modulus in Hv.
  assert (E : bv_unsigned (bv_concat 64 (Z_to_bv 32 (-1)) v) = (Z.lor (Z.shiftl (2^32 - 1) 32) (bv_unsigned v))%Z).
  { rewrite bv_concat_unsigned by reflexivity. reflexivity. }
  assert (Hhi : bv_unsigned (bv_extract 32 32 (bv_concat 64 (Z_to_bv 32 (-1)) v)) = Z.ones 32).
  { rewrite bv_extract_unsigned, E. apply Z.bits_inj'. intros i Hi.
    change (bv_wrap 32 ?x) with (x mod 2^32)%Z. change (Z.of_N 32) with 32%Z.
    destruct (Z.lt_ge_cases i 32).
    - rewrite testbit_mod_pow2_low, Z.shiftr_spec, Z.lor_spec, Z.shiftl_spec, Z.ones_spec_low by lia.
      replace (i + 32 - 32)%Z with i by lia. change (2^32 - 1)%Z with (Z.ones 32). rewrite Z.ones_spec_low by lia. reflexivity.
    - rewrite Z.ones_spec_high by lia. rewrite <- Z.land_ones, Z.land_spec, Z.ones_spec_high by lia. apply andb_false_r. }
  rewrite Hhi, Z.eqb_refl.
  apply bv_eq. rewrite bv_extract_unsigned, E, Z.shiftr_0_r. change (bv_wrap 32 ?x) with (x mod 2^32)%Z.
  apply Z.bits_inj'. intros i Hi. destruct (Z.lt_ge_cases i 32).
  - rewrite testbit_mod_pow2_low, Z.lor_spec, Z.shiftl_spec_low by lia. reflexivity.
  - rewrite <- Z.land_ones, Z.land_spec, Z.ones_spec_high, andb_false_r by lia.
    symmetry. destruct (Z.eq_dec (bv_unsigned v) 0) as [->|]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 32%Z; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma low32_nan_box : forall v : bv 32, low32 (nan_box v) = v.
Proof.
  intros v. unfold nan_box, low32. apply bv_eq. rewrite bv_extract_unsigned, bv_concat_unsigned, Z.shiftr_0_r by reflexivity.
  change (bv_wrap 32 ?x) with (x mod 2^32)%Z. pose proof (bv_unsigned_in_range 32 v) as Hv. unfold bv_modulus in Hv.
  change (Z.of_N 32) with 32%Z in *.
  apply Z.bits_inj'. intros i Hi. destruct (Z.lt_ge_cases i 32).
  - rewrite testbit_mod_pow2_low, Z.lor_spec, Z.shiftl_spec_low by lia. reflexivity.
  - rewrite <- Z.land_ones, Z.land_spec, Z.ones_spec_high, andb_false_r by lia.
    symmetry. destruct (Z.eq_dec (bv_unsigned v) 0) as [E|E]; [rewrite E; apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 32%Z; [apply Z.log2_lt_pow2; lia| lia].
Qed.

Lemma le4_nan_box : forall x : bv 32, le4 (nan_box x) = Z_to_le_bytes 4 (bv_unsigned x).
Proof. intros x. rewrite <- store_bytes_4', low32_nan_box. reflexivity. Qed.

Lemma u32_small : forall z, 0 <= z < 2^32 -> bv_unsigned (Z_to_bv 32 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 32) with (2^32). exact Hz. Qed.

Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H. exact H. Qed.

Lemma s24_range : forall b0 b1 b2, -8388608 <= s24 b0 b1 b2 < 8388608.
Proof.
  intros b0 b1 b2. unfold s24. pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2).
  destruct (Z.leb_spec 128 (bv_unsigned b2)); lia.
Qed.

Lemma conv_bytes : forall md (w y : word) b0 b1 b2,
  unbox_s y = Z_to_bv 32 F2M23 ->
  bv_unsigned w mod 2^32 = s24 b0 b1 b2 mod 2^32 ->
  le4 (fmul_s md (fcvt_s_w md w) y) = Z_to_le_bytes 4 (f32 (s24 b0 b1 b2) (-23)).
Proof.
  intros md w y b0 b1 b2 Hy Hw. pose proof (s24_range b0 b1 b2) as R.
  unfold fmul_s, fcvt_s_w.
  rewrite (f32_of_int md (s24 b0 b1 b2) (bv_unsigned w) R Hw). cbn [fst].
  rewrite unbox_nan_box, Hy.
  rewrite (u32_small (f32 (s24 b0 b1 b2) 0)) by (apply f32_range; lia).
  rewrite (u32_small F2M23) by (unfold F2M23; lia).
  rewrite (f32_mul_m23 md _ R). cbn [fst].
  rewrite le4_nan_box, u32_small by (apply f32_range; lia). reflexivity.
Qed.

Lemma lor_low : forall a b n, 0 <= a -> 0 <= b < 2^n -> 0 <= n -> Z.lor (a * 2^n) b = a * 2^n + b.
Proof.
  intros a b n Ha Hb Hn.
  assert (L : Z.land (a * 2^n) b = 0).
  { rewrite <- Z.shiftl_mul_pow2 by lia. apply Z.bits_inj'. intros i Hi.
    rewrite Z.land_spec, Z.bits_0. destruct (Z.ltb_spec i n).
    - rewrite Z.shiftl_spec_low by lia. reflexivity.
    - destruct (Z.eq_dec b 0) as [->|Hb0]; [rewrite Z.bits_0; apply andb_false_r|].
      rewrite (Z.bits_above_log2 b i); [apply andb_false_r | lia |].
      apply Z.lt_le_trans with n; [apply Z.log2_lt_pow2; lia | lia]. }
  rewrite (Z.add_nocarry_lxor _ _ L). apply Z.bits_inj'. intros i Hi.
  rewrite Z.lor_spec, Z.lxor_spec.
  pose proof (f_equal (fun z => Z.testbit z i) L) as Li. cbv beta in Li.
  rewrite Z.land_spec, Z.bits_0 in Li.
  destruct (Z.testbit (a * 2 ^ n) i), (Z.testbit b i); cbn in *; congruence.
Qed.

Lemma sxb_unsigned : forall b : byte,
  bv_unsigned (sxb b) = if bv_unsigned b <? 128 then bv_unsigned b else bv_unsigned b + 18446744073709551360.
Proof.
  intros b. pose proof (byte_range b) as R. unfold sxb. rewrite unsigned_lit_wrap.
  unfold bv_signed, bv_swrap, bv_wrap. change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
  change (2^64) with 18446744073709551616.
  destruct (Z.ltb_spec (bv_unsigned b) 128); cbv iota.
  - rewrite (Z.mod_small (bv_unsigned b + 128) 256) by lia.
    replace (bv_unsigned b + 128 - 128) with (bv_unsigned b) by lia. apply Z.mod_small. lia.
  - rewrite <- (Z.mod_unique (bv_unsigned b + 128) 256 1 (bv_unsigned b - 128)) by lia.
    symmetry. apply (Z.mod_unique _ _ (-1)); lia.
Qed.

Lemma land_hi24 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073692774400 = 2^24 * (x / 2^24).
Proof. intros x Hx. exact (land_hi x 24 Hx ltac:(lia)). Qed.

Lemma comb : forall (b0 b1 b2 : byte) (a2 : word), bv_unsigned a2 = 18446744073692774400 ->
  bv_unsigned (Z_to_bv 64
    (Z.lor
      (bv_unsigned (Z_to_bv 64
        (Z.lor
          (bv_unsigned (Z_to_bv 64
            (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b1)) 8))) (bv_unsigned (zxb b0)))))
          (bv_unsigned (Z_to_bv 64
            (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (sxb b2)) 255))) 16))))))
      (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (sxb b2)) (bv_unsigned a2)))))) mod 2^32
  = s24 b0 b1 b2 mod 2^32.
Proof.
  intros b0 b1 b2 a2 Ha2.
  pose proof (byte_range b0) as R0. pose proof (byte_range b1) as R1. pose proof (byte_range b2) as R2.
  assert (P8 : 2^8 = 256) by reflexivity. assert (P16 : 2^16 = 65536) by reflexivity.
  assert (P24 : 2^24 = 16777216) by reflexivity. assert (P32 : 2^32 = 4294967296) by reflexivity.
  assert (P64 : 2^64 = 18446744073709551616) by reflexivity.
  assert (U0 : bv_unsigned (zxb b0) = bv_unsigned b0) by (unfold zxb; apply unsigned_lit; lia).
  assert (U1 : bv_unsigned (zxb b1) = bv_unsigned b1) by (unfold zxb; apply unsigned_lit; lia).
  rewrite U0, U1, Ha2, sxb_unsigned.
  rewrite (Z.shiftl_mul_pow2 (bv_unsigned b1) 8) by lia.
  rewrite (unsigned_lit (bv_unsigned b1 * 2^8)) by lia.
  rewrite (lor_low (bv_unsigned b1) (bv_unsigned b0) 8) by lia.
  rewrite (unsigned_lit (bv_unsigned b1 * 2^8 + bv_unsigned b0)) by lia.
  unfold s24.
  destruct (Z.ltb_spec (bv_unsigned b2) 128) as [L|L]; cbv iota.
  - replace (Z.land (bv_unsigned b2) 255) with (bv_unsigned b2)
      by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
    rewrite (unsigned_lit (bv_unsigned b2)) by lia.
    rewrite (Z.shiftl_mul_pow2 (bv_unsigned b2) 16) by lia.
    rewrite (unsigned_lit (bv_unsigned b2 * 2^16)) by lia.
    rewrite (Z.lor_comm (bv_unsigned b1 * 2^8 + bv_unsigned b0) (bv_unsigned b2 * 2^16)).
    rewrite (lor_low (bv_unsigned b2) (bv_unsigned b1 * 2^8 + bv_unsigned b0) 16) by lia.
    rewrite (unsigned_lit (bv_unsigned b2 * 2^16 + (bv_unsigned b1 * 2^8 + bv_unsigned b0))) by lia.
    rewrite land_hi24 by lia. rewrite (Z.div_small (bv_unsigned b2) (2^24)) by lia. rewrite Z.mul_0_r.
    rewrite (unsigned_lit 0) by lia. rewrite Z.lor_0_r.
    rewrite unsigned_lit by lia.
    rewrite (proj2 (Z.leb_gt 128 (bv_unsigned b2))) by lia. cbv iota.
    rewrite ?P8, ?P16, ?P24, ?P32. Z.div_mod_to_equations. lia.
  - assert (E255 : Z.land (bv_unsigned b2 + 18446744073709551360) 255 = bv_unsigned b2).
    { change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite P8.
      symmetry. apply (Z.mod_unique _ _ 72057594037927935); lia. }
    rewrite E255.
    rewrite (unsigned_lit (bv_unsigned b2)) by lia.
    rewrite (Z.shiftl_mul_pow2 (bv_unsigned b2) 16) by lia.
    rewrite (unsigned_lit (bv_unsigned b2 * 2^16)) by lia.
    rewrite (Z.lor_comm (bv_unsigned b1 * 2^8 + bv_unsigned b0) (bv_unsigned b2 * 2^16)).
    rewrite (lor_low (bv_unsigned b2) (bv_unsigned b1 * 2^8 + bv_unsigned b0) 16) by lia.
    rewrite (unsigned_lit (bv_unsigned b2 * 2^16 + (bv_unsigned b1 * 2^8 + bv_unsigned b0))) by lia.
    assert (D : (bv_unsigned b2 + 18446744073709551360) / 2^24 = 1099511627775).
    { rewrite P24. symmetry.
      apply (Z.div_unique _ _ _ (bv_unsigned b2 + 18446744073709551360 - 1099511627775 * 16777216)); lia. }
    rewrite land_hi24 by lia. rewrite D. clear D.
    rewrite (unsigned_lit (2^24 * 1099511627775)) by lia.
    rewrite (Z.mul_comm (2^24) 1099511627775).
    rewrite (Z.lor_comm _ (1099511627775 * 2^24)).
    rewrite (lor_low 1099511627775 _ 24) by lia.
    rewrite unsigned_lit by lia.
    rewrite (proj2 (Z.leb_le 128 (bv_unsigned b2))) by lia. cbv iota.
    rewrite ?P8, ?P16, ?P24, ?P32. Z.div_mod_to_equations. lia.
Qed.

Local Ltac fct := try unfold wa; norm;
  first [ reflexivity | rng | (rewrite ?unsigned_lit_wrap; zb_fold_lits; Z.div_mod_to_equations; lia) ].
Local Ltac word_eq_tac ::= first [ exact eq_refl | f_equal; lia | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia
  | (norm; first [ reflexivity | f_equal; lia | lia ]) ].

Section Loops.
Variables (ra sp gp tp s1 s2 s6 s8 s9 s10 s11 t4 t5 t6 : word) (m0 : word -> option byte) (pb : Z -> byte)
  (P Q pcm nch ns : Z).
Hypothesis HN : 2 <= nch <= 127.
Hypothesis HNS : 1 <= ns <= 12.
Hypothesis HB : 3 * nch * ns <= 1440.
Hypothesis HP0 : 0 < P.
Hypothesis HP1 : P + 4 * nch * ns < 2^63.
Hypothesis HQ0 : 0 < Q.
Hypothesis HQ1 : Q + 8 * nch < 2^63.
Hypothesis HC0 : 0 < pcm.
Hypothesis HC1 : pcm + 3 * nch * ns < 2^63.
Hypothesis PB : forall i, 0 <= i < 3 * nch * ns -> mrd rsegs m0 (wa (pcm + i)) = Some (pb i).
Hypothesis WP : wr_at rsegs m0 P (4 * nch * ns).
Hypothesis WQ : wr_at rsegs m0 Q (8 * nch).
Hypothesis DPQ : P + 4 * nch * ns <= Q \/ Q + 8 * nch <= P.
Hypothesis DPC : P + 4 * nch * ns <= pcm \/ pcm + 3 * nch * ns <= P.
Hypothesis DQC : Q + 8 * nch <= pcm \/ pcm + 3 * nch * ns <= Q.
Variable G : machine_state -> Prop.

Definition crt_W : list ivl := [(P, P + 4 * nch * ns); (Q, Q + 8 * nch)].

Definition crt_inv (m : word -> option byte) (kp kq : Z) : Prop :=
  munch crt_W m0 m /\ wmono rsegs m0 m /\
  (forall j, 0 <= j < kp -> bytes_at rsegs m (P + 4 * j) (Z_to_le_bytes 4 (cv pb j))) /\
  (forall c, 0 <= c < kq -> bytes_at rsegs m (Q + 8 * c) (le8 (Z_to_bv 64 (P + 4 * (c * ns))))).

Lemma crt_nn : 0 < nch * ns <= 480.
Proof. split; [apply Z.mul_pos_pos; lia | lia]. Qed.

Lemma crt_inv_init : crt_inv m0 0 0.
Proof.
  split; [apply munch_refl|]. split; [apply wmono_refl|].
  split; intros; exfalso; lia.
Qed.

Lemma crt_inv_pcm : forall m kp kq i, crt_inv m kp kq -> 0 <= i < 3 * nch * ns -> mrd rsegs m (wa (pcm + i)) = Some (pb i).
Proof.
  intros m kp kq i (MU & _) Hi. pose proof crt_nn. pose proof (PB i Hi) as E. unfold munch in MU. unfold mrd in *.
  rewrite MU; [exact E|]. unfold crt_W. rewrite wa_unsigned by lia. cbn [outside].
  split; [lia | split; [lia | exact I]].
Qed.

Lemma crt_stP : forall m k kq (t0 : word), crt_inv m k kq -> 0 <= k < nch * ns -> bv_unsigned t0 = P + 4 * k ->
  store_ok rsegs m t0 4 = true.
Proof.
  intros m k kq t0 (_ & WM & _) Hk Ht. pose proof crt_nn.
  pose proof (wr_at_transport rsegs m0 m P (4 * nch * ns) WP WM) as W1.
  rewrite <- (wa_of_var t0 (P + 4 * k) Ht).
  apply (wr_at_store_ok rsegs m P (4 * nch * ns) (4 * k) 4 W1); lia.
Qed.

Lemma crt_stQ : forall m kp c, crt_inv m kp c -> 0 <= c < nch -> store_ok rsegs m (wa (Q + 8 * c)) 8 = true.
Proof.
  intros m kp c (_ & WM & _) Hc.
  pose proof (wr_at_transport rsegs m0 m Q (8 * nch) WQ WM) as W1.
  apply (wr_at_store_ok rsegs m Q (8 * nch) (8 * c) 8 W1); lia.
Qed.

Lemma crt_inv_P : forall m k kq (a : word) bs, crt_inv m k kq -> 0 <= k < nch * ns -> 0 <= kq <= nch ->
  bv_unsigned a = P + 4 * k -> bs = Z_to_le_bytes 4 (cv pb k) -> crt_inv (write_to_mem m a bs) (k + 1) kq.
Proof.
  intros m k kq a bs (MU & WM & HPd & HQd) Hk Hkq Ha ->. pose proof crt_nn.
  rewrite <- (wa_of_var a (P + 4 * k) Ha).
  split; [|split; [|split]].
  - apply munch_write; [exact MU | lia | rewrite length_Z_to_le_bytes; lia |].
    unfold crt_W. cbn [inside]. rewrite length_Z_to_le_bytes. lia.
  - apply wmono_write. exact WM.
  - intros j Hj. destruct (Z.eq_dec j k) as [->|Hne].
    + apply bytes_at_write_same; [lia | rewrite length_Z_to_le_bytes; lia].
    + apply bytes_at_write_other; [apply HPd; lia | lia | rewrite length_Z_to_le_bytes; lia |].
      rewrite !length_Z_to_le_bytes. lia.
  - intros c Hc. apply bytes_at_write_other; [apply HQd; lia | lia | rewrite length_Z_to_le_bytes; lia |].
    rewrite length_Z_to_le_bytes, length_le8. lia.
Qed.

Lemma crt_inv_Q : forall m kp c (a v : word), crt_inv m kp c -> 0 <= c < nch -> 0 <= kp <= nch * ns ->
  bv_unsigned a = Q + 8 * c -> bv_unsigned v = P + 4 * (c * ns) -> crt_inv (write_to_mem m a (le8 v)) kp (c + 1).
Proof.
  intros m kp c a v (MU & WM & HPd & HQd) Hc Hkp Ha Hv. pose proof crt_nn.
  rewrite <- (wa_of_var a (Q + 8 * c) Ha), <- (wa_of_var v (P + 4 * (c * ns)) Hv).
  split; [|split; [|split]].
  - apply munch_write; [exact MU | lia | rewrite length_le8; lia |].
    unfold crt_W. cbn [inside]. rewrite length_le8. lia.
  - apply wmono_write. exact WM.
  - intros j Hj. apply bytes_at_write_other; [apply HPd; lia | lia | rewrite length_le8; lia |].
    rewrite length_le8, length_Z_to_le_bytes. lia.
  - intros c' Hc'. destruct (Z.eq_dec c' c) as [->|Hne].
    + apply bytes_at_write_same; [lia | rewrite length_le8; lia].
    + apply bytes_at_write_other; [apply HQd; lia | lia | rewrite length_le8; lia |].
      rewrite !length_le8. lia.
Qed.

Local Abbreviation ST pc t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 F fc m :=
  (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 P) s1 a0 a1 a2 a3 a4 a5 a6 a7
           s2 (Z_to_bv 64 Q) (Z_to_bv 64 ns) (Z_to_bv 64 nch) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Lemma crt_body : forall k kq (t0 t1 t2 t3 a0 a1 a2 a3 a4 a5 a6 a7 s7 : word) (Fh : bvmap 5 word) (fc : bv 32) m,
  0 <= k < nch * ns -> 0 <= kq <= nch ->
  bv_unsigned t0 = P + 4 * k -> bv_unsigned a7 = pcm + 2 + 3 * k ->
  bv_unsigned a2 = 18446744073692774400 ->
  unbox_s (reg_get Fh (Z_to_bv 5 15)) = Z_to_bv 32 F2M23 ->
  frm0 fc -> crt_inv m k kq ->
  (forall (t0' t1' t2' t3' a7' v : word) (fc' : bv 32) m',
     bv_unsigned t0' = P + 4 * (k + 1) -> bv_unsigned a7' = pcm + 2 + 3 * (k + 1) ->
     frm0 fc' -> crt_inv m' (k + 1) kq ->
     evt rsegs G (ST 0x13414 t0' t1' t2' a0 a1 a2 a3 a4 a5 a6 a7' s7 t3' (bvmap_set (Z_to_bv 5 14) v Fh) fc' m')) ->
  evt rsegs G (ST 0x133d8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 Fh fc m).
Proof.
  intros k kq t0 t1 t2 t3 a0 a1 a2 a3 a4 a5 a6 a7 s7 Fh fc m Hk Hkq Ht0 Ha7 Ha2 H5 Hfc Hinv K.
  pose proof crt_nn.
  pose proof (crt_inv_pcm m k kq (3 * k) Hinv ltac:(lia)) as M0.
  pose proof (crt_inv_pcm m k kq (3 * k + 1) Hinv ltac:(lia)) as M1.
  pose proof (crt_inv_pcm m k kq (3 * k + 2) Hinv ltac:(lia)) as M2.
  pose proof (rdw m a7 (-2) _ _ M0 ltac:(lia)) as R0.
  pose proof (rdw m a7 (-1) _ _ M1 ltac:(lia)) as R1.
  pose proof (rdw0 m a7 _ _ M2 ltac:(lia)) as R2.
  pose proof (crt_stP m k kq t0 Hinv Hk Ht0) as HSt.
  do 15 step.
  apply K; [fct | fct | assumption |].
  eapply crt_inv_P; [exact Hinv | lia | lia | exact Ht0 |].
  unfold cv. apply conv_bytes; [exact H5 | exact (comb _ _ _ a2 Ha2)].
Qed.

Lemma crt_inner : forall ch (a0 a1 a2 a3 a4 a5 a6 s7 : word),
  0 <= ch < nch -> bv_unsigned a6 = P + 4 * ns * (ch + 1) -> bv_unsigned a2 = 18446744073692774400 ->
  forall n k (t0 t1 t2 t3 a7 : word) (Fh : bvmap 5 word) (fc : bv 32) m,
  ch * ns <= k -> k + Z.of_nat (S n) = (ch + 1) * ns ->
  bv_unsigned t0 = P + 4 * k -> bv_unsigned a7 = pcm + 2 + 3 * k ->
  unbox_s (reg_get Fh (Z_to_bv 5 15)) = Z_to_bv 32 F2M23 ->
  frm0 fc -> crt_inv m k (ch + 1) ->
  (forall (t0' t1' t2' t3' a7' v : word) (fc' : bv 32) m',
     frm0 fc' -> crt_inv m' ((ch + 1) * ns) (ch + 1) ->
     evt rsegs G (ST 0x13418 t0' t1' t2' a0 a1 a2 a3 a4 a5 a6 a7' s7 t3' (bvmap_set (Z_to_bv 5 14) v Fh) fc' m')) ->
  evt rsegs G (ST 0x133d8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 Fh fc m).
Proof.
  intros ch a0 a1 a2 a3 a4 a5 a6 s7 Hch Ha6 Ha2 n.
  pose proof crt_nn.
  assert (B1 : (ch + 1) * ns <= nch * ns) by (apply Z.mul_le_mono_nonneg_r; lia).
  induction n as [|n IH]; intros k t0 t1 t2 t3 a7 Fh fc m Hk0 Hkn Ht0 Ha7 H5 Hfc Hinv K.
  - apply (crt_body k (ch + 1) t0 t1 t2 t3 a0 a1 a2 a3 a4 a5 a6 a7 s7 Fh fc m); try assumption; [lia | lia |].
    intros t0' t1' t2' t3' a7' v fc' m' Ht0' Ha7' Hfc' Hinv'.
    step. take false.
    apply K; [exact Hfc' |]. replace ((ch + 1) * ns) with (k + 1) by lia. exact Hinv'.
  - apply (crt_body k (ch + 1) t0 t1 t2 t3 a0 a1 a2 a3 a4 a5 a6 a7 s7 Fh fc m); try assumption; [lia | lia |].
    intros t0' t1' t2' t3' a7' v fc' m' Ht0' Ha7' Hfc' Hinv'.
    step. take true.
    apply (IH (k + 1) t0' t1' t2' t3' a7' (bvmap_set (Z_to_bv 5 14) v Fh) fc' m');
      [lia | lia | exact Ht0' | exact Ha7' | | exact Hfc' | exact Hinv' |].
    + rewrite freg_get_other by reflexivity. exact H5.
    + intros t0'' t1'' t2'' t3'' a7'' v' fc'' m'' Hfc'' Hinv''.
      rewrite bvmap_set_set_same. apply K; assumption.
Qed.

Lemma crt_outer : forall n ch (t0 t1 t2 t3 a0 a1 a2 a3 a4 a5 a6 a7 s7 : word) (Fh : bvmap 5 word) (fc : bv 32) m,
  0 <= ch -> ch + Z.of_nat (S n) = nch ->
  bv_unsigned a0 = ch -> bv_unsigned a1 = 4 * ns -> bv_unsigned a2 = 18446744073692774400 ->
  bv_unsigned a3 = 3 * ns -> bv_unsigned a4 = 4 * ns ->
  bv_unsigned a5 = P + 4 * ns * ch -> bv_unsigned s7 = pcm + 2 + 3 * ns * ch ->
  unbox_s (reg_get Fh (Z_to_bv 5 15)) = Z_to_bv 32 F2M23 ->
  frm0 fc -> crt_inv m (ch * ns) ch ->
  (forall (t0' t1' t2' t3' a0' a1' a2' a3' a4' a5' a6' a7' s7' v : word) (fc' : bv 32) m',
     bv_unsigned s7' = pcm + 2 + 3 * nch * ns -> frm0 fc' -> crt_inv m' (nch * ns) nch ->
     evt rsegs G (ST 0x13428 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' (bvmap_set (Z_to_bv 5 14) v Fh) fc' m')) ->
  evt rsegs G (ST 0x133a8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 Fh fc m).
Proof.
  intros n. induction n as [|n IH];
    intros ch t0 t1 t2 t3 a0 a1 a2 a3 a4 a5 a6 a7 s7 Fh fc m Hc0 Hcn Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 Hs7 H5 Hfc Hinv K.
  all: assert (Hch : 0 <= ch < nch) by lia.
  all: pose proof crt_nn.
  all: assert (B0 : 0 <= ch * ns) by (apply Z.mul_nonneg_nonneg; lia).
  all: assert (B1 : (ch + 1) * ns <= nch * ns) by (apply Z.mul_le_mono_nonneg_r; lia).
  all: pose proof (crt_stQ m (ch * ns) ch Hinv Hch) as HSt.
  all: do 6 step.
  all: step; take false.
  all: do 5 step.
  all: eapply (crt_inner ch) with (n := Z.to_nat (ns - 1)) (k := ch * ns);
         [ exact Hch | fct | exact Ha2 | lia | lia | fct | fct | exact H5 | exact Hfc | | ].
  1, 3: eapply crt_inv_Q; [exact Hinv | lia | lia | fct | fct].
  - intros t0' t1' t2' t3' a7' v fc' m' Hfc' Hinv'.
    assert (Hn1 : ch + 1 = nch) by lia.
    assert (E2 : nch * ns = ch * ns + ns) by (rewrite <- Hn1; ring).
    do 3 step. step. take false.
    apply K; [fct | exact Hfc' |]. rewrite Hn1 in Hinv'. exact Hinv'.
  - intros t0' t1' t2' t3' a7' v fc' m' Hfc' Hinv'.
    do 3 step. step. take true.
    apply (IH (ch + 1)); [lia | lia | fct | first [exact Ha1 | fct] | exact Ha2 | first [exact Ha3 | fct]
                         | first [exact Ha4 | fct] | fct | fct | | exact Hfc' | exact Hinv' |].
    + rewrite freg_get_other by reflexivity. exact H5.
    + intros t0'' t1'' t2'' t3'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' s7'' v' fc'' m'' Hs7'' Hfc'' Hinv''.
      rewrite bvmap_set_set_same. apply K; assumption.
Qed.

End Loops.

Theorem crt_convert_loop :
  forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (pb : Z -> byte) (P Q pcm nch ns : Z),
    2 <= nch <= 127 -> 1 <= ns <= 12 -> 3 * nch * ns <= 1440 ->
    0 < P -> P + 4 * nch * ns < 2^63 ->
    0 < Q -> Q + 8 * nch < 2^63 ->
    0 < pcm -> pcm + 3 * nch * ns < 2^63 ->
    (forall i, 0 <= i < 3 * nch * ns -> mrd rsegs m (wa (pcm + i)) = Some (pb i)) ->
    wr_at rsegs m P (4 * nch * ns) ->
    wr_at rsegs m Q (8 * nch) ->
    P + 4 * nch * ns <= Q \/ Q + 8 * nch <= P ->
    P + 4 * nch * ns <= pcm \/ pcm + 3 * nch * ns <= P ->
    Q + 8 * nch <= pcm \/ pcm + 3 * nch * ns <= Q ->
    frm0 fc ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' t3' a0' a1' a2' a3' a4' a5' a6' a7' v4 v5 : word) (fc' : bv 32) m',
         ms' = MS (mkR ra sp gp tp t0' t1' t2' (Z_to_bv 64 P) s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 (Z_to_bv 64 Q) (Z_to_bv 64 ns) (Z_to_bv 64 nch) s6 (Z_to_bv 64 (pcm + 2 + 3 * nch * ns))
                       s8 s9 s10 s11 t3' t4 t5 t6)
                  (bvmap_set (Z_to_bv 5 14) v4 (bvmap_set (Z_to_bv 5 15) v5 F))
                  (Z_to_bv 64 CRT_LOOP_END) fc' None m' (seg_rom rsegs) /\
         frm0 fc' /\
         munch [(P, P + 4 * nch * ns); (Q, Q + 8 * nch)] m m' /\
         wmono rsegs m m' /\
         (forall ch, 0 <= ch < nch ->
            bytes_at rsegs m' (Q + 8 * ch) (le8 (Z_to_bv 64 (P + 4 * (ch * ns))))) /\
         (forall ch s, 0 <= ch < nch -> 0 <= s < ns ->
            bytes_at rsegs m' (P + 4 * (ch * ns + s)) (Z_to_le_bytes 4 (cv pb (ch * ns + s)))))
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 P) s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 (Z_to_bv 64 Q) (Z_to_bv 64 ns) (Z_to_bv 64 nch) s6 (Z_to_bv 64 pcm) s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CRT_LOOP) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m pb P Q pcm nch ns
    HN HNS HB HP0 HP1 HQ0 HQ1 HC0 HC1 PB WP WQ DPQ DPC DQC Hfc.
  assert (NN0 : 0 < nch * ns <= 480) by (split; [apply Z.mul_pos_pos; lia | lia]).
  unfold CRT_LOOP.
  step. take false.
  do 11 step.
  eapply crt_outer with (m0 := m) (pb := pb) (pcm := pcm) (n := Z.to_nat (nch - 1)) (ch := 0).
  all: lazymatch goal with
       | |- forall _ : word, _ => idtac
       | |- unbox_s _ = _ => rewrite freg_get_same by reflexivity; apply bv_eq; vm_compute; reflexivity
       | _ => first [ assumption | apply crt_inv_init | lia | fct ]
       end.
  intros t0' t1' t2' t3' a0' a1' a2' a3' a4' a5' a6' a7' s7' v fc' m' Hs7 Hfc' Hinv'.
  apply evt_done. destruct Hinv' as (MU & WM & HPd & HQd).
  exists t0', t1', t2', t3', a0', a1', a2', a3', a4', a5', a6', a7', v, (Z_to_bv 64 18446744070286999552), fc', m'.
  split; [|split; [exact Hfc' | split; [exact MU | split; [exact WM | split; [exact HQd |]]]]].
  - rewrite <- (wa_of_var s7' _ Hs7). reflexivity.
  - intros ch s Hch Hs. apply HPd.
    assert (0 <= ch * ns) by (apply Z.mul_nonneg_nonneg; lia).
    assert ((ch + 1) * ns <= nch * ns) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
Qed.
