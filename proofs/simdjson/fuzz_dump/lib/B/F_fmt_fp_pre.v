(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Arr.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim SoftFloat FmtFp.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import FmtFp_split FmtFp_facts.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import F_memset F_memcpy F_fwritex F_pad F_frexpl F_fmt_fp_lib F_fmt_fp_calls.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Record midK := MidK { K_pad : list byte; K_jk40 : list byte; K_jk8 : list byte; K_jk3 : list byte; K_jk12 : list byte; K_jk37 : list byte;
                      K_p1 : Z; K_prefix : Z; K_pl : Z; K_plz : Z; K_pfx : Z; K_Ft : bvmap 5 word }.

Lemma wfile_frame_below : forall m Fp fl0 j1 j2 lbfw B c jk (a : Z) bs,
  wfile m Fp fl0 j1 j2 lbfw B c jk -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= Fp)%Z -> (a + Z.of_nat (length bs) <= B)%Z ->
  wfile (write_to_mem m (wa a) bs) Fp fl0 j1 j2 lbfw B c jk.
Proof.
  intros m Fp fl0 j1 j2 lbfw B c jk a bs (FC & BUF & REST) Ha HF HB.
  pose proof (rw_cells_bound _ _ _ _ FC) as B1. pose proof (rw_cells_bound _ _ _ _ BUF) as B2.
  split; [|split; [|exact REST]].
  - apply rw_cells_frame; [exact FC | lia | lia | right; lia].
  - apply rw_cells_frame; [exact BUF | lia | lia | right; lia].
Qed.
Lemma wfile_transport_below : forall W m m' Fp fl0 j1 j2 lbfw B c jk,
  wfile m Fp fl0 j1 j2 lbfw B c jk -> munch W m m' -> wmono bsegs m m' ->
  (forall iv, In iv W -> (snd iv <= Fp /\ snd iv <= B)%Z) ->
  wfile m' Fp fl0 j1 j2 lbfw B c jk.
Proof.
  intros W m m' Fp fl0 j1 j2 lbfw B c jk (FC & BUF & REST) MU WM HW.
  assert (D : forall A n, (Fp <= A)%Z \/ (B <= A)%Z -> disjoint_from W A n).
  { intros A n HA. clear -HW HA. induction W as [|[lo hi] W IH]; [exact I|]. cbn. split.
    - specialize (HW (lo, hi) (or_introl eq_refl)). cbn in HW. lia.
    - apply IH. intros iv Hiv. apply HW. right. exact Hiv. }
  split; [|split; [|exact REST]].
  - eapply rw_cells_transport; [exact FC | exact MU | exact WM | apply D; left; lia].
  - eapply rw_cells_transport; [exact BUF | exact MU | exact WM | apply D; right; lia].
Qed.

Ltac transport_chunks segs m a bs ::=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wfile m ?Fp ?fl0 ?j1 ?j2 ?lbfw ?B ?c ?jk |- _ =>
      first [ apply (wfile_frame_below m Fp fl0 j1 j2 lbfw B c jk a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end.

Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wfile m ?Fp ?fl0 ?j1 ?j2 ?lbfw ?B ?c ?jk |- _ =>
      first [ apply (wfile_transport_below W m m' Fp fl0 j1 j2 lbfw B c jk) in H;
              [ | exact MU | exact WM | let iv := fresh "iv" in let Hiv := fresh "Hiv" in
                                       intros iv Hiv; cbn [In] in Hiv; decompose [or] Hiv; try subst iv; cbn [snd]; first [lia | contradiction] ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ unfold sub_fp; cbn [outside]; intros; slia | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

Ltac transport_chunks_extra_wfile m a bs n Hn Ha Hl :=
  repeat match goal with
  | H : wfile m ?Fp ?fl0 ?j1 ?j2 ?lbfw ?B ?c ?jk |- _ =>
      first [ apply (wfile_frame_below m Fp fl0 j1 j2 lbfw B c jk a bs) in H;
              [ | exact Ha | rewrite Hn; tslia | rewrite Hn; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end.
Ltac transport_call_extra_wfile segs W m m' MU WM :=
  repeat match goal with
  | H : wfile m ?Fp ?fl0 ?j1 ?j2 ?lbfw ?B ?c ?jk |- _ =>
      first [ apply (wfile_transport_below W m m' Fp fl0 j1 j2 lbfw B c jk) in H;
              [ | exact MU | exact WM | let iv := fresh "iv" in let Hiv := fresh "Hiv" in
                                       intros iv Hiv; cbn [In] in Hiv; decompose [or] Hiv; try subst iv; cbn [snd]; first [lia | contradiction] ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  end.

Lemma div9_magic : forall x, (0 <= x < 2^33)%Z -> (x * 954437177 / 2^33 = x / 9)%Z.
Proof.
  intros x Hx. symmetry.
  apply (Z.div_unique _ _ _ (x * 954437177 - 2^33 * (x / 9))%Z); [|lia].
  left. pose proof (Z.div_mod x 9 ltac:(lia)) as E. pose proof (Z.mod_pos_bound x 9 ltac:(lia)) as R.
  set (q := (x / 9)%Z) in *. set (rr := (x mod 9)%Z) in *. clearbody q rr. subst x. lia.
Qed.

Lemma need_magic : forall x, (0 <= x < 2^31)%Z ->
  (Z.shiftr (Z.land (Z.shiftr (Z.land (Z.shiftl x 32) 18446744073709551615 * 4099276461301563392) 64) 18446744073709551615) 33 = x / 9)%Z.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
  change (2^32)%Z with 4294967296%Z. change (2^64)%Z with 18446744073709551616%Z.
  rewrite (land_W64_small (x * 4294967296)) by lia.
  replace (x * 4294967296 * 4099276461301563392)%Z with ((x * 954437177) * 18446744073709551616)%Z by lia.
  rewrite Z.div_mul by lia. rewrite land_W64_small by lia. apply div9_magic. lia.
Qed.

Lemma dn_mask_eq : forall sh, (1 <= sh <= 9)%Z ->
  Z.lxor (Z.land (bv_swrap 32 (Z.shiftl 18446744073709551615 sh)) 18446744073709551615) 18446744073709551615 = (2^sh - 1)%Z.
Proof.
  intros sh Hsh.
  assert (C : (sh = 1 \/ sh = 2 \/ sh = 3 \/ sh = 4 \/ sh = 5 \/ sh = 6 \/ sh = 7 \/ sh = 8 \/ sh = 9)%Z) by lia.
  destruct C as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | -> ]]]]]]]]; reflexivity.
Qed.

Lemma dn_q9_eq : forall sh, (1 <= sh <= 9)%Z -> bv_swrap 32 (Z.shiftr 1000000000 sh) = Z.shiftr 1000000000 sh.
Proof.
  intros sh Hsh.
  assert (C : (sh = 1 \/ sh = 2 \/ sh = 3 \/ sh = 4 \/ sh = 5 \/ sh = 6 \/ sh = 7 \/ sh = 8 \/ sh = 9)%Z) by lia.
  destruct C as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | -> ]]]]]]]]; reflexivity.
Qed.

Lemma pow2_sh_range : forall sh, (1 <= sh <= 9)%Z -> (2 <= 2^sh <= 512)%Z.
Proof.
  intros sh Hsh. split.
  - change 2%Z with (2^1)%Z at 1. apply Z.pow_le_mono_r; lia.
  - change 512%Z with (2^9)%Z. apply Z.pow_le_mono_r; lia.
Qed.

Lemma q9_range : forall sh, (1 <= sh <= 9)%Z ->
  (0 < Z.shiftr 1000000000 sh /\ Z.shiftr 1000000000 sh * 2^sh <= 1000000000)%Z.
Proof.
  intros sh Hsh. rewrite Z.shiftr_div_pow2 by lia. pose proof (pow2_sh_range sh Hsh). split.
  - apply Z.div_str_pos. lia.
  - rewrite Z.mul_comm. apply Z.mul_div_le. lia.
Qed.

Lemma wrap32_sx32 : forall ww : word, bv_wrap 32 (bv_unsigned (sx32 ww)) = (bv_unsigned ww mod 4294967296)%Z.
Proof.
  intros ww. unfold sx32. rewrite unsigned_lit_wrap, swrap32_eq. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (2^64)%Z with 18446744073709551616%Z.
  pose proof (bv_unsigned_in_range 64 ww) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in R.
  Z.div_mod_to_equations. lia.
Qed.

Lemma swrap32_shr_small : forall v sh, (0 <= v < 4294967296)%Z -> (1 <= sh <= 9)%Z ->
  bv_swrap 32 (Z.shiftr v sh) = Z.shiftr v sh.
Proof.
  intros v sh Hv Hsh. rewrite Z.shiftr_div_pow2 by lia. pose proof (pow2_sh_range sh Hsh).
  assert (R : (0 <= v / 2^sh < 2147483648)%Z).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia. }
  set (X := (v / 2^sh)%Z) in *. clearbody X. rewrite swrap32_eq. Z.div_mod_to_equations. lia.
Qed.

Lemma shr_small_range : forall v sh, (0 <= v < 4294967296)%Z -> (1 <= sh <= 9)%Z -> (0 <= Z.shiftr v sh < 2147483648)%Z.
Proof.
  intros v sh Hv Hsh. rewrite Z.shiftr_div_pow2 by lia. pose proof (pow2_sh_range sh Hsh).
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

Lemma land_sx32_mask : forall (ww : word) sh, (1 <= sh <= 32)%Z ->
  Z.land (bv_unsigned (sx32 ww)) (2^sh - 1) = ((bv_unsigned ww mod 4294967296) mod 2^sh)%Z.
Proof.
  intros ww sh Hsh.
  replace (2^sh - 1)%Z with (Z.ones sh) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia).
  rewrite Z.land_ones by lia.
  assert (D : (2^sh | 4294967296)%Z).
  { exists (2^(32 - sh))%Z. change 4294967296%Z with (2^32)%Z. rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  rewrite <- (Z.mod_mod_divide (bv_unsigned (sx32 ww)) 4294967296 (2^sh) D).
  f_equal. unfold sx32. rewrite unsigned_lit_wrap, swrap32_eq. change (2^64)%Z with 18446744073709551616%Z.
  pose proof (bv_unsigned_in_range 64 ww) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in R.
  Z.div_mod_to_equations. lia.
Qed.

Lemma rm_q9_small : forall v sh, (0 <= v)%Z -> (1 <= sh <= 9)%Z ->
  (0 <= (v mod 2^sh) * Z.shiftr 1000000000 sh < 1000000000)%Z.
Proof.
  intros v sh Hv Hsh. pose proof (q9_range sh Hsh) as [Q1 Q2]. pose proof (pow2_sh_range sh Hsh).
  pose proof (Z.mod_pos_bound v (2^sh) ltac:(lia)) as R.
  set (P := (2^sh)%Z) in *. set (q := Z.shiftr 1000000000 sh) in *. clearbody P q. nia.
Qed.

Lemma dn_carry_eq : forall v sh, (0 <= v)%Z -> (1 <= sh <= 9)%Z ->
  u32 (Z.shiftr 1000000000 sh * Z.land v (Z.shiftl 1 sh - 1)) = ((v mod 2^sh) * Z.shiftr 1000000000 sh)%Z
  /\ (0 <= (v mod 2^sh) * Z.shiftr 1000000000 sh < 1000000000)%Z.
Proof.
  intros v sh Hv Hsh. pose proof (rm_q9_small v sh Hv Hsh) as R.
  rewrite Z.shiftl_1_l. replace (2^sh - 1)%Z with (Z.ones sh) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia).
  rewrite Z.land_ones by lia. split; [|exact R]. unfold u32. rewrite Z.mul_comm. apply Z.mod_small. lia.
Qed.

Lemma seqz4_eq : forall ws i v, wval ws i = v ->
  Z.shiftl (Z.b2z (bv_unsigned (sx32 (wnth ws i)) <? 1)) 2 = (if v =? 0 then 4 else 0)%Z.
Proof.
  intros ws i v Hv. pose proof (zr_word (sx32 (wnth ws i)) : (0 <= _ < 2^64)%Z) as R. unfold wval in Hv.
  destruct (Z.eqb_spec v 0) as [E|E].
  - subst v. rewrite (proj2 (sx32_zero (wnth ws i)) E). reflexivity.
  - assert (bv_unsigned (sx32 (wnth ws i)) <> 0%Z) by (apply (proj2 (sx32_nonzero _)); lia).
    destruct (Z.ltb_spec0 (bv_unsigned (sx32 (wnth ws i))) 1); [lia | reflexivity].
Qed.

Lemma e9_eq : forall k, (-1000 <= k <= 1000)%Z ->
  bv_swrap 32 (Z.land (Z.shiftl (Z.land (4 * k) 18446744073709551615) 1) 18446744073709551615
               + Z.shiftr (Z.land (4 * k) 18446744073709551615) 2) = (9 * k)%Z.
Proof.
  intros k Hk. rewrite !land_W64. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^1)%Z with 2%Z. change (2^2)%Z with 4%Z. change (2^64)%Z with 18446744073709551616%Z.
  rewrite swrap32_eq.
  destruct (Z.lt_ge_cases k 0).
  - rewrite <- (Z.mod_unique (4 * k) 18446744073709551616 (-1) (18446744073709551616 + 4 * k)) by lia.
    rewrite <- (Z.mod_unique ((18446744073709551616 + 4 * k) * 2) 18446744073709551616 1 (18446744073709551616 + 8 * k)) by lia.
    replace ((18446744073709551616 + 4 * k) / 4)%Z with (4611686018427387904 + k)%Z by mlia.
    mlia.
  - rewrite (Z.mod_small (4 * k)) by lia. rewrite (Z.mod_small (4 * k * 2)) by lia.
    replace (4 * k / 4)%Z with k by mlia. mlia.
Qed.

Lemma sx32_wval : forall ws i, (wval ws i < 2147483648)%Z -> sx32 (wnth ws i) = Z_to_bv 64 (wval ws i).
Proof.
  intros ws i Hv. unfold sx32, wval in *. f_equal. rewrite swrap32_eq.
  pose proof (zr_word (wnth ws i) : (0 <= _ < 2^64)%Z) as R. Z.div_mod_to_equations. lia.
Qed.

Lemma pow10_small : forall n v, (1 <= n)%Z -> (10 ^ n <= v)%Z -> (v < 1000000000)%Z -> (10 <= 10 ^ n <= 100000000)%Z.
Proof.
  intros n v Hn Hle Hv.
  assert (n < 9)%Z.
  { destruct (Z.lt_ge_cases n 9) as [|Hge]; [assumption|]. exfalso.
    assert (10 ^ 9 <= 10 ^ n)%Z by (apply Z.pow_le_mono_r; lia). change (10^9)%Z with 1000000000%Z in *. lia. }
  split.
  - change 10%Z with (10^1)%Z at 1. apply Z.pow_le_mono_r; lia.
  - change 100000000%Z with (10^8)%Z. apply Z.pow_le_mono_r; lia.
Qed.

Lemma fmt_fp_cnt_step : forall k v i e,
  fmt_fp_cnt (S k) v (i, e) = (if i <=? v then fmt_fp_cnt k v (i * 10, e + 1)%Z else Some (i, e)).
Proof. reflexivity. Qed.

Lemma seqz_b2z : forall x, (-2^63 <= x < 2^63)%Z ->
  Z.b2z (Z.land x 18446744073709551615 <? 1) = (if x =? 0 then 1 else 0)%Z.
Proof.
  intros x Hx. rewrite land_W64. destruct (Z.eqb_spec x 0) as [->|Hne]; [reflexivity|].
  destruct (Z.lt_ge_cases x 0).
  - rewrite <- (Z.mod_unique x (2^64) (-1) (x + 2^64)) by lia.
    destruct (Z.ltb_spec0 (x + 2^64) 1); [exfalso; lia | reflexivity].
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec0 x 1); [exfalso; lia | reflexivity].
Qed.

Lemma lor32_range : forall t, (0 <= t < 256)%Z -> (0 <= Z.lor t 32 < 288)%Z.
Proof.
  intros t Ht. pose proof (Z.add_lor_land t 32) as E.
  assert (0 <= Z.land t 32)%Z by (apply Z.land_nonneg; lia).
  assert (0 <= Z.lor t 32)%Z by (apply Z.lor_nonneg; lia). lia.
Qed.

Lemma a9_eq : forall k, (-1000 <= k <= 1000)%Z ->
  Z_to_bv 64 (Z.shiftl (Z.land (4 * k) 18446744073709551615) 1 + Z.shiftr (bv_signed (Z_to_bv 64 (4 * k))) 2 + -9)
  = Z_to_bv 64 (9 * (k - 1)).
Proof.
  intros k Hk. apply Z_to_bv_eqm. rewrite land_W64, signed_of_Z by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^1)%Z with 2%Z. change (2^2)%Z with 4%Z.
  change (2^64)%Z with 18446744073709551616%Z.
  replace (4 * k / 4)%Z with k by mlia.
  destruct (Z.lt_ge_cases k 0).
  - rewrite <- (Z.mod_unique (4 * k) 18446744073709551616 (-1) (18446744073709551616 + 4 * k)) by lia. mlia.
  - rewrite (Z.mod_small (4 * k)) by lia. mlia.
Qed.

Lemma j_eq : forall t p1 e, (0 <= t < 256)%Z -> (0 <= p1 < 2^20)%Z -> (-100000 <= e <= 100020)%Z ->
  bv_swrap 32 (Z.land (bv_swrap 32 (p1 - Z.land (Z.b2z (0 <? p1)) (Z.b2z (Z.land (Z.lor t 32 + -103) 18446744073709551615 <? 1)))) 18446744073709551615
               - Z.land (Z.land (Z.b2z (Z.land (Z.lor t 32 + -102) 18446744073709551615 <? 1) + -1) 18446744073709551615) (Z.land e 18446744073709551615))
  = ffp_j t p1 e.
Proof.
  intros t p1 e Ht Hp He. pose proof (lor32_range t Ht) as Rt.
  rewrite !seqz_b2z by lia. unfold ffp_j, CHR_f, CHR_g.
  replace (Z.lor t 32 + -103 =? 0) with (Z.lor t 32 =? 103) by (destruct (Z.eqb_spec (Z.lor t 32) 103), (Z.eqb_spec (Z.lor t 32 + -103) 0); lia || reflexivity).
  replace (Z.lor t 32 + -102 =? 0) with (Z.lor t 32 =? 102) by (destruct (Z.eqb_spec (Z.lor t 32) 102), (Z.eqb_spec (Z.lor t 32 + -102) 0); lia || reflexivity).
  set (g := Z.land (Z.b2z (0 <? p1)) (if Z.lor t 32 =? 103 then 1 else 0)).
  assert (Hg : g = (if (Z.lor t 32 =? 103) && negb (p1 =? 0) then 1 else 0)%Z /\ (0 <= g <= p1)%Z).
  { subst g. destruct (Z.ltb_spec0 0 p1), (Z.lor t 32 =? 103), (Z.eqb_spec p1 0); cbn -[Z.land];
      rewrite ?Z.land_0_l, ?Z.land_0_r; try change (Z.land 1 1) with 1%Z; lia. }
  destruct Hg as [Hg Rg]. rewrite <- Hg. clearbody g.
  set (f2 := Z.land (Z.land ((if Z.lor t 32 =? 102 then 1 else 0) + -1) 18446744073709551615) (Z.land e 18446744073709551615)).
  assert (Hf : f2 = (if Z.lor t 32 =? 102 then 0 else e mod 2^64)%Z).
  { subst f2. destruct (Z.lor t 32 =? 102); [cbn; reflexivity|].
    change (Z.land (0 + -1) 18446744073709551615)%Z with 18446744073709551615%Z.
    rewrite Z.land_comm, !land_W64. apply Z.mod_mod. lia. }
  rewrite Hf. clear Hf f2.
  rewrite land_W64, !swrap32_eq. change (2^64)%Z with 18446744073709551616%Z.
  destruct (Z.lor t 32 =? 102); cbn [negb Z.mul]; mlia.
Qed.

Lemma fmt_fp_cnt_res : forall k v i e i' e',
  fmt_fp_cnt k v (i, e) = Some (i', e') -> (e <= e' <= e + Z.of_nat k)%Z.
Proof.
  induction k as [|k IH]; intros v i e i' e' H; [discriminate H|].
  rewrite fmt_fp_cnt_step in H. destruct (i <=? v).
  - apply IH in H. rewrite Nat2Z.inj_succ. lia.
  - injection H as <- <-. lia.
Qed.
