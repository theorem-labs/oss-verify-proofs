(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Tac ZBridge FP.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.TU Require Import G3Pure_u G3Lem_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.TUB Require Import DgWalkB_u DgSpecB_u G3PureB_u.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := DgWalkB_u.rsegs.

Lemma swrap32_id : forall x, (- 2 ^ 31 <= x < 2 ^ 31)%Z -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.pow]. change (2 ^ 32 / 2)%Z with (2 ^ 31)%Z.
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma swrap32_mod : forall x k, bv_swrap 32 (x + k * 2 ^ 32) = bv_swrap 32 x.
Proof.
  intros x k. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.pow].
  replace (x + k * 2 ^ 32 + 2 ^ 32 / 2)%Z with ((x + 2 ^ 32 / 2) + k * 2 ^ 32)%Z by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma kc_arg : forall ple, (-1127 <= ple <= 971)%Z -> bv_swrap 32 (18446744073709551566 - ple mod 18446744073709551616) = (-50 - ple)%Z.
Proof.
  intros ple Hp. rewrite (Z.mod_eq ple 18446744073709551616) by lia.
  replace (18446744073709551566 - (ple - 18446744073709551616 * (ple / 18446744073709551616)))%Z
    with ((-50 - ple) + (4294967296 + 4294967296 * (ple / 18446744073709551616)) * 2 ^ 32)%Z by lia.
  rewrite swrap32_mod. apply swrap32_id. lia.
Qed.

Lemma mi_shift : forall mie ple, (-1127 <= ple <= 971)%Z -> (9 <= mie - ple + 10 <= 62)%Z ->
  ((bv_swrap 32 (mie mod 18446744073709551616 - (ple + -10) mod 18446744073709551616) mod 18446744073709551616) mod 64 = mie - ple + 10)%Z.
Proof.
  intros mie ple Hp Hx.
  rewrite (Z.mod_eq mie 18446744073709551616), (Z.mod_eq (ple + -10) 18446744073709551616) by lia.
  replace (mie - 18446744073709551616 * (mie / 18446744073709551616) - (ple + -10 - 18446744073709551616 * ((ple + -10) / 18446744073709551616)))%Z
    with ((mie - ple + 10) + (4294967296 * ((ple + -10) / 18446744073709551616) - 4294967296 * (mie / 18446744073709551616)) * 2 ^ 32)%Z by lia.
  rewrite swrap32_mod, swrap32_id by lia. rewrite !Z.mod_small by lia. reflexivity.
Qed.
Lemma shl_small : forall x k, (0 <= k)%Z -> (0 <= x)%Z -> (x * 2 ^ k < 2 ^ 64)%Z -> ((x ≪ k) mod 18446744073709551616 = x * 2 ^ k)%Z.
Proof. intros x k Hk Hx H. rewrite Z.shiftl_mul_pow2 by lia. apply Z.mod_small. lia. Qed.

Lemma zbv_eqm : forall a b, (a mod 2 ^ 64 = b mod 2 ^ 64)%Z -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros a b H. rewrite <- (Z_to_bv_mod64 a), <- (Z_to_bv_mod64 b), H. reflexivity. Qed.

Lemma extract64_id : forall z, bv_extract 0 64 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z. apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.
Lemma sext_extract32 : forall z, sext 64 (bv_extract 0 32 (Z_to_bv 64 z)) = Z_to_bv 64 (bv_swrap 32 z).
Proof.
  intros z. rewrite sext_small. f_equal. rewrite signed_of_extract by lia. rewrite Z_to_bv_unsigned.
  unfold bv_swrap. f_equal. unfold bv_wrap, bv_modulus. cbn -[Z.pow].
  rewrite (Z.add_mod (z mod 2 ^ 64)), (Z.add_mod z) by lia. rewrite Z.mod_mod_divide by (exists (2 ^ 32)%Z; reflexivity). reflexivity.
Qed.

Lemma land_mask_low : forall x k, (0 <= k <= 32)%Z -> (0 <= x)%Z -> (x mod 2 ^ k = 0)%Z -> Z.land x (2 ^ 32 - 2 ^ k) = (x mod 2 ^ 32)%Z.
Proof.
  intros x k Hk Hx H. replace (2 ^ 32 - 2 ^ k)%Z with (Z.ones 32 - Z.ones k)%Z by (rewrite !Z.ones_equiv; lia).
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec. rewrite <- Z.land_ones by lia. rewrite Z.land_spec.
  assert (E : Z.testbit (Z.ones 32 - Z.ones k) i = (Z.leb k i && Z.ltb i 32)%bool).
  { replace (Z.ones 32 - Z.ones k)%Z with (Z.shiftl (Z.ones (32 - k)) k).
    - destruct (Z.ltb_spec i k) as [Hik|Hik].
      + rewrite Z.shiftl_spec_low by lia. destruct (Z.leb_spec k i); [lia | reflexivity].
      + rewrite Z.shiftl_spec_high by lia. destruct (Z.leb_spec k i); [|lia]. cbn [andb].
        destruct (Z.ltb_spec i 32); [apply Z.ones_spec_low; lia | apply Z.ones_spec_high; lia].
    - rewrite Z.shiftl_mul_pow2 by lia. rewrite !Z.ones_equiv.
      assert (P : (2 ^ (32 - k) * 2 ^ k = 2 ^ 32)%Z) by (rewrite <- Z.pow_add_r by lia; f_equal; lia). lia. }
  rewrite E. destruct (Z.ltb_spec i k) as [Hik|Hik].
  - assert (Z.testbit x i = false).
    { rewrite <- (Z.mod_pos_bound x (2 ^ k)) || idtac. replace (Z.testbit x i) with (Z.testbit (x mod 2 ^ k) i) by (apply Z.mod_pow2_bits_low; lia). rewrite H. apply Z.bits_0. }
    rewrite H0. rewrite !Bool.andb_false_l. reflexivity.
  - destruct (Z.leb_spec k i); [|lia]. cbn [andb]. destruct (Z.ltb_spec i 32); [rewrite Z.ones_spec_low by lia | rewrite Z.ones_spec_high by lia]; rewrite ?Bool.andb_true_r, ?Bool.andb_false_r; reflexivity.
Qed.
Lemma prod32 : forall a b, (0 <= a < 2 ^ 32)%Z -> (0 <= b < 2 ^ 32)%Z -> (0 <= a * b < 2 ^ 64)%Z.
Proof. intros a b Ha Hb. split; [apply Z.mul_nonneg_nonneg; lia|]. assert (a * b <= (2 ^ 32 - 1) * (2 ^ 32 - 1))%Z by (apply Z.mul_le_mono_nonneg; lia). lia. Qed.
Lemma hi32 : forall x, (0 <= x < 2 ^ 64)%Z -> (0 <= Z.shiftr x 32 < 2 ^ 32)%Z.
Proof. intros x Hx. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.
Lemma lo32_of_shl : forall x, (0 <= x)%Z -> (Z.shiftr ((Z.shiftl x 32) mod 18446744073709551616) 32 = x mod 4294967296)%Z.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  replace 18446744073709551616%Z with (2 ^ 32 * 2 ^ 32)%Z by reflexivity. rewrite Z.mul_mod_distr_r by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.
Lemma mulhu_shl32 : forall a b, (0 <= a < 2 ^ 32)%Z -> (0 <= b < 2 ^ 32)%Z -> (Z.shiftr ((a * 4294967296) * (b * 4294967296)) 64 = a * b)%Z.
Proof. intros a b Ha Hb. rewrite Z.shiftr_div_pow2 by lia. replace (a * 4294967296 * (b * 4294967296))%Z with ((a * b) * 2 ^ 64)%Z by ring. apply Z.div_mul. lia. Qed.

Lemma shl32_mod : forall x, (0 <= x)%Z -> ((Z.shiftl x 32) mod 18446744073709551616 = (x mod 4294967296) * 4294967296)%Z.
Proof. intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. replace 18446744073709551616%Z with (2 ^ 32 * 2 ^ 32)%Z by reflexivity. apply Z.mul_mod_distr_r; lia. Qed.

Lemma negw_small : forall mk, (-307 <= mk <= 325)%Z -> bv_swrap 32 (0 - mk mod 18446744073709551616) = (- mk)%Z.
Proof.
  intros mk Hm. rewrite (Z.mod_eq mk 18446744073709551616) by lia.
  replace (0 - (mk - 18446744073709551616 * (mk / 18446744073709551616)))%Z with ((- mk) + (4294967296 * (mk / 18446744073709551616)) * 2 ^ 32)%Z by lia.
  rewrite swrap32_mod. apply swrap32_id. lia.
Qed.

Section ZS.
Local Open Scope Z_scope.
Lemma wr_at_app : forall m a n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at rsegs m a (n1 + n2) <-> wr_at rsegs m a n1 /\ wr_at rsegs m (a + n1) n2.
Proof.
  intros m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hl & H). split; [split; [lia | split; [lia | intros i Hi; apply H; lia]] |].
    split; [lia | split; [lia | intros i Hi; replace (a + n1 + i) with (a + (n1 + i)) by lia; apply H; lia]].
  - intros ((Ha & Hl1 & Ha1) & (Hb & Hl2 & Hb2)). split; [lia | split; [lia |]].
    intros i Hi. destruct (Z.lt_ge_cases i n1); [apply Ha1; lia |].
    replace (a + i) with (a + n1 + (i - n1)) by lia. apply Hb2. lia.
Qed.
Lemma u8arr_app : forall m A bs1 bs2,
  u8arr rsegs m A (bs1 ++ bs2) <-> u8arr rsegs m A bs1 /\ u8arr rsegs m (A + Z.of_nat (length bs1)) bs2.
Proof.
  intros m A bs1 bs2. unfold u8arr. rewrite bytes_at_app, length_app, Nat2Z.inj_add, wr_at_app by lia. tauto.
Qed.
Lemma rw_cells_app : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) <-> rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at. rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add, wr_at_app by lia.
  split.
  - intros (((W1 & W2) & B) & Wa & Wb). apply bytes_at_app in B as (B1 & B2). rewrite cells_bytes_length in B2 by assumption. tauto.
  - intros (((W1 & B1) & Wa) & ((W2 & B2) & Wb)). split; [split; [tauto|] | tauto].
    apply bytes_at_app. rewrite cells_bytes_length by assumption. tauto.
Qed.
End ZS.

Section G3B.

Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable F : bvmap 5 word.
Variable m0 : word -> option byte.
Variables buf lenp kp : Z.
Definition GSP : Z := bv_unsigned sp.
Hypothesis BUFR : (4096 <= buf /\ buf + 22 <= 2^47)%Z.
Hypothesis SPR0 : (2^41 <= GSP /\ GSP + 16 <= 2^47)%Z.
Hypothesis KPR : (GSP <= kp /\ kp + 8 <= 2^47)%Z.
Hypothesis KL : lenp = (kp + 4)%Z.
Hypothesis KA : (kp mod 4 = 0)%Z.
Hypothesis SEP_B : (buf + 22 <= GSP - 160 \/ GSP <= buf)%Z.
Hypothesis SEP_BK : (buf + 22 <= kp \/ kp + 8 <= buf)%Z.

Definition G3_W : list (Z * Z) := [(GSP - 160, GSP); (buf, buf + 22); (lenp, lenp + 4); (kp, kp + 4)]%Z.

Definition g3_post : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' (res len K : Z) (bs : list byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F' (ret_pc ra) fc' None m' (seg_rom rsegs)
    /\ munch G3_W m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ frm0 fc'
    /\ stk rsegs m' (GSP - 160) GSP
    /\ u8arr rsegs m' buf bs /\ length bs = 22%nat /\ nth_error bs (Z.to_nat len) = Some (Z_to_bv 8 0)
    /\ rw_cells rsegs m' lenp [C4 (Z_to_bv 64 len)] /\ (1 <= len <= 21)%Z
    /\ rw_cells rsegs m' kp [C4 (Z_to_bv 64 K)] /\ (-343 <= K <= 309)%Z
    /\ (res = 0 \/ res = 1)%Z.

Ltac pgoal := match goal with |- ?G => idtac "GOAL:" G end.

Lemma g3_call : forall t0' t1' t2' t3' t4' t5' t6' s3' s4' s5' s6' s7' s8' (F' : bvmap 5 word) fc (m : word -> option byte) (Wm W Wp s K0 : Z) (bs : list byte) lj j8,
  frm0 fc ->
  stk rsegs m (GSP - 160) (GSP - 96) ->
  rw_cells rsegs m (GSP - 96) [C8 (Z_to_bv 64 kp); CB 8 j8; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch G3_W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> rw_cells rsegs m lenp [C4 lj] -> rw_cells rsegs m kp [C4 (Z_to_bv 64 K0)] ->
  (56 <= s <= 59)%Z -> (1 <= Wm <= W)%Z -> (W <= Wp <= 2 ^ 64 - 2)%Z -> (2 ^ 62 <= Wp + 1)%Z -> (-325 <= K0 <= 307)%Z ->
  evt rsegs g3_post (MS (mkR (Z_to_bv 64 0x444c0) (Z_to_bv 64 (GSP - 96)) gp tp t0' t1' t2' (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                             (Z_to_bv 64 Wm) (Z_to_bv 64 (2 ^ 32 - s)) (Z_to_bv 64 W) (Z_to_bv 64 (2 ^ 32 - s)) (Z_to_bv 64 Wp) (Z_to_bv 64 (2 ^ 32 - s))
                             (Z_to_bv 64 buf) (Z_to_bv 64 lenp) (Z_to_bv 64 kp) s3' s4' s5' s6' s7' s8' s9 s10 s11 t3' t4' t5' t6')
                        F' (Z_to_bv 64 0x44940) fc None m (seg_rom rsegs)).
Proof using All.
  intros until j8. intros FRM ST FR MU WM MI BU BL LE KC Hs HWm HW HWp HKs.
  unfold G3_W in MU. unfold GSP in *.
  rewrite <- (firstn_skipn 21 bs) in BU. apply u8arr_app in BU as [BU1 BU2].
  assert (BL1 : length (firstn 21 bs) = 21%nat) by (rewrite firstn_length; lia).
  rewrite BL1 in BU2. change (Z.of_nat 21) with 21%Z in BU2.
  assert (B21 : exists b21, skipn 21 bs = [b21]).
  { assert (L1 : length (skipn 21 bs) = 1%nat) by (rewrite length_skipn; lia).
    destruct (skipn 21 bs) as [|b21 [|? ?]]; cbn in L1; try lia. exists b21. reflexivity. }
  destruct B21 as [b21 B21]. rewrite B21 in BU2.
  apply (proj1 (rw_cells_app m (bv_unsigned sp - 96) [C8 (Z_to_bv 64 kp)] _)) in FR as [KPc FR]. cbn [cells_size csize Nat.add] in FR.
  replace (bv_unsigned sp - 96 + Z.of_nat 8)%Z with (bv_unsigned sp - 88)%Z in FR by lia.
  replace (Z_to_bv 64 W) with (Z_to_bv 64 (Wm + (W - Wm))) by (f_equal; lia).
  replace (Z_to_bv 64 Wp) with (Z_to_bv 64 (Wm + (W - Wm) + (Wp - W))) by (f_equal; lia).
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 96)) = (bv_unsigned sp - 96)%Z) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { refine (DgSpecB_u.dg_spec (Z_to_bv 64 0x444c0) (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp (Z_to_bv 64 buf) (Z_to_bv 64 lenp) (Z_to_bv 64 kp) s3'
              s4' s5' s6' s7' s8' s9 s10 s11
              F' fc m buf lenp kp _ _ KL _ KA _ _ t0' t1' t2' t3' t4' t5' t6' m Wm (W - Wm) (Wp - W) s K0 (firstn 21 bs) lj
              _ _ _ _ _ _ _ _ _ BU1 BL1 LE _ MI eq_refl).
    all: unfold DgWalkB_u.SP0 in *; rewrite ?USP.
    all: try lia.
    all: try (replace (bv_unsigned sp - 96 - 64)%Z with (bv_unsigned sp - 160)%Z by lia; exact ST).
    all: try exact KPc.
    all: exact KC. }
  cbv beta. intros ms' P. unfold DgWalkB_u.dg_post, DgWalkB_u.DG_W, DgWalkB_u.SP0 in P. rewrite USP in P.
  destruct P as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & res & len & kappa & bs2 & -> & MUc & WMc & MI2 & ST2 & BU1' & BL1' & LE2 & LR & KC2 & KR & RES).
  replace (bv_unsigned sp - 96 - 64)%Z with (bv_unsigned sp - 160)%Z in ST2, MUc by lia.
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call rsegs mm m2 MUc WMc; clear MUc WMc; try clear MI end.
  replace (ret_pc (Z_to_bv 64 0x444c0)) with (Z_to_bv 64 0x444c0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

  zstep. if_cases Kz; [zify_cond Kz; lia | ].
  zstep. zstep. if_cases Ka; [zify_cond Ka; rewrite (land3_0 lenp ltac:(rewrite KL; rewrite <- Zplus_mod_idemp_l, KA; reflexivity)) in Ka; lia | ].
  zstep. rewrite sx32_small by lia.
  zstep.
  zstep. zstep. zstep. if_cases Kn; [zify_cond Kn; ub_norm_in Kn; lia | ].
  do 4 zstep. zstep. if_cases Kp; [zify_cond Kp; ub_norm_in Kp; cbv in Kp; discriminate | ].
  zstep. if_cases Kb; [zify_cond Kb; lia | ].
  replace (len + buf)%Z with (buf + len)%Z by lia.
  assert (BUa : u8arr rsegs m2 buf (bs2 ++ [b21])) by (apply u8arr_app; split; [exact BU1' | rewrite BL1'; exact BU2]).
  clear BU1' BU2.
  assert (BLa : length (bs2 ++ [b21]) = 22%nat) by (rewrite length_app, BL1'; reflexivity).
  pose proof (u8arr_store_ok rsegs m2 buf (bs2 ++ [b21]) len (Z_to_bv 64 (buf + len)) BUa ltac:(rewrite BLa; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
  zstep.
  replace (write_to_mem m2 (Z_to_bv 64 (buf + len)) (le1 (Z_to_bv 64 0))) with (write_to_mem m2 (wa (buf + len)) [Z_to_bv 8 0])
    by (f_equal; symmetry; apply le1_lit).
  pose proof (u8arr_write rsegs m2 buf (bs2 ++ [b21]) len (Z_to_bv 8 0) BUa ltac:(rewrite BLa; lia)) as BU'.
  clear BUa. store_done.
  lazymatch goal with FRx : rw_cells rsegs ?mm (bv_unsigned sp - 88) _ |- _ =>
    assert (FRf : rw_cells rsegs mm (bv_unsigned sp - 96) ([C8 (Z_to_bv 64 kp)] ++ [CB 8 j8; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]))
      by (apply rw_cells_app; split; [exact KPc | cbn [cells_size csize Nat.add]; replace (bv_unsigned sp - 96 + Z.of_nat 8)%Z with (bv_unsigned sp - 88)%Z by lia; exact FRx]) end.
  clear KPc FR. cbn [app] in FRf. rename FRf into FR.
  do 12 zstep.
  replace (Z_to_bv 64 (bv_unsigned sp - 96 + 96)) with sp by (rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  release_frame FR ST2 (bv_unsigned sp).
  finish.
  all: try exact BU'.
  all: try exact LE2.
  all: try exact KC2.
  all: try (rewrite upd_length; exact BLa).
  all: try (apply nth_error_upd_same; rewrite BLa; lia).
  all: lia.
Qed.

Lemma g3_mul : forall (acw bcw adw bdw acp bcp adp bdp acm bcm adm bdm : Z) (s mk : Z) (F' : bvmap 5 word) fc (m : word -> option byte) (bs : list byte) lj kj j16 ra' a6' s8' t4',
  frm0 fc -> stk rsegs m (GSP - 160) (GSP - 96) ->
  rw_cells rsegs m (GSP - 96) [CB 16 j16; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch G3_W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> rw_cells rsegs m lenp [C4 lj] -> rw_cells rsegs m kp [C4 kj] ->
  (0 <= acw <= 18446744065119617025)%Z -> (0 <= bcw <= 18446744065119617025)%Z -> (0 <= adw <= 18446744065119617025)%Z -> (0 <= bdw <= 18446744065119617025)%Z ->
  (0 <= acp <= 18446744065119617025)%Z -> (0 <= bcp <= 18446744065119617025)%Z -> (0 <= adp <= 18446744065119617025)%Z -> (0 <= bdp <= 18446744065119617025)%Z ->
  (0 <= acm <= 18446744065119617025)%Z -> (0 <= bcm <= 18446744065119617025)%Z -> (0 <= adm <= 18446744065119617025)%Z -> (0 <= bdm <= 18446744065119617025)%Z ->
  Z.land bcw 4294965248 = (bcw mod 4294967296)%Z -> Z.land bcp 4294966272 = (bcp mod 4294967296)%Z ->
  (56 <= s <= 59)%Z -> (-307 <= mk <= 325)%Z ->
  (1 <= mcode acm adm bcm bdm)%Z -> (mcode acm adm bcm bdm <= mcode acw adw bcw bdw)%Z -> (mcode acw adw bcw bdw <= mcode acp adp bcp bdp)%Z ->
  (mcode acp adp bcp bdp <= 2 ^ 64 - 2)%Z -> (2 ^ 62 <= mcode acp adp bcp bdp + 1)%Z ->
  evt rsegs g3_post (MS (mkR ra' (Z_to_bv 64 (GSP - 96)) gp tp (Z_to_bv 64 adm) (Z_to_bv 64 4294965248) (Z_to_bv 64 4294966272) (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
        (Z_to_bv 64 (- s)) (Z_to_bv 64 (- s)) (Z_to_bv 64 4294967295) (Z_to_bv 64 bdw) (Z_to_bv 64 bdm) (Z_to_bv 64 (- mk)) a6' (Z_to_bv 64 adp)
        (Z_to_bv 64 kp) (Z_to_bv 64 bcw) (Z_to_bv 64 acp) (Z_to_bv 64 bcp) (Z_to_bv 64 acm) (Z_to_bv 64 adw) s8' s9 s10 s11
        (Z_to_bv 64 bdp) t4' (Z_to_bv 64 bcm) (Z_to_bv 64 acw))
     F' (Z_to_bv 64 0x443FC) fc None m (seg_rom rsegs)).
Proof using All.
  intros until t4'. intros FRM ST FR MU WM MI BU BL LE KC Racw Rbcw Radw Rbdw Racp Rbcp Radp Rbdp Racm Rbcm Radm Rbdm Eb Ep Hs Hmk HWm HW1 HW2 HW3 HW4.
  unfold G3_W in MU.
  pose proof (shr32_range _ Racw) as Sacw. pose proof (shr32_range _ Rbcw) as Sbcw. pose proof (shr32_range _ Racp) as Sacp. pose proof (shr32_range _ Rbcp) as Sbcp.
  pose proof (shr32_range _ Racm) as Sacm. pose proof (shr32_range _ Rbcm) as Sbcm. pose proof (shr32_range _ Radw) as Sadw. pose proof (shr32_range _ Rbdw) as Sbdw.
  pose proof (shr32_range _ Radp) as Sadp. pose proof (shr32_range _ Rbdp) as Sbdp. pose proof (shr32_range _ Radm) as Sadm. pose proof (shr32_range _ Rbdm) as Sbdm.
  pose proof (Z.mod_pos_bound bcw 4294967296 ltac:(lia)) as Mbcw. pose proof (Z.mod_pos_bound bcp 4294967296 ltac:(lia)) as Mbcp.
  pose proof (Z.mod_pos_bound bcm 4294967296 ltac:(lia)) as Mbcm. pose proof (Z.mod_pos_bound adw 4294967296 ltac:(lia)) as Madw.
  pose proof (Z.mod_pos_bound adp 4294967296 ltac:(lia)) as Madp. pose proof (Z.mod_pos_bound adm 4294967296 ltac:(lia)) as Madm.
  assert (LF : forall x, (0 <= x)%Z -> Z.land x 4294967295 = (x mod 4294967296)%Z)
    by (intros x Hx; change 4294967295%Z with (Z.ones 32); rewrite Z.land_ones by lia; reflexivity).
  zs1. rewrite Eb.
  do 3 zs1. rewrite Ep.
  do 44 (zs1; try (rewrite ?LF by lia)).
  zs1.
  replace (adm mod 4294967296 + 2147483648 + (bdm ≫ 32 + bcm mod 4294967296))%Z with (adm mod 4294967296 + (bdm ≫ 32 + bcm mod 4294967296) + 2147483648)%Z by ring.
  replace (adp mod 4294967296 + 2147483648 + (bdp ≫ 32 + bcp mod 4294967296))%Z with (adp mod 4294967296 + (bdp ≫ 32 + bcp mod 4294967296) + 2147483648)%Z by ring.
  fold (mcode acw adw bcw bdw) (mcode acp adp bcp bdp) (mcode acm adm bcm bdm).
  replace ((- s mod 18446744073709551616) mod 4294967296)%Z with (2 ^ 32 - s)%Z
    by (rewrite Z.mod_mod_divide by (exists 4294967296%Z; reflexivity); rewrite <- (Z.mod_add (- s) 1) by lia; rewrite Z.mod_small by lia; lia).
  eapply g3_call; try eassumption; lia.
Qed.

End G3B.
