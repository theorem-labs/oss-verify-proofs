(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Zbitwise.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjLeaves.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_stage1_kit Od_tables.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Definition PSTR_FRAME : Z := 112.

Definition pstr_post_g (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SB CAP sbo i j lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ (a0 = wz 0 \/ exists sbo', a0 = wz (SB + sbo') /\ (sbo <= sbo' <= sbo + (j - i - 1))%Z)
    /\ munch [(bv_unsigned sp - PSTR_FRAME, bv_unsigned sp); (SB + sbo, SB + sbo + (j - i))]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
    /\ wr_at segs m' SB CAP /\ stk segs m' lo (bv_unsigned sp).

Definition pstr_stmt_g (segs : list Segment) (entry gtop : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (BUF SB CAP i j sbo lo : Z) (bs : list Z),
  mem_inv segs m -> stk segs m lo (bv_unsigned sp) -> (lo + PSTR_FRAME <= bv_unsigned sp)%Z -> (gtop <= lo)%Z ->
  bytes_ok bs -> bytes_at segs m BUF (padded_bytes bs) -> (BUF + blen bs + 64 <= lo)%Z ->
  closes bs (i + 1) j ->
  wr_at segs m SB CAP -> (SB + CAP <= lo)%Z -> (0 <= sbo)%Z -> (sbo + (j - i) <= CAP)%Z ->
  (BUF + blen bs + 64 <= SB \/ SB + CAP <= BUF)%Z ->
  evt segs (pstr_post_g segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SB CAP sbo i j lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz (BUF + i + 1)) (wz (SB + sbo)) (wz 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

Record psenv : Type := mkPsEnv {
  q_ra : word; q_sp : word; q_gp : word; q_tp : word;
  q_s0 : word; q_s1 : word; q_s2 : word; q_s3 : word; q_s4 : word; q_s5 : word;
  q_s6 : word; q_s7 : word; q_s8 : word; q_s9 : word; q_s10 : word; q_s11 : word;
  q_F : bvmap 5 word; q_fc : bv 32;
  q_BUF : Z; q_SB : Z; q_CAP : Z; q_i : Z; q_j : Z; q_sbo : Z; q_lo : Z; q_bs : list Z; q_m0 : mem }.

Notation q_SP E := (bv_unsigned (q_sp E)).
Notation q_len E := (blen (q_bs E)).

Record ps_ok_g (GTOP : Z) (E : psenv) : Prop := mkPsOk {
  po_room : (q_lo E + PSTR_FRAME <= q_SP E)%Z;
  po_gtop : (GTOP <= q_lo E)%Z;
  po_bytes : bytes_ok (q_bs E);
  po_buf : (q_BUF E + q_len E + 64 <= q_lo E)%Z;
  po_closes : closes (q_bs E) (q_i E + 1) (q_j E);
  po_sb : (q_SB E + q_CAP E <= q_lo E)%Z;
  po_sbo : (0 <= q_sbo E)%Z;
  po_cap : (q_sbo E + (q_j E - q_i E) <= q_CAP E)%Z;
  po_sep : (q_BUF E + q_len E + 64 <= q_SB E \/ q_SB E + q_CAP E <= q_BUF E)%Z }.

Notation ps_post_g segs E :=
  (pstr_post_g segs (q_ra E) (q_sp E) (q_gp E) (q_tp E) (q_s0 E) (q_s1 E) (q_s2 E) (q_s3 E) (q_s4 E) (q_s5 E) (q_s6 E) (q_s7 E) (q_s8 E)
     (q_s9 E) (q_s10 E) (q_s11 E) (q_F E) (q_fc E) (q_SB E) (q_CAP E) (q_sbo E) (q_i E) (q_j E) (q_lo E) (q_m0 E)).

Notation ps_W E := [(q_SP E - PSTR_FRAME, q_SP E); (q_SB E + q_sbo E, q_SB E + q_sbo E + (q_j E - q_i E))]%Z.

Open Scope Z_scope.
Definition sxu (v : Z) : Z := bv_unsigned (sx32 (Z_to_bv 64 v)).
Definition or4 (a b c e : Z) : Z := Z.lor (Z.lor (Z.lor (sxu a) (sxu b)) (sxu c)) (sxu e).
Definition ONES64 : Z := 18446744073709551615.
Definition DINV : Z := 4294967295.

Lemma u64_small_z : forall x, 0 <= x < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 x) = x.
Proof. intros x H. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_small. exact H. Qed.

Lemma sxu_valid : forall v, 0 <= v < 65536 -> sxu v = v.
Proof. intros v H. unfold sxu. rewrite sx32_small by lia. apply u64_small_z. lia. Qed.

Lemma sxu_invalid : sxu DINV = ONES64.
Proof. vm_compute. reflexivity. Qed.

Lemma sxu_range : forall v, 0 <= sxu v < 2 ^ 64.
Proof. intros v. unfold sxu. pose proof (bv_unsigned_in_range 64 (sx32 (Z_to_bv 64 v))) as R. unfold bv_modulus in R. exact R. Qed.

Lemma lor_ones64_r : forall x, 0 <= x < 2 ^ 64 -> Z.lor x ONES64 = ONES64.
Proof.
  intros x H. unfold ONES64. change 18446744073709551615 with (Z.ones 64).
  apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec.
  destruct (Z.ltb_spec n 64).
  - rewrite Z.ones_spec_low by lia. apply orb_true_r.
  - rewrite Z.ones_spec_high by lia. rewrite orb_false_r.
    apply Z.bits_above_log2; [lia|]. destruct (Z.eq_dec x 0) as [->|NZ]; [cbn; lia|].
    apply Z.log2_lt_pow2; [lia|]. apply Z.lt_le_trans with (2 ^ 64); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma lor_ones64_l : forall x, 0 <= x < 2 ^ 64 -> Z.lor ONES64 x = ONES64.
Proof. intros. rewrite Z.lor_comm. apply lor_ones64_r. assumption. Qed.

Lemma lor_lt_pow2 : forall a b n, 0 <= n -> 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> 0 <= Z.lor a b < 2 ^ n.
Proof.
  intros a b n Hn Ha Hb. assert (NN : 0 <= Z.lor a b) by (apply Z.lor_nonneg; lia). split; [exact NN|].
  assert (S0 : Z.shiftr (Z.lor a b) n = 0).
  { rewrite Z.shiftr_lor, !Z.shiftr_div_pow2 by lia. rewrite !Z.div_small by lia. reflexivity. }
  apply Z.shiftr_eq_0_iff in S0. destruct S0 as [->|[P L]]; [apply Z.pow_pos_nonneg; lia|].
  apply Z.log2_lt_pow2; assumption.
Qed.

Definition dshape (x : Z) : Prop := 0 <= x < 65536 \/ x = DINV.

Lemma or4_cases : forall a b c e, dshape a -> dshape b -> dshape c -> dshape e ->
  or4 a b c e = ONES64 \/
  (0 <= or4 a b c e < 65536 /\ 0 <= a < 65536 /\ 0 <= b < 65536 /\ 0 <= c < 65536 /\ 0 <= e < 65536).
Proof.
  intros a b c e Ha Hb Hc He. unfold or4.
  pose proof (sxu_range a) as Ra. pose proof (sxu_range b) as Rb. pose proof (sxu_range c) as Rc. pose proof (sxu_range e) as Re.
  assert (Rab : 0 <= Z.lor (sxu a) (sxu b) < 2 ^ 64) by (apply lor_lt_pow2; lia).
  assert (Rabc : 0 <= Z.lor (Z.lor (sxu a) (sxu b)) (sxu c) < 2 ^ 64) by (apply lor_lt_pow2; lia).
  destruct He as [He| ->]; [|left; rewrite sxu_invalid; apply lor_ones64_r; exact Rabc].
  destruct Hc as [Hc| ->]; [|left; rewrite sxu_invalid, (lor_ones64_r _ Rab); apply lor_ones64_l; exact Re].
  destruct Hb as [Hb| ->]; [|left; rewrite sxu_invalid, (lor_ones64_r _ Ra), (lor_ones64_l _ Rc); apply lor_ones64_l; exact Re].
  destruct Ha as [Ha| ->]; [|left; rewrite sxu_invalid, (lor_ones64_l _ Rb), (lor_ones64_l _ Rc); apply lor_ones64_l; exact Re].
  right. rewrite !sxu_valid by lia. change 65536 with (2 ^ 16).
  split; [|lia]. apply lor_lt_pow2; [lia| |lia]. apply lor_lt_pow2; [lia| |lia]. apply lor_lt_pow2; lia.
Qed.

Lemma odig_dshape : forall x, dshape (odig x).
Proof. intros x. unfold dshape, DINV. apply odig_shape. Qed.

Lemma odig_valid_not_qb : forall base b, (base = 630 \/ base = 420 \/ base = 210 \/ base = 0) -> odig (base + b) < 65536 -> not_qb b.
Proof.
  intros base b Hb Hv. destruct odig_hextab as [_ HT]. split; intro Eb; subst b.
  - rewrite (HT base 34 Hb (or_introl eq_refl)) in Hv. lia.
  - rewrite (HT base 92 Hb (or_intror eq_refl)) in Hv. lia.
Qed.

Lemma lor_shl8_add : forall a b, 0 <= a -> 0 <= b < 256 -> Z.lor (Z.shiftl a 8) b = a * 256 + b.
Proof.
  intros a b Ha Hb. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite <- Z.add_lor_land.
  assert (L0 : Z.land (a * 256) b = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.ltb_spec n 8).
    - replace (a * 256) with (a * 2 ^ 8) by lia. rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - rewrite (Z.bits_above_log2 b n); [apply andb_false_r|lia|].
      destruct (Z.eq_dec b 0) as [->|NZ]; [cbn; lia|].
      apply Z.lt_le_trans with 8; [|lia]. apply Z.log2_lt_pow2; lia. }
  lia.
Qed.

Lemma lor_shl8_bu : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> Z.lor (Z.shiftl a 8) b = 23669 -> a = 92 /\ b = 117.
Proof. intros a b Ha Hb H. rewrite lor_shl8_add in H by lia. lia. Qed.

Lemma shl2 : forall x, Z.shiftl x 2 = (4 * x)%Z.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.

Lemma land_m1024 : forall v, 0 <= v < 65536 -> Z.land v (-1024) = 1024 * (v / 1024).
Proof.
  intros v H. change (-1024) with (Z.lnot (Z.ones 10)).
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 10) with 1024. lia.
Qed.
Close Scope Z_scope.

Lemma zxb_B : forall bs i, bytes_ok bs -> zxb (Z_to_bv 8 (B bs i)) = Z_to_bv 64 (B bs i).
Proof. intros bs i H. apply zxb_small. apply B_range. exact H. Qed.

Lemma buf_read_at_g : forall segs (m : mem) A bs i a,
  bytes_at segs m A (padded_bytes bs) -> (0 <= i < blen bs + 64)%Z -> a = wa (A + i) ->
  ov_read_bytes segs m a 1 = Some [Z_to_bv 8 (B bs i)].
Proof. intros segs m A bs i a H Hi ->. apply buf_read_g; assumption. Qed.

Lemma wr_store_ok_at_g : forall segs (m : mem) A N i (j : nat) a,
  wr_at segs m A N -> (0 <= i)%Z -> (i + Z.of_nat j <= N)%Z -> a = wa (A + i) -> store_ok segs m a j = true.
Proof. intros segs m A N i j a H H0 H1 ->. apply (wr_at_store_ok segs m A N i j H); assumption. Qed.

Ltac ps_strip_base Ea A :=
  lazymatch Ea with
  | A => constr:(0%Z)
  | Z.add A ?i => constr:(i)
  | Z.add ?X ?c => let r := ps_strip_base X A in constr:(Z.add r c)
  end.

Ltac ps_load_buf :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a 1] =>
      lazymatch goal with
      | H : bytes_at segs m ?A (padded_bytes ?bs) |- _ =>
          let Ea := addr_expr a in
          let idx := ps_strip_base Ea A in
          rewrite (buf_read_at_g segs m A bs idx a H ltac:(lia) ltac:(unfold wa; f_equal; lia))
      end
  end;
  load_post.

Ltac ps_store_wr :=
  match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
      rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
      let Ea := addr_expr a in
      match goal with
      | H : wr_at segs m ?A ?N |- _ =>
          let idx := ps_strip_base Ea A in
          rewrite (wr_store_ok_at_g segs m A N idx n a H ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) ltac:(unfold wa; f_equal; lia));
          cbv beta iota
      end
  end.

Ltac ps_solve_store0 :=
  match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
    rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in addr_near k;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
          cbv beta iota;
          match goal with
          | |- context [write_to_mem m a ?bs] =>
              replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
          end
        end
    | HS : store_ok segs m ?a' n = true |- _ =>
        cbv delta [wa] in HS;
        first [ rewrite HS
              | replace (store_ok segs m a n) with true
                  by (rewrite <- HS; f_equal; word_eq_tac);
                try replace (write_to_mem m a) with (write_to_mem m a')
                  by (f_equal; word_eq_tac) ];
        cbv beta iota
    end
  end.

Ltac psnorm :=
  cbv beta;
  repeat match goal with
  | |- context [zxb (Z_to_bv 8 (B ?bs ?i))] => rewrite (zxb_B bs i) by assumption
  | |- context [zxb (Z_to_bv 8 ?c)] => rewrite (zxb_small c) by lia
  | |- context [bv_unsigned (Z_to_bv 8 ?c)] => rewrite (u8_small c) by lia
  | |- context [Z.shiftl ?x 2] => rewrite (shl2 x)
  end.

Ltac ps_store_done_wr :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs) _) =>
      let Ea := addr_expr a in
      (match goal with
       | H : wr_at segs m ?A ?N |- _ =>
           let idx := ps_strip_base Ea A in
           let n := lazymatch bs with
                    | le8 _ => constr:(8%nat) | le4 _ => constr:(4%nat) | le2 _ => constr:(2%nat) | le1 _ => constr:(1%nat)
                    | [_] => constr:(1%nat) end in
           let HS := fresh "HSOK" in
           assert (HS : store_ok segs m a n = true)
             by (apply (wr_store_ok_at_g segs m A N idx n a H); [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | unfold wa; f_equal; lia])
       end);
      store_done
  | _ => idtac
  end.
Ltac pstep := zstep; psnorm; ps_store_done_wr.
