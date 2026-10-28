(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes StoreFast FP ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Lemma B_nz_lt : forall bs q, (B bs q <> 0)%Z -> (q < blen bs)%Z.
Proof. intros bs q H. destruct (Z_lt_dec q (blen bs)) as [L|L]; [exact L|]. exfalso. apply H. apply B_pad. lia. Qed.

Lemma land255_mod : forall x, Z.land (x mod 18446744073709551616) 255 = (x mod 256)%Z.
Proof.
  intros x. change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia.
  change 18446744073709551616%Z with (2 ^ 56 * 2 ^ 8)%Z. change (2 ^ 8)%Z with 256%Z.
  rewrite Z.mul_comm. rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.
Lemma land255_small : forall x, (0 <= x < 256)%Z -> Z.land x 255 = x.
Proof. intros x H. change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Ltac nnorm :=
  s2norm;
  repeat match goal with
  | |- context [Z.land (Z.modulo ?x 18446744073709551616) 255] => rewrite (land255_mod x)
  | |- context [Z.land (B ?bs ?i) 255] => rewrite (land255_small (B bs i)) by lia
  end.

Ltac nnorm_land :=
  repeat match goal with
  | |- context [Z.land (Z.modulo ?x 18446744073709551616) 255] => rewrite (land255_mod x)
  | |- context [Z.land (B ?bs ?i) 255] => rewrite (land255_small (B bs i)) by lia
  end.
Ltac nstep := zstep; gnorm; nnorm_land; g_store_hook; g_store_done.

Ltac n_tape2 :=
  match goal with
  | OKh : env_ok ?E0, TI : tape_img ?E0 ?tws ?sbs ?m, N1 : bytes_at _ ?m ?A1 (le8 ?w1), N2 : bytes_at _ ?m ?A2 (le8 ?w2) |- _ =>
      let TI2 := fresh "TIMG" in
      pose proof (tape_img_app2w E0 tws sbs m w1 w2 A1 A2 OKh TI N1 N2 ltac:(tlia) ltac:(tlia) ltac:(tlia)) as TI2;
      clear TI; clear N1 N2
  end.
Ltac srun_to A :=
  repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => lazymatch pc with A => fail | _ => idtac end end; nstep).
Ltac srun := repeat nstep.

Local Open Scope Z_scope.
Lemma lor_add : forall n X Y, 0 <= n -> 0 <= X -> X mod 2 ^ n = 0 -> 0 <= Y < 2 ^ n -> Z.lor X Y = X + Y.
Proof.
  intros n X Y Hn HX HM HY. rewrite <- Z.add_lor_land.
  assert (L0 : Z.land X Y = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.ltb_spec i n).
    - assert (EX : X = (X / 2 ^ n) * 2 ^ n) by (pose proof (Z.div_mod X (2 ^ n) ltac:(lia)); lia).
      rewrite EX. rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - destruct (Z.eq_dec Y 0) as [->|NZ]; [rewrite Z.bits_0; apply andb_false_r|].
      rewrite (Z.bits_above_log2 Y i); [apply andb_false_r | lia |].
      apply Z.lt_le_trans with n; [|lia]. apply Z.log2_lt_pow2; lia. }
  lia.
Qed.

Definition V8 (b1 b2 b3 b4 b5 b6 b7 b8 : Z) : Z :=
  Z.lor (Z.shiftl (Z.lor (Z.lor (Z.shiftl b8 24 mod 18446744073709551616) (Z.shiftl b7 16 mod 18446744073709551616))
                         (Z.lor (Z.shiftl b6 8 mod 18446744073709551616) b5)) 32 mod 18446744073709551616)
        (Z.lor (Z.lor (Z.shiftl b4 24 mod 18446744073709551616) (Z.shiftl b3 16 mod 18446744073709551616))
               (Z.lor (Z.shiftl b2 8 mod 18446744073709551616) b1)).

Lemma V4_sum : forall b1 b2 b3 b4, 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 -> 0 <= b4 < 256 ->
  Z.lor (Z.lor (Z.shiftl b4 24 mod 18446744073709551616) (Z.shiftl b3 16 mod 18446744073709551616))
        (Z.lor (Z.shiftl b2 8 mod 18446744073709551616) b1) = b1 + 256 * b2 + 65536 * b3 + 16777216 * b4.
Proof.
  intros b1 b2 b3 b4 H1 H2 H3 H4.
  rewrite !Z.shiftl_mul_pow2 by lia. rewrite !Z.mod_small by lia.
  rewrite (lor_add 8 (b2 * 2 ^ 8) b1) by (try apply Z_mod_mult; lia).
  rewrite (lor_add 24 (b4 * 2 ^ 24) (b3 * 2 ^ 16)) by (try (replace (b4 * 2 ^ 24) with (b4 * 2 ^ 24) by lia; apply Z_mod_mult); lia).
  rewrite (lor_add 16 (b4 * 2 ^ 24 + b3 * 2 ^ 16) (b2 * 2 ^ 8 + b1)); [lia | lia | lia | | lia].
  replace (b4 * 2 ^ 24 + b3 * 2 ^ 16) with ((b4 * 256 + b3) * 2 ^ 16) by lia. apply Z_mod_mult.
Qed.

Lemma V8_sum : forall b1 b2 b3 b4 b5 b6 b7 b8,
  0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 -> 0 <= b4 < 256 -> 0 <= b5 < 256 -> 0 <= b6 < 256 -> 0 <= b7 < 256 -> 0 <= b8 < 256 ->
  V8 b1 b2 b3 b4 b5 b6 b7 b8 =
  b1 + 256 * b2 + 65536 * b3 + 16777216 * b4 + 4294967296 * (b5 + 256 * b6 + 65536 * b7 + 16777216 * b8).
Proof.
  intros b1 b2 b3 b4 b5 b6 b7 b8 H1 H2 H3 H4 H5 H6 H7 H8. unfold V8.
  rewrite !V4_sum by lia.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia.
  rewrite lor_add with (n := 32); [lia | lia | lia | apply Z_mod_mult | lia].
Qed.

Lemma V8_range : forall b1 b2 b3 b4 b5 b6 b7 b8,
  0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 -> 0 <= b4 < 256 -> 0 <= b5 < 256 -> 0 <= b6 < 256 -> 0 <= b7 < 256 -> 0 <= b8 < 256 ->
  0 <= V8 b1 b2 b3 b4 b5 b6 b7 b8 < 18446744073709551616.
Proof. intros. rewrite V8_sum by lia. lia. Qed.

Lemma swar8_last : forall b1 b2 b3 b4 b5 b6 b7 b8,
  0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 -> 0 <= b4 < 256 -> 0 <= b5 < 256 -> 0 <= b6 < 256 -> 0 <= b7 < 256 -> 0 <= b8 < 256 ->
  Z.lor (Z.land (Z.shiftr ((V8 b1 b2 b3 b4 b5 b6 b7 b8 + 434041037028460038) mod 18446744073709551616) 4) 1085102592571150095)
        (Z.land (V8 b1 b2 b3 b4 b5 b6 b7 b8) 17361641481138401520) = 3689348814741910323 ->
  48 <= b8 < 64.
Proof.
  intros b1 b2 b3 b4 b5 b6 b7 b8 H1 H2 H3 H4 H5 H6 H7 H8 HT.
  pose proof (V8_sum b1 b2 b3 b4 b5 b6 b7 b8 H1 H2 H3 H4 H5 H6 H7 H8) as HV.
  set (V := V8 b1 b2 b3 b4 b5 b6 b7 b8) in *.
  apply (f_equal (fun x => Z.land x 17293822569102704640)) in HT.
  rewrite Z.land_lor_distr_l, <- !Z.land_assoc in HT.
  change (Z.land 1085102592571150095 17293822569102704640) with 0 in HT.
  change (Z.land 17361641481138401520 17293822569102704640) with 17293822569102704640 in HT.
  change (Z.land 3689348814741910323 17293822569102704640) with 3458764513820540928 in HT.
  rewrite Z.land_0_r, Z.lor_0_l in HT.
  apply (f_equal (fun x => Z.shiftr x 60)) in HT. rewrite Z.shiftr_land in HT.
  change (Z.shiftr 17293822569102704640 60) with (Z.ones 4) in HT. change (Z.shiftr 3458764513820540928 60) with 3 in HT.
  rewrite Z.land_ones in HT by lia. rewrite Z.shiftr_div_pow2 in HT by lia.
  change (2 ^ 60) with 1152921504606846976 in HT. change (2 ^ 4) with 16 in HT.
  lia.
Qed.
Lemma land_bit31 : forall A T, Z.land (Z.lor A T) 18446744071570489472 = 0 -> (T / 2147483648) mod 2 = 0.
Proof.
  intros A T H.
  assert (H31 : Z.testbit (Z.land (Z.lor A T) 18446744071570489472) 31 = false) by (rewrite H; apply Z.bits_0).
  rewrite Z.land_spec, Z.lor_spec in H31.
  change (Z.testbit 18446744071570489472 31) with true in H31. rewrite andb_true_r in H31.
  apply orb_false_iff in H31. destruct H31 as [_ HT].
  apply Z.testbit_false in HT; [|lia]. exact HT.
Qed.

Lemma swar4_last : forall b1 b2 b3 b4 b5 b6 b7 b8,
  0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 -> 0 <= b4 < 256 -> 0 <= b5 < 256 -> 0 <= b6 < 256 -> 0 <= b7 < 256 -> 0 <= b8 < 256 ->
  Z.land (Z.lor (bv_swrap 32 (V8 b1 b2 b3 b4 b5 b6 b7 b8 mod 18446744073709551616 + 1179010630) mod 18446744073709551616)
                (bv_swrap 32 (V8 b1 b2 b3 b4 b5 b6 b7 b8 mod 18446744073709551616 + 18446744072901087184) mod 18446744073709551616))
         18446744071570489472 = 0 ->
  48 <= b4.
Proof.
  intros b1 b2 b3 b4 b5 b6 b7 b8 H1 H2 H3 H4 H5 H6 H7 H8 HT.
  pose proof (V8_sum b1 b2 b3 b4 b5 b6 b7 b8 H1 H2 H3 H4 H5 H6 H7 H8) as HV.
  set (V := V8 b1 b2 b3 b4 b5 b6 b7 b8) in *.
  apply land_bit31 in HT.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in HT.
  change (2 ^ Z.of_N 32) with 4294967296 in HT. change (4294967296 / 2) with 2147483648 in HT.
  lia.
Qed.

Local Close Scope Z_scope.

Ltac fold_V8 :=
  repeat match goal with
  | |- context [Z.lor (Z.shiftl (Z.lor (Z.lor (Z.shiftl ?b8 24 mod 18446744073709551616) (Z.shiftl ?b7 16 mod 18446744073709551616))
                                       (Z.lor (Z.shiftl ?b6 8 mod 18446744073709551616) ?b5)) 32 mod 18446744073709551616)
                      (Z.lor (Z.lor (Z.shiftl ?b4 24 mod 18446744073709551616) (Z.shiftl ?b3 16 mod 18446744073709551616))
                             (Z.lor (Z.shiftl ?b2 8 mod 18446744073709551616) ?b1))] =>
      fold (V8 b1 b2 b3 b4 b5 b6 b7 b8)
  end.

Ltac srun_cut cuts :=
  repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => cuts pc end; nstep).
Ltac n_closed_branch a b := fail.
Ltac nbranch :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then Z_to_bv 64 ?a else Z_to_bv 64 ?b) _ _ _ _) =>
      first [ n_closed_branch a b | (let KB := fresh "KB" in if_cases KB) ]
  end.
Ltac nexp cuts fin := srun_cut cuts; first [ fin | (nbranch; nexp cuts fin) ].

Lemma word_signed_repr : forall w : word, exists e, (-9223372036854775808 <= e < 9223372036854775808)%Z /\ w = Z_to_bv 64 e.
Proof.
  intros w. pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R. cbn in R.
  exists (if (bv_unsigned w <? 9223372036854775808)%Z then bv_unsigned w else (bv_unsigned w - 18446744073709551616)%Z).
  destruct (Z.ltb_spec (bv_unsigned w) 9223372036854775808).
  - split; [lia|]. apply bv_eq. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. unfold bv_modulus. cbn. lia.
  - split; [lia|]. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
    rewrite <- (Z.mod_add _ 1) by lia. replace (bv_unsigned w - 18446744073709551616 + 1 * 18446744073709551616)%Z with (bv_unsigned w) by lia.
    symmetry. apply Z.mod_small. lia.
Qed.

Lemma s2n_image_readable : forall segs (m : mem) n A bs0,
  image_bytes segs A n = Some bs0 -> (0 <= A)%Z -> (A + Z.of_nat n <= 2^64)%Z ->
  exists bs, length bs = n /\ bytes_at segs m A bs.
Proof.
  intros segs m n. induction n as [|n IH]; intros A bs0 H HA HB.
  - exists []. split; [reflexivity|]. apply bytes_at_nil. lia.
  - cbn [image_bytes] in H. destruct (seg_rom segs (wa A)) as [b|] eqn:E; [|discriminate].
    destruct (image_bytes segs (A + 1) n) as [bs1|] eqn:E2; [|discriminate].
    destruct (IH (A + 1)%Z bs1 E2 ltac:(lia) ltac:(lia)) as (bs & L & BA).
    assert (exists b', mrd segs m (wa A) = Some b') as [b' Hb'].
    { unfold mrd. destruct (m (wa A)); [eexists; reflexivity| exists b; exact E]. }
    exists (b' :: bs). split; [cbn; congruence|].
    destruct BA as (B1 & B2 & B3). split; [lia|]. split; [cbn [length]; lia|].
    intros i Hi. destruct i as [|i]; cbn [nth_error].
    + rewrite Z.add_0_r. exact Hb'.
    + replace (A + Z.of_nat (S i))%Z with (A + 1 + Z.of_nat i)%Z by lia. apply B3. cbn [length] in Hi. lia.
Qed.

Fixpoint s2n_covered_b (segs : list Segment) (A : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => match seg_rom segs (wa A) with Some _ => s2n_covered_b segs (A + 1) n' | None => false end
  end.
Lemma s2n_covered_bytes : forall segs n A, s2n_covered_b segs A n = true -> exists bs, image_bytes segs A n = Some bs.
Proof.
  intros segs n. induction n as [|n IH]; intros A H; cbn [s2n_covered_b image_bytes] in *; [eexists; reflexivity|].
  destruct (seg_rom segs (wa A)); [|discriminate]. destruct (IH _ H) as [bs ->]. eexists; reflexivity.
Qed.

Definition T_POW : Z := 0x266c0.
Definition T_POW_LEN : nat := Z.to_nat 10640.
Lemma T_POW_LEN_Z : Z.of_nat T_POW_LEN = 10640%Z.
Proof. reflexivity. Qed.
Lemma pow_tab_covered : s2n_covered_b bsegs T_POW T_POW_LEN = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pow_tab_read : forall (m : mem) k a, (0 <= k)%Z -> (k + 8 <= 10640)%Z -> a = wa (T_POW + k) ->
  exists w, ov_read_bytes bsegs m a 8 = Some (le8 w).
Proof.
  intros m k a Hk Hl ->.
  destruct (s2n_covered_bytes bsegs T_POW_LEN T_POW pow_tab_covered) as [bs0 E0].
  pose proof T_POW_LEN_Z as HZ.
  destruct (s2n_image_readable bsegs m T_POW_LEN T_POW bs0 E0 ltac:(unfold T_POW; lia) ltac:(rewrite HZ; unfold T_POW; lia)) as (bs & L & BA).
  assert (LZ : Z.of_nat (length bs) = 10640%Z) by (rewrite L; exact HZ).
  exists (le_bytes_to_word (firstn 8 (skipn (Z.to_nat k) bs))).
  rewrite le8_le_bytes_to_word by (rewrite length_firstn, length_skipn; lia).
  apply bytes_at_read; [exact BA | lia | lia].
Qed.

Lemma wz_eq_mod : forall x y, (x mod 18446744073709551616 = y mod 18446744073709551616)%Z -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof.
  intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z. exact H.
Qed.

Ltac ngstep := first [ gguard | nstep ].
Ltac ngrun := repeat ngstep.
Ltac ngrun_to A :=
  repeat (lazymatch goal with
          | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => lazymatch pc with A => fail | _ => idtac end
          | _ => idtac end;
          ngstep).
Ltac ngrun_cut cuts :=
  repeat (lazymatch goal with
          | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => cuts pc
          | _ => idtac end;
          ngstep).
Ltac ngbranch :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then Z_to_bv 64 ?a else Z_to_bv 64 ?b) _ _ _ _) =>
      first [ n_closed_branch a b | (let KB := fresh "KB" in if_cases KB) ]
  end.
Ltac ngexp cuts fin := ngrun_cut cuts; first [ fin | (ngbranch; ngexp cuts fin) ].

Ltac nsafe_val x :=
  lazymatch x with
  | Z_to_bv 64 (Z.shiftr _ 3) => fail
  | Z_to_bv 64 (Z.shiftr _ 3 + _)%Z => fail
  | Z_to_bv 64 (Zpos _ + _)%Z => fail
  | Z_to_bv 64 (Zpos _ + _ + _)%Z => fail
  | Z_to_bv 64 Z0 => fail
  | Z_to_bv 64 (Zpos _) => fail
  | Z_to_bv 64 (Zneg _) => fail
  | _ => idtac
  end.
Ltac nforget keep n :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let x := greg_val R n in
    tryif is_var x then idtac else (tryif nsafe_val x then gforget keep n else idtac)
  end.
Ltac nforget_all keep :=
  let go n := (tryif keep n then nforget keep n else idtac) in
  go 1%Z; go 5%Z; go 6%Z; go 7%Z; go 8%Z; go 9%Z; go 10%Z; go 11%Z; go 12%Z; go 13%Z; go 14%Z; go 15%Z; go 16%Z; go 17%Z;
  go 18%Z; go 19%Z; go 20%Z; go 21%Z; go 22%Z; go 23%Z; go 24%Z; go 25%Z; go 26%Z; go 27%Z; go 28%Z; go 29%Z; go 30%Z; go 31%Z;
  gforget_F.
Ltac ngrun_cut_f cuts keep :=
  repeat (lazymatch goal with
          | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => cuts pc
          | _ => idtac end;
          ngstep; nforget_all keep).

Ltac nfrun_to A keep :=
  repeat (lazymatch goal with
          | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => lazymatch pc with A => fail | _ => idtac end
          | _ => idtac end;
          ngstep; nforget_all keep).

Ltac nkeep more n :=
  lazymatch n with
  | 8%Z => fail | 9%Z => fail | 19%Z => fail | 21%Z => fail | 22%Z => fail | 23%Z => fail | 25%Z => fail | 26%Z => fail
  | _ => more n
  end.
Ltac ngexp_f cuts fin keep := ngrun_cut_f cuts keep; first [ fin | (ngbranch; ngexp_f cuts fin keep) ].

Lemma sxb_small7 : forall b, (0 <= b < 128)%Z -> bv_unsigned (sxb (Z_to_bv 8 b)) = b.
Proof.
  intros b H. unfold sxb. rewrite unsigned_lit_wrap.
  assert (E : bv_signed (Z_to_bv 8 b) = b).
  { unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 8)%Z with 256%Z. change (256 / 2)%Z with 128%Z. rewrite !Z.mod_small by lia. lia. }
  rewrite E. apply Z.mod_small. lia.
Qed.
Lemma swar4_last_sx : forall b1 b2 b3 b4,
  (0 <= b1 < 256)%Z -> (0 <= b2 < 256)%Z -> (0 <= b3 < 256)%Z -> (0 <= b4 < 256)%Z ->
  Z.land (Z.lor (bv_swrap 32 (Z.lor (Z.lor (Z.shiftl (bv_unsigned (sxb (Z_to_bv 8 b4))) 24 mod 18446744073709551616) (Z.shiftl b3 16 mod 18446744073709551616))
                                    (Z.lor (Z.shiftl b2 8 mod 18446744073709551616) b1) + 1179010630) mod 18446744073709551616)
                (bv_swrap 32 (Z.lor (Z.lor (Z.shiftl (bv_unsigned (sxb (Z_to_bv 8 b4))) 24 mod 18446744073709551616) (Z.shiftl b3 16 mod 18446744073709551616))
                                    (Z.lor (Z.shiftl b2 8 mod 18446744073709551616) b1) + 18446744072901087184) mod 18446744073709551616))
         18446744071570489472 = 0%Z ->
  (48 <= b4)%Z.
Proof.
  intros b1 b2 b3 b4 H1 H2 H3 H4 HT. destruct (Z_lt_dec b4 48) as [L|L]; [exfalso | lia].
  rewrite (sxb_small7 b4) in HT by lia.
  rewrite (V4_sum b1 b2 b3 b4) in HT by lia.
  apply land_bit31 in HT.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in HT.
  change (2 ^ Z.of_N 32)%Z with 4294967296%Z in HT. change (4294967296 / 2)%Z with 2147483648%Z in HT.
  lia.
Qed.

Lemma pow5_idx : forall e, (-342 <= e <= 308)%Z ->
  ((8 * (bv_swrap 32 (Z.shiftl (e mod 18446744073709551616) 1) mod 18446744073709551616)) mod 18446744073709551616
   = (16 * e) mod 18446744073709551616)%Z.
Proof.
  intros e HE. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1)%Z with 2%Z.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 / 2)%Z with 2147483648%Z.
  lia.
Qed.
Lemma pow5_addr : forall e d d', (-342 <= e <= 308)%Z -> (d = 157472 + d')%Z ->
  Z_to_bv 64 (8 * (bv_swrap 32 (Z.shiftl (e mod 18446744073709551616) 1) mod 18446744073709551616) + d)%Z = Z_to_bv 64 (157472 + (16 * e + d'))%Z.
Proof.
  intros e d d' HE ->. apply wz_eq_mod. pose proof (pow5_idx e HE) as HI.
  set (X := (bv_swrap 32 (Z.shiftl (e mod 18446744073709551616) 1) mod 18446744073709551616)%Z) in *.
  lia.
Qed.

Ltac nreg_set n v :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let x := greg_val R n in
    replace x with (Z_to_bv 64 v) by (apply wz_eq_mod; lia) end.

Lemma shr3_add8 : forall x j, Z.shiftr (x + 8 * j) 3 = (Z.shiftr x 3 + j)%Z.
Proof. intros x j. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3)%Z with 8%Z. rewrite (Z.mul_comm 8 j). apply Z.div_add. lia. Qed.

Ltac s2_st_eq_leaf :=
  lazymatch goal with
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [ reflexivity | (f_equal; lia) | (f_equal; repeat (f_equal; try lia); lia) | (apply wz_eq_mod; f_equal; lia) ]
  | |- _ => reflexivity
  end.
Ltac s2_st_eq_tree :=
  lazymatch goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal; s2_st_eq_tree
  | |- Some _ = Some _ => f_equal; s2_st_eq_leaf
  | |- _ => reflexivity
  end.
Ltac s2_st_eq :=
  cbv delta [mkR];
  lazymatch goal with
  | |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => first [ reflexivity | (f_equal; [ s2_st_eq_tree | .. ]; try reflexivity) ]
  end.

Tactic Notation "kapply" uconstr(K) := eapply evt_eq; [| eapply K]; [ s2_st_eq | .. ].

Ltac s2_gproj_goal :=
  cbn [e_ra e_sp e_gp e_tp e_s0 e_s1 e_s2 e_s3 e_s4 e_s5 e_s6 e_s7 e_s8 e_s9 e_s10 e_s11 e_lo e_spa e_FF e_THIS e_DOC e_IDX e_BUF e_TAPE e_SBUF e_OC e_IA
       e_bs e_idxs e_iws e_tcap e_scap e_vptr e_p12 e_nxt0 e_p28 e_capv e_p50 e_dcap e_j0 e_j256 e_m0 e_tws e_sbs s2_ghost gapp gpatch].
Ltac s2_kvr_kapply K :=
  lazymatch goal with
  | TI : tape_img _ (_ ++ [?v; ?r]) (_ ++ []) _ |- _ => eapply evt_eq; [| eapply (K v r ltac:(s2_num_word))]; [ s2_gproj_goal; s2_st_eq | .. ]
  | |- _ => fail "s2_kvr_kapply: no extended tape image in the context (run n_tape2 first)"
  end.

Definition pw (m : word -> option byte) (a : word) : word :=
  match ov_read_bytes bsegs m a 8 with Some bs => le_bytes_to_word bs | None => Z_to_bv 64 0 end.
Lemma pow_tab_read_pw : forall (m : word -> option byte) k a, (0 <= k)%Z -> (k + 8 <= 10640)%Z -> a = wa (T_POW + k) ->
  ov_read_bytes bsegs m a 8 = Some (le8 (pw m a)).
Proof.
  intros m k a Hk Hl Ha. destruct (pow_tab_read m k a Hk Hl Ha) as [w RD].
  unfold pw. rewrite RD. rewrite le_bytes_to_word_le8. reflexivity.
Qed.
Ltac p_lia := lia.
Ltac s2_load_pow :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a 8] =>
      let Ea := addr_expr a in
      rewrite (pow_tab_read_pw m ((Ea - 157376) mod 18446744073709551616)%Z a ltac:(p_lia) ltac:(p_lia) ltac:(unfold wa, T_POW; apply wz_eq_mod; p_lia))
  end;
  load_post.
